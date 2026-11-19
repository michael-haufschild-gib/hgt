import GaloisForLFunctions.RestrictedFactorizationCalculus.ResidueDensityOfShortExchanges

/-!
# Switching the first eligible local divisor

Read each range through the gcd with its squarefree modulus. Replacing a
paired local divisor changes the Möbius sign. The complementary cofactor
is coprime to the modulus, so the inverse recovers the original integer.
Ranges with coprime moduli retain their gcd exactly.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def adequate (J k : ℕ) (f : ℕ → ℕ) : Prop :=
  IsShortExchange J k f ∧ 1/1040 ≤ ∑ p ∈ (switchProducts k).image f, 1/(p:ℝ)

/-- A short exchange table in the range, whenever that range supports one. -/
def bandPartner (J k : ℕ) : ℕ → ℕ :=
  if h : ∃ f, adequate J k f then h.choose else id

/-- The canonical table has disjoint short exchanges and fixed reciprocal mass. -/
def bandReady (J k : ℕ) := adequate J k (bandPartner J k)

theorem bandReady_of_table {J k : ℕ} (ht : ∃ f : ℕ → ℕ, IsShortExchange J k f ∧
    1/1040 ≤ ∑ p ∈ (switchProducts k).image f, 1/(p:ℝ)) : bandReady J k := by
  have h : ∃ f, adequate J k f := ht
  simpa only [bandReady,bandPartner,dif_pos h] using h.choose_spec

theorem eventually_bandReady (J : ℕ) (hJ : 0 < J) : ∀ᶠ k : ℕ in atTop, bandReady J k :=
  (eventually_positive_mass_short_exchanges J hJ).mono fun _ ht => bandReady_of_table ht

/-- Eligible local divisors at either end of a reversible exchange. -/
def bandEndpoints (J k : ℕ) :=
  switchProducts k ∪ (switchProducts k).image (bandPartner J k)

private def flipFactor (J k d : ℕ) : ℕ :=
  if d ∈ switchProducts k then bandPartner J k d
  else if h : d ∈ (switchProducts k).image (bandPartner J k) then (mem_image.mp h).choose else d

private theorem divide_period {k p : ℕ} (hp : p ∈ switchPrimes k) : p ∣ switchModulus k :=
  Nat.dvd_of_mem_primeFactors ((switchModulus_spec k).2.1 ▸ hp)

/-- The two endpoints divide the local modulus and have opposite Möbius signs. -/
theorem table_pair_divisors_and_signs {J k w : ℕ} (h : bandReady J k) (hw : w ∈ switchProducts k) :
    w ∣ switchModulus k ∧ bandPartner J k w ∣ switchModulus k ∧
    μ w = 1 ∧ μ (bandPartner J k w) = -1 := by
  obtain ⟨hp,⟨q,hq,r,hr,hqr,he⟩,_,_⟩ := h.1.2 w hw
  have hc := (Nat.coprime_primes (mem_switchPrimes.mp hq).1 (mem_switchPrimes.mp hr).1).2 hqr.ne
  refine ⟨he ▸ hc.mul_dvd_of_dvd_of_dvd (divide_period hq) (divide_period hr),divide_period hp,?_,
    moebius_apply_prime (mem_switchPrimes.mp hp).1⟩
  rw [he,isMultiplicative_moebius.map_mul_of_coprime hc,moebius_apply_prime (mem_switchPrimes.mp hq).1,
    moebius_apply_prime (mem_switchPrimes.mp hr).1]
  decide

private theorem flip_prime {J k w : ℕ} (h : bandReady J k) (hw : w ∈ switchProducts k) :
    flipFactor J k (bandPartner J k w)=w := by
  let p := bandPartner J k w
  have hin : p ∈ (switchProducts k).image (bandPartner J k) := mem_image_of_mem _ hw
  have hnot : p ∉ switchProducts k := by
    intro hp
    have h₁ := (table_pair_divisors_and_signs h hp).2.2.1
    have h₂ := (table_pair_divisors_and_signs h hw).2.2.2
    change μ p = -1 at h₂
    omega
  change (if p ∈ switchProducts k then _ else if h : p ∈ _ then _ else _) = _
  rw [if_neg hnot,dif_pos hin]
  exact h.1.1 (mem_image.mp hin).choose_spec.1 hw (mem_image.mp hin).choose_spec.2

private theorem flip_pair {J k d : ℕ} (h : bandReady J k) (hd : d ∈ bandEndpoints J k) :
    ∃ w ∈ switchProducts k,
      (d=w ∧ flipFactor J k d=bandPartner J k w) ∨
      (d=bandPartner J k w ∧ flipFactor J k d=w) := by
  rcases mem_union.mp hd with hw | hp
  · exact ⟨d,hw,Or.inl ⟨rfl,by rw [flipFactor,if_pos hw]⟩⟩
  · obtain ⟨w,hw,rfl⟩ := mem_image.mp hp
    exact ⟨w,hw,Or.inr ⟨rfl,flip_prime h hw⟩⟩

private theorem flip_spec {J k d : ℕ} (h : bandReady J k) (hd : d ∈ bandEndpoints J k) :
    let e := flipFactor J k d
    e ∈ bandEndpoints J k ∧ e ∣ switchModulus k ∧ flipFactor J k e=d ∧
      |(e:ℝ)-d| ≤ (d:ℝ)/J ∧ μ d = -μ e ∧
      ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ q < r ∧
        ((d=p ∧ e=q*r) ∨ (e=p ∧ d=q*r)) := by
  obtain ⟨w,hw,he⟩ := flip_pair h hd
  obtain ⟨hp,⟨q,hq,r,hr,hqr,hwr⟩,hdis₁,hdis₂⟩ := h.1.2 w hw
  obtain ⟨hwd,hpd,hμw,hμp⟩ := table_pair_divisors_and_signs h hw
  have hdw : flipFactor J k w=bandPartner J k w := by rw [flipFactor,if_pos hw]
  dsimp only
  rcases he with ⟨rfl,hf⟩ | ⟨rfl,hf⟩
  · rw [hf]
    exact ⟨mem_union_right _ (mem_image_of_mem _ hw),hpd,flip_prime h hw,hdis₁,by omega,
      _,q,r,(mem_switchPrimes.mp hp).1,(mem_switchPrimes.mp hq).1,(mem_switchPrimes.mp hr).1,hqr,
      Or.inr ⟨rfl,hwr⟩⟩
  · rw [hf]
    exact ⟨mem_union_left _ hw,hwd,hdw,by rwa [abs_sub_comm],by omega,
      _,q,r,(mem_switchPrimes.mp hp).1,(mem_switchPrimes.mp hq).1,(mem_switchPrimes.mp hr).1,hqr,
      Or.inl ⟨rfl,hwr⟩⟩

/-- No prime of the modulus survives in the complementary squarefree cofactor. -/
theorem coprime_without_gcd {n : ℕ} (hn : Squarefree n) (M : ℕ) :
    (n/n.gcd M).Coprime M := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd h
  have ha := hpg.trans (Nat.gcd_dvd_left _ _)
  have hM := hpg.trans (Nat.gcd_dvd_right _ _)
  have hd := Nat.gcd_dvd_left n M
  have hpn := ha.trans (Nat.div_dvd_of_dvd hd)
  have hpp := Nat.mul_dvd_mul ha (Nat.dvd_gcd hpn hM)
  rw [Nat.div_mul_cancel hd] at hpp
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hn p hpp))

/-- Change the complete local divisor while retaining every external factor. -/
def switchInteger (J k n : ℕ) : ℕ :=
  let d := n.gcd (switchModulus k)
  (n/d)*flipFactor J k d

/-- The local switch reverses its edge and preserves the entire gcd with every coprime modulus. -/
theorem switchInteger_on_endpoint {J k n : ℕ} (h : bandReady J k) (hn : Squarefree n)
    (ha : n.gcd (switchModulus k) ∈ bandEndpoints J k) :
    let m := switchInteger J k n
    GlobalDyadicOneTwoRel n m ∧ m.gcd (switchModulus k) ∈ bandEndpoints J k ∧
      switchInteger J k m=n ∧ |(m:ℝ)-n| ≤ (n:ℝ)/J ∧
      ∀ Q : ℕ, (switchModulus k).Coprime Q → m.gcd Q=n.gcd Q := by
  let M := switchModulus k
  let d := n.gcd M
  let c := n/d
  let e := flipFactor J k d
  have hd : d ∣ n := Nat.gcd_dvd_left _ _
  have hdM : d ∣ M := Nat.gcd_dvd_right _ _
  have hdec : c*d=n := Nat.div_mul_cancel hd
  have hcM := coprime_without_gcd hn M
  change c.Coprime M at hcM
  obtain ⟨he,heM,hinv,hdis,hμ,p,q,r,hp,hq,hr,hqr,hform⟩ := flip_spec h ha
  have he0 := Nat.pos_of_dvd_of_pos heM (switchModulus_spec k).2.2
  have heSq := (switchModulus_spec k).1.squarefree_of_dvd heM
  have hcSq := hn.squarefree_of_dvd (Nat.div_dvd_of_dvd hd)
  have hcd := Nat.Coprime.coprime_dvd_right hdM hcM
  have hce := Nat.Coprime.coprime_dvd_right heM hcM
  have hmSq := Nat.squarefree_mul_iff.mpr ⟨hce,hcSq,heSq⟩
  have hg : (c*e).gcd M=e := (Nat.Coprime.gcd_mul_left_cancel _ hcM).trans (Nat.gcd_eq_left heM)
  change GlobalDyadicOneTwoRel n (c*e) ∧ (c*e).gcd M ∈ _ ∧ switchInteger J k (c*e)=n ∧
    |((c*e:ℕ):ℝ)-n| ≤ _ ∧ _
  refine ⟨⟨hn,hmSq,?_,c,p,q,r,hp,hq,hr,hqr,?_⟩,by rw [hg]; exact he,?_,?_,?_⟩
  · calc μ n = μ (c*d) := congrArg (fun a => μ a) hdec.symm
         _ = -μ (c*e) := by
           rw [isMultiplicative_moebius.map_mul_of_coprime hcd,isMultiplicative_moebius.map_mul_of_coprime hce,
             hμ,mul_neg]
  · rcases hform with ⟨hp,hqr⟩ | ⟨hp,hqr⟩
    · exact Or.inl ⟨hdec.symm.trans (congrArg (c*·) hp),congrArg (c*·) hqr⟩
    · exact Or.inr ⟨congrArg (c*·) hp,hdec.symm.trans (congrArg (c*·) hqr)⟩
  · change ((c*e)/((c*e).gcd M))*flipFactor J k ((c*e).gcd M)=n
    rw [hg,Nat.mul_div_cancel _ he0,hinv,hdec]
  · have hr : ((c*d:ℕ):ℝ)=n := congrArg Nat.cast hdec
    change |((c*e:ℕ):ℝ)-n| ≤ (n:ℝ)/J
    rw [←hr]
    push_cast
    rw [←mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg c),mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hdis (Nat.cast_nonneg c)
  · intro Q hMQ
    have hdQ := Nat.Coprime.coprime_dvd_left hdM hMQ
    have heQ := Nat.Coprime.coprime_dvd_left heM hMQ
    calc (c*e).gcd Q = c.gcd Q := Nat.Coprime.gcd_mul_right_cancel c heQ
         _ = (c*d).gcd Q := (Nat.Coprime.gcd_mul_right_cancel c hdQ).symm
         _ = n.gcd Q := congrArg (fun a => a.gcd Q) hdec

/-- The two local gcds of a switched integer are the two entries of one
canonical table pair. Either local divisor identifies the same pair. -/
theorem switchInteger_gcd_pair {J k n : ℕ} (h : bandReady J k) (hn : Squarefree n)
    (ha : n.gcd (switchModulus k) ∈ bandEndpoints J k) :
    let d := n.gcd (switchModulus k)
    let e := (switchInteger J k n).gcd (switchModulus k)
    ∃ w ∈ switchProducts k, (d=w ∧ e=bandPartner J k w) ∨ (d=bandPartner J k w ∧ e=w) := by
  let M := switchModulus k
  let d := n.gcd M
  have he := (flip_spec h ha).2.1
  have hg : (switchInteger J k n).gcd M=flipFactor J k d :=
    (Nat.Coprime.gcd_mul_left_cancel _ (coprime_without_gcd hn M)).trans (Nat.gcd_eq_left he)
  dsimp only
  rw [hg]
  exact flip_pair h ha

/-- Ranges whose complete local divisor is one of the two eligible factors. -/
def activeBands (J : ℕ) (I : Finset ℕ) (n : ℕ) :=
  I.filter fun k => n.gcd (switchModulus k) ∈ bandEndpoints J k

/-- Switch at the least eligible range, fixing integers that fail every test. -/
def rangeSwitch (J : ℕ) (I : Finset ℕ) (n : ℕ) :=
  if h : (activeBands J I n).Nonempty then switchInteger J ((activeBands J I n).min' h) n else n

private theorem first_switch_spec {J n : ℕ} {I : Finset ℕ}
    (hI : ∀ k ∈ I, bandReady J k)
    (hco : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j))
    (hn : Squarefree n) (hA : (activeBands J I n).Nonempty) :
    let m := rangeSwitch J I n
    GlobalDyadicOneTwoRel n m ∧ (activeBands J I m).Nonempty ∧ rangeSwitch J I m=n ∧
      |(m:ℝ)-n| ≤ (n:ℝ)/J := by
  let k := (activeBands J I n).min' hA
  let m := switchInteger J k n
  have hk : k ∈ activeBands J I n := min'_mem _ hA
  obtain ⟨hki,hka⟩ := mem_filter.mp hk
  obtain ⟨edge,inside,back,near,stable⟩ := switchInteger_on_endpoint (hI k hki) hn hka
  have same : activeBands J I m=activeBands J I n := by
    ext j
    simp only [activeBands,mem_filter]
    by_cases hj : j ∈ I
    · simp only [hj,true_and]
      by_cases he : k=j
      · subst j
        exact iff_of_true inside hka
      · rw [show m.gcd (switchModulus j)=n.gcd (switchModulus j) from stable _ (hco k hki j hj he)]
    · simp [hj]
  have hA' : (activeBands J I m).Nonempty := same ▸ hA
  have hk' : (activeBands J I m).min' hA'=k := by dsimp only [k]; congr 1
  have hm : rangeSwitch J I n=m := dif_pos hA
  refine ⟨hm ▸ edge,hm ▸ hA',?_,hm ▸ near⟩
  rw [hm,rangeSwitch,dif_pos hA',hk']
  exact back

/-- One map acts on all squarefree integers. Its fixed points are precisely
the integers with no eligible complete local divisor. -/
theorem rangeSwitch_involution (J : ℕ) (I : Finset ℕ)
    (hI : ∀ k ∈ I, bandReady J k)
    (hco : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j))
    {n : ℕ} (hn : Squarefree n) :
    let m := rangeSwitch J I n
    rangeSwitch J I m=n ∧ |(m:ℝ)-n| ≤ (n:ℝ)/J ∧
      (m=n ↔ ¬(activeBands J I n).Nonempty) ∧ (m=n ∨ GlobalDyadicOneTwoRel n m) := by
  by_cases ha : (activeBands J I n).Nonempty
  · obtain ⟨edge,_,back,near⟩ := first_switch_spec hI hco hn ha
    have hd : rangeSwitch J I n ≠ n := by
      intro he
      have hsg := edge.2.2.1
      rw [he] at hsg
      rcases moebius_eq_one_or_neg_one_of_squarefree hn with h | h <;> omega
    exact ⟨back,near,iff_of_false hd (not_not.mpr ha),Or.inr edge⟩
  · have he : rangeSwitch J I n=n := dif_neg ha
    refine ⟨(congrArg (rangeSwitch J I) he).trans he,?_,iff_of_true he ha,Or.inl he⟩
    rw [he,sub_self,abs_zero]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every eligible squarefree integer outside the two short boundary strips
is matched. All partners lie within 2X/J, uniformly across the selected prime
ranges and with arbitrary external cofactors. -/
theorem matching_from_disjoint_ranges (J X : ℕ) (I : Finset ℕ)
    (hI : ∀ k ∈ I, bandReady J k)
    (hco : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j)) :
    ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
      (∀ n ∈ M.unmatchedSet, (activeBands J I n).Nonempty →
        (n:ℝ) ≤ X+2*(X:ℝ)/J ∨ 2*(X:ℝ)-2*(X:ℝ)/J < n) ∧
      ∀ n ∈ M.sources, |(M.partner n:ℝ)-n| ≤ 2*(X:ℝ)/J := by
  let S := Ioc X (2*X)
  let F := rangeSwitch J I
  let src := (posParity S).filter (fun n => (activeBands J I n).Nonempty ∧ F n ∈ S)
  have posInfo {x : ℕ} (hx : x ∈ src) :
      μ x=1 ∧ μ (F x) = -1 ∧ GlobalDyadicOneTwoRel x (F x) ∧ F (F x)=x ∧
      |(F x:ℝ)-x| ≤ (x:ℝ)/J := by
    obtain ⟨hp,ha,_⟩ := mem_filter.mp hx
    have hμ := (mem_filter.mp hp).2
    have hsq := squarefree_iff_moebius_ne_zero.mpr (by rw [hμ]; decide)
    obtain ⟨edge,_,back,near⟩ := first_switch_spec hI hco hsq ha
    have sign := edge.2.2.1
    change μ x = - μ (F x) at sign
    exact ⟨hμ,by omega,edge,back,near⟩
  let M : OppositeParityMatching GlobalDyadicOneTwoRel S := {
    sources := src
    partner := F
    sources_subset := filter_subset _ _
    injOn := fun a ha b hb he => (posInfo ha).2.2.2.1.symm.trans
      ((congrArg F he).trans (posInfo hb).2.2.2.1)
    partner_mem := fun n hn => mem_filter.mpr ⟨(mem_filter.mp hn).2.2,(posInfo hn).2.1⟩
    adj := fun n hn => (posInfo hn).2.2.1 }
  have range {n : ℕ} (hn : n ∈ S) : (n:ℝ)/J ≤ 2*(X:ℝ)/J :=
    div_le_div_of_nonneg_right (by exact_mod_cast (mem_Ioc.mp hn).2) (Nat.cast_nonneg _)
  refine ⟨M,?_,fun n hn => (posInfo hn).2.2.2.2.trans (range (mem_filter.mp (M.sources_subset hn)).1)⟩
  intro n hn ha
  obtain ⟨hnS,hnm⟩ := mem_sdiff.mp hn
  obtain ⟨hm,hsq⟩ := mem_filter.mp hnS
  obtain ⟨edge,ha',back,near⟩ := first_switch_spec hI hco hsq ha
  by_contra! h
  have hdis := abs_le.mp (near.trans (range hm))
  have hF : F n ∈ S := mem_Ioc.mpr ⟨by exact_mod_cast
    (show (X:ℝ) < F n by linarith only [h.1,hdis.1]),by exact_mod_cast
    (show (F n:ℝ) ≤ 2*X by linarith only [h.2,hdis.2])⟩
  rcases moebius_eq_one_or_neg_one_of_squarefree hsq with hμ | hμ
  · exact hnm (mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hm,hμ⟩,ha,hF⟩))
  · have hsign := edge.2.2.1
    change μ n = - μ (F n) at hsign
    have hplus : μ (F n)=1 := by omega
    have hb : F (F n) ∈ S := by change F (F n)=n at back; rw [back]; exact hm
    have hsrc : F n ∈ src := mem_filter.mpr ⟨mem_filter.mpr ⟨hF,hplus⟩,ha',hb⟩
    exact hnm (mem_union_right _ (mem_image.mpr ⟨F n,hsrc,back⟩))

end GaloisForLFunctions.RestrictedFactorizationCalculus
