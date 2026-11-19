import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusCancellationAndOddDilationMeans
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture

/-!
# Inverting two close prime dilations on sharp prefixes

At the cutoff pn the first dilation recovers n and the second has strictly
smaller argument. The geometric loss is finite at every positive power
exponent. Thus a difference of dilations preserves the exact power-bound
class, including every floor.
-/

noncomputable section

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Sharp power growth of an integer prefix. -/
def PrefixPower (θ : ℝ) (F : ℕ → ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |F n| ≤ C*(n:ℝ)^θ

/-- The signed difference produced by changing a single reserved prime partner. -/
def dilationDifference (p q : ℕ) (F : ℕ → ℝ) (n : ℕ) := F (n/p)-F (n/q)

private theorem div_nat_real_le (n d : ℕ) (hd : 0 < d) : ((n/d:ℕ):ℝ) ≤ (n:ℝ)/d :=
  (le_div_iff₀ (Nat.cast_pos.mpr hd)).2 (by exact_mod_cast Nat.div_mul_le_self n d)

/-- A change of partner from p to q preserves every positive power exponent.
The inverse loses only the fixed geometric factor p^θ/(1-(p/q)^θ). -/
theorem prefixPower_dilationDifference_iff {p q : ℕ} (hp : 0 < p) (hpq : p < q)
    {θ : ℝ} (hθ : 0 < θ) (F : ℕ → ℝ) (h0 : F 0=0) :
    PrefixPower θ (dilationDifference p q F) ↔ PrefixPower θ F := by
  constructor
  · rintro ⟨C,hC,h⟩
    let r := (p:ℝ)/q
    have hq : (0:ℝ)<q := Nat.cast_pos.mpr (hp.trans hpq)
    have hr : 0 < r := div_pos (Nat.cast_pos.mpr hp) hq
    have hr1 : r<1 := (div_lt_one hq).2 (Nat.cast_lt.mpr hpq)
    have hrθ : r^θ<1 := Real.rpow_lt_one hr.le hr1 hθ
    let B := C*(p:ℝ)^θ/(1-r^θ)
    have hB : 0 ≤ B := div_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (sub_pos.mpr hrθ).le
    have hprice : B*(1-r^θ)=C*(p:ℝ)^θ := div_mul_cancel₀ _ (sub_pos.mpr hrθ).ne'
    refine ⟨B,hB,fun n => ?_⟩
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n=0
      · rw [hn,h0,abs_zero]; positivity
      have hn0 := Nat.pos_of_ne_zero hn
      let m := p*n/q
      have hm : m < n := (Nat.div_lt_iff_lt_mul (hp.trans hpq)).2
        ((Nat.mul_lt_mul_of_pos_right hpq hn0).trans_eq (Nat.mul_comm q n))
      have hmR : (m:ℝ) ≤ r*n := by
        apply (div_nat_real_le (p*n) q (hp.trans hpq)).trans_eq
        dsimp only [r]; push_cast; ring
      have hs := h (p*n)
      change |F (p*n/p)-F m| ≤ C*((p*n:ℕ):ℝ)^θ at hs
      rw [Nat.mul_div_cancel_left _ hp,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hs
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg m) hmR hθ.le
      rw [Real.mul_rpow hr.le (Nat.cast_nonneg n)] at hpow
      have hstep := (ih m hm).trans (mul_le_mul_of_nonneg_left hpow hB)
      have hsum : |F n| ≤ |F n-F m|+|F m| := by simpa only [sub_add_cancel] using abs_add_le (F n-F m) (F m)
      have he := congrArg (fun t : ℝ => t*(n:ℝ)^θ) hprice
      linarith only [hs,hstep,hsum,he]
  · rintro ⟨C,hC,h⟩
    refine ⟨2*C,by positivity,fun n => ?_⟩
    have hbound (d : ℕ) : |F (n/d)| ≤ C*(n:ℝ)^θ := (h _).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.div_le_self n d)) hθ.le) hC)
    calc |F (n/p)-F (n/q)| ≤ |F (n/p)|+|F (n/q)| := abs_sub _ _
         _ ≤ _ := by linarith only [hbound p,hbound q]

private theorem power_sub {θ : ℝ} {F G : ℕ → ℝ}
    (hf : PrefixPower θ F) (hg : PrefixPower θ G) : PrefixPower θ (fun x => F x-G x) := by
  obtain ⟨A,hA,ha⟩ := hf
  obtain ⟨B,hB,hb⟩ := hg
  refine ⟨A+B,add_nonneg hA hB,fun x => ?_⟩
  exact (abs_sub _ _).trans ((add_le_add (ha x) (hb x)).trans_eq (add_mul ..).symm)

private theorem power_mono {F : ℕ → ℝ} (h0 : F 0=0) {θ φ : ℝ}
    (hle : θ ≤ φ) (h : PrefixPower θ F) : PrefixPower φ F := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,fun n => ?_⟩
  by_cases hn : n=0
  · rw [hn,h0,abs_zero]; positivity
  exact (h n).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast Nat.pos_of_ne_zero hn : (1:ℝ) ≤ n) hle) hC)

/-- An exact signed divisor sum of dilated sharp prefixes. -/
def divisorPrefix (E : Finset ℕ) (G : ℕ → ℝ) (X : ℕ) :=
  ∑ d ∈ E, (ArithmeticFunction.moebius d:ℝ)*G (X/d)

private theorem divisorPrefix_zero (E : Finset ℕ) {G : ℕ → ℝ} (h0 : G 0=0) :
    divisorPrefix E G 0=0 := by simp [divisorPrefix,h0]

theorem prefixPower_divisorPrefix {θ : ℝ} (hθ : 0 < θ) (E : Finset ℕ) {G : ℕ → ℝ}
    (hG : PrefixPower θ G) : PrefixPower θ (divisorPrefix E G) := by
  obtain ⟨C,hC,h⟩ := hG
  refine ⟨(E.card:ℝ)*C,by positivity,fun n => ?_⟩
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ _d ∈ E,C*(n:ℝ)^θ := by
             apply Finset.sum_le_sum
             intro d _
             rw [abs_mul]
             have hm : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
               exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
             have hdiv := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.div_le_self n d)) hθ.le
             exact (mul_le_mul_of_nonneg_right hm (abs_nonneg (G (n/d)))).trans (by
               rw [one_mul]; exact (h _).trans (mul_le_mul_of_nonneg_left hdiv hC))
       _ = _ := by simp [mul_assoc]

/-- Between keeping and omitting one marked exchange, a single choice
preserves every sharp power exponent of the incoming prefix, including its
endpoint. Its two local charges have opposite signs. -/
theorem choose_pair_preserving_every_power (E : Finset ℕ) {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hne : a ≠ b) (haE : a ∉ E) (hbE : b ∉ E)
    (haμ : ArithmeticFunction.moebius a=1) (hbμ : ArithmeticFunction.moebius b= -1)
    {G : ℕ → ℝ} (h0 : G 0=0) :
    ∃ T : Finset ℕ, (T=E ∨ T=insert a (insert b E)) ∧ ∀ θ : ℝ, 0<θ →
      (PrefixPower θ (divisorPrefix T G) ↔ PrefixPower θ G) := by
  classical
  let F := divisorPrefix E G
  let H := divisorPrefix (insert a (insert b E)) G
  have da : ∀ x, H x-F x=dilationDifference a b G x := by
    intro x
    dsimp only [H,F,divisorPrefix,dilationDifference]
    rw [Finset.sum_insert (show a ∉ insert b E by simpa only [Finset.mem_insert,not_or] using And.intro hne haE),Finset.sum_insert hbE,haμ,hbμ]
    push_cast
    ring
  have recover {θ : ℝ} (hθ : 0<θ) (hf : PrefixPower θ F) (hh : PrefixPower θ H) : PrefixPower θ G := by
    rcases lt_or_gt_of_ne hne with hab | hba
    · apply (prefixPower_dilationDifference_iff ha hab hθ G h0).1
      exact (funext da) ▸ power_sub hh hf
    · apply (prefixPower_dilationDifference_iff hb hba hθ G h0).1
      have he : (fun x => F x-H x)=dilationDifference b a G := by
        funext x
        have h := da x
        dsimp [dilationDifference] at h ⊢
        linarith only [h]
      exact he ▸ power_sub hf hh
  by_cases hF : ∀ θ : ℝ, 0<θ → PrefixPower θ F → PrefixPower θ H
  · exact ⟨E,Or.inl rfl,fun θ hθ => ⟨fun hf => recover hθ hf (hF θ hθ hf),
      prefixPower_divisorPrefix hθ E⟩⟩
  push Not at hF
  obtain ⟨s,_,hFs,hHs⟩ := hF
  refine ⟨insert a (insert b E),Or.inr rfl,fun θ hθ => ⟨?_,prefixPower_divisorPrefix hθ _⟩⟩
  intro hh
  have hst : s ≤ θ := le_of_not_gt (fun h => hHs (power_mono (divisorPrefix_zero _ h0) h.le hh))
  exact recover hθ (power_mono (divisorPrefix_zero E h0) hst hFs) hh

open GaloisForLFunctions.BezoutValuationIncidence

/-- Deleting finitely many prime factors preserves every positive sharp
power class of the Möbius prefix. Each deletion is the invertible
difference between the identity dilation and the prime dilation. -/
theorem coprime_prefix_preserves_every_power {Q : ℕ} (hQ : Squarefree Q) {θ : ℝ} (hθ : 0<θ) :
    PrefixPower θ (coprimeMoebiusSum Q) ↔ PrefixPower θ (coprimeMoebiusSum 1) := by
  have aux (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
      PrefixPower θ (coprimeMoebiusSum (∏ p ∈ S,p)) ↔ PrefixPower θ (coprimeMoebiusSum 1) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
      have hP := hS p (Finset.mem_insert_self ..)
      have hT (q : ℕ) (hq : q ∈ S) := hS q (Finset.mem_insert_of_mem hq)
      let T := ∏ q ∈ S,q
      have hcop : p.Coprime T := Nat.Coprime.prod_right
        (fun q hq => (Nat.coprime_primes hP (hT q hq)).2 (fun h => hp (h ▸ hq)))
      have hd := (Nat.Prime.coprime_iff_not_dvd hP).1 hcop
      have he : dilationDifference 1 p (coprimeMoebiusSum (p*T))=coprimeMoebiusSum T := by
        funext n
        simpa only [dilationDifference,Nat.div_one] using (coprimeMoebiusSum_prime_relation hP hd n).symm
      have hz : coprimeMoebiusSum (p*T) 0=0 := by simp [coprimeMoebiusSum]
      have hb := prefixPower_dilationDifference_iff (by decide : 0 < 1) hP.one_lt hθ _ hz
      rw [he] at hb
      rw [Finset.prod_insert hp]
      exact hb.symm.trans (ih hT)
  simpa only [Nat.prod_primeFactors_of_squarefree hQ] using
    aux Q.primeFactors (fun p h => Nat.prime_of_mem_primeFactors h)

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

private theorem gcd_divisor_row {Q d : ℕ} (hd : d ∈ Q.divisors) (X : ℕ) :
    ∑ n ∈ (Icc 1 X).filter (fun n => n.gcd Q=d), (μ n:ℝ) =
      (μ d:ℝ)*coprimeMoebiusSum Q (X/d) := by
  classical
  let f (n : ℕ) : ℝ := if n.gcd Q=d then μ n else 0
  have hdQ := Nat.dvd_of_mem_divisors hd
  have hsum : ∑ n ∈ (Icc 1 X).filter (d ∣ ·),f n=∑ n ∈ Icc 1 X,f n := by
    apply sum_subset (filter_subset _ _)
    intro n hn hni
    apply if_neg
    intro he
    exact hni (mem_filter.mpr ⟨hn,he ▸ Nat.gcd_dvd_left n Q⟩)
  rw [sum_filter]
  change (∑ n ∈ Icc 1 X,f n)=_
  rw [←hsum,RHTower.sum_Icc_dvd_reindex d X (Nat.pos_of_mem_divisors hd),coprimeMoebiusSum,mul_sum]
  apply sum_congr rfl
  intro a _
  by_cases hc : Q.Coprime a
  · have hg : (d*a).gcd Q=d := (Nat.Coprime.gcd_mul_right_cancel d hc.symm).trans (Nat.gcd_eq_left hdQ)
    dsimp only [f]
    rw [if_pos hg,coprimeMoebiusIndicator,if_pos hc,
      isMultiplicative_moebius.map_mul_of_coprime (Nat.Coprime.coprime_dvd_left hdQ hc),Int.cast_mul]
  · rw [coprimeMoebiusIndicator,if_neg hc,mul_zero]
    dsimp only [f]
    split_ifs with he
    · have hs : ¬Squarefree (d*a) := by
        intro h
        have hda := (Nat.squarefree_mul_iff.mp h).1
        have heq : a.gcd ((d*a).gcd Q)=a.gcd Q := by
          rw [←Nat.gcd_assoc,Nat.gcd_eq_left (Nat.dvd_mul_left a d)]
        rw [he] at heq
        exact hc (show a.Coprime Q from heq.symm.trans hda.symm.gcd_eq_one).symm
      rw [moebius_eq_zero_of_not_squarefree hs,Int.cast_zero]
    · rfl

/-- The exact sharp prefix of any union of local gcd classes is the
associated finite combination of dilated coprime Möbius prefixes. -/
theorem signed_prefix_of_gcd_classes {Q : ℕ} {E : Finset ℕ} (hE : E ⊆ Q.divisors) (X : ℕ) :
    ∑ n ∈ (Icc 1 X).filter (fun n => n.gcd Q ∈ E),(μ n:ℝ) =
      divisorPrefix E (coprimeMoebiusSum Q) X := by
  classical
  let V := (Icc 1 X).filter (fun n => n.gcd Q ∈ E)
  have maps : ∀ n ∈ V,n.gcd Q ∈ E := fun _ h => (mem_filter.mp h).2
  change (∑ n ∈ V,(μ n:ℝ))=_
  rw [←sum_fiberwise_of_maps_to maps (fun n => (μ n:ℝ))]
  apply sum_congr rfl
  intro d hd
  have hrow : V.filter (fun n => n.gcd Q=d)=(Icc 1 X).filter (fun n => n.gcd Q=d) := by
    ext n
    simp only [V,mem_filter]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2 ▸ hd⟩,h.2⟩⟩
  rw [hrow]
  exact gcd_divisor_row (hE hd) X

#print axioms choose_pair_preserving_every_power
#print axioms coprime_prefix_preserves_every_power
#print axioms signed_prefix_of_gcd_classes

end GaloisForLFunctions.RestrictedFactorizationCalculus
