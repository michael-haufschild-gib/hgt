import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeMassInDeficientRows
import GaloisForLFunctions.RHTower.PrimeCellPartition

/-!
# Short reversible exchanges in disjoint ranges of primes

Pair each selected semiprime to a prime in the same short cell. Multiple
separated octaves in one prime range supply a fixed reciprocal mass of
eligible local factors, independent of both the range and the cell width.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells
open scoped Classical

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem fits_cube_cell {t u v : ℝ} (ht : 2 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {w : ℕ} (hw : w ∈ deficientProducts t) (hl : u < w) (hh : (w:ℝ) ≤ v) :
    w ∈ cubeProducts (t^2) u v := by
  obtain ⟨q,r,hq,hr,_,hlo,hhi,rfl,_,_⟩ := deficientProducts_factors ht hw
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq.pos
  have h56 := pow_le_pow_right₀ ht1 (by decide : 5 ≤ 6)
  push_cast at hl hh
  refine mem_biUnion.mpr ⟨q,(mem_windowPrimes (by positivity) (by positivity)).2
    ⟨hq,?_,?_⟩,mem_image.mpr ⟨r,(mem_windowPrimes (div_nonneg hu hq0.le)
      (div_nonneg hv hq0.le)).2 ⟨hr,?_,?_⟩,rfl⟩⟩
  · nlinarith only [hlo,pow_nonneg ht0.le 4]
  · nlinarith only [hhi,h56,pow_nonneg ht0.le 6]
  · rw [div_lt_iff₀ hq0,mul_comm]; exact hl
  · rw [le_div_iff₀ hq0,mul_comm]; exact hh

private theorem uniform_short_prime_partners :
    ∀ᶠ t : ℝ in atTop, ∀ J : ℕ, 0 < J → (J:ℝ) ≤ Real.log t →
      ∃ f : ℕ → ℕ, Set.InjOn f (deficientProducts t) ∧
      ∀ w ∈ deficientProducts t, f w ∈ windowPrimes (t^12) (2*t^12) ∧
        |(f w:ℝ)-w| ≤ t^12/J := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_cubeProducts_capacity 1)
  filter_upwards [eventually_ge_atTop (max 2 H)] with t ht
  intro J hJ hlog
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ t := by linarith only [ht2]
  have ht0 : 0 < t := by linarith only [ht2]
  let T := t^12
  let h := T/J
  have hJ0 : (0:ℝ) < J := by exact_mod_cast hJ
  have hT : 0 < T := pow_pos ht0 _
  have hh : 0 < h := div_pos hT hJ0
  have hcover : (J:ℝ)*h=T := by rw [mul_comm]; exact div_mul_cancel₀ _ hJ0.ne'
  have ht' : t ≤ t^2 := by simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 2)
  have hscale : (t^2)^6=T := by dsimp [T]; ring
  have hgap : (t^2)^6/Real.log (t^2)^1 ≤ h := by
    rw [hscale,pow_one]
    exact div_le_div_of_nonneg_left hT.le hJ0 (hlog.trans (Real.log_le_log ht0 ht'))
  let W := deficientProducts t
  let P := windowPrimes T (2*T)
  have ends {w : ℕ} (hw : w ∈ W) : T < w ∧ (w:ℝ) ≤ 2*T := by
    obtain ⟨_,_,_,_,_,_,_,_,hl,hu⟩ := deficientProducts_factors ht2 hw
    exact ⟨hl,hu⟩
  have counts (i : ℕ) : (W.filter (cellIndex T h · = i)).card ≤ (P.filter (cellIndex T h · = i)).card := by
    by_cases hi : i < J
    · let u := T+i*h
      let v := T+((i:ℝ)+1)*h
      have hu : T ≤ u := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le)
      have hwid : v-u=h := by dsimp [v,u]; ring
      have huv : u ≤ v := sub_nonneg.mp (hwid ▸ hh.le)
      have hv : v ≤ 2*T := by
        have hc : (i:ℝ)+1 ≤ J := by exact_mod_cast (Nat.succ_le_of_lt hi)
        have hle := mul_le_mul_of_nonneg_right hc hh.le
        rw [hcover] at hle
        dsimp [v]; linarith only [hle]
      have hcap := hH (t^2) (((le_max_right _ _).trans ht).trans ht') u v
        (hscale.trans_le hu) huv (hscale ▸ hv) (hwid ▸ hgap)
      have hW : W.filter (cellIndex T h · = i) ⊆ cubeProducts (t^2) u v := by
        intro w hw
        obtain ⟨hm,he⟩ := mem_filter.mp hw
        have hc := cellIndex_spec hh (ends hm).1
        rw [he] at hc
        exact fits_cube_cell ht2 (hT.le.trans hu) (hT.le.trans (hu.trans huv)) hm hc.1 hc.2
      have hP : windowPrimes u v ⊆ P.filter (cellIndex T h · = i) := by
        intro p hp
        obtain ⟨hpr,hl,hr⟩ := (mem_windowPrimes (hT.le.trans hu) (hT.le.trans (hu.trans huv))).1 hp
        exact mem_filter.mpr ⟨(mem_windowPrimes hT.le (by positivity)).2
          ⟨hpr,hu.trans_lt hl,hr.trans hv⟩,cellIndex_eq hh hl hr⟩
      exact (card_le_card hW).trans (hcap.trans (card_le_card hP))
    · have hem : W.filter (cellIndex T h · = i) = ∅ := filter_eq_empty_iff.mpr fun w hw he => by
        apply hi
        rw [←he]
        exact cellIndex_lt hh (ends hw).1 (by rw [hcover]; linarith only [(ends hw).2])
      rw [hem,card_empty]
      exact Nat.zero_le _
  obtain ⟨f,hf,hslot⟩ := exists_cellwise_injOn (cellIndex T h) W P counts
  refine ⟨f,hf,fun w hw => ⟨(hslot w hw).1,?_⟩⟩
  have h₁ := cellIndex_spec hh (ends hw).1
  have h₂ := cellIndex_spec hh ((mem_windowPrimes hT.le (by positivity)).1 (hslot w hw).1).2.1
  rw [(hslot w hw).2] at h₂
  rw [abs_le]
  constructor <;> nlinarith only [h₁.1,h₁.2,h₂.1,h₂.2]

/-- Every selected semiprime in a large octave has a distinct prime partner
within relative distance 1/J in either direction. -/
theorem eventually_short_prime_partners (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ t : ℝ in atTop, ∃ f : ℕ → ℕ, Set.InjOn f (deficientProducts t) ∧
      ∀ w ∈ deficientProducts t, f w ∈ windowPrimes (t^12) (2*t^12) ∧
        |(f w:ℝ)-w| ≤ t^12/J := by
  filter_upwards [uniform_short_prime_partners,Real.tendsto_log_atTop.eventually_ge_atTop (J:ℝ)]
    with t h ht using h J hJ ht

private def octaveScale (j : ℕ) : ℝ := 2^j

private theorem octaveScale_pos (j : ℕ) : 0 < octaveScale j := pow_pos (by norm_num) _

private theorem octaveScale_mono {i j : ℕ} (h : i ≤ j) : octaveScale i ≤ octaveScale j :=
  pow_le_pow_right₀ (by norm_num) h

private theorem separated_octaves {i j : ℕ} (h : i < j) :
    2*(octaveScale i)^12 ≤ (octaveScale j)^12 := by
  have he : octaveScale (i+1) = 2*octaveScale i := by
    change (2:ℝ)^(i+1)=2*2^i
    rw [pow_succ,mul_comm]
  have hf := pow_le_pow_left₀ (octaveScale_pos (i+1)).le (octaveScale_mono h) 12
  rw [he,mul_pow] at hf
  exact (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ) ≤ 2^12)
    (pow_nonneg (octaveScale_pos i).le _)).trans hf

/-- The primes available to one switch, disjoint from later bands whose lower
endpoint exceeds this upper endpoint. -/
def switchPrimes (k : ℕ) : Finset ℕ := windowPrimes (octaveScale k) ((octaveScale k)^24)

/-- Separated product octaves used inside a single range of prime divisors. -/
def switchProducts (k : ℕ) : Finset ℕ := (Ico k (2*k)).biUnion fun j => deficientProducts (octaveScale j)

private theorem octave_upper {k j : ℕ} (hj : j < 2*k) :
    2*(octaveScale j)^12 ≤ (octaveScale k)^24 := by
  apply (separated_octaves hj).trans_eq
  dsimp [octaveScale]
  rw [←pow_mul,←pow_mul]
  congr 1
  omega

private theorem octave_unique {a b : ℕ} {v : ℝ} (ha : (octaveScale a)^12 < v ∧ v ≤ 2*(octaveScale a)^12)
    (hb : (octaveScale b)^12 < v ∧ v ≤ 2*(octaveScale b)^12) : a=b := by
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim (hb.1.not_ge (ha.2.trans (separated_octaves h)))
  · exact h
  · exact False.elim (ha.1.not_ge (hb.2.trans (separated_octaves h)))

/-- The prime and product endpoints of a disjoint switch table on one prime range. -/
def IsShortExchange (J k : ℕ) (f : ℕ → ℕ) : Prop :=
  Set.InjOn f (switchProducts k) ∧
    (∀ w ∈ switchProducts k, f w ∈ switchPrimes k ∧
        (∃ q ∈ switchPrimes k, ∃ r ∈ switchPrimes k, q < r ∧ w=q*r) ∧
        |(f w:ℝ)-w| ≤ (w:ℝ)/J ∧ |(f w:ℝ)-w| ≤ (f w:ℝ)/J)

/-- Each sufficiently high range supports all cell resolutions up to its
logarithmic lower endpoint, with one absolute reciprocal mass bound. -/
theorem uniform_positive_mass_short_exchanges :
    ∀ᶠ k : ℕ in atTop, ∀ J : ℕ, 0 < J → (J:ℝ) ≤ (k:ℝ)*Real.log 2 →
      ∃ f : ℕ → ℕ, IsShortExchange J k f ∧
      1/1040 ≤ ∑ p ∈ (switchProducts k).image f, 1/(p:ℝ) := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp uniform_short_prime_partners
  obtain ⟨G,hG⟩ := eventually_atTop.mp eventually_deficientProducts_lower
  have hlim : Tendsto octaveScale atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [eventually_ge_atTop 1,hlim.eventually_ge_atTop (max 2 (max G H))] with k hk hs
  intro J hJ hjlog
  let I := Ico k (2*k)
  let D := switchProducts k
  let W := fun j => deficientProducts (octaveScale j)
  have base {j : ℕ} (hj : j ∈ I) : max 2 (max G H) ≤ octaveScale j :=
    hs.trans (octaveScale_mono (mem_Ico.mp hj).1)
  have htwo {j : ℕ} (hj : j ∈ I) : 2 ≤ octaveScale j := (le_max_left _ _).trans (base hj)
  have hjL (j : I) : (J:ℝ) ≤ Real.log (octaveScale j) := by
    change (J:ℝ) ≤ Real.log ((2:ℝ)^(j:ℕ))
    rw [Real.log_pow]
    exact hjlog.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (mem_Ico.mp j.property).1)
      (Real.log_nonneg (by norm_num)))
  have short (j : I) := hH (octaveScale j)
    ((le_max_right _ _).trans ((le_max_right _ _).trans (base j.property))) J hJ (hjL j)
  let g := fun j : I => (short j).choose
  have cell (j : I) {w : ℕ} (hw : w ∈ W j) := (short j).choose_spec.2 w hw
  have ends {j w : ℕ} (hj : j ∈ I) (hw : w ∈ W j) :
      (octaveScale j)^12 < w ∧ (w:ℝ) ≤ 2*(octaveScale j)^12 := by
    obtain ⟨_,_,_,_,_,_,_,_,hl,hu⟩ := deficientProducts_factors (htwo hj) hw
    exact ⟨hl,hu⟩
  have primeEnds (j : I) {w : ℕ} (hw : w ∈ W j) :
      (g j w).Prime ∧ (octaveScale j)^12 < g j w ∧ (g j w:ℝ) ≤ 2*(octaveScale j)^12 := by
    have hh := pow_nonneg (octaveScale_pos (j:ℕ)).le 12
    exact (mem_windowPrimes hh (mul_nonneg (by norm_num) hh)).1 (cell j hw).1
  have address {w : ℕ} (hw : w ∈ D) : ∃ j : I, w ∈ W j := by
    obtain ⟨j,hj,hm⟩ := mem_biUnion.mp hw
    exact ⟨⟨j,hj⟩,hm⟩
  let f := fun w => if hw : w ∈ D then g (address hw).choose w else 0
  have eval (j : I) {w : ℕ} (hw : w ∈ W j) : f w=g j w := by
    have hm : w ∈ D := mem_biUnion.mpr ⟨j,j.property,hw⟩
    have hrow : (address hm).choose = j := Subtype.ext (octave_unique
      (ends (address hm).choose.property (address hm).choose_spec) (ends j.property hw))
    simp only [f,dif_pos hm,hrow]
  have hinj : Set.InjOn f D := by
    intro v hv w hw he
    obtain ⟨i,hi⟩ := address hv
    obtain ⟨j,hj⟩ := address hw
    rw [eval i hi,eval j hj] at he
    have hr := (primeEnds i hi).2
    rw [he] at hr
    have hij : i=j := Subtype.ext (octave_unique hr (primeEnds j hj).2)
    subst j
    exact (short i).choose_spec.1 hi hj he
  refine ⟨f,⟨hinj,?_⟩,?_⟩
  · intro w hw
    obtain ⟨j,hj⟩ := address hw
    rw [eval j hj]
    obtain ⟨hq',hpl,hpu⟩ := primeEnds j hj
    obtain ⟨q,r,hq,hr,hqr,hlo,_,he,hwL,hwU⟩ := deficientProducts_factors (htwo j.property) hj
    have ht1 : 1 ≤ octaveScale j := by linarith only [htwo j.property]
    have small := octaveScale_mono (mem_Ico.mp j.property).1
    have top := octave_upper (mem_Ico.mp j.property).2
    have below {e : ℕ} (he : 1 ≤ e) : octaveScale k ≤ (octaveScale j)^e :=
      small.trans (by simpa only [pow_one] using pow_le_pow_right₀ ht1 he)
    have hqL : octaveScale k < q := by linarith only [below (by decide : 1 ≤ 4),hlo,pow_nonneg (zero_le_one.trans ht1) 4]
    have hqN : q ≤ w := he ▸ Nat.le_mul_of_pos_right q hr.pos
    have hrN : r ≤ w := he ▸ Nat.le_mul_of_pos_left r hq.pos
    have band {p : ℕ} : p ∈ switchPrimes k ↔ p.Prime ∧ octaveScale k < p ∧ (p:ℝ) ≤ (octaveScale k)^24 :=
      mem_windowPrimes (octaveScale_pos k).le (pow_nonneg (octaveScale_pos k).le 24)
    have hdiv {a b : ℝ} (h : a ≤ b) : a/(J:ℝ) ≤ b/J :=
      div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
    exact ⟨band.2 ⟨hq',(below (by decide)).trans_lt hpl,hpu.trans top⟩,
      ⟨q,band.2 ⟨hq,hqL,(Nat.cast_le.mpr hqN).trans (hwU.trans top)⟩,
       r,band.2 ⟨hr,hqL.trans (Nat.cast_lt.mpr hqr),(Nat.cast_le.mpr hrN).trans (hwU.trans top)⟩,
       hqr,he⟩,(cell j hj).2.trans (hdiv hwL.le),(cell j hj).2.trans (hdiv hpl.le)⟩
  · change (1:ℝ)/1040 ≤ ∑ p ∈ D.image f, 1/(p:ℝ)
    rw [sum_image hinj]
    have dis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (W i) (W j) := fun i hi j hj h =>
      disjoint_left.mpr (fun _ hwi hwj => h (octave_unique (ends hi hwi) (ends hj hwj)))
    change 1/1040 ≤ ∑ w ∈ I.biUnion W, 1/(f w:ℝ)
    have hpw : (I : Set ℕ).PairwiseDisjoint W := by
      intro i hi j hj h
      exact dis i hi j hj h
    rw [sum_biUnion hpw]
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have row (j : ℕ) (hj : j ∈ I) : 1/(1040*(k:ℝ)) ≤ ∑ w ∈ W j, 1/(f w:ℝ) := by
      let t := octaveScale j
      have ht0 : 0 < t := octaveScale_pos _
      have hlt := Real.log_pos (by linarith only [htwo hj] : 1 < t)
      have hcount := hG t ((le_max_left _ _).trans ((le_max_right _ _).trans (base hj)))
      have htlog : Real.log t ≤ 2*(k:ℝ) := by
        change Real.log ((2:ℝ)^j) ≤ _
        rw [Real.log_pow]
        have hj' : (j:ℝ) ≤ 2*k := by exact_mod_cast (mem_Ico.mp hj).2.le
        have htwoLog : Real.log 2 ≤ 1 := by
          linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
        exact (mul_le_mul_of_nonneg_left htwoLog (Nat.cast_nonneg j)).trans (by simpa using hj')
      have hsum : ((W j).card:ℝ)*(1/(2*t^12)) ≤ ∑ w ∈ W j, 1/(f w:ℝ) := by
        calc _ = ∑ _w ∈ W j, 1/(2*t^12) := by simp
             _ ≤ _ := by
               apply sum_le_sum
               intro w hw
               rw [eval ⟨j,hj⟩ hw]
               exact one_div_le_one_div_of_le (by exact_mod_cast (primeEnds ⟨j,hj⟩ hw).1.pos)
                 (primeEnds ⟨j,hj⟩ hw).2.2
      calc 1/(1040*(k:ℝ)) ≤ 1/(520*Real.log t) := one_div_le_one_div_of_le
              (by positivity) (by linarith only [htlog])
           _ = (t^12/(260*Real.log t))*(1/(2*t^12)) := by field_simp [ht0.ne',hlt.ne']; ring
           _ ≤ _ := (mul_le_mul_of_nonneg_right hcount (by positivity)).trans hsum
    have rows := sum_le_sum row
    have hc : I.card=k := by simp only [I,Nat.card_Ico]; omega
    calc (1:ℝ)/1040 = (I.card:ℝ)*(1/(1040*k)) := by rw [hc]; field_simp [hk0.ne']
         _ = ∑ _j ∈ I, 1/(1040*(k:ℝ)) := by simp
         _ ≤ _ := rows

/-- Arbitrarily high disjoint prime ranges support near-equal, reversible
one-to-two local factors of fixed positive reciprocal mass. The mass bound
is independent of the requested relative displacement. -/
theorem eventually_positive_mass_short_exchanges (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ k : ℕ in atTop, ∃ f : ℕ → ℕ, IsShortExchange J k f ∧
      1/1040 ≤ ∑ p ∈ (switchProducts k).image f, 1/(p:ℝ) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [uniform_positive_mass_short_exchanges,eventually_ge_atTop ⌈(J:ℝ)/Real.log 2⌉₊]
    with k h hk
  exact h J hJ ((div_le_iff₀ hl).1 ((Nat.le_ceil _).trans (Nat.cast_le.mpr hk)))

#print axioms uniform_positive_mass_short_exchanges
#print axioms eventually_positive_mass_short_exchanges

end GaloisForLFunctions.RestrictedFactorizationCalculus
