import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheRemoteVariationOfTheStateWeights
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Signed integer rows past the time cutoff

In the exponential part of the original test, translation by the particle
abscissa leaves reciprocal centered Mangoldt weights. Their ordered interval
sums are uniformly small at both endpoints.
-/

noncomputable section
open MeasureTheory Filter Set Topology ArithmeticFunction
open scoped Classical
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations _root_.RHTower

private theorem centeredAbelPrefix_zero_base (j : ℕ) :
    centeredAbelPrefix 0 j = Chebyshev.psi j-j := by
  have h := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc (Nat.cast_nonneg (α := ℝ) j)
  simp only [Chebyshev.psi_zero,sub_zero,Nat.floor_zero,Nat.floor_natCast] at h
  rw [centeredAbelPrefix,Finset.sum_sub_distrib,← h,Finset.sum_const,Nat.card_Ioc,
    Nat.sub_zero,nsmul_eq_mul,mul_one]

/-- Concavity of the power d majorizes the reciprocal Abel cost by a
telescoping difference at consecutive positive real abscissae. -/
private theorem reciprocal_power_step {d x : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hx : 1 ≤ x) :
    x^(1-d)*(x⁻¹-(x+1)⁻¹) ≤ (x^(-d)-(x+1)^(-d))/d := by
  have hx0 := zero_lt_one.trans_le hx
  have hx1 : 0 < x+1 := by linarith only [hx]
  have hBern := rpow_one_add_le_one_add_mul_self (s := -(x+1)⁻¹)
    (by have h := inv_le_one_of_one_le₀ (by linarith only [hx] : 1 ≤ x+1); linarith only [h]) hd.le hd1
  rw [show 1 + -(x+1)⁻¹ = x/(x+1) by field_simp; ring,Real.div_rpow hx0.le hx1.le] at hBern
  have hmult := mul_le_mul_of_nonneg_left hBern (Real.rpow_nonneg hx0.le (-d))
  have hcancel : x^(-d)*(x^d/(x+1)^d)=(x+1)^(-d) := by
    rw [← mul_div_assoc,← Real.rpow_add hx0,neg_add_cancel,Real.rpow_zero,Real.rpow_neg hx1.le,one_div]
  rw [hcancel] at hmult
  have hleft : x^(1-d)*(x⁻¹-(x+1)⁻¹) = x^(-d)*(x+1)⁻¹ := by
    rw [sub_eq_add_neg (1:ℝ),Real.rpow_add hx0,Real.rpow_one]
    field_simp [hx0.ne',hx1.ne']; ring
  rw [hleft,le_div_iff₀ hd]
  linarith only [hmult]

/-- All ordered reciprocal prime-excess tails above a given starting index
have a uniform power saving from the unconditional zero-free strip. -/
theorem centered_reciprocal_prime_intervals {d : ℝ} (hd : 0 < d) (hd' : d < 3001/24000) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k L : ℕ, 1 ≤ k → k ≤ L →
      |∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)/(n:ℝ)| ≤ B*(k:ℝ)^(-d) := by
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun q => by
    by_contra! hq
    exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hq
      (riemannZeta_eq_zero_of_xiZeroCopy q)
  obtain ⟨C,hC,hE⟩ := exists_abs_chebyshevPsi_sub_le_rpow
    (by linarith only [hd',hΘ] : zeroReSup < 1-d)
  have hd1 : d ≤ 1 := by linarith only [hd']
  let D := fun n : ℕ => (n:ℝ)^(-d)
  let P := centeredAbelPrefix 0
  have herr (j : ℕ) (hj : 1 ≤ j) : |P j| ≤ C*(j:ℝ)^(1-d) := by
    rw [show P j=Chebyshev.psi j-j from centeredAbelPrefix_zero_base j]
    exact hE j (by exact_mod_cast hj)
  have hend (j : ℕ) (hj : 1 ≤ j) : |(j:ℝ)⁻¹*P j| ≤ C*D j := by
    have hj0 : (0:ℝ) < j := by exact_mod_cast hj
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hj0.le)]
    apply (mul_le_mul_of_nonneg_left (herr j hj) (inv_nonneg.mpr hj0.le)).trans_eq
    have heq : (j:ℝ)^(1-d) = j*D j := by
      rw [sub_eq_add_neg,Real.rpow_add hj0,Real.rpow_one]
    rw [heq]; field_simp
  have hcost (j : ℕ) (hj : 1 ≤ j) :
      |P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹)| ≤ (C/d)*(D j-D (j+1)) := by
    have hj0 : (0:ℝ) < j := by exact_mod_cast hj
    have hdec : 0 ≤ (j:ℝ)⁻¹-((j:ℝ)+1)⁻¹ := sub_nonneg.mpr
      ((inv_le_inv₀ (by positivity) hj0).2 (le_add_of_nonneg_right zero_le_one))
    rw [Nat.cast_add_one,abs_mul,abs_of_nonneg hdec]
    apply (mul_le_mul_of_nonneg_right (herr j hj) hdec).trans
    have h := mul_le_mul_of_nonneg_left (reciprocal_power_step hd hd1
      (show (1:ℝ) ≤ j by exact_mod_cast hj)) hC
    simpa only [D,Nat.cast_add_one,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
  refine ⟨2*C+C/d,by positivity,fun k L hk hkL => ?_⟩
  have hsum : ∑ j ∈ Finset.Ico k L, |P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹)| ≤ (C/d)*(D k-D L) := by
    induction L, hkL using Nat.le_induction with
    | base => simp
    | succ L hL ih =>
      rw [Finset.sum_Ico_succ_top hL]
      linarith only [add_le_add ih (hcost L (hk.trans hL))]
  have hparts := centeredAbelPrefix_by_parts (fun j : ℕ => (j:ℝ)⁻¹) (Nat.zero_le k) hkL
  simp only [div_eq_mul_inv]
  rw [hparts]
  rw [div_eq_mul_inv C d] at hsum
  have hD := Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < k by omega) : (0:ℝ) < k)
    (show (k:ℝ) ≤ L by exact_mod_cast hkL) (neg_nonpos.mpr hd.le)
  have hA := abs_add_le ((L:ℝ)⁻¹*P L-(k:ℝ)⁻¹*P k)
    (∑ j ∈ Finset.Ico k L, P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹))
  have hB := abs_sub ((L:ℝ)⁻¹*P L) ((k:ℝ)⁻¹*P k)
  have hS := Finset.abs_sum_le_sum_abs (fun j : ℕ => P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹)) (Finset.Ico k L)
  have hDL : 0 ≤ D L := Real.rpow_nonneg (Nat.cast_nonneg _) _
  change D L ≤ D k at hD
  linarith only [hA,hB,hS,hsum,hend k hk,hend L (hk.trans hkL),
    mul_le_mul_of_nonneg_left hD hC,mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hd.le)) hDL]

private theorem criticalRelativeWidth_antitone {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    Real.exp (-t/2)*Real.sqrt t ≤ Real.exp (-s/2)*Real.sqrt s := by
  have hs0 := zero_le_one.trans hs
  have ht0 := hs0.trans hst
  have hgrow : t ≤ s*Real.exp (t-s) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t-s)) hs0
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hst)]
  have ht' := mul_le_mul_of_nonneg_right hgrow (Real.exp_pos (-t)).le
  rw [mul_assoc,← Real.exp_add,show t-s + -t = -s by ring] at ht'
  have hsq (x : ℝ) (hx : 0 ≤ x) : (Real.exp (-x/2)*Real.sqrt x)^2 = x*Real.exp (-x) := by
    rw [mul_pow,Real.sq_sqrt hx,pow_two,← Real.exp_add,show -x/2 + -x/2 = -x by ring,mul_comm]
  have h := (hsq t ht0).trans_le (ht'.trans_eq (hsq s hs0).symm)
  exact le_of_sq_le_sq h (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))

/-- The integer lies beyond the complete critical window at time t. -/
def pastCriticalEdge (n : ℕ) (t : ℝ) : Prop :=
  Real.exp t + Real.exp (t/2)*Real.sqrt t < n

private theorem measurableSet_pastCriticalEdge (n : ℕ) : MeasurableSet {t | pastCriticalEdge n t} :=
  measurableSet_lt (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t)
    measurable_const

private theorem pastCriticalEdge_at_shift {n : ℕ} (hn : 0 < n) (v : ℝ) :
    pastCriticalEdge n (v+Real.log n) ↔
      1+Real.exp (-(v+Real.log n)/2)*Real.sqrt (v+Real.log n) < Real.exp (-v) := by
  let t := v+Real.log n
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn' : Real.exp t*Real.exp (-v) = n := by
    rw [← Real.exp_add,show t + -v = Real.log n by dsimp only [t]; ring,Real.exp_log hn0]
  have hh : Real.exp t*Real.exp (-t/2) = Real.exp (t/2) := by rw [← Real.exp_add]; congr 1; ring
  change Real.exp t + Real.exp (t/2)*Real.sqrt t < n ↔ _
  calc Real.exp t + Real.exp (t/2)*Real.sqrt t < n ↔
      Real.exp t*(1+Real.exp (-t/2)*Real.sqrt t)<Real.exp t*Real.exp (-v) := by
        rw [hn',mul_add,mul_one,← mul_assoc,hh]
    _ ↔ _ := mul_lt_mul_iff_right₀ (Real.exp_pos t)

/-- At a fixed translated state coordinate, every surviving finite row past
the time cutoff and the far edge is a terminal interval of integers. -/
private theorem reciprocal_on_terminal_set {d B : ℝ} (hd : 0 < d) (hB : 0 ≤ B)
    (hbound : ∀ k L : ℕ, 1 ≤ k → k ≤ L →
      |∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)/(n:ℝ)| ≤ B*(k:ℝ)^(-d))
    {N L : ℕ} (hN : 1 ≤ N) (P : ℕ → Prop) [DecidablePred P]
    (hlow : ∀ n, 0 < n → P n → N < n) (hup : ∀ n j, 0 < n → n ≤ j → P n → P j) :
    |∑ n ∈ (Finset.Ioc 0 L).filter P, (vonMangoldt n-1)/(n:ℝ)| ≤ B*(N:ℝ)^(-d) := by
  let J := (Finset.Ioc 0 L).filter P
  by_cases he : J.Nonempty
  · let b := J.min' he
    have hb : b ∈ J := Finset.min'_mem _ _
    obtain ⟨hI,hP⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb0,hbL⟩ := Finset.mem_Ioc.mp hI
    have hNb := hlow b hb0 hP
    have heq : J=Finset.Ioc (b-1) L := by
      ext n
      constructor
      · intro hn
        have hbn : b ≤ n := Finset.min'_le _ _ hn
        exact Finset.mem_Ioc.mpr ⟨by omega,(Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2⟩
      · intro hn
        obtain ⟨hdiff,hnL⟩ := Finset.mem_Ioc.mp hn
        have hbn : b ≤ n := by omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hb0.trans_le hbn,hnL⟩,hup b n hb0 hbn hP⟩
    change |∑ n ∈ J, _| ≤ _
    rw [heq]
    apply (hbound (b-1) L (by omega) (by omega)).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN : (0:ℝ)<N)
      (by exact_mod_cast (show N ≤ b-1 by omega)) (neg_nonpos.mpr hd.le)) hB
  · have hJ := Finset.not_nonempty_iff_eq_empty.mp he
    change |∑ n ∈ J, _| ≤ _
    rw [hJ,Finset.sum_empty,abs_zero]
    exact mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Both the time cutoff and an independent integer cutoff survive translation
as lower endpoints of a single reciprocal prime interval. -/
theorem reciprocal_past_critical_edge {d : ℝ} (hd : 0 < d) (hd' : d < 3001/24000) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (R v : ℝ) (k L : ℕ), 1 ≤ R → v ≤ 0 →
      |∑ n ∈ (Finset.Ioc k L).filter (fun n : ℕ => R < v+Real.log n ∧ pastCriticalEdge n (v+Real.log n)),
        (vonMangoldt n-1)/(n:ℝ)| ≤ B*((max k ⌊Real.exp R⌋₊ : ℕ):ℝ)^(-d) := by
  classical
  obtain ⟨B,hB,hbound⟩ := centered_reciprocal_prime_intervals hd hd'
  refine ⟨B,hB,fun R v k L hR hv => ?_⟩
  let P := fun n : ℕ => R < v+Real.log n ∧ pastCriticalEdge n (v+Real.log n)
  have heq : (Finset.Ioc k L).filter P = (Finset.Ioc 0 L).filter (fun n => k < n ∧ P n) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hn,hnL⟩,hp⟩
      exact ⟨⟨(Nat.zero_le k).trans_lt hn,hnL⟩,hn,hp⟩
    · rintro ⟨⟨_,hnL⟩,hn,hp⟩
      exact ⟨⟨hn,hnL⟩,hp⟩
  change |∑ n ∈ (Finset.Ioc k L).filter P, _| ≤ _
  rw [heq]
  have he1 := Real.one_le_exp (zero_le_one.trans hR)
  apply reciprocal_on_terminal_set hd hB hbound
    (((Nat.one_le_floor_iff _).mpr he1).trans (le_max_right k _))
  · rintro n hn ⟨hkn,ht,_⟩
    have hlog : R < Real.log n := by linarith only [ht,hv]
    exact max_lt hkn ((Nat.floor_lt (Real.exp_pos R).le).mpr ((Real.exp_lt_exp.mpr hlog).trans_eq
      (Real.exp_log (by exact_mod_cast hn))))
  · rintro n j hn hnj ⟨hkn,hRtime,hedge⟩
    have hj := hn.trans_le hnj
    have hl := Real.log_le_log (by exact_mod_cast hn : (0:ℝ)<n)
      (by exact_mod_cast hnj : (n:ℝ) ≤ j)
    have ht : v+Real.log n ≤ v+Real.log j := add_le_add le_rfl hl
    refine ⟨hkn.trans_le hnj,hRtime.trans_le ht,(pastCriticalEdge_at_shift hj v).mpr ?_⟩
    apply lt_of_le_of_lt _ ((pastCriticalEdge_at_shift hn v).mp hedge)
    exact add_le_add le_rfl (criticalRelativeWidth_antitone (hR.trans hRtime.le) ht)

/-- Ordered complementary integer band at the original moving edge. -/
def finiteCriticalComplementBand (Φ : ℝ → ℝ) (k L : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc k L, if pastCriticalEdge n t then
    (vonMangoldt n-1)*continuousIntegerAtom Φ n t else 0

/-- Complete finite row from the first integer through L. -/
def finiteCriticalComplementRow (Φ : ℝ → ℝ) (L : ℕ) : ℝ → ℝ :=
  finiteCriticalComplementBand Φ 0 L

private theorem lateComplement_time_translation {Φ : ℝ → ℝ}
    (hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v)
    {T R : ℝ} (hTR : T ≤ R) (k L : ℕ) :
    let g := fun v : ℝ => Real.exp (-v/2)*Φ v
    let A := fun v : ℝ => (Finset.Ioc k L).filter (fun n : ℕ => R < v+Real.log n ∧
      pastCriticalEdge n (v+Real.log n))
    IntegrableOn (fun t => finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)) (Ioi R) ∧
    (∫ t in Ioi R, finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)) =
      Real.exp (T/2)*(∫ v, g v*(∑ n ∈ A v, (vonMangoldt n-1)/(n:ℝ))) := by
  classical
  let I := Finset.Ioc k L
  let g := fun v : ℝ => Real.exp (-v/2)*Φ v
  let a := fun n : ℕ => (vonMangoldt n-1)/(n:ℝ)
  let S := fun n : ℕ => {v : ℝ | R < v+Real.log n ∧ pastCriticalEdge n (v+Real.log n)}
  let A := fun v : ℝ => I.filter (fun n => v ∈ S n)
  let G := fun n : ℕ => (S n).indicator (fun v : ℝ => g v*a n)
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_lt measurable_const (measurable_id.add_const _)).inter
      ((measurableSet_pastCriticalEdge n).preimage (measurable_id.add_const _))
  have hgi (n : ℕ) : Integrable (G n) := (hp.mul_const (a n)).indicator (hS n)
  have hsum (v : ℝ) : (∑ n ∈ I, G n v) = g v*∑ n ∈ A v, a n := by
    rw [Finset.mul_sum,Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by
      by_cases h : v ∈ S n <;> simp [G,h]
  let f := fun t => finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)
  have hpoint : (Ioi R).indicator f = fun t => Real.exp (T/2)*
      ∑ n ∈ I, G n (t-Real.log n) := by
    funext t
    by_cases ht : t ∈ Ioi R
    · rw [indicator_of_mem ht,Finset.mul_sum]
      dsimp only [f,finiteCriticalComplementBand]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0:ℝ)<n := by exact_mod_cast (Nat.zero_le k).trans_lt (Finset.mem_Ioc.mp hn).1
      have hshift : t-Real.log n+Real.log n=t := sub_add_cancel ..
      have hmem : t-Real.log n ∈ S n ↔ pastCriticalEdge n t := by
        dsimp only [S,mem_setOf_eq]; rw [hshift]; exact and_iff_right ht
      by_cases hedge : pastCriticalEdge n t
      · rw [if_pos hedge,show G n (t-Real.log n)=g (t-Real.log n)*a n from indicator_of_mem (hmem.mpr hedge) _]
        have hneg := sub_neg.mpr (hTR.trans_lt ht)
        have hk : fractionalPrimeTest (T-t) = Real.exp ((T-t)/2) := by
          rw [fractionalPrimeTest,Int.fract_eq_self.mpr ⟨(Real.exp_pos _).le,Real.exp_lt_one_iff.mpr hneg⟩,
            ← Real.exp_add]; congr 1; ring
        have hsqrt : (Real.sqrt n)⁻¹ = Real.exp (-(Real.log n)/2) := by
          rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log hn0]
        have hex : Real.exp (-(Real.log n)/2)*Real.exp ((T-t)/2)*(n:ℝ) =
            Real.exp (T/2)*Real.exp (-(t-Real.log n)/2) := by
          conv_lhs => rhs; rw [← Real.exp_log hn0]
          rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; congr 1; ring
        rw [hk,continuousIntegerAtom,hsqrt]
        dsimp only [g,a]; field_simp [hn0.ne']
        linear_combination (vonMangoldt n-1)*Φ (t-Real.log n)*hex
      · rw [if_neg hedge,zero_mul,show G n (t-Real.log n)=0 from indicator_of_notMem
          (fun h => hedge (hmem.mp h)) _,mul_zero]
    · rw [indicator_of_notMem ht]
      symm
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero fun n _ => ?_
      apply indicator_of_notMem
      intro h
      apply ht
      have hlt := h.1
      simpa only [sub_add_cancel] using hlt
  have hshiftInt (n : ℕ) : Integrable (fun t : ℝ => G n (t-Real.log n)) :=
    (hgi n).comp_sub_right _
  have hi : Integrable ((Ioi R).indicator f) := by
    rw [hpoint]; exact (integrable_finsetSum _ fun n _ => hshiftInt n).const_mul _
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).mp hi,?_⟩
  change (∫ t in Ioi R, f t)=Real.exp (T/2)*(∫ v, g v*∑ n ∈ A v, a n)
  rw [← integral_indicator measurableSet_Ioi,hpoint,integral_const_mul,
    integral_finsetSum _ (fun n _ => hshiftInt n)]
  simp_rw [integral_sub_right_eq_self,← hsum]
  rw [integral_finsetSum _ (fun n _ => hgi n)]

/-- Exponentially small late signed cost, uniformly in the ordered upper
integer endpoint. The cutoff follows the actual moving far edge at every time. -/
theorem criticalComplement_late_bound {Φ : ℝ → ℝ}
    (hs : ∀ v, 0 ≤ v → Φ v=0)
    (hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v) {d : ℝ} (hd : 0 < d)
    (hd' : d < 3001/24000) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T R : ℝ) (k L : ℕ), 1 ≤ R → T ≤ R →
      |∫ t in Ioi R, finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)| ≤
        B*Real.exp (T/2)*((max k ⌊Real.exp R⌋₊ : ℕ):ℝ)^(-d) := by
  classical
  let g := fun v : ℝ => Real.exp (-v/2)*Φ v
  obtain ⟨B,hB,h⟩ := reciprocal_past_critical_edge hd hd'
  refine ⟨B*(∫ v, |g v|),mul_nonneg hB (integral_nonneg fun _ => abs_nonneg _),fun T R k L hR hTR => ?_⟩
  let A := fun v : ℝ => (Finset.Ioc k L).filter (fun n : ℕ => R < v+Real.log n ∧
    pastCriticalEdge n (v+Real.log n))
  let H := B*((max k ⌊Real.exp R⌋₊ : ℕ):ℝ)^(-d)
  have hab : |∫ v, g v*∑ n ∈ A v, (vonMangoldt n-1)/(n:ℝ)| ≤ H*(∫ v, |g v|) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hp.abs.const_mul H)
    apply Eventually.of_forall fun v => ?_
    change |g v*(∑ n ∈ A v, (vonMangoldt n-1)/(n:ℝ))| ≤ H*|g v|
    rw [abs_mul,mul_comm H]
    rcases le_or_gt v 0 with hv | hv
    · exact mul_le_mul_of_nonneg_left (h R v k L hR hv) (abs_nonneg _)
    · simp only [g,hs v hv.le,mul_zero,abs_zero,zero_mul]
  rw [(lateComplement_time_translation hp hTR k L).2,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le).trans_eq
  dsimp only [H]; ring

/-- The signed cost past the test center is uniform in both integer
endpoints and the terminal time. -/
theorem criticalComplement_late_band_interval {Φ : ℝ → ℝ}
    (hs : ∀ v, 0 ≤ v → Φ v=0) (hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v)
    {d : ℝ} (hd : 0 < d) (hd' : d < 3001/24000) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T M : ℝ) (k L : ℕ), 1 ≤ k → 1 ≤ T → T ≤ M →
      let f := fun t => finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)
      IntegrableOn f (Ioc T M) ∧ |∫ t in Ioc T M, f t| ≤ B*Real.exp (T/2)*(k:ℝ)^(-d) := by
  obtain ⟨B,hB,h⟩ := criticalComplement_late_bound hs hp hd hd'
  refine ⟨2*B,by positivity,fun T M k L hk hT hTM => ?_⟩
  let f := fun t => finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)
  have hi : IntegrableOn f (Ioi T) := (lateComplement_time_translation hp le_rfl k L).1
  have hi' : IntegrableOn f (Ioc T M) := hi.mono_set (fun _ hx => hx.1)
  have hsplit : (∫ t in Ioc T M, f t)+(∫ t in Ioi M, f t)=∫ t in Ioi T, f t := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi'
      (hi.mono_set (Ioi_subset_Ioi hTM)),Ioc_union_Ioi_eq_Ioi hTM]
  have hR (R : ℝ) (hTR : T ≤ R) : |∫ t in Ioi R, f t| ≤ B*Real.exp (T/2)*(k:ℝ)^(-d) := by
    apply (h T R k L (hT.trans hTR) hTR).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Real.exp_pos _).le)
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hk : (0:ℝ)<k)
      (by exact_mod_cast (le_max_left k ⌊Real.exp R⌋₊)) (neg_nonpos.mpr hd.le)
  refine ⟨hi',?_⟩
  change |∫ t in Ioc T M, f t| ≤ _
  rw [eq_sub_of_add_eq hsplit]
  exact (abs_sub _ _).trans ((add_le_add (hR T le_rfl) (hR M hTM)).trans_eq (by ring))

/-- Infinite prime-excess tail satisfying both lower cutoffs. -/
def criticalComplementBand (Φ : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, if k < n ∧ pastCriticalEdge n t then (vonMangoldt n-1)*continuousIntegerAtom Φ n t else 0

/-- Infinite complementary row through all positive integers. -/
def criticalComplementRow (Φ : ℝ → ℝ) : ℝ → ℝ := criticalComplementBand Φ 0

theorem finiteCriticalComplementBand_on_bounded_cut {Φ : ℝ → ℝ} (hc : Continuous Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) (k : ℕ) (R M T : ℝ) :
    Tendsto (fun L : ℕ => ∫ t in Ioc R M, finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t))
      atTop (𝓝 (∫ t in Ioc R M, criticalComplementBand Φ k t*fractionalPrimeTest (T-t))) := by
  let w := fun (n : ℕ) (t : ℝ) => if k < n ∧ pastCriticalEdge n t then
    (vonMangoldt n-1)*continuousIntegerAtom Φ n t else 0
  let a := fun n : ℕ => (Real.log n/(n:ℝ)^2 + 1/(n:ℝ)^2)
  let D := C*Real.exp (2*M)
  have hD : 0 ≤ D := mul_nonneg hC (Real.exp_pos _).le
  have ha : Summable a := GaloisForLFunctions.summable_log_nat_div_sq.add
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hapos (n : ℕ) : 0 ≤ a n :=
    add_nonneg (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _)) (by positivity)
  have hwm (n : ℕ) : Measurable (w n) := by
    dsimp only [w]
    exact Measurable.ite ((MeasurableSet.const _).inter (measurableSet_pastCriticalEdge n))
      (measurable_const.mul (measurable_const.mul (hc.measurable.comp (measurable_id.sub_const _))))
      measurable_const
  have hw (n : ℕ) (t : ℝ) (ht : t ≤ M) : |w n t| ≤ D*a n := by
    dsimp only [w]
    split_ifs
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [continuousIntegerAtom,a]
      · have hcoeff : |vonMangoldt n-1| ≤ Real.log n+1 := by
          apply (abs_sub _ _).trans
          rw [abs_of_nonneg vonMangoldt_nonneg,abs_one]
          exact add_le_add vonMangoldt_le_log le_rfl
        have hex : C*Real.exp (2*t) ≤ D := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith only [ht])) hC
        rw [abs_mul]
        calc _ ≤ (Real.log n+1)*(D*(1/(n:ℝ)^2)) := mul_le_mul hcoeff
              ((continuousIntegerAtom_bound hb (by exact_mod_cast hn : (1:ℝ) ≤ n) t).trans
                (mul_le_mul_of_nonneg_right hex (by positivity))) (abs_nonneg _)
                  (add_nonneg (Real.log_natCast_nonneg n) zero_le_one)
          _ = _ := by dsimp only [a]; ring
    · rw [abs_zero]; exact mul_nonneg hD (hapos n)
  have hrepr (L : ℕ) (t : ℝ) : finiteCriticalComplementBand Φ k L t =
      ∑ n ∈ Finset.range (L+1), w n t := by
    have hI : Finset.Ioc k L = (Finset.range (L+1)).filter (fun n => k < n) := by
      ext n
      simp only [Finset.mem_Ioc,Finset.mem_filter,Finset.mem_range]
      omega
    rw [finiteCriticalComplementBand,hI,Finset.sum_filter]
    apply Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : k < n <;> simp [w,hn]
  have hi (L : ℕ) : Measurable (finiteCriticalComplementBand Φ k L) := by
    rw [funext (hrepr L)]
    exact Finset.measurable_sum _ (fun n _ => hwm n)
  have hfin : volume (Ioc R M) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => D*(∑' n, a n))
    (fun L => ((hi L).mul (measurable_fractionalPrimeTest.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable)
    (integrableOn_const hfin)
  · intro L
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := R) (b := M))] with t ht
    rw [Real.norm_eq_abs,abs_mul]
    apply (mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1).trans
    rw [hrepr]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [← tsum_mul_left]
    apply (Finset.sum_le_sum (fun n _ => hw n t ht.2)).trans
    exact (ha.mul_left D).sum_le_tsum _ (fun n _ => mul_nonneg hD (hapos n))
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := R) (b := M))] with t ht
    have hs : Summable (fun n => w n t) := Summable.of_norm_bounded (ha.mul_left D)
      (fun n => hw n t ht.2)
    have hl := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    apply (hl.congr (fun L => ?_)).mul_const (fractionalPrimeTest (T-t))
    exact (hrepr L t).symm

/-- The whole infinite complementary row on every late portion of the original
test. The time endpoint M is arbitrary, and the integer series has already
been summed before integration. -/
theorem riemannHypothesis_or_late_critical_complement : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), ArithmeticHodgeTheoryOfDegenerations.windowThreshold a) = (W₀ : EReal) ∧
      ArithmeticHodgeTheoryOfDegenerations.IsCriticalHalfLineGroundState W₀ F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ (T M : ℝ), 1 ≤ T → 6*T ≤ M →
        |(∫ v, Φ v)*(∫ t in Ioc (6*T) M, criticalComplementRow Φ t*fractionalPrimeTest (T-t))| ≤
          B*Real.exp (-T/10) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hdr := ArithmeticHodgeTheoryOfDegenerations.criticalHalfLineEnergyDomain_of_groundState hF
  have hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v := by
    apply (integrable_mul_exp_of_domain hdr (by norm_num : (-4:ℝ)< -1/2)).congr
    filter_upwards [he] with v hv
    rw [hv,show (-1/2:ℝ)*v = -v/2 by ring,mul_comm]
  obtain ⟨B,hB,h⟩ := criticalComplement_late_bound hs hp (by norm_num : (0:ℝ)<1/10) (by norm_num)
  let m := ∫ v, Φ v
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,2*|m| *B*(2:ℝ)^(1/10:ℝ),by positivity,fun T M hT hM => ?_⟩
  let R := 6*T
  have hR : 1 ≤ R := by dsimp only [R]; linarith only [hT]
  have hTR : T ≤ R := by dsimp only [R]; linarith only [hT]
  have hflo (x : ℝ) (hx : R ≤ x) : Real.exp (T/2)*(⌊Real.exp x⌋₊:ℝ)^(-(1/10:ℝ)) ≤
      (2:ℝ)^(1/10:ℝ)*Real.exp (-T/10) := by
    have hX : 2 ≤ Real.exp x := by linarith only [Real.add_one_le_exp x,hR,hx]
    have hfl : Real.exp R/2 ≤ (⌊Real.exp x⌋₊:ℝ) := by
      linarith only [Nat.lt_floor_add_one (Real.exp x),Real.exp_le_exp.mpr hx,hX]
    have hpow := Real.rpow_le_rpow_of_nonpos (half_pos (Real.exp_pos R)) hfl (by norm_num : -(1/10:ℝ) ≤ 0)
    apply (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le).trans_eq
    rw [Real.div_rpow (Real.exp_pos R).le (by norm_num : (0:ℝ)≤2),← Real.exp_mul,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
    rw [show Real.exp (T/2)*(Real.exp (R*(-(1/10:ℝ)))*2^(1/10:ℝ))=
      2^(1/10:ℝ)*(Real.exp (T/2)*Real.exp (R*(-(1/10:ℝ)))) by ring,← Real.exp_add]
    congr 2; dsimp only [R]; ring
  have hL (L : ℕ) : |m*(∫ t in Ioc R M, finiteCriticalComplementRow Φ L t*fractionalPrimeTest (T-t))| ≤
      2*|m| *B*(2:ℝ)^(1/10:ℝ)*Real.exp (-T/10) := by
    let f := fun t => finiteCriticalComplementRow Φ L t*fractionalPrimeTest (T-t)
    have hi := (lateComplement_time_translation hp hTR 0 L).1
    have hsplit : (∫ t in Ioc R M, f t)+(∫ t in Ioi M, f t)=∫ t in Ioi R, f t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hi.mono_set (fun _ hx => hx.1)) (hi.mono_set (Ioi_subset_Ioi hM)),Ioc_union_Ioi_eq_Ioi hM]
    have htail (x : ℝ) (hx : R ≤ x) : |∫ t in Ioi x, f t| ≤ B*((2:ℝ)^(1/10:ℝ)*Real.exp (-T/10)) :=
      (show |∫ t in Ioi x, f t| ≤ B*Real.exp (T/2)*(⌊Real.exp x⌋₊:ℝ)^(-(1/10:ℝ)) by
        simpa only [Nat.zero_max] using h T x 0 L (hR.trans hx) (hTR.trans hx)).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hflo x hx) hB)
    change |m*(∫ t in Ioc R M, f t)| ≤ _
    rw [eq_sub_of_add_eq hsplit,abs_mul]
    apply (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg m)).trans
    have both := add_le_add (htail R le_rfl) (htail M hM)
    apply (mul_le_mul_of_nonneg_left both (abs_nonneg m)).trans_eq
    ring
  have hl := (finiteCriticalComplementBand_on_bounded_cut hc hC hb 0 R M T).const_mul m
  exact le_of_tendsto hl.abs (Eventually.of_forall hL)

#print axioms centered_reciprocal_prime_intervals
#print axioms reciprocal_past_critical_edge
#print axioms criticalComplement_late_bound
#print axioms riemannHypothesis_or_late_critical_complement
end GaloisForLFunctions.ExclusionOfTheCriticalState
