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
open _root_.RHTower

private theorem centeredAbelPrefix_zero_base (j : ℕ) :
    centeredAbelPrefix 0 j = Chebyshev.psi j-j := by
  have h := Sieve.psi_sub_eq_sum_Ioc (Nat.cast_nonneg (α := ℝ) j)
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
  simp only [div_eq_mul_inv] at *
  rw [hparts]
  have hD := Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < k by omega) : (0:ℝ) < k)
    (show (k:ℝ) ≤ L by exact_mod_cast hkL) hd.le.neg
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
      (by exact_mod_cast (show N ≤ b-1 by omega)) hd.le.neg) hB
  · have hJ := Finset.not_nonempty_iff_eq_empty.mp he
    change |∑ n ∈ J, _| ≤ _
    rw [hJ,Finset.sum_empty,abs_zero]
    exact mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- In translated coordinates the original late cutoff and the moving
critical edge retain the full reciprocal prime cancellation. -/
theorem reciprocal_past_critical_edge {d : ℝ} (hd : 0 < d) (hd' : d < 3001/24000) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (R v : ℝ) (L : ℕ), 1 ≤ R → v ≤ 0 →
      |∑ n ∈ (Finset.Ioc 0 L).filter (fun n => R < v+Real.log n ∧ pastCriticalEdge n (v+Real.log n)),
        (vonMangoldt n-1)/(n:ℝ)| ≤ B*(⌊Real.exp R⌋₊:ℝ)^(-d) := by
  classical
  obtain ⟨B,hB,hbound⟩ := centered_reciprocal_prime_intervals hd hd'
  refine ⟨B,hB,fun R v L hR hv => ?_⟩
  have he1 := Real.one_le_exp (zero_le_one.trans hR)
  apply reciprocal_on_terminal_set hd hB hbound (Nat.one_le_floor_iff.mpr he1)
  · intro n hn h
    have hlog : R < Real.log n := by linarith only [h.1,hv]
    exact (Nat.floor_lt (Real.exp_pos R).le).mpr ((Real.exp_lt_exp.mpr hlog).trans_eq
      (Real.exp_log (by exact_mod_cast hn)))
  · intro n j hn hnj h
    have hj := hn.trans_le hnj
    have hl := Real.log_le_log (by exact_mod_cast hn : (0:ℝ)<n)
      (by exact_mod_cast hnj : (n:ℝ) ≤ j)
    have ht : v+Real.log n ≤ v+Real.log j := add_le_add le_rfl hl
    refine ⟨h.1.trans_le ht,(pastCriticalEdge_at_shift hj v).mpr ?_⟩
    apply lt_of_le_of_lt _ ((pastCriticalEdge_at_shift hn v).mp h.2)
    exact add_le_add le_rfl (criticalRelativeWidth_antitone (hR.trans h.1.le) ht)

/-- Finite ordered complementary row, with the original signed coefficients. -/
def finiteCriticalComplementRow (Φ : ℝ → ℝ) (L : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 L, if pastCriticalEdge n t then
    (vonMangoldt n-1)*continuousIntegerAtom Φ n t else 0

private theorem lateComplement_time_translation {Φ : ℝ → ℝ}
    (hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v)
    {T R : ℝ} (hTR : T ≤ R) (L : ℕ) :
    let g := fun v : ℝ => Real.exp (-v/2)*Φ v
    let A := fun v : ℝ => (Finset.Ioc 0 L).filter (fun n => R < v+Real.log n ∧
      pastCriticalEdge n (v+Real.log n))
    IntegrableOn (fun t => finiteCriticalComplementRow Φ L t*fractionalPrimeTest (T-t)) (Ioi R) ∧
    (∫ t in Ioi R, finiteCriticalComplementRow Φ L t*fractionalPrimeTest (T-t)) =
      Real.exp (T/2)*(∫ v, g v*(∑ n ∈ A v, (vonMangoldt n-1)/(n:ℝ))) := by
  classical
  let I := Finset.Ioc 0 L
  let g := fun v : ℝ => Real.exp (-v/2)*Φ v
  let a := fun n : ℕ => (vonMangoldt n-1)/(n:ℝ)
  let S := fun n : ℕ => {v : ℝ | R < v+Real.log n ∧ pastCriticalEdge n (v+Real.log n)}
  let A := fun v : ℝ => I.filter (fun n => v ∈ S n)
  let G := fun n : ℕ => (S n).indicator (fun v : ℝ => g v*a n)
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_lt measurable_const (measurable_id.add_const _)).inter
      (measurableSet_lt (by dsimp only [pastCriticalEdge]; fun_prop) measurable_const)
  have hgi (n : ℕ) : Integrable (G n) := (hp.mul_const (a n)).indicator (hS n)
  have hsum (v : ℝ) : (∑ n ∈ I, G n v) = g v*∑ n ∈ A v, a n := by
    rw [Finset.mul_sum,Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by
      by_cases h : v ∈ S n <;> simp [G,Set.indicator,h]
  let f := fun t => finiteCriticalComplementRow Φ L t*fractionalPrimeTest (T-t)
  have hpoint : (Ioi R).indicator f = fun t => Real.exp (T/2)*
      ∑ n ∈ I, G n (t-Real.log n) := by
    funext t
    by_cases ht : R < t
    · rw [indicator_of_mem ht,Finset.mul_sum]
      dsimp only [f,finiteCriticalComplementRow]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
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
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T R : ℝ) (L : ℕ), 1 ≤ R → T ≤ R →
      |∫ t in Ioi R, finiteCriticalComplementRow Φ L t*fractionalPrimeTest (T-t)| ≤
        B*Real.exp (T/2)*(⌊Real.exp R⌋₊:ℝ)^(-d) := by
  classical
  let g := fun v : ℝ => Real.exp (-v/2)*Φ v
  obtain ⟨B,hB,h⟩ := reciprocal_past_critical_edge hd hd'
  refine ⟨B*(∫ v, |g v|),mul_nonneg hB (integral_nonneg fun _ => abs_nonneg _),fun T R L hR hTR => ?_⟩
  let A := fun v : ℝ => (Finset.Ioc 0 L).filter (fun n => R < v+Real.log n ∧
    pastCriticalEdge n (v+Real.log n))
  let H := B*(⌊Real.exp R⌋₊:ℝ)^(-d)
  have hab : |∫ v, g v*∑ n ∈ A v, (vonMangoldt n-1)/(n:ℝ)| ≤ H*(∫ v, |g v|) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hp.abs.const_mul H)
    apply Eventually.of_forall fun v => ?_
    change |g v*_ | ≤ H*|g v|
    rw [abs_mul,mul_comm H]
    rcases le_or_gt v 0 with hv | hv
    · exact mul_le_mul_of_nonneg_left (h R v L hR hv) (abs_nonneg _)
    · simp only [g,hs v hv.le,mul_zero,abs_zero,zero_mul]
  rw [(lateComplement_time_translation hp hTR L).2,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le).trans_eq
  dsimp only [H]; ring

#print axioms centered_reciprocal_prime_intervals
#print axioms reciprocal_past_critical_edge
#print axioms criticalComplement_late_bound
end GaloisForLFunctions.ExclusionOfTheCriticalState
