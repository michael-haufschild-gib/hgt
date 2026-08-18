import GaloisForLFunctions.RHTower.SuzukiEulerPoleArchimedeanMomentAnnihilation
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac

/-!
# Suzuki's completed tail is exactly the shifted-Euler summatory error transform

For `ω > 0` put `c_ω(n) = n^ω ∏_{p ∣ n} (1 - p^{-2ω})`, `A_ω(X) = ∑_{n ≤ X} c_ω(n)`,
`r_ω = 1/ζ(1+2ω)`, `M_ω(X) = r_ω X^{1+ω}/(1+ω)` and `E_ω = A_ω - M_ω`.

The Stieltjes measure of `A_ω` is the atomic measure `dA_ω = ∑ₙ c_ω(n) δₙ`, and the Stieltjes
measure of `M_ω` is the absolutely continuous measure `r_ω t^ω dt`.  Both facts are proved here as
exact interval-mass identities, so the signed Stieltjes integral against `dE_ω` is well defined.

The theorem of this module is the exact error-transform identity

`h_ω^{⟨1⟩}(x) = x^{-1} ∫_{(0,x]} g_ω^{⟨1⟩}(t/x) dE_ω(t)`,

valid for every `x > 1`.  Its content is that the smooth main term contributes nothing: the
archimedean moment `∫₀¹ g_ω^{⟨1⟩}(u) u^ω du` vanishes, so the positive average size of the Euler
coefficients has been projected out exactly and every sign-bearing contribution to Suzuki's
completed causal source lies in the arithmetic summatory error `E_ω`.
-/

namespace RHTower

noncomputable section

open Complex Filter Topology Set MeasureTheory

/-! ## Real-argument summatory data -/

/-- The summatory function `A_ω(X) = ∑_{n ≤ X} c_ω(n)` at a real argument. -/
def suzukiShiftedSummatoryReal (ω X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, suzukiShiftedCoefficient ω n

/-- The Euler density constant `r_ω = 1/ζ(1+2ω)`. -/
def suzukiEulerDensityConstant (ω : ℝ) : ℝ :=
  1 / (riemannZeta (((1 + 2 * ω : ℝ) : ℂ))).re

/-- The main-term density `dM_ω/dt = r_ω t^ω`. -/
def suzukiMainTermDensity (ω t : ℝ) : ℝ := suzukiEulerDensityConstant ω * t ^ ω

/-- The main term `M_ω(X) = r_ω X^{1+ω}/(1+ω)` at a real argument. -/
def suzukiMainTermReal (ω X : ℝ) : ℝ :=
  suzukiEulerDensityConstant ω * X ^ (1 + ω) / (1 + ω)

/-- The coupled summatory error `E_ω(X) = A_ω(X) - M_ω(X)` at a real argument. -/
def suzukiCoupledErrorReal (ω X : ℝ) : ℝ :=
  suzukiShiftedSummatoryReal ω X - suzukiMainTermReal ω X

theorem suzukiShiftedSummatoryReal_natCast (ω : ℝ) (N : ℕ) :
    suzukiShiftedSummatoryReal ω (N : ℝ) = suzukiShiftedSummatory ω N := by
  rw [suzukiShiftedSummatoryReal, suzukiShiftedSummatory, Nat.floor_natCast]

theorem suzukiMainTermReal_natCast (ω : ℝ) (N : ℕ) :
    suzukiMainTermReal ω (N : ℝ) = suzukiMainTerm ω N := by
  rw [suzukiMainTermReal, suzukiMainTerm, suzukiEulerDensityConstant, one_div,
    div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

theorem suzukiCoupledErrorReal_natCast (ω : ℝ) (N : ℕ) :
    suzukiCoupledErrorReal ω (N : ℝ) = suzukiCoupledError ω N := by
  rw [suzukiCoupledErrorReal, suzukiCoupledError, suzukiShiftedSummatoryReal_natCast,
    suzukiMainTermReal_natCast]

/-! ## The atomic Stieltjes measure of the summatory function -/

/-- The Stieltjes measure `dA_ω = ∑ₙ c_ω(n) δₙ` of the shifted-Euler summatory function. -/
def suzukiShiftedAtomicMeasure (ω : ℝ) : Measure ℝ :=
  HTGeometry.countableWeightedDirac (suzukiShiftedCoefficient ω) (fun n : ℕ => (n : ℝ))

/-- The shifted Euler coefficients are nonnegative. -/
theorem suzukiShiftedCoefficient_nonneg {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    0 ≤ suzukiShiftedCoefficient ω n := by
  rw [suzukiShiftedCoefficient]
  refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ω) ?_
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 : (2 : ℕ) ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp2
  have hlt : (p : ℝ) ^ (-2 * ω) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith

/-- The natural numbers lying in `(0, X]` are exactly `1, …, ⌊X⌋`. -/
theorem natCast_mem_Ioc_zero_iff {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    ((n : ℝ) ∈ Ioc (0 : ℝ) X) ↔ n ∈ Finset.Icc 1 ⌊X⌋₊ := by
  simp only [mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨h0, h1⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at h0
    exact ⟨Nat.one_le_iff_ne_zero.mpr hn0, Nat.le_floor h1⟩
  · rintro ⟨h0, h1⟩
    have hnpos : 0 < n := h0
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    refine ⟨hpos, ?_⟩
    calc (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ X := Nat.floor_le hX

/-- The atomic measure restricted to `(0, x]` is the finite sum of its visible atoms. -/
theorem suzukiShiftedAtomicMeasure_restrict_Ioc (ω : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (suzukiShiftedAtomicMeasure ω).restrict (Ioc 0 x)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (ENNReal.ofReal (suzukiShiftedCoefficient ω n)) • Measure.dirac (n : ℝ) := by
  ext s hs
  rw [Measure.restrict_apply hs, suzukiShiftedAtomicMeasure,
    HTGeometry.countableWeightedDirac_apply _ _ (hs.inter measurableSet_Ioc),
    Measure.finsetSum_apply]
  refine (tsum_eq_sum ?_).trans (Finset.sum_congr rfl ?_)
  · intro n hn
    have hnot : (n : ℝ) ∉ Ioc (0 : ℝ) x := fun h => hn ((natCast_mem_Ioc_zero_iff hx n).1 h)
    rw [Set.indicator_of_notMem (fun h => hnot h.2)]
    simp
  · intro n hn
    have hmem : (n : ℝ) ∈ Ioc (0 : ℝ) x := (natCast_mem_Ioc_zero_iff hx n).2 hn
    rw [Measure.smul_apply, Measure.dirac_apply' _ hs]
    by_cases hns : (n : ℝ) ∈ s
    · rw [Set.indicator_of_mem (show (n : ℝ) ∈ s ∩ Ioc (0 : ℝ) x from ⟨hns, hmem⟩),
        Set.indicator_of_mem hns, smul_eq_mul]
    · rw [Set.indicator_of_notMem (fun h => hns h.1), Set.indicator_of_notMem hns, smul_eq_mul]

/-- **Equation (6).**  Integration against the atomic Stieltjes measure over `(0,x]` is the
truncated arithmetic sum. -/
theorem integral_suzukiShiftedAtomicMeasure_Ioc {ω : ℝ} (hω : 0 < ω) {x : ℝ} (hx : 0 ≤ x)
    (f : ℝ → ℂ) :
    ∫ t in Ioc (0 : ℝ) x, f t ∂(suzukiShiftedAtomicMeasure ω)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((suzukiShiftedCoefficient ω n : ℝ) : ℂ) * f (n : ℝ) := by
  have hint : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      Integrable f ((ENNReal.ofReal (suzukiShiftedCoefficient ω n)) • Measure.dirac (n : ℝ)) :=
    fun n _ => (integrable_dirac (f := f) (a := (n : ℝ)) (by simp)).smul_measure
      ENNReal.ofReal_ne_top
  rw [suzukiShiftedAtomicMeasure_restrict_Ioc ω hx, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (suzukiShiftedCoefficient_nonneg hω n), Complex.real_smul]

/-- **The atomic measure is the Stieltjes measure of `A_ω`.**  Its mass on an interval is the
increment of the summatory function. -/
theorem suzukiShiftedAtomicMeasure_Ioc {ω : ℝ} (hω : 0 < ω) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    suzukiShiftedAtomicMeasure ω (Ioc a b)
      = ENNReal.ofReal (suzukiShiftedSummatoryReal ω b - suzukiShiftedSummatoryReal ω a) := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hIccIoc : ∀ m : ℕ, Finset.Icc 1 m = Finset.Ioc 0 m := by
    intro m
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum : suzukiShiftedSummatoryReal ω b - suzukiShiftedSummatoryReal ω a
      = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, suzukiShiftedCoefficient ω n := by
    rw [suzukiShiftedSummatoryReal, suzukiShiftedSummatoryReal, hIccIoc, hIccIoc,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊a⌋₊) hfloor]
    ring
  rw [hsum, suzukiShiftedAtomicMeasure,
    HTGeometry.countableWeightedDirac_apply _ _ measurableSet_Ioc,
    tsum_eq_sum (s := Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) ?_]
  · rw [ENNReal.ofReal_sum_of_nonneg fun n _ => suzukiShiftedCoefficient_nonneg hω n]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hmem : (n : ℝ) ∈ Ioc a b := by
      simp only [Finset.mem_Ioc] at hn
      refine ⟨(Nat.floor_lt ha).1 hn.1, ?_⟩
      calc (n : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast hn.2
        _ ≤ b := Nat.floor_le (le_trans ha hab)
    rw [Set.indicator_of_mem hmem]
    simp
  · intro n hn
    simp only [Finset.mem_Ioc, not_and_or, not_le, not_lt] at hn
    have hnot : (n : ℝ) ∉ Ioc a b := by
      rcases hn with h | h
      · intro hmem
        exact absurd ((Nat.floor_lt ha).2 hmem.1) (not_lt.2 h)
      · intro hmem
        exact absurd (Nat.le_floor hmem.2) (not_le.2 h)
    rw [Set.indicator_of_notMem hnot]
    simp

/-! ## The absolutely continuous Stieltjes measure of the main term -/

/-- **The density `r_ω t^ω` is the Stieltjes density of `M_ω`.** -/
theorem integral_suzukiMainTermDensity_Ioc {ω : ℝ} (hω : 0 < ω) {a b : ℝ}
    (_ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t in Ioc a b, suzukiMainTermDensity ω t
      = suzukiMainTermReal ω b - suzukiMainTermReal ω a := by
  have hpow : ∫ t in a..b, t ^ ω = (b ^ (ω + 1) - a ^ (ω + 1)) / (ω + 1) :=
    integral_rpow (Or.inl (by linarith))
  have hset : (∫ t in Ioc a b, suzukiMainTermDensity ω t)
      = ∫ t in a..b, suzukiEulerDensityConstant ω * t ^ ω := by
    rw [intervalIntegral.integral_of_le hab]
    simp only [suzukiMainTermDensity]
  rw [hset, intervalIntegral.integral_const_mul, hpow,
    suzukiMainTermReal, suzukiMainTermReal, show (1 : ℝ) + ω = ω + 1 by ring]
  field_simp

/-! ## The exact error transform -/

/-- The signed Stieltjes integral of `f` against `dE_ω = dA_ω - dM_ω` over `(0, x]`. -/
def suzukiCoupledErrorStieltjes (ω x : ℝ) (f : ℝ → ℂ) : ℂ :=
  (∫ t in Ioc (0 : ℝ) x, f t ∂(suzukiShiftedAtomicMeasure ω)) -
    ∫ t in Ioc (0 : ℝ) x, ((suzukiMainTermDensity ω t : ℝ) : ℂ) * f t

/-- The dilated `ω`-moment of the once-integrated kernel vanishes on the half-line. -/
theorem integral_rpow_mul_suzukiSourceGOne_dilate_eq_zero
    {ω : ℝ} (hω : 0 < ω) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((ω : ℝ) : ℂ) * suzukiSourceGOne ω (t / x) = 0 := by
  have hinv : (0 : ℝ) < 1 / x := by positivity
  have hdil := mellin_comp_mul_left (suzukiSourceGOne ω) (suzukiEulerPolePoint ω) hinv
  rw [mellin_suzukiSourceGOne_at_eulerPole hω, smul_zero, mellin] at hdil
  refine Eq.trans ?_ hdil
  apply integral_congr_ae
  filter_upwards with t
  rw [smul_eq_mul]
  congr 2
  · rw [suzukiEulerPolePoint]
    push_cast
    ring
  · rw [one_div, inv_mul_eq_div]

/-- **Equation (7).**  The smooth main term contributes nothing to the completed source: the
`ω`-moment of the once-integrated archimedean kernel vanishes. -/
theorem integral_suzukiMainTermDensity_mul_suzukiSourceGOne_eq_zero
    {ω : ℝ} (hω : 0 < ω) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioc (0 : ℝ) x, ((suzukiMainTermDensity ω t : ℝ) : ℂ) *
        suzukiSourceGOne ω (t / x) = 0 := by
  have hIoi := integral_rpow_mul_suzukiSourceGOne_dilate_eq_zero hω hx
  have hkey : ∫ t in Ioc (0 : ℝ) x, (t : ℂ) ^ ((ω : ℝ) : ℂ) * suzukiSourceGOne ω (t / x) = 0 := by
    refine Eq.trans ?_ hIoi
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht0 : 0 < t
    · by_cases htx : t ≤ x
      · rw [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) x from ⟨ht0, htx⟩),
          Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht0)]
      · have hone : (1 : ℝ) ≤ t / x := (one_le_div hx).2 (le_of_not_ge htx)
        rw [Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) x from fun h => htx h.2),
          Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht0),
          suzukiSourceGOne_eq_zero_of_one_le ω hone, mul_zero]
    · rw [Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) x from fun h => ht0 h.1),
        Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from fun h => ht0 h)]
  have hrw : (∫ t in Ioc (0 : ℝ) x, ((suzukiMainTermDensity ω t : ℝ) : ℂ) *
        suzukiSourceGOne ω (t / x))
      = ∫ t in Ioc (0 : ℝ) x, ((suzukiEulerDensityConstant ω : ℝ) : ℂ) *
          ((t : ℂ) ^ ((ω : ℝ) : ℂ) * suzukiSourceGOne ω (t / x)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [suzukiMainTermDensity]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le]
    ring
  rw [hrw, integral_const_mul, hkey, mul_zero]

/-- **The error-transform identity.**  For every `x > 1`, Suzuki's completed causal primitive is
exactly the Stieltjes transform of the shifted-Euler summatory error. -/
theorem suzukiSourceHOneFinite_eq_coupledErrorStieltjes
    {ω : ℝ} (hω : 0 < ω) {x : ℝ} (hx : 1 < x) :
    suzukiSourceHOneFinite ω x
      = (x : ℂ)⁻¹ * suzukiCoupledErrorStieltjes ω x (fun t => suzukiSourceGOne ω (t / x)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [suzukiCoupledErrorStieltjes,
    integral_suzukiShiftedAtomicMeasure_Ioc hω hx0.le,
    integral_suzukiMainTermDensity_mul_suzukiSourceGOne_eq_zero hω hx0,
    sub_zero, suzukiSourceHOneFinite, if_pos hx, one_div]

/-- The same identity for the series form of Suzuki's completed causal primitive. -/
theorem suzukiSourceHOne_eq_coupledErrorStieltjes
    {ω : ℝ} (hω : 0 < ω) {x : ℝ} (hx : 1 < x) :
    suzukiSourceHOne ω x
      = (x : ℂ)⁻¹ * suzukiCoupledErrorStieltjes ω x (fun t => suzukiSourceGOne ω (t / x)) := by
  rw [suzukiSourceHOne_eq_finite, suzukiSourceHOneFinite_eq_coupledErrorStieltjes hω hx]

end

end RHTower
