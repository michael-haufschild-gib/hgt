import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation

/-!
# Logarithmic polar reference diagonals vanish on terminal fractions

The finite self energy grows only as the overlap logarithm. After critical row
normalization its terminal-fraction square norm vanishes by `log c / c → 0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The polar logarithmic reference diagonal disappears in the normalized top-window square norm. -/
theorem tendsto_topWindow_polar_reference_diagonal
    (φ : ℝ → ℝ) (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        ((completeWeilSelfFinitePart φ (c N) + a) • normalizedRamanujanHorizonVector 1 N))
      atTop (𝓝 0) := by
  have hd : Tendsto (fun N : ℕ => (completeWeilSelfFinitePart φ (c N) + a) / c N)
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun N : ℕ => (completeWeilSelfFinitePart φ 1 + a) / c N)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcinf
    have ht := hdiv.sub (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcinf)
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    rw [completeWeilSelfFinitePart_eq_at_one_sub_log φ (hc N)]
    dsimp only [Function.comp_def, id]
    ring
  have hlim := (hd.pow 2).const_mul (1 / δ)
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hN hL
  have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) n ^ 2 =
        (1 / Real.log N) * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩⟩
    change primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) idx.1 ^ 2 = _
    rw [primeHorizonExtension_coe]
    change ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode 1 n / Real.sqrt n)) ^ 2 = _
    rw [normalizedRamanujanMode_one, mul_pow, div_pow, inv_pow,
      Real.sq_sqrt hn0.le, Real.sq_sqrt hL.le]
    ring
  have hm : topWindowResidualMass δ N (normalizedRamanujanHorizonVector 1 N) ≤
      1 / (δ * Real.log N) := by
    unfold topWindowResidualMass
    rw [sum_congr rfl hpt, ← mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_topWindow_inv_le hδ hN)
      (by positivity : 0 ≤ 1 / Real.log N)).trans_eq (by ring)
  rw [topWindowResidualMass_smul]
  calc
    _ ≤ (Real.log (N : ℝ) / c N ^ 2) *
        ((completeWeilSelfFinitePart φ (c N) + a) ^ 2 * (1 / (δ * Real.log N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (sq_nonneg _)) (by positivity)
    _ = _ := by field_simp [hL.ne', (hc N).ne', hδ.ne']

#print axioms tendsto_topWindow_polar_reference_diagonal
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
