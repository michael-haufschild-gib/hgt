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

/-- Every polar scalar diagonal of size `o(c)` vanishes in the normalized terminal norm. -/
theorem tendsto_topWindow_polar_scalar_diagonal
    {δ : ℝ} (hδ : 0 < δ) {c d : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hd : Tendsto (fun N => d N / c N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N (d N • normalizedRamanujanHorizonVector 1 N))
      atTop (𝓝 0) := by
  have hlim := (hd.pow 2).const_mul (1 / δ)
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hN hL
  change 0 < Real.log (N : ℝ) at hL
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
        ((d N) ^ 2 * (1 / (δ * Real.log N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (sq_nonneg _)) (by positivity)
    _ = _ := by field_simp [hL.ne', (hc N).ne', hδ.ne']

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
  exact tendsto_topWindow_polar_scalar_diagonal hδ hc hd

/-- The completed ground conductor energy is also negligible in the normalized terminal row. -/
theorem tendsto_topWindow_completed_polar_diagonal
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N
      (completedConductorEnergy tiltedUnitSpline (c N) 1 • normalizedRamanujanHorizonVector 1 N))
      atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  let C := tiltedConductorUpperCoefficient 1
  have hC : 0 < C := tiltedConductorUpperCoefficient_pos one_pos
  have hlim : Tendsto (fun N : ℕ => C / c N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcinf
  apply tendsto_topWindow_polar_scalar_diagonal hδ hc0
  refine squeeze_zero (fun N => div_nonneg
    (completedConductorEnergy_tilted_pos (hc0 N) (by norm_num)).le (hc0 N).le) (fun N => ?_) hlim
  have hE : completedConductorEnergy tiltedUnitSpline (c N) 1 ≤ C :=
    (tiltedConductorEnergy_two_sided (m := 1) one_pos
      (by simpa only [Nat.cast_one] using hc N)).2.trans
        (div_le_self hC.le (one_le_pow₀ (hc N)))
  exact div_le_div_of_nonneg_right hE (hc0 N).le

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
