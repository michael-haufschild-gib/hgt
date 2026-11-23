import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.ThreeTraces
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-! # Zeta zeros and the Born test from three surviving spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- The removable value of the ratio of successive increments, read from three surviving spectra. -/
def measuredInsertion (a : ℕ+) (v : MissingWave) (z : ℂ) :=
  meromorphicTrailingCoeffAt (fun w => insertionIncrement a (insertMissing a v) w/insertionIncrement a v w) z

theorem measuredInsertion_eq (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) :
    measuredInsertion a v z = heat z a := by
  rw [measuredInsertion,meromorphicTrailingCoeffAt_congr_nhdsNE (three_traces_heat_germ a v ha hz)]
  exact (insertion_heat_analytic a z).meromorphicTrailingCoeffAt_of_ne_zero (Complex.exp_ne_zero _)

theorem measuredInsertion_balance (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) :
    (a.val:ℝ)*‖measuredInsertion a v z‖^2 = 1 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x := by
  have hen : energy a ≠ 0 := (Real.log_pos (show (1:ℝ) < a.val by exact_mod_cast ha)).ne'
  rw [measuredInsertion_eq a v ha hz,← shellMass_eq,split_isometric_iff,shellMass,Real.exp_eq_one_iff,mul_eq_zero,or_iff_left hen]
  constructor <;> intro h <;> linarith only [h]

/-- A zero test using only the three continued surviving traces, even at a common zero of all three. -/
theorem three_traces_zero_iff (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) (h1 : z ≠ 1) :
    Tendsto (fun w => traceDeterminant a v w/traceCurvature a v w) (𝓝[≠] z) (𝓝 0) ↔ riemannZeta z = 0 := by
  have h := (three_traces_zeta_germ a v ha hz).symm
  have ht := ((HTGeometry.analyticAt_riemannZeta h1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' h
  constructor
  · intro h0
    exact tendsto_nhds_unique ht h0
  · intro h0
    rwa [← h0]

/-- For any fixed exterior wave and nontrivial insertion, RH is equivalent to the Born test at every vanishing reconstructed partition. -/
theorem rh_iff_three_trace_balance (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) :
    RiemannHypothesis ↔ ∀ z : ℂ, 0 < z.re → z.re < 1 →
      Tendsto (fun w => traceDeterminant a v w/traceCurvature a v w) (𝓝[≠] z) (𝓝 0) →
        (a.val:ℝ)*‖measuredInsertion a v z‖^2 = 1 := by
  constructor
  · intro rh z hz h1 hzero
    have hne : z ≠ 1 := fun h => (show ¬(1:ℝ)<1 from lt_irrefl _) (by simpa only [h,Complex.one_re] using h1)
    apply (measuredInsertion_balance a v ha hz).mpr
    apply (split_isometric_iff z).mpr
    apply rh z ((three_traces_zero_iff a v ha hz hne).mp hzero) _ hne
    rintro ⟨n,hn⟩
    rw [hn] at hz
    norm_num [Complex.mul_re] at hz
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro z hh h1 hzero
    have hz : 0 < z.re := by linarith only [hh]
    have hne : z ≠ 1 := fun he => (show ¬(1:ℝ)<1 from lt_irrefl _) (by simpa only [he,Complex.one_re] using h1)
    have hb := h z hz h1 ((three_traces_zero_iff a v ha hz hne).mpr hzero)
    exact hh.ne' ((split_isometric_iff z).mp ((measuredInsertion_balance a v ha hz).mp hb))

#print axioms measuredInsertion_eq
#print axioms measuredInsertion_balance
#print axioms three_traces_zero_iff
#print axioms rh_iff_three_trace_balance

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
