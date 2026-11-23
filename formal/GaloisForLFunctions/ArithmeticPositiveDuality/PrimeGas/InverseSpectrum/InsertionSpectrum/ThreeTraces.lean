import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Germs

/-! # Three successive surviving spectra recover the native partition and the occupation heat -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Meromorphic continuation of the absolute partition of a physical omission. -/
abbrev survivingTrace (v : MissingWave) := survivingPartition (missingSpectrum v)

def insertionIncrement (a : ℕ+) (v : MissingWave) (z : ℂ) :=
  survivingTrace (insertMissing a v) z-survivingTrace v z

def traceCurvature (a : ℕ+) (v : MissingWave) (z : ℂ) :=
  insertionIncrement a (insertMissing a v) z-insertionIncrement a v z

def traceDeterminant (a : ℕ+) (v : MissingWave) (z : ℂ) :=
  survivingTrace v z*survivingTrace (insertMissing a (insertMissing a v)) z-survivingTrace (insertMissing a v) z^2

theorem insertionIncrement_eq (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    insertionIncrement a v z = (1-heat z a)*omissionPartition v z := by
  change (riemannZeta z-omissionPartition (insertMissing a v) z)-(riemannZeta z-omissionPartition v z) = _
  rw [omissionPartition_insert a v hz]
  ring

theorem insertionIncrement_insert (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    insertionIncrement a (insertMissing a v) z = heat z a*insertionIncrement a v z := by
  rw [insertionIncrement_eq _ _ hz,insertionIncrement_eq _ _ hz,omissionPartition_insert a v hz]
  ring

theorem traceCurvature_eq (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    traceCurvature a v z = -(1-heat z a)^2*omissionPartition v z := by
  rw [traceCurvature,insertionIncrement_insert a v hz,insertionIncrement_eq a v hz]
  ring

theorem traceDeterminant_eq (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    traceDeterminant a v z = riemannZeta z*traceCurvature a v z := by
  rw [traceCurvature_eq a v hz]
  change (riemannZeta z-omissionPartition v z)*(riemannZeta z-omissionPartition (insertMissing a (insertMissing a v)) z)-
    (riemannZeta z-omissionPartition (insertMissing a v) z)^2 = _
  rw [omissionPartition_insert a _ hz,omissionPartition_insert a v hz]
  ring

private theorem one_sub_heat_ne {a : ℕ+} (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) : 1-heat z a ≠ 0 := by
  have he : 0 < energy a := Real.log_pos (by exact_mod_cast ha)
  have h : ‖heat z a‖ < 1 := by rw [norm_heat,Real.exp_lt_one_iff]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hz) he
  intro hzero
  have heq := (sub_eq_zero.mp hzero).symm
  rw [heq,norm_one] at h
  exact lt_irrefl _ h

theorem omission_punctured_ne (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    ∀ᶠ w in 𝓝[≠] z, omissionPartition v w ≠ 0 :=
  (omissionPartition_analytic v z hz).meromorphicAt.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun h => omission_finite_order v hz (meromorphicOrderAt_eq_top_iff.mpr h))

private theorem right_punctured {z : ℂ} (hz : 0 < z.re) : {w : ℂ | 0 < w.re} ∈ 𝓝[≠] z :=
  mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

/-- The determinant divided by the second difference recovers the full zeta germ, including at common zeros and the pole. -/
theorem three_traces_zeta_germ (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) :
    (fun w => traceDeterminant a v w/traceCurvature a v w) =ᶠ[𝓝[≠] z] riemannZeta := by
  filter_upwards [right_punctured hz,omission_punctured_ne v hz] with w hw hv
  have hc : traceCurvature a v w ≠ 0 := by
    rw [traceCurvature_eq a v hw]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (one_sub_heat_ne ha hw))) hv
  exact (congrArg (fun t : ℂ => t/traceCurvature a v w) (traceDeterminant_eq a v hw)).trans (mul_div_cancel_right₀ _ hc)

/-- The same three surviving spectra recover the complex amplitude without an undeleted reference. -/
theorem three_traces_heat_germ (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) :
    (fun w => insertionIncrement a (insertMissing a v) w/insertionIncrement a v w) =ᶠ[𝓝[≠] z] fun w => heat w a := by
  filter_upwards [right_punctured hz,omission_punctured_ne v hz] with w hw hv
  have hi : insertionIncrement a v w ≠ 0 := by rw [insertionIncrement_eq a v hw]; exact mul_ne_zero (one_sub_heat_ne ha hw) hv
  rw [insertionIncrement_insert a v hw,mul_div_cancel_right₀ _ hi]

/-- At all points, the regularized determinant quotient has exactly the order of the native partition. -/
theorem three_traces_zeta_order (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (fun w => traceDeterminant a v w/traceCurvature a v w) z = meromorphicOrderAt riemannZeta z :=
  meromorphicOrderAt_congr (three_traces_zeta_germ a v ha hz)

/-- Multiplicity of a determinant zero separates into the native zeta order and the order of the omitted reading. -/
theorem traceDeterminant_order (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (traceDeterminant a v) z = meromorphicOrderAt riemannZeta z + meromorphicOrderAt (omissionPartition v) z := by
  let U (w : ℂ) := -(1-heat w a)^2
  have hU : AnalyticAt ℂ U z := ((analyticAt_const.sub (insertion_heat_analytic a z)).pow 2).neg
  have hne : U z ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 (one_sub_heat_ne ha hz))
  have he : traceDeterminant a v =ᶠ[𝓝[≠] z] riemannZeta*(U*omissionPartition v) := by
    filter_upwards [right_punctured hz] with w hw
    exact (traceDeterminant_eq a v hw).trans (congrArg (riemannZeta w * ·) (traceCurvature_eq a v hw))
  rw [meromorphicOrderAt_congr he,meromorphicOrderAt_mul (HTGeometry.meromorphicOn_riemannZeta z (Set.mem_univ z))
    (hU.mul (omissionPartition_analytic v z hz)).meromorphicAt,meromorphicOrderAt_mul_of_ne_zero hU hne]

#print axioms traceDeterminant_order
#print axioms insertionIncrement_eq
#print axioms insertionIncrement_insert
#print axioms traceCurvature_eq
#print axioms traceDeterminant_eq
#print axioms omission_punctured_ne
#print axioms three_traces_zeta_germ
#print axioms three_traces_heat_germ
#print axioms three_traces_zeta_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
