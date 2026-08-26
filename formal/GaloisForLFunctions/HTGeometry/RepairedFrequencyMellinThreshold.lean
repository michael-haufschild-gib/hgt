import GaloisForLFunctions.HTGeometry.RepairedFrequencyDxOverXLaw
import GaloisForLFunctions.HTGeometry.NearZeroTruncatedPower

/-!
# Exact Mellin threshold of the repaired-frequency source

The `dx/x` law reduces every positive Mellin exponent to the already formalized near-zero
integrability criterion for a real power.  The zero exponent is the existing local-infinity
theorem; negative exponents dominate a positive constant times that infinite mass.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

/-- Nonnegative real Mellin power as an `ℝ≥0∞` weight. -/
def positiveMellinWeight (q x : ℝ) : ENNReal := ENNReal.ofReal (x ^ q)

theorem measurable_positiveMellinWeight (q : ℝ) : Measurable (positiveMellinWeight q) := by
  unfold positiveMellinWeight
  fun_prop

/-- Every positive Mellin power is locally integrable against `dx/x`. -/
theorem positiveMultiplicativeHaar_mellin_ne_top {q delta : ℝ}
    (hq : 0 < q) (_hdelta : 0 < delta) :
    (∫⁻ x in Ioo 0 delta, positiveMellinWeight q x ∂positiveMultiplicativeHaar) ≠ ⊤ := by
  rw [positiveMultiplicativeHaar]
  have hinv : Measurable (fun x : ℝ => ENNReal.ofReal x⁻¹) := by fun_prop
  rw [setLIntegral_withDensity_eq_setLIntegral_mul (volume.restrict (Ioi 0))
    hinv (measurable_positiveMellinWeight q) measurableSet_Ioo]
  change (∫⁻ x, ENNReal.ofReal x⁻¹ * positiveMellinWeight q x
    ∂(volume.restrict (Ioi 0)).restrict (Ioo 0 delta)) ≠ ⊤
  rw [Measure.restrict_restrict_of_subset (fun _ hx => hx.1)]
  have hint : IntegrableOn (fun x : ℝ => x ^ (q - 1)) (Ioo 0 delta) volume :=
    integrableOn_rpow_Ioo_zero (by linarith)
  have heq : (fun x : ℝ => ENNReal.ofReal x⁻¹ * positiveMellinWeight q x)
      =ᵐ[volume.restrict (Ioo 0 delta)] fun x => ENNReal.ofReal (x ^ (q - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [positiveMellinWeight, ← ENNReal.ofReal_mul (inv_nonneg.2 hx.1.le),
      Real.rpow_sub_one hx.1.ne' q]
    congr 1
    field_simp
  rw [lintegral_congr_ae heq]
  exact hint.lintegral_lt_top.ne

theorem source_positiveMellin_lintegral_ne_top
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R delta q : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (hpos : nu (Ioi 0) ≠ 0) (hdelta : 0 < delta) (hq : 0 < q)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu) :
    (∫⁻ x in Ioo 0 delta, positiveMellinWeight q x ∂mu) ≠ ⊤ := by
  refine (source_weighted_lintegral_ne_top_iff hR hsupp hpos hdelta hmu hmomInt hmom
    (measurable_positiveMellinWeight q)).2 ?_
  exact positiveMultiplicativeHaar_mellin_ne_top hq hdelta

theorem source_measure_Ioo_eq_top
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R delta : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (hpos : nu (Ioi 0) ≠ 0) (hdelta : 0 < delta)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu) :
    mu (Ioo 0 delta) = ⊤ := by
  obtain ⟨eta, heta, hmass⟩ := exists_pos_measure_Ici_of_measure_Ioi_ne_zero hpos
  exact measure_Ioo_eq_top_of_shiftedFactorialMoments hR hsupp heta hmass hmu hmomInt hmom hdelta

theorem source_negativeMellin_lintegral_eq_top
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R delta q : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (hpos : nu (Ioi 0) ≠ 0) (hdelta : 0 < delta) (hq : q < 0)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu) :
    (∫⁻ x in Ioo 0 delta, positiveMellinWeight q x ∂mu) = ⊤ := by
  have hmass := source_measure_Ioo_eq_top hR hsupp hpos hdelta hmu hmomInt hmom
  have hle : (∫⁻ _x in Ioo 0 delta, ENNReal.ofReal (delta ^ q) ∂mu)
      ≤ ∫⁻ x in Ioo 0 delta, positiveMellinWeight q x ∂mu := by
    refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
    rw [positiveMellinWeight]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hx.1 hx.2.le hq.le)
  have hc0 : ENNReal.ofReal (delta ^ q) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (Real.rpow_pos_of_pos hdelta q)
  rw [MeasureTheory.setLIntegral_const, hmass, ENNReal.mul_top hc0] at hle
  exact top_unique hle

/-- **Exact zero-frequency Mellin threshold.**  Positive exponents are finite, exponent zero has
infinite mass, and every negative exponent has infinite lower integral. -/
theorem source_exact_localMellin_threshold
    {nu : Measure ℝ} [IsFiniteMeasure nu]
    {R delta : ℝ} (hR : 0 < R) (hsupp : ∀ᵐ y ∂nu, y ∈ Icc 0 R)
    (hpos : nu (Ioi 0) ≠ 0) (hdelta : 0 < delta)
    {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmomInt : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (n + 1)) mu)
    (hmom : ∀ n : ℕ, (∫ x, x ^ (n + 1) ∂mu)
      = (Nat.factorial (2 * n + 1) : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) ∂nu) :
    (∀ q : ℝ, 0 < q → (∫⁻ x in Ioo 0 delta, positiveMellinWeight q x ∂mu) ≠ ⊤) ∧
      mu (Ioo 0 delta) = ⊤ ∧
      ∀ q : ℝ, q < 0 → (∫⁻ x in Ioo 0 delta, positiveMellinWeight q x ∂mu) = ⊤ := by
  refine ⟨?_, source_measure_Ioo_eq_top hR hsupp hpos hdelta hmu hmomInt hmom, ?_⟩
  · intro q hq
    exact source_positiveMellin_lintegral_ne_top
      hR hsupp hpos hdelta hq hmu hmomInt hmom
  · intro q hq
    exact source_negativeMellin_lintegral_eq_top
      hR hsupp hpos hdelta hq hmu hmomInt hmom

end

end GaloisForLFunctions.HTGeometry
