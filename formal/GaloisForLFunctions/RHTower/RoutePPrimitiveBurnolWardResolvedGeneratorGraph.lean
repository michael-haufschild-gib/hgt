import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardHerglotzTangent
import GaloisForLFunctions.RHTower.XiWardCubicPrimitiveTailRateNoGo

/-!
# Route P resolved Ward column / conormal-generator graph bridge

P-G197's one-mode positive tangent resolves a zero mode through the ordinary Hardy/Laplace
column `(w + lambda)⁻¹`.  The cubic completed-Xi conormal column is not another polarization of
that positive tangent: it is obtained by applying the common radial position generator `L ·`
before taking the Laplace transform.  Its transform is the squared resolvent and its Gram is the
cubic Cauchy kernel.

The generator is necessarily unbounded at the critical wall.  For a positive real rate `a`, its
base energy is `1/(2a)`, its graph energy is `1/(4a^3)`, and the exact gain is `1/(2a^2)`.
Consequently no uniform graph bound exists even on `0 < a ≤ 1/2`.  Thus the missing Route P map
must pay a coefficient-faithful polar--Gamma graph norm; P-G197 base-Hardy positivity alone cannot
provide W-H184's cubic zero Gram.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Radial exponential whose Laplace transform is P-G197's resolved Ward column. -/
def xiWardResolvedRadialMode (lam : ℂ) (L : ℝ) : ℂ :=
  Complex.exp (-(lam * (L : ℂ)))

/-- Common radial position generator applied to a resolved Ward mode. -/
def xiWardResolvedRadialGeneratorMode (lam : ℂ) (L : ℝ) : ℂ :=
  (L : ℂ) * xiWardResolvedRadialMode lam L

/-- P-G197's zero-aperture resolvent column is the Laplace transform of its radial mode. -/
theorem xiWardCayleyResolventColumn_zero_eq_radialMode_laplace
    {n : ℕ} (w : Fin n → ℂ) {lam : ℂ} (i : Fin n)
    (h : 0 < (w i + lam).re) :
    xiWardCayleyResolventColumn w lam 0 i () =
      ∫ L : ℝ in Ioi 0,
        Complex.exp (-(w i * (L : ℂ))) * xiWardResolvedRadialMode lam L := by
  have hint := integral_cauchyFeaturePair (a := w i + lam) h
  rw [xiWardCayleyResolventColumn]
  simp only [ofReal_zero, add_zero]
  rw [show (fun L : ℝ =>
      Complex.exp (-(w i * (L : ℂ))) * xiWardResolvedRadialMode lam L) =
      fun L : ℝ => Complex.exp (-((w i + lam) * (L : ℂ))) by
    funext L
    rw [xiWardResolvedRadialMode, ← Complex.exp_add]
    congr 1
    ring]
  simpa only [one_div, neg_mul] using hint.symm

/-- The common generator turns a resolved radial mode into the completed-Xi base conormal
feature at the shifted spectral point. -/
theorem xiWardResolvedRadialGeneratorMode_eq_routePXiBaseConormalResidueFeature
    (lam : ℂ) (L : ℝ) :
    xiWardResolvedRadialGeneratorMode lam L =
      routePXiBaseConormalResidueFeature (lam + 1 / 2) L := by
  rw [xiWardResolvedRadialGeneratorMode, xiWardResolvedRadialMode,
    routePXiBaseConormalResidueFeature]
  congr 1
  ring_nf

/-- The same generated mode is Burnol's inverse-window conormal feature. -/
theorem xiWardResolvedRadialGeneratorMode_eq_burnolWindowConormalFeature
    (lam : ℂ) (L : ℝ) :
    xiWardResolvedRadialGeneratorMode lam L =
      xiWardCubicBurnolWindowConormalFeature L (lam + 1 / 2) := by
  rw [xiWardCubicBurnolWindowConormalFeature_eq,
    xiWardResolvedRadialGeneratorMode_eq_routePXiBaseConormalResidueFeature]

/-- Every canonical primitive Burnol source column is a coefficient-weighted common-generator
mode, with its exact von Mangoldt depth amplitude retained. -/
theorem routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode
    (pe : Nat.Primes × ℕ) (kappa L : ℝ) :
    routePPrimitiveBurnolWindowFeature pe kappa L =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        xiWardResolvedRadialGeneratorMode
          ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)) L := by
  rw [routePPrimitiveBurnolWindowFeature,
    xiWardResolvedRadialGeneratorMode_eq_burnolWindowConormalFeature]
  congr 2
  rw [routePPrimitiveBurnolSpectralPoint]
  push_cast
  ring

/-- Cross-Gram of common-generator modes is exactly P-G181/P-G182's cubic Cauchy kernel. -/
theorem integral_star_xiWardResolvedRadialGeneratorMode_mul
    {lam mu : ℂ} (hlam : 0 < lam.re) (hmu : 0 < mu.re) :
    (∫ L : ℝ in Ioi 0,
      star (xiWardResolvedRadialGeneratorMode lam L) *
        xiWardResolvedRadialGeneratorMode mu L) =
      routePBaseCauchyCubicKernel 1 lam.re mu.re (mu.im - lam.im) := by
  have hlam' : 1 / 2 < (lam + 1 / 2).re := by simp; linarith
  have hmu' : 1 / 2 < (mu + 1 / 2).re := by simp; linarith
  simp_rw [xiWardResolvedRadialGeneratorMode_eq_routePXiBaseConormalResidueFeature]
  rw [integral_star_routePXiBaseConormalResidueFeature_mul hlam' hmu']
  simp

/-- After the common radial generator, the same Laplace reporter becomes the squared
resolvent. -/
theorem integral_xiWardResolvedRadialGeneratorMode_laplace
    {w lam : ℂ} (h : 0 < (w + lam).re) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-(w * (L : ℂ))) *
        xiWardResolvedRadialGeneratorMode lam L) =
      (w + lam)⁻¹ ^ 2 := by
  have hgamma :=
    GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi
      (s := (2 : ℂ)) (w := w + lam) (by norm_num) h
  have hfun : (fun L : ℝ =>
      Complex.exp (-(w * (L : ℂ))) *
        xiWardResolvedRadialGeneratorMode lam L) =
      fun L : ℝ => (L : ℂ) ^ ((2 : ℂ) - 1) *
        Complex.exp (-((w + lam) * (L : ℂ))) := by
    funext L
    rw [xiWardResolvedRadialGeneratorMode, xiWardResolvedRadialMode]
    norm_num
    calc
      Complex.exp (-(w * (L : ℂ))) *
          ((L : ℂ) * Complex.exp (-(lam * (L : ℂ)))) =
          (L : ℂ) * (Complex.exp (-(w * (L : ℂ))) *
            Complex.exp (-(lam * (L : ℂ)))) := by ring
      _ = (L : ℂ) * Complex.exp (-((w + lam) * (L : ℂ))) := by
        rw [← Complex.exp_add]
        congr 2
        ring
  rw [hfun, hgamma]
  have hGamma : Complex.Gamma (2 : ℂ) = 1 := by
    norm_num [Complex.Gamma_nat_eq_factorial]
  rw [hGamma, one_mul, Complex.cpow_neg, inv_pow]
  congr 1
  exact Complex.cpow_natCast (w + lam) 2

/-- The generator Laplace column is the negative derivative of P-G197's resolved column in its
zero-mode parameter. -/
theorem hasDerivAt_xiWard_resolvedColumn
    {w lam : ℂ} (hne : w + lam ≠ 0) :
    HasDerivAt (fun z : ℂ => 1 / (w + z)) (-1 / (w + lam) ^ 2) lam := by
  have hbase : HasDerivAt (fun z : ℂ => z + w) 1 lam :=
    (hasDerivAt_id lam).add_const w
  simpa only [one_div, one_mul, neg_div, add_comm] using!
    hbase.inv (by simpa only [add_comm] using hne)

/-- Pointwise squared norm of a positive real resolved radial mode. -/
theorem norm_xiWardResolvedRadialMode_sq
    (a L : ℝ) :
    ‖xiWardResolvedRadialMode (a : ℂ) L‖ ^ 2 = Real.exp (-2 * a * L) := by
  rw [xiWardResolvedRadialMode, Complex.norm_exp]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Pointwise squared norm after applying the common radial position generator. -/
theorem norm_xiWardResolvedRadialGeneratorMode_sq
    (a L : ℝ) :
    ‖xiWardResolvedRadialGeneratorMode (a : ℂ) L‖ ^ 2 =
      L ^ 2 * Real.exp (-2 * a * L) := by
  rw [xiWardResolvedRadialGeneratorMode, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, norm_xiWardResolvedRadialMode_sq]
  rw [sq_abs]

/-- Exact base `L²` energy of one positive real resolved Ward mode. -/
theorem integral_norm_xiWardResolvedRadialMode_sq
    {a : ℝ} (ha : 0 < a) :
    (∫ L : ℝ in Ioi 0, ‖xiWardResolvedRadialMode (a : ℂ) L‖ ^ 2) =
      1 / (2 * a) := by
  simp_rw [norm_xiWardResolvedRadialMode_sq]
  rw [integral_exp_mul_Ioi (by linarith : -2 * a < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ha.ne']

/-- Exact graph energy after applying the common radial position generator. -/
theorem integral_norm_xiWardResolvedRadialGeneratorMode_sq
    {a : ℝ} (ha : 0 < a) :
    (∫ L : ℝ in Ioi 0,
      ‖xiWardResolvedRadialGeneratorMode (a : ℂ) L‖ ^ 2) =
      1 / (4 * a ^ 3) := by
  simp_rw [norm_xiWardResolvedRadialGeneratorMode_sq]
  rw [integral_Ioi_sq_mul_exp_neg_two_mul ha (le_refl 0)]
  rw [xiWardCubicConormalTailEnergy]
  norm_num

/-- Exact graph-norm amplification converting P-G197's base Hardy mode into P-G182's cubic
conormal mode. -/
theorem xiWardResolvedRadialGenerator_energy_ratio
    {a : ℝ} (ha : 0 < a) :
    (∫ L : ℝ in Ioi 0,
      ‖xiWardResolvedRadialGeneratorMode (a : ℂ) L‖ ^ 2) /
        (∫ L : ℝ in Ioi 0, ‖xiWardResolvedRadialMode (a : ℂ) L‖ ^ 2) =
      1 / (2 * a ^ 2) := by
  rw [integral_norm_xiWardResolvedRadialGeneratorMode_sq ha,
    integral_norm_xiWardResolvedRadialMode_sq ha]
  field_simp [ha.ne']
  ring

/-- The generator gain is arbitrarily large inside the strict-right zero-rate chamber. -/
theorem exists_xiWardResolvedRadialGenerator_gain_gt
    (C : ℝ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ C < 1 / (2 * a ^ 2) := by
  let u : ℝ := |C| + 1
  let a : ℝ := 1 / (2 * u)
  have hu : 0 < u := by dsimp [u]; linarith [abs_nonneg C]
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, ha, ?_, ?_⟩
  · dsimp [a]
    have hu1 : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg C]
    exact (div_le_iff₀ (by positivity : 0 < 2 * u)).2 (by nlinarith)
  · have hgain : 1 / (2 * a ^ 2) = 2 * u ^ 2 := by
      dsimp [a]
      field_simp [hu.ne']
    rw [hgain]
    have hC : C ≤ |C| := le_abs_self C
    have hsq : 0 ≤ |C| ^ 2 := sq_nonneg |C|
    dsimp [u]
    nlinarith

/-- No uniform bounded operator on the base Hardy carrier can perform the common radial
generator required for the cubic conormal landing, even when restricted to `0 < a ≤ 1/2`. -/
theorem not_exists_uniform_xiWardResolvedRadialGenerator_energy_bound :
    ¬ ∃ C : ℝ, ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
      (∫ L : ℝ in Ioi 0,
        ‖xiWardResolvedRadialGeneratorMode (a : ℂ) L‖ ^ 2) ≤
      C * (∫ L : ℝ in Ioi 0,
        ‖xiWardResolvedRadialMode (a : ℂ) L‖ ^ 2) := by
  rintro ⟨C, hC⟩
  obtain ⟨a, ha, hahalf, hgain⟩ :=
    exists_xiWardResolvedRadialGenerator_gain_gt C
  have hbound := hC a ha hahalf
  rw [integral_norm_xiWardResolvedRadialGeneratorMode_sq ha,
    integral_norm_xiWardResolvedRadialMode_sq ha] at hbound
  have hbase : 0 < 1 / (2 * a) := by positivity
  have hratio : 1 / (2 * a ^ 2) ≤ C := by
    rw [← xiWardResolvedRadialGenerator_energy_ratio ha]
    rw [integral_norm_xiWardResolvedRadialGeneratorMode_sq ha,
      integral_norm_xiWardResolvedRadialMode_sq ha]
    exact (div_le_iff₀ hbase).2 hbound
  linarith

end

end RHTower
