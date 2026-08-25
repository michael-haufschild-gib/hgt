import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import GaloisForLFunctions.HTGeometry.GaussianL2Tail
import GaloisForLFunctions.HTGeometry.GaussianCovarianceStableRankLowerTail
import GaloisForLFunctions.HTGeometry.GaussianAffineStableRankLowerTail
import GaloisForLFunctions.RHTower.GaussianAffineHermitianPencilSpectralActionLaw
import GaloisForLFunctions.RHTower.GaussianScaledAffineHermitianPencilSpectralActionLaw
import GaloisForLFunctions.RHTower.StaticChoiOscillationActionCarrierLaw
import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedOscillationQuantitativeLaw

/-!
# Growing-replica Gaussian pseudodeterminant law

Exact affine Gaussian Laplace products retain every observer singular value.
Combined with replica centralizer suppression, they give an incidence-normalized
quenched bound for complete weighted circuit images on the same local-Hamiltonian
draws that carry certified laboratory complexity growth.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal


namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integral_exp_neg_mul_sq_gaussianReal (a : ℝ) (_ha : 0 < a + 1 / 2) :
    ∫ x : ℝ, Real.exp (-a * x ^ 2) ∂gaussianReal 0 1 =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (a + 1 / 2)) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun x => by
        rw [gaussianPDF_def]
        exact ENNReal.ofReal_ne_top.lt_top)]
  rw [gaussianPDF_def]
  simp_rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul]
  have hpoint : ∀ x : ℝ,
      gaussianPDFReal 0 1 x * Real.exp (-a * x ^ 2) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(a + 1 / 2) * x ^ 2) := by
    intro x
    unfold gaussianPDFReal
    norm_num
    rw [mul_assoc]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (-a * x ^ 2)) =
      fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(a + 1 / 2) * x ^ 2) by funext x; exact hpoint x]
  rw [integral_const_mul, integral_gaussian]

theorem integral_exp_neg_mul_sq_sub_gaussianReal
    (a b : ℝ) (ha : 0 ≤ a) :
    ∫ x : ℝ, Real.exp (-a * (x - b) ^ 2) ∂gaussianReal 0 1 =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(a * b ^ 2 / (2 * (a + 1 / 2)))) *
          Real.sqrt (Real.pi / (a + 1 / 2)) := by
  have hq : 0 < a + 1 / 2 := by linarith
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun x => by
        rw [gaussianPDF_def]
        exact ENNReal.ofReal_ne_top.lt_top)]
  rw [gaussianPDF_def]
  simp_rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul]
  let m := a * b / (a + 1 / 2)
  have hpoint : ∀ x : ℝ,
      gaussianPDFReal 0 1 x * Real.exp (-a * (x - b) ^ 2) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(a * b ^ 2 / (2 * (a + 1 / 2)))) *
            Real.exp (-(a + 1 / 2) * (x - m) ^ 2) := by
    intro x
    have hpdf : gaussianPDFReal 0 1 x =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
      unfold gaussianPDFReal
      norm_num
    rw [hpdf]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [m]
    field_simp
    ring
  rw [show (fun x : ℝ => gaussianPDFReal 0 1 x *
      Real.exp (-a * (x - b) ^ 2)) =
      fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(a * b ^ 2 / (2 * (a + 1 / 2)))) *
          Real.exp (-(a + 1 / 2) * (x - m) ^ 2) by
        funext x; exact hpoint x]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun x : ℝ => Real.exp (-(a + 1 / 2) * x ^ 2)) m]
  rw [integral_gaussian]

theorem integral_exp_neg_mul_sq_sub_gaussianReal_le
    (a b : ℝ) (ha : 0 ≤ a) :
    ∫ x : ℝ, Real.exp (-a * (x - b) ^ 2) ∂gaussianReal 0 1 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (a + 1 / 2)) := by
  rw [integral_exp_neg_mul_sq_sub_gaussianReal a b ha]
  have hexp : Real.exp (-(a * b ^ 2 / (2 * (a + 1 / 2)))) ≤ 1 := by
    have hden : 0 ≤ 2 * (a + 1 / 2) := by positivity
    calc
      Real.exp (-(a * b ^ 2 / (2 * (a + 1 / 2)))) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr
          (neg_nonpos.mpr (div_nonneg (mul_nonneg ha (sq_nonneg b)) hden))
      _ = 1 := Real.exp_zero
  have hleft : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hright : 0 ≤ Real.sqrt (Real.pi / (a + 1 / 2)) := Real.sqrt_nonneg _
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(a * b ^ 2 / (2 * (a + 1 / 2)))) *
          Real.sqrt (Real.pi / (a + 1 / 2)) ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * 1 *
          Real.sqrt (Real.pi / (a + 1 / 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp hleft) hright
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi / (a + 1 / 2)) := by ring

theorem integral_exp_neg_weighted_sq_sum_pi_gaussian
    {I : Type*} [Fintype I] (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∫ x : I → ℝ, Real.exp (-(∑ i, a i * x i ^ 2))
        ∂(Measure.pi fun _ : I => gaussianReal 0 1) =
      ∏ i, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (a i + 1 / 2)) := by
  have hfun : (fun x : I → ℝ => Real.exp (-(∑ i, a i * x i ^ 2))) =
      fun x => ∏ i, Real.exp (-a i * x i ^ 2) := by
    funext x
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun, integral_fintype_prod_eq_prod
    (fun i x => Real.exp (-a i * x ^ 2))]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_exp_neg_mul_sq_gaussianReal (a i) (by linarith [ha i])

theorem integral_exp_neg_weighted_shifted_sq_sum_pi_gaussian_le
    {I : Type*} [Fintype I] (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (center : I → ℝ) :
    ∫ x : I → ℝ, Real.exp (-(∑ i, a i * (x i - center i) ^ 2))
        ∂(Measure.pi fun _ : I => gaussianReal 0 1) ≤
      ∏ i, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (a i + 1 / 2)) := by
  have hfun :
      (fun x : I → ℝ => Real.exp (-(∑ i, a i * (x i - center i) ^ 2))) =
        fun x => ∏ i, Real.exp (-a i * (x i - center i) ^ 2) := by
    funext x
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun, integral_fintype_prod_eq_prod
    (fun i x => Real.exp (-a i * (x - center i) ^ 2))]
  apply Finset.prod_le_prod
  · intro i _
    rw [integral_exp_neg_mul_sq_sub_gaussianReal (a i) (center i) (ha i)]
    positivity
  · intro i _
    exact integral_exp_neg_mul_sq_sub_gaussianReal_le (a i) (center i) (ha i)

theorem integral_exp_neg_mul_norm_sq_linearMap_stdGaussian
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    (tau : ℝ) (htau : 0 ≤ tau) :
    ∫ x : E, Real.exp (-tau * ‖A x‖ ^ 2) ∂stdGaussian E =
      ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * A.singularValues i ^ 2 + 1 / 2)) := by
  let T : E →ₗ[ℝ] E := A.adjoint ∘ₗ A
  let hT : T.IsSymmetric := A.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis hn
  let synth : (Fin n → ℝ) → E := fun x => ∑ i, x i • b i
  have hsynth : Measurable synth := by
    fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map hsynth.aemeasurable
    ((by fun_prop : Continuous fun x : E => Real.exp (-tau * ‖A x‖ ^ 2)).aestronglyMeasurable)]
  have hcoord : ∀ (x : Fin n → ℝ) i, b.repr (synth x) i = x i := by
    intro x i
    have hsynth_eq : synth x = b.repr.symm (WithLp.toLp 2 x) := by
      simpa [synth] using b.sum_repr_symm (WithLp.toLp 2 x)
    rw [hsynth_eq]
    change b.repr (b.repr.symm (WithLp.toLp 2 x)) i = x i
    simp
  have hnorm : ∀ x : Fin n → ℝ,
      ‖A (synth x)‖ ^ 2 =
        ∑ i, hT.eigenvalues hn i * x i ^ 2 := by
    intro x
    rw [← real_inner_self_eq_norm_sq]
    rw [← LinearMap.adjoint_inner_right]
    change inner ℝ (synth x) (T (synth x)) = _
    rw [real_inner_apply_eq_sum_eigenvalues hT hn]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord x i]
  have hfun : (fun x : Fin n → ℝ => Real.exp (-tau * ‖A (synth x)‖ ^ 2)) =
      fun x => Real.exp (-(∑ i, (tau * hT.eigenvalues hn i) * x i ^ 2)) := by
    funext x
    rw [hnorm x]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  have heig : ∀ i, 0 ≤ hT.eigenvalues hn i :=
    fun i => A.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i
  rw [integral_exp_neg_weighted_sq_sum_pi_gaussian
    (fun i => tau * hT.eigenvalues hn i)
    (fun i => mul_nonneg htau (heig i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [show hT.eigenvalues hn i = A.singularValues i ^ 2 by
    simpa [T, hT] using (A.sq_singularValues_fin hn i).symm]

theorem integral_exp_neg_mul_norm_sq_sub_linearMap_stdGaussian_le
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (z : E) (hn : Module.finrank ℝ E = n)
    (tau : ℝ) (htau : 0 ≤ tau) :
    ∫ x : E, Real.exp (-tau * ‖A (x - z)‖ ^ 2) ∂stdGaussian E ≤
      ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * A.singularValues i ^ 2 + 1 / 2)) := by
  let T : E →ₗ[ℝ] E := A.adjoint ∘ₗ A
  let hT : T.IsSymmetric := A.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis hn
  let synth : (Fin n → ℝ) → E := fun x => ∑ i, x i • b i
  let center : Fin n → ℝ := fun i => b.repr z i
  have hsynth : Measurable synth := by
    fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map hsynth.aemeasurable
    ((by fun_prop : Continuous fun x : E =>
      Real.exp (-tau * ‖A (x - z)‖ ^ 2)).aestronglyMeasurable)]
  have hsynth_eq : ∀ x : Fin n → ℝ,
      synth x = b.repr.symm (WithLp.toLp 2 x) := by
    intro x
    simpa [synth] using b.sum_repr_symm (WithLp.toLp 2 x)
  have hcoord : ∀ (x : Fin n → ℝ) i,
      b.repr (synth x - z) i = x i - center i := by
    intro x i
    rw [map_sub, hsynth_eq x]
    simp [center]
  have hnorm : ∀ x : Fin n → ℝ,
      ‖A (synth x - z)‖ ^ 2 =
        ∑ i, hT.eigenvalues hn i * (x i - center i) ^ 2 := by
    intro x
    rw [← real_inner_self_eq_norm_sq]
    rw [← LinearMap.adjoint_inner_right]
    change inner ℝ (synth x - z) (T (synth x - z)) = _
    rw [real_inner_apply_eq_sum_eigenvalues hT hn]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord x i]
  have hfun : (fun x : Fin n → ℝ =>
      Real.exp (-tau * ‖A (synth x - z)‖ ^ 2)) =
      fun x => Real.exp
        (-(∑ i, (tau * hT.eigenvalues hn i) * (x i - center i) ^ 2)) := by
    funext x
    rw [hnorm x]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  have heig : ∀ i, 0 ≤ hT.eigenvalues hn i :=
    fun i => A.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i
  refine (integral_exp_neg_weighted_shifted_sq_sum_pi_gaussian_le
    (fun i => tau * hT.eigenvalues hn i)
    (fun i => mul_nonneg htau (heig i)) center).trans_eq ?_
  apply Finset.prod_congr rfl
  intro i _
  rw [show hT.eigenvalues hn i = A.singularValues i ^ 2 by
    simpa [T, hT] using (A.sq_singularValues_fin hn i).symm]

theorem integral_exp_neg_mul_affine_norm_sq_linearMap_stdGaussian_le
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (y : F) (hn : Module.finrank ℝ E = n)
    (tau : ℝ) (htau : 0 ≤ tau) :
    ∫ x : E, Real.exp (-tau * ‖A x - y‖ ^ 2) ∂stdGaussian E ≤
      ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (tau * A.singularValues i ^ 2 + 1 / 2)) := by
  obtain ⟨z, hz⟩ := exists_linearMap_translate_norm_le_affine_norm A y
  have hpoint : ∀ x : E,
      Real.exp (-tau * ‖A x - y‖ ^ 2) ≤
        Real.exp (-tau * ‖A (x - z)‖ ^ 2) := by
    intro x
    apply Real.exp_le_exp.mpr
    have hsq : ‖A (x - z)‖ ^ 2 ≤ ‖A x - y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hz x) 2
    nlinarith
  have hleft : Integrable (fun x : E =>
      Real.exp (-tau * ‖A x - y‖ ^ 2)) (stdGaussian E) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr htau) (sq_nonneg _))
  have hright : Integrable (fun x : E =>
      Real.exp (-tau * ‖A (x - z)‖ ^ 2)) (stdGaussian E) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr htau) (sq_nonneg _))
  exact (integral_mono hleft hright hpoint).trans
    (integral_exp_neg_mul_norm_sq_sub_linearMap_stdGaussian_le
      A z hn tau htau)

/-- Incidence-normalized affine Laplace law.  A weighted reporter may retain
arbitrary target multiplicity; only its pointwise affine-Gaussian majorants
enter the quenched bad-set probability. -/
theorem stdGaussian_measure_weightedReporter_on_set_ge_le_of_affineLaplace
    {n : ℕ} {E F C : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype C]
    (G : Set E) (A : C → E →ₗ[ℝ] F) (y : C → F)
    (reporter : C → E → ℝ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hn : Module.finrank ℝ E = n)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hreporter : ∀ x ∈ G, ∀ c,
      reporter c x ≤ Real.exp (-tau * ‖A c x - y c‖ ^ 2))
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * reporter c x} ≤
      (∑ c, w c *
        ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (tau * (A c).singularValues i ^ 2 + 1 / 2))) / κ := by
  let f : E → ℝ := fun x => ∑ c, w c *
    Real.exp (-tau * ‖A c x - y c‖ ^ 2)
  have hkernelMeas (c : C) : Measurable
      (fun x : E => Real.exp (-tau * ‖A c x - y c‖ ^ 2)) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul
        (((LinearMap.continuous_of_finiteDimensional (A c)).sub
          continuous_const).norm.pow 2))).measurable
  have hmeas : Measurable f := by
    dsimp [f]
    apply Finset.measurable_sum
    intro c _
    exact (hkernelMeas c).const_mul (w c)
  have hnonnegPoint (x : E) : 0 ≤ f x := by
    dsimp [f]
    exact Finset.sum_nonneg fun c _ =>
      mul_nonneg (hw.1 c) (Real.exp_pos _).le
  have hleOne (x : E) : f x ≤ 1 := by
    dsimp [f]
    calc
      (∑ c, w c * Real.exp (-tau * ‖A c x - y c‖ ^ 2)) ≤
          ∑ c, w c * 1 := by
        apply Finset.sum_le_sum
        intro c _
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr htau) (sq_nonneg _)))
          (hw.1 c)
      _ = 1 := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hnonneg : 0 ≤ᵐ[stdGaussian E] f :=
    Filter.Eventually.of_forall hnonnegPoint
  have hint : Integrable f (stdGaussian E) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonnegPoint x)]
    exact hleOne x
  have hsubset :
      {x | x ∈ G ∧ κ ≤ ∑ c, w c * reporter c x} ⊆
        {x | κ ≤ f x} := by
    intro x hx
    refine hx.2.trans ?_
    dsimp [f]
    apply Finset.sum_le_sum
    intro c _
    exact mul_le_mul_of_nonneg_left (hreporter x hx.1 c) (hw.1 c)
  refine (measureReal_mono hsubset).trans ?_
  apply (le_div_iff₀ hκ).2
  rw [mul_comm]
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hint κ
  refine hmark.trans ?_
  change (∫ x, ∑ c, w c * Real.exp
      (-tau * ‖A c x - y c‖ ^ 2) ∂stdGaussian E) ≤ _
  rw [integral_finsetSum]
  · apply Finset.sum_le_sum
    intro c _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_exp_neg_mul_affine_norm_sq_linearMap_stdGaussian_le
        (A c) (y c) hn tau htau) (hw.1 c)
  · intro c _
    apply Integrable.const_mul
    apply Integrable.of_bound (hkernelMeas c).aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr htau) (sq_nonneg _))

/-- Prefactored incidence-normalized affine Laplace law.  Targetwise return
removal survives Gaussian coarea as an exact multiplicative charge instead
of being discarded before the occupied-image sum. -/
theorem stdGaussian_measure_weightedReporter_on_set_ge_le_of_prefactoredAffineLaplace
    {n : ℕ} {E F C : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype C]
    (G : Set E) (A : C → E →ₗ[ℝ] F) (y : C → F)
    (prefactor : C → ℝ) (hprefactor0 : ∀ c, 0 ≤ prefactor c)
    (hprefactor1 : ∀ c, prefactor c ≤ 1)
    (reporter : C → E → ℝ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hn : Module.finrank ℝ E = n)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hreporter : ∀ x ∈ G, ∀ c,
      reporter c x ≤ prefactor c *
        Real.exp (-tau * ‖A c x - y c‖ ^ 2))
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * reporter c x} ≤
      (∑ c, w c * prefactor c *
        ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (tau * (A c).singularValues i ^ 2 + 1 / 2))) / κ := by
  let f : E → ℝ := fun x => ∑ c, w c * prefactor c *
    Real.exp (-tau * ‖A c x - y c‖ ^ 2)
  have hkernelMeas (c : C) : Measurable
      (fun x : E => Real.exp (-tau * ‖A c x - y c‖ ^ 2)) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul
        (((LinearMap.continuous_of_finiteDimensional (A c)).sub
          continuous_const).norm.pow 2))).measurable
  have hmeas : Measurable f := by
    dsimp [f]
    apply Finset.measurable_sum
    intro c _
    exact (hkernelMeas c).const_mul (w c * prefactor c)
  have hnonnegPoint (x : E) : 0 ≤ f x := by
    dsimp [f]
    exact Finset.sum_nonneg fun c _ =>
      mul_nonneg (mul_nonneg (hw.1 c) (hprefactor0 c))
        (Real.exp_pos _).le
  have hleOne (x : E) : f x ≤ 1 := by
    dsimp [f]
    calc
      (∑ c, w c * prefactor c *
          Real.exp (-tau * ‖A c x - y c‖ ^ 2)) ≤
          ∑ c, w c * 1 := by
        apply Finset.sum_le_sum
        intro c _
        calc
          w c * prefactor c * Real.exp (-tau * ‖A c x - y c‖ ^ 2) ≤
              w c * prefactor c * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr
                (mul_nonpos_of_nonpos_of_nonneg
                  (neg_nonpos.mpr htau) (sq_nonneg _)))
              (mul_nonneg (hw.1 c) (hprefactor0 c))
          _ ≤ w c * 1 := by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left (hprefactor1 c) (hw.1 c))
      _ = 1 := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hnonneg : 0 ≤ᵐ[stdGaussian E] f :=
    Filter.Eventually.of_forall hnonnegPoint
  have hint : Integrable f (stdGaussian E) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonnegPoint x)]
    exact hleOne x
  have hsubset :
      {x | x ∈ G ∧ κ ≤ ∑ c, w c * reporter c x} ⊆
        {x | κ ≤ f x} := by
    intro x hx
    refine hx.2.trans ?_
    dsimp [f]
    apply Finset.sum_le_sum
    intro c _
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hreporter x hx.1 c) (hw.1 c))
  refine (measureReal_mono hsubset).trans ?_
  apply (le_div_iff₀ hκ).2
  rw [mul_comm]
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hint κ
  refine hmark.trans ?_
  change (∫ x, ∑ c, w c * prefactor c *
      Real.exp (-tau * ‖A c x - y c‖ ^ 2) ∂stdGaussian E) ≤ _
  rw [integral_finsetSum]
  · apply Finset.sum_le_sum
    intro c _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_exp_neg_mul_affine_norm_sq_linearMap_stdGaussian_le
        (A c) (y c) hn tau htau)
      (mul_nonneg (hw.1 c) (hprefactor0 c))
  · intro c _
    apply Integrable.const_mul
    apply Integrable.of_bound (hkernelMeas c).aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr htau) (sq_nonneg _))

end

end GaloisForLFunctions.HTGeometry

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

def pairQubitProjectiveSeedGrowingReplicaOscillationCeiling
    (L : ℕ) (rho scale : ℝ) : ℝ :=
  2 * ((L : ℝ) + 1 + rho * nearestNeighborPathLocalGeneratorMass L +
    |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) + 1

theorem pairQubitProjectiveSeedGrowingReplicaOscillationCeiling_pos
    (L : ℕ) {rho scale : ℝ} (hrho : 0 ≤ rho) :
    0 < pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale := by
  unfold pairQubitProjectiveSeedGrowingReplicaOscillationCeiling
  have hmass : 0 ≤ nearestNeighborPathLocalGeneratorMass L := by
    unfold nearestNeighborPathLocalGeneratorMass
    positivity
  positivity

theorem directStaticChoiTargetNearActionMass_choiVector_le_exp_normalizedCommutator
    {d : ℕ} (hd : 0 < d)
    (energy : Fin d → ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector W) energy r δ ≤
      Real.exp (-(r : ℝ) *
        (normalizedSpectralCommutatorEnergy energy W /
          staticChoiOscillationScale energy ^ 2)) := by
  have hnear := directStaticChoiTargetNearActionMass_choiVector_le hd W energy r δ
  have hscale : 0 < staticChoiOscillationScale energy ^ 2 :=
    sq_pos_of_pos (staticChoiOscillationScale_pos energy)
  have hcomm :
      normalizedSpectralCommutatorEnergy energy W ≤
        staticChoiOscillationScale energy ^ 2 *
          (1 - unitaryDiagonalCentralizerMass W ^ 2) := by
    calc
      normalizedSpectralCommutatorEnergy energy W ≤
          staticChoiOscillationScale energy ^ 2 *
            normalizedSpectralOffDiagonalMass W :=
        normalizedSpectralCommutatorEnergy_le_oscillation_sq_mul_offDiagonal energy W
      _ ≤ staticChoiOscillationScale energy ^ 2 *
            (1 - unitaryDiagonalCentralizerMass W ^ 2) :=
        mul_le_mul_of_nonneg_left
          (normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq hd hW)
          (sq_nonneg _)
  have hmassSq :
      unitaryDiagonalCentralizerMass W ^ 2 ≤
        1 - normalizedSpectralCommutatorEnergy energy W /
          staticChoiOscillationScale energy ^ 2 := by
    have hratio : normalizedSpectralCommutatorEnergy energy W /
          staticChoiOscillationScale energy ^ 2 ≤
        1 - unitaryDiagonalCentralizerMass W ^ 2 := by
      exact (div_le_iff₀ hscale).2 (by simpa [mul_comm] using hcomm)
    linarith
  have hexpBase :
      1 - normalizedSpectralCommutatorEnergy energy W /
          staticChoiOscillationScale energy ^ 2 ≤
        Real.exp (-(normalizedSpectralCommutatorEnergy energy W /
          staticChoiOscillationScale energy ^ 2)) := by
    linarith [Real.add_one_le_exp
      (-(normalizedSpectralCommutatorEnergy energy W /
        staticChoiOscillationScale energy ^ 2))]
  have hpow : unitaryDiagonalCentralizerMass W ^ (2 * r) ≤
      (Real.exp (-(normalizedSpectralCommutatorEnergy energy W /
        staticChoiOscillationScale energy ^ 2))) ^ r := by
    calc
      unitaryDiagonalCentralizerMass W ^ (2 * r) =
          (unitaryDiagonalCentralizerMass W ^ 2) ^ r := by rw [pow_mul]
      _ ≤ (1 - normalizedSpectralCommutatorEnergy energy W /
            staticChoiOscillationScale energy ^ 2) ^ r :=
        pow_le_pow_left₀ (sq_nonneg _) hmassSq r
      _ ≤ (Real.exp (-(normalizedSpectralCommutatorEnergy energy W /
            staticChoiOscillationScale energy ^ 2))) ^ r :=
        pow_le_pow_left₀ (le_trans (sq_nonneg _) hmassSq) hexpBase r
  refine hnear.trans (hpow.trans_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_exp_of_scale
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ B : ℝ)
    (hscale : staticChoiOscillationScale hH.eigenvalues ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ))
        hH.eigenvalues r δ ≤
      Real.exp (-(((r : ℝ) * (d : ℝ)⁻¹ / B ^ 2) *
        finiteMatrixHilbertSchmidtEnergy
          (H * (U : Matrix (Fin d) (Fin d) ℂ) -
            (U : Matrix (Fin d) (Fin d) ℂ) * H))) := by
  have hraw :=
    directStaticChoiTargetNearActionMass_choiVector_le_exp_normalizedCommutator
      hd hH.eigenvalues (hermitianSpectralEndpoint hH U).2 r δ
  rw [normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint hd hH U] at hraw
  refine hraw.trans (Real.exp_le_exp.mpr ?_)
  have hspos : 0 < staticChoiOscillationScale hH.eigenvalues :=
    staticChoiOscillationScale_pos hH.eigenvalues
  have hsq : staticChoiOscillationScale hH.eigenvalues ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hspos.le hB.le).2 hscale
  have hinv : (B ^ 2)⁻¹ ≤
      (staticChoiOscillationScale hH.eigenvalues ^ 2)⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hB) (sq_pos_of_pos hspos)).2 hsq
  have hE : 0 ≤ finiteMatrixHilbertSchmidtEnergy
      (H * (U : Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ) * H) :=
    finiteMatrixHilbertSchmidtEnergy_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hinv
    (mul_nonneg (Nat.cast_nonneg r)
      (inv_nonneg.mpr (Nat.cast_nonneg d)))
  have hfull := mul_le_mul_of_nonneg_right hmul hE
  calc
    -(r : ℝ) * ((d : ℝ)⁻¹ *
        finiteMatrixHilbertSchmidtEnergy
          (H * (U : Matrix (Fin d) (Fin d) ℂ) -
            (U : Matrix (Fin d) (Fin d) ℂ) * H) /
        staticChoiOscillationScale hH.eigenvalues ^ 2) =
      -(((r : ℝ) * (d : ℝ)⁻¹) *
        (staticChoiOscillationScale hH.eigenvalues ^ 2)⁻¹ *
          finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ) * H)) := by ring
    _ ≤ -(((r : ℝ) * (d : ℝ)⁻¹) * (B ^ 2)⁻¹ *
          finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ) * H)) := neg_le_neg hfull
    _ = -(((r : ℝ) * (d : ℝ)⁻¹ / B ^ 2) *
        finiteMatrixHilbertSchmidtEnergy
          (H * (U : Matrix (Fin d) (Fin d) ℂ) -
            (U : Matrix (Fin d) (Fin d) ℂ) * H)) := by ring

variable {E ι : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.affineNearAction_le_exp_of_scale
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (r : ℕ) (δ B : ℝ)
    (hscale : staticChoiOscillationScale
      (P.affineSpectralEnergy hH₀ x) ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (choiVector
          (P.affineSpectralEndpoint hH₀ x U :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.affineSpectralEnergy hH₀ x) r δ ≤
      Real.exp (-(((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ / B ^ 2) *
        ‖P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U‖ ^ 2)) := by
  have h :=
    directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_exp_of_scale
      (d := Fintype.card ι) Fintype.card_pos
      (P.affineReindexedHamiltonian_isHermitian hH₀ x)
      (finiteGaussianHermitianPencilReindexedEndpoint U) r δ B hscale hB
  rw [P.affineReindexedCommutatorEnergy H₀ x U] at h
  simpa [FiniteGaussianHermitianPencil.affineSpectralEndpoint,
    FiniteGaussianHermitianPencil.affineSpectralEnergy] using h

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.scaledAffineNearAction_le_exp_of_scale
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (r : ℕ) (δ B : ℝ)
    (hosc : staticChoiOscillationScale
      (P.scaledAffineSpectralEnergy hH₀ scale x) ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (choiVector
          (P.scaledAffineSpectralEndpoint hH₀ scale x U :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ ≤
      Real.exp (-(((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ 2 / B ^ 2) *
        ‖P.commutatorMap U x -
          scaledHermitianPencilCommutatorDrift scale H₀ U‖ ^ 2)) := by
  have h := P.affineNearAction_le_exp_of_scale
    hH₀ (scale • x) U r δ B hosc hB
  rw [P.scaledAffineCommutatorEnergy hscale H₀ x U] at h
  exact h.trans_eq (by
    congr 1
    ring)

theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedScaledAffineNearAction_on_scaleSet_ge_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (G : Set E) (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ B : ℝ)
    (hosc : ∀ x ∈ G, staticChoiOscillationScale
      (P.scaledAffineSpectralEnergy hH₀ scale x) ≤ B)
    (hB : 0 < B) (n : ℕ) (hn : Module.finrank ℝ E = n)
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
          (choiVector
            (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
          (P.scaledAffineSpectralEnergy hH₀ scale x) r δ} ≤
      (∑ c, w c *
        ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ 2 / B ^ 2) *
              (P.commutatorMap (U c)).singularValues i ^ 2 + 1 / 2))) / κ := by
  let tau : ℝ :=
    (r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ 2 / B ^ 2
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  apply GaloisForLFunctions.HTGeometry.stdGaussian_measure_weightedReporter_on_set_ge_le_of_affineLaplace
    G (fun c => P.commutatorMap (U c))
      (fun c => scaledHermitianPencilCommutatorDrift scale H₀ (U c))
      (fun c x => directStaticChoiTargetNearActionMass
        (choiVector
          (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ)
      w hw hn tau htau
  · intro x hx c
    have hpoint := P.scaledAffineNearAction_le_exp_of_scale
      hH₀ hscale x (U c) r δ B (hosc x hx) hB
    simpa [tau] using hpoint
  · exact hκ

/-- Growing-replica pseudodeterminant law on the same ordinary two-local
draws that carry the certified laboratory complexity ramp. -/
theorem stdGaussian_measure_pairQubitProjectiveSeedWeightedGrowingReplicaNearAction_on_growthSet_ge_le
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ} (hrho : 0 ≤ rho)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))).real
        {x | x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
          κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
            (choiVector
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
                  L p scale x (U c) :
                Matrix (Fin (Fintype.card
                  (FiniteQubitConfiguration (Fin (L * 2)))))
                  (Fin (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))))) ℂ))
            (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy
              L p scale x) r δ} ≤
      (∑ c, w c *
        ∏ i : Fin (Module.finrank ℝ
            (TwoLocalPauliCoefficientSpace (L * 2))),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
                  scale ^ 2 /
                    pairQubitProjectiveSeedGrowingReplicaOscillationCeiling
                      L rho scale ^ 2) *
                ((twoLocalPauliGaussianHermitianPencil
                    (L * 2)).commutatorMap
                      (pairQubitPathUnitaryReindex L (U c))).singularValues i ^ 2 +
                1 / 2))) / κ := by
  let P := twoLocalPauliGaussianHermitianPencil (L * 2)
  let B := pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale
  have hB : 0 < B :=
    pairQubitProjectiveSeedGrowingReplicaOscillationCeiling_pos L hrho
  have hosc : ∀ x ∈ weakTwoLocalPauliCertifiedGrowthSet L,
      staticChoiOscillationScale
        (P.scaledAffineSpectralEnergy
          (pairQubitProjectivePauliSeed_isHermitian L p) scale x) ≤ B := by
    intro x hx
    simpa [P, B, pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy,
      pairQubitProjectiveSeedGrowingReplicaOscillationCeiling] using
      pairQubitProjectiveSeedWeakTwoLocalSpectralOscillationScale_le
        hL hseed hx
  exact P.stdGaussian_measure_weightedScaledAffineNearAction_on_scaleSet_ge_le
    (pairQubitProjectivePauliSeed_isHermitian L p) hscale
    (weakTwoLocalPauliCertifiedGrowthSet L)
    (fun c => pairQubitPathUnitaryReindex L (U c))
    w hw r δ B hosc hB
    (Module.finrank ℝ (TwoLocalPauliCoefficientSpace (L * 2))) rfl hκ

theorem FiniteGaussianHermitianPencil.stdGaussian_measure_affineNearAction_on_scaleSet_ge_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    (G : Set E) (U : Matrix.unitaryGroup ι ℂ)
    (r : ℕ) (δ B : ℝ)
    (hscale : ∀ x ∈ G, staticChoiOscillationScale
      (P.affineSpectralEnergy hH₀ x) ≤ B)
    (hB : 0 < B) (n : ℕ) (hn : Module.finrank ℝ E = n)
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ directStaticChoiTargetNearActionMass
          (choiVector
            (P.affineSpectralEndpoint hH₀ x U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
          (P.affineSpectralEnergy hH₀ x) r δ} ≤
      (∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi /
          (((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ / B ^ 2) *
            (P.commutatorMap U).singularValues i ^ 2 + 1 / 2))) / κ := by
  let tau : ℝ := (r : ℝ) * (Fintype.card ι : ℝ)⁻¹ / B ^ 2
  let f : E → ℝ := fun x => Real.exp
    (-tau * ‖P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U‖ ^ 2)
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hmeas : Measurable f := by
    dsimp [f]
    fun_prop
  have hnonneg : 0 ≤ᵐ[stdGaussian E] f :=
    Filter.Eventually.of_forall fun x => Real.exp_pos _ |>.le
  have hint : Integrable f (stdGaussian E) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htau) (sq_nonneg _))
  have hsubset :
      {x | x ∈ G ∧ κ ≤ directStaticChoiTargetNearActionMass
          (choiVector
            (P.affineSpectralEndpoint hH₀ x U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
          (P.affineSpectralEnergy hH₀ x) r δ} ⊆
        {x | κ ≤ f x} := by
    intro x hx
    have hpoint := P.affineNearAction_le_exp_of_scale
      hH₀ x U r δ B (hscale x hx.1) hB
    exact hx.2.trans (by simpa [f, tau] using hpoint)
  refine (measureReal_mono hsubset).trans ?_
  apply (le_div_iff₀ hκ).2
  rw [mul_comm]
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hint κ
  refine hmark.trans ?_
  simpa [f, tau] using
    (GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_affine_norm_sq_linearMap_stdGaussian_le
      (P.commutatorMap U) (hermitianPencilCommutatorDrift H₀ U) hn tau htau)

theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedAffineNearAction_on_scaleSet_ge_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {C : Type*} [Fintype C]
    (G : Set E) (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ B : ℝ)
    (hscale : ∀ x ∈ G, staticChoiOscillationScale
      (P.affineSpectralEnergy hH₀ x) ≤ B)
    (hB : 0 < B) (n : ℕ) (hn : Module.finrank ℝ E = n)
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
          (choiVector
            (P.affineSpectralEndpoint hH₀ x (U c) :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
          (P.affineSpectralEnergy hH₀ x) r δ} ≤
      (∑ c, w c *
        ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ / B ^ 2) *
              (P.commutatorMap (U c)).singularValues i ^ 2 + 1 / 2))) / κ := by
  let tau : ℝ := (r : ℝ) * (Fintype.card ι : ℝ)⁻¹ / B ^ 2
  let f : E → ℝ := fun x => ∑ c, w c * Real.exp
    (-tau * ‖P.commutatorMap (U c) x -
      hermitianPencilCommutatorDrift H₀ (U c)‖ ^ 2)
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hmeas : Measurable f := by
    dsimp [f]
    fun_prop
  have hnonnegPoint (x : E) : 0 ≤ f x := by
    dsimp [f]
    exact Finset.sum_nonneg fun c _ =>
      mul_nonneg (hw.1 c) (Real.exp_pos _).le
  have hleOne (x : E) : f x ≤ 1 := by
    dsimp [f]
    calc
      (∑ c, w c * Real.exp
          (-tau * ‖P.commutatorMap (U c) x -
            hermitianPencilCommutatorDrift H₀ (U c)‖ ^ 2)) ≤
          ∑ c, w c * 1 := by
        apply Finset.sum_le_sum
        intro c _
        apply mul_le_mul_of_nonneg_left _ (hw.1 c)
        exact Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr htau) (sq_nonneg _))
      _ = 1 := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hnonneg : 0 ≤ᵐ[stdGaussian E] f :=
    Filter.Eventually.of_forall hnonnegPoint
  have hint : Integrable f (stdGaussian E) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonnegPoint x)]
    exact hleOne x
  have hsubset :
      {x | x ∈ G ∧ κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
          (choiVector
            (P.affineSpectralEndpoint hH₀ x (U c) :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
          (P.affineSpectralEnergy hH₀ x) r δ} ⊆
        {x | κ ≤ f x} := by
    intro x hx
    refine hx.2.trans ?_
    dsimp [f]
    apply Finset.sum_le_sum
    intro c _
    have hpoint := P.affineNearAction_le_exp_of_scale
      hH₀ x (U c) r δ B (hscale x hx.1) hB
    exact mul_le_mul_of_nonneg_left (by simpa [tau] using hpoint) (hw.1 c)
  refine (measureReal_mono hsubset).trans ?_
  apply (le_div_iff₀ hκ).2
  rw [mul_comm]
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hint κ
  refine hmark.trans ?_
  change (∫ x, ∑ c, w c * Real.exp
      (-tau * ‖P.commutatorMap (U c) x -
        hermitianPencilCommutatorDrift H₀ (U c)‖ ^ 2) ∂stdGaussian E) ≤ _
  rw [integral_finsetSum]
  · apply Finset.sum_le_sum
    intro c _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa [tau] using
        (GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_affine_norm_sq_linearMap_stdGaussian_le
          (P.commutatorMap (U c))
          (hermitianPencilCommutatorDrift H₀ (U c)) hn tau htau))
      (hw.1 c)
  · intro c _
    apply Integrable.const_mul
    apply Integrable.of_bound (by fun_prop : AEStronglyMeasurable
      (fun x : E => Real.exp
        (-tau * ‖P.commutatorMap (U c) x -
          hermitianPencilCommutatorDrift H₀ (U c)‖ ^ 2)) (stdGaussian E)) 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr htau) (sq_nonneg _))

end

end RHTower
