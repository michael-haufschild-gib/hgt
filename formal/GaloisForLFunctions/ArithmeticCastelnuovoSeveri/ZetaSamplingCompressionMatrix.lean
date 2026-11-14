import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZetaSamplingArchimedeanCompression
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FourthTracePerturbation
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Matrices of the sampled real densities

The entries are literal full-line integrals. Their quadratic forms are the
sampling integrals, so uniform quadratic bounds give operator norm bounds.
-/

open MeasureTheory Matrix Real Zeta23 Filter Topology
open scoped ComplexConjugate Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The sampling space is nonzero in the positive-height taper regime. -/
theorem zetaSampling_dimension_pos {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8*P.w ≤ P.L T) (hT : 2*π ≤ T) : 0 < P.d T := by
  have hL : 1 ≤ P.L T := by linarith only [hwL,hP.one_le_w]
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hF : 1 ≤ P.L T*T/(2*π) := by
    rw [le_div_iff₀ (by positivity : 0<2*π)]
    have hh := mul_le_mul_of_nonneg_right hL hT0.le
    nlinarith only [hh,hT]
  have hh : P.L T*T/(2*π) < (P.d T : ℝ)+1 := Nat.lt_floor_add_one _
  have hd : (0:ℝ) < P.d T := by linarith only [hF,hh]
  exact_mod_cast hd

/-- The Frobenius energy is at most dimension times squared operator norm. -/
theorem matrixFrobeniusEnergy_le_dim_opNorm_sq {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (A : Matrix n n ℂ) :
    matrixFrobeniusEnergy A ≤ (Fintype.card n : ℝ) * ‖A‖^2 := by
  have hh := matrixFrobeniusEnergy_mul_le_opNorm A (1 : Matrix n n ℂ)
  rw [mul_one] at hh
  have hi : matrixFrobeniusEnergy (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
    simp [matrixFrobeniusEnergy,Matrix.one_apply,apply_ite]
  rw [hi,mul_comm] at hh
  exact hh

/-- Compression of a real density in the sampled Fourier family. -/
def zetaSamplingCompression (P : Params) (T : ℝ) (w : ℝ → ℝ) :
    Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ := fun i j =>
  (((∫ τ, w τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j)) /
    (P.a T * P.L T ^ 2) : ℝ) : ℂ)

theorem zetaSamplingCompression_isHermitian (P : Params) (T : ℝ) (w : ℝ → ℝ) :
    (zetaSamplingCompression P T w).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, zetaSamplingCompression, Complex.star_def, Complex.conj_ofReal]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with τ
  ring

/-- A linear density times the square of one translated sampling function is integrable. -/
theorem integrable_linearDensity_sampling_sq {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {w : ℝ → ℝ} (hw : Continuous w) {A : ℝ}
    (hA : ∀ τ, |w τ| ≤ A + |τ|) (t : ℝ) :
    Integrable (fun τ => w τ * P.phiHatR T (τ-t) ^ 2) := by
  have hi := (Params.integrable_phiHatR_sq hP hwL).comp_sub_right t
  have hj := (Params.integrable_phiHatR_sq_mul_sq hP hwL).comp_sub_right t
  have hc := Params.phiHatR_continuous hP hwL
  have hct : Continuous (fun τ => w τ * P.phiHatR T (τ-t)^2) :=
    hw.mul ((hc.comp (continuous_id.sub continuous_const)).pow 2)
  refine ((hi.const_mul (A + |t| + 1)).add hj).mono' hct.aestronglyMeasurable ?_
  filter_upwards [] with τ
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (P.phiHatR T (τ-t)))]
  have hτ : |τ| ≤ |τ-t| + |t| := by
    simpa only [sub_add_cancel] using abs_add_le (τ-t) t
  have hr : |τ-t| ≤ 1 + (τ-t)^2 := by
    nlinarith only [sq_nonneg (|τ-t|-1), sq_abs (τ-t)]
  have hh := mul_le_mul_of_nonneg_right
    (show |w τ| ≤ A + |t| + 1 + (τ-t)^2 by linarith only [hA τ, hτ, hr])
    (sq_nonneg (P.phiHatR T (τ-t)))
  nlinarith only [hh]

/-- Products of two sampling functions remain integrable against a linear density. -/
theorem integrable_linearDensity_sampling_mul {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {w : ℝ → ℝ} (hw : Continuous w) {A : ℝ}
    (hA : ∀ τ, |w τ| ≤ A + |τ|) (s t : ℝ) :
    Integrable (fun τ => w τ * P.phiHatR T (τ-s) * P.phiHatR T (τ-t)) := by
  have hi := (integrable_linearDensity_sampling_sq hP hwL hw hA s).norm
  have hj := (integrable_linearDensity_sampling_sq hP hwL hw hA t).norm
  have hc := Params.phiHatR_continuous hP hwL
  have hct : Continuous (fun τ => w τ * P.phiHatR T (τ-s) * P.phiHatR T (τ-t)) :=
    (hw.mul (hc.comp (continuous_id.sub continuous_const))).mul
      (hc.comp (continuous_id.sub continuous_const))
  refine ((hi.add hj).div_const 2).mono' hct.aestronglyMeasurable ?_
  filter_upwards [] with τ
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs, Pi.add_apply]
  have hh := mul_nonneg (abs_nonneg (w τ))
    (sq_nonneg (|P.phiHatR T (τ-s)| - |P.phiHatR T (τ-t)|))
  simp only [sub_sq,sq_abs] at hh
  nlinarith only [hh]

/-- The matrix quadratic form is exactly the full-line sampling integral. -/
theorem zetaSamplingCompression_quadratic {P : Params} {T : ℝ} {w : ℝ → ℝ}
    (hi : ∀ i j : Fin (P.d T), Integrable (fun τ =>
      w τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j)))
    (c : Fin (P.d T) → ℂ) :
    star c ⬝ᵥ (zetaSamplingCompression P T w *ᵥ c) =
      (((∫ τ, w τ * ‖zetaSamplingSynthesis P T c τ‖ ^ 2) /
        (P.a T * P.L T ^ 2) : ℝ) : ℂ) := by
  have hp (τ : ℝ) : ((w τ * ‖zetaSamplingSynthesis P T c τ‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, conj (c i) * c j *
        ((w τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
    simp only [zetaSamplingSynthesis, map_sum, map_mul, Complex.conj_ofReal]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by push_cast; ring
  rw [Complex.ofReal_div, ← integral_complex_ofReal]
  simp_rw [hp]
  have hint (i : Fin (P.d T)) : Integrable (fun τ => ∑ j : Fin (P.d T),
      conj (c i) * c j * ((w τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j) : ℝ) : ℂ)) :=
    integrable_finsetSum Finset.univ fun j _ => (hi i j).ofReal.const_mul (conj (c i) * c j)
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  have hinner (i : Fin (P.d T)) :
      (∫ τ, ∑ j : Fin (P.d T), conj (c i) * c j *
        ((w τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j) : ℝ) : ℂ)) =
      ∑ j : Fin (P.d T), ∫ τ, conj (c i) * c j *
        ((w τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j) : ℝ) : ℂ) :=
    integral_finsetSum Finset.univ fun j _ => (hi i j).ofReal.const_mul (conj (c i) * c j)
  simp_rw [hinner,integral_const_mul,integral_complex_ofReal]
  simp only [dotProduct, mulVec, zetaSamplingCompression, Pi.star_apply,
    Complex.star_def, Complex.ofReal_div, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermitian_l2Norm_le_of_quadratic_bound {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {q : ℝ} (hq : 0 ≤ q)
    (hb : ∀ c : n → ℂ, |(star c ⬝ᵥ (A *ᵥ c)).re| ≤ q * ∑ i, ‖c i‖ ^ 2) :
    ‖A‖ ≤ q := by
  let S := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  have hS : (S : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [Matrix.cstar_norm_def, ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hS]
  refine ciSup_le fun c => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
  by_cases hc : c = 0
  · simp [hc, hq]
  have hn : 0 < ‖c‖ ^ 2 := by positivity
  rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
  have hh := hb (WithLp.ofLp c)
  rw [← EuclideanSpace.norm_sq_eq] at hh
  have hsym : inner ℂ (S c) c = inner ℂ c (S c) := hS c c
  rw [hsym, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
    dotProduct_comm]
  exact hh

theorem zetaSamplingCompression_sub {P : Params} {T : ℝ} {w v : ℝ → ℝ}
    (hw : ∀ i j : Fin (P.d T), Integrable (fun τ =>
      w τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j)))
    (hv : ∀ i j : Fin (P.d T), Integrable (fun τ =>
      v τ * P.phiHatR T (τ-P.tau T i) * P.phiHatR T (τ-P.tau T j))) :
    zetaSamplingCompression P T (fun τ => w τ - v τ) =
      zetaSamplingCompression P T w - zetaSamplingCompression P T v := by
  ext i j
  simp only [zetaSamplingCompression, Matrix.sub_apply, sub_mul]
  rw [integral_sub (hw i j) (hv i j), sub_div, Complex.ofReal_sub]

/-- The constant-density baseline has trace equal to the sampling dimension. -/
theorem trace_zetaSamplingCompression_baseline {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) :
    (zetaSamplingCompression P T (fun _ => P.L T / (2 * π))).trace = (P.d T : ℂ) := by
  have hL : 0 < P.L T := by linarith only [hwL, hP.one_le_w]
  have ha : 0 < P.a T := by have := Params.half_le_a hP hwL; linarith only [this]
  have hd (i : Fin (P.d T)) :
      zetaSamplingCompression P T (fun _ => P.L T / (2 * π)) i i = 1 := by
    rw [zetaSamplingCompression]
    have he : (fun τ => P.L T / (2 * π) * P.phiHatR T (τ-P.tau T i) *
        P.phiHatR T (τ-P.tau T i)) =
        fun τ => P.L T / (2 * π) * P.phiHatR T (τ-P.tau T i)^2 := by funext τ; ring
    rw [he, integral_const_mul,
      integral_sub_right_eq_self (fun r => P.phiHatR T r ^ 2) (P.tau T i),
      Params.integral_phiHatR_sq hP hwL]
    have hr : P.L T / (2 * π) * (2 * π * P.a T * P.L T) /
        (P.a T * P.L T ^ 2) = 1 := by field_simp <;> ring
    rw [hr, Complex.ofReal_one]
  simp only [Matrix.trace, Matrix.diag, hd, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The literal matrix of the archimedean density error vanishes in operator norm. -/
theorem zetaSamplingCompression_archimedean_error_uniformly_small {P : Params}
    (hP : P.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ‖zetaSamplingCompression P T (fun τ => mu τ - l T / (2 * π))‖ ≤ ε := by
  obtain ⟨T₁, hT₁⟩ := normalizedArchimedeanDeviation_uniformly_small hP hε
  obtain ⟨T₂, hT₂⟩ := zetaSampling_bandwidth_eventually_ge hP (8 * P.w)
  obtain ⟨A, _, hA⟩ := exists_mu_linear_bound
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hwL := hT₂ T ((le_max_right _ _).trans hT)
  have hw : Continuous (fun τ => mu τ - l T / (2 * π)) :=
    gammaFacts.smooth.continuous.sub continuous_const
  have hb (τ : ℝ) : |mu τ - l T / (2 * π)| ≤ (A + |l T / (2 * π)|) + |τ| := by
    have hh := abs_sub_le (mu τ) 0 (l T / (2 * π))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith only [hh, hA τ]
  apply hermitian_l2Norm_le_of_quadratic_bound (zetaSamplingCompression_isHermitian _ _ _) hε.le
  intro c
  rw [zetaSamplingCompression_quadratic (fun i j =>
    integrable_linearDensity_sampling_mul hP hwL hw hb _ _) c, Complex.ofReal_re]
  exact hT₁ T ((le_max_left _ _).trans hT) c

private theorem centered_trace_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (((A-1)^k).trace).re = ∑ i, (hA.eigenvalues i - 1)^k := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
  have hd : diagonal (fun i => (hA.eigenvalues i : ℂ) - 1) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have he : A-1 = e (diagonal (fun i => (hA.eigenvalues i : ℂ) - 1)) := by
    rw [hd, map_sub, map_one]
    exact congrArg (fun M => M-1) hA.spectral_theorem
  rw [he, ← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (((hA.eigenvalues i : ℂ)-1)^k).re = _
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem star_dot_self_eq_energy {n : Type*} [Fintype n] (c : n → ℂ) :
    star c ⬝ᵥ c = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

/-- The baseline quadratic form lies between zero and `a⁻¹` times coefficient energy. -/
theorem zetaSamplingCompression_baseline_quadratic_bounds {P : Params} (hP : P.Valid)
    {T : ℝ} (hwL : 8 * P.w ≤ P.L T) (c : Fin (P.d T) → ℂ) :
    0 ≤ (star c ⬝ᵥ (zetaSamplingCompression P T (fun _ => P.L T / (2*π)) *ᵥ c)).re ∧
    (star c ⬝ᵥ (zetaSamplingCompression P T (fun _ => P.L T / (2*π)) *ᵥ c)).re ≤
      (P.a T)⁻¹ * ∑ i, ‖c i‖ ^ 2 := by
  have hL : 0 < P.L T := by linarith only [hwL, hP.one_le_w]
  have ha : 0 < P.a T := by have := Params.half_le_a hP hwL; linarith only [this]
  have hi (i j : Fin (P.d T)) := integrable_linearDensity_sampling_mul hP hwL
    (continuous_const : Continuous (fun _ : ℝ => P.L T / (2*π)))
    (fun τ => le_add_of_nonneg_right (abs_nonneg τ)) (P.tau T i) (P.tau T j)
  rw [zetaSamplingCompression_quadratic hi c, Complex.ofReal_re, integral_const_mul]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (P.L T / (2*π) * (2*π*P.L T * ∑ i, ‖c i‖^2)) /
        (P.a T * P.L T ^ 2) := by
      gcongr
      exact integral_zetaSamplingSynthesis_sq_le hP hwL c
    _ = _ := by field_simp <;> ring

/-- The centered baseline is an operator contraction. -/
theorem norm_zetaSamplingCompression_baseline_sub_one_le {P : Params} (hP : P.Valid)
    {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    ‖zetaSamplingCompression P T (fun _ => P.L T / (2*π)) - 1‖ ≤ 1 := by
  have ha := Params.half_le_a hP hwL
  have ha0 : 0 < P.a T := by linarith only [ha]
  have hai : (P.a T)⁻¹ ≤ 2 := by rw [inv_eq_one_div, div_le_iff₀ ha0]; linarith only [ha]
  apply hermitian_l2Norm_le_of_quadratic_bound
    ((zetaSamplingCompression_isHermitian _ _ _).sub Matrix.isHermitian_one) zero_le_one
  intro c
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re,
    star_dot_self_eq_energy, Complex.ofReal_re, one_mul]
  obtain ⟨hlo, hhi⟩ := zetaSamplingCompression_baseline_quadratic_bounds hP hwL c
  have hh := mul_le_mul_of_nonneg_right hai (show 0 ≤ ∑ i, ‖c i‖ ^ 2 by positivity)
  exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi, hh]⟩

/-- The baseline has operator norm at most two in the taper regime. -/
theorem norm_zetaSamplingCompression_baseline_le_two {P : Params} (hP : P.Valid)
    {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    ‖zetaSamplingCompression P T (fun _ => P.L T / (2*π))‖ ≤ 2 := by
  have ha := Params.half_le_a hP hwL
  have ha0 : 0 < P.a T := by linarith only [ha]
  have hai : (P.a T)⁻¹ ≤ 2 := by rw [inv_eq_one_div,div_le_iff₀ ha0]; linarith only [ha]
  apply hermitian_l2Norm_le_of_quadratic_bound (zetaSamplingCompression_isHermitian _ _ _) (by norm_num)
  intro c
  obtain ⟨hlo,hhi⟩ := zetaSamplingCompression_baseline_quadratic_bounds hP hwL c
  rw [abs_of_nonneg hlo]
  exact hhi.trans (mul_le_mul_of_nonneg_right hai (by positivity))

/-- The normalized fourth centered baseline moment is at most the taper defect. -/
theorem trace_fourth_zetaSamplingCompression_baseline_sub_one_le {P : Params}
    (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    (((zetaSamplingCompression P T (fun _ => P.L T / (2*π)) - 1)^4).trace).re ≤
      ((P.a T)⁻¹ - 1) * (P.d T : ℝ) := by
  let B := zetaSamplingCompression P T (fun _ => P.L T / (2*π))
  have hB := zetaSamplingCompression_isHermitian P T (fun _ => P.L T / (2*π))
  have ha := Params.half_le_a hP hwL
  have ha0 : 0 < P.a T := by linarith only [ha]
  have hai : (P.a T)⁻¹ ≤ 2 := by rw [inv_eq_one_div, div_le_iff₀ ha0]; linarith only [ha]
  have he (i : Fin (P.d T)) : 0 ≤ hB.eigenvalues i ∧ hB.eigenvalues i ≤ (P.a T)⁻¹ := by
    have hh := zetaSamplingCompression_baseline_quadratic_bounds hP hwL
      (WithLp.ofLp (hB.eigenvectorBasis i))
    have hn : ∑ j, ‖(hB.eigenvectorBasis i) j‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hB.eigenvectorBasis.orthonormal.1 i]
      norm_num
    rw [hn, mul_one] at hh
    have hei := hB.eigenvalues_eq i
    simp only [RCLike.re_eq_complex_re] at hei
    rw [← hei] at hh
    exact hh
  have ht : ∑ i, hB.eigenvalues i = (P.d T : ℝ) := by
    have hh := congrArg Complex.re (trace_zetaSamplingCompression_baseline hP hwL)
    rw [hB.trace_eq_sum_eigenvalues, Complex.re_sum] at hh
    simpa only [RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_re, Complex.natCast_re] using hh
  rw [centered_trace_pow hB]
  simpa only [Fintype.card_fin] using sum_fourth_centered_le_edge_defect
    hB.eigenvalues hai he (by simpa only [Fintype.card_fin] using ht)

private theorem trace_fourth_small_perturbation {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A Q : Matrix n n ℂ) (hA : ‖A‖ ≤ 1) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hQ : ‖Q‖ ≤ q) :
    (((A+Q)^4).trace).re ≤ ((A^4).trace).re + 15*q*(Fintype.card n : ℝ) := by
  have hE0 : 0 ≤ matrixFrobeniusEnergy A := by unfold matrixFrobeniusEnergy; positivity
  have hE : matrixFrobeniusEnergy A ≤ (Fintype.card n : ℝ) := by
    calc
      _ ≤ (Fintype.card n : ℝ) * ‖A‖^2 := matrixFrobeniusEnergy_le_dim_opNorm_sq A
      _ ≤ (Fintype.card n : ℝ) * 1^2 := by gcongr
      _ = _ := by ring
  have hs := Real.sqrt_le_sqrt hE
  have hbound : ‖((A+Q)^4 - A^4).trace‖ ≤ 15*q*(Fintype.card n : ℝ) := by
    calc
      _ ≤ 4*‖A‖*‖Q‖*matrixFrobeniusEnergy A + 6*‖Q‖^2*matrixFrobeniusEnergy A +
          4*‖Q‖^3*Real.sqrt (Fintype.card n : ℝ)*Real.sqrt (matrixFrobeniusEnergy A) +
          (Fintype.card n : ℝ)*‖Q‖^4 := norm_trace_fourth_perturbation_le_secondMoment A Q
      _ ≤ 4*1*q*(Fintype.card n : ℝ) + 6*q^2*(Fintype.card n : ℝ) +
          4*q^3*Real.sqrt (Fintype.card n : ℝ)*Real.sqrt (Fintype.card n : ℝ) +
          (Fintype.card n : ℝ)*q^4 := by gcongr
      _ = (4*q+6*q^2+4*q^3+q^4)*(Fintype.card n : ℝ) := by
        rw [mul_assoc (4*q^3), Real.mul_self_sqrt (Nat.cast_nonneg _)]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        have h2 : q^2 ≤ q := by nlinarith only [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
        have h3 : q^3 ≤ q := by
          rw [pow_succ]
          exact (mul_le_mul_of_nonneg_right h2 hq0).trans (by simpa only [pow_two] using h2)
        have h4 : q^4 ≤ q := by
          rw [pow_succ]
          exact (mul_le_mul_of_nonneg_right h3 hq0).trans (by simpa only [pow_two] using h2)
        linarith only [h2,h3,h4]
  have hh := Complex.re_le_norm (((A+Q)^4 - A^4).trace)
  rw [Matrix.trace_sub, Complex.sub_re] at hh
  rw [Matrix.trace_sub] at hbound
  linarith only [hh,hbound]

/-- At bandwidth one the actual archimedean compression converges to the identity
in normalized fourth Schatten energy. -/
theorem zetaSamplingCompression_archimedean_centered_fourth_small {P : Params}
    (hP : P.Valid) (hlam : P.lam = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (((zetaSamplingCompression P T mu - 1)^4).trace).re ≤ ε * (P.d T : ℝ) := by
  let q : ℝ := min 1 (ε/30)
  have hq : 0 < q := lt_min zero_lt_one (by positivity)
  have hq1 : q ≤ 1 := min_le_left _ _
  have hqε : 15*q ≤ ε/2 := by have := min_le_right (1:ℝ) (ε/30); dsimp [q]; linarith only [this]
  obtain ⟨T₁,hT₁⟩ := zetaSamplingCompression_archimedean_error_uniformly_small hP hq
  obtain ⟨T₂,hT₂⟩ := zetaSampling_inverse_bandwidth_uniformly_small hP
    (show 0 ≤ 2*P.w by linarith only [hP.one_le_w]) (show 0 < ε/2 by positivity)
  obtain ⟨A, _, hμ⟩ := exists_mu_linear_bound
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  obtain ⟨hwL, htπ, hsmall⟩ := hT₂ T ((le_max_right _ _).trans hT)
  letI : Nonempty (Fin (P.d T)) := Fin.pos_iff_nonempty.mp (zetaSampling_dimension_pos hP hwL htπ)
  have hL : 0 < P.L T := by linarith only [hwL,hP.one_le_w]
  have ha : 0 < P.a T := by have := Params.half_le_a hP hwL; linarith only [this]
  have heL : P.L T = l T := by change P.lam * l T = l T; rw [hlam,one_mul]
  let B := zetaSamplingCompression P T (fun _ => P.L T / (2*π))
  let Q := zetaSamplingCompression P T (fun τ => mu τ - l T / (2*π))
  have hQ : ‖Q‖ ≤ q := hT₁ T ((le_max_left _ _).trans hT)
  have hdiff : Q = zetaSamplingCompression P T mu - B := by
    dsimp only [Q]
    rw [← heL]
    exact zetaSamplingCompression_sub
      (fun i j => integrable_linearDensity_sampling_mul hP hwL gammaFacts.smooth.continuous hμ _ _)
      (fun i j => integrable_linearDensity_sampling_mul hP hwL continuous_const
        (fun τ => le_add_of_nonneg_right (abs_nonneg τ)) _ _)
  have hsum : (B-1)+Q = zetaSamplingCompression P T mu - 1 := by rw [hdiff]; abel
  have hpert := trace_fourth_small_perturbation (B-1) Q
    (norm_zetaSamplingCompression_baseline_sub_one_le hP hwL) hq.le hq1 hQ
  rw [hsum] at hpert
  have hbase := trace_fourth_zetaSamplingCompression_baseline_sub_one_le hP hwL
  have hdef : (P.a T)⁻¹ - 1 ≤ ε/2 := by
    have hab := (Params.one_sub_le_b hP hwL).trans (Params.b_le_a hP hwL)
    have hh : (P.a T)⁻¹ - 1 ≤ 2*P.w/(P.a T*P.L T) := by
      rw [le_div_iff₀ (mul_pos ha hL)]
      have he : ((P.a T)⁻¹ - 1)*(P.a T*P.L T) = (1-P.a T)*P.L T := by field_simp <;> ring
      rw [he]
      have hab' := (le_div_iff₀ hL).mp (show 1-P.a T ≤ 2*P.w/P.L T by linarith only [hab])
      linarith only [hab']
    exact hh.trans hsmall
  have hd : 0 ≤ (P.d T : ℝ) := Nat.cast_nonneg _
  have hb' := mul_le_mul_of_nonneg_right hdef hd
  have hq' := mul_le_mul_of_nonneg_right hqε hd
  dsimp [B] at hpert
  simp only [Fintype.card_fin] at hpert
  linarith only [hpert,hbase,hb',hq']

/-- The actual archimedean matrix has a uniform operator bound at bandwidth one. -/
theorem zetaSamplingCompression_archimedean_eventually_bounded {P : Params}
    (hP : P.Valid) (hlam : P.lam = 1) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ‖zetaSamplingCompression P T mu‖ ≤ 3 := by
  obtain ⟨T₁,hT₁⟩ := zetaSamplingCompression_archimedean_error_uniformly_small hP zero_lt_one
  obtain ⟨T₂,hT₂⟩ := zetaSampling_bandwidth_eventually_ge hP (8*P.w)
  obtain ⟨A,_,hμ⟩ := exists_mu_linear_bound
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hwL := hT₂ T ((le_max_right _ _).trans hT)
  have heL : P.L T = l T := by change P.lam*l T=l T; rw [hlam,one_mul]
  have he := zetaSamplingCompression_sub
    (fun i j => integrable_linearDensity_sampling_mul hP hwL gammaFacts.smooth.continuous hμ
      (P.tau T i) (P.tau T j))
    (fun i j => integrable_linearDensity_sampling_mul hP hwL
      (continuous_const : Continuous (fun _ : ℝ => P.L T/(2*π)))
      (fun τ => le_add_of_nonneg_right (abs_nonneg τ)) (P.tau T i) (P.tau T j))
  rw [heL] at he
  have hd := hT₁ T ((le_max_left _ _).trans hT)
  rw [he] at hd
  have hb := norm_zetaSamplingCompression_baseline_le_two hP hwL
  rw [heL] at hb
  have hh := norm_add_le
    (zetaSamplingCompression P T mu - zetaSamplingCompression P T (fun _ => l T/(2*π)))
    (zetaSamplingCompression P T (fun _ => l T/(2*π)))
  rw [sub_add_cancel] at hh
  linarith only [hh,hd,hb]

/-- A bounded density compresses with the sharp sampling constant. -/
theorem norm_zetaSamplingCompression_le_of_bound {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) {w : ℝ → ℝ} (hw : Continuous w) {M : ℝ}
    (hb : ∀ τ, |w τ| ≤ M) :
    ‖zetaSamplingCompression P T w‖ ≤ 2*π*M/(P.a T*P.L T) := by
  have hM : 0 ≤ M := (abs_nonneg (w 0)).trans (hb 0)
  have hL : 0 < P.L T := by linarith only [hwL,hP.one_le_w]
  have ha : 0 < P.a T := by have := Params.half_le_a hP hwL; linarith only [this]
  apply hermitian_l2Norm_le_of_quadratic_bound (zetaSamplingCompression_isHermitian _ _ _) (by positivity)
  intro c
  rw [zetaSamplingCompression_quadratic (fun i j => integrable_linearDensity_sampling_mul hP hwL hw
    (fun τ => (hb τ).trans (le_add_of_nonneg_right (abs_nonneg τ))) _ _) c,
    Complex.ofReal_re, abs_div, abs_of_pos (mul_pos ha (sq_pos_of_pos hL))]
  have hi := integrable_zetaSamplingSynthesis_sq hP hwL c
  have hbound : |∫ τ, w τ * ‖zetaSamplingSynthesis P T c τ‖^2| ≤
      M * (2*π*P.L T * ∑ i, ‖c i‖^2) := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ∫ τ, M * ‖zetaSamplingSynthesis P T c τ‖^2 :=
        norm_integral_le_of_norm_le (hi.const_mul M) (Eventually.of_forall fun τ => by
          rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (‖zetaSamplingSynthesis P T c τ‖))]
          exact mul_le_mul_of_nonneg_right (hb τ) (sq_nonneg _))
      _ = M * ∫ τ, ‖zetaSamplingSynthesis P T c τ‖^2 := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_zetaSamplingSynthesis_sq_le hP hwL c) hM
  calc
    _ ≤ (M * (2*π*P.L T * ∑ i, ‖c i‖^2)) / (P.a T * P.L T^2) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by field_simp <;> ring

/-- The literal pole matrix obeys the full-line quadratic estimate. -/
theorem norm_zetaSamplingCompression_pole_le {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8 * P.w ≤ P.L T) (hT : 0 < T) :
    ‖zetaSamplingCompression P T (PiX (P.X T))‖ ≤
      poleCompressionConstant P * Real.sqrt (P.X T) / (P.a T * P.L T * T) := by
  have hL : 0 < P.L T := by linarith only [hwL,hP.one_le_w]
  have ha : 0 < P.a T := by have := Params.half_le_a hP hwL; linarith only [this]
  have hX : 1 ≤ P.X T := by
    change 1 ≤ Real.exp (P.L T)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hL.le
  have hb (τ : ℝ) : |PiX (P.X T) τ| ≤ 3*Real.sqrt (P.X T) + |τ| := by
    have hh := (PiX_abs_le hX τ).trans
      (div_le_self (by positivity) (by linarith only [abs_nonneg τ]))
    exact hh.trans (le_add_of_nonneg_right (abs_nonneg τ))
  apply hermitian_l2Norm_le_of_quadratic_bound (zetaSamplingCompression_isHermitian _ _ _)
    (by have := poleCompressionConstant_pos P; positivity)
  intro c
  rw [zetaSamplingCompression_quadratic (fun i j =>
    integrable_linearDensity_sampling_mul hP hwL (PiX_continuous (by positivity : 0 < P.X T)) hb _ _) c,
    Complex.ofReal_re]
  exact abs_normalizedPoleQuadratic_le_sqrt_div hP hwL hT c

/-- The full-line pole matrix tends to zero in operator norm. -/
theorem zetaSamplingCompression_pole_uniformly_small {P : Params} (hP : P.Valid)
    {ε : ℝ} (hε : 0 < ε) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ‖zetaSamplingCompression P T (PiX (P.X T))‖ ≤ ε := by
  obtain ⟨T₁,hT₁⟩ := normalizedPoleQuadratic_uniformly_small hP hε
  obtain ⟨T₂,hT₂⟩ := zetaSampling_bandwidth_eventually_ge hP (8*P.w)
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hwL := hT₂ T ((le_max_right _ _).trans hT)
  have hL : 0 < P.L T := by linarith only [hwL,hP.one_le_w]
  have hX : 1 ≤ P.X T := by
    change 1 ≤ Real.exp (P.L T)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hL.le
  have hb (τ : ℝ) : |PiX (P.X T) τ| ≤ 3*Real.sqrt (P.X T) + |τ| := by
    have hh := (PiX_abs_le hX τ).trans
      (div_le_self (by positivity) (by linarith only [abs_nonneg τ]))
    exact hh.trans (le_add_of_nonneg_right (abs_nonneg τ))
  apply hermitian_l2Norm_le_of_quadratic_bound (zetaSamplingCompression_isHermitian _ _ _) hε.le
  intro c
  rw [zetaSamplingCompression_quadratic (fun i j =>
    integrable_linearDensity_sampling_mul hP hwL (PiX_continuous (by positivity : 0 < P.X T)) hb _ _) c,
    Complex.ofReal_re]
  exact hT₁ T ((le_max_left _ _).trans hT) c

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.zetaSamplingCompression_archimedean_centered_fourth_small
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.zetaSamplingCompression_pole_uniformly_small
