import GaloisForLFunctions.RHTower.CCM.CCMParityCauchyPairExclusion
import GaloisForLFunctions.HTGeometry.KroneckerFlowDensity

/-!
# Leading-order CCM parity: the odd sector wins for independent top ordinates

Let `σ_j = t_j + iδ` be a top layer of off-line spectral points (`t_j > 0` distinct, `δ > 0`) with
multiplicities `M_j > 0`. The leading-order parity operator `T(θ) = Re Σ_j M_j e^{iθ_j} ψ_j ⊗ ψ_j`,
`ψ_j(s) = e^{−(δ − it_j)s}`, acts on the real span `V` of the `ψ_j, ψ̄_j` in `L²(0, ∞)`. A real
`u ∈ V` is `u = Σ_j x_j ψ_j + x̄_j ψ̄_j`, `x ∈ ℂ^m`. Then `‖u‖² = zᵀGz` and `⟨Tu, u⟩ = Re Σ_i c_i (Gz)_i²`
with `z = (x, x̄)`, `G = [(p_i + p_l)⁻¹]` the Cauchy Gram matrix and `c = ((M/2)e^{iθ}, (M/2)e^{−iθ})`
(`normForm`, `quadForm`).

* `normForm` is the integral of a square and is positive definite (`normForm_pos`), since its
  moments are `Gz` and `G` is invertible.
* `ccmLambdaMax θ`, the maximum of `quadForm` on `normForm = 1`, is attained, and every maximizer is
  an eigenvector of `diag(c)·G` (`mulVec_eq_of_isMaxOn`).
* `T(θ + π𝟙) = −T(θ)`, so `F(θ) = λ_max(θ) − λ_max(θ + π𝟙) = λ_max + λ_min` is antisymmetric
  under the half-turn. `F(θ) = 0` would give an eigenvalue pair `±μ` of `diag(c)·G`, which is
  excluded at arbitrarily large apertures (MUST-936, `ccm_exists_large_aperture_no_symmetric_matrix_pair`).
* `λ_max` is Lipschitz in the weights.

**Theorem** (`ccm_exists_large_aperture_odd_wins`). If the ordinates `t_j` have no integer relation,
then for every `N` there is an aperture `a ≥ N` with `F(θ(a)) > 0`, `θ_j(a) = −2t_j a`. Kronecker's
theorem (`exists_flow_near_of_nonresonant`) brings the aperture line back near `θ(a₀) + π𝟙`.
At leading order the odd sector of the CCM restricted Weil form then has the lower ground energy.
-/

open Matrix Complex Filter Topology MeasureTheory Set

namespace RHTower.CCMParityCauchy

noncomputable section

variable {m : ℕ}

/-! ## The real structure -/

/-- The coefficient vector `(x, x̄)` of the real function `Σ_j x_j ψ_j + x̄_j ψ̄_j`. -/
def realLift (x : Fin m → ℂ) : Fin m ⊕ Fin m → ℂ := Sum.elim x fun j => (starRingEnd ℂ) (x j)

theorem realLift_add (x y : Fin m → ℂ) : realLift (x + y) = realLift x + realLift y := by
  funext i; rcases i with j | j <;> simp [realLift]

theorem realLift_real_smul (r : ℝ) (x : Fin m → ℂ) :
    realLift (fun j => (r : ℂ) * x j) = fun i => (r : ℂ) * realLift x i := by
  funext i; rcases i with j | j <;> simp [realLift]

theorem continuous_realLift : Continuous (realLift (m := m)) := by
  refine continuous_pi fun i => ?_
  rcases i with j | j
  · exact continuous_apply j
  · exact Complex.continuous_conj.comp (continuous_apply j)

theorem norm_realLift_le (x : Fin m → ℂ) (i : Fin m ⊕ Fin m) : ‖realLift x i‖ ≤ ‖x‖ := by
  rcases i with j | j
  · exact norm_le_pi_norm x j
  · simp only [realLift, Sum.elim_inr, Complex.norm_conj]; exact norm_le_pi_norm x j

/-- The norm form `zᵀGz = ‖u‖²`. -/
def normForm (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) : ℝ :=
  (realLift x ⬝ᵥ (cauchyGram (ccmNodes δ t) *ᵥ realLift x)).re

/-- The parity weights `(M_j/2)e^{±iθ_j}`. -/
def phaseWeight (M θ : Fin m → ℝ) : Fin m ⊕ Fin m → ℂ :=
  Sum.elim (fun j => ((M j / 2 : ℝ) : ℂ) * Complex.exp ((θ j : ℂ) * I))
    (fun j => ((M j / 2 : ℝ) : ℂ) * Complex.exp (-((θ j : ℂ) * I)))

/-- The quadratic form `⟨T(θ)u, u⟩ = Re Σ_i c_i (Gz)_i²`. -/
def quadForm (δ : ℝ) (t M θ : Fin m → ℝ) (x : Fin m → ℂ) : ℝ :=
  (∑ i, phaseWeight M θ i * ((cauchyGram (ccmNodes δ t) *ᵥ realLift x) i) ^ 2).re

/-! ## The norm form is an integral of a square -/

/-- The profile `Σ_i z_i e^{−p_i s}`. -/
def nodeProfile {ι : Type*} [Fintype ι] (p z : ι → ℂ) (s : ℝ) : ℂ :=
  ∑ i, z i * Complex.exp (-p i * s)

theorem integrable_exp_neg_add {a b : ℂ} (h : 0 < (a + b).re) :
    IntegrableOn (fun s : ℝ => Complex.exp (-(a + b) * s)) (Ioi 0) := by
  exact integrableOn_exp_mul_complex_Ioi (by simp only [neg_re]; linarith) 0

theorem cauchyGram_mulVec_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℂ}
    (hp : ∀ i l, 0 < (p i + p l).re) (z : ι → ℂ) (l : ι) :
    (cauchyGram p *ᵥ z) l = ∫ s in Ioi (0 : ℝ), Complex.exp (-p l * s) * nodeProfile p z s := by
  simp only [nodeProfile, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => by
    have := (integrable_exp_neg_add (hp l i)).const_mul (z i)
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    rw [show -(p l + p i) * (s : ℂ) = -p l * s + -p i * s by ring, Complex.exp_add]
    ring]
  simp only [mulVec, dotProduct, cauchyGram, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∫ s in Ioi (0 : ℝ), Complex.exp (-p l * s) * (z i * Complex.exp (-p i * s)) =
      z i * ∫ s in Ioi (0 : ℝ), Complex.exp (-(p l + p i) * s) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [show -(p l + p i) * (s : ℂ) = -p l * s + -p i * s by ring, Complex.exp_add]
    ring
  rw [h1, integral_exp_neg_mul_Ioi (hp l i)]
  ring

theorem dotProduct_cauchyGram_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℂ}
    (hp : ∀ i l, 0 < (p i + p l).re) (z : ι → ℂ) :
    z ⬝ᵥ (cauchyGram p *ᵥ z) = ∫ s in Ioi (0 : ℝ), nodeProfile p z s ^ 2 := by
  have hint : ∀ l, IntegrableOn (fun s : ℝ => z l * (Complex.exp (-p l * s) * nodeProfile p z s))
      (Ioi 0) := by
    intro l
    simp only [nodeProfile, Finset.mul_sum]
    refine integrable_finsetSum _ fun i _ => ?_
    have := (integrable_exp_neg_add (hp l i)).const_mul (z l * z i)
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    rw [show -(p l + p i) * (s : ℂ) = -p l * s + -p i * s by ring, Complex.exp_add]
    ring
  simp only [dotProduct]
  simp_rw [cauchyGram_mulVec_eq_integral hp z, ← integral_const_mul]
  rw [← integral_finsetSum _ fun l _ => hint l]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [nodeProfile]
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The real profile `2 Re Σ_j x_j e^{−(δ − it_j)s}` of the real function with coefficients `x`. -/
def realProfile (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (s : ℝ) : ℝ :=
  2 * (∑ j, x j * Complex.exp (-((δ : ℂ) - I * t j) * s)).re

theorem nodeProfile_realLift (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (s : ℝ) :
    nodeProfile (ccmNodes δ t) (realLift x) s = (realProfile δ t x s : ℂ) := by
  simp only [nodeProfile, Fintype.sum_sum_type, realLift, ccmNodes, Sum.elim_inl, Sum.elim_inr,
    realProfile]
  have hconj : ∀ j, (starRingEnd ℂ) (x j) * Complex.exp (-((δ : ℂ) + I * t j) * s) =
      (starRingEnd ℂ) (x j * Complex.exp (-((δ : ℂ) - I * t j) * s)) := by
    intro j
    have he : (starRingEnd ℂ) (-((δ : ℂ) - I * t j) * s) = -((δ : ℂ) + I * t j) * s := by
      simp only [map_mul, map_neg, map_sub, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [map_mul, ← Complex.exp_conj, he]
  simp_rw [hconj]
  rw [← map_sum, Complex.add_conj]

theorem continuous_realProfile (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    Continuous (realProfile δ t x) := by
  unfold realProfile
  fun_prop

/-- **The norm form is `‖u‖² = ∫_0^∞ u²`.** -/
theorem normForm_eq_integral {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    normForm δ t x = ∫ s in Ioi (0 : ℝ), realProfile δ t x s ^ 2 := by
  unfold normForm
  rw [dotProduct_cauchyGram_eq_integral (ccmNodes_re_add_pos hδ t)]
  simp_rw [nodeProfile_realLift]
  have hfun : (fun s : ℝ => ((realProfile δ t x s : ℝ) : ℂ) ^ 2) =
      fun s : ℝ => ((realProfile δ t x s ^ 2 : ℝ) : ℂ) := by funext s; push_cast; rfl
  simp only [hfun]
  rw [integral_complex_ofReal, Complex.ofReal_re]

theorem integrableOn_realProfile_sq {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    IntegrableOn (fun s => realProfile δ t x s ^ 2) (Ioi 0) := by
  have hp := ccmNodes_re_add_pos hδ t
  have hint : IntegrableOn (fun s : ℝ => nodeProfile (ccmNodes δ t) (realLift x) s ^ 2) (Ioi 0) := by
    simp only [nodeProfile, sq, Finset.sum_mul, Finset.mul_sum]
    refine integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => ?_
    have := (integrable_exp_neg_add (hp l i)).const_mul (realLift x l * realLift x i)
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    rw [show -(ccmNodes δ t l + ccmNodes δ t i) * (s : ℂ) =
      -ccmNodes δ t l * s + -ccmNodes δ t i * s by ring, Complex.exp_add]
    ring
  simp_rw [nodeProfile_realLift] at hint
  have := hint.re
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  rw [show ((realProfile δ t x s : ℂ)) ^ 2 = ((realProfile δ t x s ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  exact RCLike.ofReal_re _

theorem normForm_nonneg {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    0 ≤ normForm δ t x := by
  rw [normForm_eq_integral hδ]
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _

/-- **The norm form is positive definite.** -/
theorem normForm_pos {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) {x : Fin m → ℂ} (hx : x ≠ 0) : 0 < normForm δ t x := by
  refine lt_of_le_of_ne (normForm_nonneg hδ t x) fun h0 => hx ?_
  rw [eq_comm, normForm_eq_integral hδ] at h0
  -- the profile vanishes on `(0, ∞)`
  have hae := (integral_eq_zero_iff_of_nonneg (fun s => sq_nonneg (realProfile δ t x s))
    (integrableOn_realProfile_sq hδ t x)).mp h0
  have hzero : ∀ s ∈ Ioi (0 : ℝ), realProfile δ t x s = 0 := by
    intro s₀ hs₀
    by_contra hne
    set U : Set ℝ := Ioi 0 ∩ {s | realProfile δ t x s ≠ 0} with hU
    have hUopen : IsOpen U :=
      isOpen_Ioi.inter (isOpen_ne_fun (continuous_realProfile δ t x) continuous_const)
    have hUnull : volume U = 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi] at hae
      refine measure_mono_null (fun s hs => ?_) (ae_iff.mp hae)
      simp only [Set.mem_setOf_eq, Pi.zero_apply]
      intro h
      exact hs.2 (pow_eq_zero_iff two_ne_zero |>.mp (h hs.1))
    rw [IsOpen.measure_eq_zero_iff volume hUopen] at hUnull
    exact (hUnull ▸ (show s₀ ∈ U from ⟨hs₀, hne⟩) : s₀ ∈ (∅ : Set ℝ))
  -- hence every moment vanishes, and `G` is invertible
  have hGz : cauchyGram (ccmNodes δ t) *ᵥ realLift x = 0 := by
    funext l
    rw [cauchyGram_mulVec_eq_integral (ccmNodes_re_add_pos hδ t), Pi.zero_apply]
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ)) fun s hs => by
      simp only
      rw [nodeProfile_realLift, hzero s hs, Complex.ofReal_zero, mul_zero]]
    simp
  have hdet : (cauchyGram (ccmNodes δ t)).det ≠ 0 := by
    have := det_cauchyGram_submatrix_ne_zero (ccmNodes_injective ht htpos)
      (fun i l h => by
        have := ccmNodes_re_add_pos hδ t i l
        rw [h, Complex.zero_re] at this
        exact lt_irrefl _ this) (e := id) Function.injective_id
    simpa using this
  have hz : realLift x = 0 := by
    by_contra hz
    exact hdet ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨realLift x, hz, hGz⟩)
  funext j
  have := congr_fun hz (Sum.inl j)
  simpa [realLift] using this

/-! ## Compactness of the unit level set -/

theorem cauchyGram_symm {ι : Type*} (p : ι → ℂ) (i l : ι) : cauchyGram p i l = cauchyGram p l i := by
  simp [cauchyGram, add_comm]

theorem sum_mul_mulVec_comm {ι : Type*} [Fintype ι] (p : ι → ℂ) (z w : ι → ℂ) :
    ∑ i, w i * (cauchyGram p *ᵥ z) i = ∑ i, z i * (cauchyGram p *ᵥ w) i := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [cauchyGram_symm p l i]
  ring

theorem continuous_normForm (δ : ℝ) (t : Fin m → ℝ) : Continuous (normForm δ t) :=
  Complex.continuous_re.comp (continuous_realLift.dotProduct
    (continuous_const.matrix_mulVec continuous_realLift))

theorem continuous_quadForm (δ : ℝ) (t M θ : Fin m → ℝ) : Continuous (quadForm δ t M θ) := by
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
  refine continuous_const.mul (Continuous.pow ?_ 2)
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_realLift)

theorem normForm_smul (δ : ℝ) (t : Fin m → ℝ) (r : ℝ) (x : Fin m → ℂ) :
    normForm δ t (fun j => (r : ℂ) * x j) = r ^ 2 * normForm δ t x := by
  unfold normForm
  rw [realLift_real_smul]
  have h : (fun i => (r : ℂ) * realLift x i) = (r : ℂ) • realLift x := rfl
  rw [h, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← sq]
  rw [show ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]

theorem quadForm_real_smul (δ : ℝ) (t M θ : Fin m → ℝ) (r : ℝ) (x : Fin m → ℂ) :
    quadForm δ t M θ (fun j => (r : ℂ) * x j) = r ^ 2 * quadForm δ t M θ x := by
  unfold quadForm
  rw [realLift_real_smul]
  have h : (fun i => (r : ℂ) * realLift x i) = (r : ℂ) • realLift x := rfl
  rw [h, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [show (∑ i, phaseWeight M θ i * ((r : ℂ) ^ 2 * (cauchyGram (ccmNodes δ t) *ᵥ realLift x) i ^ 2))
    = ((r ^ 2 : ℝ) : ℂ) * ∑ i, phaseWeight M θ i * (cauchyGram (ccmNodes δ t) *ᵥ realLift x) i ^ 2
    by rw [Finset.mul_sum]; push_cast; exact Finset.sum_congr rfl fun i _ => by ring,
    Complex.re_ofReal_mul]

theorem normForm_zero (δ : ℝ) (t : Fin m → ℝ) : normForm δ t 0 = 0 := by
  have := normForm_smul δ t 0 0
  simp only [Complex.ofReal_zero, zero_mul, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at this
  exact this

theorem quadForm_at_zero (δ : ℝ) (t M θ : Fin m → ℝ) : quadForm δ t M θ 0 = 0 := by
  have := quadForm_real_smul δ t M θ 0 0
  simp only [Complex.ofReal_zero, zero_mul, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at this
  exact this

/-- **Coercivity:** `normForm x ≥ κ‖x‖²`. -/
theorem exists_normForm_coercive {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x, κ * ‖x‖ ^ 2 ≤ normForm δ t x := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    subst this
    rw [normForm_zero, norm_zero]
    simp
  have hne : (Metric.sphere (0 : Fin m → ℂ) 1).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    rw [mem_sphere_zero_iff_norm]
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    simp [pi_norm_const]
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : Fin m → ℂ) 1).exists_isMinOn hne
    (continuous_normForm δ t).continuousOn
  have hx₀ne : x₀ ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx₀; exact zero_ne_one hx₀
  refine ⟨normForm δ t x₀, normForm_pos hδ ht htpos hx₀ne, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, normForm_zero, norm_zero]; simp
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set y : Fin m → ℂ := fun j => ((‖x‖⁻¹ : ℝ) : ℂ) * x j with hy
    have hy1 : y ∈ Metric.sphere (0 : Fin m → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      have : y = (‖x‖⁻¹ : ℂ) • x := by
        funext j; simp [hy]
      rw [this, norm_smul]
      simp [hnx.ne']
    have h1 := hmin hy1
    simp only [Set.mem_setOf_eq] at h1
    rw [hy, normForm_smul] at h1
    have hxy : normForm δ t x = ‖x‖ ^ 2 * (‖x‖⁻¹ ^ 2 * normForm δ t x) := by
      field_simp
    rw [hxy]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _) |>.trans_eq' (by ring)

/-- The unit level set of the norm form. -/
def unitLevel (δ : ℝ) (t : Fin m → ℝ) : Set (Fin m → ℂ) := {x | normForm δ t x = 1}

theorem isCompact_unitLevel {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) : IsCompact (unitLevel δ t) := by
  obtain ⟨κ, hκ, hcoer⟩ := exists_normForm_coercive hδ ht htpos
  refine (isCompact_closedBall (0 : Fin m → ℂ) (Real.sqrt (1 / κ))).of_isClosed_subset
    (isClosed_eq (continuous_normForm δ t) continuous_const) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := hcoer x
  rw [unitLevel, Set.mem_setOf_eq] at hx
  rw [hx] at h1
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ hκ]
  linarith

theorem unitLevel_nonempty {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) : (unitLevel δ t).Nonempty := by
  set x₀ : Fin m → ℂ := fun _ => 1 with hx₀
  have hne : x₀ ≠ 0 := by
    intro h; have := congr_fun h ⟨0, hm⟩; simp [hx₀] at this
  have hpos := normForm_pos hδ ht htpos hne
  refine ⟨fun j => ((Real.sqrt (normForm δ t x₀))⁻¹ : ℝ) * x₀ j, ?_⟩
  rw [unitLevel, Set.mem_setOf_eq, normForm_smul, inv_pow, Real.sq_sqrt hpos.le,
    inv_mul_cancel₀ hpos.ne']

/-! ## The top of the spectrum -/

/-- `λ_max(T(θ))` on the real span: the maximum of the quadratic form on the unit level set. -/
def ccmLambdaMax (δ : ℝ) (t M θ : Fin m → ℝ) : ℝ :=
  sSup (quadForm δ t M θ '' unitLevel δ t)

theorem exists_isMaxOn_quadForm {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) :
    ∃ x ∈ unitLevel δ t, quadForm δ t M θ x = ccmLambdaMax δ t M θ ∧
      ∀ y ∈ unitLevel δ t, quadForm δ t M θ y ≤ ccmLambdaMax δ t M θ := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_unitLevel hδ ht htpos).exists_isMaxOn
    (unitLevel_nonempty hδ ht htpos hm) (continuous_quadForm δ t M θ).continuousOn
  have hbdd : BddAbove (quadForm δ t M θ '' unitLevel δ t) :=
    ((isCompact_unitLevel hδ ht htpos).image (continuous_quadForm δ t M θ)).bddAbove
  have hle : ∀ y ∈ unitLevel δ t, quadForm δ t M θ y ≤ ccmLambdaMax δ t M θ :=
    fun y hy => le_csSup hbdd (Set.mem_image_of_mem _ hy)
  refine ⟨x, hx, le_antisymm (hle x hx) ?_, hle⟩
  exact csSup_le ((unitLevel_nonempty hδ ht htpos hm).image _) fun v ⟨y, hy, hyv⟩ =>
    hyv ▸ hmax hy

/-- **Homogeneous bound:** `⟨T u, u⟩ ≤ λ_max ‖u‖²`. -/
theorem quadForm_le_lambdaMax_mul {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    (x : Fin m → ℂ) : quadForm δ t M θ x ≤ ccmLambdaMax δ t M θ * normForm δ t x := by
  obtain ⟨-, -, -, hle⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  by_cases hx : x = 0
  · rw [hx, quadForm_at_zero, normForm_zero, mul_zero]
  have hpos := normForm_pos hδ ht htpos hx
  set r : ℝ := (Real.sqrt (normForm δ t x))⁻¹ with hr
  have hy : (fun j => (r : ℂ) * x j) ∈ unitLevel δ t := by
    rw [unitLevel, Set.mem_setOf_eq, normForm_smul, hr, inv_pow, Real.sq_sqrt hpos.le,
      inv_mul_cancel₀ hpos.ne']
  have h1 := hle _ hy
  rw [quadForm_real_smul, hr, inv_pow, Real.sq_sqrt hpos.le] at h1
  rw [inv_mul_le_iff₀ hpos] at h1
  linarith

/-! ## The Lagrange condition -/

/-- Real coefficient vectors: `v (σ i) = conj (v i)` for the swap `σ` of the two copies. -/
def IsRealVec (v : Fin m ⊕ Fin m → ℂ) : Prop := ∀ i, v (Sum.swap i) = (starRingEnd ℂ) (v i)

theorem isRealVec_realLift (x : Fin m → ℂ) : IsRealVec (realLift x) := by
  intro i; rcases i with j | j <;> simp [realLift]

theorem cauchyGram_ccmNodes_swap (δ : ℝ) (t : Fin m → ℝ) (i l : Fin m ⊕ Fin m) :
    cauchyGram (ccmNodes δ t) (Sum.swap i) (Sum.swap l) =
      (starRingEnd ℂ) (cauchyGram (ccmNodes δ t) i l) := by
  rcases i with j | j <;> rcases l with k | k <;>
    simp [cauchyGram, ccmNodes, map_inv₀, map_add, map_sub, map_mul, Complex.conj_ofReal,
      Complex.conj_I] <;> ring_nf

theorem isRealVec_cauchyGram_mulVec (δ : ℝ) (t : Fin m → ℝ) {v : Fin m ⊕ Fin m → ℂ}
    (hv : IsRealVec v) : IsRealVec (cauchyGram (ccmNodes δ t) *ᵥ v) := by
  intro i
  simp only [mulVec, dotProduct]
  rw [map_sum]
  rw [← (Equiv.sumComm (Fin m) (Fin m)).sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Equiv.sumComm_apply]
  rw [cauchyGram_ccmNodes_swap, hv l, map_mul]

theorem isRealVec_phaseWeight_mul (M θ : Fin m → ℝ) {v : Fin m ⊕ Fin m → ℂ} (hv : IsRealVec v) :
    IsRealVec fun i => phaseWeight M θ i * v i := by
  intro i
  show phaseWeight M θ (Sum.swap i) * v (Sum.swap i) = (starRingEnd ℂ) (phaseWeight M θ i * v i)
  rw [hv i, map_mul]
  congr 1
  rcases i with j | j <;>
    simp [phaseWeight, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]

theorem isRealVec_sub {v w : Fin m ⊕ Fin m → ℂ} (hv : IsRealVec v) (hw : IsRealVec w) :
    IsRealVec (v - w) := by
  intro i; simp [hv i, hw i]

theorem isRealVec_real_smul (r : ℝ) {v : Fin m ⊕ Fin m → ℂ} (hv : IsRealVec v) :
    IsRealVec fun i => (r : ℂ) * v i := by
  intro i; simp [hv i]

/-- A real vector orthogonal to every real vector vanishes. -/
theorem eq_zero_of_isRealVec_of_re_sum_eq_zero {v : Fin m ⊕ Fin m → ℂ} (hv : IsRealVec v)
    (h : ∀ y : Fin m → ℂ, (∑ i, realLift y i * v i).re = 0) : v = 0 := by
  have hsingle : ∀ (j : Fin m) (c : ℂ),
      ∑ i, realLift (Pi.single j c) i * v i =
        c * v (Sum.inl j) + (starRingEnd ℂ) c * v (Sum.inr j) := by
    intro j c
    rw [Fintype.sum_sum_type]
    simp only [realLift, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp
    · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp
  have hinl : ∀ j, v (Sum.inl j) = 0 := by
    intro j
    have h1 := h (Pi.single j 1)
    have h2 := h (Pi.single j I)
    rw [hsingle] at h1 h2
    have hr : v (Sum.inr j) = (starRingEnd ℂ) (v (Sum.inl j)) := hv (Sum.inl j)
    rw [hr] at h1 h2
    simp only [map_one, one_mul, Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.conj_im, Complex.conj_I, Complex.neg_re, Complex.neg_im] at h1 h2
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith
    · simp only [Complex.zero_im]; linarith
  funext i
  rcases i with j | j
  · exact hinl j
  · rw [Pi.zero_apply, show (Sum.inr j : Fin m ⊕ Fin m) = Sum.swap (Sum.inl j) from rfl, hv,
      hinl j, map_zero]

theorem le_zero_mul_of_forall {a b : ℝ} (h : ∀ s : ℝ, b * s + a * s ^ 2 ≤ 0) : b = 0 := by
  by_contra hb
  have hA : 0 < |a| + 1 := by positivity
  set s : ℝ := b / (2 * (|a| + 1)) with hs
  have h1 := h s
  have hbs : b * s = b ^ 2 / (2 * (|a| + 1)) := by rw [hs]; field_simp
  have hs2 : s ^ 2 = b ^ 2 / (4 * (|a| + 1) ^ 2) := by rw [hs]; field_simp; ring
  have has : -|a| * s ^ 2 ≤ a * s ^ 2 :=
    mul_le_mul_of_nonneg_right (neg_abs_le a) (sq_nonneg s)
  have hb2 : 0 < b ^ 2 := by positivity
  have key : 0 < b ^ 2 / (2 * (|a| + 1)) + -|a| * (b ^ 2 / (4 * (|a| + 1) ^ 2)) := by
    have : b ^ 2 / (2 * (|a| + 1)) + -|a| * (b ^ 2 / (4 * (|a| + 1) ^ 2)) =
        b ^ 2 * (|a| + 2) / (4 * (|a| + 1) ^ 2) := by field_simp; ring
    rw [this]; positivity
  rw [hs2] at has
  rw [hbs, hs2] at h1
  linarith

/-- **Maximizers are eigenvectors.** A maximizer of the quadratic form on the unit level set is an
eigenvector of `diag(c)·G` with eigenvalue `λ_max`. -/
theorem mulVec_eq_of_isMaxOn {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) {x : Fin m → ℂ}
    (hx : x ∈ unitLevel δ t) (hxmax : quadForm δ t M θ x = ccmLambdaMax δ t M θ) :
    (diagonal (phaseWeight M θ) * cauchyGram (ccmNodes δ t)) *ᵥ realLift x =
      (ccmLambdaMax δ t M θ : ℂ) • realLift x := by
  set G := cauchyGram (ccmNodes δ t) with hG
  set c := phaseWeight M θ with hc
  set lam := ccmLambdaMax δ t M θ with hlam
  set z := realLift x with hz
  have hxn : normForm δ t x = 1 := hx
  -- the first variation vanishes
  have hvar : ∀ y : Fin m → ℂ,
      (∑ i, c i * ((G *ᵥ z) i * (G *ᵥ realLift y) i)).re =
        lam * (∑ i, z i * (G *ᵥ realLift y) i).re := by
    intro y
    have hpoint : ∀ s : ℝ,
        2 * ((∑ i, c i * ((G *ᵥ z) i * (G *ᵥ realLift y) i)).re -
            lam * (∑ i, z i * (G *ᵥ realLift y) i).re) * s +
          (quadForm δ t M θ y - lam * normForm δ t y) * s ^ 2 ≤ 0 := by
      intro s
      have hb := quadForm_le_lambdaMax_mul hδ ht htpos hm M θ (fun j => x j + (s : ℂ) * y j)
      have hlift : realLift (fun j => x j + (s : ℂ) * y j) =
          fun i => z i + (s : ℂ) * realLift y i := by
        funext i; rcases i with j | j <;> simp [realLift, hz]
      have hGlift : G *ᵥ realLift (fun j => x j + (s : ℂ) * y j) =
          fun i => (G *ᵥ z) i + (s : ℂ) * (G *ᵥ realLift y) i := by
        rw [hlift]
        funext i
        simp only [mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun l _ => by ring
      have hQ : quadForm δ t M θ (fun j => x j + (s : ℂ) * y j) =
          quadForm δ t M θ x + 2 * s * (∑ i, c i * ((G *ᵥ z) i * (G *ᵥ realLift y) i)).re +
            s ^ 2 * quadForm δ t M θ y := by
        unfold quadForm
        rw [hGlift]
        simp only [← hG, ← hc, ← hz]
        rw [show (∑ i, c i * ((G *ᵥ z) i + (s : ℂ) * (G *ᵥ realLift y) i) ^ 2) =
          (∑ i, c i * (G *ᵥ z) i ^ 2) + ((2 * s : ℝ) : ℂ) *
            (∑ i, c i * ((G *ᵥ z) i * (G *ᵥ realLift y) i)) +
            ((s ^ 2 : ℝ) : ℂ) * (∑ i, c i * (G *ᵥ realLift y) i ^ 2) by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          push_cast; ring]
        rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have hN : normForm δ t (fun j => x j + (s : ℂ) * y j) =
          normForm δ t x + 2 * s * (∑ i, z i * (G *ᵥ realLift y) i).re +
            s ^ 2 * normForm δ t y := by
        unfold normForm
        rw [hGlift, hlift]
        simp only [dotProduct, ← hG, ← hz]
        have hsym := sum_mul_mulVec_comm (ccmNodes δ t) z (realLift y)
        rw [← hG] at hsym
        rw [show (∑ i, (z i + (s : ℂ) * realLift y i) * ((G *ᵥ z) i + (s : ℂ) * (G *ᵥ realLift y) i))
          = (∑ i, z i * (G *ᵥ z) i) + ((2 * s : ℝ) : ℂ) * (∑ i, z i * (G *ᵥ realLift y) i) +
            ((s ^ 2 : ℝ) : ℂ) * (∑ i, realLift y i * (G *ᵥ realLift y) i) by
          have e1 : (∑ i, (z i + (s : ℂ) * realLift y i) *
              ((G *ᵥ z) i + (s : ℂ) * (G *ᵥ realLift y) i)) =
              (∑ i, z i * (G *ᵥ z) i) + (s : ℂ) * (∑ i, z i * (G *ᵥ realLift y) i) +
                (s : ℂ) * (∑ i, realLift y i * (G *ᵥ z) i) +
                ((s : ℂ) ^ 2) * (∑ i, realLift y i * (G *ᵥ realLift y) i) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
              ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [e1, hsym]
          push_cast; ring]
        rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      rw [hQ, hN, hxn, hxmax] at hb
      nlinarith
    have := le_zero_mul_of_forall hpoint
    linarith
  -- the residual vector
  set v : Fin m ⊕ Fin m → ℂ :=
    (G *ᵥ fun i => c i * (G *ᵥ z) i) - fun i => (lam : ℂ) * (G *ᵥ z) i with hv
  have hvreal : IsRealVec v := by
    apply isRealVec_sub
    · exact isRealVec_cauchyGram_mulVec δ t
        (isRealVec_phaseWeight_mul M θ (isRealVec_cauchyGram_mulVec δ t (isRealVec_realLift x)))
    · exact isRealVec_real_smul lam (isRealVec_cauchyGram_mulVec δ t (isRealVec_realLift x))
  have horth : ∀ y : Fin m → ℂ, (∑ i, realLift y i * v i).re = 0 := by
    intro y
    have h1 := hvar y
    have hA : (∑ i, realLift y i * (G *ᵥ fun i => c i * (G *ᵥ z) i) i) =
        ∑ i, c i * ((G *ᵥ z) i * (G *ᵥ realLift y) i) := by
      have := sum_mul_mulVec_comm (ccmNodes δ t) (fun i => c i * (G *ᵥ z) i) (realLift y)
      rw [← hG] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hB : (∑ i, realLift y i * (G *ᵥ z) i) = ∑ i, z i * (G *ᵥ realLift y) i := by
      have := sum_mul_mulVec_comm (ccmNodes δ t) z (realLift y)
      rw [← hG] at this
      exact this
    simp only [hv, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hA, show (∑ i, realLift y i * ((lam : ℂ) * (G *ᵥ z) i)) =
      (lam : ℂ) * ∑ i, realLift y i * (G *ᵥ z) i by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hB,
      Complex.sub_re, Complex.re_ofReal_mul, h1, sub_self]
  have hv0 := eq_zero_of_isRealVec_of_re_sum_eq_zero hvreal horth
  -- invert `G`
  have hdet : G.det ≠ 0 := by
    have := det_cauchyGram_submatrix_ne_zero (ccmNodes_injective ht htpos)
      (fun i l h => by
        have := ccmNodes_re_add_pos hδ t i l
        rw [h, Complex.zero_re] at this
        exact lt_irrefl _ this) (e := id) Function.injective_id
    simpa [hG] using this
  have hres : G *ᵥ ((fun i => c i * (G *ᵥ z) i) - fun i => (lam : ℂ) * z i) = 0 := by
    rw [Matrix.mulVec_sub]
    have : G *ᵥ (fun i => (lam : ℂ) * z i) = fun i => (lam : ℂ) * (G *ᵥ z) i := by
      have h' : (fun i => (lam : ℂ) * z i) = (lam : ℂ) • z := rfl
      rw [h', Matrix.mulVec_smul]; rfl
    rw [this]
    exact hv0
  have hzero : (fun i => c i * (G *ᵥ z) i) - (fun i => (lam : ℂ) * z i) = 0 := by
    by_contra hne
    exact hdet ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨_, hne, hres⟩)
  rw [← Matrix.mulVec_mulVec]
  funext i
  have := congr_fun hzero i
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  rw [Matrix.mulVec_diagonal, this]
  rfl

/-! ## The half-turn and the parity balance -/

/-- `θ + π𝟙`. -/
def halfTurn (θ : Fin m → ℝ) : Fin m → ℝ := fun j => θ j + Real.pi

theorem phaseWeight_halfTurn (M θ : Fin m → ℝ) :
    phaseWeight M (halfTurn θ) = -phaseWeight M θ := by
  funext i
  rcases i with j | j
  · simp only [phaseWeight, halfTurn, Sum.elim_inl, Pi.neg_apply]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · simp only [phaseWeight, halfTurn, Sum.elim_inr, Pi.neg_apply]
    push_cast
    rw [add_mul, neg_add, Complex.exp_add, Complex.exp_neg ((Real.pi : ℂ) * I),
      Complex.exp_pi_mul_I]
    norm_num

theorem phaseWeight_halfTurn_halfTurn (M θ : Fin m → ℝ) :
    phaseWeight M (halfTurn (halfTurn θ)) = phaseWeight M θ := by
  rw [phaseWeight_halfTurn, phaseWeight_halfTurn, neg_neg]

theorem quadForm_halfTurn (δ : ℝ) (t M θ : Fin m → ℝ) (x : Fin m → ℂ) :
    quadForm δ t M (halfTurn θ) x = -quadForm δ t M θ x := by
  unfold quadForm
  rw [phaseWeight_halfTurn]
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Complex.neg_re]

theorem ccmLambdaMax_halfTurn_halfTurn (δ : ℝ) (t M θ : Fin m → ℝ) :
    ccmLambdaMax δ t M (halfTurn (halfTurn θ)) = ccmLambdaMax δ t M θ := by
  unfold ccmLambdaMax
  congr 1
  ext v
  simp only [Set.mem_image]
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, by rw [quadForm_halfTurn,
    quadForm_halfTurn, neg_neg]⟩

/-- **The parity balance** `F(θ) = λ_max(T(θ)) + λ_min(T(θ)) = λ_max(θ) − λ_max(θ + π𝟙)`. At
leading order the odd sector of the CCM form has the lower ground energy iff `F > 0`. -/
def ccmParityBalance (δ : ℝ) (t M θ : Fin m → ℝ) : ℝ :=
  ccmLambdaMax δ t M θ - ccmLambdaMax δ t M (halfTurn θ)

theorem ccmParityBalance_halfTurn (δ : ℝ) (t M θ : Fin m → ℝ) :
    ccmParityBalance δ t M (halfTurn θ) = -ccmParityBalance δ t M θ := by
  unfold ccmParityBalance
  rw [ccmLambdaMax_halfTurn_halfTurn]
  ring

/-- The aperture weights of the CCM data are the phase weights on the aperture line. -/
theorem apertureWeight_ccm_eq_phaseWeight (t M : Fin m → ℝ) (a : ℝ) :
    apertureWeight (ccmAmp M) (ccmFreq t) a = phaseWeight M fun j => -2 * t j * a := by
  funext i
  rcases i with j | j <;>
  · simp only [apertureWeight, ccmAmp, ccmFreq, phaseWeight, Sum.elim_inl, Sum.elim_inr]
    congr 2
    push_cast
    ring

/-- **The balance is nonzero wherever `diag(c)·G` has no pair `±μ`.** -/
theorem ccmParityBalance_ne_zero {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) {M : Fin m → ℝ}
    (hM : ∀ j, M j ≠ 0) (θ : Fin m → ℝ)
    (hno : ∀ μ : ℂ, μ ≠ 0 → ∀ v w : Fin m ⊕ Fin m → ℂ, v ≠ 0 → w ≠ 0 →
      (diagonal (phaseWeight M θ) * cauchyGram (ccmNodes δ t)) *ᵥ v = μ • v →
      (diagonal (phaseWeight M θ) * cauchyGram (ccmNodes δ t)) *ᵥ w ≠ -μ • w) :
    ccmParityBalance δ t M θ ≠ 0 := by
  intro h0
  obtain ⟨x₁, hx₁, hmax₁, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  obtain ⟨x₂, hx₂, hmax₂, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M (halfTurn θ)
  have he₁ := mulVec_eq_of_isMaxOn hδ ht htpos hm M θ hx₁ hmax₁
  have he₂ := mulVec_eq_of_isMaxOn hδ ht htpos hm M (halfTurn θ) hx₂ hmax₂
  have hμ : ccmLambdaMax δ t M (halfTurn θ) = ccmLambdaMax δ t M θ := by
    unfold ccmParityBalance at h0; linarith
  rw [hμ, phaseWeight_halfTurn] at he₂
  have hneg : (diagonal (-phaseWeight M θ) * cauchyGram (ccmNodes δ t)) =
      -(diagonal (phaseWeight M θ) * cauchyGram (ccmNodes δ t)) := by
    ext i l
    simp [Matrix.diagonal_mul]
  rw [hneg, Matrix.neg_mulVec, neg_eq_iff_eq_neg, ← neg_smul] at he₂
  have hz : ∀ {x : Fin m → ℂ}, x ∈ unitLevel δ t → realLift x ≠ 0 := by
    intro x hx h
    have : normForm δ t x = 0 := by unfold normForm; rw [h]; simp
    rw [unitLevel, Set.mem_setOf_eq] at hx
    linarith
  by_cases hμ0 : (ccmLambdaMax δ t M θ : ℂ) = 0
  · -- the matrix is invertible
    rw [hμ0, zero_smul] at he₁
    have hdet : (diagonal (phaseWeight M θ) * cauchyGram (ccmNodes δ t)).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_diagonal]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) ?_
      · rcases i with j | j <;>
          simp [phaseWeight, hM j, Complex.exp_ne_zero]
      · have := det_cauchyGram_submatrix_ne_zero (ccmNodes_injective ht htpos)
          (fun i l h => by
            have := ccmNodes_re_add_pos hδ t i l
            rw [h, Complex.zero_re] at this
            exact lt_irrefl _ this) (e := id) Function.injective_id
        simpa using this
    exact hdet ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨_, hz hx₁, he₁⟩)
  · exact hno _ hμ0 _ _ (hz hx₁) (hz hx₂) he₁ he₂

/-! ## Continuity in the phases -/

theorem norm_cexp_phase_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have hsplit : Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I) =
      Complex.exp ((b : ℂ) * I) * (Complex.exp (((a - b : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast; ring_nf
  rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  set u : ℝ := a - b
  have hsq : ‖Complex.exp ((u : ℂ) * I) - 1‖ ^ 2 = 2 - 2 * Real.cos u := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := u)
  have h2 : ‖Complex.exp ((u : ℂ) * I) - 1‖ ^ 2 ≤ |u| ^ 2 := by
    rw [hsq, sq_abs]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp h2


/-- **Lipschitz control of the quadratic form in the weights**, uniformly on the unit level set. -/
theorem exists_quadForm_sub_le {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (M θ θ' : Fin m → ℝ), ∀ x ∈ unitLevel δ t,
      |quadForm δ t M θ x - quadForm δ t M θ' x| ≤
        B * ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ := by
  set f : (Fin m → ℂ) → ℝ :=
    fun x => ∑ i, ‖(cauchyGram (ccmNodes δ t) *ᵥ realLift x) i‖ ^ 2 with hf
  have hfc : Continuous f := by
    refine continuous_finsetSum _ fun i _ => (Continuous.pow ?_ 2)
    exact continuous_norm.comp ((continuous_apply i).comp
      (continuous_const.matrix_mulVec continuous_realLift))
  obtain ⟨B, hB⟩ := (isCompact_unitLevel hδ ht htpos).exists_bound_of_continuousOn
    hfc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun M θ θ' x hx => ?_⟩
  have hfx : f x ≤ max B 0 := by
    have := hB x hx
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  unfold quadForm
  rw [← Complex.sub_re, ← Finset.sum_sub_distrib]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  calc ∑ i, ‖phaseWeight M θ i * (cauchyGram (ccmNodes δ t) *ᵥ realLift x) i ^ 2 -
        phaseWeight M θ' i * (cauchyGram (ccmNodes δ t) *ᵥ realLift x) i ^ 2‖
      = ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ *
          ‖(cauchyGram (ccmNodes δ t) *ᵥ realLift x) i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_mul, norm_mul, norm_pow]
    _ ≤ ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ * f x := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ‖(cauchyGram (ccmNodes δ t) *ᵥ realLift x) i‖ ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    _ = f x * ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ max B 0 * ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ :=
        mul_le_mul_of_nonneg_right hfx (Finset.sum_nonneg fun i _ => norm_nonneg _)

theorem abs_ccmLambdaMax_sub_le {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) {B : ℝ}
    (hB : ∀ (M θ θ' : Fin m → ℝ), ∀ x ∈ unitLevel δ t,
      |quadForm δ t M θ x - quadForm δ t M θ' x| ≤
        B * ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖) (M θ θ' : Fin m → ℝ) :
    |ccmLambdaMax δ t M θ - ccmLambdaMax δ t M θ'| ≤
      B * ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ := by
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  obtain ⟨x', hx', hmax', -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ'
  obtain ⟨-, -, -, hle⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  obtain ⟨-, -, -, hle'⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ'
  have h1 := hB M θ θ' x hx
  have h2 := hB M θ θ' x' hx'
  have hsym : ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ =
      ∑ i, ‖phaseWeight M θ' i - phaseWeight M θ i‖ :=
    Finset.sum_congr rfl fun i _ => norm_sub_rev _ _
  have a1 := hle' x hx
  have a2 := hle x' hx'
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem halfTurn_sub (θ θ' : Fin m → ℝ) (j : Fin m) :
    halfTurn θ j - halfTurn θ' j = θ j - θ' j := by
  simp [halfTurn]

/-- Phase weights move by at most `|M_j|·|θ_j − θ'_j − 2πz_j|`. -/
theorem sum_norm_phaseWeight_sub_le (M θ θ' : Fin m → ℝ) {η : ℝ} (z : Fin m → ℤ)
    (hz : ∀ j, |θ j - θ' j - z j * (2 * Real.pi)| ≤ η) :
    ∑ i, ‖phaseWeight M θ i - phaseWeight M θ' i‖ ≤ (∑ j, |M j|) * η := by
  have hper : ∀ j, Complex.exp ((θ' j : ℂ) * I) =
      Complex.exp (((θ' j + z j * (2 * Real.pi) : ℝ) : ℂ) * I) := by
    intro j
    push_cast
    rw [add_mul, Complex.exp_add, show ((z j : ℂ) * (2 * Real.pi)) * I =
      (z j : ℂ) * (2 * Real.pi * I) by ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hstep : ∀ j, ‖Complex.exp ((θ j : ℂ) * I) - Complex.exp ((θ' j : ℂ) * I)‖ ≤ η := by
    intro j
    rw [hper j]
    refine (norm_cexp_phase_sub_le _ _).trans ?_
    have := hz j
    rwa [show θ j - (θ' j + z j * (2 * Real.pi)) = θ j - θ' j - z j * (2 * Real.pi) by ring]
  have hstep' : ∀ j, ‖Complex.exp (-((θ j : ℂ) * I)) - Complex.exp (-((θ' j : ℂ) * I))‖ ≤ η := by
    intro j
    have h := hstep j
    rw [show -((θ j : ℂ) * I) = ((-θ j : ℝ) : ℂ) * I by push_cast; ring,
      show -((θ' j : ℂ) * I) = ((-θ' j : ℝ) : ℂ) * I by push_cast; ring]
    have hc : Complex.exp (((-θ j : ℝ) : ℂ) * I) - Complex.exp (((-θ' j : ℝ) : ℂ) * I) =
        (starRingEnd ℂ) (Complex.exp ((θ j : ℂ) * I) - Complex.exp ((θ' j : ℂ) * I)) := by
      rw [map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
      simp [Complex.conj_ofReal, Complex.conj_I]
    rw [hc, Complex.norm_conj]
    exact h
  rw [Fintype.sum_sum_type, Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [show (∑ j, |M j| * η) = ∑ j, (|M j| / 2 * η + |M j| / 2 * η) by
    exact Finset.sum_congr rfl fun j _ => by ring]
  refine Finset.sum_le_sum fun j _ => add_le_add ?_ ?_
  · simp only [phaseWeight, Sum.elim_inl]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    exact mul_le_mul_of_nonneg_left (hstep j) (by positivity)
  · simp only [phaseWeight, Sum.elim_inr]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    exact mul_le_mul_of_nonneg_left (hstep' j) (by positivity)

/-! ## The odd sector wins -/

/-- **Positivity of the balance is open in the phases (modulo `2π`).** -/
theorem exists_phase_window_ccmParityBalance_pos {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ₁ : Fin m → ℝ)
    (hpos : 0 < ccmParityBalance δ t M θ₁) :
    ∃ η : ℝ, 0 < η ∧ ∀ (θ : Fin m → ℝ) (z : Fin m → ℤ),
      (∀ j, |θ j - θ₁ j - z j * (2 * Real.pi)| ≤ η) → 0 < ccmParityBalance δ t M θ := by
  set g : ℝ := ccmParityBalance δ t M θ₁ with hg
  obtain ⟨B, hB0, hB⟩ := exists_quadForm_sub_le hδ ht htpos
  set S : ℝ := ∑ j, |M j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨g / (4 * (B + 1) * (S + 1)), by positivity, fun θ z hphase => ?_⟩
  set η : ℝ := g / (4 * (B + 1) * (S + 1)) with hη
  have hD := sum_norm_phaseWeight_sub_le M θ θ₁ z hphase
  have hD' := sum_norm_phaseWeight_sub_le M (halfTurn θ) (halfTurn θ₁) z
    (fun j => by rw [halfTurn_sub]; exact hphase j)
  have hL1 := abs_ccmLambdaMax_sub_le hδ ht htpos hm hB M θ θ₁
  have hL2 := abs_ccmLambdaMax_sub_le hδ ht htpos hm hB M (halfTurn θ) (halfTurn θ₁)
  have hbal : ccmParityBalance δ t M θ ≥ g - 2 * (B * (S * η)) := by
    have e1 : B * ∑ i, ‖phaseWeight M θ i - phaseWeight M θ₁ i‖ ≤ B * (S * η) :=
      mul_le_mul_of_nonneg_left hD hB0
    have e2 : B * ∑ i, ‖phaseWeight M (halfTurn θ) i - phaseWeight M (halfTurn θ₁) i‖
        ≤ B * (S * η) := mul_le_mul_of_nonneg_left hD' hB0
    rw [hg]
    unfold ccmParityBalance
    rw [abs_le] at hL1 hL2
    linarith [hL1.1, hL2.2]
  have hsmall : 2 * (B * (S * η)) < g := by
    rw [hη]
    have : 2 * (B * (S * (g / (4 * (B + 1) * (S + 1))))) =
        g * (B * S) / (2 * ((B + 1) * (S + 1))) := by field_simp; ring
    rw [this, div_lt_iff₀ (by positivity)]
    have hBS : B * S < 2 * ((B + 1) * (S + 1)) := by nlinarith
    have := mul_lt_mul_of_pos_left hBS hpos
    linarith
  linarith

/-- **The aperture line returns near every admissible torus point.** If every integer relation
`Σ k_j t_j = 0` makes `Σ k_j x_j` an integer, then for arbitrarily large `a` the phases `−2t_j a`
are within `η` of `−2πx_j` modulo `2π`. -/
theorem exists_large_aperture_phase_near {t x : Fin m → ℝ}
    (hrel : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → ∃ z : ℤ, ∑ j, (k j : ℝ) * x j = z)
    {η : ℝ} (hη : 0 < η) (N : ℝ) :
    ∃ a : ℝ, N ≤ a ∧ ∃ z : Fin m → ℤ,
      ∀ j, |-2 * t j * a - (-2 * Real.pi * x j) - z j * (2 * Real.pi)| ≤ η := by
  have hrel' : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * (t j / Real.pi) = 0 →
      ∃ z : ℤ, ∑ j, (k j : ℝ) * x j = z := by
    intro k h0
    have hsum : ∑ j, (k j : ℝ) * (t j / Real.pi) = (∑ j, (k j : ℝ) * t j) / Real.pi := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, div_eq_zero_iff] at h0
    exact hrel k (h0.resolve_right Real.pi_ne_zero)
  obtain ⟨a, haN, hclose⟩ :=
    GaloisForLFunctions.HTGeometry.KroneckerFlow.exists_flow_near_of_relations x hrel'
      (show 0 < η / (2 * Real.pi) by positivity) N
  choose z hz using hclose
  refine ⟨a, haN, fun j => -z j, fun j => ?_⟩
  have hkey : -2 * t j * a - (-2 * Real.pi * x j) - ((-z j : ℤ) : ℝ) * (2 * Real.pi) =
      -(2 * Real.pi) * (a * (t j / Real.pi) - x j - z j) := by
    push_cast
    field_simp
    ring
  rw [hkey, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have := mul_lt_mul_of_pos_left (hz j) (by positivity : (0 : ℝ) < 2 * Real.pi)
  rw [mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at this
  linarith

/-- **One positive point suffices.** For every top layer, with no condition on the ordinates, the
odd sector wins at arbitrarily large apertures iff it wins at one real aperture: the aperture line
is almost periodic, so it returns near any of its points. -/
theorem ccm_frequently_odd_wins_iff {δ : ℝ} (hδ : 0 < δ) {t M : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) :
    (∀ N : ℝ, ∃ a : ℝ, N ≤ a ∧ 0 < ccmParityBalance δ t M fun j => -2 * t j * a) ↔
      ∃ a : ℝ, 0 < ccmParityBalance δ t M fun j => -2 * t j * a := by
  refine ⟨fun h => (h 0).imp fun a ha => ha.2, fun ⟨a₁, ha₁⟩ N => ?_⟩
  obtain ⟨η, hη, hwin⟩ := exists_phase_window_ccmParityBalance_pos hδ ht htpos hm M _ ha₁
  obtain ⟨a, haN, z, hz⟩ := exists_large_aperture_phase_near (x := fun j => a₁ * (t j / Real.pi))
    (fun k hk => ⟨0, by
      rw [Int.cast_zero]
      have : ∑ j, (k j : ℝ) * (a₁ * (t j / Real.pi)) = a₁ / Real.pi * ∑ j, (k j : ℝ) * t j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hk, mul_zero]⟩) hη N
  refine ⟨a, haN, hwin _ z fun j => ?_⟩
  have h := hz j
  rwa [show -2 * Real.pi * (a₁ * (t j / Real.pi)) = -2 * t j * a₁ by
    field_simp] at h

/-- **Leading-order CCM parity: the odd sector wins at arbitrarily large apertures.** For a top
layer of off-line spectral points `t_j + iδ` with distinct positive ordinates, common real offset
`δ > 0` and positive multiplicities, such that every integer relation `Σ k_j t_j = 0` has even
coefficient sum `Σ k_j`, the leading-order parity balance `λ_max(T(θ)) + λ_min(T(θ))` is positive on
the aperture line `θ_j = −2t_j a` for arbitrarily large `a`. The parity condition says exactly that
the half-turn `π𝟙` lies in the closure of the aperture line on the torus. -/
theorem ccm_exists_large_aperture_odd_wins_of_even_relations {δ : ℝ} (hδ : 0 < δ)
    {t M : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hM : ∀ j, 0 < M j)
    (hm : 0 < m) (heven : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → Even (∑ j, k j)) (N : ℝ) :
    ∃ a : ℝ, N ≤ a ∧ 0 < ccmParityBalance δ t M fun j => -2 * t j * a := by
  obtain ⟨a₀, ha₀, hno⟩ := ccm_exists_large_aperture_no_symmetric_matrix_pair hδ ht htpos
    (fun j => (hM j).ne') N
  set θ₀ : Fin m → ℝ := fun j => -2 * t j * a₀ with hθ₀
  have hno' : ∀ μ : ℂ, μ ≠ 0 → ∀ v w : Fin m ⊕ Fin m → ℂ, v ≠ 0 → w ≠ 0 →
      (diagonal (phaseWeight M θ₀) * cauchyGram (ccmNodes δ t)) *ᵥ v = μ • v →
      (diagonal (phaseWeight M θ₀) * cauchyGram (ccmNodes δ t)) *ᵥ w ≠ -μ • w := by
    have h := apertureWeight_ccm_eq_phaseWeight t M a₀
    simp only [parityMatrix, h] at hno
    exact hno
  have hF := ccmParityBalance_ne_zero hδ ht htpos hm (fun j => (hM j).ne') θ₀ hno'
  rcases hF.lt_or_gt with hneg | hpos
  swap
  · exact ⟨a₀, ha₀, hpos⟩
  -- the half-turn of `θ₀` has positive balance; the aperture line returns near it
  have hg0 : 0 < ccmParityBalance δ t M (halfTurn θ₀) := by
    rw [ccmParityBalance_halfTurn]; linarith
  obtain ⟨η, hη, hwin⟩ := exists_phase_window_ccmParityBalance_pos hδ ht htpos hm M _ hg0
  have hrel : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 →
      ∃ z : ℤ, ∑ j, (k j : ℝ) * (a₀ * (t j / Real.pi) - 1 / 2) = z := by
    intro k h1
    obtain ⟨n, hn⟩ := heven k h1
    refine ⟨-n, ?_⟩
    have hk : (∑ j, (k j : ℝ)) = n + n := by exact_mod_cast hn
    have : ∑ j, (k j : ℝ) * (a₀ * (t j / Real.pi) - 1 / 2) =
        a₀ / Real.pi * (∑ j, (k j : ℝ) * t j) - (∑ j, (k j : ℝ)) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, h1, hk]
    push_cast
    ring
  obtain ⟨a, haN, z, hz⟩ := exists_large_aperture_phase_near hrel hη N
  refine ⟨a, haN, hwin _ z fun j => ?_⟩
  have h := hz j
  rwa [show -2 * Real.pi * (a₀ * (t j / Real.pi) - 1 / 2) = halfTurn θ₀ j by
    simp only [halfTurn, hθ₀]; field_simp; ring] at h

/-- **The odd sector wins for ℚ-independent ordinates.** -/
theorem ccm_exists_large_aperture_odd_wins {δ : ℝ} (hδ : 0 < δ) {t M : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hM : ∀ j, 0 < M j) (hm : 0 < m)
    (hind : ∀ k : Fin m → ℤ, k ≠ 0 → ∑ j, (k j : ℝ) * t j ≠ 0) (N : ℝ) :
    ∃ a : ℝ, N ≤ a ∧ 0 < ccmParityBalance δ t M fun j => -2 * t j * a := by
  refine ccm_exists_large_aperture_odd_wins_of_even_relations hδ ht htpos hM hm
    (fun k hk => ?_) N
  by_cases h0 : k = 0
  · simp [h0]
  · exact absurd hk (hind k h0)

end

end RHTower.CCMParityCauchy
