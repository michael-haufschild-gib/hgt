import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite diagonal multipliers: precision spectrum and inverse capacity

A finite family of scalars `g : ι → ℂ` acts on `EuclideanSpace ℂ ι` by coordinatewise
multiplication.  The exact precision data of that finite section are

* `smallestSingularValue_diagOp` : the least singular value is `min_i ‖g i‖`;
* `inner_normalDiagOp_self` : the normal operator has quadratic form `∑ i ‖g i‖²‖x i‖²`, so its
  least value on the unit sphere is `(min_i ‖g i‖)²`, attained at a coordinate vector;
* `opNorm_diagOp_inv` : the inverse has norm `(min_i ‖g i‖)⁻¹`;
* `le_opNorm_of_approxLeftInverse` : every `ε`-accurate approximate inverse has norm at least
  `(1 − ε)/min_i ‖g i‖`.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinatewise multiplication by a finite family of scalars. -/
noncomputable def diagOp (g : ι → ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (WithLp.toLp 2 (fun i => g i * x i) : EuclideanSpace ℂ ι)
      map_add' := by
        intro x y
        ext i
        show g i * (x + y) i = g i * x i + g i * y i
        rw [show ((x + y : EuclideanSpace ℂ ι)) i = x i + y i from rfl, mul_add]
      map_smul' := by
        intro c x
        ext i
        show g i * (c • x) i = c * (g i * x i)
        rw [show ((c • x : EuclideanSpace ℂ ι)) i = c * x i from rfl]
        ring }

omit [DecidableEq ι] in
@[simp] theorem diagOp_apply (g : ι → ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    diagOp g x i = g i * x i := rfl

omit [DecidableEq ι] in
theorem norm_sq_diagOp (g : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    ‖diagOp g x‖ ^ 2 = ∑ i : ι, (‖g i‖ * ‖x i‖) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun i _ => by rw [diagOp_apply, norm_mul]

theorem diagOp_single (g : ι → ℂ) (i : ι) (c : ℂ) :
    diagOp g (EuclideanSpace.single i c) = EuclideanSpace.single i (g i * c) := by
  ext j
  rw [diagOp_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

section Nonempty

variable [Nonempty ι]

/-- The least modulus of a finite family. -/
noncomputable def diagMin (g : ι → ℂ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => ‖g i‖

/-- The greatest modulus of a finite family. -/
noncomputable def diagMax (g : ι → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ‖g i‖

omit [DecidableEq ι] in
theorem diagMin_le (g : ι → ℂ) (i : ι) : diagMin g ≤ ‖g i‖ :=
  Finset.inf'_le (fun j => ‖g j‖) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem le_diagMax (g : ι → ℂ) (i : ι) : ‖g i‖ ≤ diagMax g :=
  Finset.le_sup' (fun j => ‖g j‖) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem le_diagMin (g : ι → ℂ) {c : ℝ} (h : ∀ i, c ≤ ‖g i‖) : c ≤ diagMin g :=
  Finset.le_inf' Finset.univ_nonempty (fun i => ‖g i‖) fun i _ => h i

omit [DecidableEq ι] in
theorem exists_diagMin_eq (g : ι → ℂ) : ∃ i : ι, diagMin g = ‖g i‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun i => ‖g i‖
  exact ⟨i, hi⟩

omit [DecidableEq ι] in
theorem exists_diagMax_eq (g : ι → ℂ) : ∃ i : ι, diagMax g = ‖g i‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => ‖g i‖
  exact ⟨i, hi⟩

omit [DecidableEq ι] in
theorem diagMin_nonneg (g : ι → ℂ) : 0 ≤ diagMin g := by
  obtain ⟨i, hi⟩ := exists_diagMin_eq g
  rw [hi]
  exact norm_nonneg _

omit [DecidableEq ι] in
theorem diagMin_mul_norm_le (g : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    diagMin g * ‖x‖ ≤ ‖diagOp g x‖ := by
  have hsq : (diagMin g * ‖x‖) ^ 2 ≤ ‖diagOp g x‖ ^ 2 := by
    rw [norm_sq_diagOp, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hle : diagMin g ≤ ‖g i‖ := diagMin_le g i
    have h1 : (0 : ℝ) ≤ diagMin g := diagMin_nonneg g
    have hsq : diagMin g ^ 2 ≤ ‖g i‖ ^ 2 := by nlinarith
    calc diagMin g ^ 2 * ‖x i‖ ^ 2 ≤ ‖g i‖ ^ 2 * ‖x i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (‖g i‖ * ‖x i‖) ^ 2 := by ring
  have h1 : (0 : ℝ) ≤ diagMin g * ‖x‖ := mul_nonneg (diagMin_nonneg g) (norm_nonneg _)
  nlinarith [norm_nonneg (diagOp g x)]

omit [DecidableEq ι] in
theorem norm_diagOp_le (g : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    ‖diagOp g x‖ ≤ diagMax g * ‖x‖ := by
  have hmaxnn : (0 : ℝ) ≤ diagMax g := by
    obtain ⟨i, hi⟩ := exists_diagMax_eq g
    rw [hi]; exact norm_nonneg _
  have hsq : ‖diagOp g x‖ ^ 2 ≤ (diagMax g * ‖x‖) ^ 2 := by
    rw [norm_sq_diagOp, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hle : ‖g i‖ ≤ diagMax g := le_diagMax g i
    have hsq : ‖g i‖ ^ 2 ≤ diagMax g ^ 2 := by nlinarith [norm_nonneg (g i)]
    calc (‖g i‖ * ‖x i‖) ^ 2 = ‖g i‖ ^ 2 * ‖x i‖ ^ 2 := by ring
      _ ≤ diagMax g ^ 2 * ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have h1 : (0 : ℝ) ≤ diagMax g * ‖x‖ := mul_nonneg hmaxnn (norm_nonneg _)
  nlinarith [norm_nonneg (diagOp g x)]

omit [Nonempty ι] in
theorem norm_euclideanSpace_single (i : ι) (c : ℂ) :
    ‖(EuclideanSpace.single i c : EuclideanSpace ℂ ι)‖ = ‖c‖ := by
  simp

/-- The **least singular value** of a bounded operator on a normed space. -/
noncomputable def smallestSingularValue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) : ℝ :=
  sInf {r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = ‖T x‖}

/-- **The exact finite precision law.**  The least singular value of a finite diagonal multiplier
is the least modulus of its symbol. -/
theorem smallestSingularValue_diagOp (g : ι → ℂ) :
    smallestSingularValue (diagOp g) = diagMin g := by
  obtain ⟨i₀, hi₀⟩ := exists_diagMin_eq g
  refine IsLeast.csInf_eq ⟨⟨EuclideanSpace.single i₀ 1, ?_, ?_⟩, ?_⟩
  · rw [norm_euclideanSpace_single, norm_one]
  · rw [diagOp_single, norm_euclideanSpace_single, mul_one, hi₀]
  · rintro r ⟨x, hx, rfl⟩
    have := diagMin_mul_norm_le g x
    rwa [hx, mul_one] at this

omit [DecidableEq ι] [Nonempty ι] in
/-- The normal operator of a finite diagonal multiplier. -/
theorem inner_normalDiagOp_self (g : ι → ℂ) (x : EuclideanSpace ℂ ι) :
    RCLike.re (⟪(ContinuousLinearMap.adjoint (diagOp g)) (diagOp g x), x⟫_ℂ)
      = ∑ i : ι, (‖g i‖ * ‖x i‖) ^ 2 := by
  rw [ContinuousLinearMap.adjoint_inner_left (diagOp g) x (diagOp g x), inner_self_eq_norm_sq,
    norm_sq_diagOp]

omit [Nonempty ι] in
/-- The normal operator is diagonalized by the coordinate vectors, with eigenvalue `‖g i‖²`. -/
theorem normalDiagOp_single (g : ι → ℂ) (i : ι) (c : ℂ) :
    (ContinuousLinearMap.adjoint (diagOp g)) (diagOp g (EuclideanSpace.single i c))
      = ((‖g i‖ ^ 2 : ℝ) : ℂ) • EuclideanSpace.single i c := by
  have hadj : ContinuousLinearMap.adjoint (diagOp g) = diagOp (fun i => (starRingEnd ℂ) (g i)) := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro y x
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [diagOp_apply, RCLike.inner_apply, map_mul, Complex.conj_conj]
    ring
  rw [hadj, diagOp_single, diagOp_single]
  have hconj : (starRingEnd ℂ) (g i) * g i = ((‖g i‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]
    norm_cast
  ext j
  by_cases hj : j = i
  · subst hj
    have hlhs : (EuclideanSpace.single j ((starRingEnd ℂ) (g j) * (g j * c))
        : EuclideanSpace ℂ ι) j = (starRingEnd ℂ) (g j) * (g j * c) := by simp
    have hrhs : (((‖g j‖ ^ 2 : ℝ) : ℂ) • (EuclideanSpace.single j c : EuclideanSpace ℂ ι)) j
        = ((‖g j‖ ^ 2 : ℝ) : ℂ) * c := by simp
    rw [hlhs, hrhs, ← mul_assoc, hconj]
  · simp [hj]

omit [DecidableEq ι] in
/-- The least eigenvalue of the normal operator is the square of the least singular value. -/
theorem inner_normalDiagOp_self_ge (g : ι → ℂ) (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    diagMin g ^ 2 ≤ RCLike.re (⟪(ContinuousLinearMap.adjoint (diagOp g)) (diagOp g x), x⟫_ℂ) := by
  rw [ContinuousLinearMap.adjoint_inner_left (diagOp g) x (diagOp g x), inner_self_eq_norm_sq]
  have hle := diagMin_mul_norm_le g x
  rw [hx, mul_one] at hle
  nlinarith [diagMin_nonneg g, norm_nonneg (diagOp g x)]

section Invertible

variable {g : ι → ℂ} (hg : ∀ i, g i ≠ 0)

include hg

omit [DecidableEq ι] in
theorem diagMin_pos : 0 < diagMin g := by
  obtain ⟨i, hi⟩ := exists_diagMin_eq g
  rw [hi]
  exact norm_pos_iff.mpr (hg i)

omit [DecidableEq ι] [Nonempty ι] in
theorem diagOp_inv_comp : diagOp (fun i => (g i)⁻¹) ∘L diagOp g = ContinuousLinearMap.id ℂ _ := by
  ext x i
  show (g i)⁻¹ * (g i * x i) = x i
  rw [← mul_assoc, inv_mul_cancel₀ (hg i), one_mul]

omit [DecidableEq ι] [Nonempty ι] in
theorem diagOp_comp_inv : diagOp g ∘L diagOp (fun i => (g i)⁻¹) = ContinuousLinearMap.id ℂ _ := by
  ext x i
  show g i * ((g i)⁻¹ * x i) = x i
  rw [← mul_assoc, mul_inv_cancel₀ (hg i), one_mul]

omit [DecidableEq ι] in
theorem diagMax_inv : diagMax (fun i => (g i)⁻¹) = (diagMin g)⁻¹ := by
  have hpos : 0 < diagMin g := diagMin_pos hg
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := exists_diagMax_eq (fun i => (g i)⁻¹)
    rw [hi, norm_inv, ← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos (diagMin_le g i)
  · obtain ⟨i, hi⟩ := exists_diagMin_eq g
    have hle : ‖(g i)⁻¹‖ ≤ diagMax (fun j => (g j)⁻¹) := le_diagMax (fun j => (g j)⁻¹) i
    rw [norm_inv] at hle
    rw [hi]
    exact hle

/-- **The inverse capacity law.**  The inverse of a finite diagonal multiplier has norm the
reciprocal of the least modulus of its symbol. -/
theorem opNorm_diagOp_inv : ‖diagOp (fun i => (g i)⁻¹)‖ = (diagMin g)⁻¹ := by
  have hpos : 0 < diagMin g := diagMin_pos hg
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have h := norm_diagOp_le (fun i => (g i)⁻¹) x
    rwa [diagMax_inv hg] at h
  · obtain ⟨i, hi⟩ := exists_diagMin_eq g
    have hle := (diagOp (fun j => (g j)⁻¹)).le_opNorm (EuclideanSpace.single i 1)
    rw [diagOp_single, norm_euclideanSpace_single, norm_euclideanSpace_single, norm_one,
      mul_one, mul_one, norm_inv] at hle
    rw [hi]
    exact hle

/-- **The approximate inverse uncertainty law.**  Every `ε`-accurate approximate left inverse of a
finite diagonal multiplier has norm at least `(1 − ε)` times the inverse capacity. -/
theorem le_opNorm_of_approxLeftInverse
    (G : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) {ε : ℝ}
    (hGB : ‖G ∘L diagOp g - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι)‖ ≤ ε) :
    (1 - ε) * (diagMin g)⁻¹ ≤ ‖G‖ := by
  have hpos : 0 < diagMin g := diagMin_pos hg
  obtain ⟨i, hi⟩ := exists_diagMin_eq g
  set e : EuclideanSpace ℂ ι := EuclideanSpace.single i 1 with he
  have hen : ‖e‖ = 1 := by rw [he, norm_euclideanSpace_single, norm_one]
  have hdiff : ‖G (diagOp g e) - e‖ ≤ ε := by
    have h := (G ∘L diagOp g - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι)).le_opNorm e
    rw [hen, mul_one] at h
    refine le_trans ?_ (le_trans h hGB)
    exact le_of_eq rfl
  have hge : 1 - ε ≤ ‖G (diagOp g e)‖ := by
    have htri : ‖e‖ ≤ ‖G (diagOp g e)‖ + ‖G (diagOp g e) - e‖ := by
      have := norm_sub_norm_le e (G (diagOp g e))
      have h2 : ‖e - G (diagOp g e)‖ = ‖G (diagOp g e) - e‖ := norm_sub_rev _ _
      linarith [norm_sub_le e (G (diagOp g e)), (norm_sub_rev (G (diagOp g e)) e) ▸ this]
    rw [hen] at htri
    linarith
  have hnorm : ‖diagOp g e‖ = diagMin g := by
    rw [he, diagOp_single, norm_euclideanSpace_single, mul_one, hi]
  have hle : ‖G (diagOp g e)‖ ≤ ‖G‖ * diagMin g := by
    have := G.le_opNorm (diagOp g e)
    rwa [hnorm] at this
  rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hpos]
  linarith

end Invertible

end Nonempty

end GaloisForLFunctions.HTGeometry
