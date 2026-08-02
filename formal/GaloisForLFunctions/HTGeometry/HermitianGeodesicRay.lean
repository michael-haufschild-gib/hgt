import GaloisForLFunctions.HTGeometry.HermitianApartment
import GaloisForLFunctions.HTGeometry.CfcEigenvector
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The ray of observer metrics and its degeneration flag

A Hermitian direction `T` generates the ray of observer metrics `t ↦ exp (t T)`.  Along that ray
the norm of a vector grows exponentially, at a rate read off from the eigenvalues, and the
degeneration flag of `T` is exactly the record of those rates:

* on the flag member at threshold `c` the ray expands at least at rate `c`;
* orthogonally to it the ray expands at most at rate `c`.

So the subspaces of the flag are the asymptotic degeneration pattern of the metric ray, which is
what makes the flag the endpoint of the ray at infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open Module NormedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E}

/-! ## The exponential of a direction on an eigenvector -/

/-- The ray of observer metrics in the direction `T`, at parameter `t`: the exponential `exp (t T)`.
-/
noncomputable def metricRay (T : E →ₗ[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  NormedSpace.exp ((t : ℂ) • T.toContinuousLinearMap)

/-- **The ray dilates an eigenvector by the exponential of its eigenvalue.** -/
theorem metricRay_apply_of_eigenvector {μ : ℝ} {v : E} (hv : T v = (μ : ℂ) • v) (t : ℝ) :
    metricRay T t v = ((Real.exp (t * μ) : ℝ) : ℂ) • v := by
  have hA : ((t : ℂ) • T.toContinuousLinearMap) v = (((t * μ : ℝ)) : ℂ) • v := by
    show (t : ℂ) • (T v) = _
    rw [hv, smul_smul]
    push_cast
    ring_nf
  have hsum : HasSum
      (fun k : ℕ => ((Nat.factorial k : ℂ)⁻¹ • ((t : ℂ) • T.toContinuousLinearMap) ^ k))
      (metricRay T t) := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) _
  have happ : HasSum
      (fun k : ℕ => (((Nat.factorial k : ℂ)⁻¹ * (((t * μ : ℝ)) : ℂ) ^ k) • v))
      (metricRay T t v) := by
    have := hsum.map (ContinuousLinearMap.apply ℂ E v) (ContinuousLinearMap.apply ℂ E v).continuous
    refine this.congr_fun fun k => ?_
    show (((Nat.factorial k : ℂ)⁻¹ * (((t * μ : ℝ)) : ℂ) ^ k) • v)
        = ((Nat.factorial k : ℂ)⁻¹ • ((t : ℂ) • T.toContinuousLinearMap) ^ k) v
    rw [smul_apply, pow_apply_of_eigenvector' hA k, smul_smul]
    push_cast
    ring_nf
  have hscal : HasSum (fun k : ℕ => ((Nat.factorial k : ℂ)⁻¹ * (((t * μ : ℝ)) : ℂ) ^ k))
      (Complex.exp (((t * μ : ℝ)) : ℂ)) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (((t * μ : ℝ)) : ℂ)
    rw [Complex.exp_eq_exp_ℂ]
    exact h.congr_fun fun k => by rw [smul_eq_mul]
  have := hscal.smul_const (M := E) v
  have heq := happ.unique this
  rw [heq]
  congr 1
  rw [← Complex.ofReal_exp]

/-! ## Growth of the ray along the flag -/

theorem metricRay_eigenvectorBasis (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (i : Fin n)
    (t : ℝ) :
    metricRay T t (hT.eigenvectorBasis hn i)
      = ((Real.exp (t * hT.eigenvalues hn i) : ℝ) : ℂ) • hT.eigenvectorBasis hn i :=
  metricRay_apply_of_eigenvector (hT.apply_eigenvectorBasis hn i) t

/-- The coordinates of the ray's image in the eigenbasis are the coordinates of the vector, scaled
by the exponentials of the eigenvalues. -/
theorem repr_metricRay (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (v : E) (t : ℝ) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr (metricRay T t v) i
      = ((Real.exp (t * hT.eigenvalues hn i) : ℝ) : ℂ) * (hT.eigenvectorBasis hn).repr v i := by
  classical
  set b := hT.eigenvectorBasis hn with hb
  have hexp : metricRay T t v = ∑ j, (b.repr v j * ((Real.exp (t * hT.eigenvalues hn j) : ℝ) : ℂ))
      • b j := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, metricRay_eigenvectorBasis hT hn j t, smul_smul]
  have hortho : ∀ j k : Fin n, inner ℂ (b j) (b k) = if j = k then (1 : ℂ) else 0 :=
    fun j k => orthonormal_iff_ite.1 b.orthonormal j k
  rw [hexp, b.repr_apply_apply, inner_sum]
  rw [Finset.sum_eq_single i]
  · rw [inner_smul_right, b.repr_apply_apply, hortho i i, if_pos rfl, mul_one, mul_comm]
  · intro j _ hj
    rw [inner_smul_right, hortho i j, if_neg (Ne.symm hj), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

theorem norm_sq_repr (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (v : E) :
    ‖v‖ = Real.sqrt (∑ i, ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2) := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map v, EuclideanSpace.norm_eq]

/-- **On the flag member at threshold `c` the ray expands at least at rate `c`.** -/
theorem norm_metricRay_ge (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ eigenSum T c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (c * t) * ‖v‖ ≤ ‖metricRay T t v‖ := by
  classical
  set b := hT.eigenvectorBasis hn with hb
  have hzero : ∀ i : Fin n, hT.eigenvalues hn i ≤ c → b.repr v i = 0 := by
    intro i hi
    rw [hb, (hT.eigenvectorBasis hn).repr_apply_apply]
    have hmem : v ∈ Submodule.span ℂ (b '' {j | c < hT.eigenvalues hn j}) := by
      rwa [← eigenSum_eq_span hT hn c]
    refine Submodule.span_induction (p := fun x _ => inner ℂ (b i) x = (0 : ℂ)) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨j, hj, rfl⟩
      have hortho : inner ℂ (b i) (b j) = if i = j then (1 : ℂ) else 0 :=
        orthonormal_iff_ite.1 b.orthonormal i j
      rw [hortho, if_neg]
      rintro rfl
      exact absurd hj (not_lt.2 hi)
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_right, hx, hy, add_zero]
    · intro a x _ hx
      rw [inner_smul_right, hx, mul_zero]
  have hbound : ∀ i : Fin n,
      (Real.exp (c * t)) ^ 2 * ‖b.repr v i‖ ^ 2 ≤ ‖b.repr (metricRay T t v) i‖ ^ 2 := by
    intro i
    rw [repr_metricRay hT hn v t i, norm_mul]
    by_cases hi : hT.eigenvalues hn i ≤ c
    · rw [hzero i hi]
      simp
    · have hlt : c < hT.eigenvalues hn i := not_le.1 hi
      have hle : Real.exp (c * t) ≤ Real.exp (t * hT.eigenvalues hn i) := by
        refine Real.exp_le_exp.2 ?_
        rw [mul_comm c t]
        exact mul_le_mul_of_nonneg_left (le_of_lt hlt) ht
      have hnorm : ‖((Real.exp (t * hT.eigenvalues hn i) : ℝ) : ℂ)‖
          = Real.exp (t * hT.eigenvalues hn i) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [hnorm, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hle 2)
        (sq_nonneg _)
  rw [norm_sq_repr hT hn v, norm_sq_repr hT hn (metricRay T t v),
    ← Real.sqrt_sq (le_of_lt (Real.exp_pos (c * t))), ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hbound i

/-- **Orthogonally to the flag member at threshold `c` the ray expands at most at rate `c`.** -/
theorem norm_metricRay_le (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ (eigenSum T c)ᗮ) {t : ℝ} (ht : 0 ≤ t) :
    ‖metricRay T t v‖ ≤ Real.exp (c * t) * ‖v‖ := by
  classical
  set b := hT.eigenvectorBasis hn with hb
  have hzero : ∀ i : Fin n, c < hT.eigenvalues hn i → b.repr v i = 0 := by
    intro i hi
    rw [hb, (hT.eigenvectorBasis hn).repr_apply_apply]
    have hmem : b i ∈ eigenSum T c :=
      eigenspace_le_eigenSum hi (hT.hasEigenvector_eigenvectorBasis hn i).1
    exact inner_eq_zero_comm ((Submodule.mem_orthogonal' _ _).1 hv (b i) hmem)
  have hbound : ∀ i : Fin n,
      ‖b.repr (metricRay T t v) i‖ ^ 2 ≤ (Real.exp (c * t)) ^ 2 * ‖b.repr v i‖ ^ 2 := by
    intro i
    rw [repr_metricRay hT hn v t i, norm_mul]
    by_cases hi : c < hT.eigenvalues hn i
    · rw [hzero i hi]
      simp
    · have hle : Real.exp (t * hT.eigenvalues hn i) ≤ Real.exp (c * t) := by
        refine Real.exp_le_exp.2 ?_
        rw [mul_comm c t]
        exact mul_le_mul_of_nonneg_left (not_lt.1 hi) ht
      have hnorm : ‖((Real.exp (t * hT.eigenvalues hn i) : ℝ) : ℂ)‖
          = Real.exp (t * hT.eigenvalues hn i) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [hnorm, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hle 2)
        (sq_nonneg _)
  rw [norm_sq_repr hT hn v, norm_sq_repr hT hn (metricRay T t v),
    ← Real.sqrt_sq (le_of_lt (Real.exp_pos (c * t))), ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hbound i

end GaloisForLFunctions.HTGeometry
