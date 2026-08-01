import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The inner product induced by a positive symmetric operator

A positive symmetric operator `T` on a real inner product space induces the bilinear form
`⟪u, v⟫_T = ⟪T u, v⟫`.  It is symmetric, bilinear and positive semidefinite, so it satisfies the
Cauchy–Schwarz inequality — proved here from the discriminant of the nonnegative quadratic
`t ↦ ⟪u + t v, u + t v⟫_T`, which needs no completeness or definiteness.

The identity that makes such a form useful against a resolvent is that solving `T v = e` collapses
the `T`-pairing of `v` to the plain pairing of `e`: the operator disappears from the left slot.  In
particular the `T`-pairings of solutions of `T v_z = e_z` are computed by the plain pairings of the
right-hand sides, with no reference to `T` at all.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bilinear form induced by an operator: `⟪u, v⟫_T = ⟪T u, v⟫`. -/
def tInner (T : E →ₗ[ℝ] E) (u v : E) : ℝ := inner ℝ (T u) v

theorem tInner_def (T : E →ₗ[ℝ] E) (u v : E) : tInner T u v = inner ℝ (T u) v := rfl

/-- **The boundary-form identity.**  Solving `T v = e` removes the operator from the pairing: the
`T`-inner product of `v` against anything is the plain inner product of `e` against it. -/
theorem tInner_eq_inner_of_apply {T : E →ₗ[ℝ] E} {v e : E} (h : T v = e) (w : E) :
    tInner T v w = inner ℝ e w := by
  rw [tInner_def, h]

/-- A symmetric operator induces a symmetric form. -/
theorem tInner_comm {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u v : E) :
    tInner T u v = tInner T v u := by
  rw [tInner_def, tInner_def, hT u v, real_inner_comm]

theorem tInner_add_left (T : E →ₗ[ℝ] E) (u v w : E) :
    tInner T (u + v) w = tInner T u w + tInner T v w := by
  rw [tInner_def, tInner_def, tInner_def, map_add, inner_add_left]

theorem tInner_smul_left (T : E →ₗ[ℝ] E) (c : ℝ) (u v : E) :
    tInner T (c • u) v = c * tInner T u v := by
  rw [tInner_def, tInner_def, map_smul, real_inner_smul_left]

theorem tInner_add_right {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u v w : E) :
    tInner T u (v + w) = tInner T u v + tInner T u w := by
  rw [tInner_comm hT u (v + w), tInner_add_left, tInner_comm hT v u, tInner_comm hT w u]

theorem tInner_smul_right {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (c : ℝ) (u v : E) :
    tInner T u (c • v) = c * tInner T u v := by
  rw [tInner_comm hT u (c • v), tInner_smul_left, tInner_comm hT v u]

/-- The quadratic expansion along a line, the input of the Cauchy–Schwarz argument. -/
theorem tInner_self_add_smul {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u v : E) (t : ℝ) :
    tInner T (u + t • v) (u + t • v)
      = tInner T v v * (t * t) + 2 * tInner T u v * t + tInner T u u := by
  simp only [tInner_add_left, tInner_add_right hT, tInner_smul_left, tInner_smul_right hT,
    tInner_comm hT v u]
  ring

/-- **Cauchy–Schwarz for the induced form.**  Positivity of the quadratic along every line forces its
discriminant to be nonpositive.  No definiteness or completeness is used. -/
theorem tInner_sq_le_of_nonneg {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ w : E, 0 ≤ tInner T w w) (u v : E) :
    (tInner T u v) ^ 2 ≤ tInner T u u * tInner T v v := by
  have hquad : ∀ t : ℝ,
      0 ≤ tInner T v v * (t * t) + 2 * tInner T u v * t + tInner T u u := by
    intro t
    rw [← tInner_self_add_smul hT u v t]
    exact hpos _
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- The induced form vanishes on the kernel of the operator. -/
theorem tInner_eq_zero_of_apply_eq_zero {T : E →ₗ[ℝ] E} {v : E} (h : T v = 0) (w : E) :
    tInner T v w = 0 := by
  rw [tInner_eq_inner_of_apply h, inner_zero_left]

/-! ## Normalized masses

A spectral mass is the squared pairing of two *normalized* vectors.  Expanding the normalizations
gives the squared pairing over the two squared norms, with no nonvanishing hypothesis: in the
degenerate case both sides are zero, because the inverse of the zero norm is zero and the quotient
has zero numerator. -/

/-- The induced form is bilinear in scalars. -/
theorem tInner_smul_smul {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (c d : ℝ) (u v : E) :
    tInner T (c • u) (d • v) = c * d * tInner T u v := by
  rw [tInner_smul_left, tInner_smul_right hT]
  ring

/-- **The normalized mass.**  The squared pairing of the normalizations of `v` and `w` is the squared
pairing divided by the two squared norms — and this holds unconditionally. -/
theorem inner_normalize_sq (v w : E) :
    (inner ℝ (‖v‖⁻¹ • v) (‖w‖⁻¹ • w)) ^ 2
      = (inner ℝ v w) ^ 2 / (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  rw [real_inner_smul_left, real_inner_smul_right]
  rcases eq_or_ne ‖v‖ 0 with hv | hv
  · rw [hv]
    simp
  · rcases eq_or_ne ‖w‖ 0 with hw | hw
    · rw [hw]
      simp
    · field_simp

/-- The same for the induced form: the mass of the `T`-normalizations. -/
theorem tInner_normalize_sq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (nv nw : ℝ) (v w : E) :
    (tInner T (nv • v) (nw • w)) ^ 2 = nv ^ 2 * nw ^ 2 * (tInner T v w) ^ 2 := by
  rw [tInner_smul_smul hT]
  ring

/-! ## Even–odd defect energies

Splitting a pair of defect vectors into even and odd parts turns their pairing into the *difference*
of the two energies and, when the pair has equal norms, their sum into the common energy.  So the
normalized pairing is exactly the even–odd energy imbalance, and it is a strict contraction as soon
as the odd part is nonzero. -/

/-- The even and odd parts of a defect pair. -/
noncomputable def evenPart (vp vm : E) : E := (2 : ℝ)⁻¹ • (vp + vm)

noncomputable def oddPart (vp vm : E) : E := (2 : ℝ)⁻¹ • (vp - vm)

/-- **The pairing is the energy difference.** -/
theorem inner_eq_evenPart_sq_sub_oddPart_sq (vp vm : E) :
    (inner ℝ vm vp : ℝ) = ‖evenPart vp vm‖ ^ 2 - ‖oddPart vp vm‖ ^ 2 := by
  rw [evenPart, oddPart, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs]
  rw [mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real, real_inner_comm]
  norm_num
  ring

/-- **Equal norms make the sum the common energy.**  This is where parity of the defect pair
enters. -/
theorem norm_sq_eq_evenPart_sq_add_oddPart_sq {vp vm : E} (hnorm : ‖vm‖ = ‖vp‖) :
    ‖vp‖ ^ 2 = ‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2 := by
  rw [evenPart, oddPart, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs]
  rw [mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real, hnorm]
  norm_num
  ring

/-- **`(8)`, the normalized even–odd imbalance.**  The anchored jet is the imbalance of the two
defect energies. -/
theorem inner_div_norm_sq_eq_imbalance {vp vm : E} (hnorm : ‖vm‖ = ‖vp‖) :
    (inner ℝ vm vp : ℝ) / ‖vp‖ ^ 2
      = (‖evenPart vp vm‖ ^ 2 - ‖oddPart vp vm‖ ^ 2)
        / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) := by
  rw [inner_eq_evenPart_sq_sub_oddPart_sq, norm_sq_eq_evenPart_sq_add_oddPart_sq hnorm]

/-- **It is a strict contraction exactly when both parts survive.**  A nonzero odd part alone is not
enough: if the even part vanishes the imbalance is `-1`.  Both energies must be positive. -/
theorem abs_imbalance_lt_one {vp vm : E} (heven : evenPart vp vm ≠ 0) (hodd : oddPart vp vm ≠ 0) :
    |(‖evenPart vp vm‖ ^ 2 - ‖oddPart vp vm‖ ^ 2)
      / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2)| < 1 := by
  have hop : 0 < ‖oddPart vp vm‖ ^ 2 := by positivity
  have hep : 0 < ‖evenPart vp vm‖ ^ 2 := by positivity
  have hsum : 0 < ‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2 := by linarith
  rw [abs_div, abs_of_pos hsum, div_lt_one hsum, abs_lt]
  constructor <;> linarith

/-- **The boundary cases.**  A vanishing odd part gives imbalance `1`, a vanishing even part gives
`-1`; so the strict bound is exactly the statement that both defect components survive. -/
theorem imbalance_eq_one_of_oddPart_eq_zero {vp vm : E} (heven : evenPart vp vm ≠ 0)
    (hodd : oddPart vp vm = 0) :
    (‖evenPart vp vm‖ ^ 2 - ‖oddPart vp vm‖ ^ 2)
      / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) = 1 := by
  have hep : 0 < ‖evenPart vp vm‖ ^ 2 := by positivity
  rw [hodd, norm_zero]
  norm_num
  exact heven

theorem imbalance_eq_neg_one_of_evenPart_eq_zero {vp vm : E} (heven : evenPart vp vm = 0)
    (hodd : oddPart vp vm ≠ 0) :
    (‖evenPart vp vm‖ ^ 2 - ‖oddPart vp vm‖ ^ 2)
      / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) = -1 := by
  have hop : 0 < ‖oddPart vp vm‖ ^ 2 := by positivity
  rw [heven, norm_zero]
  norm_num
  rw [neg_div, div_self (ne_of_gt hop)]

/-! ## The parity weights

Shifting and halving the imbalance turns it into the pair of parity weights, and they sum to one.
So the imbalance is not an arbitrary derivative but the signed polarization of a two-state
probability: each weight is one component's share of the total defect energy. -/

/-- **`(12)`, the parity weights.**  The shifted imbalance is each part's share of the total, and the
two shares sum to one. -/
theorem parity_weights (e o : ℝ) (h : 0 < e + o) :
    (1 + (e - o) / (e + o)) / 2 = e / (e + o) ∧
      (1 - (e - o) / (e + o)) / 2 = o / (e + o) ∧
      e / (e + o) + o / (e + o) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp

/-- The parity weights of a defect pair: each component's share of the total defect energy. -/
theorem parity_weights_of_defect {vp vm : E}
    (h : 0 < ‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) :
    (1 + (‖evenPart vp vm‖ ^ 2 - ‖oddPart vp vm‖ ^ 2)
        / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2)) / 2
      = ‖evenPart vp vm‖ ^ 2 / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) :=
  (parity_weights _ _ h).1

/-- Both weights are nonnegative, so the polarization really is a two-state probability. -/
theorem parity_weight_nonneg {vp vm : E}
    (h : 0 < ‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) :
    0 ≤ ‖evenPart vp vm‖ ^ 2 / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) ∧
      0 ≤ ‖oddPart vp vm‖ ^ 2 / (‖evenPart vp vm‖ ^ 2 + ‖oddPart vp vm‖ ^ 2) :=
  ⟨div_nonneg (sq_nonneg _) h.le, div_nonneg (sq_nonneg _) h.le⟩

/-! ## The two-defect Gram state

The normalized Gram of a defect pair is a two-by-two state whose off-diagonal is the pairing.  Its
parity vectors diagonalize it, with the parity weights as eigenvalues — so the polarization reading
is not an analogy but the spectral decomposition of an explicit matrix. -/

open Matrix in
/-- The normalized two-defect Gram state. -/
noncomputable def defectGramState (N C : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2 * N)⁻¹ • !![N, C; C, N]

open Matrix in
/-- **The even parity vector is an eigenvector**, with the even parity weight. -/
theorem defectGramState_mulVec_even {N : ℝ} (C : ℝ) (hN : N ≠ 0) :
    (defectGramState N C) *ᵥ ![1, 1] = ((1 + C / N) / 2) • ![1, 1] := by
  funext i
  fin_cases i <;>
    (simp [defectGramState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
     field_simp
     try ring)

open Matrix in
/-- **The odd parity vector is an eigenvector**, with the odd parity weight. -/
theorem defectGramState_mulVec_odd {N : ℝ} (C : ℝ) (hN : N ≠ 0) :
    (defectGramState N C) *ᵥ ![1, -1] = ((1 - C / N) / 2) • ![1, -1] := by
  funext i
  fin_cases i <;>
    (simp [defectGramState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
     field_simp
     try ring)

open Matrix in
/-- The state is symmetric, so its parity decomposition is orthogonal. -/
theorem defectGramState_isHermitian (N C : ℝ) : (defectGramState N C).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [defectGramState, Matrix.conjTranspose_apply]

/-! ## Shifting the floor

Adding a multiple of the identity raises the induced form by exactly that multiple of the squared
norm.  So a shift chosen relative to the source's own bottom places the new bottom at the shift
value, with no reference to an absolute scale. -/

/-- The induced form of a shifted operator. -/
theorem tInner_add_smul_id (T : E →ₗ[ℝ] E) (c : ℝ) (v : E) :
    tInner (T + c • LinearMap.id) v v = tInner T v v + c * ‖v‖ ^ 2 := by
  rw [tInner_def, tInner_def, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **`(13)`, the shifted floor.**  A lower bound for the form shifts by exactly the added
multiple. -/
theorem tInner_shift_lower_bound {T : E →ₗ[ℝ] E} {floor : ℝ}
    (h : ∀ v : E, floor * ‖v‖ ^ 2 ≤ tInner T v v) (c : ℝ) (v : E) :
    (floor + c) * ‖v‖ ^ 2 ≤ tInner (T + c • LinearMap.id) v v := by
  rw [tInner_add_smul_id]
  have := h v
  nlinarith [this]

/-- **A source-relative shift puts the bottom at the shift.**  If the form is nonnegative — the
source normalized to its own bottom — then shifting by `c` makes `c` a lower bound. -/
theorem tInner_shift_floor_eq_shift {T : E →ₗ[ℝ] E}
    (h : ∀ v : E, 0 ≤ tInner T v v) (c : ℝ) (v : E) :
    c * ‖v‖ ^ 2 ≤ tInner (T + c • LinearMap.id) v v := by
  have := tInner_shift_lower_bound (floor := 0) (fun w => by simpa using h w) c v
  simpa using this

end GaloisForLFunctions.HTGeometry
