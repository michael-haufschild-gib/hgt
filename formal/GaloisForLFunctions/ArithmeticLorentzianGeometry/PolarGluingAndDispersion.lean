import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianFormsAtDegreeTwo
import GaloisForLFunctions.HTGeometry.QuotientFusionProjectionGenesis

/-!
# Polar gluing and dispersion

Local Hodge inequalities require a compatibility estimate before they can be added. With a
common positive anchor `e`, the reserve of a sum is the sum of the local reserves minus the
weighted variance of the normalized polar rows. This identifies the exact cost of gluing.

Subtracting the dispersion matrix preserves the anchor row and adds the reserves without loss.
It therefore constructs a hyperbolic form from any anchored family of hyperbolic forms. This is
a construction of a new form, not a signature theorem for an independently specified form.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

theorem bil_sum_family (Q : κ → Matrix ι ι ℝ) (x y : ι → ℝ) :
    bil (∑ i, Q i) x y = ∑ i, bil (Q i) x y := by
  simp only [bil, sum_mulVec, dotProduct_sum]

theorem qf_sum_matrix (Q : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    qf (∑ i, Q i) x = ∑ i, qf (Q i) x := bil_sum_family Q x x

omit [Fintype ι] in
theorem isSymm_sum_matrix (Q : κ → Matrix ι ι ℝ) (hQ : ∀ i, (Q i).IsSymm) :
    (∑ i, Q i).IsSymm := by
  change (∑ i, Q i)ᵀ = ∑ i, Q i
  rw [Matrix.transpose_sum]
  exact sum_congr rfl fun i _ => (hQ i).eq

theorem bil_sub_matrix (Q R : Matrix ι ι ℝ) (x y : ι → ℝ) :
    bil (Q - R) x y = bil Q x y - bil R x y := by
  simp only [bil, sub_mulVec, dotProduct_sub]

theorem qf_sub_matrix (Q R : Matrix ι ι ℝ) (x : ι → ℝ) :
    qf (Q - R) x = qf Q x - qf R x := bil_sub_matrix Q R x x

theorem qf_matrix_pullback (Q : Matrix ι ι ℝ) (A : Matrix ι τ ℝ) (x : τ → ℝ) :
    qf (Aᵀ * Q * A) x = qf Q (A *ᵥ x) := bil_pullback Q A x x

/-- The rank-one form agreeing with `Q` along its positive anchor. -/
def anchorSquare (Q : Matrix ι ι ℝ) (e : ι → ℝ) : Matrix ι ι ℝ :=
  (qf Q e)⁻¹ • vecMulVec (Qᵀ *ᵥ e) (Qᵀ *ᵥ e)

theorem anchorSquare_isSymm (Q : Matrix ι ι ℝ) (e : ι → ℝ) :
    (anchorSquare Q e).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [anchorSquare, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  ring

theorem bil_anchorSquare (Q : Matrix ι ι ℝ) (e x y : ι → ℝ) :
    bil (anchorSquare Q e) x y = bil Q e x * bil Q e y / qf Q e := by
  have hrow (z : ι → ℝ) : (Qᵀ *ᵥ e) ⬝ᵥ z = bil Q e z := by
    rw [mulVec_transpose, ← dotProduct_mulVec]
    rfl
  simp only [anchorSquare, bil, smul_mulVec, dotProduct_smul, vecMulVec_mulVec,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [dotProduct_comm x, hrow x, hrow y]
  simp only [bil]
  ring

theorem qf_anchorSquare (Q : Matrix ι ι ℝ) (e x : ι → ℝ) :
    qf (anchorSquare Q e) x = bil Q e x ^ 2 / qf Q e := by
  rw [qf, bil_anchorSquare, pow_two]

theorem bil_anchorSquare_anchor {Q : Matrix ι ι ℝ} {e : ι → ℝ}
    (he : qf Q e ≠ 0) (x : ι → ℝ) :
    bil (anchorSquare Q e) e x = bil Q e x := by
  rw [bil_anchorSquare]
  change qf Q e * bil Q e x / qf Q e = _
  exact mul_div_cancel_left₀ _ he

/-- The negative energy left after removing the anchor direction. -/
def anchorReserve (Q : Matrix ι ι ℝ) (e x : ι → ℝ) : ℝ :=
  bil Q e x ^ 2 / qf Q e - qf Q x

/-- A positive anchor turns hyperbolicity into nonnegativity of its Schur reserve. -/
theorem isHyperbolic_iff_anchorReserve_nonneg {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    {e : ι → ℝ} (he : 0 < qf Q e) :
    IsHyperbolic Q ↔ ∀ x, 0 ≤ anchorReserve Q e x := by
  constructor
  · intro h x
    rw [anchorReserve, sub_nonneg, le_div_iff₀ he]
    simpa only [mul_comm] using h e x he
  · intro h
    apply isHyperbolic_of_nonpos_on_ker hQ (bilLeft Q e)
    intro x hx
    have hx' : bil Q e x = 0 := hx
    have hr := h x
    simp only [anchorReserve, hx', zero_pow (by decide : 2 ≠ 0), zero_div, zero_sub] at hr
    linarith

/-- Dispersion of local polar rows about the polar row of their sum. -/
def polarDispersion (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ) : ℝ :=
  ∑ i, qf (Q i) e *
    (bil (Q i) e x / qf (Q i) e - bil (∑ j, Q j) e x / qf (∑ j, Q j) e) ^ 2

/-- The matrix charged by gluing local polar directions. -/
def polarGluingCorrection (Q : κ → Matrix ι ι ℝ) (e : ι → ℝ) : Matrix ι ι ℝ :=
  (∑ i, anchorSquare (Q i) e) - anchorSquare (∑ i, Q i) e

theorem polarGluingCorrection_isSymm (Q : κ → Matrix ι ι ℝ) (e : ι → ℝ) :
    (polarGluingCorrection Q e).IsSymm :=
  (isSymm_sum_matrix _ fun i => anchorSquare_isSymm (Q i) e).sub
    (anchorSquare_isSymm _ _)

theorem polarDispersion_nonneg (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 ≤ qf (Q i) e) : 0 ≤ polarDispersion Q e x :=
  sum_nonneg fun i _ => mul_nonneg (he i) (sq_nonneg _)

variable [Nonempty κ]

/-- The matrix correction is exactly a weighted variance, hence positive semidefinite. -/
theorem qf_polarGluingCorrection (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 < qf (Q i) e) :
    qf (polarGluingCorrection Q e) x = polarDispersion Q e x := by
  have h := HTGeometry.schurComplement_sum_eq (fun _ : κ => (0 : ℝ))
    (fun i => bil (Q i) e x) (fun i => qf (Q i) e) he
  simp only [sum_const_zero, zero_sub, sum_neg_distrib] at h
  simp only [polarGluingCorrection, qf_sub_matrix, qf_sum_matrix, qf_anchorSquare,
    polarDispersion, bil_sum_family]
  linarith

theorem polarGluingCorrection_nonneg (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 < qf (Q i) e) : 0 ≤ qf (polarGluingCorrection Q e) x := by
  rw [qf_polarGluingCorrection Q e x he]
  exact polarDispersion_nonneg Q e x fun i => (he i).le

/-- Exact gluing law: local reserves pay the dispersion of their polar directions. -/
theorem anchorReserve_sum (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 < qf (Q i) e) :
    anchorReserve (∑ i, Q i) e x =
      (∑ i, anchorReserve (Q i) e x) - polarDispersion Q e x := by
  rw [← qf_polarGluingCorrection Q e x he]
  simp only [anchorReserve, polarGluingCorrection, qf_sub_matrix, qf_sum_matrix,
    qf_anchorSquare, sum_sub_distrib]
  ring

/-- Sharp summation criterion, without assuming any local signature. -/
theorem isHyperbolic_sum_iff_dispersion_le (Q : κ → Matrix ι ι ℝ)
    (hQ : ∀ i, (Q i).IsSymm) (e : ι → ℝ) (he : ∀ i, 0 < qf (Q i) e) :
    IsHyperbolic (∑ i, Q i) ↔
      ∀ x, polarDispersion Q e x ≤ ∑ i, anchorReserve (Q i) e x := by
  have hs := isSymm_sum_matrix Q hQ
  have ha : 0 < qf (∑ i, Q i) e := by
    rw [qf_sum_matrix]
    exact sum_pos (fun i _ => he i) univ_nonempty
  rw [isHyperbolic_iff_anchorReserve_nonneg hs ha]
  exact forall_congr' fun x => by rw [anchorReserve_sum Q e x he, sub_nonneg]

/-- Subtracting the dispersion glues local forms without changing their total polar row. -/
def polarGlue (Q : κ → Matrix ι ι ℝ) (e : ι → ℝ) : Matrix ι ι ℝ :=
  (∑ i, Q i) - polarGluingCorrection Q e

omit [Nonempty κ] in
/-- A glued form consists of one total polar square minus the sum of local reserves. -/
theorem qf_polarGlue (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ) :
    qf (polarGlue Q e) x = bil (∑ i, Q i) e x ^ 2 / qf (∑ i, Q i) e -
      ∑ i, anchorReserve (Q i) e x := by
  simp only [polarGlue, polarGluingCorrection, qf_sub_matrix, qf_sum_matrix,
    qf_anchorSquare, anchorReserve, sum_sub_distrib]
  ring

theorem bil_polarGluingCorrection_anchor (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 < qf (Q i) e) : bil (polarGluingCorrection Q e) e x = 0 := by
  have ha : 0 < qf (∑ i, Q i) e := by
    rw [qf_sum_matrix]
    exact sum_pos (fun i _ => he i) univ_nonempty
  simp only [polarGluingCorrection, bil_sub_matrix, bil_sum_family]
  rw [bil_anchorSquare_anchor ha.ne']
  rw [sum_congr rfl (fun i _ => bil_anchorSquare_anchor (he i).ne' x), bil_sum_family]
  exact sub_self _

theorem bil_polarGlue_anchor (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 < qf (Q i) e) : bil (polarGlue Q e) e x = bil (∑ i, Q i) e x := by
  rw [polarGlue, bil_sub_matrix, bil_polarGluingCorrection_anchor Q e x he, sub_zero]

/-- Local reserves add exactly after the correction. -/
theorem anchorReserve_polarGlue (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 < qf (Q i) e) :
    anchorReserve (polarGlue Q e) e x = ∑ i, anchorReserve (Q i) e x := by
  have hq : qf (polarGlue Q e) e = qf (∑ i, Q i) e :=
    bil_polarGlue_anchor Q e e he
  rw [anchorReserve, bil_polarGlue_anchor Q e x he, hq,
    polarGlue, qf_sub_matrix, qf_polarGluingCorrection Q e x he]
  have h := anchorReserve_sum Q e x he
  unfold anchorReserve at h ⊢
  linarith

/-- Constructive closure under polar gluing. The correction is part of the constructed form. -/
theorem isHyperbolic_polarGlue (Q : κ → Matrix ι ι ℝ) (hQ : ∀ i, (Q i).IsSymm)
    (e : ι → ℝ) (he : ∀ i, 0 < qf (Q i) e) (hH : ∀ i, IsHyperbolic (Q i)) :
    IsHyperbolic (polarGlue Q e) := by
  have hs := isSymm_sum_matrix Q hQ
  have hg : (polarGlue Q e).IsSymm := hs.sub (polarGluingCorrection_isSymm Q e)
  have ha : 0 < qf (polarGlue Q e) e := by
    change 0 < bil (polarGlue Q e) e e
    rw [bil_polarGlue_anchor Q e e he, bil_sum_family]
    exact sum_pos (fun i _ => he i) univ_nonempty
  apply (isHyperbolic_iff_anchorReserve_nonneg hg ha).mpr
  intro x
  rw [anchorReserve_polarGlue Q e x he]
  exact sum_nonneg fun i _ =>
    (isHyperbolic_iff_anchorReserve_nonneg (hQ i) (he i)).mp (hH i) x

omit [Nonempty κ] in
/-- Dispersion vanishes precisely when all normalized polar readings agree. -/
theorem polarDispersion_eq_zero_iff (Q : κ → Matrix ι ι ℝ) (e x : ι → ℝ)
    (he : ∀ i, 0 < qf (Q i) e) :
    polarDispersion Q e x = 0 ↔ ∀ i,
      bil (Q i) e x / qf (Q i) e = bil (∑ j, Q j) e x / qf (∑ j, Q j) e := by
  rw [polarDispersion, sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (he i).le (sq_nonneg _))]
  constructor
  · intro h i
    have hz := (mul_eq_zero.mp (h i (mem_univ i))).resolve_left (he i).ne'
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hz)
  · intro h i _
    rw [h i, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

/-- Without local reserve, alignment is necessary as well as sufficient for summation. -/
theorem isHyperbolic_sum_iff_alignment_of_zero_reserve (Q : κ → Matrix ι ι ℝ)
    (hQ : ∀ i, (Q i).IsSymm) (e : ι → ℝ) (he : ∀ i, 0 < qf (Q i) e)
    (hzero : ∀ i x, anchorReserve (Q i) e x = 0) :
    IsHyperbolic (∑ i, Q i) ↔ ∀ x i,
      bil (Q i) e x / qf (Q i) e = bil (∑ j, Q j) e x / qf (∑ j, Q j) e := by
  rw [isHyperbolic_sum_iff_dispersion_le Q hQ e he]
  have hz (x : ι → ℝ) : (∑ i, anchorReserve (Q i) e x) = 0 :=
    sum_eq_zero fun i _ => hzero i x
  constructor
  · intro h x
    have hv : polarDispersion Q e x = 0 := le_antisymm
      (by simpa only [hz x] using h x) (polarDispersion_nonneg Q e x fun i => (he i).le)
    exact (polarDispersion_eq_zero_iff Q e x he).mp hv
  · intro h x
    rw [hz x, (polarDispersion_eq_zero_iff Q e x he).mpr (h x)]

omit [Nonempty κ] in
/-- Grouping local pieces adds within-group and between-group corrections exactly. -/
theorem polarGluingCorrection_group (Q : κ → τ → Matrix ι ι ℝ) (e : ι → ℝ) :
    polarGluingCorrection (fun i : κ × τ => Q i.1 i.2) e =
      (∑ i, polarGluingCorrection (Q i) e) +
        polarGluingCorrection (fun i => ∑ j, Q i j) e := by
  simp only [polarGluingCorrection, Fintype.sum_prod_type, sum_sub_distrib]
  abel

omit [Nonempty κ] in
/-- Corrected assembly is associative as a quadratic form. -/
theorem qf_polarGlue_group [Nonempty τ] (Q : κ → τ → Matrix ι ι ℝ)
    (e x : ι → ℝ) (he : ∀ i j, 0 < qf (Q i j) e) :
    qf (polarGlue (fun i => polarGlue (Q i) e) e) x =
      qf (polarGlue (fun i : κ × τ => Q i.1 i.2) e) x := by
  have hb (i : κ) : bil (polarGlue (Q i) e) e x = ∑ j, bil (Q i j) e x := by
    rw [bil_polarGlue_anchor (Q i) e x (he i), bil_sum_family]
  have ha (i : κ) : qf (polarGlue (Q i) e) e = ∑ j, qf (Q i j) e := by
    change bil (polarGlue (Q i) e) e e = _
    rw [bil_polarGlue_anchor (Q i) e e (he i), bil_sum_family]
    rfl
  have hr (i : κ) := anchorReserve_polarGlue (Q i) e x (he i)
  rw [qf_polarGlue, qf_polarGlue]
  simp only [bil_sum_family, qf_sum_matrix, hb, ha, hr, Fintype.sum_prod_type]

omit [Nonempty κ] in
/-- Polar correction commutes with linear restriction when the anchor is mapped with the tests. -/
theorem qf_polarGluingCorrection_pullback (Q : κ → Matrix ι ι ℝ)
    (A : Matrix ι τ ℝ) (e x : τ → ℝ) :
    qf (polarGluingCorrection (fun i => Aᵀ * Q i * A) e) x =
      qf (polarGluingCorrection Q (A *ᵥ e)) (A *ᵥ x) := by
  simp only [polarGluingCorrection, qf_sub_matrix, qf_sum_matrix, qf_anchorSquare,
    bil_sum_family, bil_pullback, qf_matrix_pullback]

omit [Nonempty κ] in
/-- Gluing and anchor-preserving linear restriction give the same quadratic form. -/
theorem qf_polarGlue_pullback (Q : κ → Matrix ι ι ℝ)
    (A : Matrix ι τ ℝ) (e x : τ → ℝ) :
    qf (polarGlue (fun i => Aᵀ * Q i * A) e) x =
      qf (polarGlue Q (A *ᵥ e)) (A *ᵥ x) := by
  simp only [polarGlue, qf_sub_matrix, qf_sum_matrix, qf_matrix_pullback,
    qf_polarGluingCorrection_pullback]

/-! ### Sharp two-plane calibration -/

/-- A plane with polar slope `t` and transverse reserve `r`. -/
def tiltedPlane (t r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, t; t, t ^ 2 - r]

theorem tiltedPlane_isSymm (t r : ℝ) : (tiltedPlane t r).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem qf_tiltedPlane (t r : ℝ) (x : Fin 2 → ℝ) :
    qf (tiltedPlane t r) x = (x 0 + t * x 1) ^ 2 - r * x 1 ^ 2 := by
  simp [qf, bil, tiltedPlane, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Each tilted plane is hyperbolic exactly when its transverse reserve is nonnegative. -/
theorem isHyperbolic_tiltedPlane_iff (t r : ℝ) :
    IsHyperbolic (tiltedPlane t r) ↔ 0 ≤ r := by
  constructor
  · intro h
    have h' := h ![1, 0] ![0, 1] (by simp [qf_tiltedPlane])
    rw [qf_tiltedPlane, qf_tiltedPlane] at h'
    simp [bil, tiltedPlane, mulVec, dotProduct, Fin.sum_univ_two] at h'
    linarith only [h']
  · intro hr
    apply isHyperbolic_of_nonpos_on_ker (tiltedPlane_isSymm t r) (dotLeft ![1, t])
    intro x hx
    have hx' : x 0 + t * x 1 = 0 := by
      simpa [dotLeft, dotProduct, Fin.sum_univ_two] using hx
    rw [qf_tiltedPlane, hx']
    nlinarith only [mul_nonneg hr (sq_nonneg (x 1))]

/-- Opposite polar slopes cost exactly `t²` per local transverse direction. -/
theorem isHyperbolic_opposite_tiltedPlanes_iff (t r : ℝ) :
    IsHyperbolic (tiltedPlane t r + tiltedPlane (-t) r) ↔ t ^ 2 ≤ r := by
  have hs := (tiltedPlane_isSymm t r).add (tiltedPlane_isSymm (-t) r)
  have hq (x : Fin 2 → ℝ) :
      qf (tiltedPlane t r + tiltedPlane (-t) r) x =
        2 * x 0 ^ 2 + 2 * (t ^ 2 - r) * x 1 ^ 2 := by
    rw [qf_add_matrix, qf_tiltedPlane, qf_tiltedPlane]
    ring
  constructor
  · intro h
    have h' := h ![1, 0] ![0, 1] (by simp [hq])
    have hb : bil (tiltedPlane t r + tiltedPlane (-t) r) ![1, 0] ![0, 1] = 0 := by
      simp [bil, tiltedPlane, mulVec, dotProduct, Fin.sum_univ_two]
    rw [hq, hq, hb] at h'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h'
    nlinarith only [h']
  · intro hr
    apply isHyperbolic_of_nonpos_on_ker hs (dotLeft ![1, 0])
    intro x hx
    have hx' : x 0 = 0 := by simpa [dotLeft, dotProduct, Fin.sum_univ_two] using hx
    rw [hq, hx']
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (x 1))]

/-- The exact correction for two opposite slopes is the transverse square `2t² x₁²`. -/
theorem polarGluingCorrection_opposite_tiltedPlanes (t r : ℝ) :
    polarGluingCorrection ![tiltedPlane t r, tiltedPlane (-t) r] ![1, 0] =
      !![0, 0; 0, 2 * t ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [polarGluingCorrection, anchorSquare, qf, bil, tiltedPlane, mulVec,
      dotProduct, Fin.sum_univ_two, vecMulVec]
  ring

#print axioms anchorReserve_sum
#print axioms isHyperbolic_sum_iff_dispersion_le
#print axioms isHyperbolic_polarGlue
#print axioms isHyperbolic_sum_iff_alignment_of_zero_reserve
#print axioms polarGluingCorrection_group
#print axioms qf_polarGlue_group
#print axioms qf_polarGluingCorrection_pullback
#print axioms qf_polarGlue_pullback
#print axioms isHyperbolic_opposite_tiltedPlanes_iff
#print axioms polarGluingCorrection_opposite_tiltedPlanes

end GaloisForLFunctions.ArithmeticLorentzianGeometry
