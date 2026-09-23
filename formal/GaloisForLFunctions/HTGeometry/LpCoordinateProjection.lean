import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# Coordinate projections on complex `ell^(2 : ℕ)`

Restriction to an arbitrary coordinate set is packaged as an unconditional orthogonal projection.
The module supplies its exact norm and inner-product value relations, including a real-coordinate
criterion that discharges the phase interface in complex cutoff Ward laws.
-/

open Complex Set
open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinate restriction to a set, as a norm-one orthogonal projection on complex `ell^(2 : ℕ)`. -/
noncomputable def lpCoordinateProjection
    {ι : Type*} (S : Set ι) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  let L : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun x =>
        ⟨S.indicator (fun i => x i),
          (lp.memℓp x).mono' (fun i => by
            by_cases hi : i ∈ S
            · rw [indicator_of_mem hi]
            · rw [indicator_of_notMem hi]
              simp)⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change S.indicator (fun j => x j + y j) i =
          S.indicator (fun j => x j) i + S.indicator (fun j => y j) i
        by_cases hi : i ∈ S
        · simp only [indicator_of_mem hi]
        · simp only [indicator_of_notMem hi, add_zero]
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change S.indicator (fun j => c * x j) i =
          c * S.indicator (fun j => x j) i
        by_cases hi : i ∈ S
        · simp only [indicator_of_mem hi]
        · simp only [indicator_of_notMem hi, mul_zero] }
  exact L.mkContinuous 1 (fun x => by
    simpa using lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun i => by
      change ‖S.indicator (fun j => x j) i‖ ≤ ‖x i‖
      by_cases hi : i ∈ S
      · rw [indicator_of_mem hi]
      · rw [indicator_of_notMem hi]
        simp))

@[simp] theorem lpCoordinateProjection_apply
    {ι : Type*} (S : Set ι) (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpCoordinateProjection S x i = S.indicator (fun j => x j) i := by
  rfl

/-- Coordinate restriction is idempotent, with no caller-supplied projection hypothesis. -/
theorem lpCoordinateProjection_idempotent
    {ι : Type*} (S : Set ι) :
    IsIdempotentElem (lpCoordinateProjection S) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i ∈ S
  · simp only [mul_apply_eq_comp, lpCoordinateProjection_apply,
      indicator_of_mem hi]
  · simp only [mul_apply_eq_comp, lpCoordinateProjection_apply,
      indicator_of_notMem hi]

/-- Coordinate restriction is self-adjoint, with no caller-supplied adjoint hypothesis. -/
theorem lpCoordinateProjection_selfAdjoint
    {ι : Type*} (S : Set ι) :
    ContinuousLinearMap.adjoint (lpCoordinateProjection S) =
      lpCoordinateProjection S := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  change inner ℂ (S.indicator (fun j => x j) i) (y i) =
    inner ℂ (x i) (S.indicator (fun j => y j) i)
  by_cases hi : i ∈ S
  · simp only [indicator_of_mem hi]
  · simp only [indicator_of_notMem hi, inner_zero_left, inner_zero_right]

/-- Exact cutoff-mass value relation. -/
theorem norm_lpCoordinateProjection_sq
    {ι : Type*} (S : Set ι) (x : lp (fun _ : ι => ℂ) 2) :
    ‖lpCoordinateProjection S x‖ ^ 2 =
      ∑' i : ι, S.indicator (fun j => ‖x j‖ ^ 2) i := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ S
  · simp only [lpCoordinateProjection_apply, indicator_of_mem hi]
  · simp only [lpCoordinateProjection_apply, indicator_of_notMem hi, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0)]

/-- Exact cutoff-overlap value relation. -/
theorem inner_lpCoordinateProjection
    {ι : Type*} (S : Set ι)
    (x y : lp (fun _ : ι => ℂ) 2) :
    inner ℂ (lpCoordinateProjection S x) (lpCoordinateProjection S y) =
      ∑' i : ι, S.indicator (fun j => inner ℂ (x j) (y j)) i := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ S
  · simp only [lpCoordinateProjection_apply, indicator_of_mem hi]
  · simp only [lpCoordinateProjection_apply, indicator_of_notMem hi, inner_zero_left]

/-- A coordinatewise real overlap has no complex cutoff phase defect. -/
theorem inner_lpCoordinateProjection_im_eq_zero
    {ι : Type*} (S : Set ι)
    (x y : lp (fun _ : ι => ℂ) 2)
    (hreal : ∀ i ∈ S, (inner ℂ (x i) (y i)).im = 0) :
    (inner ℂ (lpCoordinateProjection S x) (lpCoordinateProjection S y)).im = 0 := by
  rw [inner_lpCoordinateProjection]
  have hsum : Summable (fun i : ι =>
      S.indicator (fun j => inner ℂ (x j) (y j)) i) :=
    (lp.summable_inner (lpCoordinateProjection S x)
      (lpCoordinateProjection S y)).congr (fun i => by
        by_cases hi : i ∈ S
        · simp only [lpCoordinateProjection_apply, indicator_of_mem hi]
        · simp only [lpCoordinateProjection_apply, indicator_of_notMem hi,
            inner_zero_left])
  rw [Complex.im_tsum hsum]
  rw [show (fun i : ι =>
      (S.indicator (fun j => inner ℂ (x j) (y j)) i).im) = 0 by
    funext i
    by_cases hi : i ∈ S
    · simp only [indicator_of_mem hi, hreal i hi, Pi.zero_apply]
    · simp only [indicator_of_notMem hi, Complex.zero_im, Pi.zero_apply]]
  exact tsum_zero

end

end GaloisForLFunctions.HTGeometry
