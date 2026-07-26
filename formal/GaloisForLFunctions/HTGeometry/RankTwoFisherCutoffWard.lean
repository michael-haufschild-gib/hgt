import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Complex rank-two Fisher cutoff Ward law

For an orthogonal source state and tangent, the canonical self-adjoint rank-two Fisher connection
has cutoff-commutator energy determined by the truncated `2 x 2` Gram matrix.  Over a complex
Hilbert space the exact law is phase-sensitive: the phase-blind real formula misses the
nonnegative orientation defect `4 * (Im c)^2`.
-/

open Complex
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap InnerProductSpace

/-- Lower off-diagonal corner of an observable relative to a cutoff. -/
noncomputable def cutoffLowerBoundary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e X : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - e) ∘L (X ∘L e)

/-- Upper off-diagonal corner of an observable relative to a cutoff. -/
noncomputable def cutoffUpperBoundary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e X : H →L[ℂ] H) : H →L[ℂ] H :=
  e ∘L (X ∘L (1 - e))

/-- Observable--cutoff commutator, with the lower corner appearing with positive sign. -/
noncomputable def cutoffCommutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e X : H →L[ℂ] H) : H →L[ℂ] H :=
  X ∘L e - e ∘L X

/-- Complementing the cutoff exchanges its lower and upper boundary corners. -/
theorem cutoffLowerBoundary_one_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e X : H →L[ℂ] H) :
    cutoffLowerBoundary (1 - e) X = cutoffUpperBoundary e X := by
  dsimp only [cutoffLowerBoundary, cutoffUpperBoundary]
  noncomm_ring

/-- Complementing the cutoff exchanges its upper and lower boundary corners. -/
theorem cutoffUpperBoundary_one_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e X : H →L[ℂ] H) :
    cutoffUpperBoundary (1 - e) X = cutoffLowerBoundary e X := by
  dsimp only [cutoffLowerBoundary, cutoffUpperBoundary]
  noncomm_ring

/-- Cutoff complementation reverses the orientation of the boundary commutator. -/
theorem cutoffCommutator_one_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e X : H →L[ℂ] H) :
    cutoffCommutator (1 - e) X = -cutoffCommutator e X := by
  ext z
  simp [cutoffCommutator]

/-- **Cutoff-reflection law.** Boundary Hilbert--Schmidt energy is exactly invariant under
exchanging the observed window with its complement. -/
theorem hsNormSq_cutoffCommutator_one_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e X : H →L[ℂ] H) :
    hsNormSq (cutoffCommutator (1 - e) X) =
      hsNormSq (cutoffCommutator e X) := by
  rw [cutoffCommutator_one_sub, hsNormSq_neg_eq_self]

/-- A self-adjoint Hilbert--Schmidt observable has exactly twice the energy of either cutoff
corner. -/
theorem hsNormSq_cutoffCommutator_eq_two_mul_lowerBoundary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : adjoint e = e) (hXAdj : adjoint X = X)
    (hX : IsHilbertSchmidt X) :
    hsNormSq (cutoffCommutator e X) =
      2 * hsNormSq (cutoffLowerBoundary e X) := by
  let L : H →L[ℂ] H := cutoffLowerBoundary e X
  let U : H →L[ℂ] H := cutoffUpperBoundary e X
  have hL : IsHilbertSchmidt L := by
    exact (hX.comp_right e).comp_left (1 - e)
  have hAdjL : adjoint L = U := by
    dsimp only [L, U, cutoffLowerBoundary, cutoffUpperBoundary]
    rw [adjoint_comp, adjoint_comp]
    simp only [map_sub, ContinuousLinearMap.adjoint_one, heAdj, hXAdj]
    ext z
    rfl
  have hU : IsHilbertSchmidt U := by
    rw [← hAdjL]
    exact hL.adjoint
  have hUU : U * U = 0 := by
    dsimp only [U, cutoffUpperBoundary]
    have hzero : (1 - e) * e = 0 := by
      rw [sub_mul, one_mul, he, sub_self]
    change (e * (X * (1 - e))) * (e * (X * (1 - e))) = 0
    calc
      (e * (X * (1 - e))) * (e * (X * (1 - e))) =
          e * X * ((1 - e) * e) * X * (1 - e) := by noncomm_ring
      _ = 0 := by rw [hzero]; simp
  have horth : hsInner L U = 0 := by
    have htrace : opTrace (adjoint L ∘L U) = hsInner L U := by
      simpa using opTrace_comp_eq_hsInner (adjoint L) U
    calc
      hsInner L U = opTrace (adjoint L ∘L U) := htrace.symm
      _ = opTrace (U ∘L U) := by rw [hAdjL]
      _ = opTrace 0 := congrArg opTrace (by
        change U * U = 0
        exact hUU)
      _ = 0 := by simp [opTrace]
  have hUnorm : hsNormSq U = hsNormSq L := by
    rw [← hAdjL]
    exact hL.hsNormSq_adjoint
  have hcomm : cutoffCommutator e X = L - U := by
    dsimp only [L, U, cutoffCommutator, cutoffLowerBoundary, cutoffUpperBoundary]
    change X * e - e * X = (1 - e) * X * e - e * X * (1 - e)
    noncomm_ring [he]
  rw [hcomm]
  calc
    hsNormSq (L - U) = hsNormSq L + hsNormSq U :=
      hsNormSq_sub_eq_add_of_hsInner_eq_zero hL hU horth
    _ = 2 * hsNormSq L := by rw [hUnorm]; ring

/-- Canonical self-adjoint rank-two Fisher connection of a pointed source line and tangent. -/
noncomputable def pointedFisherConnection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (psi chi : H) : H →L[ℂ] H :=
  ((Real.sqrt 2)⁻¹ : ℂ) •
    (rankOne ℂ chi psi + rankOne ℂ psi chi)

theorem invSqrtTwo_norm_sq :
    ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem pointedFisherConnection_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi chi : H) :
    adjoint (pointedFisherConnection psi chi) = pointedFisherConnection psi chi := by
  rw [pointedFisherConnection,
    ContinuousLinearMap.adjoint.map_smulₛₗ, map_add,
    adjoint_rankOne, adjoint_rankOne]
  simp only [map_inv₀, Complex.conj_ofReal, add_comm]

theorem pointedFisherConnection_isHilbertSchmidt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi chi : H) :
    IsHilbertSchmidt (pointedFisherConnection psi chi) := by
  exact ((isHilbertSchmidt_rankOne chi psi).add
    (isHilbertSchmidt_rankOne psi chi)).smul _

/-- Total pointed-connection energy, including the complex state--tangent phase term. -/
theorem hsNormSq_pointedFisherConnection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi chi : H) :
    hsNormSq (pointedFisherConnection psi chi) =
      ‖chi‖ ^ 2 * ‖psi‖ ^ 2 + Complex.re ((inner ℂ chi psi) ^ 2) := by
  rw [pointedFisherConnection,
    hsNormSq_smul
      ((isHilbertSchmidt_rankOne chi psi).add
        (isHilbertSchmidt_rankOne psi chi)),
    invSqrtTwo_norm_sq, hsNormSq_rankOne_add_rankOne]
  ring_nf

/-- Orthogonality removes the phase term from the total pointed-connection energy. -/
theorem hsNormSq_pointedFisherConnection_of_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi chi : H) (horth : inner ℂ psi chi = 0) :
    hsNormSq (pointedFisherConnection psi chi) =
      ‖chi‖ ^ 2 * ‖psi‖ ^ 2 := by
  have horth' : inner ℂ chi psi = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  rw [hsNormSq_pointedFisherConnection, horth']
  norm_num

/-- A unit pointed source identifies total connection energy with tangent energy exactly. -/
theorem hsNormSq_pointedFisherConnection_of_unit_of_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi chi : H) (hunit : ‖psi‖ = 1) (horth : inner ℂ psi chi = 0) :
    hsNormSq (pointedFisherConnection psi chi) = ‖chi‖ ^ 2 := by
  rw [hsNormSq_pointedFisherConnection_of_orthogonal psi chi horth, hunit]
  ring_nf

/-- Exact lower-corner value relation for the pointed Fisher connection. -/
theorem pointedFisherConnection_lowerBoundary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (heAdj : adjoint e = e) (psi chi : H) :
    cutoffLowerBoundary e (pointedFisherConnection psi chi) =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        (rankOne ℂ ((1 - e) chi) (e psi) +
          rankOne ℂ ((1 - e) psi) (e chi)) := by
  ext z
  simp only [cutoffLowerBoundary, pointedFisherConnection,
    comp_apply, smul_apply, add_apply, rankOne_apply]
  rw [← adjoint_inner_left, heAdj, ← adjoint_inner_left, heAdj]
  simp only [map_add, map_smul, smul_add, smul_smul]

private theorem inner_complement_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (x y : H) :
    inner ℂ ((1 - e) x) ((1 - e) y) =
      inner ℂ x y - inner ℂ (e x) (e y) := by
  have hxy : inner ℂ (e x) y = inner ℂ x (e y) := by
    simpa only [heAdj] using adjoint_inner_left e y x
  have he_apply : e (e y) = e y := by
    have h := congrArg (fun f : H →L[ℂ] H => f y) he
    simpa only [mul_apply] using h
  have hproj : inner ℂ (e x) (e y) = inner ℂ x (e y) := by
    simpa only [heAdj, he_apply] using adjoint_inner_left e (e y) x
  simp only [sub_apply, one_apply, inner_sub_left, inner_sub_right]
  rw [hxy, hproj]
  ring

private theorem norm_sq_projection_add_complement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (x : H) :
    ‖e x‖ ^ 2 + ‖(1 - e) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hstar : IsStarProjection e := by
    rw [isStarProjection_iff]
    exact ⟨he, by simpa [star_eq_adjoint] using heAdj⟩
  obtain ⟨hRange, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp hstar
  letI : e.range.HasOrthogonalProjection := hRange
  have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection x e.range
  rw [← heq, Submodule.starProjection_orthogonal', ← heq] at hdecomp
  linarith

/-- **Complex rank-two cutoff Ward law.**  The commutator energy is determined by the truncated
Gram matrix, with the complex overlap entering through `Re (c^2)`. -/
theorem hsNormSq_pointedFisherConnection_cutoffCommutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi chi : H) (horth : inner ℂ psi chi = 0) :
    hsNormSq (cutoffCommutator e (pointedFisherConnection psi chi)) =
      (‖chi‖ ^ 2 - ‖e chi‖ ^ 2) * ‖e psi‖ ^ 2 +
      (‖psi‖ ^ 2 - ‖e psi‖ ^ 2) * ‖e chi‖ ^ 2 -
      2 * Complex.re ((inner ℂ (e chi) (e psi)) ^ 2) := by
  have hX := pointedFisherConnection_isHilbertSchmidt psi chi
  rw [hsNormSq_cutoffCommutator_eq_two_mul_lowerBoundary
      e (pointedFisherConnection psi chi) he heAdj
      (pointedFisherConnection_selfAdjoint psi chi) hX,
    pointedFisherConnection_lowerBoundary e heAdj psi chi,
    hsNormSq_smul
      ((isHilbertSchmidt_rankOne ((1 - e) chi) (e psi)).add
        (isHilbertSchmidt_rankOne ((1 - e) psi) (e chi))),
    invSqrtTwo_norm_sq, hsNormSq_rankOne_add_rankOne]
  have hchi := norm_sq_projection_add_complement e he heAdj chi
  have hpsi := norm_sq_projection_add_complement e he heAdj psi
  have horth' : inner ℂ chi psi = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  have hcross := inner_complement_projection e he heAdj chi psi
  rw [horth', zero_sub] at hcross
  rw [hcross]
  simp only [Complex.neg_re, neg_mul, pow_two]
  nlinarith

/-- **Phase-defect value law.**  The phase-blind real formula misses exactly four times the
squared imaginary part of the truncated state--tangent overlap. -/
theorem hsNormSq_pointedFisherConnection_cutoffCommutator_phase
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi chi : H) (horth : inner ℂ psi chi = 0) :
    hsNormSq (cutoffCommutator e (pointedFisherConnection psi chi)) =
      (‖chi‖ ^ 2 - ‖e chi‖ ^ 2) * ‖e psi‖ ^ 2 +
      (‖psi‖ ^ 2 - ‖e psi‖ ^ 2) * ‖e chi‖ ^ 2 -
      2 * ‖inner ℂ (e chi) (e psi)‖ ^ 2 +
      4 * (inner ℂ (e chi) (e psi)).im ^ 2 := by
  rw [hsNormSq_pointedFisherConnection_cutoffCommutator e he heAdj psi chi horth]
  have hphase (z : ℂ) : Complex.re (z ^ 2) = ‖z‖ ^ 2 - 2 * z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [pow_two, Complex.mul_re]
    ring
  rw [hphase]
  ring

/-- **Real-overlap classification.**  The phase-blind formula is exact precisely when the
truncated state--tangent overlap is real. -/
theorem hsNormSq_pointedFisherConnection_cutoffCommutator_eq_phaseBlind_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi chi : H) (horth : inner ℂ psi chi = 0) :
    hsNormSq (cutoffCommutator e (pointedFisherConnection psi chi)) =
        (‖chi‖ ^ 2 - ‖e chi‖ ^ 2) * ‖e psi‖ ^ 2 +
        (‖psi‖ ^ 2 - ‖e psi‖ ^ 2) * ‖e chi‖ ^ 2 -
        2 * ‖inner ℂ (e chi) (e psi)‖ ^ 2 ↔
      (inner ℂ (e chi) (e psi)).im = 0 := by
  rw [hsNormSq_pointedFisherConnection_cutoffCommutator_phase
    e he heAdj psi chi horth]
  constructor
  · intro h
    nlinarith [sq_nonneg (inner ℂ (e chi) (e psi)).im]
  · intro h
    rw [h]
    ring

end

end GaloisForLFunctions.HTGeometry
