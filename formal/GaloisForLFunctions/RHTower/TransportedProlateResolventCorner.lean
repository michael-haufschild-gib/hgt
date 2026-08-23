import GaloisForLFunctions.RHTower.SoninSylvesterFactorization

/-!
# The transported prolate relative-resolvent corner

Transporting a self-adjoint operator with trace-class resolvent through a boundedly invertible map
gives a closed operator, similar to a self-adjoint one, whose resolvent is again trace class; if
the archimedean Sonin space reduces the original resolvent, its image reduces the transported one.

The relative-resolvent Sonin corner of the transported control is then the Sylvester transform of
the Euler metric crossing, hence trace class.  Its nonvanishing does not need the whole Sonin
restriction: it is enough to compress to the negative spectral part, whose complement inside the
Sonin space is finite dimensional.  A noncompact crossing cannot be killed by a compact — in
particular a finite-rank — complement, so the compressed crossing is nonzero, and disjoint
compressed spectra then force the corner to be nonzero.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-! ## Item 1: the transported resolvent is again trace class -/

/-- Conjugation of a bounded operator by a boundedly invertible map. -/
def conjOp (θ : H ≃L[ℂ] H) (R : H →L[ℂ] H) : H →L[ℂ] H :=
  (θ : H →L[ℂ] H) * R * (θ.symm : H →L[ℂ] H)

omit [CompleteSpace H] in
/-- **Similarity preserves the Schatten ideals.**  The transport of a Schatten-class operator by a
boundedly invertible map is again Schatten class of the same order. -/
theorem memSchattenClass_conjOp {p : ℝ} (hp : 0 < p) (θ : H ≃L[ℂ] H) {R : H →L[ℂ] H}
    (hR : MemSchattenClass p R) : MemSchattenClass p (conjOp θ R) := by
  have h1 : MemSchattenClass p ((θ : H →L[ℂ] H) * R) := memSchattenClass_comp_left hp hR
  exact memSchattenClass_comp_right hp h1

omit [CompleteSpace H] in
/-- Conjugation is an algebra homomorphism, so it carries every operator identity — in particular
the resolvent identity — to the transported picture. -/
theorem conjOp_mul (θ : H ≃L[ℂ] H) (R S : H →L[ℂ] H) :
    conjOp θ R * conjOp θ S = conjOp θ (R * S) := by
  ext x
  simp [conjOp]

/-! ## Item 2: the transported Sonin space reduces the transported resolvent -/

omit [CompleteSpace H] in
/-- **Transport of reduction.**  If a projection reduces an operator, its conjugate reduces the
conjugated operator. -/
theorem conjOp_reduces (θ : H ≃L[ℂ] H) {Q R : H →L[ℂ] H} (hred : R * Q = Q * R * Q) :
    conjOp θ R * conjOp θ Q = conjOp θ Q * conjOp θ R * conjOp θ Q := by
  rw [conjOp_mul, conjOp_mul, conjOp_mul, hred]

omit [CompleteSpace H] in
/-- Conjugation preserves idempotents. -/
theorem conjOp_idem (θ : H ≃L[ℂ] H) {Q : H →L[ℂ] H} (hQ : Q * Q = Q) :
    conjOp θ Q * conjOp θ Q = conjOp θ Q := by
  rw [conjOp_mul, hQ]

/-! ## Item 3: nonvanishing through the negative spectral part -/

omit [CompleteSpace H] in
/-- A noncompact operator cannot be supported on a compact complement: if `X (1 − E)` is compact
and `X` is not, then `X E` is nonzero. -/
theorem mul_ne_zero_of_not_isCompactOperator {X E : H →L[ℂ] H}
    (hcomp : IsCompactOperator ⇑(X * (1 - E))) (hX : ¬ IsCompactOperator ⇑X) :
    X * E ≠ 0 := by
  intro h
  refine hX ?_
  have hsplit : X = X * (1 - E) + X * E := by noncomm_ring
  rw [hsplit, h, add_zero]
  exact hcomp

/-- **The compressed Sylvester criterion.**  If a subprojection `E` reduces the inner resolvent,
the compressed crossing `X E` is nonzero, and the outer spectrum is disjoint from the compressed
inner spectrum, then the full relative-resolvent corner is nonzero. -/
theorem sylvester_ne_zero_of_compressed [Nontrivial (H →L[ℂ] H)]
    {A B X E : H →L[ℂ] H} (hE : E * E = E)
    (hA : IsSelfAdjoint A) (hBE : IsSelfAdjoint (E * B * E))
    (hred : B * E = E * B * E) (hne : X * E ≠ 0)
    (hdisj : Disjoint (spectrum ℝ A) (spectrum ℝ (E * B * E))) :
    A * X - X * B ≠ 0 := by
  intro hzero
  have hcompressed : A * (X * E) - (X * E) * (E * B * E) = 0 := by
    have hmul : (A * X - X * B) * E = 0 := by rw [hzero, zero_mul]
    have hexp : (A * X - X * B) * E = A * (X * E) - X * (B * E) := by noncomm_ring
    rw [hexp, hred] at hmul
    have hXE : (X * E) * (E * B * E) = X * (E * B * E) := by
      have hstep : (X * E) * (E * B * E) = X * ((E * E) * B * E) := by noncomm_ring
      rw [hstep, hE]
    rw [hXE]
    exact hmul
  exact hne (eq_zero_of_intertwine_of_disjoint_spectrum hA hBE
    (sub_eq_zero.mp hcompressed) hdisj)

/-! ## The card's theorem -/

/-- **The transported prolate relative-resolvent corner.**  With a trace-class archimedean
resolvent, a boundedly invertible transport, a Sonin projection reducing the inner resolvent, a
noncompact Euler metric crossing whose finite-dimensional positive exceptional part is compact,
and disjoint compressed spectra, the exact relative-resolvent Sonin corner is trace class and
nonzero. -/
theorem transported_relativeResolvent_corner [Nontrivial (H →L[ℂ] H)]
    {Q G Rhat Rinf E : H →L[ℂ] H}
    (hQ : Q * Q = Q) (hinv : (1 - Q) * Rhat * Q = 0) (hred : Rinf * Q = Q * Rinf * Q)
    (hA : MemSchattenClass 1 (soninOuter Q Rhat))
    (hB : MemSchattenClass 1 (soninInner Q Rinf))
    (hE : E * E = E)
    (hAsa : IsSelfAdjoint (soninOuter Q Rhat))
    (hBEsa : IsSelfAdjoint (E * soninInner Q Rinf * E))
    (hEred : soninInner Q Rinf * E = E * soninInner Q Rinf * E)
    (hcomp : IsCompactOperator ⇑(soninCross Q G * (1 - E)))
    (hnoncomp : ¬ IsCompactOperator ⇑(soninCross Q G))
    (hdisj : Disjoint (spectrum ℝ (soninOuter Q Rhat))
      (spectrum ℝ (E * soninInner Q Rinf * E))) :
    MemSchattenClass 1 ((1 - Q) * (Rhat * G - G * Rinf) * Q)
      ∧ (1 - Q) * (Rhat * G - G * Rinf) * Q ≠ 0 := by
  have hfac := sonin_sylvester_factorization (G := G) hQ hinv hred
  constructor
  · rw [hfac]
    exact memSchattenClass_one_sylvester hA hB
  · rw [hfac]
    exact sylvester_ne_zero_of_compressed hE hAsa hBEsa hEred
      (mul_ne_zero_of_not_isCompactOperator hcomp hnoncomp) hdisj

end

end RHTower
