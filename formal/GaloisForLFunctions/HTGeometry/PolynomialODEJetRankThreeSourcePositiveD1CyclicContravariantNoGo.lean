import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveInfiniteContravariantNoGo
import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveSeamNoGo
import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading

/-!
# D1 cyclic scalar-contravariant no-go for the source-positive theta sl₂ action

The actual rank-three D1 polynomial has a nonconstant restriction to the invariant boundary
`r=k=0`.  The positive adapted grading `(wt r, wt b, wt k)=(1,1,2)` isolates a positive-weight
D1 component nonzero at `b=1`.  Exact lowering is `-∂b`, so successive lowerings reach a nonzero
constant through a weight-one predecessor.  This produces an internal affine-vacuum string
`Fv=u`, `Eu=0`, `Hv=2v`, `Ev≠0` in every graded `sl₂` carrier containing D1.

Consequently no such carrier admits a positive scalar-contravariant form.  Vacuum pairing forces
the scalar star coefficient to vanish; positivity of `Ev` then gives the contradiction.  No
finite-dimensionality, completion, numerical certificate, or expansion of D1 is used.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- The invariant adapted-coordinate boundary `r=k=0`, parametrized by `b`. -/
def modularThetaSourcePositiveVacuumBoundaryState (b : ℂ) :
    ModularThetaSourcePositiveState → ℂ
  | .U => -3 * b
  | .B => b
  | .Q => (3 / 8 : ℂ) * (b ^ 2 - 1)

/-- Polynomial restriction to the invariant boundary `r=k=0`. -/
def modularThetaSourcePositiveVacuumBoundaryPullback :
    ModularThetaSourcePositivePolynomial →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C fun
    | .U => Polynomial.C (-3 : ℂ) * Polynomial.X
    | .B => Polynomial.X
    | .Q => Polynomial.C (3 / 8 : ℂ) * (Polynomial.X ^ 2 - 1)

theorem eval_modularThetaSourcePositiveVacuumBoundaryPullback
    (b : ℂ) (P : ModularThetaSourcePositivePolynomial) :
    Polynomial.eval b (modularThetaSourcePositiveVacuumBoundaryPullback P) =
      MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState b) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [modularThetaSourcePositiveVacuumBoundaryPullback]
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.eval_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, Polynomial.eval_mul, map_mul, hP]
      apply congrArg (fun z : ℂ =>
        MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState b) P * z)
      cases i <;>
        simp [modularThetaSourcePositiveVacuumBoundaryPullback,
          modularThetaSourcePositiveVacuumBoundaryState]

theorem modularThetaSourcePositiveVacuumBoundaryPullback_sl2F_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveVacuumBoundaryPullback
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
          (MvPolynomial.X i)) =
      -(modularThetaSourcePositiveVacuumBoundaryPullback
        (MvPolynomial.X i)).derivative := by
  cases i <;>
    simp [modularThetaSourcePositiveFieldLie_X,
      modularThetaSourcePositiveVacuumBoundaryPullback,
      modularThetaSourcePositiveSl2F,
      modularThetaSourcePositiveLoweringField] <;>
    apply Polynomial.funext <;>
    intro z <;>
    simp <;>
    ring

theorem modularThetaSourcePositiveVacuumBoundaryPullback_sl2E_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveVacuumBoundaryPullback
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
          (MvPolynomial.X i)) =
      Polynomial.X ^ 2 *
        (modularThetaSourcePositiveVacuumBoundaryPullback
          (MvPolynomial.X i)).derivative := by
  cases i <;>
    simp [modularThetaSourcePositiveFieldLie_X,
      modularThetaSourcePositiveVacuumBoundaryPullback,
      modularThetaSourcePositiveSl2E,
      modularThetaSourcePositiveVectorField,
      modularThetaSourcePositiveLoweringField,
      modularThetaSourcePositiveGap] <;>
    apply Polynomial.funext <;>
    intro z <;>
    simp <;>
    ring

theorem modularThetaSourcePositiveVacuumBoundaryPullback_sl2H_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveVacuumBoundaryPullback
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H
          (MvPolynomial.X i)) =
      2 * Polynomial.X *
        (modularThetaSourcePositiveVacuumBoundaryPullback
          (MvPolynomial.X i)).derivative := by
  cases i <;>
    simp [modularThetaSourcePositiveFieldLie_X,
      modularThetaSourcePositiveVacuumBoundaryPullback,
      modularThetaSourcePositiveSl2H,
      modularThetaSourcePositiveScaleField] <;>
    apply Polynomial.funext <;>
    intro z <;>
    simp <;>
    ring

/-- On the invariant boundary the source lowering action is `-d/db`. -/
theorem modularThetaSourcePositiveVacuumBoundaryPullback_sl2F
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveVacuumBoundaryPullback
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P) =
      -(modularThetaSourcePositiveVacuumBoundaryPullback P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [modularThetaSourcePositiveFieldLie_C,
        modularThetaSourcePositiveVacuumBoundaryPullback]
  | add P Q hP hQ =>
      rw [modularThetaSourcePositiveFieldLie_add, map_add, hP, hQ, map_add]
      rw [Polynomial.derivative_add]
      ring
  | mul_X P i hP =>
      rw [modularThetaSourcePositiveFieldLie_mul,
        map_add, map_mul, map_mul,
        hP, modularThetaSourcePositiveVacuumBoundaryPullback_sl2F_X,
        map_mul]
      rw [Polynomial.derivative_mul]
      ring

/-- On the invariant boundary the source raising action is `b² d/db`. -/
theorem modularThetaSourcePositiveVacuumBoundaryPullback_sl2E
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveVacuumBoundaryPullback
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P) =
      Polynomial.X ^ 2 *
        (modularThetaSourcePositiveVacuumBoundaryPullback P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [modularThetaSourcePositiveFieldLie_C,
        modularThetaSourcePositiveVacuumBoundaryPullback]
  | add P Q hP hQ =>
      rw [modularThetaSourcePositiveFieldLie_add, map_add, hP, hQ, map_add]
      rw [Polynomial.derivative_add]
      ring
  | mul_X P i hP =>
      rw [modularThetaSourcePositiveFieldLie_mul,
        map_add, map_mul, map_mul,
        hP, modularThetaSourcePositiveVacuumBoundaryPullback_sl2E_X,
        map_mul]
      rw [Polynomial.derivative_mul]
      ring

/-- On the invariant boundary the source Cartan action is `2b d/db`. -/
theorem modularThetaSourcePositiveVacuumBoundaryPullback_sl2H
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveVacuumBoundaryPullback
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H P) =
      2 * Polynomial.X *
        (modularThetaSourcePositiveVacuumBoundaryPullback P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [modularThetaSourcePositiveFieldLie_C,
        modularThetaSourcePositiveVacuumBoundaryPullback]
  | add P Q hP hQ =>
      rw [modularThetaSourcePositiveFieldLie_add, map_add, hP, hQ, map_add]
      rw [Polynomial.derivative_add]
      ring
  | mul_X P i hP =>
      rw [modularThetaSourcePositiveFieldLie_mul,
        map_add, map_mul, map_mul,
        hP, modularThetaSourcePositiveVacuumBoundaryPullback_sl2H_X,
        map_mul]
      rw [Polynomial.derivative_mul]
      ring

theorem eval_modularThetaSourcePositiveSl2R_vacuumBoundary (b : ℂ) :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState b)
      modularThetaSourcePositiveSl2R = 0 := by
  simp [modularThetaSourcePositiveVacuumBoundaryState,
    modularThetaSourcePositiveSl2R]

theorem eval_modularThetaSourcePositiveSl2K_vacuumBoundary (b : ℂ) :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState b)
      modularThetaSourcePositiveSl2K = 0 := by
  simp [modularThetaSourcePositiveVacuumBoundaryState,
    modularThetaSourcePositiveSl2K]
  ring

theorem eval_modularThetaSourcePositiveVectorField_vacuumBoundary_one
    (i : ModularThetaSourcePositiveState) :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 1)
      (modularThetaSourcePositiveVectorField i) = 0 := by
  cases i <;>
    simp [modularThetaSourcePositiveVacuumBoundaryState,
      modularThetaSourcePositiveVectorField,
      modularThetaSourcePositiveGap] <;>
    ring

theorem eval_modularThetaSourcePositiveNormalizedLie_vacuumBoundary_one
    (P : ModularThetaSourcePositivePolynomial) :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 1)
      (modularThetaSourcePositiveNormalizedLie P) =
      (1 / 2 : ℂ) *
        MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 1) P := by
  unfold modularThetaSourcePositiveNormalizedLie modularThetaSourcePositiveLie
  simp only [map_add, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X]
  simp_rw [eval_modularThetaSourcePositiveVectorField_vacuumBoundary_one]
  simp [modularThetaSourcePositiveVacuumBoundaryState]

theorem eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one
    (n : ℕ) :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 1)
      (modularThetaSourcePositiveNormalizedSourceJet n) = 0 := by
  induction n with
  | zero =>
      simp [modularThetaSourcePositiveNormalizedSourceJet,
        modularThetaSourcePositiveVacuumBoundaryState]
  | succ n ih =>
      rw [modularThetaSourcePositiveNormalizedSourceJet,
        eval_modularThetaSourcePositiveNormalizedLie_vacuumBoundary_one,
        ih, mul_zero]

theorem eval_modularThetaSourcePositiveReflectedEighthPolynomial_vacuumBoundary_one :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 1)
      modularThetaSourcePositiveReflectedEighthPolynomial = 0 := by
  unfold modularThetaSourcePositiveReflectedEighthPolynomial
  simp only [map_sub, map_mul, map_pow, map_add, MvPolynomial.eval_C]
  rw [eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 0,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 1,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 2,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 3,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 4,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 5,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 6,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 7,
    eval_modularThetaSourcePositiveNormalizedSourceJet_vacuumBoundary_one 8]
  ring

theorem eval_modularThetaSourcePositiveChartPullback_vacuumBoundary_zero
    (P : ModularThetaLyapunovPolynomial) :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 0)
        (modularThetaSourcePositiveChartPullback P) =
      MvPolynomial.eval (modularThetaLyapunovSeamState 0) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      simp only [map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, hP,
        modularThetaSourcePositiveChartPullback_X]
      rw [map_mul]
      apply congrArg (fun z : ℂ =>
        MvPolynomial.eval (modularThetaLyapunovSeamState 0) P * z)
      cases i <;>
        simp [modularThetaSourcePositiveChartCoordinate,
          modularThetaSourcePositiveGap,
          modularThetaSourcePositiveVacuumBoundaryState,
          modularThetaLyapunovSeamState] <;>
        ring

theorem eval_modularThetaSourcePositiveReflectedEighthPolynomial_vacuumBoundary_zero :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 0)
        modularThetaSourcePositiveReflectedEighthPolynomial =
      modularThetaReflectedEighthSeamPolynomial 0 := by
  rw [← modularThetaSourcePositiveChart_reflectedEighthPolynomial,
    eval_modularThetaSourcePositiveChartPullback_vacuumBoundary_zero,
    eval_modularThetaLyapunovReflectedEighthPolynomial_seam]
  simp

/-- D1 has a nonconstant shadow on the invariant vacuum boundary. -/
theorem eval_modularThetaSourcePositiveReflectedEighthPolynomial_vacuumBoundary_zero_ne_one :
    MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 0)
        modularThetaSourcePositiveReflectedEighthPolynomial ≠
      MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState 1)
        modularThetaSourcePositiveReflectedEighthPolynomial := by
  rw [eval_modularThetaSourcePositiveReflectedEighthPolynomial_vacuumBoundary_zero,
    eval_modularThetaSourcePositiveReflectedEighthPolynomial_vacuumBoundary_one]
  norm_num [modularThetaReflectedEighthSeamPolynomial]

/-- The D1 boundary shadow is genuinely nonconstant. -/
theorem modularThetaSourcePositiveReflectedEighth_vacuumBoundaryPullback_not_constant :
    ¬ ∃ c : ℂ,
      modularThetaSourcePositiveVacuumBoundaryPullback
        modularThetaSourcePositiveReflectedEighthPolynomial = Polynomial.C c := by
  rintro ⟨c, hc⟩
  apply eval_modularThetaSourcePositiveReflectedEighthPolynomial_vacuumBoundary_zero_ne_one
  rw [← eval_modularThetaSourcePositiveVacuumBoundaryPullback,
    ← eval_modularThetaSourcePositiveVacuumBoundaryPullback, hc]
  simp

/-! ## Adapted positive grading -/

/-- Positive weights of the lowering-adapted coordinates `(r,b,k)`. -/
def modularThetaSourcePositiveAdaptedWeight :
    ModularThetaSourcePositiveState → ℕ
  | .U => 1
  | .B => 1
  | .Q => 2

/-- Rewrite an original `(U,B,Q)` polynomial in abstract `(r,b,k)` coordinates. -/
def modularThetaSourcePositiveToAdaptedCoordinate :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial
  | .U => MvPolynomial.X .U - MvPolynomial.C (3 : ℂ) * MvPolynomial.X .B
  | .B => MvPolynomial.X .B
  | .Q => MvPolynomial.X .Q - MvPolynomial.C (3 / 8 : ℂ) +
      MvPolynomial.C (3 / 8 : ℂ) * MvPolynomial.X .B ^ 2

def modularThetaSourcePositiveToAdapted :
    ModularThetaSourcePositivePolynomial →+* ModularThetaSourcePositivePolynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    modularThetaSourcePositiveToAdaptedCoordinate

/-- Interpret an abstract `(r,b,k)` polynomial back in original coordinates. -/
def modularThetaSourcePositiveOfAdaptedCoordinate :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial
  | .U => modularThetaSourcePositiveSl2R
  | .B => MvPolynomial.X .B
  | .Q => modularThetaSourcePositiveSl2K

def modularThetaSourcePositiveOfAdapted :
    ModularThetaSourcePositivePolynomial →+* ModularThetaSourcePositivePolynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    modularThetaSourcePositiveOfAdaptedCoordinate

@[simp] theorem modularThetaSourcePositiveToAdapted_C (c : ℂ) :
    modularThetaSourcePositiveToAdapted (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [modularThetaSourcePositiveToAdapted]

@[simp] theorem modularThetaSourcePositiveToAdapted_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveToAdapted (MvPolynomial.X i) =
      modularThetaSourcePositiveToAdaptedCoordinate i := by
  simp [modularThetaSourcePositiveToAdapted]

@[simp] theorem modularThetaSourcePositiveOfAdapted_C (c : ℂ) :
    modularThetaSourcePositiveOfAdapted (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [modularThetaSourcePositiveOfAdapted]

@[simp] theorem modularThetaSourcePositiveOfAdapted_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveOfAdapted (MvPolynomial.X i) =
      modularThetaSourcePositiveOfAdaptedCoordinate i := by
  simp [modularThetaSourcePositiveOfAdapted]

theorem modularThetaSourcePositiveToAdapted_comp_ofAdapted :
    modularThetaSourcePositiveToAdapted.comp modularThetaSourcePositiveOfAdapted =
      RingHom.id ModularThetaSourcePositivePolynomial := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    cases i <;>
      simp [modularThetaSourcePositiveToAdaptedCoordinate,
        modularThetaSourcePositiveOfAdaptedCoordinate,
        modularThetaSourcePositiveSl2R, modularThetaSourcePositiveSl2K]
    all_goals
      apply MvPolynomial.funext
      intro v
      simp
    all_goals ring

theorem modularThetaSourcePositiveOfAdapted_comp_toAdapted :
    modularThetaSourcePositiveOfAdapted.comp modularThetaSourcePositiveToAdapted =
      RingHom.id ModularThetaSourcePositivePolynomial := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    cases i <;>
      simp [modularThetaSourcePositiveToAdaptedCoordinate,
        modularThetaSourcePositiveOfAdaptedCoordinate,
        modularThetaSourcePositiveSl2R, modularThetaSourcePositiveSl2K]
    all_goals
      apply MvPolynomial.funext
      intro v
      simp
    all_goals ring

theorem modularThetaSourcePositiveToAdapted_injective :
    Function.Injective modularThetaSourcePositiveToAdapted := by
  intro P Q hPQ
  have h := congrArg modularThetaSourcePositiveOfAdapted hPQ
  simpa [← RingHom.comp_apply,
    modularThetaSourcePositiveOfAdapted_comp_toAdapted] using h

theorem modularThetaSourcePositiveOfAdapted_injective :
    Function.Injective modularThetaSourcePositiveOfAdapted := by
  intro P Q hPQ
  have h := congrArg modularThetaSourcePositiveToAdapted hPQ
  simpa [← RingHom.comp_apply,
    modularThetaSourcePositiveToAdapted_comp_ofAdapted] using h

/-- Adapted-weight component of an original source polynomial. -/
def modularThetaSourcePositiveAdaptedComponent
    (W : ℕ) (P : ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositivePolynomial :=
  modularThetaSourcePositiveOfAdapted
    (MvPolynomial.weightedHomogeneousComponent
      modularThetaSourcePositiveAdaptedWeight W
      (modularThetaSourcePositiveToAdapted P))

/-- Set `r=k=0` in an adapted polynomial, retaining the clock coordinate `b`. -/
def modularThetaSourcePositiveAdaptedBoundaryCoordinate :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial
  | .U => 0
  | .B => MvPolynomial.X .B
  | .Q => 0

def modularThetaSourcePositiveAdaptedBoundary :
    ModularThetaSourcePositivePolynomial →+* ModularThetaSourcePositivePolynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    modularThetaSourcePositiveAdaptedBoundaryCoordinate

/-- Boundary restriction expressed as an endomorphism of the source polynomial ring. -/
def modularThetaSourcePositiveVacuumBoundaryEnd :
    ModularThetaSourcePositivePolynomial →+* ModularThetaSourcePositivePolynomial :=
  modularThetaSourcePositiveAdaptedBoundary.comp
    modularThetaSourcePositiveToAdapted

theorem eval_modularThetaSourcePositiveVacuumBoundaryEnd
    (b : ℂ) (P : ModularThetaSourcePositivePolynomial) :
    MvPolynomial.eval
        (fun i => match i with
          | .U => 0
          | .B => b
          | .Q => 0)
        (modularThetaSourcePositiveVacuumBoundaryEnd P) =
      MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState b) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [modularThetaSourcePositiveVacuumBoundaryEnd,
      modularThetaSourcePositiveAdaptedBoundary,
      modularThetaSourcePositiveToAdapted]
  | add P Q hP hQ =>
      simp only [map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, map_mul, hP]
      apply congrArg (fun z : ℂ =>
        MvPolynomial.eval (modularThetaSourcePositiveVacuumBoundaryState b) P * z)
      cases i <;>
        simp [modularThetaSourcePositiveVacuumBoundaryEnd,
          modularThetaSourcePositiveAdaptedBoundary,
          modularThetaSourcePositiveAdaptedBoundaryCoordinate,
          modularThetaSourcePositiveToAdapted,
          modularThetaSourcePositiveToAdaptedCoordinate,
          modularThetaSourcePositiveVacuumBoundaryState] <;>
        ring

theorem modularThetaSourcePositiveAdaptedBoundary_preserves_weight
    (i : ModularThetaSourcePositiveState) :
    (modularThetaSourcePositiveAdaptedBoundaryCoordinate i).IsWeightedHomogeneous
      modularThetaSourcePositiveAdaptedWeight
      (modularThetaSourcePositiveAdaptedWeight i) := by
  cases i
  · exact MvPolynomial.isWeightedHomogeneous_zero ℂ
      modularThetaSourcePositiveAdaptedWeight 1
  · simpa [modularThetaSourcePositiveAdaptedBoundaryCoordinate,
      modularThetaSourcePositiveAdaptedWeight] using
      (MvPolynomial.isWeightedHomogeneous_X ℂ
        modularThetaSourcePositiveAdaptedWeight
        ModularThetaSourcePositiveState.B)
  · exact MvPolynomial.isWeightedHomogeneous_zero ℂ
      modularThetaSourcePositiveAdaptedWeight 2

/-- Boundary restriction commutes with every adapted-weight projection. -/
theorem modularThetaSourcePositiveVacuumBoundaryEnd_adaptedComponent
    (W : ℕ) (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveVacuumBoundaryEnd
        (modularThetaSourcePositiveAdaptedComponent W P) =
      MvPolynomial.weightedHomogeneousComponent
        modularThetaSourcePositiveAdaptedWeight W
        (modularThetaSourcePositiveVacuumBoundaryEnd P) := by
  unfold modularThetaSourcePositiveVacuumBoundaryEnd
    modularThetaSourcePositiveAdaptedComponent
  have hto (R : ModularThetaSourcePositivePolynomial) :
      modularThetaSourcePositiveToAdapted
          (modularThetaSourcePositiveOfAdapted R) = R := by
    change (modularThetaSourcePositiveToAdapted.comp
      modularThetaSourcePositiveOfAdapted) R = R
    rw [modularThetaSourcePositiveToAdapted_comp_ofAdapted]
    rfl
  change modularThetaSourcePositiveAdaptedBoundary
      (modularThetaSourcePositiveToAdapted
        (modularThetaSourcePositiveOfAdapted
          (MvPolynomial.weightedHomogeneousComponent
            modularThetaSourcePositiveAdaptedWeight W
            (modularThetaSourcePositiveToAdapted P)))) =
    MvPolynomial.weightedHomogeneousComponent
      modularThetaSourcePositiveAdaptedWeight W
      (modularThetaSourcePositiveAdaptedBoundary
        (modularThetaSourcePositiveToAdapted P))
  rw [hto]
  change MvPolynomial.eval₂ MvPolynomial.C
      modularThetaSourcePositiveAdaptedBoundaryCoordinate
      (MvPolynomial.weightedHomogeneousComponent
        modularThetaSourcePositiveAdaptedWeight W
        (modularThetaSourcePositiveToAdapted P)) =
    MvPolynomial.weightedHomogeneousComponent
      modularThetaSourcePositiveAdaptedWeight W
      (MvPolynomial.eval₂ MvPolynomial.C
        modularThetaSourcePositiveAdaptedBoundaryCoordinate
        (modularThetaSourcePositiveToAdapted P))
  exact (GaloisForLFunctions.eval₂_weightedHomogeneousComponent
    modularThetaSourcePositiveAdaptedWeight
    modularThetaSourcePositiveAdaptedWeight
    modularThetaSourcePositiveAdaptedBoundaryCoordinate
    modularThetaSourcePositiveAdaptedBoundary_preserves_weight W
    (modularThetaSourcePositiveToAdapted P)).symm

/-- D1 has a strictly positive adapted-weight boundary component nonzero at `b=1`. -/
theorem exists_pos_modularThetaSourcePositiveReflectedEighth_boundary_component_eval_one :
    ∃ W : ℕ, 0 < W ∧
      MvPolynomial.eval
          (fun i => match i with
            | .U => 0
            | .B => 1
            | .Q => 0)
          (MvPolynomial.weightedHomogeneousComponent
            modularThetaSourcePositiveAdaptedWeight W
            (modularThetaSourcePositiveVacuumBoundaryEnd
              modularThetaSourcePositiveReflectedEighthPolynomial)) ≠ 0 := by
  let R := modularThetaSourcePositiveVacuumBoundaryEnd
    modularThetaSourcePositiveReflectedEighthPolynomial
  let o : ModularThetaSourcePositiveState → ℂ := fun i => match i with
    | .U => 0
    | .B => 1
    | .Q => 0
  let z : ModularThetaSourcePositiveState → ℂ := fun i => match i with
    | .U => 0
    | .B => 0
    | .Q => 0
  by_contra h
  push Not at h
  have hdecomp := GaloisForLFunctions.sum_weightedHomogeneousComponent_natRange
    modularThetaSourcePositiveAdaptedWeight R
  have hweight : ∀ i : ModularThetaSourcePositiveState,
      modularThetaSourcePositiveAdaptedWeight i ≠ 0 := by
    intro i
    cases i <;> simp [modularThetaSourcePositiveAdaptedWeight]
  have hone : MvPolynomial.eval o R = MvPolynomial.coeff 0 R := by
    calc
      MvPolynomial.eval o R = MvPolynomial.eval o
          (∑ W ∈ Finset.range
            (R.weightedTotalDegree modularThetaSourcePositiveAdaptedWeight + 1),
            MvPolynomial.weightedHomogeneousComponent
              modularThetaSourcePositiveAdaptedWeight W R) := by rw [hdecomp]
      _ = ∑ W ∈ Finset.range
            (R.weightedTotalDegree modularThetaSourcePositiveAdaptedWeight + 1),
            MvPolynomial.eval o
              (MvPolynomial.weightedHomogeneousComponent
                modularThetaSourcePositiveAdaptedWeight W R) := by simp
      _ = MvPolynomial.eval o
            (MvPolynomial.weightedHomogeneousComponent
              modularThetaSourcePositiveAdaptedWeight 0 R) := by
          apply Finset.sum_eq_single 0
          · intro W hW hW0
            simpa [o, R] using h W (Nat.pos_of_ne_zero hW0)
          · intro hzero
            exact (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim
      _ = MvPolynomial.coeff 0 R := by
          rw [MvPolynomial.weightedHomogeneousComponent_zero R hweight]
          simp
  apply eval_modularThetaSourcePositiveReflectedEighthPolynomial_vacuumBoundary_zero_ne_one
  rw [← eval_modularThetaSourcePositiveVacuumBoundaryEnd,
    ← eval_modularThetaSourcePositiveVacuumBoundaryEnd]
  have htarget : MvPolynomial.eval 0 R = MvPolynomial.eval o R := by
    rw [hone]
    simpa [MvPolynomial.constantCoeff] using congrFun MvPolynomial.eval_zero R
  have hz : z = (0 : ModularThetaSourcePositiveState → ℂ) := by
    funext i
    cases i <;> rfl
  have htarget' : MvPolynomial.eval z R = MvPolynomial.eval o R := by
    rw [hz]
    exact htarget
  simpa only [R, o, z] using htarget'

/-! ## Exact lowering and Cartan actions in adapted coordinates -/

theorem modularThetaSourcePositiveToAdapted_sl2F_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveToAdapted
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
          (MvPolynomial.X i)) =
      -MvPolynomial.pderiv .B
        (modularThetaSourcePositiveToAdapted (MvPolynomial.X i)) := by
  cases i <;>
    apply MvPolynomial.funext <;>
    intro v <;>
    simp [modularThetaSourcePositiveFieldLie_X,
      modularThetaSourcePositiveSl2F,
      modularThetaSourcePositiveLoweringField,
      modularThetaSourcePositiveToAdapted,
      modularThetaSourcePositiveToAdaptedCoordinate] <;>
    ring

/-- The exact source lowering operator is `-∂b` after the adapted automorphism. -/
theorem modularThetaSourcePositiveToAdapted_sl2F
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveToAdapted
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P) =
      -MvPolynomial.pderiv .B (modularThetaSourcePositiveToAdapted P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [modularThetaSourcePositiveFieldLie_C]
  | add P Q hP hQ =>
      rw [modularThetaSourcePositiveFieldLie_add, map_add, hP, hQ, map_add,
        map_add]
      abel
  | mul_X P i hP =>
      rw [modularThetaSourcePositiveFieldLie_mul, map_add, map_mul, map_mul,
        hP, modularThetaSourcePositiveToAdapted_sl2F_X, map_mul,
        MvPolynomial.pderiv_mul]
      ring

/-- Weighted Euler field in abstract `(r,b,k)` coordinates. -/
def modularThetaSourcePositiveAdaptedEuler
    (P : ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositivePolynomial :=
  ∑ i : ModularThetaSourcePositiveState,
    modularThetaSourcePositiveAdaptedWeight i •
      (MvPolynomial.X i * MvPolynomial.pderiv i P)

theorem modularThetaSourcePositiveAdaptedEuler_eq (P :
    ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveAdaptedEuler P =
      MvPolynomial.X .U * MvPolynomial.pderiv .U P +
      MvPolynomial.X .B * MvPolynomial.pderiv .B P +
      2 • (MvPolynomial.X .Q * MvPolynomial.pderiv .Q P) := by
  classical
  unfold modularThetaSourcePositiveAdaptedEuler
  rw [show (Finset.univ : Finset ModularThetaSourcePositiveState) =
      {.U, .B, .Q} by
        ext i
        cases i <;> simp]
  simp [modularThetaSourcePositiveAdaptedWeight]
  ring

theorem modularThetaSourcePositiveAdaptedEuler_add
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveAdaptedEuler (P + Q) =
      modularThetaSourcePositiveAdaptedEuler P +
        modularThetaSourcePositiveAdaptedEuler Q := by
  simp only [modularThetaSourcePositiveAdaptedEuler_eq, map_add,
    mul_add, nsmul_add]
  abel

theorem modularThetaSourcePositiveAdaptedEuler_mul
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveAdaptedEuler (P * Q) =
      modularThetaSourcePositiveAdaptedEuler P * Q +
        P * modularThetaSourcePositiveAdaptedEuler Q := by
  simp only [modularThetaSourcePositiveAdaptedEuler_eq,
    MvPolynomial.pderiv_mul, mul_add, nsmul_eq_mul]
  ring

theorem modularThetaSourcePositiveToAdapted_sl2H_X
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveToAdapted
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H
          (MvPolynomial.X i)) =
      (2 : ℂ) • modularThetaSourcePositiveAdaptedEuler
        (modularThetaSourcePositiveToAdapted (MvPolynomial.X i)) := by
  cases i <;>
    apply MvPolynomial.funext <;>
    intro v <;>
    simp [modularThetaSourcePositiveFieldLie_X,
      modularThetaSourcePositiveSl2H,
      modularThetaSourcePositiveScaleField,
      modularThetaSourcePositiveToAdapted,
      modularThetaSourcePositiveToAdaptedCoordinate,
      modularThetaSourcePositiveAdaptedEuler_eq] <;>
    ring

/-- The exact source Cartan action is twice the positive weighted Euler field. -/
theorem modularThetaSourcePositiveToAdapted_sl2H
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveToAdapted
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H P) =
      (2 : ℂ) • modularThetaSourcePositiveAdaptedEuler
        (modularThetaSourcePositiveToAdapted P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [modularThetaSourcePositiveFieldLie_C,
        modularThetaSourcePositiveAdaptedEuler]
  | add P Q hP hQ =>
      rw [modularThetaSourcePositiveFieldLie_add, map_add, hP, hQ, map_add]
      rw [modularThetaSourcePositiveAdaptedEuler_add]
      module
  | mul_X P i hP =>
      rw [modularThetaSourcePositiveFieldLie_mul, map_add, map_mul, map_mul,
        hP, modularThetaSourcePositiveToAdapted_sl2H_X, map_mul]
      rw [modularThetaSourcePositiveAdaptedEuler_mul]
      simp only [MvPolynomial.smul_eq_C_mul]
      ring

/-- Every adapted-weight-`W` polynomial is a Cartan eigenvector of weight `2W`. -/
theorem modularThetaSourcePositiveFieldLie_sl2H_of_adaptedHomogeneous
    {W : ℕ} {P : ModularThetaSourcePositivePolynomial}
    (hP : P.IsWeightedHomogeneous modularThetaSourcePositiveAdaptedWeight W) :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H
        (modularThetaSourcePositiveOfAdapted P) =
      ((2 * W : ℕ) : ℂ) • modularThetaSourcePositiveOfAdapted P := by
  apply modularThetaSourcePositiveToAdapted_injective
  rw [modularThetaSourcePositiveToAdapted_sl2H]
  have hto : modularThetaSourcePositiveToAdapted
      (modularThetaSourcePositiveOfAdapted P) = P := by
    change (modularThetaSourcePositiveToAdapted.comp
      modularThetaSourcePositiveOfAdapted) P = P
    rw [modularThetaSourcePositiveToAdapted_comp_ofAdapted]
    rfl
  rw [hto]
  unfold modularThetaSourcePositiveAdaptedEuler
  rw [hP.sum_weight_X_mul_pderiv]
  have hmap : modularThetaSourcePositiveToAdapted
      (((2 * W : ℕ) : ℂ) • modularThetaSourcePositiveOfAdapted P) =
      (((2 * W : ℕ) : ℂ) • P) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul,
      modularThetaSourcePositiveToAdapted_C, hto]
  rw [hmap]
  apply MvPolynomial.funext
  intro v
  simp
  ring

/-- Iterated lowering in abstract adapted coordinates. -/
def modularThetaSourcePositiveAdaptedLowerIterate :
    ℕ → ModularThetaSourcePositivePolynomial →
      ModularThetaSourcePositivePolynomial
  | 0, P => P
  | n + 1, P => -MvPolynomial.pderiv .B
      (modularThetaSourcePositiveAdaptedLowerIterate n P)

/-- Iterated exact source lowering. -/
def modularThetaSourcePositiveSl2FIterate :
    ℕ → ModularThetaSourcePositivePolynomial →
      ModularThetaSourcePositivePolynomial
  | 0, P => P
  | n + 1, P =>
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
        (modularThetaSourcePositiveSl2FIterate n P)

theorem modularThetaSourcePositiveToAdapted_sl2FIterate
    (n : ℕ) (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveToAdapted
        (modularThetaSourcePositiveSl2FIterate n P) =
      modularThetaSourcePositiveAdaptedLowerIterate n
        (modularThetaSourcePositiveToAdapted P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [modularThetaSourcePositiveSl2FIterate,
        modularThetaSourcePositiveAdaptedLowerIterate,
        modularThetaSourcePositiveToAdapted_sl2F, ih]

theorem modularThetaSourcePositiveAdaptedLowerIterate_isWeightedHomogeneous
    {n W : ℕ} {P : ModularThetaSourcePositivePolynomial}
    (hP : P.IsWeightedHomogeneous modularThetaSourcePositiveAdaptedWeight W)
    (hn : n ≤ W) :
    (modularThetaSourcePositiveAdaptedLowerIterate n P).IsWeightedHomogeneous
      modularThetaSourcePositiveAdaptedWeight (W - n) := by
  induction n with
  | zero =>
      change P.IsWeightedHomogeneous modularThetaSourcePositiveAdaptedWeight W
      exact hP
  | succ n ih =>
      have hn' : n ≤ W := le_trans (Nat.le_succ n) hn
      have hprev := ih hn'
      have hweight : (W - (n + 1)) +
          modularThetaSourcePositiveAdaptedWeight .B = W - n := by
        simp [modularThetaSourcePositiveAdaptedWeight]
        omega
      have hd := hprev.pderiv hweight
      simpa [modularThetaSourcePositiveAdaptedLowerIterate,
        MvPolynomial.smul_eq_C_mul] using hd.C_mul (-1 : ℂ)

theorem eval_one_pderiv_B_of_isWeightedHomogeneous
    {W : ℕ} {P : ModularThetaSourcePositivePolynomial}
    (hP : P.IsWeightedHomogeneous modularThetaSourcePositiveAdaptedWeight W) :
    MvPolynomial.eval
        (fun i => match i with
          | .U => 0
          | .B => 1
          | .Q => 0)
        (MvPolynomial.pderiv .B P) =
      (W : ℂ) * MvPolynomial.eval
        (fun i => match i with
          | .U => 0
          | .B => 1
          | .Q => 0) P := by
  have hEuler := hP.sum_weight_X_mul_pderiv
  change modularThetaSourcePositiveAdaptedEuler P = W • P at hEuler
  rw [modularThetaSourcePositiveAdaptedEuler_eq] at hEuler
  have h := congrArg (MvPolynomial.eval
    (fun i => match i with
      | .U => 0
      | .B => 1
      | .Q => 0)) hEuler
  simpa [nsmul_eq_mul] using h

theorem eval_one_adaptedLowerIterate_ne_zero
    {n W : ℕ} {P : ModularThetaSourcePositivePolynomial}
    (hP : P.IsWeightedHomogeneous modularThetaSourcePositiveAdaptedWeight W)
    (hn : n ≤ W)
    (hPone : MvPolynomial.eval
      (fun i => match i with
        | .U => 0
        | .B => 1
        | .Q => 0) P ≠ 0) :
    MvPolynomial.eval
      (fun i => match i with
        | .U => 0
        | .B => 1
        | .Q => 0)
      (modularThetaSourcePositiveAdaptedLowerIterate n P) ≠ 0 := by
  induction n with
  | zero =>
      change MvPolynomial.eval _ P ≠ 0
      exact hPone
  | succ n ih =>
      have hn' : n ≤ W := le_trans (Nat.le_succ n) hn
      have hprev :=
        modularThetaSourcePositiveAdaptedLowerIterate_isWeightedHomogeneous hP hn'
      have hprevone := ih hn'
      rw [modularThetaSourcePositiveAdaptedLowerIterate]
      simp only [map_neg]
      rw [eval_one_pderiv_B_of_isWeightedHomogeneous hprev]
      apply neg_ne_zero.mpr
      apply mul_ne_zero
      · exact_mod_cast (show W - n ≠ 0 by omega)
      · exact hprevone

theorem modularThetaSourcePositiveAdaptedLowerIterate_eq_C_of_weight
    {W : ℕ} {P : ModularThetaSourcePositivePolynomial}
    (hP : P.IsWeightedHomogeneous modularThetaSourcePositiveAdaptedWeight W) :
    ∃ a : ℂ,
      modularThetaSourcePositiveAdaptedLowerIterate W P = MvPolynomial.C a := by
  have hzero :=
    modularThetaSourcePositiveAdaptedLowerIterate_isWeightedHomogeneous hP le_rfl
  simp only [Nat.sub_self] at hzero
  have hcomponent := MvPolynomial.weightedHomogeneousComponent_of_mem
    (m := 0) hzero
  have hweight : ∀ i : ModularThetaSourcePositiveState,
      modularThetaSourcePositiveAdaptedWeight i ≠ 0 := by
    intro i
    cases i <;> simp [modularThetaSourcePositiveAdaptedWeight]
  rw [MvPolynomial.weightedHomogeneousComponent_zero _ hweight] at hcomponent
  exact ⟨_, hcomponent.symm⟩

theorem eval_one_modularThetaSourcePositiveAdaptedBoundary
    (P : ModularThetaSourcePositivePolynomial) :
    MvPolynomial.eval
        (fun i => match i with
          | .U => 0
          | .B => 1
          | .Q => 0)
        (modularThetaSourcePositiveAdaptedBoundary P) =
      MvPolynomial.eval
        (fun i => match i with
          | .U => 0
          | .B => 1
          | .Q => 0) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [modularThetaSourcePositiveAdaptedBoundary]
  | add P Q hP hQ =>
      simp only [map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, map_mul, hP]
      apply congrArg (fun z : ℂ =>
        MvPolynomial.eval
          (fun i => match i with
            | .U => 0
            | .B => 1
            | .Q => 0) P * z)
      cases i <;>
        simp [modularThetaSourcePositiveAdaptedBoundary,
          modularThetaSourcePositiveAdaptedBoundaryCoordinate]

theorem eval_one_modularThetaSourcePositiveVacuumBoundaryEnd_ofAdapted
    (P : ModularThetaSourcePositivePolynomial) :
    MvPolynomial.eval
        (fun i => match i with
          | .U => 0
          | .B => 1
          | .Q => 0)
        (modularThetaSourcePositiveVacuumBoundaryEnd
          (modularThetaSourcePositiveOfAdapted P)) =
      MvPolynomial.eval
        (fun i => match i with
          | .U => 0
          | .B => 1
          | .Q => 0) P := by
  have hto : modularThetaSourcePositiveToAdapted
      (modularThetaSourcePositiveOfAdapted P) = P := by
    change (modularThetaSourcePositiveToAdapted.comp
      modularThetaSourcePositiveOfAdapted) P = P
    rw [modularThetaSourcePositiveToAdapted_comp_ofAdapted]
    rfl
  unfold modularThetaSourcePositiveVacuumBoundaryEnd
  change MvPolynomial.eval _
      (modularThetaSourcePositiveAdaptedBoundary
        (modularThetaSourcePositiveToAdapted
          (modularThetaSourcePositiveOfAdapted P))) = _
  rw [hto]
  exact eval_one_modularThetaSourcePositiveAdaptedBoundary P

theorem modularThetaSourcePositiveFieldLie_sl2F_ofAdapted
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
        (modularThetaSourcePositiveOfAdapted P) =
      modularThetaSourcePositiveOfAdapted
        (-MvPolynomial.pderiv .B P) := by
  apply modularThetaSourcePositiveToAdapted_injective
  rw [modularThetaSourcePositiveToAdapted_sl2F]
  have hto (Q : ModularThetaSourcePositivePolynomial) :
      modularThetaSourcePositiveToAdapted
          (modularThetaSourcePositiveOfAdapted Q) = Q := by
    change (modularThetaSourcePositiveToAdapted.comp
      modularThetaSourcePositiveOfAdapted) Q = Q
    rw [modularThetaSourcePositiveToAdapted_comp_ofAdapted]
    rfl
  rw [hto, hto]

theorem modularThetaSourcePositiveFieldLie_sl2E_C (a : ℂ) :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
      (MvPolynomial.C a) = 0 := by
  exact modularThetaSourcePositiveFieldLie_C _ _

theorem modularThetaSourcePositiveToAdapted_adaptedComponent
    (W : ℕ) (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveToAdapted
        (modularThetaSourcePositiveAdaptedComponent W P) =
      MvPolynomial.weightedHomogeneousComponent
        modularThetaSourcePositiveAdaptedWeight W
        (modularThetaSourcePositiveToAdapted P) := by
  unfold modularThetaSourcePositiveAdaptedComponent
  change (modularThetaSourcePositiveToAdapted.comp
    modularThetaSourcePositiveOfAdapted) _ = _
  rw [modularThetaSourcePositiveToAdapted_comp_ofAdapted]
  rfl

/-- D1 itself generates a nonzero affine-vacuum `sl₂` string. -/
theorem exists_modularThetaSourcePositiveReflectedEighth_vacuumString :
    ∃ (n : ℕ) (v u : ModularThetaSourcePositivePolynomial),
      v = modularThetaSourcePositiveSl2FIterate n
        (modularThetaSourcePositiveAdaptedComponent (n + 1)
          modularThetaSourcePositiveReflectedEighthPolynomial) ∧
      u = modularThetaSourcePositiveSl2FIterate (n + 1)
        (modularThetaSourcePositiveAdaptedComponent (n + 1)
          modularThetaSourcePositiveReflectedEighthPolynomial) ∧
      u ≠ 0 ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F v = u ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E u = 0 ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H v =
        (2 : ℂ) • v ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ≠ 0 := by
  rcases
      exists_pos_modularThetaSourcePositiveReflectedEighth_boundary_component_eval_one with
    ⟨W, hW, hWone⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hW)
  let A := MvPolynomial.weightedHomogeneousComponent
    modularThetaSourcePositiveAdaptedWeight (n + 1)
    (modularThetaSourcePositiveToAdapted
      modularThetaSourcePositiveReflectedEighthPolynomial)
  let vA := modularThetaSourcePositiveAdaptedLowerIterate n A
  let uA := modularThetaSourcePositiveAdaptedLowerIterate (n + 1) A
  let v := modularThetaSourcePositiveOfAdapted vA
  let u := modularThetaSourcePositiveOfAdapted uA
  have hA : A.IsWeightedHomogeneous
      modularThetaSourcePositiveAdaptedWeight (n + 1) :=
    MvPolynomial.weightedHomogeneousComponent_mem _ _ _
  have hAone : MvPolynomial.eval
      (fun i => match i with
        | .U => 0
        | .B => 1
        | .Q => 0) A ≠ 0 := by
    have hcomm := congrArg
      (MvPolynomial.eval (fun i => match i with
        | .U => 0
        | .B => 1
        | .Q => 0))
      (modularThetaSourcePositiveVacuumBoundaryEnd_adaptedComponent
        (n + 1) modularThetaSourcePositiveReflectedEighthPolynomial)
    change MvPolynomial.eval _
      (modularThetaSourcePositiveVacuumBoundaryEnd
        (modularThetaSourcePositiveOfAdapted A)) = _ at hcomm
    rw [eval_one_modularThetaSourcePositiveVacuumBoundaryEnd_ofAdapted] at hcomm
    intro hzero
    apply hWone
    rw [← hcomm, hzero]
  have hvAhom : vA.IsWeightedHomogeneous
      modularThetaSourcePositiveAdaptedWeight 1 := by
    have h := modularThetaSourcePositiveAdaptedLowerIterate_isWeightedHomogeneous
      hA (show n ≤ n + 1 by omega)
    simpa [vA] using h
  have huAone : MvPolynomial.eval
      (fun i => match i with
        | .U => 0
        | .B => 1
        | .Q => 0) uA ≠ 0 := by
    exact eval_one_adaptedLowerIterate_ne_zero hA le_rfl hAone
  obtain ⟨a, huAC⟩ :=
    modularThetaSourcePositiveAdaptedLowerIterate_eq_C_of_weight hA
  have ha : a ≠ 0 := by
    intro ha
    apply huAone
    change MvPolynomial.eval _
      (modularThetaSourcePositiveAdaptedLowerIterate (n + 1) A) = 0
    rw [huAC, ha]
    simp
  have huC : u = MvPolynomial.C a := by
    simp [u, uA, huAC]
  have hu : u ≠ 0 := by
    rw [huC]
    exact MvPolynomial.C_ne_zero.mpr ha
  have hFv : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F v = u := by
    rw [show v = modularThetaSourcePositiveOfAdapted vA by rfl,
      modularThetaSourcePositiveFieldLie_sl2F_ofAdapted]
    rfl
  have hEu : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E u = 0 := by
    rw [huC]
    exact modularThetaSourcePositiveFieldLie_sl2E_C a
  have hHv : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H v =
      (2 : ℂ) • v := by
    simpa [v] using
      modularThetaSourcePositiveFieldLie_sl2H_of_adaptedHomogeneous hvAhom
  have hv : v ≠ 0 := by
    intro hvzero
    apply hu
    rw [← hFv, hvzero]
    simp [modularThetaSourcePositiveFieldLie]
  have hEv : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ≠ 0 := by
    intro hzero
    have hbracket := modularThetaSourcePositiveFieldLie_sl2_ef v
    rw [hFv, hEu, hzero, hHv] at hbracket
    have hz : (2 : ℂ) • v = 0 := by
      simpa [modularThetaSourcePositiveFieldLie] using hbracket.symm
    exact hv ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  have hvgen : v = modularThetaSourcePositiveSl2FIterate n
      (modularThetaSourcePositiveAdaptedComponent (n + 1)
        modularThetaSourcePositiveReflectedEighthPolynomial) := by
    apply modularThetaSourcePositiveToAdapted_injective
    rw [modularThetaSourcePositiveToAdapted_sl2FIterate,
      modularThetaSourcePositiveToAdapted_adaptedComponent]
    change modularThetaSourcePositiveToAdapted v = vA
    change modularThetaSourcePositiveToAdapted
      (modularThetaSourcePositiveOfAdapted vA) = vA
    change (modularThetaSourcePositiveToAdapted.comp
      modularThetaSourcePositiveOfAdapted) vA = vA
    rw [modularThetaSourcePositiveToAdapted_comp_ofAdapted]
    rfl
  have hugen : u = modularThetaSourcePositiveSl2FIterate (n + 1)
      (modularThetaSourcePositiveAdaptedComponent (n + 1)
        modularThetaSourcePositiveReflectedEighthPolynomial) := by
    apply modularThetaSourcePositiveToAdapted_injective
    rw [modularThetaSourcePositiveToAdapted_sl2FIterate,
      modularThetaSourcePositiveToAdapted_adaptedComponent]
    change modularThetaSourcePositiveToAdapted u = uA
    change modularThetaSourcePositiveToAdapted
      (modularThetaSourcePositiveOfAdapted uA) = uA
    change (modularThetaSourcePositiveToAdapted.comp
      modularThetaSourcePositiveOfAdapted) uA = uA
    rw [modularThetaSourcePositiveToAdapted_comp_ofAdapted]
    rfl
  exact ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, hHv, hEv⟩

/-- Positive scalar-contravariant data on a graded source carrier containing actual D1. -/
structure ModularThetaSourcePositiveD1GradedScalarContravariantCarrier
    (c : ℝ) where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  adaptedComponent_mem : ∀ (W : ℕ) (P : ModularThetaSourcePositivePolynomial),
    P ∈ carrier → modularThetaSourcePositiveAdaptedComponent W P ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → ℂ
  smul_left : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair (a • p) q = star a * pair p q
  smul_right : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair p (a • q) = a * pair p q
  positive : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → 0 < (pair p p).re
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        pair p ((c : ℂ) •
          modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q)

theorem ModularThetaSourcePositiveD1GradedScalarContravariantCarrier.sl2FIterate_mem
    {c : ℝ} (B : ModularThetaSourcePositiveD1GradedScalarContravariantCarrier c)
    (n : ℕ) {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ B.carrier) :
    modularThetaSourcePositiveSl2FIterate n P ∈ B.carrier := by
  induction n with
  | zero => exact hP
  | succ n ih =>
      exact B.sl2F_mem _ ih

/-- **D1 cyclic scalar-form no-go.** No positive scalar-contravariant form exists on any
adapted-graded source `sl₂` carrier containing the actual rank-three D1 polynomial. -/
theorem modularThetaSourcePositive_no_D1_gradedScalarContravariantCarrier :
    ¬ ∃ (c : ℝ), Nonempty
      (ModularThetaSourcePositiveD1GradedScalarContravariantCarrier c) := by
  rintro ⟨c, ⟨B⟩⟩
  rcases exists_modularThetaSourcePositiveReflectedEighth_vacuumString with
    ⟨n, v, u, hvgen, hugen, hu, hFv, hEu, hHv, hEv⟩
  have hcomponent : modularThetaSourcePositiveAdaptedComponent (n + 1)
      modularThetaSourcePositiveReflectedEighthPolynomial ∈ B.carrier :=
    B.adaptedComponent_mem _ _ B.d1_mem
  have hvMem : v ∈ B.carrier := by
    rw [hvgen]
    exact B.sl2FIterate_mem n hcomponent
  have huMem : u ∈ B.carrier := by
    rw [hugen]
    exact B.sl2FIterate_mem (n + 1) hcomponent
  have hEvMem : modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v ∈
      B.carrier := B.sl2E_mem v hvMem
  have hcontra := B.contravariant u v huMem hvMem
  rw [hEu, hFv] at hcontra
  have hleft := B.smul_left (0 : ℂ) u v
  have hleftzero : B.pair 0 v = 0 := by
    simpa using hleft
  have hright := B.smul_right (c : ℂ) u u
  rw [hleftzero, hright] at hcontra
  have hre := congrArg Complex.re hcontra
  have hpos := B.positive u huMem hu
  simp at hre
  have hc : c = 0 := by
    rcases hre with hc | hp
    · exact hc
    · exfalso
      linarith
  have hcontraEv := B.contravariant v
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hvMem hEvMem
  have hcC : (c : ℂ) = 0 := by exact_mod_cast hc
  rw [hcC] at hcontraEv
  have hzeroRight := B.smul_right (0 : ℂ) v
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v))
  have hzeroRight' : B.pair v
      ((0 : ℂ) • modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)) = 0 := by
    simpa using hzeroRight
  rw [hzeroRight'] at hcontraEv
  have hreEv := congrArg Complex.re hcontraEv
  have hposEv := B.positive
    (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E v)
    hEvMem hEv
  simp at hreEv
  linarith

end

end HTGeometry
