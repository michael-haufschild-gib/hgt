import GaloisForLFunctions.HTGeometry.BRSTHodgeConstraint
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Conservative parity suspension and Hodge positivity

Every module endomorphism has a canonical faithful square-zero realization on its parity double.
An anticommuting symmetry becomes a commuting chain symmetry after the odd parity sign is included.
For bounded Hilbert realizations, the BRST--Hodge anticommutator is positive, self-adjoint, and
vanishes exactly when the original current vanishes.

This is the mechanism by which nilpotent conormal information can survive positivity: the current
is odd, while positivity is formed one categorical level later from its Hodge Hamiltonian.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Faithful odd suspension of a linear current to the parity double. -/
def paritySuspensionCharge (J : Module.End R M) : Module.End R (M × M) where
  toFun p := (0, J p.1)
  map_add' p q := by simp
  map_smul' c p := by simp

@[simp]
theorem paritySuspensionCharge_apply (J : Module.End R M) (p : M × M) :
    paritySuspensionCharge J p = (0, J p.1) :=
  rfl

/-- Parity suspension turns every current into a square-zero differential. -/
theorem paritySuspensionCharge_sq (J : Module.End R M) :
    paritySuspensionCharge J * paritySuspensionCharge J = 0 := by
  ext p <;> simp [paritySuspensionCharge, Module.End.mul_apply]

/-- The square-zero completion is conservative: it vanishes exactly with the input current. -/
theorem paritySuspensionCharge_eq_zero_iff (J : Module.End R M) :
    paritySuspensionCharge J = 0 ↔ J = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun h (x, 0)
    have hx2 := congrArg Prod.snd hx
    simpa using hx2
  · rintro rfl
    apply LinearMap.ext
    intro p
    simp [paritySuspensionCharge]

/-- Closed states retain the kernel of the original current and the full odd summand. -/
theorem paritySuspensionCharge_ker (J : Module.End R M) :
    LinearMap.ker (paritySuspensionCharge J) =
      (LinearMap.ker J).prod (⊤ : Submodule R M) := by
  ext p
  constructor
  · intro hp
    exact ⟨congrArg Prod.snd hp, trivial⟩
  · rintro ⟨hp, -⟩
    exact Prod.ext rfl hp

/-- Exact states are precisely the odd copy of the original current range. -/
theorem paritySuspensionCharge_range (J : Module.End R M) :
    LinearMap.range (paritySuspensionCharge J) =
      (⊥ : Submodule R M).prod (LinearMap.range J) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨rfl, ⟨q.1, rfl⟩⟩
  · rintro ⟨hp1, ⟨x, hx⟩⟩
    refine ⟨(x, 0), ?_⟩
    exact Prod.ext hp1.symm hx

/-- Parity-corrected lift of a source action. -/
def paritySuspensionEvenLift (tau : M → M) (p : M × M) : M × M :=
  (tau p.1, -tau p.2)

/-- Unsigned diagonal lift of a source action. -/
def paritySuspensionDiagonalLift (tau : M → M) (p : M × M) : M × M :=
  (tau p.1, tau p.2)

/-- An odd external action becomes an internal chain symmetry after parity correction. -/
theorem paritySuspensionCharge_evenLift
    (J : Module.End R M) (tau : M → M)
    (hodd : ∀ x, J (tau x) = -tau (J x)) (hzero : tau 0 = 0) (p : M × M) :
    paritySuspensionCharge J (paritySuspensionEvenLift tau p) =
      paritySuspensionEvenLift tau (paritySuspensionCharge J p) := by
  simp [paritySuspensionCharge, paritySuspensionEvenLift, hodd, hzero]

/-- Without the parity sign, the same lifted action still anticommutes with the charge. -/
theorem paritySuspensionCharge_diagonalLift
    (J : Module.End R M) (tau : M → M)
    (hodd : ∀ x, J (tau x) = -tau (J x)) (hzero : tau 0 = 0) (p : M × M) :
    paritySuspensionCharge J (paritySuspensionDiagonalLift tau p) =
      -paritySuspensionDiagonalLift tau (paritySuspensionCharge J p) := by
  simp [paritySuspensionCharge, paritySuspensionDiagonalLift, hodd, hzero]

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Hilbert `ℓ²` parity double. -/
abbrev HilbertParityDouble := WithLp 2 (E × E)

/-- Bounded parity suspension of a bounded Hilbert current. -/
def hilbertParitySuspensionCharge (J : E →L[𝕜] E) :
    HilbertParityDouble (E := E) →L[𝕜] HilbertParityDouble (E := E) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr 𝕜 E E).comp
      (J.comp (WithLp.fstL 2 𝕜 E E)))

@[simp]
theorem hilbertParitySuspensionCharge_apply (J : E →L[𝕜] E)
    (p : HilbertParityDouble (E := E)) :
    WithLp.equiv 2 (E × E) (hilbertParitySuspensionCharge J p) =
      (0, J (WithLp.equiv 2 (E × E) p).1) :=
  rfl

/-- The bounded parity charge is square-zero. -/
theorem hilbertParitySuspensionCharge_sq (J : E →L[𝕜] E) :
    hilbertParitySuspensionCharge J * hilbertParitySuspensionCharge J = 0 := by
  apply ContinuousLinearMap.ext
  intro p
  apply (WithLp.equiv 2 (E × E)).injective
  simp [hilbertParitySuspensionCharge]

/-- Bounded parity suspension remains conservative. -/
theorem hilbertParitySuspensionCharge_eq_zero_iff (J : E →L[𝕜] E) :
    hilbertParitySuspensionCharge J = 0 ↔ J = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    let p : HilbertParityDouble (E := E) :=
      (WithLp.equiv 2 (E × E)).symm (x, 0)
    have hx := congrArg (fun T => T p) h
    have hx2 := congrArg (fun q => (WithLp.equiv 2 (E × E) q).2) hx
    simpa [p, hilbertParitySuspensionCharge] using hx2
  · rintro rfl
    apply ContinuousLinearMap.ext
    intro p
    apply (WithLp.equiv 2 (E × E)).injective
    simp [hilbertParitySuspensionCharge]

section Complete

variable [CompleteSpace E]

/-- Positive Hodge observer formed from the suspended current. -/
def paritySuspensionHodgeHamiltonian (J : E →L[𝕜] E) :
    HilbertParityDouble (E := E) →L[𝕜] HilbertParityDouble (E := E) :=
  _root_.HTGeometry.brstHodgeHamiltonian (hilbertParitySuspensionCharge J)

/-- Hodge positivity is conservative: zero energy operator means zero original current. -/
theorem paritySuspensionHodgeHamiltonian_eq_zero_iff (J : E →L[𝕜] E) :
    paritySuspensionHodgeHamiltonian J = 0 ↔ J = 0 := by
  constructor
  · intro hH
    apply (hilbertParitySuspensionCharge_eq_zero_iff J).mp
    apply ContinuousLinearMap.ext
    intro p
    have hHp := congrArg (fun T => T p) hH
    have hQp := (_root_.HTGeometry.brstHodgeHamiltonian_apply_eq_zero_iff
      (hilbertParitySuspensionCharge J) p).mp (by simpa
        [paritySuspensionHodgeHamiltonian] using hHp) |>.1
    simpa using hQp
  · intro hJ
    rw [hJ]
    simp [paritySuspensionHodgeHamiltonian,
      _root_.HTGeometry.brstHodgeHamiltonian,
      _root_.HTGeometry.quantumMasterConstraint,
      hilbertParitySuspensionCharge]

/-- A bounded current survives positivity exactly when it was nonzero before Hodge formation. -/
theorem paritySuspensionHodgeHamiltonian_ne_zero_iff (J : E →L[𝕜] E) :
    paritySuspensionHodgeHamiltonian J ≠ 0 ↔ J ≠ 0 :=
  not_congr (paritySuspensionHodgeHamiltonian_eq_zero_iff J)

/-- Hodge observer is automatically self-adjoint. -/
theorem paritySuspensionHodgeHamiltonian_isSelfAdjoint (J : E →L[𝕜] E) :
    IsSelfAdjoint (paritySuspensionHodgeHamiltonian J) :=
  _root_.HTGeometry.brstHodgeHamiltonian_isSelfAdjoint
    (hilbertParitySuspensionCharge J)

/-- Exact positive energy reconstruction from closed and coclosed residuals. -/
theorem re_inner_paritySuspensionHodgeHamiltonian_eq_sum_normSq
    (J : E →L[𝕜] E) (psi : HilbertParityDouble (E := E)) :
    RCLike.re (inner 𝕜 psi (paritySuspensionHodgeHamiltonian J psi)) =
      ‖hilbertParitySuspensionCharge J psi‖ ^ (2 : ℕ) +
        ‖(hilbertParitySuspensionCharge J).adjoint psi‖ ^ (2 : ℕ) :=
  _root_.HTGeometry.re_inner_brstHodgeHamiltonian_eq_sum_normSq
    (hilbertParitySuspensionCharge J) psi

/-- Positivity of the Hodge observer is automatic. -/
theorem re_inner_paritySuspensionHodgeHamiltonian_nonneg
    (J : E →L[𝕜] E) (psi : HilbertParityDouble (E := E)) :
    0 ≤ RCLike.re (inner 𝕜 psi (paritySuspensionHodgeHamiltonian J psi)) :=
  _root_.HTGeometry.re_inner_brstHodgeHamiltonian_nonneg
    (hilbertParitySuspensionCharge J) psi

end Complete

end Hilbert

end

end GaloisForLFunctions.HTGeometry
