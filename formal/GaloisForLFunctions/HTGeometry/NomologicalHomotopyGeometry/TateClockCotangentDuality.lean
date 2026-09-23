import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicCotangentNoether

/-!
# Tate-clock Ind/Pro duality is cotangent duality

The algebraic dual of finitely supported `k`-valued coordinates is canonically the space of all
`k`-valued coordinate functions.  Under this equivalence, evaluation is the existing restricted
Ind/Pro Tate-clock pairing, and the dual of the Ind forward shift is the Pro backward shift.

This identifies two independently developed corpus structures.  It also records a topology
warning: the Pro half is the full algebraic dual, not the continuous dual of an `ell^(2 : ℕ)` completion.
Full-support boundary defects can therefore survive here even when every continuous Hausdorff
quotient killing the dense Ind core collapses.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.TateClockCotangentDuality

open GaloisForLFunctions.HTGeometry
open CyclicCotangentNoether

noncomputable section

universe u v

variable {k : Type u} [Field k]
variable {ι : Type v}

/-- Algebraic dual of a free direct sum, written as its unrestricted Pro coordinate space. -/
def finsuppDualEquivPi : Module.Dual k (ι →₀ k) ≃ₗ[k] (ι → k) :=
  (Finsupp.lsum k).symm.trans
    (LinearEquiv.piCongrRight fun _ => LinearMap.ringLmapEquivSelf k k k)

@[simp] theorem finsuppDualEquivPi_apply
    (phi : Module.Dual k (ι →₀ k)) (i : ι) :
    finsuppDualEquivPi phi i = phi (Finsupp.single i 1) :=
  rfl

@[simp] theorem finsuppDualEquivPi_symm_apply
    (p : ι → k) (a : ι →₀ k) :
    (finsuppDualEquivPi.symm p) a =
      a.sum (fun i c => c * p i) := by
  simp [finsuppDualEquivPi, Finsupp.lsum_apply,
    LinearMap.ringLmapEquivSelf]

/-! ## The countable Tate-clock specialization -/

/-- Ind/Pro presentation of the cotangent double of the countable free source. -/
abbrev TateClockCotangentFields (k : Type u) [Field k] :=
  (ℕ →₀ k) × (ℕ → k)

/-- Cotangent fields are exactly the Ind/Pro Tate-clock pair. -/
def tateClockCotangentEquiv :
    CotangentFields k (ℕ →₀ k) ≃ₗ[k] TateClockCotangentFields k :=
  LinearEquiv.prodCongr (LinearEquiv.refl k (ℕ →₀ k)) finsuppDualEquivPi

@[simp] theorem tateClockCotangentEquiv_apply
    (x : CotangentFields k (ℕ →₀ k)) :
    tateClockCotangentEquiv x = (x.1, finsuppDualEquivPi x.2) :=
  rfl

/-- Under Ind/Pro coordinates, the canonical cotangent pairing is the sum of the two restricted
Tate-clock evaluations. -/
theorem cotangentPairing_eq_tateClockPairing
    (x y : CotangentFields k (ℕ →₀ k)) :
    cotangentPairing x y =
      tateClockPairing y.1 (finsuppDualEquivPi x.2) +
        tateClockPairing x.1 (finsuppDualEquivPi y.2) := by
  rw [cotangentPairing_apply]
  congr 1
  · have h := congrArg (fun phi : Module.Dual k (ℕ →₀ k) => phi y.1)
      (finsuppDualEquivPi.symm_apply_apply x.2)
    rw [finsuppDualEquivPi_symm_apply] at h
    simpa [tateClockPairing] using h.symm
  · have h := congrArg (fun phi : Module.Dual k (ℕ →₀ k) => phi x.1)
      (finsuppDualEquivPi.symm_apply_apply y.2)
    rw [finsuppDualEquivPi_symm_apply] at h
    simpa [tateClockPairing] using h.symm

/-- Linear Ind forward shift. -/
def tateClockIndForwardLinear : Module.End k (ℕ →₀ k) where
  toFun := tateClockIndForward
  map_add' a b := by
    ext n
    cases n <;> simp [tateClockIndForward_apply_zero,
      tateClockIndForward_apply_succ]
  map_smul' c a := by
    ext n
    cases n <;> simp [tateClockIndForward_apply_zero,
      tateClockIndForward_apply_succ]

@[simp] theorem tateClockIndForwardLinear_apply (a : ℕ →₀ k) :
    tateClockIndForwardLinear a = tateClockIndForward a :=
  rfl

/-- Linear Pro backward shift. -/
def tateClockProBackwardLinear : Module.End k (ℕ → k) where
  toFun := tateClockProBackward
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem tateClockProBackwardLinear_apply (p : ℕ → k) :
    tateClockProBackwardLinear p = tateClockProBackward p :=
  rfl

/-- The cotangent-dual differential of the Ind forward clock is literally the Pro backward clock. -/
theorem finsuppDualEquivPi_dualDifferential_forward
    (phi : Module.Dual k (ℕ →₀ k)) :
    finsuppDualEquivPi
        (dualDifferential (tateClockIndForwardLinear (k := k)) phi) =
      tateClockProBackwardLinear (finsuppDualEquivPi phi) := by
  funext n
  change phi (tateClockIndForward (Finsupp.single n 1)) =
    phi (Finsupp.single (n + 1) 1)
  congr
  ext m
  cases m with
  | zero => simp [tateClockIndForward_apply_zero]
  | succ m =>
      simp [tateClockIndForward_apply_succ, Finsupp.single_apply]

end

end HTGeometry.NomologicalHomotopyGeometry.TateClockCotangentDuality
