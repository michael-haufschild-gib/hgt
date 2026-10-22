import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel

/-!
# PW-B operator-level full/native anomaly law

The preceding modewise and finite spectral no-gos are shadows of one identity
which needs no spectral decomposition. For any additive current map, full
source contact equals the first-row operator-intertwining anomaly minus its
complex-linearity defect, divided by the nonzero physical coupling. In
particular, a complex-linear adjoint-compatible current has zero full source
contact even if it mixes modes nonlocally.

This is an algebraic operator-domain theorem. Applying it to the actual
non-`L²` cusp field requires a source-faithful domain and boundary trace;
no current incidence, extinction, or RH claim is made here.
-/

namespace RHTower.D4BMPWOperatorAnomaly

noncomputable section
set_option autoImplicit false

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Triangular full/native action, with arbitrary native operator `D`. -/
def triangularAction (lam : ℂ) (D : E → E) (p : E × E) : E × E :=
  (lam • (p.1 + p.2), D p.2)

/-- Algebraic transpose action, requiring no inner-product choice. -/
def transposeAction (lam : ℂ) (D : E → E) (p : E × E) : E × E :=
  (lam • p.1, lam • p.1 + D p.2)

/-- First-row failure of adjoint intertwining at the single native probe. -/
def firstRowAnomaly (lam : ℂ) (D : E → E)
    (S : (E × E) →ₗ[ℂ] (E × E)) (H : E) : E :=
  (S (triangularAction lam D (0,H))).1 -
    (transposeAction lam D (S (0,H))).1

/-- The full source contact is exactly the first-row anomaly, without any
modewise or locality assumption. -/
theorem firstRowAnomaly_eq_fullSourceReadout
    (lam : ℂ) (D : E → E) (S : (E × E) →ₗ[ℂ] (E × E))
    (H Q : E) (hsource : D H = lam • (H + Q)) :
    firstRowAnomaly lam D S H = lam • (S (H,Q)).1 := by
  have hdecomp : triangularAction lam D (0,H) =
      lam • ((H,Q) + (0,H)) := by
    apply Prod.ext
    · simp [triangularAction]
    · simpa [triangularAction, add_comm] using hsource
  unfold firstRowAnomaly
  rw [hdecomp, map_smul, map_add]
  simp [transposeAction, smul_add]

/-- No complex-linear operator intertwiner, local or nonlocal, can retain
full-channel contact at a source vertex when coupling is nonzero. -/
theorem compatible_source_full_zero
    (lam : ℂ) (D : E → E) (S : (E × E) →ₗ[ℂ] (E × E))
    (H Q : E) (hlam : lam ≠ 0)
    (hcompat : ∀ p : E × E,
      S (triangularAction lam D p) = transposeAction lam D (S p))
    (hsource : D H = lam • (H + Q)) :
    (S (H,Q)).1 = 0 := by
  have hz : firstRowAnomaly lam D S H = 0 := by
    simp [firstRowAnomaly, hcompat]
  rw [firstRowAnomaly_eq_fullSourceReadout lam D S H Q hsource] at hz
  have hzero := congrArg (fun y : E => lam⁻¹ • y) hz
  simpa [smul_smul, hlam] using hzero

/-- First-row anomaly without assuming complex linearity. -/
def firstRowAnomalyAdd (lam : ℂ) (D : E → E)
    (S : (E × E) →+ (E × E)) (H : E) : E :=
  (S (triangularAction lam D (0,H))).1 - lam • (S (0,H)).1

/-- Failure of a merely additive current to respect complex scaling at the
single vector selected by the source equation. -/
def scalarLinearityDefect (lam : ℂ)
    (S : (E × E) →+ (E × E)) (H Q : E) : E :=
  (S (lam • ((H,Q) + (0,H)))).1 -
    lam • (S ((H,Q) + (0,H))).1

/-- Exact two-defect budget: operator anomaly is full source contact plus
the complex-linearity defect. This states both possible algebraic escapes
without hiding either in a boundary normalization. -/
theorem two_defect_source_law
    (lam : ℂ) (D : E → E) (S : (E × E) →+ (E × E))
    (H Q : E) (hsource : D H = lam • (H + Q)) :
    firstRowAnomalyAdd lam D S H =
      lam • (S (H,Q)).1 + scalarLinearityDefect lam S H Q := by
  have hdecomp : triangularAction lam D (0,H) =
      lam • ((H,Q) + (0,H)) := by
    apply Prod.ext
    · simp [triangularAction]
    · simpa [triangularAction, add_comm] using hsource
  unfold firstRowAnomalyAdd scalarLinearityDefect
  rw [hdecomp, map_add]
  simp only [Prod.fst_add, smul_add]
  abel

/-- First-row anomaly for an additive current whose scalar action may be
twisted, as in a Hermitian rather than bilinear pairing. -/
def semilinearFirstRowAnomaly (lam kap : ℂ) (D : E → E)
    (S : (E × E) →+ (E × E)) (H : E) : E :=
  (S (triangularAction lam D (0,H))).1 - kap • (S (0,H)).1

/-- The source-contact obstruction is unchanged by a scalar twist: if the
current sends multiplication by `lam` to multiplication by `kap` at the
source-selected vector, its first-row anomaly is `kap` times full contact. -/
theorem semilinear_source_law
    (lam kap : ℂ) (D : E → E) (S : (E × E) →+ (E × E))
    (H Q : E) (hsource : D H = lam • (H + Q))
    (hscale : S (lam • ((H,Q) + (0,H))) =
      kap • S ((H,Q) + (0,H))) :
    semilinearFirstRowAnomaly lam kap D S H =
      kap • (S (H,Q)).1 := by
  have hdecomp : triangularAction lam D (0,H) =
      lam • ((H,Q) + (0,H)) := by
    apply Prod.ext
    · simp [triangularAction]
    · simpa [triangularAction, add_comm] using hsource
  unfold semilinearFirstRowAnomaly
  rw [hdecomp, hscale, map_add]
  simp [Prod.fst_add, smul_add]

/-- Even a twisted scalar action cannot retain full source contact when its
matching adjoint first row is compatible and the twist is nonzero. -/
theorem semilinear_compatible_source_full_zero
    (lam kap : ℂ) (D : E → E) (S : (E × E) →+ (E × E))
    (H Q : E) (hkap : kap ≠ 0)
    (hsource : D H = lam • (H + Q))
    (hscale : S (lam • ((H,Q) + (0,H))) =
      kap • S ((H,Q) + (0,H)))
    (hcompat : (S (triangularAction lam D (0,H))).1 =
      kap • (S (0,H)).1) :
    (S (H,Q)).1 = 0 := by
  have hz : semilinearFirstRowAnomaly lam kap D S H = 0 :=
    sub_eq_zero.mpr hcompat
  rw [semilinear_source_law lam kap D S H Q hsource hscale] at hz
  have hzero := congrArg (fun y : E => kap⁻¹ • y) hz
  simpa [smul_smul, hkap] using hzero

/-- In particular, the Hermitian/conjugate-linear change of pairing does
not rescue a conserved full-source current. -/
theorem conjugateLinear_compatible_source_full_zero
    (lam : ℂ) (D : E → E) (S : (E × E) →+ (E × E))
    (H Q : E) (hlam : lam ≠ 0)
    (hsource : D H = lam • (H + Q))
    (hconj : ∀ p : E × E, S (lam • p) = star lam • S p)
    (hcompat : (S (triangularAction lam D (0,H))).1 =
      star lam • (S (0,H)).1) :
    (S (H,Q)).1 = 0 := by
  have hkap : star lam ≠ 0 := by
    intro hz
    apply hlam
    have hh := congrArg star hz
    simpa using hh
  exact semilinear_compatible_source_full_zero lam (star lam) D S
    H Q hkap hsource (hconj _) hcompat

/-- The source's literal full-minus-native vertex is selected by the signed
channel reader. This reader is not conserved; its defect is the survivor. -/
def differenceReader : (E × E) →ₗ[ℂ] (E × E) where
  toFun p := (p.1 - p.2, 0)
  map_add' p q := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add]
      abel
    · simp
  map_smul' c p := by
    apply Prod.ext
    · simp [smul_sub]
    · simp

/-- Exact source-to-defect identity for the signed reader: the full/native
lift vertex `H-Q` is precisely its normalized first-row operator anomaly. -/
theorem differenceReader_source_anomaly
    (lam : ℂ) (D : E → E) (H Q : E)
    (hsource : D H = lam • (H + Q)) :
    firstRowAnomaly lam D (differenceReader (E := E)) H =
      lam • (H - Q) := by
  rw [firstRowAnomaly_eq_fullSourceReadout lam D (differenceReader (E := E))
    H Q hsource]
  rfl

end
end RHTower.D4BMPWOperatorAnomaly
