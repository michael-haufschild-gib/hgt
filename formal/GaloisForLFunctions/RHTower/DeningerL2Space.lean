import GaloisForLFunctions.RHTower.DeningerL2Norm2
import GaloisForLFunctions.RHTower.DeningerRealSmulModule
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The `L²` Kummer space and its completion

The Kummer space already carries the height norm, so the `L²` norm is installed on a type synonym.
That synonym is a normed `ℚ`-vector space, its completion is complete, and the real scalar
extension makes the completion a real normed space: this is the Hilbert--Kummer space.

* `DeningerL2Space` : the Kummer space with the `L²` norm.
* `DeningerL2Completion` : its completion.
* `deningerL2Completion_realModule` : the real structure on the completion.
-/

namespace RHTower

open NumberField

section L2Space

variable (F : Type*) [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- The Kummer space `𝒢 ⊗ ℚ` carrying the `L²` norm. -/
def DeningerL2Space : Type _ := deningerKummerSpace F

instance : AddCommGroup (DeningerL2Space F) :=
  inferInstanceAs (AddCommGroup (deningerKummerSpace F))

noncomputable instance deningerL2Space_module : Module ℚ (DeningerL2Space F) :=
  inferInstanceAs (Module ℚ (deningerKummerSpace F))

noncomputable instance : NormedAddCommGroup (DeningerL2Space F) :=
  (deningerL2AddGroupNorm (F := F)).toNormedAddCommGroup

variable {F}

theorem deningerL2Space_norm_def (x : DeningerL2Space F) :
    ‖x‖ = deningerL2Norm (F := F) (x : deningerKummerSpace F) := rfl

/-- The `L²` norm scales by the absolute value of a rational scalar. -/
theorem deningerL2Norm_qsmul (q : ℚ) (x : deningerKummerSpace F) :
    deningerL2Norm (q • x) = |(q : ℝ)| * deningerL2Norm x := by
  have hq : deningerSpaceL2Inner (q • x) (q • x)
      = (q : ℝ) ^ 2 * deningerSpaceL2Inner x x := by
    rw [deningerSpaceL2Inner_qsmul_left, deningerSpaceL2Inner_comm x (q • x),
      deningerSpaceL2Inner_qsmul_left, deningerSpaceL2Inner_comm x x]
    ring
  rw [deningerL2Norm, deningerL2Norm, hq, Real.sqrt_mul (by positivity),
    Real.sqrt_sq_eq_abs]

variable (F)

noncomputable instance : NormedSpace ℚ (DeningerL2Space F) :=
  { deningerL2Space_module F with
    norm_smul_le := fun q x => by
      have h : deningerL2Norm (F := F) (q • x) = |(q : ℝ)| * deningerL2Norm (F := F) x :=
        deningerL2Norm_qsmul q x
      have hn : ‖q‖ = |(q : ℝ)| := by
        rw [← Rat.norm_cast_real, Real.norm_eq_abs]
      show deningerL2Norm (F := F) (q • x) ≤ ‖q‖ * deningerL2Norm (F := F) x
      rw [hn]
      exact le_of_eq h }

/-- **The Hilbert--Kummer space**: the completion of `𝒢 ⊗ ℚ` for the `L²` norm. -/
abbrev DeningerL2Completion : Type _ := UniformSpace.Completion (DeningerL2Space F)

/-- **The real structure on the Hilbert--Kummer space**, from the extension of rational scalars
along the dense embedding `ℚ ↪ ℝ`. -/
@[reducible] noncomputable def deningerL2Completion_realModule : Module ℝ (DeningerL2Completion F) :=
  deningerRealModule

/-- The real action on the completion has the expected norm law. -/
theorem deningerL2Completion_realSmul_norm (r : ℝ) (x : DeningerL2Completion F) :
    ‖deningerRealSmul r x‖ = |r| * ‖x‖ :=
  deningerRealSmul_norm r x

end L2Space

end RHTower
