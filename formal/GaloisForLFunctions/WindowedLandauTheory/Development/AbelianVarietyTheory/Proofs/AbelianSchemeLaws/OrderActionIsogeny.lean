import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELOrderAction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GeometricPointDivision
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! An integral coefficient of nonzero norm acts by an étale isogeny over a rational base. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT

open GlobalTheory.GrpTangent ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem OActN.act_natCast_eq_mulN {O : Type} [Ring O] (a : OActN O A) (n : ℕ) :
    a.act (n : O) = mulN A n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    simpa only [Nat.cast_zero, mulN, pow_zero] using mul_eq_left.mp h.symm
  | succ n ih =>
    rw [Nat.cast_succ, a.add, ih, a.one]
    exact (pow_succ (𝟙 A) n).symm

/-- Nonzero elements of the coefficient ring give finite étale surjections in characteristic zero. -/
theorem OActN.finiteEtaleSurjective_of_ne_zero {R F : Type} [CommRing R] [Algebra ℚ R]
    [Field F] [NumberField F] (s : S ⟶ Spec (CommRingCat.of R)) (a : OActN (𝓞 F) A)
    (hA : IsAbelianScheme A) {c : 𝓞 F} (hc : c ≠ 0) :
    IsFinite (a.act c).left ∧ Etale (a.act c).left ∧ Surjective (a.act c).left := by
  let I : Ideal (𝓞 F) := Ideal.span {c}
  let n := I.absNorm
  have hn : 0 < n := by
    change 0 < (Ideal.span {c}).absNorm
    rw [Nat.pos_iff_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem I)
  change d * c = (n : 𝓞 F) at hd
  have h₁ : a.act c ≫ a.act d = mulN A n := by
    rw [← a.mul d c, hd, a.act_natCast_eq_mulN]
  have h₂ : a.act d ≫ a.act c = mulN A n := by
    rw [← a.mul c d, mul_comm c d, hd, a.act_natCast_eq_mulN]
  letI := hA.comm
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  exact finiteEtaleSurjective_of_quasiInverse (isUnit_natCast_of_overRat s hn) _ _ h₁ h₂

/-- The coefficient action is surjective on geometric points over a rational base. -/
theorem OActN.surjective_geometric_points_of_ne_zero {R F k : Type} [CommRing R] [Algebra ℚ R]
    [Field F] [NumberField F] [Field k] [IsAlgClosed k] (s : S ⟶ Spec (CommRingCat.of R))
    (a : OActN (𝓞 F) A) (hA : IsAbelianScheme A) {c : 𝓞 F} (hc : c ≠ 0)
    (x : Spec (CommRingCat.of k) ⟶ S) :
    Function.Surjective (fun y : Over.mk x ⟶ A => y ≫ a.act c) := by
  obtain ⟨hfinite, _, hsurj⟩ := a.finiteEtaleSurjective_of_ne_zero s hA hc
  intro y
  exact @exists_lift_geometric_point S A A (a.act c) hfinite hsurj k _ _ x y

end GlobalTheory.UPel.HT
