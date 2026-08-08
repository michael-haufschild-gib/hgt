import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Parachain Connes comparison and inverse-monodromy totalization

This file supplies the route-independent algebraic infrastructure used by the Stage-2 cards
`polarized-exactness-horizon-and-relative-connes-phase-law.md` and
`split-prime-euler-class-and-inverse-monodromy-totalization-no-go.md`.

It proves the exact Connes null-homotopy identity for every map of underlying `b`-complexes and
separately proves that pairing scalar monodromy with its inverse makes total monodromy trivial
without making either factor trivial.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Parachain comparison -/

variable {C C' : Type*} [AddCommGroup C] [AddCommGroup C']

/-- Ungraded operator package for the parachain identities used in the paper theorem. -/
structure ParachainDatum (C : Type*) [AddCommGroup C] where
  b : C →+ C
  B : C →+ C
  T : C →+ C
  b_sq : ∀ x, b (b x) = 0
  B_sq : ∀ x, B (B x) = 0
  connes : ∀ x, b (B x) + B (b x) = x - T x

/-- Map of the underlying `b`-complexes. -/
structure ParachainBMap (source : ParachainDatum C) (target : ParachainDatum C') where
  toAddHom : C →+ C'
  commutes_b : ∀ x, target.b (toAddHom x) = toAddHom (source.b x)

instance {source : ParachainDatum C} {target : ParachainDatum C'} :
    CoeFun (ParachainBMap source target) (fun _ => C → C') :=
  ⟨fun f => f.toAddHom⟩

/-- Connes comparison `H_f=B'f-fB`. -/
def connesComparison {source : ParachainDatum C} {target : ParachainDatum C'}
    (f : ParachainBMap source target) : C →+ C' :=
  target.B.comp f.toAddHom - f.toAddHom.comp source.B

/-- Monodromy defect `E_f=T'f-fT`. -/
def paracyclicMonodromyDefect {source : ParachainDatum C} {target : ParachainDatum C'}
    (f : ParachainBMap source target) : C →+ C' :=
  target.T.comp f.toAddHom - f.toAddHom.comp source.T

/-- **Target monodromy is Connes-null-homotopic.**  For every underlying `b`-chain map,
`b'H_f+H_fb=-E_f`. -/
theorem connesComparison_nullhomotopy
    {source : ParachainDatum C} {target : ParachainDatum C'}
    (f : ParachainBMap source target) (x : C) :
    target.b (connesComparison f x) + connesComparison f (source.b x) =
      -paracyclicMonodromyDefect f x := by
  change target.b (target.B (f x) - f (source.B x)) +
      (target.B (f (source.b x)) - f (source.B (source.b x))) =
    -(target.T (f x) - f (source.T x))
  rw [map_sub, f.commutes_b (source.B x), ← f.commutes_b x]
  calc
    target.b (target.B (f x)) - f (source.b (source.B x)) +
          (target.B (target.b (f x)) - f (source.B (source.b x))) =
        (target.b (target.B (f x)) + target.B (target.b (f x))) -
          f (source.b (source.B x) + source.B (source.b x)) := by
            rw [map_add]
            abel
    _ = (f x - target.T (f x)) - f (x - source.T x) := by
      rw [target.connes, source.connes]
    _ = -(target.T (f x) - f (source.T x)) := by
      rw [map_sub]
      abel

/-! ## Inverse scalar monodromy -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Scalar monodromy operator. -/
def scalarMonodromy (u : K) : V →ₗ[K] V :=
  u • LinearMap.id

@[simp]
theorem scalarMonodromy_apply (u : K) (x : V) : scalarMonodromy u x = u • x := by
  simp [scalarMonodromy]

/-- Horizontal scalar monodromy and its inverse have identity total monodromy. -/
theorem scalarMonodromy_comp_inverse (u : Kˣ) :
    (scalarMonodromy (V := V) (u : K)).comp
        (scalarMonodromy (V := V) (↑u⁻¹ : K)) = LinearMap.id := by
  ext x
  simp [scalarMonodromy, smul_smul]

/-- Nontrivial factor monodromy can cancel against its inverse in totalization. -/
theorem scalarMonodromy_factors_nontrivial
    [Nontrivial V] (u : Kˣ) (hu : (u : K) ≠ 1) :
    scalarMonodromy (V := V) (u : K) ≠ LinearMap.id ∧
      scalarMonodromy (V := V) (↑u⁻¹ : K) ≠ LinearMap.id := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  constructor
  · intro heq
    have happ := LinearMap.congr_fun heq x
    simp [scalarMonodromy] at happ
    apply hu
    rw [← sub_eq_zero, ← smul_eq_zero_iff_left hx, sub_smul]
    simpa using sub_eq_zero.mpr happ
  · intro heq
    have happ := LinearMap.congr_fun heq x
    simp [scalarMonodromy] at happ
    have hinv : (↑u⁻¹ : K) = 1 := by
      rw [← sub_eq_zero, ← smul_eq_zero_iff_left hx, sub_smul]
      simpa using sub_eq_zero.mpr happ
    apply hu
    simpa using congrArg Inv.inv hinv

end GaloisForLFunctions.HTGeometry
