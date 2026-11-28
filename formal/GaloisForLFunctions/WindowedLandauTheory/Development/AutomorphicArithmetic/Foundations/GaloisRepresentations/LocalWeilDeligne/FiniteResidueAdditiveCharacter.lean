import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Trace.Basic

/-! Pairing with a primitive multiplicative generator under the
finite-field trace gives an additive character with trivial
stabilizer in the field automorphism group. -/

noncomputable section

namespace GlobalTheory.WeilDeligne

theorem exists_additiveCharacter_aut_stabilizer_trivial (F : Type*) [Field F] [Finite F] :
    ∃ χ : Multiplicative F →* ℂˣ, ∀ g : RingAut F,
      (∀ x : F, χ (Multiplicative.ofAdd (g x)) = χ (Multiplicative.ofAdd x)) ↔ g = 1 := by
  classical
  let p := ringChar F
  haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := Fˣ)
  let T : F →ₗ[ZMod p] ZMod p := Algebra.trace (ZMod p) F
  let ψ := ((ZMod.stdAddChar (N := p)).compAddMonoidHom T.toAddMonoidHom).mulShift (b : F)
  have hψ (x : F) : ψ x = ZMod.stdAddChar (T ((b : F) * x)) := rfl
  refine ⟨ψ.toMonoidHom.toHomUnits, fun g => ⟨fun h => ?_, fun h x => by rw [h]; rfl⟩⟩
  have hχ (x : F) : T ((b : F) * g x) = T ((b : F) * x) := by
    apply ZMod.injective_stdAddChar
    rw [← hψ, ← hψ]
    exact congrArg Units.val (h x)
  let e : F ≃ₐ[ZMod p] F := AlgEquiv.ofRingEquiv (f := g) fun c => by
    have := RingHom.ext_zmod ((g : F →+* F).comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)
    exact DFunLike.congr_fun this c
  have hT (x : F) : T (g x) = T x := Algebra.trace_eq_of_algEquiv e x
  have hbg : g (b : F) = b := by
    by_contra hne
    have hne' : (b : F) - g (b : F) ≠ 0 := fun he => hne (sub_eq_zero.mp he).symm
    obtain ⟨y, hy⟩ := FiniteField.trace_to_zmod_nondegenerate F hne'
    apply hy
    obtain ⟨x, rfl⟩ := g.surjective y
    change T (((b : F) - g b) * g x) = 0
    rw [sub_mul, map_sub, hχ, ← map_mul, hT, sub_self]
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hb (Units.mk0 x hx))
    have he : x = (b : F) ^ i := by rw [← Units.val_zpow_eq_zpow_val, hi]; rfl
    rw [he, map_zpow₀, hbg]
    rfl

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_additiveCharacter_aut_stabilizer_trivial
