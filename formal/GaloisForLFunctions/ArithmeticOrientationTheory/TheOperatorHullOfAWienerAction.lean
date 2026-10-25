import GaloisForLFunctions.ArithmeticOrientationTheory.WienersLemmaOnTheBohrPolydisk
import Mathlib.Topology.Algebra.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The operator hull of a Wiener action

Characters bounded by the represented norm form a nonempty subset of the
annihilator hull and satisfy exact dilation-coordinate bounds. Closed image
makes these hulls equal by the spectral bound for algebra characters.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open WienerAlgebraAt

variable {σ : ℝ} {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Bohr evaluations bounded by the represented norm. -/
def operatorHull (π : WienerAlgebraAt σ →ₐ[ℂ] A) : Set BohrPoint :=
  {ω | ∀ a, ‖bohrEval σ a.toFn ω‖ ≤ ‖π a‖}

/-- A character of the closed commutative image gives a norm-bounded Bohr point. -/
theorem operatorHull_nonempty [CompleteSpace A] [Nontrivial A] [NormOneClass A]
    (π : WienerAlgebraAt σ →ₐ[ℂ] A) :
    (operatorHull π).Nonempty := by
  let S := π.range
  have hcomm : ∀ x y : S, x * y = y * x := by
    intro x y
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    apply Subtype.ext
    change (x : A) * (y : A) = (y : A) * (x : A)
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm a b]
  let B := S.topologicalClosure
  letI : CommRing B := S.commRingTopologicalClosure hcomm
  letI : NormedCommRing B := { (inferInstance : NormedRing B) with mul_comm := mul_comm }
  letI : CompleteSpace B := S.isClosed_topologicalClosure.completeSpace_coe
  letI : NormOneClass B := ⟨show ‖(1 : A)‖ = 1 from norm_one⟩
  let f : WienerAlgebraAt σ →ₐ[ℂ] B :=
    (Subalgebra.inclusion S.le_topologicalClosure).comp π.rangeRestrict
  obtain ⟨M, hM, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal B) bot_ne_top
  letI := hM
  let χ := M.toCharacterSpace
  let φ : WeakDual.characterSpace ℂ (WienerAlgebraAt σ) :=
    WeakDual.CharacterSpace.equivAlgHom.symm
      ((WeakDual.CharacterSpace.equivAlgHom χ).comp f)
  refine ⟨characterBohrPoint φ, fun a => ?_⟩
  rw [← apply_eq_bohrEval]
  change ‖χ (f a)‖ ≤ ‖(f a : A)‖
  have hχ : ‖χ (f a)‖ ≤ ‖f a‖ :=
    spectrum.norm_le_norm_of_mem (AlgHom.apply_mem_spectrum χ (f a))
  exact hχ

/-- Norm-bounded characters vanish on the representation kernel. -/
theorem operatorHull_subset_annihilatorHull (π : WienerAlgebraAt σ →ₐ[ℂ] A) :
    operatorHull π ⊆ {ω | ∀ a ∈ RingHom.ker π.toRingHom, bohrEval σ a.toFn ω = 0} := by
  intro ω hω a ha
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := hω a
  change π a = 0 at ha
  simpa only [ha, norm_zero] using h

/-- The norm-bounded hull, rather than the entire annihilator hull, obeys the dilation radii. -/
theorem norm_coordinate_le_operatorHull (π : WienerAlgebraAt σ →ₐ[ℂ] A)
    {ω : BohrPoint} (hω : ω ∈ operatorHull π) (p : ℕ+) :
    ‖ω.ω p‖ ≤ (p : ℝ) ^ σ * ‖π (pointMass p)‖ := by
  have h := hω (pointMass p)
  have heval : bohrEval σ (pointMass (σ := σ) p).toFn ω =
      ω.ω p / (p : ℂ) ^ (σ : ℂ) :=
    bohrEval_pointMass (σ := σ) (n := (p : ℕ)) p.property.ne' ω
  rw [heval, norm_div,
    norm_natCast_cpow p p.property.ne'] at h
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property
  simpa only [mul_comm] using (div_le_iff₀ (Real.rpow_pos_of_pos hp σ)).mp h

end GaloisForLFunctions.ArithmeticOrientationTheory

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open WienerAlgebraAt

variable {σ : ℝ} {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [NormOneClass A]

/-- A closed represented algebra makes every annihilator character norm-bounded. -/
theorem annihilatorHull_subset_operatorHull_of_isClosed_range
    (π : WienerAlgebraAt σ →ₐ[ℂ] A) (hclosed : IsClosed (π.range : Set A)) :
    {ω | ∀ a ∈ RingHom.ker π.toRingHom, bohrEval σ a.toFn ω = 0} ⊆ operatorHull π := by
  intro ω hω a
  let φ := WienerAlgebraAt.bohrCharacter σ ω
  have hle : RingHom.ker π.toRingHom ≤ RingHom.ker φ.toRingHom := by
    intro b hb
    change φ b = 0
    exact hω b hb
  let χ : π.range →ₐ[ℂ] ℂ :=
    (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) φ hle).comp
      (Ideal.quotientKerEquivRange π).symm.toAlgHom
  letI : CompleteSpace π.range := hclosed.completeSpace_coe
  letI : NormOneClass π.range := ⟨show ‖(1 : A)‖ = 1 from norm_one⟩
  have hforward : Ideal.quotientKerEquivRange π
      (Ideal.Quotient.mk (RingHom.ker π.toRingHom) a) = π.rangeRestrict a := rfl
  have hχ : χ (π.rangeRestrict a) = φ a := by
    rw [← hforward]
    change (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) φ hle)
      ((Ideal.quotientKerEquivRange π).symm
        ((Ideal.quotientKerEquivRange π) (Ideal.Quotient.mk _ a))) = φ a
    rw [AlgEquiv.symm_apply_apply]
    rfl
  change ‖φ a‖ ≤ ‖π a‖
  rw [← hχ]
  have hnorm : ‖χ (π.rangeRestrict a)‖ ≤ ‖π.rangeRestrict a‖ :=
    spectrum.norm_le_norm_of_mem (AlgHom.apply_mem_spectrum χ (π.rangeRestrict a))
  exact hnorm

/-- A closed representation image identifies the two hulls. -/
theorem operatorHull_eq_annihilatorHull_of_isClosed_range
    (π : WienerAlgebraAt σ →ₐ[ℂ] A) (hclosed : IsClosed (π.range : Set A)) :
    operatorHull π = {ω | ∀ a ∈ RingHom.ker π.toRingHom, bohrEval σ a.toFn ω = 0} :=
  (operatorHull_subset_annihilatorHull π).antisymm
    (annihilatorHull_subset_operatorHull_of_isClosed_range π hclosed)

end GaloisForLFunctions.ArithmeticOrientationTheory
