import GaloisForLFunctions.HTGeometry.DifferentialClosureClosed
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealAvoiding

/-!
# Kolchin's Nullstellensatz

A nonzero element of a differentially reduced algebra survives some differential map to a
differential field — that is the weak differential Nullstellensatz with a nonvanishing element.
Presenting the algebra by finitely many generators turns that map into a solution, in a differential
field extension, of a *finite* differential system over the base: the defining relations, the
first-order equations expressing the derivatives of the generators, and the Rabinowitsch equation
forcing the given element to be invertible.

Over a differentially closed field that system therefore has a solution in the field itself, and the
solution is a differential point not killing the element.  Hence the differential points of a
finitely generated differentially reduced algebra separate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

/-- An ordinary polynomial read as a differential polynomial of order zero. -/
def orderZeroEmbed {C ι : Type*} [CommRing C] {k : ℕ} (ι₀ : Fin k → ι) :
    MvPolynomial (Fin k) C →ₐ[C] DifferentialPolynomial ι C :=
  MvPolynomial.aeval (fun i => MvPolynomial.X (ι₀ i, 0))

@[simp] theorem orderZeroEmbed_X {C ι : Type*} [CommRing C] {k : ℕ} (ι₀ : Fin k → ι) (i : Fin k) :
    orderZeroEmbed (C := C) ι₀ (MvPolynomial.X i) = MvPolynomial.X (ι₀ i, 0) := by
  simp [orderZeroEmbed]

theorem differentialPolynomialEvalOver_orderZeroEmbed {C ι M : Type*} [CommRing C] [CommRing M]
    [Algebra C M] [Differential M] {k : ℕ} (ι₀ : Fin k → ι) (y : ι → M)
    (g : MvPolynomial (Fin k) C) :
    differentialPolynomialEvalOver (K := C) y (orderZeroEmbed ι₀ g)
      = MvPolynomial.aeval (fun i => y (ι₀ i)) g := by
  have hcomp := MvPolynomial.comp_aeval (R := C) (σ := Fin k)
    (fun i : Fin k => (MvPolynomial.X (ι₀ i, 0) : DifferentialPolynomial ι C))
    (differentialPolynomialEvalOver (K := C) y)
  have h := congrArg (fun φ : MvPolynomial (Fin k) C →ₐ[C] M => φ g) hcomp
  simp only [AlgHom.coe_comp, Function.comp_apply] at h
  have hfun : (fun i : Fin k =>
      differentialPolynomialEvalOver (K := C) y (MvPolynomial.X (ι₀ i, 0)))
      = fun i : Fin k => y (ι₀ i) := by
    funext i
    rw [differentialPolynomialEvalOver_X, differentialJet_zero]
  rw [orderZeroEmbed, ← hfun]
  exact h

variable {C E : Type u} [Field C] [Algebra ℚ C] [Differential C] [IsDifferentiallyClosed C]
  [CommRing E] [IsReduced E] [Algebra C E] [Algebra ℚ E]
  [Differential E] [DifferentialAlgebra C E] [Algebra.FiniteType C E]

set_option maxHeartbeats 1600000 in
/-- **Kolchin's Nullstellensatz.**  Over a differentially closed field, a nonzero element of a
finitely generated differentially reduced algebra is not killed by all differential points. -/
theorem exists_differentialAlgHom_ne_zero {e : E} (he : e ≠ 0) :
    ∃ χ : E →ₐ[C] C, (∀ x : E, χ (Differential.deriv x) = Differential.deriv (χ x)) ∧ χ e ≠ 0 := by
  classical
  have hbotrad : (⊥ : Ideal E).IsRadical := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    rw [Ideal.mem_bot] at hn ⊢
    exact IsReduced.eq_zero y ⟨n, hn⟩
  have hbotδ : ∀ x ∈ (⊥ : Ideal E), Differential.deriv x ∈ (⊥ : Ideal E) := by
    intro x hx
    rw [Ideal.mem_bot] at hx ⊢
    rw [hx, map_zero]
  obtain ⟨L, hLfield, hLdiff, f, hfδ, _, hfe⟩ :=
    exists_differentialField_hom_of_notMem (R := E) hbotrad hbotδ
      (e := e) (by rw [Ideal.mem_bot]; exact he)
  letI := hLfield
  letI := hLdiff
  letI : Algebra C L := (f.comp (algebraMap C E)).toAlgebra
  letI : Algebra ℚ L := (f.comp (algebraMap ℚ E)).toAlgebra
  have hCL : ∀ c : C, algebraMap C L c = f (algebraMap C E c) := fun _ => rfl
  have hcompatL : ∀ c : C, Differential.deriv (algebraMap C L c)
      = algebraMap C L (Differential.deriv c) := by
    intro c
    rw [hCL, hCL, ← hfδ, DifferentialAlgebra.deriv_algebraMap]
  letI fA : E →ₐ[C] L := { f with commutes' := fun c => rfl }
  have hfA : ∀ x : E, fA x = f x := fun _ => rfl
  obtain ⟨k, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType C E)
  haveI : IsNoetherianRing (MvPolynomial (Fin k) C) := MvPolynomial.isNoetherianRing
  obtain ⟨G, hG⟩ :=
    (isNoetherianRing_iff_ideal_fg (MvPolynomial (Fin k) C)).mp inferInstance
      (RingHom.ker (π : MvPolynomial (Fin k) C →+* E))
  have hPex : ∀ i : Fin k, ∃ P : MvPolynomial (Fin k) C,
      π P = Differential.deriv (π (MvPolynomial.X i)) := fun i => hπ _
  choose P hP using hPex
  obtain ⟨Q, hQ⟩ := hπ e
  set ι₀ : Fin k → ULift.{u} (Fin (k + 1)) := fun i => ULift.up i.castSucc with hι₀
  set ιlast : ULift.{u} (Fin (k + 1)) := ULift.up (Fin.last k) with hιlast
  set T : Finset (DifferentialPolynomial (ULift.{u} (Fin (k + 1))) C) :=
    (G.image (orderZeroEmbed ι₀))
      ∪ (Finset.univ.image (fun i : Fin k =>
          MvPolynomial.X (ι₀ i, 1) - orderZeroEmbed ι₀ (P i)))
      ∪ {MvPolynomial.X (ιlast, 0) * orderZeroEmbed ι₀ Q - 1} with hT
  obtain ⟨z, hzcast, hzlast⟩ : ∃ z : ULift.{u} (Fin (k + 1)) → L,
      (∀ i : Fin k, z (ι₀ i) = fA (π (MvPolynomial.X i))) ∧ z ιlast = (fA e)⁻¹ := by
    refine ⟨fun v => Fin.lastCases ((fA e)⁻¹)
      (fun i => fA (π (MvPolynomial.X i))) v.down, fun i => ?_, ?_⟩
    · exact Fin.lastCases_castSucc i
    · exact Fin.lastCases_last
  have hevalcomp : ∀ g : MvPolynomial (Fin k) C,
      differentialPolynomialEvalOver (K := C) z (orderZeroEmbed ι₀ g) = fA (π g) := by
    intro g
    rw [differentialPolynomialEvalOver_orderZeroEmbed]
    have hfun : (fun i : Fin k => z (ι₀ i)) = (⇑(fA.comp π) ∘ MvPolynomial.X) := by
      funext i
      rw [hzcast]
      rfl
    rw [hfun, ← MvPolynomial.aeval_unique (fA.comp π)]
    rfl
  have hzsol : ∀ p ∈ T, differentialPolynomialEvalOver (K := C) z p = 0 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨g, hgG, rfl⟩ := Finset.mem_image.mp hp
        rw [hevalcomp]
        have hgker : g ∈ RingHom.ker (π : MvPolynomial (Fin k) C →+* E) := by
          rw [← hG]
          exact Ideal.subset_span hgG
        rw [RingHom.mem_ker] at hgker
        have hgker0 : π g = 0 := hgker
        show fA (π g) = 0
        rw [hgker0, map_zero]
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
        rw [map_sub, hevalcomp, differentialPolynomialEvalOver_X, hzcast,
          differentialJet_succ, differentialJet_zero]
        show Differential.deriv (f (π (MvPolynomial.X i))) - f (π (P i)) = 0
        rw [hP i, hfδ, sub_self]
    · rw [Finset.mem_singleton] at hp
      subst hp
      rw [map_sub, map_mul, hevalcomp, differentialPolynomialEvalOver_X, hzlast,
        differentialJet_zero, map_one, hQ]
      show (f e)⁻¹ * f e - 1 = 0
      rw [inv_mul_cancel₀ hfe, sub_self]
  obtain ⟨b, hb⟩ := IsDifferentiallyClosed.exists_point (C := C) T
    ⟨L, hcompatL⟩ z hzsol
  set bb : Fin k → C := fun i => b (ι₀ i) with hbb
  have hbG : ∀ g ∈ G, MvPolynomial.aeval bb g = 0 := by
    intro g hg
    have := hb (orderZeroEmbed ι₀ g)
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg)))
    rwa [differentialPolynomialEvalOver_orderZeroEmbed] at this
  have hbODE : ∀ i : Fin k, Differential.deriv (bb i) = MvPolynomial.aeval bb (P i) := by
    intro i
    have := hb (MvPolynomial.X (ι₀ i, 1) - orderZeroEmbed ι₀ (P i))
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
    rw [map_sub, differentialPolynomialEvalOver_orderZeroEmbed,
      differentialPolynomialEvalOver_X, differentialJet_succ, differentialJet_zero,
      sub_eq_zero] at this
    exact this
  have hbQ : MvPolynomial.aeval bb Q ≠ 0 := by
    have := hb (MvPolynomial.X (ιlast, 0) * orderZeroEmbed ι₀ Q - 1)
      (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    rw [map_sub, map_mul, differentialPolynomialEvalOver_orderZeroEmbed,
      differentialPolynomialEvalOver_X, differentialJet_zero, map_one, sub_eq_zero] at this
    intro hzero
    rw [hzero, mul_zero] at this
    exact zero_ne_one this
  have hkerle : RingHom.ker (π : MvPolynomial (Fin k) C →+* E)
      ≤ RingHom.ker ((MvPolynomial.aeval bb : MvPolynomial (Fin k) C →ₐ[C] C) :
        MvPolynomial (Fin k) C →+* C) := by
    rw [← hG]
    refine Ideal.span_le.mpr ?_
    intro g hg
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact hbG g hg
  set χ : E →ₐ[C] C :=
    (Ideal.Quotient.liftₐ (RingHom.ker (π : MvPolynomial (Fin k) C →+* E))
      (MvPolynomial.aeval bb) (fun a ha => RingHom.mem_ker.mp (hkerle ha))).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom with hχ
  have hχπ : ∀ g : MvPolynomial (Fin k) C, χ (π g) = MvPolynomial.aeval bb g := by
    intro g
    show (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval bb) (fun a ha => RingHom.mem_ker.mp (hkerle ha)))
      ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π g)) = _
    have hsymm : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π g)
        = Ideal.Quotient.mk (RingHom.ker (π : MvPolynomial (Fin k) C →+* E)) g := by
      refine (AlgEquiv.symm_apply_eq _).mpr ?_
      rfl
    rw [hsymm]
    rfl
  refine ⟨χ, ?_, ?_⟩
  · intro x
    obtain ⟨g, rfl⟩ := hπ x
    induction g using MvPolynomial.induction_on with
    | C c =>
        have hπC : π (MvPolynomial.C c) = algebraMap C E c := by
          rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        rw [hπC, DifferentialAlgebra.deriv_algebraMap, AlgHom.commutes, AlgHom.commutes]
        simp
    | add g h hg hh =>
        simp only [map_add, hg, hh]
    | mul_X g i hg =>
        have hL : χ (Differential.deriv (π (g * MvPolynomial.X i)))
            = MvPolynomial.aeval bb g * MvPolynomial.aeval bb (P i)
              + bb i * Differential.deriv (MvPolynomial.aeval bb g) := by
          rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
            ← hP i, hg, hχπ, hχπ, hχπ, MvPolynomial.aeval_X]
        have hR : Differential.deriv (χ (π (g * MvPolynomial.X i)))
            = MvPolynomial.aeval bb g * MvPolynomial.aeval bb (P i)
              + bb i * Differential.deriv (MvPolynomial.aeval bb g) := by
          rw [hχπ, map_mul, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
            hbODE i]
        rw [hL, hR]
  · rw [← hQ, hχπ]
    exact hbQ

/-- The differential points of a differential algebra: the algebra maps to the base commuting with
the derivations. -/
def differentialPoints (C E : Type*) [CommRing C] [Differential C] [CommRing E] [Differential E]
    [Algebra C E] : Set (E →ₐ[C] C) :=
  {χ | ∀ z : E, χ (Differential.deriv z) = Differential.deriv (χ z)}

/-- **The differential points separate.**  Over a differentially closed field, an element of a
finitely generated differentially reduced algebra killed by every differential point is zero. -/
theorem eq_zero_of_forall_mem_differentialPoints {x : E}
    (h : ∀ χ ∈ differentialPoints C E, χ x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨χ, hχδ, hχx⟩ := exists_differentialAlgHom_ne_zero (C := C) (E := E) hx
  exact hχx (h χ hχδ)

end

end GaloisForLFunctions.HTGeometry
