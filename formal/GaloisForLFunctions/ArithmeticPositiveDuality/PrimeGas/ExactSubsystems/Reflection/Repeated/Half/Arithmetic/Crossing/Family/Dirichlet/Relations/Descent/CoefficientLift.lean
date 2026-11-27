import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.ShellPhases

/-! # Simultaneous specialization of all algebraic-integer shell coefficients -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Finset Polynomial

abbrev ShellIntegers := integralClosure ℤ ℂ

/-- A characteristic-zero specialization is injective on algebraic integers:
each nonzero algebraic integer divides a nonzero rational integer. -/
theorem coefficient_injective (ρ : ShellIntegers →+* ℂ) : Function.Injective ρ := by
  apply (injective_iff_map_eq_zero ρ).mpr
  intro x zero
  by_contra nz
  obtain ⟨b,hb,y,eq⟩ := (integralClosure.isIntegral x).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_iff_ne_zero.mpr nz)
  have h := congrArg ρ eq
  change ρ (b : ShellIntegers)=ρ (x*y) at h
  rw [map_intCast,map_mul,zero,zero_mul,Int.cast_eq_zero] at h
  exact hb h

/-- Images of a fixed coefficient lie in one finite set of complex roots. -/
noncomputable def coefficientRoots (c : ShellIntegers) : Finset ℂ :=
  ((minpoly ℤ c).map (algebraMap ℤ ℂ)).roots.toFinset

theorem coefficient_mem (ρ : ShellIntegers →+* ℂ) (c : ShellIntegers) : ρ c ∈ coefficientRoots c := by
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots_map_of_injective (Int.cast_injective (α := ℂ))
    (minpoly.ne_zero (integralClosure.isIntegral c))).mpr
  change Polynomial.aeval (ρ.toIntAlgHom c) (minpoly ℤ c)=0
  rw [Polynomial.aeval_algHom_apply,minpoly.aeval,map_zero]

/-- One embedding of all algebraic-integer coefficients accompanies the shell
phases. It preserves every finite linear relation at the source at once. -/
theorem coefficient_specialization {m : ℕ} {t v : ℝ} (h : TorsionSpecialization m t v) :
    ∃ (ρ : ShellIntegers →+* ℂ) (ω : ℕ+ → ℂ), (∀ n, (ω n)^m=1) ∧
      ∀ {ι : Type} [Fintype ι] (a : ι → ℕ+) (c : ι → ShellIntegers),
        (∑ i, (c i : ℂ)*(shellPower t (a i) : ℂ))=0 →
        (∑ i, ρ (c i)*ω (a i)*(shellPower v (a i) : ℂ))=0 := by
  obtain ⟨e,ω,unit,atoms,keep⟩ := twisted_evaluation h
  let src := (IsScalarTower.toAlgHom ℤ ℝ ℂ).comp (value t)
  let A := src.range
  let g : PolynomialRing →ₐ[ℤ] A := src.rangeRestrict
  have onto : Function.Surjective g := src.rangeRestrict_surjective
  have inc : RingHom.ker g.toRingHom ≤ RingHom.ker e.toRingHom := by
    intro P hp
    apply keep
    apply Complex.ofReal_eq_zero.mp
    exact congrArg ((↑) : A → ℂ) (show g P=0 from hp)
  let φ := AlgHom.liftOfSurjective g onto e inc
  let B := integralClosure A ℂ
  have integ : (algebraMap A B).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  have inj : Function.Injective (algebraMap A B) := fun _ _ eq =>
    Subtype.ext (congrArg ((↑) : B → ℂ) eq)
  obtain ⟨ψ,agree⟩ := RHTower.deningerHom_exists_extension_of_ringHom_isIntegral
    (algebraMap A B) integ inj φ.toRingHom
  let j : ShellIntegers →+* B :=
    { toFun := fun x => ⟨(x : ℂ),IsIntegral.tower_top (A := A) x.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  have coeff (x : ShellIntegers) : (j x : ℂ)=(x : ℂ) := rfl
  let z (n : ℕ+) := algebraMap A B (g (atom n))
  have source (n : ℕ+) : (z n : ℂ)=(shellPower t n : ℂ) := by
    change ((value t (atom n) : ℝ) : ℂ)=_
    rw [value_atom,← shellPower_exp]
  have target (n : ℕ+) : ψ (z n)=ω n*(shellPower v n : ℂ) :=
    (RingHom.congr_fun agree (g (atom n))).trans
      ((AlgHom.liftOfSurjective_apply g onto e inc (atom n)).trans (atoms n))
  refine ⟨ψ.comp j,ω,unit,?_⟩
  intro ι inst a c rel
  have lifted : (∑ i, j (c i)*z (a i))=0 := by
    apply Subtype.ext
    change B.val (∑ i, j (c i)*z (a i))=0
    simpa only [map_sum,map_mul,Subalgebra.val_apply,source,coeff] using rel
  have eq := congrArg ψ lifted
  simpa only [map_sum,map_mul,target,map_zero,RingHom.comp_apply,mul_assoc] using eq

#print axioms coefficient_injective
#print axioms coefficient_specialization

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
