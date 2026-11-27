import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Substitution
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysIntegralLift

/-! # Complex lifts of substitutions between powered shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open MvPolynomial

variable {ι : Type*}

private abbrev Eval (x : ι → ℝ) := (aeval x : MvPolynomial ι ℤ →ₐ[ℤ] ℝ).toRingHom
private abbrev Relations (x : ι → ℝ) := RingHom.ker (Eval x)
private abbrev CoordinateRing (x : ι → ℝ) := MvPolynomial ι ℤ ⧸ Relations x
private abbrev point (x : ι → ℝ) := Ideal.Quotient.mk (Relations x)

/-- Adjoining the coordinate roots gives an integral injection of the two evaluation rings. -/
private def inclusion (x : ι → ℝ) (m : ℕ) :
    CoordinateRing (x^m) →+* CoordinateRing x :=
  Ideal.Quotient.lift _ ((point x).comp (expand m).toRingHom) (fun P h =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (show aeval x (expand m P)=0 by rw [aeval_expand]; exact h))

private theorem inclusion_injective (x : ι → ℝ) (m : ℕ) : Function.Injective (inclusion x m) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective v
  change point x (expand m P)=0 → point (x^m) P=0
  rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.Quotient.eq_zero_iff_mem]
  change aeval x (expand m P)=0 → aeval (x^m) P=0
  rw [aeval_expand]
  exact id

private theorem inclusion_integral (x : ι → ℝ) {m : ℕ} (hm : 0 < m) :
    (inclusion x m).IsIntegral := by
  let A := CoordinateRing (x^m)
  letI : Algebra A (CoordinateRing x) := (inclusion x m).toAlgebra
  have base (P : MvPolynomial ι ℤ) : IsIntegral A (point x (expand m P)) :=
    isIntegral_algebraMap (x := point (x^m) P)
  have root (i : ι) : IsIntegral A (point x (X i)) := by
    apply IsIntegral.of_pow hm
    simpa only [expand_X,map_pow] using base (X i)
  intro v
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective v
  change IsIntegral A (point x P)
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [expand_C] using base (C c)
  | add P Q p q => rw [map_add]; exact p.add q
  | mul_X P i p => rw [map_mul]; exact p.mul (root i)

/-- A specialization at the powered coordinates lifts to complex roots which
satisfy every original integral relation at once. -/
theorem lift_power_relations (x y : ι → ℝ) {m : ℕ} (hm : 0 < m)
    (inc : RingHom.ker (Eval (x^m)) ≤ RingHom.ker (Eval y)) :
    ∃ z : ι → ℂ, (∀ i, z i^m=(y i : ℂ)) ∧
      ∀ P : MvPolynomial ι ℤ, aeval x P=0 → aeval z P=0 := by
  let dst := Complex.ofRealHom.comp (Eval y)
  let φ : CoordinateRing (x^m) →+* ℂ := Ideal.Quotient.lift _ dst (fun P hp => by
    change ((Eval y P : ℝ) : ℂ)=0
    exact_mod_cast (show Eval y P=0 from inc hp))
  obtain ⟨ψ,extending⟩ := RHTower.deningerHom_exists_extension_of_ringHom_isIntegral (inclusion x m)
    (inclusion_integral x hm) (inclusion_injective x m) φ
  let z (i : ι) := ψ (point x (X i))
  have eval : (aeval z : MvPolynomial ι ℤ →ₐ[ℤ] ℂ).toRingHom=ψ.comp (point x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change aeval z (C c)=ψ (point x (C c))
      rw [aeval_C,show (C c : MvPolynomial ι ℤ)=(c : MvPolynomial ι ℤ) by simp,map_intCast,map_intCast]
      rfl
    · intro i
      exact aeval_X z i
  refine ⟨z,fun i => ?_,fun P hp => ?_⟩
  · have law := RingHom.congr_fun extending (point (x^m) (X i))
    change ψ (point x (expand m (X i)))=((aeval y (X i) : ℝ) : ℂ) at law
    simpa only [z,expand_X,map_pow,aeval_X] using law
  · change (aeval z : MvPolynomial ι ℤ →ₐ[ℤ] ℂ).toRingHom P=0
    rw [eval,RingHom.comp_apply,show point x P=0 from Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]

#print axioms lift_power_relations

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
