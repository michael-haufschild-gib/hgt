import GaloisForLFunctions.HTGeometry.QuantumChannels.PolynomialJumpCommutators
import GaloisForLFunctions.HTGeometry.SchwartzCanonicalCommutation

/-!
# Exact polynomial jump heating on Schwartz space

For physical momentum P = −i d/dx and Q = x, a real polynomial jump has
adjoint dissipator −[f(P),[f(P),·]]/2. It sends Q² to f'(P)² and kills
every polynomial in P, Q itself, and QP+PQ. These double-commutator
identities extend algebraically to complex polynomial coefficients.
-/

noncomputable section
namespace GaloisForLFunctions.PolynomialJump.Schwartz

open Polynomial Complex
open scoped SchwartzMap FourierTransform
abbrev Op := 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)
abbrev P : Op := SchwartzMap.momentumCLM
abbrev Q : Op := mulXCLM

/-- Polynomial functional calculus for physical momentum on Schwartz space. -/
def momentum : ℂ[X] →ₐ[ℂ] Op := aeval P

/-- Double commutator giving the adjoint noise generator for real jump
polynomials, in units ℏ = 1. -/
def dissipator (f : ℂ[X]) (B : Op) := (-1/2:ℂ) • bracket (momentum f) (bracket (momentum f) B)

private theorem ccr : bracket Q P = I • (1:Op) := schwartz_position_momentum_operatorCCR

/-- Polynomial identities in physical momentum can be tested on Schwartz space. -/
theorem momentum_injective : Function.Injective momentum := by
  letI : Nontrivial (𝓢(ℝ, ℂ)) := ⟨⟨hermiteSchwartz 0,0,by
    intro h
    apply hermiteSchwartz_toLp_ne_zero 0
    simp [h]⟩⟩
  exact canonical_aeval_injective I_ne_zero ccr

private theorem jump_position (f : ℂ[X]) : bracket (momentum f) Q = (-I) • momentum f.derivative := by
  rw [neg_smul,← conjugate_polynomial ccr]
  unfold bracket
  exact (neg_sub _ _).symm

private theorem commute_polynomials (f g : ℂ[X]) : Commute (momentum f) (momentum g) :=
  (Commute.all f g).map momentum.toRingHom

private theorem annihilate_momentum (f g : ℂ[X]) : bracket (momentum f) (momentum g) = 0 :=
  sub_eq_zero.mpr (commute_polynomials f g)

private theorem bracket_smul (F B : Op) (k : ℂ) : bracket F (k • B) = k • bracket F B := by
  simp [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]

/-- The nth position power has vanishing (n+1)st noise commutator. The previous
commutator is exactly n! times the nth power of the differentiated jump. -/
theorem position_power (f : ℂ[X]) (n : ℕ) :
    (bracket (momentum f))^[n] (Q^n) = n.factorial • ((-I) • momentum f.derivative)^n ∧
    (bracket (momentum f))^[n+1] (Q^n) = 0 := by
  simpa only [momentum,map_mul,aeval_C,← Algebra.smul_def] using polynomial_highest ccr f n

/-- Position-square diffusion for every polynomial jump; equality is between Schwartz operators. -/
theorem position_heating (f : ℂ[X]) : dissipator f (Q^2) = momentum (f.derivative^2) := by
  have he := (position_power f 2).1
  change bracket (momentum f) (bracket (momentum f) (Q^2)) = _ at he
  rw [dissipator,he,map_pow]
  simp only [Nat.factorial_succ,Nat.factorial_zero,mul_one,pow_two,smul_mul_assoc,mul_smul_comm,
    smul_smul,two_nsmul,← two_smul ℂ,smul_smul]
  norm_num

/-- The adjoint jump conserves the full momentum algebra, mean position,
and the symmetrized position–momentum observable. -/
theorem conserved_observables (f g : ℂ[X]) :
    dissipator f (momentum g) = 0 ∧ dissipator f Q = 0 ∧
      dissipator f (Q*P+P*Q) = 0 := by
  have hp : bracket (momentum f) P = 0 := by
    simpa [momentum] using annihilate_momentum f Polynomial.X
  have hq : bracket (momentum f) (bracket (momentum f) Q) = 0 := by
    rw [jump_position,bracket_smul,annihilate_momentum,smul_zero]
  refine ⟨by simp [dissipator,annihilate_momentum,bracket],by rw [dissipator,hq,smul_zero],?_⟩
  simp only [dissipator,bracket_add,bracket_mul,hp,hq,zero_mul,mul_zero,add_zero,
    zero_add,smul_zero]

/-- The least momentum degree representing the noise correction to Q² is twice
the predecessor of the jump degree. -/
theorem heating_order (f : ℂ[X]) (d : ℕ) :
    (∃ g : ℂ[X], g.natDegree ≤ d ∧ dissipator f (Q^2) = momentum g) ↔
      2*(f.natDegree-1) ≤ d := by
  rw [position_heating]
  constructor
  · rintro ⟨g,hg,he⟩
    rw [← momentum_injective he,natDegree_pow,natDegree_derivative] at hg
    exact hg
  · intro hd
    exact ⟨_,by rwa [natDegree_pow,natDegree_derivative],rfl⟩

/-- Every polynomial representative of the quartic model's heating has degree six. -/
theorem quartic_heating :
    dissipator (Polynomial.X^4) (Q^2) = (16:ℂ) • P^6 ∧
      ¬ ∃ g : ℂ[X], g.natDegree ≤ 5 ∧ dissipator (Polynomial.X^4) (Q^2) = momentum g := by
  constructor
  · rw [position_heating]
    have hp : ((Polynomial.X^4 : ℂ[X]).derivative)^2 = C 16 * Polynomial.X^6 := by
      simp only [derivative_X_pow]
      norm_num
      ring
    rw [hp,map_mul,map_pow,momentum,aeval_C,aeval_X,Algebra.smul_def]
  · rw [heating_order]
    norm_num

end GaloisForLFunctions.PolynomialJump.Schwartz
