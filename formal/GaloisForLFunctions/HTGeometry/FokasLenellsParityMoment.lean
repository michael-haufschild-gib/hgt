import GaloisForLFunctions.HTGeometry.FokasLenellsCompatibilityMoment
import GaloisForLFunctions.HTGeometry.SchwartzEulerOperator

/-!
# The precise parity compatibility law behind the origin cancellation

Writing q = e + o, with e even and o odd, the cubic term in equation (3.52)
is exactly the coupling integral of e² o'. Thus the displayed cancellation
is equivalent to a mass-coupling balance. Requiring it simultaneously for
q and its reflection is equivalent to separate vanishing of both invariants.
The proof uses the corpus's Euler parity rule, reflection invariance of
Lebesgue integration, and CCM Schwartz total-derivative cancellation.
-/

open MeasureTheory Complex Filter Topology
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem deriv_evenInitialPart_reflection (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (evenInitialPart q : ℝ → ℂ) (-x) = -deriv (evenInitialPart q : ℝ → ℂ) x :=
  deriv_neg_of_even_schwartz (evenInitialPart_reflection q) x

theorem initialParts_derivative_sum (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (q : ℝ → ℂ) x = deriv (evenInitialPart q : ℝ → ℂ) x+deriv (oddInitialPart q : ℝ → ℂ) x := by
  have hd := ((evenInitialPart q).hasDerivAt x).fun_add ((oddInitialPart q).hasDerivAt x)
  have he : (fun y => evenInitialPart q y+oddInitialPart q y) = (q : ℝ → ℂ) := by
    funext y
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f y) (initialParts_sum q)
  rw [he] at hd
  exact hd.deriv

theorem initialParts_reflected_product (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    q x*q (-x) = (evenInitialPart q x)^(2 : ℕ)-(oddInitialPart q x)^(2 : ℕ) := by
  simp only [evenInitialPart_apply,oddInitialPart_apply]
  ring

theorem schwartz_square_derivative_integrable (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => (f x)^(2 : ℕ)*deriv (g : ℝ → ℂ) x) := by
  have hi : Integrable (fun x : ℝ => mulS (mulS f f) (SchwartzMap.derivCLM ℂ ℂ g) x) :=
    (mulS (mulS f f) (SchwartzMap.derivCLM ℂ ℂ g)).integrable
  simpa only [mulS_apply,SchwartzMap.derivCLM_apply,pow_two] using hi

/-- The odd-square/even-derivative term is the parity-forbidden cubic contribution. -/
theorem integral_oddInitialPart_sq_mul_even_deriv (q : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (oddInitialPart q x)^(2 : ℕ)*deriv (evenInitialPart q : ℝ → ℂ) x = 0 := by
  have he : (fun x : ℝ => (oddInitialPart q (-x))^(2 : ℕ)*deriv (evenInitialPart q : ℝ → ℂ) (-x)) =
      fun x => -((oddInitialPart q x)^(2 : ℕ)*deriv (evenInitialPart q : ℝ → ℂ) x) := by
    funext x
    rw [oddInitialPart_reflection,deriv_evenInitialPart_reflection]
    ring
  have hi := integral_neg_eq_self
    (fun x : ℝ => (oddInitialPart q x)^(2 : ℕ)*deriv (evenInitialPart q : ℝ → ℂ) x) volume
  rw [he,integral_neg] at hi
  exact self_eq_neg.mp hi.symm

/-- The surviving nonlinear invariant couples the even amplitude to the odd derivative. -/
def parityCoupling (q : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, (evenInitialPart q x)^(2 : ℕ)*deriv (oddInitialPart q : ℝ → ℂ) x

theorem compatibilityCubic_eq_parityCoupling (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, q x*q (-x)*deriv (q : ℝ → ℂ) x) = parityCoupling q := by
  let e := evenInitialPart q
  let o := oddInitialPart q
  have he : (fun x : ℝ => q x*q (-x)*deriv (q : ℝ → ℂ) x) = fun x =>
      ((e x)^(2 : ℕ)*deriv (e : ℝ → ℂ) x+(e x)^(2 : ℕ)*deriv (o : ℝ → ℂ) x)-
        ((o x)^(2 : ℕ)*deriv (e : ℝ → ℂ) x+(o x)^(2 : ℕ)*deriv (o : ℝ → ℂ) x) := by
    funext x
    rw [initialParts_reflected_product,initialParts_derivative_sum]
    change (e x^(2 : ℕ)-o x^(2 : ℕ))*(deriv (e : ℝ → ℂ) x+deriv (o : ℝ → ℂ) x) = _
    ring
  have hl : Integrable (fun x : ℝ => (e x)^(2 : ℕ)*deriv (e : ℝ → ℂ) x+(e x)^(2 : ℕ)*deriv (o : ℝ → ℂ) x) :=
    (schwartz_square_derivative_integrable e e).add (schwartz_square_derivative_integrable e o)
  have hr : Integrable (fun x : ℝ => (o x)^(2 : ℕ)*deriv (e : ℝ → ℂ) x+(o x)^(2 : ℕ)*deriv (o : ℝ → ℂ) x) :=
    (schwartz_square_derivative_integrable o e).add (schwartz_square_derivative_integrable o o)
  rw [he,integral_sub hl hr,
    integral_add (schwartz_square_derivative_integrable e e) (schwartz_square_derivative_integrable e o),
    integral_add (schwartz_square_derivative_integrable o e) (schwartz_square_derivative_integrable o o),
    integral_cubic_derivative,integral_cubic_derivative,integral_oddInitialPart_sq_mul_even_deriv]
  simp only [zero_add,add_zero,sub_zero,parityCoupling,e,o]

/-- The exact survivor of the failed unrestricted cancellation is a mass-parity balance law. -/
theorem compatibilityMoment_parity_decomposition (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment q = (∫ x : ℝ, q x)-I*parityCoupling q := by
  rw [compatibilityMoment_eq,compatibilityCubic_eq_parityCoupling]

theorem compatibilityMoment_zero_iff_parity_balance (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment q = 0 ↔ (∫ x : ℝ, q x) = I*parityCoupling q := by
  rw [compatibilityMoment_parity_decomposition,sub_eq_zero]

/-- Explicit scaling exposes the linear and cubic orders of the missing initial compatibility condition. -/
theorem compatibilityMoment_smul (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    compatibilityMoment (c • q) = c*(∫ x : ℝ, q x)-I*c^(3 : ℕ)*parityCoupling q := by
  have hd (x : ℝ) : deriv ((c • q : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = c*deriv (q : ℝ → ℂ) x :=
    ((q.hasDerivAt x).const_mul c).deriv
  have he : (fun x : ℝ => (c • q) x*(c • q) (-x)*deriv ((c • q : SchwartzMap ℝ ℂ) : ℝ → ℂ) x) =
      fun x => c^(3 : ℕ)*(q x*q (-x)*deriv (q : ℝ → ℂ) x) := by
    funext x
    rw [hd]
    simp only [_root_.smul_apply,smul_eq_mul]
    ring
  rw [compatibilityMoment_eq,he,integral_const_mul,compatibilityCubic_eq_parityCoupling]
  simp only [_root_.smul_apply,smul_eq_mul]
  rw [integral_const_mul]
  ring

private theorem reflected_deriv (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (RHTower.negSchwartz' q : ℝ → ℂ) x = -deriv (q : ℝ → ℂ) (-x) := by
  change deriv (fun y => q (-y)) x = _
  exact deriv_comp_neg (q : ℝ → ℂ) x

theorem parityCoupling_reflection (q : SchwartzMap ℝ ℂ) :
    parityCoupling (RHTower.negSchwartz' q) = -parityCoupling q := by
  rw [← compatibilityCubic_eq_parityCoupling,← compatibilityCubic_eq_parityCoupling]
  have he : (fun x : ℝ => RHTower.negSchwartz' q x*RHTower.negSchwartz' q (-x)*
      deriv (RHTower.negSchwartz' q : ℝ → ℂ) x) =
        fun x => -(q (-x)*q (-(-x))*deriv (q : ℝ → ℂ) (-x)) := by
    funext x
    rw [reflected_deriv]
    simp only [RHTower.negSchwartz'_apply]
    ring
  rw [he,integral_neg,integral_neg_eq_self (fun x : ℝ => q x*q (-x)*deriv (q : ℝ → ℂ) x) volume]

/-- Reflection fixes mass and reverses the nonlinear coupling contribution. -/
theorem compatibilityMoment_reflection (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (RHTower.negSchwartz' q) = (∫ x : ℝ, q x)+I*parityCoupling q := by
  rw [compatibilityMoment_parity_decomposition,parityCoupling_reflection]
  change (∫ x : ℝ, q (-x))-I*(-parityCoupling q) = _
  rw [integral_neg_eq_self (q : ℝ → ℂ) volume]
  ring

theorem compatibilityMoment_add_reflection (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment q+compatibilityMoment (RHTower.negSchwartz' q) = 2*(∫ x : ℝ, q x) := by
  rw [compatibilityMoment_parity_decomposition,compatibilityMoment_reflection]
  ring

/-- Simultaneous cancellation for both reflected channels imposes two separate exact moment conditions. -/
theorem compatibilityMoment_both_zero_iff (q : SchwartzMap ℝ ℂ) :
    (compatibilityMoment q = 0 ∧ compatibilityMoment (RHTower.negSchwartz' q) = 0) ↔
      ((∫ x : ℝ, q x) = 0 ∧ parityCoupling q = 0) := by
  rw [compatibilityMoment_parity_decomposition,compatibilityMoment_reflection]
  constructor
  · rintro ⟨h1,h2⟩
    have hm : (∫ x : ℝ, q x) = 0 := by linear_combination (h1+h2)/2
    refine ⟨hm,?_⟩
    rw [hm,zero_add] at h2
    exact (mul_eq_zero.mp h2).resolve_left I_ne_zero
  · rintro ⟨hm,hp⟩
    simp [hm,hp]

/-- After explicit small-data normalization, compatibility still demands the same linear-cubic balance. -/
theorem compatibilityMoment_globalSmall (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (globalSmallScatteringPotential q) =
      (globalScatteringScale q : ℂ)*(∫ x : ℝ, q x)-
        I*(globalScatteringScale q : ℂ)^(3 : ℕ)*parityCoupling q :=
  compatibilityMoment_smul q _

end
end GaloisForLFunctions.HTGeometry.FokasLenells
