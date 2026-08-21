import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Jordan triangular form of Connes' generalized eigenvectors

Appendix I (32)(34) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

At a zero of `L(χ₀, ·)` of order `> a`, the orthogonal of the range of the periodization map `E`
inside `L²_{-δ}(C_k)` contains the vector

  `η_{t,a}(x) = χ₀(x) |x|^{it} (log |x|)^a`,

and the transposed representation acts on these by the *triangular* rule Appendix I (34)

  `W(λ)^t η_{t,a} = ∑_{b=0}^{a} C(a,b) λ^{it} (log λ)^b η_{t,a-b}`.

This is why `D` fails to be semisimple at a multiple zero, which Connes points out is compatible
with the almost-unitarity §III (22) but not with skew-symmetry.  In the logarithmic coordinate
`u = log |x|` the rule is exactly the binomial theorem, proved here without hypotheses.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Finset

/-- Connes' generalized eigenvector in the logarithmic coordinate `u = log |x|`, stripped of the
character factor: `η_{t,a}(u) = e^{itu} u^a`. -/
def connesJordanMode (t : ℝ) (a : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (t * u * Complex.I) * (u : ℂ) ^ a

/-- **Appendix I (34).**  The translation action on the generalized eigenvectors is triangular with
binomial coefficients. -/
theorem connesJordanMode_translate (t : ℝ) (a : ℕ) (v u : ℝ) :
    connesJordanMode t a (v + u)
      = ∑ b ∈ range (a + 1),
          ((a.choose b : ℂ) * (Complex.exp (t * v * Complex.I) * (v : ℂ) ^ b)) *
            connesJordanMode t (a - b) u := by
  have hexp : Complex.exp ((t : ℂ) * ((v : ℝ) + (u : ℝ)) * Complex.I)
      = Complex.exp ((t : ℂ) * v * Complex.I) * Complex.exp ((t : ℂ) * u * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have hbin : ((v : ℂ) + (u : ℂ)) ^ a
      = ∑ b ∈ range (a + 1), (v : ℂ) ^ b * (u : ℂ) ^ (a - b) * (a.choose b : ℂ) := add_pow _ _ _
  simp only [connesJordanMode]
  push_cast
  rw [hexp, hbin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Appendix I (34), multiplicative coordinate.**  In the original variable `x` and for a positive
scaling `λ`, the same rule reads `η_{t,a}(λ x) = ∑_b C(a,b) (log λ)^b λ^{it} η_{t,a-b}(x)`. -/
theorem connesJordanMode_scale (t : ℝ) (a : ℕ) {lam x : ℝ} (hl : lam ≠ 0) (hx : x ≠ 0) :
    connesJordanMode t a (Real.log |lam * x|)
      = ∑ b ∈ range (a + 1),
          ((a.choose b : ℂ) *
            (Complex.exp (t * Real.log |lam| * Complex.I) * (Real.log |lam| : ℂ) ^ b)) *
            connesJordanMode t (a - b) (Real.log |x|) := by
  have hlog : Real.log |lam * x| = Real.log |lam| + Real.log |x| := by
    rw [abs_mul, Real.log_mul (abs_ne_zero.mpr hl) (abs_ne_zero.mpr hx)]
  rw [hlog]
  exact connesJordanMode_translate t a _ _

end

end GaloisForLFunctions.RHTower
