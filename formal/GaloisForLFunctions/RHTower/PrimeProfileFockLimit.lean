import GaloisForLFunctions.RHTower.CoherentKernelChart

/-!
# The prime-profile squarefree Fock limit

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(13p)`–`(13y)`.

The radial family `u ↦ ut` is only one line inside the complete normal experiment.  For an arbitrary
prime-scale profile `f` vanishing at the origin, put

`q_{p,x}(f) = p^{-1} e^{2 f(log p / log x)}`

and let `B_x(f,g)` be the Hellinger affinity of the corresponding product Bernoulli laws.  The same
mechanism as in the radial case — first-order cancellation in the parity digit, Mertens weak
convergence of the prime window, and a Tannery-dominated remainder — gives

`B_x(f,g) → K(f,g) = exp(-½ ∫₀¹ (e^{f(t)} - e^{g(t)})² dt/t)`.

The radial kernel is the specialization `f(t) = ut`, and the profile field is total in the
symmetric Fock space over `L²((0,1), dt/t)` because `G_{log(1+εφ)} = εφ`.
-/

open Filter Topology Set
open GaloisForLFunctions.HTGeometry

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The prime-scale profile nome `q_{p,x}(f) = p^{-1} e^{2 f(log p / log x)}`. -/
def profileNome (f : ℝ → ℝ) (N n : ℕ) : ℝ :=
  ((n : ℝ))⁻¹ * Real.exp (2 * f (Real.log n / Real.log N))

theorem profileNome_pos {f : ℝ → ℝ} {N n : ℕ} (hn : 2 ≤ n) : 0 < profileNome f N n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [profileNome]
  positivity

/-- The radial family is the linear profile. -/
theorem profileNome_linear (u : ℝ) (N n : ℕ) (hn : 2 ≤ n) :
    profileNome (fun t => u * t) N n = radialNome (u / Real.log N) n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [profileNome, radialNome_eq_exp hn]
  have hinv : ((n : ℝ))⁻¹ = Real.exp (-Real.log n) := by
    rw [Real.exp_neg, Real.exp_log hn0]
  rw [hinv, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem sqrt_profileNome {f : ℝ → ℝ} {N n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (profileNome f N n)
      = Real.sqrt ((n : ℝ))⁻¹ * Real.exp (f (Real.log n / Real.log N)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hinv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
  rw [profileNome, Real.sqrt_mul hinv0]
  congr 1
  rw [show (2 : ℝ) * f (Real.log n / Real.log N)
    = f (Real.log n / Real.log N) + f (Real.log n / Real.log N) by ring, Real.exp_add,
    ← sq, Real.sqrt_sq (Real.exp_nonneg _)]

/-- **The quadratic Hellinger displacement of a profile pair.** -/
theorem sq_sqrt_profileNome_sub {f g : ℝ → ℝ} {N n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt (profileNome f N n) - Real.sqrt (profileNome g N n)) ^ 2
      = (Real.exp (f (Real.log n / Real.log N)) - Real.exp (g (Real.log n / Real.log N))) ^ 2
        / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hinv : Real.sqrt ((n : ℝ))⁻¹ ^ 2 = ((n : ℝ))⁻¹ :=
    Real.sq_sqrt (by positivity)
  rw [sqrt_profileNome hn, sqrt_profileNome hn, ← mul_sub, mul_pow, hinv]
  ring

end

end RHTower
