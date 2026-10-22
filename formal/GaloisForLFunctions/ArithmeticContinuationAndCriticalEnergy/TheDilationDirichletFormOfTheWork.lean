import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheQuotientIncidenceKernelIsIndefinite
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePositiveCoreOfTheDilationForm
import Mathlib.Algebra.Order.Chebyshev

/-!
# The dilation Dirichlet form of the signed work

The signed damping work pairs the source with its own prime dilations, and its sign is the open
obstruction of the continuation layer.  The dilation form has no diagonal, so it is a pure cross
term; polarising every cross term edgewise turns it into a *Dirichlet form on the dilation graph*,
whose vertices are the horizons, whose edges join `n` to `n / j` with conductance
`Λ(j) j^{-ε}/(n(n+1))`, and whose mass is the sum of the squares at the two endpoints of each edge:

`2 Q_ε(v) = M_ε(v) − J_ε(v)`   (`two_mul_rowDilationForm_eq`),

`M_ε(v) = Σ_n Σ_{j ≤ n} Λ(j) j^{-ε}(v(n)² + v(n/j)²)/(n(n+1))` the **edge mass** and
`J_ε(v) = Σ_n Σ_{j ≤ n} Λ(j) j^{-ε}(v(n) − v(n/j))²/(n(n+1))` the **dilation jump energy**.

Three consequences.  The sign criterion of the continuation layer becomes a *Poincaré inequality*
on that graph — the jump energy must not exceed the edge mass
(`rowDilationForm_nonneg_iff`, `riemannHypothesis_of_dilationPoincare`) — rather than a statement
about an indefinite kernel; the edge mass splits off an explicit **creation potential**, the
pronic average of the damped prime prefix `ψ_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε}` against `v²`, giving the
unconditional floor `2Q_ε(v) ≥ Σ_n v(n)² ψ_ε(n)/(n(n+1)) − J_ε(v)`
(`creationPotential_sub_dilationJumpEnergy_le`); and the form obeys the normal contraction of
Beurling–Deny theory, `Q_ε(v) ≤ Q_ε(|v|)` (`rowDilationForm_le_abs`), so the obstruction is
carried by the sign changes of the source and the extremal rows are maximally oscillating.

Finally the jump energy at a prime power telescopes along the dilation chain
`n → n/p → ⋯ → n/p^k`, with the exact composition `(n/p^i)/p = n/p^{i+1}`, so the whole energy is
controlled by the single-prime steps at a multiplicity cost
(`sq_sub_dilation_pow_le`): the Poincaré inequality on the dilation graph reduces to the primes.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The edge mass and the dilation jump energy -/

/-- The **edge mass** of the dilation graph: the squares at the two endpoints of every dilation
edge, weighted by the prime conductance and the pronic weight of the upper endpoint. -/
def dilationEdgeMass (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * (v n ^ 2 + v (n / j) ^ 2)) /
    ((n : ℝ) * ((n : ℝ) + 1))

/-- The **dilation jump energy**: the Dirichlet energy of the row along the dilation edges. -/
def dilationJumpEnergy (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * (v n - v (n / j)) ^ 2) /
    ((n : ℝ) * ((n : ℝ) + 1))

theorem dampedPrimeWeight_nonneg (ε : ℝ) (j : ℕ) : 0 ≤ dampedPrimeWeight ε j :=
  mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)

theorem dilationEdgeMass_nonneg (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    0 ≤ dilationEdgeMass ε T v := by
  refine Finset.sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine div_nonneg (Finset.sum_nonneg fun j _ => ?_) (by positivity)
  exact mul_nonneg (dampedPrimeWeight_nonneg ε j) (by positivity)

theorem dilationJumpEnergy_nonneg (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    0 ≤ dilationJumpEnergy ε T v := by
  refine Finset.sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine div_nonneg (Finset.sum_nonneg fun j _ => ?_) (by positivity)
  exact mul_nonneg (dampedPrimeWeight_nonneg ε j) (sq_nonneg _)

/-! ## §2. The Dirichlet identity -/

/-- **The dilation form is a Dirichlet form.**  Edgewise polarisation of the pure cross term:
twice the dilation form is the edge mass minus the dilation jump energy. -/
theorem two_mul_rowDilationForm_eq (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    2 * rowDilationForm ε T v = dilationEdgeMass ε T v - dilationJumpEnergy ε T v := by
  rw [rowDilationForm, dilationEdgeMass, dilationJumpEnergy, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_sub_div_same, ← Finset.sum_sub_distrib]
  have hterm : (∑ j ∈ Icc 1 n, (dampedPrimeWeight ε j * (v n ^ 2 + v (n / j) ^ 2) -
      dampedPrimeWeight ε j * (v n - v (n / j)) ^ 2)) =
      2 * (v n * ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hterm]
  ring

/-- **The sign criterion is a Poincaré inequality.**  The dilation form is nonnegative exactly when
the dilation jump energy is dominated by the edge mass. -/
theorem rowDilationForm_nonneg_iff (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    0 ≤ rowDilationForm ε T v ↔ dilationJumpEnergy ε T v ≤ dilationEdgeMass ε T v := by
  have h := two_mul_rowDilationForm_eq ε T v
  constructor
  · intro hQ; linarith
  · intro hP; linarith

/-! ## §3. The creation potential -/

/-- The **creation potential**: the pronic average of the damped prime prefix against `v²`.  It is
the part of the edge mass carried by the upper endpoint of every edge. -/
def dilationCreationPotential (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, v n ^ 2 * dampedPrimePrefix ε n / ((n : ℝ) * ((n : ℝ) + 1))

/-- The **fibre potential**: the part of the edge mass carried by the lower endpoint. -/
def dilationFibrePotential (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j) ^ 2) /
    ((n : ℝ) * ((n : ℝ) + 1))

/-- The edge mass splits into the creation potential and the fibre potential. -/
theorem dilationEdgeMass_eq (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    dilationEdgeMass ε T v =
      dilationCreationPotential ε T v + dilationFibrePotential ε T v := by
  rw [dilationEdgeMass, dilationCreationPotential, dilationFibrePotential,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_add_div_same, ← Finset.sum_add_distrib, dampedPrimePrefix, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem dilationFibrePotential_nonneg (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    0 ≤ dilationFibrePotential ε T v := by
  refine Finset.sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine div_nonneg (Finset.sum_nonneg fun j _ => ?_) (by positivity)
  exact mul_nonneg (dampedPrimeWeight_nonneg ε j) (sq_nonneg _)

/-- **The unconditional floor of the dilation form.**  The prime creation potential, an explicit
pronic average of the damped prime prefix, is available against the dilation jump energy. -/
theorem creationPotential_sub_dilationJumpEnergy_le (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    dilationCreationPotential ε T v - dilationJumpEnergy ε T v ≤
      2 * rowDilationForm ε T v := by
  rw [two_mul_rowDilationForm_eq, dilationEdgeMass_eq]
  have := dilationFibrePotential_nonneg ε T v
  linarith

/-! ## §4. The normal contraction -/

theorem dilationEdgeMass_abs (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    dilationEdgeMass ε T (fun n => |v n|) = dilationEdgeMass ε T v := by
  rw [dilationEdgeMass, dilationEdgeMass]
  exact Finset.sum_congr rfl fun n _ => by
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [sq_abs, sq_abs]

/-- The jump energy decreases under the modulus: `(|a| − |b|)² ≤ (a − b)²`. -/
theorem dilationJumpEnergy_abs_le (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    dilationJumpEnergy ε T (fun n => |v n|) ≤ dilationJumpEnergy ε T v := by
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (dampedPrimeWeight_nonneg ε j)
  have := abs_sub_abs_le_abs_sub (v n) (v (n / j))
  have h2 : |(|v n| - |v (n / j)|)| ≤ |v n - v (n / j)| := by
    rcases abs_cases (|v n| - |v (n / j)|) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact abs_sub_abs_le_abs_sub _ _
    · rw [h]
      have := abs_sub_abs_le_abs_sub (v (n / j)) (v n)
      rw [abs_sub_comm (v (n / j)) (v n)] at this
      linarith
  calc (|v n| - |v (n / j)|) ^ 2 = |(|v n| - |v (n / j)|)| ^ 2 := (sq_abs _).symm
    _ ≤ |v n - v (n / j)| ^ 2 := by
        exact pow_le_pow_left (abs_nonneg _) h2 2
    _ = (v n - v (n / j)) ^ 2 := sq_abs _

/-- **Normal contraction (Beurling–Deny) for the dilation form.**  Replacing the row by its modulus
never decreases the dilation form: the obstruction to the sign is carried by the sign changes of the
source, and the extremal rows are the maximally oscillating ones. -/
theorem rowDilationForm_le_abs (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) :
    rowDilationForm ε T v ≤ rowDilationForm ε T (fun n => |v n|) := by
  have h1 := two_mul_rowDilationForm_eq ε T v
  have h2 := two_mul_rowDilationForm_eq ε T (fun n => |v n|)
  have h3 := dilationEdgeMass_abs ε T v
  have h4 := dilationJumpEnergy_abs_le ε T v
  rw [h3] at h2
  linarith

/-! ## §5. The Poincaré criterion for the Riemann hypothesis -/

/-- **The receiver as a Poincaré inequality on the dilation graph.**  If at every damping below one
half and every horizon the dilation jump energy of the literal centred source is dominated by its
edge mass plus twice the explicit polar pairing, the Riemann hypothesis follows. -/
theorem riemannHypothesis_of_dilationPoincare
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      dilationJumpEnergy ε T (pmPowerDampedCenteredDivisorPrefix ε) ≤
        dilationEdgeMass ε T (pmPowerDampedCenteredDivisorPrefix ε) +
          2 * polarDilationCorrection ε T) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_nonneg_dilationForm_add_correction fun T ε hε hε2 => ?_
  have hid := two_mul_rowDilationForm_eq ε T (pmPowerDampedCenteredDivisorPrefix ε)
  have hform : dilationForm ε T = rowDilationForm ε T (pmPowerDampedCenteredDivisorPrefix ε) := rfl
  have := h T ε hε hε2
  rw [hform]
  linarith

/-! ## §6. Telescoping along the dilation chain -/

/-- The dilation chain composes exactly: one further step of the chain `n → n/p → n/p² → ⋯` is a
dilation by one more power. -/
theorem dilation_chain_step (n p i : ℕ) : n / p ^ i / p = n / p ^ (i + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- The jump along the chain telescopes. -/
theorem sub_dilation_pow_eq_sum (v : ℕ → ℝ) (n p k : ℕ) :
    v n - v (n / p ^ k) = ∑ i ∈ range k, (v (n / p ^ i) - v (n / p ^ (i + 1))) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring

/-- **Telescoping of the dilation jump at a prime power.**  The jump across `k` steps costs at most
`k` times the sum of the single-prime steps along the chain, so the Poincaré inequality on the
dilation graph reduces to the prime steps at an explicit multiplicity cost. -/
theorem sq_sub_dilation_pow_le (v : ℕ → ℝ) (n p k : ℕ) :
    (v n - v (n / p ^ k)) ^ 2 ≤
      k * ∑ i ∈ range k, (v (n / p ^ i) - v (n / p ^ (i + 1))) ^ 2 := by
  rw [sub_dilation_pow_eq_sum v n p k]
  have h := sq_sum_le_card_mul_sum_sq (s := range k)
    (f := fun i => v (n / p ^ i) - v (n / p ^ (i + 1)))
  simpa using h

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
