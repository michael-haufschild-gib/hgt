/-
# The order-shift identity for the regularized determinant of a power-trace sequence

Lowering the regularization order from `p` to `q` reinstates exactly the finitely many trace terms
between the two orders.  On the operator side this is the classical transition identity
`det_q = det_p · exp(−∑_{q ≤ j < p} Tr(A^j) z^j / j)`; on the power-trace side it is a plain split
of one absolutely convergent series into its head and its tail.

Main results:
* `tracePowerTerm` — the term of the regularized exponent at one exponent.
* `summable_tracePowerTerm_add` — the tail from any order below `p` is summable.
* `tracePowerDetExp_order_shift` — the exponent splits as head plus tail.
* `tracePowerDet_order_shift` — **the transition identity between two regularization orders**.
-/
import GaloisForLFunctions.HTGeometry.TracePowerDeterminant

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The term of the regularized exponent at exponent `m`. -/
def tracePowerTerm (τ : ℕ → ℂ) (z : ℂ) (m : ℕ) : ℂ := z ^ m / (m : ℂ) * τ m

theorem tracePowerDetExp_eq_tsum_tracePowerTerm (p : ℕ) (τ : ℕ → ℂ) (z : ℂ) :
    tracePowerDetExp p τ z = ∑' k : ℕ, tracePowerTerm τ z (k + p) := rfl

/-- The regularized exponent from any order at most `p` converges under the geometric bound at
order `p`: the two series differ in finitely many terms. -/
theorem summable_tracePowerTerm_add {p : ℕ} (hp : 0 < p) {τ : ℕ → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hbound : ∀ k : ℕ, ‖τ (k + p)‖ ≤ S * B ^ k)
    {z : ℂ} (hz : ‖z‖ * B < 1) {q : ℕ} (hqp : q ≤ p) :
    Summable fun k : ℕ => tracePowerTerm τ z (k + q) := by
  have hbase : Summable fun k : ℕ => tracePowerTerm τ z (k + p) :=
    summable_tracePowerDetExp hp hB1 hbound hz
  refine (summable_nat_add_iff (f := fun k : ℕ => tracePowerTerm τ z (k + q)) (p - q)).mp ?_
  refine hbase.congr fun k => ?_
  have : k + (p - q) + q = k + p := by omega
  rw [this]

/-- **The regularized exponent splits at any lower order** into the finitely many terms between
the two orders and the tail from the higher order. -/
theorem tracePowerDetExp_order_shift {p : ℕ} (hp : 0 < p) {τ : ℕ → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hbound : ∀ k : ℕ, ‖τ (k + p)‖ ≤ S * B ^ k)
    {z : ℂ} (hz : ‖z‖ * B < 1) {q : ℕ} (hqp : q ≤ p) :
    tracePowerDetExp q τ z
      = (∑ m ∈ Finset.Ico q p, tracePowerTerm τ z m) + tracePowerDetExp p τ z := by
  have hsum : Summable fun k : ℕ => tracePowerTerm τ z (k + q) :=
    summable_tracePowerTerm_add hp hB1 hbound hz hqp
  have hsplit := hsum.sum_add_tsum_nat_add (p - q)
  have htail : (∑' i : ℕ, tracePowerTerm τ z (i + (p - q) + q)) = tracePowerDetExp p τ z := by
    rw [tracePowerDetExp_eq_tsum_tracePowerTerm]
    refine tsum_congr fun i => ?_
    have : i + (p - q) + q = i + p := by omega
    rw [this]
  have hhead : (∑ i ∈ Finset.range (p - q), tracePowerTerm τ z (i + q))
      = ∑ m ∈ Finset.Ico q p, tracePowerTerm τ z m := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
  rw [tracePowerDetExp_eq_tsum_tracePowerTerm, ← hsplit, hhead, htail]

/-- **The transition identity between two regularization orders.**  Lowering the order from `p` to
`q` multiplies the determinant by the exponential of the finitely many reinstated trace terms. -/
theorem tracePowerDet_order_shift {p : ℕ} (hp : 0 < p) {τ : ℕ → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hbound : ∀ k : ℕ, ‖τ (k + p)‖ ≤ S * B ^ k)
    {z : ℂ} (hz : ‖z‖ * B < 1) {q : ℕ} (hqp : q ≤ p) :
    tracePowerDet q τ z
      = tracePowerDet p τ z * Complex.exp (-∑ m ∈ Finset.Ico q p, tracePowerTerm τ z m) := by
  rw [tracePowerDet, tracePowerDet, tracePowerDetExp_order_shift hp hB1 hbound hz hqp,
    neg_add, Complex.exp_add]
  ring

end

end GaloisForLFunctions.HTGeometry
