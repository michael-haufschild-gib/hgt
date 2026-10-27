import GaloisForLFunctions.ArithmeticIntersectionTheory.TheLocalFormsDoNotSum

/-!
# The finite intersection is gauge blind

A **real sign twin** of `ζ` replaces `Λ` by `εΛ`, where `ε` is completely multiplicative on positive
integers with `ε(n)² = 1` (a point of order two of the gauge torus `∏_p {±1}`); Liouville's
`λ(n) = (−1)^{Ω(n)}`, with twin `ζ(2s)/ζ(s)`, is one of them. Its prime kernel is
`P^ε(m, n) = ε(n/m) Λ(n/m) (n/m)^{−1/2}` on `m ∣ n` (`signTwistKernel`).

* **Gauge law** (`signTwistKernel_eq`): `P^ε(m, n) = ε(m) ε(n) P(m, n)`, because `ε(n/m) = ε(m) ε(n)`.
* **Unitary equivalence** (`signTwistForm_eq`): `Σ x_m x_n P^ε(m,n) = Σ (εx)_m (εx)_n P(m,n)`, and
  `|εx| = |x|`. Every twin's prime form is ζ's prime form in the gauge `x ↦ εx`; the two have the same
  spectrum, the same local bounds and the same unboundedness, along `ε(n) n^{−1/2}` for the twin.
* **Liouville** (`liouville_mul`, `liouville_sq`): `λ` is such a gauge.

So no statement about the finite intersection pairing alone — local or global, a bound or a sign —
separates `ζ` from its sign twins. Selectivity has to come from the parts of Weil's form that the
gauge moves: the pole term `(Σ x_n √n)(Σ x_n/√n)` and the archimedean place.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-- A **real sign gauge**: completely multiplicative on positive integers, with values `±1`. -/
structure IsSignGauge (ε : ℕ → ℝ) : Prop where
  mul : ∀ a b, 0 < a → 0 < b → ε (a * b) = ε a * ε b
  sq_eq_one : ∀ n, 0 < n → ε n ^ 2 = 1

/-- The prime kernel of the sign twin `εΛ`. -/
def signTwistKernel (ε : ℕ → ℝ) (m n : ℕ) : ℝ :=
  if m ∣ n ∧ m ≠ n then ε (n / m) * Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)
  else if n ∣ m ∧ n ≠ m then ε (m / n) * Λ (m / n) / Real.sqrt ((m / n : ℕ) : ℝ) else 0

/-- `ε(n/m) = ε(m) ε(n)` for `m ∣ n`. -/
theorem IsSignGauge.div_eq {ε : ℕ → ℝ} (h : IsSignGauge ε) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ∣ n) : ε (n / m) = ε m * ε n := by
  have hq : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) hm
  have e := h.mul m (n / m) hm hq
  rw [Nat.mul_div_cancel' hmn] at e
  rw [e, ← mul_assoc, show ε m * ε m = 1 by rw [← pow_two, h.sq_eq_one m hm], one_mul]

/-- **The gauge law** `P^ε(m, n) = ε(m) ε(n) P(m, n)`. -/
theorem signTwistKernel_eq {ε : ℕ → ℝ} (h : IsSignGauge ε) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    signTwistKernel ε m n = ε m * ε n * weilPrimeKernel m n := by
  unfold signTwistKernel weilPrimeKernel
  split_ifs with h1 h2
  · rw [h.div_eq hm hn h1.1]; ring
  · rw [h.div_eq hn hm h2.1]; ring
  · ring

/-- **Every sign twin's prime form is ζ's prime form in the gauge `x ↦ εx`.** -/
theorem signTwistForm_eq {ε : ℕ → ℝ} (h : IsSignGauge ε) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (x : ℕ → ℝ) :
    ∑ m ∈ S, ∑ n ∈ S, x m * x n * signTwistKernel ε m n = primeForm S (fun n => ε n * x n) := by
  unfold primeForm
  refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
  rw [signTwistKernel_eq h (hS m hm) (hS n hn)]
  ring

/-- The gauge preserves the mass: `|εx|² = |x|²`. -/
theorem sum_sq_gauge {ε : ℕ → ℝ} (h : IsSignGauge ε) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (x : ℕ → ℝ) : ∑ n ∈ S, (ε n * x n) ^ 2 = ∑ n ∈ S, x n ^ 2 := by
  refine sum_congr rfl fun n hn => ?_
  rw [mul_pow, h.sq_eq_one n (hS n hn), one_mul]

/-- **The sign twins share the unboundedness of the prime form**: no constant bounds the twisted
prime form by the mass. -/
theorem not_exists_signTwistForm_le {ε : ℕ → ℝ} (h : IsSignGauge ε) :
    ¬ ∃ C : ℝ, ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
      ∑ m ∈ S, ∑ n ∈ S, x m * x n * signTwistKernel ε m n ≤ C * ∑ n ∈ S, x n ^ 2 := by
  rintro ⟨C, hC⟩
  refine not_exists_primeForm_le ⟨C, fun S x hS => ?_⟩
  have hS' : ∀ n ∈ S, 0 < n := fun n hn => Nat.pos_of_ne_zero (hS n hn)
  have hεε : ∀ n ∈ S, ε n * (ε n * x n) = x n := fun n hn => by
    rw [← mul_assoc, ← pow_two, h.sq_eq_one n (hS' n hn), one_mul]
  have e := hC S (fun n => ε n * x n) hS'
  rw [signTwistForm_eq h S hS', sum_sq_gauge h S hS'] at e
  have hx : primeForm S (fun n => ε n * (ε n * x n)) = primeForm S x := by
    unfold primeForm
    exact sum_congr rfl fun m hm => sum_congr rfl fun n hn => by
      dsimp only
      rw [hεε m hm, hεε n hn]
  rw [hx] at e
  exact e

/-! ### Liouville's gauge -/

/-- Liouville's function `λ(n) = (−1)^{Ω(n)}`. -/
def liouville (n : ℕ) : ℝ := (-1) ^ ArithmeticFunction.cardFactors n

theorem liouville_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    liouville (a * b) = liouville a * liouville b := by
  rw [liouville, ArithmeticFunction.cardFactors_mul ha.ne' hb.ne', pow_add]; rfl

theorem liouville_sq (n : ℕ) : liouville n ^ 2 = 1 := by
  rw [liouville, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem isSignGauge_liouville : IsSignGauge liouville :=
  ⟨fun _ _ ha hb => liouville_mul ha hb, fun n _ => liouville_sq n⟩

/-- **Liouville's twin**: its prime kernel `λΛ(n/m)(n/m)^{−1/2}` is `λ(m) λ(n) P(m, n)`. -/
theorem liouvilleKernel_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    signTwistKernel liouville m n = liouville m * liouville n * weilPrimeKernel m n :=
  signTwistKernel_eq isSignGauge_liouville hm hn

end GaloisForLFunctions.ArithmeticIntersectionTheory
