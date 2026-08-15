import GaloisForLFunctions.HTGeometry.EntireSeriesEulerJet
import GaloisForLFunctions.HTGeometry.HighDegreeJetFreedom

/-!
# Coefficient windows inside a source

A coefficient sequence supported in a degree window `[N, N + n)` contributes to the jet-weighted
series exactly the polynomial jet of the window, so the free Euler jets of a high-degree window are
free increments of the jets of the source.  Two windows with disjoint degree ranges do not interfere,
which is what lets a source be built one window at a time inside a fixed coefficient box.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficient sequence of a degree window. -/
def windowSeq (N n : ℕ) (w : Fin n → ℂ) : ℕ → ℂ :=
  fun k => if h : N ≤ k ∧ k - N < n then w ⟨k - N, h.2⟩ else 0

theorem windowSeq_eq_zero_of_lt (N n : ℕ) (w : Fin n → ℂ) {k : ℕ} (hk : k < N) :
    windowSeq N n w k = 0 := by
  rw [windowSeq, dif_neg]
  omega

theorem windowSeq_eq_zero_of_ge (N n : ℕ) (w : Fin n → ℂ) {k : ℕ} (hk : N + n ≤ k) :
    windowSeq N n w k = 0 := by
  rw [windowSeq, dif_neg]
  omega

theorem windowSeq_apply_add (N n : ℕ) (w : Fin n → ℂ) (i : Fin n) :
    windowSeq N n w (N + (i : ℕ)) = w i := by
  have h : N ≤ N + (i : ℕ) ∧ N + (i : ℕ) - N < n := ⟨by omega, by omega⟩
  rw [windowSeq, dif_pos h]
  congr 1
  exact Fin.ext (by simp)

theorem norm_windowSeq_le {N n : ℕ} {w : Fin n → ℂ} {b : ℕ → ℝ} (hb : ∀ i : Fin n, ‖w i‖ ≤ b (N + i))
    (hb0 : ∀ k, 0 ≤ b k) (k : ℕ) : ‖windowSeq N n w k‖ ≤ b k := by
  rw [windowSeq]
  split
  · next h =>
      have := hb ⟨k - N, h.2⟩
      simpa [show N + (k - N) = k by omega] using this
  · simpa using hb0 k

/-! ### The jet series of a window -/

theorem polyEuler_sum {κ : Type*} (s : Finset κ) (p : κ → Polynomial ℂ) :
    polyEuler (∑ i ∈ s, p i) = ∑ i ∈ s, polyEuler (p i) := by
  rw [polyEuler, Polynomial.derivative_sum, Finset.mul_sum]
  rfl

theorem polyEuler_iterate_sum {κ : Type*} (s : Finset κ) (p : κ → Polynomial ℂ) (r : ℕ) :
    polyEuler^[r] (∑ i ∈ s, p i) = ∑ i ∈ s, polyEuler^[r] (p i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih,
        Finset.sum_congr rfl fun i (_ : i ∈ s) => Function.iterate_succ_apply' polyEuler r (p i)]
      exact polyEuler_sum s _

theorem polyEuler_iterate_windowLin (N n r : ℕ) (w : Fin n → ℂ) :
    polyEuler^[r] (windowLin N n w) =
      ∑ i : Fin n, Polynomial.monomial (N + (i : ℕ)) (((N + (i : ℕ) : ℕ) : ℂ) ^ r * w i) := by
  rw [show windowLin N n w = ∑ i : Fin n, Polynomial.monomial (N + (i : ℕ)) (w i) from
    windowLin_apply N n w, polyEuler_iterate_sum]
  exact Finset.sum_congr rfl fun i _ => polyEuler_iterate_monomial r (N + (i : ℕ)) (w i)

theorem eval_polyEuler_iterate_windowLin (N n r : ℕ) (w : Fin n → ℂ) (x : ℂ) :
    (polyEuler^[r] (windowLin N n w)).eval x =
      ∑ i : Fin n, ((N + (i : ℕ) : ℕ) : ℂ) ^ r * w i * x ^ (N + (i : ℕ)) := by
  rw [polyEuler_iterate_windowLin, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => Polynomial.eval_monomial

/-- **The jet-weighted series of a window is the polynomial jet of that window.** -/
theorem jetSeriesFun_windowSeq (N n r : ℕ) (w : Fin n → ℂ) (x : ℂ) :
    jetSeriesFun (windowSeq N n w) r x = (polyEuler^[r] (windowLin N n w)).eval x := by
  classical
  rw [jetSeriesFun, eval_polyEuler_iterate_windowLin]
  rw [tsum_eq_sum (s := Finset.Ico N (N + n)) (f := fun k : ℕ => (k : ℂ) ^ r * windowSeq N n w k
    * x ^ k) ?_]
  · rw [Finset.sum_Ico_eq_sum_range]
    rw [show N + n - N = n by omega]
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => ((N + i : ℕ) : ℂ) ^ r * windowSeq N n w (N + i) * x ^ (N + i)) n]
    exact Finset.sum_congr rfl fun i _ => by rw [windowSeq_apply_add]
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rcases lt_or_ge k N with h | h
    · rw [windowSeq_eq_zero_of_lt N n w h, mul_zero, zero_mul]
    · rw [windowSeq_eq_zero_of_ge N n w (by omega), mul_zero, zero_mul]

/-! ### Additivity in the coefficient sequence -/

theorem jetSeriesFun_add {c d : ℕ → ℂ} (r : ℕ) (x : ℂ)
    (hcs : Summable fun n : ℕ => (n : ℂ) ^ r * c n * x ^ n)
    (hds : Summable fun n : ℕ => (n : ℂ) ^ r * d n * x ^ n) :
    jetSeriesFun (fun n => c n + d n) r x = jetSeriesFun c r x + jetSeriesFun d r x := by
  rw [jetSeriesFun, jetSeriesFun, jetSeriesFun, ← Summable.tsum_add hcs hds]
  exact tsum_congr fun n => by ring

end

end GaloisForLFunctions.HTGeometry
