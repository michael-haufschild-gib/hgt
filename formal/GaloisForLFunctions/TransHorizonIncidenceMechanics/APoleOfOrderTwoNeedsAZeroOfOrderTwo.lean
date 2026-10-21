import GaloisForLFunctions.TransHorizonIncidenceMechanics.FinitePerturbationsOfTheSmoothPowerAreDecidedAtThePole

/-!
# A pole of order two needs a zero of order two

Let `q ≥ 0` drift like `n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε} log n` (a double pole at `s = 1 − ε`, as for
`log(d) d^{-ε}`), and let `k` be a kernel on `[1, J]` with Dirichlet polynomial `K`. The Mellin pairing
of the drift now has order `δ^{-2}`:

`Φ_q(1 − ε + δ) ≤ −(κσ/2) ((2/δ²)(M^{-δ} − 2/3) − log 2/δ)`,

from `log m ≥ (2/δ)(1 − m^{-δ/2})` and the tail bounds of `Σ m^{-1-δ}` and `Σ m^{-1-3δ/2}`. Against the
receiver bound `O(δ^{-1/2})` this forces **both `K(1 − ε) = 0` and `K'(1 − ε) = 0`** whenever the
receiver of `k ⋆ q` is bounded: if `K(1 − ε) ≠ 0` the product `K(σ)Φ_q(σ)` has order `δ^{-2}`, and if
`K(1 − ε) = 0 ≠ K'(1 − ε)` it still has order `δ^{-1}` since `K(σ) ≈ K'(1 − ε) δ`.

So the receiver reads the order of the pole: a double pole is repaired only by a double zero, and the
separating observables are the first two Taylor coefficients `Σ_j k(j) j^{-(1−ε)}` and
`Σ_j k(j) log j · j^{-(1−ε)}` of the kernel at the pole. In particular the Fermi kernel
`δ₁ − 2^{1−ε}δ₂`, which pays `d^{-ε}`, never pays `log(d) d^{-ε}` (its slope at the pole is `log 2`).
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The slope of the kernel at the pole, `−K'(1 − ε) = Σ_j k(j) log j · j^{-(1−ε)}`. -/
def poleSlope (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) : ℝ := ∑ j ∈ Icc 1 J, k j * Real.log j * (j : ℝ) ^ (-(1 - ε))

/-- **The logarithmic sum near the pole**: for `M ≥ 2` and `0 < δ`,
`Σ_{m ≥ M} log m · m^{-1-δ} ≥ (2/δ²)(M^{-δ} − 2/3)`. -/
theorem tsum_log_mul_rpow_ge {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    (2 / δ ^ 2) * ((M : ℝ) ^ (-δ) - 2 / 3) ≤
      ∑' k : ℕ, Real.log ((M : ℝ) + k) * ((M : ℝ) + k) ^ (-δ - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  have hs1 := HTGeometry.summable_shift_rpow (q := -δ) (by linarith) N
  have hs2 := HTGeometry.summable_shift_rpow (q := -(3 * δ / 2)) (by linarith) N
  have hlow := HTGeometry.tsum_shift_rpow_ge (q := -δ) (by linarith) N
  have hup := HTGeometry.tsum_shift_rpow_le (q := -(3 * δ / 2)) (by linarith) hN
  rw [neg_neg] at hlow hup
  have hN1 : ((N : ℝ)) ^ (-(3 * δ / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
  -- `log x ≥ (2/δ)(1 − x^{-δ/2})`
  have hterm : ∀ k : ℕ, (2 / δ) * (((N : ℝ) + 1 + k) ^ (-δ - 1) - ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1)) ≤
      Real.log (((N + 1 : ℕ) : ℝ) + k) * (((N + 1 : ℕ) : ℝ) + k) ^ (-δ - 1) := fun k => by
    push_cast
    set x : ℝ := (N : ℝ) + 1 + k
    have hx : 0 < x := by positivity
    have hlog : (2 / δ) * (1 - x ^ (-(δ / 2))) ≤ Real.log x := by
      have h := Real.one_sub_inv_le_log_of_pos (Real.rpow_pos_of_pos hx (δ / 2))
      rw [Real.log_rpow hx, ← Real.rpow_neg hx.le] at h
      calc (2 / δ) * (1 - x ^ (-(δ / 2))) ≤ (2 / δ) * (δ / 2 * Real.log x) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = Real.log x := by field_simp
    have hsplit : x ^ (-(3 * δ / 2) - 1) = x ^ (-(δ / 2)) * x ^ (-δ - 1) := by
      rw [← Real.rpow_add hx]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ x ^ (-δ - 1) := Real.rpow_nonneg hx.le _
    calc (2 / δ) * (x ^ (-δ - 1) - x ^ (-(δ / 2)) * x ^ (-δ - 1))
        = (2 / δ) * (1 - x ^ (-(δ / 2))) * x ^ (-δ - 1) := by ring
      _ ≤ Real.log x * x ^ (-δ - 1) := mul_le_mul_of_nonneg_right hlog hp
  have hsum : Summable (fun k : ℕ => (2 / δ) * (((N : ℝ) + 1 + k) ^ (-δ - 1) -
      ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1))) := (hs1.sub hs2).mul_left _
  have hsumL : Summable (fun k : ℕ => Real.log (((N + 1 : ℕ) : ℝ) + k) *
      (((N + 1 : ℕ) : ℝ) + k) ^ (-δ - 1)) := by
    refine (HTGeometry.summable_shift_rpow (q := -(δ / 2)) (by linarith) N |>.mul_left (2 / δ)).of_nonneg_of_le
      (fun k => mul_nonneg (Real.log_nonneg (by push_cast; linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]))
        (Real.rpow_nonneg (by positivity) _)) fun k => ?_
    push_cast
    set x : ℝ := (N : ℝ) + 1 + k
    have hx : 0 < x := by positivity
    have hlog := Real.log_le_rpow_div hx.le (show 0 < δ / 2 by linarith)
    have hp : 0 ≤ x ^ (-δ - 1) := Real.rpow_nonneg hx.le _
    calc Real.log x * x ^ (-δ - 1) ≤ x ^ (δ / 2) / (δ / 2) * x ^ (-δ - 1) :=
          mul_le_mul_of_nonneg_right hlog hp
      _ = (2 / δ) * x ^ (-(δ / 2) - 1) := by
          rw [div_eq_mul_inv, mul_comm (x ^ (δ / 2)), mul_assoc, ← Real.rpow_add hx]
          field_simp; ring_nf
  calc (2 / δ ^ 2) * ((((N + 1 : ℕ) : ℝ)) ^ (-δ) - 2 / 3)
      ≤ (2 / δ) * (((N : ℝ) + 1) ^ (-δ) / δ - 1 / (3 * δ / 2)) := by
        push_cast
        apply le_of_eq
        field_simp
    _ ≤ (2 / δ) * (∑' k : ℕ, ((N : ℝ) + 1 + k) ^ (-δ - 1) -
          ∑' k : ℕ, ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1)) := by
        refine mul_le_mul_of_nonneg_left (sub_le_sub hlow ?_) (by positivity)
        exact hup.trans (div_le_div_of_nonneg_right hN1 (by positivity))
    _ = ∑' k : ℕ, (2 / δ) * (((N : ℝ) + 1 + k) ^ (-δ - 1) - ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1)) := by
        rw [tsum_mul_left, hs1.tsum_sub hs2]
    _ ≤ _ := Summable.tsum_le_tsum hterm hsum hsumL

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
