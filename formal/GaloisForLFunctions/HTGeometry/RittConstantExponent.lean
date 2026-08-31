import GaloisForLFunctions.HTGeometry.RittTransportConstant

/-!
# A constant multiplier has no chain-rule exponent

The multipliers produced by the tower descent have the shape `q^i · ρ^k` with `q` a constant of the
derivation and `ρ` the chain-rule factor.  If such a product is itself a constant then the exponent
of the chain-rule factor vanishes: evaluating the order at a zero or pole of `ρ` — which a
nonconstant rational function has, over an algebraically closed field — leaves `k · ord ρ = 0`.

So the degenerate branch of the descent, where the multiplier is `1`, can only arise with `k = 0`
and `q^i = 1`; and when the multiplier is the multiplier of a repelling fixed point, `q^i = 1`
forces `i = 0` as well.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- **A constant times a power of a nonconstant rational function is constant only in exponent
zero.** -/
theorem zpow_exponent_eq_zero_of_isConst {q : K} (hq : q ≠ 0) {r : RatFunc K} (hr0 : r ≠ 0)
    (hr : ¬ ∃ w : K, r = RatFunc.C w) {i k : ℤ} (w : K)
    (h : (RatFunc.C q) ^ i * r ^ k = RatFunc.C w) : k = 0 := by
  by_contra hk
  have hqC : (RatFunc.C q : RatFunc K) ≠ 0 := by simpa using hq
  -- a nonconstant rational function has a zero or a pole
  obtain ⟨z, hz⟩ : ∃ z : K, ratOrder r z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc0, hc⟩ := eq_C_of_ratOrder_eq_zero_algClosed hr0 hcon
    exact hr ⟨c, hc⟩
  have hord : ratOrder ((RatFunc.C q) ^ i * r ^ k) z = ratOrder (RatFunc.C w : RatFunc K) z := by
    rw [h]
  rw [ratOrder_mul (zpow_ne_zero i hqC) (zpow_ne_zero k hr0), ratOrder_zpow hqC,
    ratOrder_zpow hr0, ratOrder_C, ratOrder_C, mul_zero, zero_add] at hord
  exact hz ((mul_eq_zero.mp hord).resolve_left hk)

end GaloisForLFunctions.HTGeometry
