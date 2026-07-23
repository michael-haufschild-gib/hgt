import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces
import GaloisForLFunctions.RHTower.CompactCarrierLambert

/-!
# Dual reduction for the weighted Euler joint graph

A continuous functional pair `(λ, ℓ)` annihilating the joint graph
`{(b, Σ_p b_p u_p)}` satisfies the graph relation `λ(e_p) + ℓ(u_p) = 0`, and
continuity of the coefficient side bounds `|λ(e_p)|` by the exact coordinate
norm `C (log p) p^{-σ₀}`.  Through the compact-carrier Lambert normalisation
`ℓ(u_p) = (log p)·H(log p)` this forces the super-source sampling decay

`‖H(log p)‖ ≤ C p^{-σ₀}`   .

This file proves that reduction unconditionally against the existing
compact-carrier infrastructure (`CompactCarrierLambert`): the flux functional
is a continuous functional `L` on `C(K, ℂ)` for a compact carrier `K`, the
Euler tangent is `compactPrimeEulerUnitTangent`, and `H` is
`compactCarrierLambertTransform L s`.  The critical-boundary instance
`σ₀ = 1` is fed by the exact `T_1` coordinate norm, proved here as
`criticalNorm_coordinate`.

The decisive upgrade of (7) to a carrier statement is the prime-log
prime-log oversampling lemma, formalized separately.
-/

noncomputable section

namespace RHTower

open Complex Set

/-- The critical (`T_1`) norm of a coefficient field. -/
def criticalNorm (b : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, ({p : ℕ | p.Prime}.indicator fun n => Real.log n / n * |b n|) n

/-- **Exact coordinate norm in `T_1`** (the critical coordinate norm):
`‖e_p‖_{T_1} = (log p)/p`. -/
theorem criticalNorm_coordinate {p : ℕ} (hp : p.Prime) :
    criticalNorm (primeCoordinateField p) = Real.log p / p := by
  unfold criticalNorm
  rw [tsum_eq_single p]
  · rw [Set.indicator_of_mem (show p ∈ {q : ℕ | q.Prime} from hp)]
    simp [primeCoordinateField]
  · intro n hnp
    by_cases hn : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {q : ℕ | q.Prime} from hn)]
      simp [primeCoordinateField, hnp]
    · rw [Set.indicator_of_notMem (show n ∉ {q : ℕ | q.Prime} from hn)]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The flux value of the compact Euler tangent is the prime-log Lambert
sample times `log p`: `A(u_p) = (log p)·H_A(log p)`. -/
theorem map_compactPrimeEulerUnitTangent_eq_logMul_lambert
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (p : ℕ) :
    L (compactPrimeEulerUnitTangent s p)
      = (Real.log p : ℂ) * compactCarrierLambertTransform L s (Real.log p) := by
  unfold compactPrimeEulerUnitTangent compactCarrierLambertTransform
  rw [map_smul, smul_eq_mul]

/-- **Dual reduction with decay**: if the
joint-graph relation `λ_p + L(u_p) = 0` holds and the coefficient dual value
obeys the weighted bound `‖λ_p‖ ≤ C (log p) p^{-σ₀}`, then the prime-log
Lambert sample decays like `C p^{-σ₀}` — exponentially small in `log p`. -/
theorem norm_lambert_primeLog_le_of_graph_annihilation
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {p : ℕ} (hp : 2 ≤ p)
    {lam : ℂ} (hgraph : lam + L (compactPrimeEulerUnitTangent s p) = 0)
    {C σ₀ : ℝ}
    (hdual : ‖lam‖ ≤ C * Real.log p * (p : ℝ) ^ (-σ₀)) :
    ‖compactCarrierLambertTransform L s (Real.log p)‖
      ≤ C * (p : ℝ) ^ (-σ₀) := by
  have hlogpos : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hp)
  have hL := map_compactPrimeEulerUnitTangent_eq_logMul_lambert L s p
  have hneg : L (compactPrimeEulerUnitTangent s p) = -lam :=
    eq_neg_of_add_eq_zero_right hgraph
  have hval : Real.log p
      * ‖compactCarrierLambertTransform L s (Real.log p)‖ = ‖lam‖ := by
    calc Real.log p * ‖compactCarrierLambertTransform L s (Real.log p)‖
        = ‖(Real.log p : ℂ)‖
          * ‖compactCarrierLambertTransform L s (Real.log p)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hlogpos.le]
      _ = ‖(Real.log p : ℂ)
            * compactCarrierLambertTransform L s (Real.log p)‖ :=
          (norm_mul _ _).symm
      _ = ‖L (compactPrimeEulerUnitTangent s p)‖ := by rw [hL]
      _ = ‖lam‖ := by rw [hneg, norm_neg]
  have hkey : Real.log p
      * ‖compactCarrierLambertTransform L s (Real.log p)‖
      ≤ Real.log p * (C * (p : ℝ) ^ (-σ₀)) := by
    rw [hval]
    calc ‖lam‖ ≤ C * Real.log p * (p : ℝ) ^ (-σ₀) := hdual
      _ = Real.log p * (C * (p : ℝ) ^ (-σ₀)) := by ring
  exact le_of_mul_le_mul_left hkey hlogpos

/-- **Critical-boundary dual reduction** (`σ₀ = 1`, the `T_1`/`M_0` case of
case): the dual bound is exactly `C` times the `T_1` coordinate norm, and
the Lambert samples decay like `C/p`. -/
theorem norm_lambert_primeLog_le_of_graph_annihilation_critical
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {p : ℕ} (hp : p.Prime)
    {lam : ℂ} (hgraph : lam + L (compactPrimeEulerUnitTangent s p) = 0)
    {C : ℝ}
    (hdual : ‖lam‖ ≤ C * criticalNorm (primeCoordinateField p)) :
    ‖compactCarrierLambertTransform L s (Real.log p)‖ ≤ C / p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hdual' : ‖lam‖ ≤ C * Real.log p * (p : ℝ) ^ (-(1:ℝ)) := by
    rw [Real.rpow_neg_one]
    calc ‖lam‖ ≤ C * criticalNorm (primeCoordinateField p) := hdual
      _ = C * (Real.log p / p) := by rw [criticalNorm_coordinate hp]
      _ = C * Real.log p * ((p:ℝ))⁻¹ := by ring
  have h := norm_lambert_primeLog_le_of_graph_annihilation L s hp.two_le
    hgraph hdual'
  calc ‖compactCarrierLambertTransform L s (Real.log p)‖
      ≤ C * (p : ℝ) ^ (-(1:ℝ)) := h
    _ = C / p := by rw [Real.rpow_neg_one, div_eq_mul_inv]

end RHTower
