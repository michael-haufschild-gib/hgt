import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanGram

/-!
# Ramanujan prefix energy as a Gram quadratic form

For `ε > 0` the Ramanujan weights `w_ε(q)` and the primitives `C_q(N) = ∑_{n≤N} c_q(n)` are
real, and the cumulative centered prefix is `∑_{2≤q<Q+2} w_ε(q) C_q(N)`. Its discrete energy
`∑_N |·|²/(N(N+1))` over all `N` therefore equals the finite quadratic form
`Γ_Q = ∑_{2≤p,q<Q+2} w_ε(p) w_ε(q) G(p,q)` in the Gram entries `G(p,q)` of the primitives. The
truncated prefix energies increase to `Γ_Q`, so a uniform bound on all truncated energies is
equivalent to a uniform bound on the quadratic forms `Γ_Q`, and either implies `L²` admission
of the power-damped Fermi source.

## Main results

- `pmPowerDampedRamanujanCumulativePrefix_eq_primitive`: the cumulative prefix is `∑_{q<Q} w_ε(q+2) C_{q+2}(N)`.
- `hasSum_pmPowerDampedRamanujanEnergyTerm`: for `ε > 0`, `∑_N |cumulative prefix_Q(N)|²/(N(N+1)) = Γ_Q`.
- `pmPowerDampedRamanujanPrefixEnergy_le_gram`: every truncated prefix energy is at most `Γ_Q`.
- `pmPowerDampedRamanujan_budget_iff_gram`: a bound `B` on all truncated prefix energies holds iff `Γ_Q ≤ B` for all `Q`.
- `pmPowerDampedFermiSource_memLp_of_ramanujan_gram`: `sup_Q Γ_Q ≤ B` implies `F_ε ∈ L²(0,∞)`.

## Hypotheses

Unconditional apart from `0 < ε`. `pmPowerDampedFermiSource_memLp_of_ramanujan_gram` is
conditional on the hypothesis `hB` that one real `B` bounds `Γ_Q` for every `Q`; this bound is
not proved here.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The Ramanujan primitive `C_q(N)` is real. -/
theorem pmRamanujanPrimitive_im (q N : ℕ) : (pmRamanujanPrimitive q N).im = 0 := by
  rw [pmRamanujanPrimitive_eq_floor]
  simp [Complex.mul_im]

/-- For `ε > 0`, the Ramanujan weight `w_ε(q)` is real. -/
theorem pmPowerDampedRamanujanWeight_im {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (pmPowerDampedRamanujanWeight ε q).im = 0 := by
  rw [pmPowerDampedRamanujanWeight_eq_ofReal hε]
  exact Complex.ofReal_im _

/-- The cumulative centered prefix equals `∑_{q<Q} w_ε(q+2) C_{q+2}(N)`. -/
theorem pmPowerDampedRamanujanCumulativePrefix_eq_primitive (ε : ℝ) (Q N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε Q N =
      ∑ q ∈ Finset.range Q, pmPowerDampedRamanujanWeight ε (q+2)*
        pmRamanujanPrimitive (q+2) N := by
  unfold pmPowerDampedRamanujanCumulativePrefix pmPowerDampedRamanujanCenteredPrefix
  rw [Finset.sum_comm]
  simp_rw [pmRamanujanPrimitive, Finset.mul_sum]

theorem pmPowerDampedRamanujanCumulativePrefix_im {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    (pmPowerDampedRamanujanCumulativePrefix ε Q N).im = 0 := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_primitive]
  simp [Complex.mul_im, pmPowerDampedRamanujanWeight_im hε, pmRamanujanPrimitive_im]

/-- For `ε > 0`, the real part of the cumulative prefix is `∑_{q<Q} Re w_ε(q+2) Re C_{q+2}(N)`. -/
theorem pmPowerDampedRamanujanCumulativePrefix_re {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    (pmPowerDampedRamanujanCumulativePrefix ε Q N).re =
      ∑ q ∈ Finset.range Q, (pmPowerDampedRamanujanWeight ε (q+2)).re*
        (pmRamanujanPrimitive (q+2) N).re := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_primitive]
  simp [Complex.mul_re, pmPowerDampedRamanujanWeight_im hε]

/-- The Gram quadratic form `Γ_Q = ∑_{p,q<Q} Re w_ε(p+2) Re w_ε(q+2) G(p+2, q+2)`. -/
def pmPowerDampedRamanujanGramQuadratic (ε : ℝ) (Q : ℕ) : ℝ :=
  ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
    (pmPowerDampedRamanujanWeight ε (p+2)).re*
      (pmPowerDampedRamanujanWeight ε (q+2)).re*pmRamanujanPrimitiveGram (p+2) (q+2)

/-- For `ε > 0`, each energy term `|cumulative prefix_Q(N)|²/(N(N+1))` expands as the
quadratic form in the Gram terms at `N`. -/
theorem pmPowerDampedRamanujanEnergyTerm_eq_gram {ε : ℝ} (hε : 0 < ε) (Q N : ℕ) :
    ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖^2/((N : ℝ)*((N : ℝ)+1)) =
      ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
        (pmPowerDampedRamanujanWeight ε (p+2)).re*
          (pmPowerDampedRamanujanWeight ε (q+2)).re*
            pmRamanujanPrimitiveGramTerm (p+2) (q+2) N := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    pmPowerDampedRamanujanCumulativePrefix_im hε]
  simp only [mul_zero, add_zero, pmPowerDampedRamanujanCumulativePrefix_re hε,
    Finset.sum_mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  unfold pmRamanujanPrimitiveGramTerm
  ring

/-- For `ε > 0`, the full discrete energy of the `Q`-truncated cumulative prefix is `Γ_Q`. -/
theorem hasSum_pmPowerDampedRamanujanEnergyTerm {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    HasSum (fun N : ℕ => ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖^2/
      ((N : ℝ)*((N : ℝ)+1))) (pmPowerDampedRamanujanGramQuadratic ε Q) := by
  have hs : HasSum (fun N : ℕ =>
      ∑ p ∈ Finset.range Q, ∑ q ∈ Finset.range Q,
        (pmPowerDampedRamanujanWeight ε (p+2)).re*
          (pmPowerDampedRamanujanWeight ε (q+2)).re*
            pmRamanujanPrimitiveGramTerm (p+2) (q+2) N)
      (pmPowerDampedRamanujanGramQuadratic ε Q) := by
    apply hasSum_sum
    intro p hp
    apply hasSum_sum
    intro q hq
    exact (summable_pmRamanujanPrimitiveGramTerm (by omega : 1 < p+2)
      (by omega : 1 < q+2)).hasSum.mul_left _
  exact hs.congr_fun (pmPowerDampedRamanujanEnergyTerm_eq_gram hε Q)

/-- For `ε > 0`, every truncated prefix energy up to `T` is at most `Γ_Q`. -/
theorem pmPowerDampedRamanujanPrefixEnergy_le_gram {ε : ℝ} (hε : 0 < ε) (Q T : ℕ) :
    pmPowerDampedRamanujanPrefixEnergy ε Q T ≤ pmPowerDampedRamanujanGramQuadratic ε Q := by
  have hs := hasSum_pmPowerDampedRamanujanEnergyTerm hε Q
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum (Finset.Icc 1 T) (fun _ _ => by positivity)

/-- For `ε > 0`, the truncated prefix energies converge to `Γ_Q` as `T → ∞`. -/
theorem tendsto_pmPowerDampedRamanujanPrefixEnergy_gram {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    Tendsto (fun T : ℕ => pmPowerDampedRamanujanPrefixEnergy ε Q T)
      atTop (𝓝 (pmPowerDampedRamanujanGramQuadratic ε Q)) := by
  have hs := hasSum_pmPowerDampedRamanujanEnergyTerm hε Q
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, div_zero, sub_zero] at ht
  simpa only [pmPowerDampedRamanujanPrefixEnergy, sum_Icc_eq_sum_range_succ] using
    ht.tendsto_sum_nat

/-- For `ε > 0`, `B` bounds all truncated prefix energies iff `Γ_Q ≤ B` for every `Q`. -/
theorem pmPowerDampedRamanujan_budget_iff_gram {ε B : ℝ} (hε : 0 < ε) :
    (∀ Q T : ℕ, pmPowerDampedRamanujanPrefixEnergy ε Q T ≤ B) ↔
      (∀ Q : ℕ, pmPowerDampedRamanujanGramQuadratic ε Q ≤ B) := by
  constructor
  · intro h Q
    exact le_of_tendsto (tendsto_pmPowerDampedRamanujanPrefixEnergy_gram hε Q)
      (Eventually.of_forall (h Q))
  · intro h Q T
    exact (pmPowerDampedRamanujanPrefixEnergy_le_gram hε Q T).trans (h Q)

/-- Conditional admission: for `ε > 0`, if `hB` gives `Γ_Q ≤ B` for every `Q`, then
`F_ε ∈ L²(0,∞)`. -/
theorem pmPowerDampedFermiSource_memLp_of_ramanujan_gram {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ, pmPowerDampedRamanujanGramQuadratic ε Q ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  exact pmPowerDampedFermiSource_memLp_of_ramanujan_budget hε
    ((pmPowerDampedRamanujan_budget_iff_gram hε).mpr hB)

end RHTower
