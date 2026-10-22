import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# Mean–variance split of the Ramanujan Gram quadratic form

For `ε > 0` the `Q`-truncated cumulative Ramanujan prefix `P_Q(N) = ∑_{2≤q<Q+2} w_ε(q) C_q(N)`
has weighted mean `μ_Q = ∑_N Re P_Q(N)/(N(N+1)) = −∑_{2≤q<Q+2} w_ε(q) Λ(q)`, and this mean is
bounded uniformly in `Q` because `|w_ε(q)| ≤ q^(−1−ε)` makes `∑ w_ε(q) Λ(q)` absolutely
convergent. The Gram quadratic form splits as `Γ_Q = μ_Q² + V_Q`, where
`V_Q = ∑_N (Re P_Q(N) − μ_Q)²/(N(N+1)) ≥ 0`. Hence `Γ_Q` is uniformly bounded iff `V_Q` is, and a
uniform variance bound gives `L²` admission of the Fermi source. For the `Λ`-centered Gram
entries, `Ĝ(p,q)/log p → φ(q)/2 − Λ(q)` along primes `p`.

## Main results

- `hasSum_pmPowerDampedRamanujanCumulativeMean`: `∑_N Re P_Q(N)/(N(N+1)) = μ_Q`.
- `exists_pmPowerDampedRamanujanEnergyMean_bound`: `|μ_Q| ≤ C` uniformly in `Q`, for `ε > 0`.
- `pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance`: `Γ_Q = μ_Q² + V_Q`.
- `pmPowerDampedRamanujan_gram_budget_iff_variance`: `sup_Q Γ_Q < ∞` iff `sup_Q V_Q < ∞`.
- `pmPowerDampedFermiSource_memLp_of_ramanujan_variance`: `V_Q ≤ B` for all `Q` implies `F_ε ∈ L²(0,∞)`.
- `tendsto_pmRamanujanEnergyCenteredGram_prime_div_log`: `Ĝ(p,q)/log p → φ(q)/2 − Λ(q)` as `p → ∞` over primes.

## Hypotheses

Unconditional apart from `0 < ε` (and `1 < q` for the prime asymptotic).
`pmPowerDampedFermiSource_memLp_of_ramanujan_variance` is conditional on the hypothesis `hB`
that one real `B` bounds `V_Q` for every `Q`; this variance budget is not proved here.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The weighted mean `μ_Q = −∑_{q<Q} Re w_ε(q+2) Λ(q+2)` of the truncated cumulative prefix. -/
def pmPowerDampedRamanujanEnergyMean (ε : ℝ) (Q : ℕ) : ℝ :=
  -∑ q ∈ Finset.range Q, (pmPowerDampedRamanujanWeight ε (q+2)).re*vonMangoldt (q+2)

/-- For `ε > 0`, `∑_N Re P_Q(N)/(N(N+1)) = μ_Q`. -/
theorem hasSum_pmPowerDampedRamanujanCumulativeMean {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    HasSum (fun N : ℕ => (pmPowerDampedRamanujanCumulativePrefix ε Q N).re/
      ((N : ℝ)*((N : ℝ)+1))) (pmPowerDampedRamanujanEnergyMean ε Q) := by
  have h := hasSum_sum (s := Finset.range Q) (fun q _ =>
    (hasSum_pmRamanujanPrimitive_reciprocal (by omega : 1 < q+2)).mul_left
      (pmPowerDampedRamanujanWeight ε (q+2)).re)
  simp only [mul_neg, Finset.sum_neg_distrib] at h
  change HasSum _ (pmPowerDampedRamanujanEnergyMean ε Q) at h
  apply h.congr_fun
  intro N
  rw [pmPowerDampedRamanujanCumulativePrefix_re hε, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- For `ε > 0`, `∑_q Re w_ε(q) Λ(q)` converges absolutely (dominated by `∑ Λ(q) q^(−1−ε)`). -/
theorem summable_pmPowerDampedRamanujanVonMangoldt {ε : ℝ} (hε : 0 < ε) :
    Summable (fun q : ℕ => (pmPowerDampedRamanujanWeight ε q).re*vonMangoldt q) := by
  apply Summable.of_norm_bounded
    (GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow (by linarith : 1 < 1+ε))
  intro q
  by_cases hq : q = 0
  · subst q
    simp [pmPowerDampedRamanujanWeight_zero]
  have hqp : 0 < q := Nat.pos_of_ne_zero hq
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  calc
    _ ≤ (1/(q : ℝ)^(1+ε))*vonMangoldt q :=
      mul_le_mul_of_nonneg_right
        ((Complex.abs_re_le_norm _).trans (norm_pmPowerDampedRamanujanWeight_le hε hqp))
        vonMangoldt_nonneg
    _ = _ := by rw [Real.rpow_neg (Nat.cast_nonneg q)]; ring

/-- For `ε > 0`, the means `μ_Q` are bounded uniformly in `Q`. -/
theorem exists_pmPowerDampedRamanujanEnergyMean_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, |pmPowerDampedRamanujanEnergyMean ε Q| ≤ C := by
  let g : ℕ → ℝ := fun q => (pmPowerDampedRamanujanWeight ε (q+2)).re*vonMangoldt (q+2)
  have hs : Summable g := (summable_nat_add_iff
    (f := fun q : ℕ => (pmPowerDampedRamanujanWeight ε q).re*vonMangoldt q) 2).mpr
      (summable_pmPowerDampedRamanujanVonMangoldt hε)
  refine ⟨∑' q : ℕ, ‖g q‖, tsum_nonneg (fun _ => norm_nonneg _), fun Q => ?_⟩
  change |-(∑ q ∈ Finset.range Q, g q)| ≤ _
  rw [abs_neg, ← Real.norm_eq_abs]
  exact (norm_sum_le _ _).trans (hs.norm.sum_le_tsum (Finset.range Q) (fun _ _ => norm_nonneg _))

/-- The weighted variance `V_Q = ∑'_N (Re P_Q(N) − μ_Q)²/(N(N+1))`. -/
def pmPowerDampedRamanujanEnergyVariance (ε : ℝ) (Q : ℕ) : ℝ :=
  ∑' N : ℕ, ((pmPowerDampedRamanujanCumulativePrefix ε Q N).re-
    pmPowerDampedRamanujanEnergyMean ε Q)^2/((N : ℝ)*((N : ℝ)+1))

/-- For `ε > 0`, the variance series sums to `Γ_Q − μ_Q²`. -/
theorem hasSum_pmPowerDampedRamanujanEnergyVariance {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    HasSum (fun N : ℕ => ((pmPowerDampedRamanujanCumulativePrefix ε Q N).re-
      pmPowerDampedRamanujanEnergyMean ε Q)^2/((N : ℝ)*((N : ℝ)+1)))
      (pmPowerDampedRamanujanGramQuadratic ε Q-pmPowerDampedRamanujanEnergyMean ε Q^2) := by
  have h := ((hasSum_pmPowerDampedRamanujanEnergyTerm hε Q).sub
    ((hasSum_pmPowerDampedRamanujanCumulativeMean hε Q).mul_left
      (2*pmPowerDampedRamanujanEnergyMean ε Q))).add
        (hasSum_pm_reciprocal_weight.mul_left (pmPowerDampedRamanujanEnergyMean ε Q^2))
  have he : pmPowerDampedRamanujanGramQuadratic ε Q-
      (2*pmPowerDampedRamanujanEnergyMean ε Q)*pmPowerDampedRamanujanEnergyMean ε Q+
        pmPowerDampedRamanujanEnergyMean ε Q^2*1 =
      pmPowerDampedRamanujanGramQuadratic ε Q-pmPowerDampedRamanujanEnergyMean ε Q^2 := by ring
  rw [he] at h
  apply h.congr_fun
  intro N
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    pmPowerDampedRamanujanCumulativePrefix_im hε]
  ring

theorem pmPowerDampedRamanujanEnergyVariance_nonneg (ε : ℝ) (Q : ℕ) :
    0 ≤ pmPowerDampedRamanujanEnergyVariance ε Q :=
  tsum_nonneg (fun _ => div_nonneg (sq_nonneg _) (by positivity))

/-- For `ε > 0`, the Gram quadratic form splits as `Γ_Q = μ_Q² + V_Q`. -/
theorem pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance {ε : ℝ}
    (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanGramQuadratic ε Q = pmPowerDampedRamanujanEnergyMean ε Q^2+
      pmPowerDampedRamanujanEnergyVariance ε Q := by
  have h := (hasSum_pmPowerDampedRamanujanEnergyVariance hε Q).tsum_eq
  change pmPowerDampedRamanujanEnergyVariance ε Q = _ at h
  linarith

/-- For `ε > 0`, `V_Q ≤ Γ_Q`. -/
theorem pmPowerDampedRamanujanEnergyVariance_le_gram {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanEnergyVariance ε Q ≤ pmPowerDampedRamanujanGramQuadratic ε Q := by
  rw [pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance hε Q]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- For `ε > 0`, the Gram forms `Γ_Q` are uniformly bounded iff the variances `V_Q` are. -/
theorem pmPowerDampedRamanujan_gram_budget_iff_variance {ε : ℝ} (hε : 0 < ε) :
    (∃ B : ℝ, ∀ Q : ℕ, pmPowerDampedRamanujanGramQuadratic ε Q ≤ B) ↔
      (∃ B : ℝ, ∀ Q : ℕ, pmPowerDampedRamanujanEnergyVariance ε Q ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun Q => (pmPowerDampedRamanujanEnergyVariance_le_gram hε Q).trans (hB Q)⟩
  · rintro ⟨B, hB⟩
    obtain ⟨C, hC0, hC⟩ := exists_pmPowerDampedRamanujanEnergyMean_bound hε
    refine ⟨B+C^2, fun Q => ?_⟩
    rw [pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance hε Q]
    have hs := mul_self_le_mul_self (abs_nonneg (pmPowerDampedRamanujanEnergyMean ε Q)) (hC Q)
    have hsq := sq_abs (pmPowerDampedRamanujanEnergyMean ε Q)
    nlinarith [hB Q]

/-- Conditional admission: for `ε > 0`, if `hB` gives `V_Q ≤ B` for every `Q`, then
`F_ε ∈ L²(0,∞)`. -/
theorem pmPowerDampedFermiSource_memLp_of_ramanujan_variance {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ, pmPowerDampedRamanujanEnergyVariance ε Q ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨C, hC⟩ := (pmPowerDampedRamanujan_gram_budget_iff_variance hε).mpr ⟨B, hB⟩
  exact pmPowerDampedFermiSource_memLp_of_ramanujan_gram hε hC

/-- For `q > 1`, the `Λ`-centered Gram entry satisfies `Ĝ(p,q)/log p → φ(q)/2 − Λ(q)` as `p → ∞`
through the primes. -/
theorem tendsto_pmRamanujanEnergyCenteredGram_prime_div_log {q : ℕ} (hq : 1 < q) :
    Tendsto (fun p : {p : ℕ // p.Prime} =>
      pmRamanujanEnergyCenteredGram p q/Real.log (p : ℕ)) atTop
        (𝓝 ((q.totient : ℝ)/2-vonMangoldt q)) := by
  have h := (tendsto_pmRamanujanPrimitiveGram_prime_div_log hq).sub_const (vonMangoldt q)
  apply h.congr
  intro p
  rw [pmRamanujanPrimitiveGram_eq_energyCentered p.property.one_lt hq,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hpL : Real.log (p : ℕ) ≠ 0 := (Real.log_pos hp1).ne'
  field_simp
  ring

end RHTower
