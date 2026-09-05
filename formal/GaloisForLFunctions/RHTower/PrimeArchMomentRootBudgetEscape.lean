import GaloisForLFunctions.HTGeometry.OrderedRootBudgetMomentCompactness
import GaloisForLFunctions.RHTower.GammaSewnPluckerGlobalMeanMomentNoGo

/-!
# Completed Xi moment landing forces root-budget escape

The target-free compactness theorem is classical. The arithmetic application combines
the exact completed prime--Gamma Hankel criterion, multiplicity-faithful Xi moment
determination, and the nonsummable reciprocal Xi spectrum. RH is derived only inside
the contradiction; no RH premise is assumed in any exported result.

Changing carriers or apertures does not evade a common nuclear-root ceiling. Conversely,
no exclusion of unbounded root budgets, signed relative traces, or other source producers
is asserted. This is a scoped firewall and quantitative survivor, not an RH proof.
-/

open Filter Topology ContinuousLinearMap
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The complete prime--Gamma moments cannot be approached with bounded root mass,
even when the positive carrier and its dimension change at every stage. -/
theorem tendsto_rootBudget_atTop_of_primeArch_squareMoment_landing
    {a : ℕ → ℕ → ℝ}
    (ha : ∀ N, Summable (a N)) (ha0 : ∀ N k, 0 ≤ a N k)
    (haa : ∀ N, Antitone (a N))
    (hm : ∀ r, Tendsto (fun N => ∑' k, (a N k ^ 2) ^ (r + 1)) atTop
      (nhds (normalizedPrimeArchMoment r))) :
    Tendsto (fun N => ∑' k, a N k) atTop atTop := by
  apply GaloisForLFunctions.HTGeometry.tendsto_rootBudget_atTop_of_no_summable_squareMoment_realization
    ha ha0 haa ?_ hm
  rintro ⟨b, hb, hb0, hba, hbm⟩
  exact not_summable_nonneg_primeArch_square_moments hb hb0 hba hbm

/-- Every proposed root-budget ceiling has a finite completed-source moment obstruction.
No effective value of the obstructing degree or error is asserted. -/
theorem exists_finite_primeArch_squareMoment_gap (C : ℝ) :
    ∃ n : ℕ, ∀ a : ℕ → ℝ, Summable a → (∀ k, 0 ≤ a k) → Antitone a →
      (∑' k, a k) ≤ C → ∃ r ≤ n,
        1 / ((n : ℝ) + 1) ≤
          |(∑' k, (a k ^ 2) ^ (r + 1)) - normalizedPrimeArchMoment r| := by
  apply GaloisForLFunctions.HTGeometry.exists_finite_squareMoment_gap_of_no_summable_realization
    (C := C)
  rintro ⟨b, hb, hb0, hba, hbm⟩
  exact not_summable_nonneg_primeArch_square_moments hb hb0 hba hbm

private theorem repeatTwo_approxNumber_squareMoment
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : MemSchattenClass 1 A) (r : ℕ) :
    ((∑' k : ℕ, (approxNumber A (k / 2) ^ 2) ^ (r + 1) : ℝ) : ℂ) =
      2 * opTrace (energyOp A ^ (r + 1)) := by
  have hA2 : MemSchattenClass 2 A := hA.mono one_pos (by norm_num)
  have hasq : Summable (fun n => approxNumber A n ^ 2) := by
    simpa [MemSchattenClass, Real.rpow_two] using hA2
  have hapow : Summable (fun n => (approxNumber A n ^ 2) ^ (r + 1)) :=
    GaloisForLFunctions.HTGeometry.summable_pow_succ_of_nonneg_antitone
      hasq (fun _ => sq_nonneg _) (fun _ _ h =>
        pow_le_pow_left₀ (approxNumber_nonneg _ _) (approxNumber_antitone _ h) 2) r
  rw [repeatTwo_tsum hapow (fun n => pow_nonneg (sq_nonneg _) _),
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_tsum]
  simp_rw [Complex.ofReal_pow]
  rw [opTrace_energyOp_pow_eq_approxNumber_moments
    ((memSchattenClass_two_iff_isHilbertSchmidt A).mp hA2)]
  simp only [Complex.ofReal_pow]

/-- Half-normalized operator landing preserves both reflection copies by duplicating every
singular value. The literal nuclear root cost must tend to infinity. -/
theorem tendsto_nuclearRootCost_of_half_primeArch_moment_landing
    {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)]
    [∀ N, InnerProductSpace ℂ (H N)] [∀ N, CompleteSpace (H N)]
    (A : ∀ N, H N →L[ℂ] H N) (hA : ∀ N, MemSchattenClass 1 (A N))
    (hm : ∀ r, Tendsto (fun N => 2 * opTrace (energyOp (A N) ^ (r + 1))) atTop
      (nhds (normalizedPrimeArchMoment r : ℂ))) :
    Tendsto (fun N => ∑' k, approxNumber (A N) k) atTop atTop := by
  let a : ℕ → ℕ → ℝ := fun N k => approxNumber (A N) (k / 2)
  have ha : ∀ N, Summable (a N) := fun N =>
    repeatTwo_summable (hA N).one_summable_approxNumber (approxNumber_nonneg _)
  have ha0 : ∀ N k, 0 ≤ a N k := fun N k => approxNumber_nonneg _ _
  have haa : ∀ N, Antitone (a N) := fun N _ _ h =>
    approxNumber_antitone _ (Nat.div_le_div_right h)
  have hmreal (r : ℕ) : Tendsto (fun N => ∑' k, (a N k ^ 2) ^ (r + 1)) atTop
      (nhds (normalizedPrimeArchMoment r)) := by
    have h := (Complex.continuous_re.tendsto (normalizedPrimeArchMoment r : ℂ)).comp (hm r)
    have heq (N : ℕ) : (∑' k, (a N k ^ 2) ^ (r + 1)) =
        (2 * opTrace (energyOp (A N) ^ (r + 1))).re := by
      exact congrArg Complex.re (repeatTwo_approxNumber_squareMoment (hA N) r)
    exact h.congr (fun N => (heq N).symm)
  have hmass := tendsto_rootBudget_atTop_of_primeArch_squareMoment_landing ha ha0 haa hmreal
  have heq (N : ℕ) : (∑' k, a N k) = 2 * ∑' k, approxNumber (A N) k :=
    repeatTwo_tsum (hA N).one_summable_approxNumber (approxNumber_nonneg _)
  rw [tendsto_atTop] at hmass ⊢
  intro C
  filter_upwards [hmass (2 * C)] with N hN
  rw [heq N] at hN
  linarith

/-- No bounded stage-dependent mixing of a fixed nuclear source can approach all
half-normalized completed Xi energy moments. The amplification cost must escape. -/
theorem tendsto_mixingCost_of_fixed_nuclear_half_primeArch_moment_landing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : MemSchattenClass 1 A)
    (B C : ℕ → H →L[ℂ] H)
    (hm : ∀ r, Tendsto (fun N => 2 * opTrace
      (energyOp (B N ∘L A ∘L C N) ^ (r + 1))) atTop
        (nhds (normalizedPrimeArchMoment r : ℂ))) :
    Tendsto (fun N => ‖B N‖ * ‖C N‖) atTop atTop := by
  have hAC (N : ℕ) : MemSchattenClass 1 (A ∘L C N) :=
    memSchattenClass_one_comp_right hA (C N)
  have hBAC (N : ℕ) : MemSchattenClass 1 (B N ∘L A ∘L C N) :=
    memSchattenClass_one_comp_left (hAC N) (B N)
  have hcost : Tendsto (fun N => traceNorm H (B N ∘L A ∘L C N)) atTop atTop :=
    tendsto_nuclearRootCost_of_half_primeArch_moment_landing _ hBAC hm
  have hbound (N : ℕ) : traceNorm H (B N ∘L A ∘L C N) ≤
      (‖B N‖ * ‖C N‖) * traceNorm H A := by
    calc
      _ ≤ ‖B N‖ * traceNorm H (A ∘L C N) :=
        traceNorm_comp_left_le (hAC N).one_summable_approxNumber (B N)
      _ ≤ ‖B N‖ * (traceNorm H A * ‖C N‖) :=
        mul_le_mul_of_nonneg_left
          (traceNorm_comp_right_le hA.one_summable_approxNumber (C N)) (norm_nonneg _)
      _ = _ := by ring
  rw [tendsto_atTop] at hcost ⊢
  intro R
  filter_upwards [hcost (max R 0 * traceNorm H A + 1)] with N hN
  by_contra hR
  have hR' : ‖B N‖ * ‖C N‖ ≤ max R 0 := (le_of_not_ge hR).trans (le_max_left _ _)
  have hmul := mul_le_mul_of_nonneg_right hR' (traceNorm_nonneg A)
  linarith [hbound N]

namespace HedenmalmThetaSource

local instance : ContinuousFunctionalCalculus ℝ
    (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert)
      IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The literal C1 source cannot acquire full Xi moments through bounded cofinal mixing.
This strengthens the fixed-operator exclusion without excluding unbounded amplification. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMean_half_moment_landing_forces_mixing_escape
    (B C : ℕ → GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert)
    (hm : ∀ r, Tendsto (fun N => 2 * opTrace
      (energyOp (B N ∘L CFC.sqrt gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator
        ∘L C N) ^ (r + 1))) atTop (nhds (normalizedPrimeArchMoment r : ℂ))) :
    Tendsto (fun N => ‖B N‖ * ‖C N‖) atTop atTop :=
  tendsto_mixingCost_of_fixed_nuclear_half_primeArch_moment_landing _
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_sqrt_memSchattenClass_one B C hm

end HedenmalmThetaSource

end RHTower
