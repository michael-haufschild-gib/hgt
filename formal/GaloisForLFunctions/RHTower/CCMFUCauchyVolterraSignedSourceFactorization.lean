import GaloisForLFunctions.RHTower.CCMFUCauchyVolterraSourceBridge

/-!
# Source-faithful Cauchy--Volterra factorization of the critical FU action

The literal critical prime--polar coefficient remains outside its own Cauchy--Volterra cell.
Thus this is not a common-base-point Fubini rewrite: moving the lower endpoint would insert a
truncated source and can lose the required prime--polar cancellation.  The remaining RH-bearing
problem is uniform signed control of this exact nested positive-kernel family.
-/

open Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem ccmFUSuzuki_activeSqrtClockRange
    {H : ℝ} (hH : 2 ≤ H) {j : ℕ}
    (hj : j ∈ Finset.range (suzukiCheckpointEventIndex H - 2)) :
    1 < Real.sqrt ((j + 3 : ℕ) : ℝ) ∧
      Real.sqrt ((j + 3 : ℕ) : ℝ) ≤ Real.exp (H / 2) := by
  have hlog2one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  obtain ⟨hM2, _⟩ := suzukiCheckpointEventIndex_two_le_and_mem_cell
    (hlog2one.trans (one_le_two.trans hH))
  have hjlt : j < suzukiCheckpointEventIndex H - 2 := Finset.mem_range.mp hj
  have hjcell : j + 2 ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H) := by
    rw [Finset.mem_Ico]
    omega
  have hlog := one_lt_log_event_succ_and_log_event_succ_le hjcell
  have hn : (0 : ℝ) < ((j + 3 : ℕ) : ℝ) := by positivity
  have hsqgt : 1 < ((j + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < j + 3 by omega)
  constructor
  · rw [Real.lt_sqrt (by positivity)]
    nlinarith
  · have hnexp : ((j + 3 : ℕ) : ℝ) ≤ Real.exp H :=
      (Real.log_le_iff_le_exp hn).mp hlog.2
    have hsqrt := Real.sqrt_le_sqrt hnexp
    rw [← Real.exp_half] at hsqrt
    exact hsqrt

private theorem ccmFUSuzuki_criticalMultiplier_eq_cellProfile (H : ℝ) (j : ℕ) :
    suzukiCheckpointCriticalTriangularMultiplier H j =
      ((j + 3 : ℕ) : ℝ) *
        cauchyVolterraFUProfile H (Real.sqrt ((j + 3 : ℕ) : ℝ)) := by
  have hdiv := suzukiCheckpointCriticalTriangularMultiplier_div_eq_cauchyVolterraFUProfile H j
  have hden : ((j + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    suzukiCheckpointCriticalTriangularMultiplier H j =
        (suzukiCheckpointCriticalTriangularMultiplier H j /
          ((j + 3 : ℕ) : ℝ)) * ((j + 3 : ℕ) : ℝ) := by
            field_simp
    _ = cauchyVolterraFUProfile H (Real.sqrt ((j + 3 : ℕ) : ℝ)) *
          ((j + 3 : ℕ) : ℝ) := by rw [hdiv]
    _ = _ := by ring

/-- Literal von Mangoldt-minus-polar increment on the forced critical FU cell. -/
noncomputable def ccmFUSuzukiCriticalPrimePolarIncrement (j : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
    (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))

/--
Exact source-faithful cell decomposition of the literal weighted prime--polar source.

Every signed coefficient is retained outside the integral whose lower endpoint is its own
square-root clock.  In particular, this theorem does not replace the actual source by a
common-lower-limit cumulative source.
-/
theorem ccmFUSuzukiWeightedPrimePolar_eq_cauchyVolterraCells
    {H : ℝ} (hH : 2 ≤ H) :
    (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
      ccmFUSuzukiCriticalPrimePolarIncrement j * suzukiCheckpointCriticalTriangularMultiplier H j) =
      (-Real.exp (H / 2) *
          cauchyVolterraFUProfileDeriv H (Real.exp (H / 2))) *
        (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
            (1 - Real.sqrt ((j + 3 : ℕ) : ℝ) / Real.exp (H / 2))) +
      ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
          ∫ y in Real.sqrt ((j + 3 : ℕ) : ℝ)..Real.exp (H / 2),
            cauchyVolterraFUCurvature H y *
              cauchyVolterraKernel (Real.sqrt ((j + 3 : ℕ) : ℝ)) y := by
  let M := suzukiCheckpointEventIndex H - 2
  let a : ℕ → ℝ := fun j => ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j
  let xi : ℕ → ℝ := fun j => Real.sqrt ((j + 3 : ℕ) : ℝ)
  let Y : ℝ := Real.exp (H / 2)
  let J : ℝ := -Y * cauchyVolterraFUProfileDeriv H Y
  have hH0 : 0 < H := by linarith
  have hrecon : ∀ j ∈ Finset.range M,
      cauchyVolterraFUProfile H (xi j) =
        J * (1 - xi j / Y) +
          ∫ y in xi j..Y,
            cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y := by
    intro j hj
    have hjrange : j ∈ Finset.range (suzukiCheckpointEventIndex H - 2) := by
      simpa only [M] using hj
    have hactive := ccmFUSuzuki_activeSqrtClockRange hH hjrange
    have hrec := cauchyVolterraFUProfile_reconstruction hH0 hactive.1 hactive.2
    simpa only [xi, Y, J] using hrec
  have hterm (j : ℕ) :
      ccmFUSuzukiCriticalPrimePolarIncrement j * suzukiCheckpointCriticalTriangularMultiplier H j =
        a j * cauchyVolterraFUProfile H (xi j) := by
    dsimp only [a, xi]
    rw [ccmFUSuzuki_criticalMultiplier_eq_cellProfile]
    ring
  change (∑ j ∈ Finset.range M,
      ccmFUSuzukiCriticalPrimePolarIncrement j * suzukiCheckpointCriticalTriangularMultiplier H j) = _
  calc
    (∑ j ∈ Finset.range M,
      ccmFUSuzukiCriticalPrimePolarIncrement j * suzukiCheckpointCriticalTriangularMultiplier H j) =
        ∑ j ∈ Finset.range M, a j * cauchyVolterraFUProfile H (xi j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hterm j
    _ = J * ∑ j ∈ Finset.range M, a j * (1 - xi j / Y) +
        ∑ j ∈ Finset.range M, a j *
          ∫ y in xi j..Y, cauchyVolterraFUCurvature H y * cauchyVolterraKernel (xi j) y := by
            rw [Finset.mul_sum]
            calc
              (∑ j ∈ Finset.range M, a j * cauchyVolterraFUProfile H (xi j)) =
                  ∑ j ∈ Finset.range M,
                    (J * (a j * (1 - xi j / Y)) + a j *
                      ∫ y in xi j..Y, cauchyVolterraFUCurvature H y *
                        cauchyVolterraKernel (xi j) y) := by
                          apply Finset.sum_congr rfl
                          intro j hj
                          rw [hrecon j hj]
                          ring
              _ = _ := Finset.sum_add_distrib
    _ = _ := by
      dsimp only [M, a, xi, Y, J]

/--
The complete critical Mertens-deviation action equals its literal zero-clock term plus the
source-faithful Cauchy--Volterra cells.
-/
theorem ccmFUSuzukiCriticalMertensDeviationVariationAction_eq_zeroClock_add_cauchyVolterraCells
    {H : ℝ} (hH : 2 ≤ H) :
    suzukiCheckpointCriticalVariationAction suzukiCheckpointCriticalMertensDeviation H =
      suzukiCheckpointCriticalMertensDeviation 0 *
          suzukiCheckpointCriticalTriangularMultiplier H 0 +
      (-Real.exp (H / 2) *
          cauchyVolterraFUProfileDeriv H (Real.exp (H / 2))) *
        (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
            (1 - Real.sqrt ((j + 3 : ℕ) : ℝ) / Real.exp (H / 2))) +
      ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
          ∫ y in Real.sqrt ((j + 3 : ℕ) : ℝ)..Real.exp (H / 2),
            cauchyVolterraFUCurvature H y *
              cauchyVolterraKernel (Real.sqrt ((j + 3 : ℕ) : ℝ)) y := by
  rw [suzukiCheckpointCriticalMertensDeviationVariationAction_eq_weightedPrimePolar,
    show (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
      (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
          suzukiCheckpointCriticalTriangularMultiplier H j) =
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          ccmFUSuzukiCriticalPrimePolarIncrement j *
            suzukiCheckpointCriticalTriangularMultiplier H j by
      apply Finset.sum_congr rfl
      intro j _
      rfl,
    ccmFUSuzukiWeightedPrimePolar_eq_cauchyVolterraCells hH]
  ring

/--
Explicit positive endpoint-jet form of the source-faithful critical action factorization.
-/
theorem ccmFUSuzukiCriticalMertensDeviationVariationAction_eq_zeroClock_add_explicitCauchyVolterraCells
    {H : ℝ} (hH : 2 ≤ H) :
    suzukiCheckpointCriticalVariationAction suzukiCheckpointCriticalMertensDeviation H =
      suzukiCheckpointCriticalMertensDeviation 0 *
          suzukiCheckpointCriticalTriangularMultiplier H 0 +
      (64 / (Real.exp (H / 2) * H ^ 4)) *
        (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
            (1 - Real.sqrt ((j + 3 : ℕ) : ℝ) / Real.exp (H / 2))) +
      ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
          ∫ y in Real.sqrt ((j + 3 : ℕ) : ℝ)..Real.exp (H / 2),
            cauchyVolterraFUCurvature H y *
              cauchyVolterraKernel (Real.sqrt ((j + 3 : ℕ) : ℝ)) y := by
  rw [ccmFUSuzukiCriticalMertensDeviationVariationAction_eq_zeroClock_add_cauchyVolterraCells hH,
    ← cauchyVolterraFUProfile_endpointJet (ne_of_gt (by linarith : 0 < H))]

end

end RHTower
