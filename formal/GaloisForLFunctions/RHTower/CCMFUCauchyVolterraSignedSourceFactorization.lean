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

/--
An active lower endpoint can be moved to a common outer interval only by retaining its indicator.
The identity is exact for signed sources: no coefficient is discarded at the moving boundary.
-/
theorem cauchyVolterra_intervalIntegral_activeLower_eq
    {x ξ Y : ℝ} (hxξ : x ≤ ξ) (hξY : ξ ≤ Y) (g : ℝ → ℝ)
    (hleft : IntervalIntegrable (fun y => if ξ ≤ y then g y else 0) volume x ξ)
    (hright : IntervalIntegrable (fun y => if ξ ≤ y then g y else 0) volume ξ Y) :
    (∫ y in x..Y, if ξ ≤ y then g y else 0) = ∫ y in ξ..Y, g y := by
  have hzero : (∫ y in x..ξ, if ξ ≤ y then g y else 0) = 0 := by
    calc
      (∫ y in x..ξ, if ξ ≤ y then g y else 0) = ∫ y in x..ξ, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hxξ
        intro y hy
        simp [not_le_of_gt hy.2]
      _ = 0 := intervalIntegral.integral_zero
  have hid : (∫ y in ξ..Y, if ξ ≤ y then g y else 0) = ∫ y in ξ..Y, g y := by
    apply intervalIntegral.integral_congr_Ioo_of_le hξY
    intro y hy
    simp [hy.1.le]
  calc
    (∫ y in x..Y, if ξ ≤ y then g y else 0) =
        (∫ y in x..ξ, if ξ ≤ y then g y else 0) +
          ∫ y in ξ..Y, if ξ ≤ y then g y else 0 :=
      (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
    _ = _ := by rw [hzero, hid, zero_add]

/--
Finite signed Cauchy--Volterra transport with genuine variable lower clocks.

The active indicator is part of the transported source.  Omitting it would replace the physical
triangular source by a different common-base-point source.
-/
theorem cauchyVolterra_finite_signed_transport_variable_lower
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ξ : ι → ℝ)
    {x Y : ℝ} {q : ℝ → ℝ}
    (hrange : ∀ i ∈ s, x ≤ ξ i ∧ ξ i ≤ Y)
    (hleft : ∀ i ∈ s, IntervalIntegrable
      (fun y => if ξ i ≤ y then a i * (q y * cauchyVolterraKernel (ξ i) y) else 0)
      volume x (ξ i))
    (hright : ∀ i ∈ s, IntervalIntegrable
      (fun y => if ξ i ≤ y then a i * (q y * cauchyVolterraKernel (ξ i) y) else 0)
      volume (ξ i) Y)
    (hfull : ∀ i ∈ s, IntervalIntegrable
      (fun y => if ξ i ≤ y then a i * (q y * cauchyVolterraKernel (ξ i) y) else 0)
      volume x Y) :
    (∑ i ∈ s, a i * ∫ y in ξ i..Y, q y * cauchyVolterraKernel (ξ i) y) =
      ∫ y in x..Y, ∑ i ∈ s,
        if ξ i ≤ y then a i * (q y * cauchyVolterraKernel (ξ i) y) else 0 := by
  calc
    (∑ i ∈ s, a i * ∫ y in ξ i..Y, q y * cauchyVolterraKernel (ξ i) y) =
        ∑ i ∈ s, ∫ y in x..Y,
          if ξ i ≤ y then a i * (q y * cauchyVolterraKernel (ξ i) y) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← intervalIntegral.integral_const_mul]
          exact (cauchyVolterra_intervalIntegral_activeLower_eq
            (hrange i hi).1 (hrange i hi).2 _ (hleft i hi) (hright i hi)).symm
    _ = _ := (intervalIntegral.integral_finsetSum hfull).symm

/-- Active zeroth source moment at a common clock.  The indicator retains each cell's literal
moving lower endpoint. -/
def cauchyVolterraActiveZerothMoment {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ξ : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, if ξ i ≤ y then a i else 0

/-- Active first square-root-clock source moment at a common clock. -/
def cauchyVolterraActiveFirstMoment {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ξ : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, if ξ i ≤ y then a i * ξ i else 0

/-- The signed active Cauchy codiagonal has exactly two coupled source moments.  It is crucial
that this is a difference of moments *after* common active support has been imposed: separate
bounds on the two moments do not preserve the critical cancellation. -/
theorem cauchyVolterra_activeCodiagonal_eq_coupledMoments
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ξ : ι → ℝ)
    {y : ℝ} (hy : y ≠ 0) :
    (∑ i ∈ s, if ξ i ≤ y then a i * cauchyVolterraKernel (ξ i) y else 0) =
      cauchyVolterraActiveZerothMoment s a ξ y / y -
        cauchyVolterraActiveFirstMoment s a ξ y / y ^ 2 := by
  unfold cauchyVolterraActiveZerothMoment cauchyVolterraActiveFirstMoment
    cauchyVolterraKernel
  calc
    (∑ i ∈ s, if ξ i ≤ y then a i * (1 / y - ξ i / y ^ 2) else 0) =
        ∑ i ∈ s, ((if ξ i ≤ y then a i else 0) / y -
          (if ξ i ≤ y then a i * ξ i else 0) / y ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs with h
          · field_simp [hy]
          · simp
    _ = (∑ i ∈ s, if ξ i ≤ y then a i else 0) / y -
        (∑ i ∈ s, if ξ i ≤ y then a i * ξ i else 0) / y ^ 2 := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]

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

/-- Literal active zeroth moment of the critical finite prime--polar head. -/
noncomputable def ccmFUSuzukiCriticalActiveZerothMoment (H y : ℝ) : ℝ :=
  cauchyVolterraActiveZerothMoment
    (Finset.range (suzukiCheckpointEventIndex H - 2))
    (fun j => ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j)
    (fun j => Real.sqrt ((j + 3 : ℕ) : ℝ)) y

/-- Literal active first square-root-clock moment of the critical finite prime--polar head. -/
noncomputable def ccmFUSuzukiCriticalActiveFirstMoment (H y : ℝ) : ℝ :=
  cauchyVolterraActiveFirstMoment
    (Finset.range (suzukiCheckpointEventIndex H - 2))
    (fun j => ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j)
    (fun j => Real.sqrt ((j + 3 : ℕ) : ℝ)) y

/-- Minimal signed invariant carried by the literal critical finite head at clock `y`.
This is the codiagonal which must be controlled jointly under the positive FU curvature. -/
noncomputable def ccmFUSuzukiCriticalActiveCauchyCodiagonal (H y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    if Real.sqrt ((j + 3 : ℕ) : ℝ) ≤ y then
      (((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j) *
        cauchyVolterraKernel (Real.sqrt ((j + 3 : ℕ) : ℝ)) y
    else 0

/-- Exact two-moment reduction of the actual signed critical Cauchy codiagonal. -/
theorem ccmFUSuzukiCriticalActiveCauchyCodiagonal_eq_coupledMoments
    {H y : ℝ} (hy : y ≠ 0) :
    ccmFUSuzukiCriticalActiveCauchyCodiagonal H y =
      ccmFUSuzukiCriticalActiveZerothMoment H y / y -
        ccmFUSuzukiCriticalActiveFirstMoment H y / y ^ 2 := by
  exact cauchyVolterra_activeCodiagonal_eq_coupledMoments
    (Finset.range (suzukiCheckpointEventIndex H - 2))
    (fun j => ((j + 3 : ℕ) : ℝ) * ccmFUSuzukiCriticalPrimePolarIncrement j)
    (fun j => Real.sqrt ((j + 3 : ℕ) : ℝ)) hy

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
