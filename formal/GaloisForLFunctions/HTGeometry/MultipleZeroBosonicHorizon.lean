import GaloisForLFunctions.HTGeometry.GammaSimpleZeroBellHorizonAnalytic

/-!
# Multiple-zero bosonic holographic horizon

At a zero of multiplicity `m`, the highest-pole residue of the `k`th normalized derivative is the
falling factorial `m.descFactorial k`.  These are exactly the normally ordered factorial moments
of a bosonic number state of occupation `m`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- A local analytic section with a zero of order `m` and regular unit `U`. -/
def multipleZeroSection (m : ℕ) (U : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ m * U z

/-- Leibniz expansion of every derivative of a multiple-zero section. -/
theorem iteratedDeriv_multipleZeroSection
    (m k : ℕ) {U : ℂ → ℂ} {z : ℂ} (hU : AnalyticAt ℂ U z) :
    iteratedDeriv k (multipleZeroSection m U) z =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * (m.descFactorial i : ℂ) * z ^ (m - i) *
          iteratedDeriv (k - i) U z := by
  change iteratedDeriv k ((fun z : ℂ => z ^ m) * U) z = _
  rw [iteratedDeriv_mul
    (by fun_prop : ContDiffAt ℂ k (fun z : ℂ => z ^ m) z)
    (hU.contDiffAt.of_le le_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_pow]
  ring

/-- Away from the crossing, scaling the normalized derivative by its predicted pole order exposes
the finite Leibniz boundary packet. -/
theorem scaled_multipleZeroCorrelator_eq
    (m k : ℕ) (hk : k ≤ m) {U : ℂ → ℂ} {z : ℂ}
    (hU : AnalyticAt ℂ U z) (hz : z ≠ 0) (hUz : U z ≠ 0) :
    z ^ k *
        (iteratedDeriv k (multipleZeroSection m U) z /
          multipleZeroSection m U z) =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * (m.descFactorial i : ℂ) * z ^ (k - i) *
          (iteratedDeriv (k - i) U z / U z) := by
  rw [iteratedDeriv_multipleZeroSection m k hU]
  simp only [multipleZeroSection, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have him : i ≤ m := hik.trans hk
  field_simp
  calc
    z ^ k * (k.choose i : ℂ) * (m.descFactorial i : ℂ) * z ^ (m - i) *
          iteratedDeriv (k - i) U z =
        (k.choose i : ℂ) * (m.descFactorial i : ℂ) *
          iteratedDeriv (k - i) U z * (z ^ k * z ^ (m - i)) := by ring
    _ = (k.choose i : ℂ) * (m.descFactorial i : ℂ) *
          iteratedDeriv (k - i) U z * z ^ (k + (m - i)) := by rw [pow_add]
    _ = (k.choose i : ℂ) * (m.descFactorial i : ℂ) *
          iteratedDeriv (k - i) U z * z ^ (m + (k - i)) := by
            congr 2
            omega
    _ = (k.choose i : ℂ) * (m.descFactorial i : ℂ) *
          iteratedDeriv (k - i) U z * z ^ m * z ^ (k - i) := by
            rw [pow_add]
            ring

/-- **Bosonic number-state principal symbol.**  The highest-pole residue of the `k`th normalized
derivative at a zero of multiplicity `m` is the falling factorial `m.descFactorial k`. -/
theorem tendsto_scaled_multipleZeroCorrelator_descFactorial
    (m k : ℕ) (hk : k ≤ m) {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 ≠ 0) :
    Tendsto
      (fun z : ℂ => z ^ k *
        (iteratedDeriv k (multipleZeroSection m U) z /
          multipleZeroSection m U z))
      (𝓝[≠] 0) (𝓝 (m.descFactorial k : ℂ)) := by
  have hz : Tendsto (fun z : ℂ => z) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hUan : ∀ᶠ z : ℂ in 𝓝[≠] 0, AnalyticAt ℂ U z :=
    nhdsWithin_le_nhds hU.eventually_analyticAt
  have hUne : ∀ᶠ z : ℂ in 𝓝[≠] 0, U z ≠ 0 :=
    nhdsWithin_le_nhds (hU.continuousAt.eventually_ne hU0)
  have heq :
      (fun z : ℂ => z ^ k *
        (iteratedDeriv k (multipleZeroSection m U) z /
          multipleZeroSection m U z)) =ᶠ[𝓝[≠] 0]
      (fun z : ℂ => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * (m.descFactorial i : ℂ) * z ^ (k - i) *
          (iteratedDeriv (k - i) U z / U z)) := by
    filter_upwards [self_mem_nhdsWithin, hUan, hUne] with z hz0 hUz hUnez
    exact scaled_multipleZeroCorrelator_eq m k hk hUz hz0 hUnez
  have hterm : ∀ i ∈ Finset.range (k + 1),
      Tendsto
        (fun z : ℂ =>
          (k.choose i : ℂ) * (m.descFactorial i : ℂ) * z ^ (k - i) *
            (iteratedDeriv (k - i) U z / U z))
        (𝓝[≠] 0)
        (𝓝 (if i = k then (m.descFactorial k : ℂ) else 0)) := by
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hder : Tendsto (iteratedDeriv (k - i) U) (𝓝[≠] 0)
        (𝓝 (iteratedDeriv (k - i) U 0)) :=
      (analyticAt_iteratedDeriv_of_analyticAt hU (k - i)).continuousAt.tendsto.mono_left
        inf_le_left
    have hden : Tendsto U (𝓝[≠] 0) (𝓝 (U 0)) :=
      hU.continuousAt.tendsto.mono_left inf_le_left
    have hquot := hder.div hden hU0
    by_cases hik' : i = k
    · subst i
      simpa [hU0, mul_assoc] using hquot.const_mul (m.descFactorial k : ℂ)
    · have hlt : i < k := lt_of_le_of_ne hik hik'
      have hpow : Tendsto (fun z : ℂ => z ^ (k - i)) (𝓝[≠] 0) (𝓝 0) := by
        simpa [zero_pow (Nat.sub_pos_of_lt hlt).ne'] using hz.pow (k - i)
      convert ((hpow.mul hquot).const_mul
        ((k.choose i : ℂ) * (m.descFactorial i : ℂ))) using 1 <;>
        simp [hik', mul_assoc]
  have hsum := tendsto_finsetSum (s := Finset.range (k + 1)) fun i hi => hterm i hi
  have hlimsum :
      (∑ i ∈ Finset.range (k + 1),
        (if i = k then (m.descFactorial k : ℂ) else 0)) =
        (m.descFactorial k : ℂ) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i hi hne
      simp [hne]
    · simp
  rw [hlimsum] at hsum
  exact hsum.congr' heq.symm

end

end GaloisForLFunctions
