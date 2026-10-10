import GaloisForLFunctions.RHTower.PhotonicLosslessStackFresnelChain
import GaloisForLFunctions.RHTower.LeeYangProducerFieldDensity
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya

/-!
# The integer clock of a lossless Ξ-medium runs at most at half rate

An integer-clock lossless temporal stack has slab `j` of duration
`c · log((j + 2)/(j + 1))`, so its interfaces sit at the times `c · log n`. The
Fresnel–Lee–Yang budget counts at least `Σ_j (⌈2τ_j T/2π⌉ - 1)` zeros of the
stack entry in the disc of diameter `[-η, T + η]`. The integer-clock durations
telescope: the first `T/2π` slabs alone force about `2c · log(T/2π)` zeros per
unit of `2π/T`. Ξ has only `(T/2π)(log(T/2π) - 1) + O(√T)` zeros there. Hence
for `c > 1/2` no normalized integer-clock lossless stack converges locally
uniformly to Ξ.

The rate `c = 1/2` is critical and is itself excluded. With interfaces at
`½ log n` the smooth parts of the forced count and of Ξ's count agree to first
order, but the ceiling budget adds the fractional excess of the slabs with
`M·log(1 + 1/m) ∈ (1, 3/2]`, about `M/6`. This beats the `O(√M)` error in Ξ's
zero count. So integer clocks compatible with Ξ run strictly slower than half
rate. One half is the supremum of compatible clock rates and is not attained.
`½ log n` is also where the Weil explicit formula places the prime-power echoes
(round trip `log n`).

The same budget gives the integer density law. For every scale `x`, eventually
the first `K` slabs of total duration `S_K` satisfy `K ≥ 2x·S_K - x log x + x - C√x`.
A lossless Ξ-medium therefore has at least `x - C√x` interfaces below depth
`½ log x`. The natural numbers are the minimal interface clock, and sparser
clocks such as the prime powers alone are excluded.
-/

open Complex Metric Set Filter Topology Finset
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Every zero of `Ξ` is the spectral point of a zero copy. -/
theorem exists_xiZeroCopy_of_XiC_eq_zero {z : ℂ} (hz : XiC z = 0) :
    ∃ q : XiZeroCopy, xiSpectralPoint q = z := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero (ρ := 1 / 2 + z * Complex.I) hz
  refine ⟨q, ?_⟩
  rw [xiSpectralPoint, hq]
  have hI : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  linear_combination z * hI

/-- **Admissible circles.** For every `T > 0` some `η ∈ (0, 1]` makes `Ξ`
zero-free on the circle `|z - T/2| = T/2 + η`. -/
theorem exists_admissible_eta (T : ℝ) (hT : 0 < T) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), XiC z ≠ 0 := by
  classical
  set m : ℕ := ⌈T + 1⌉₊ with hm
  set B : Set ℝ := (fun q : XiZeroCopy => ‖xiSpectralPoint q - (T : ℂ) / 2‖ - T / 2) ''
    (xiZeroBall m : Set XiZeroCopy) with hB
  have hBfin : B.Finite := (Finset.finite_toSet _).image _
  have hinf : (Ioc (0 : ℝ) 1).Infinite := Set.Ioc_infinite (by norm_num)
  obtain ⟨η, ⟨hη0, hη1⟩, hηB⟩ := (hinf.sdiff hBfin).nonempty
  refine ⟨η, hη0, hη1, fun z hz hzero => hηB ?_⟩
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_XiC_eq_zero hzero
  have hzd : ‖z - (T : ℂ) / 2‖ = T / 2 + η := by rw [← dist_eq_norm]; exact mem_sphere.mp hz
  refine ⟨q, ?_, ?_⟩
  · rw [Finset.mem_coe, mem_xiZeroBall, hq]
    have h2 : ‖(T : ℂ) / 2‖ = T / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]; norm_num
    have h3 : T + 1 ≤ (m : ℝ) := Nat.le_ceil _
    have h4 : ‖z‖ ≤ ‖z - (T : ℂ) / 2‖ + ‖(T : ℂ) / 2‖ := by
      have := norm_add_le (z - (T : ℂ) / 2) ((T : ℂ) / 2)
      simpa using this
    rw [hzd, h2] at h4
    linarith
  · simp only [hq, hzd]
    ring

/-- The integer-clock durations telescope. -/
theorem sum_integerClock_log (J : ℕ) :
    ∑ j ∈ range J, Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) = Real.log ((J : ℝ) + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp
    ring

/-- **Half-rate law.** For `c > 1/2`, no sequence of nonzero multiples of
integer-clock lossless stacks with slab durations `c·log((j+2)/(j+1))`, any
positive impedances and a number of slabs tending to infinity, converges locally
uniformly to `Ξ`. -/
theorem not_tendsto_XiC_of_integerClock_losslessStacks {c : ℝ} (hc : 1 / 2 < c)
    (κ : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (a : ℕ → ℂ) (hκ : ∀ n j, 0 < κ n j) (ha : ∀ n, a n ≠ 0)
    (hN : Tendsto N atTop atTop) :
    ¬ TendstoLocallyUniformly (fun n k => a n * ptrLosslessStackSeq (κ n)
        (fun j => c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) (N n) k 0 0) XiC atTop := by
  intro hconv
  have hc0 : 0 < c := by linarith
  have hπ := Real.pi_pos
  obtain ⟨C, hC, hbound⟩ := LeeYangCount.exists_two_pi_div_mul_xiZeroCount_le
  -- choose the scale `T = 2πM`
  obtain ⟨M, hM⟩ := exists_nat_ge (Real.exp (C / (2 * c - 1)) + 3)
  have hM3 : (3 : ℝ) ≤ M := by linarith [Real.exp_pos (C / (2 * c - 1))]
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogM : C < (2 * c - 1) * Real.log M := by
    have h1 : C / (2 * c - 1) < Real.log M := by
      rw [Real.lt_log_iff_exp_lt hMpos]; linarith
    have h2 : 0 < 2 * c - 1 := by linarith
    rw [div_lt_iff₀ h2] at h1
    linarith
  set T : ℝ := 2 * Real.pi * M with hTdef
  have hT : 0 < T := by positivity
  have hT4 : 4 ≤ T := by
    have : (2 : ℝ) * 3 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith
  obtain ⟨η, hη0, hη1, hsph⟩ := exists_admissible_eta T hT
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hτpos : ∀ (n j : ℕ), 0 < c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
    intro n j
    apply mul_pos hc0
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    linarith
  have hbud := ptrLosslessStackSeq_eventually_budget κ
    (fun (_ : ℕ) (j : ℕ) => c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) N a hκ hτpos ha hXiCd
    hconv hT hη0
    hsph
  have hcount : (zeroSumBall XiC ((T : ℂ) / 2) (T / 2 + η)).re ≤ (xiZeroCount (T + η) : ℝ) := by
    have h := LeeYangCount.zeroSumBall_le_xiZeroCount (E := fun _ => (1 : ℂ))
      (differentiable_const _) (fun _ => one_ne_zero) hT hη0 hη1
      (fun z hz => by simpa using hsph z hz)
    simpa using h
  have hgamma := hbound T η hT4 hη0 hη1
  have hNev : ∀ᶠ n in atTop, M ≤ N n + 1 := by
    filter_upwards [hN.eventually_ge_atTop M] with n hn
    omega
  obtain ⟨n, hn1, hn2⟩ := (hbud.and hNev).exists
  -- lower bound of the budget by the first `M` slabs
  have hlow : 2 * c * Real.log ((M : ℝ) + 1) - 1 ≤
      2 * Real.pi / T * ∑ j : Fin (N n + 1),
        (((⌈(2 * (c * Real.log (((j : ℕ) + 2 : ℝ) / ((j : ℕ) + 1)))) * T /
          (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) := by
    have hterm : ∀ j : Fin (N n + 1),
        max (2 * (c * Real.log (((j : ℕ) + 2 : ℝ) / ((j : ℕ) + 1))) - 2 * Real.pi / T) 0 ≤
          2 * Real.pi / T * ((((⌈(2 * (c * Real.log (((j : ℕ) + 2 : ℝ) / ((j : ℕ) + 1)))) * T /
            (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)) := fun j =>
      LeeYangCount.max_sub_le_mul_ceil_sub_one (by have := hτpos n j; positivity) hT
    rw [Finset.mul_sum]
    refine le_trans ?_ (Finset.sum_le_sum fun j _ => hterm j)
    -- restrict to the first `M` slabs
    have hsub : ∑ j ∈ range M, (2 * (c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) -
        2 * Real.pi / T) ≤ ∑ j : Fin (N n + 1),
        max (2 * (c * Real.log (((j : ℕ) + 2 : ℝ) / ((j : ℕ) + 1))) - 2 * Real.pi / T) 0 := by
      calc ∑ j ∈ range M, (2 * (c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) - 2 * Real.pi / T)
          ≤ ∑ j ∈ range (N n + 1),
            max (2 * (c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) - 2 * Real.pi / T) 0 := by
            calc _ ≤ ∑ j ∈ range M,
                  max (2 * (c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) - 2 * Real.pi / T) 0 :=
                Finset.sum_le_sum fun j _ => le_max_left _ _
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn2)
                  fun j _ _ => le_max_right _ _
        _ = _ := (Fin.sum_univ_eq_sum_range (fun j =>
            max (2 * (c * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) - 2 * Real.pi / T) 0)
              (N n + 1)).symm
    refine le_trans ?_ hsub
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_integerClock_log,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hMT : (M : ℝ) * (2 * Real.pi / T) = 1 := by
      rw [hTdef]; field_simp
    nlinarith [hMT]
  -- upper bound via the zero count
  have hup : 2 * Real.pi / T * ∑ j : Fin (N n + 1),
        (((⌈(2 * (c * Real.log (((j : ℕ) + 2 : ℝ) / ((j : ℕ) + 1)))) * T /
          (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤
      Real.log (T / (2 * Real.pi)) - 1 + C / Real.sqrt T :=
    (mul_le_mul_of_nonneg_left (hn1.trans hcount) (by positivity)).trans hgamma
  have hTM : T / (2 * Real.pi) = M := by rw [hTdef]; field_simp
  rw [hTM] at hup
  have hsqrt : C / Real.sqrt T ≤ C := by
    apply div_le_self hC
    rw [Real.le_sqrt (by norm_num) hT.le]
    linarith
  have hlog1 : Real.log M ≤ Real.log ((M : ℝ) + 1) :=
    Real.log_le_log hMpos (by linarith)
  have hlogpos : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  nlinarith [hlow, hup, hlogM, hsqrt, hlog1]

/-- **Strict half-rate law.** Even at the critical rate `c = 1/2` no sequence of
nonzero multiples of integer-clock lossless stacks, with slab durations
`½·log((j+2)/(j+1))`, any positive impedances and a number of slabs tending to
infinity, converges locally uniformly to `Ξ`. The ceiling Lee–Yang budget exceeds
the smooth count by the fractional excess of the slabs with
`M·log(1 + 1/m) ∈ (1, 3/2]`, about `M/6`, which beats the `O(√M)` error in Ξ's
zero count. Integer clocks compatible with `Ξ` run strictly slower than half
rate. -/
theorem not_tendsto_XiC_of_halfRate_integerClock_losslessStacks
    (κ : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (a : ℕ → ℂ) (hκ : ∀ n j, 0 < κ n j) (ha : ∀ n, a n ≠ 0)
    (hN : Tendsto N atTop atTop) :
    ¬ TendstoLocallyUniformly (fun n k => a n * ptrLosslessStackSeq (κ n)
        (fun j => 1 / 2 * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) (N n) k 0 0) XiC atTop := by
  intro hconv
  have hπ := Real.pi_pos
  obtain ⟨C, hC, hbound⟩ := LeeYangCount.exists_two_pi_div_mul_xiZeroCount_le
  obtain ⟨M, hM⟩ := exists_nat_ge ((6 * C + 6) ^ 2 + 12)
  have hM12 : (12 : ℝ) ≤ M := by nlinarith [sq_nonneg (6 * C + 6)]
  have hMpos : (0 : ℝ) < M := by linarith
  have hsqrtM : 6 * C + 6 ≤ Real.sqrt M := by
    rw [Real.le_sqrt (by positivity) hMpos.le]
    nlinarith [sq_nonneg (6 * C + 6)]
  set T : ℝ := 2 * Real.pi * M with hTdef
  have hT : 0 < T := by positivity
  have hT4 : 4 ≤ T := by
    have : (2 : ℝ) * 3 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith
  obtain ⟨η, hη0, hη1, hsph⟩ := exists_admissible_eta T hT
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hlogpos : ∀ j : ℕ, 0 < Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
    intro j
    apply Real.log_pos
    rw [one_lt_div (by positivity)]
    linarith
  have hτpos : ∀ (n j : ℕ), 0 < 1 / 2 * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) :=
    fun _ j => by have := hlogpos j; positivity
  have hbud := ptrLosslessStackSeq_eventually_budget κ
    (fun (_ : ℕ) (j : ℕ) => 1 / 2 * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1))) N a hκ hτpos ha
    hXiCd hconv hT hη0 hsph
  have hcount : (zeroSumBall XiC ((T : ℂ) / 2) (T / 2 + η)).re ≤ (xiZeroCount (T + η) : ℝ) := by
    have h := LeeYangCount.zeroSumBall_le_xiZeroCount (E := fun _ => (1 : ℂ))
      (differentiable_const _) (fun _ => one_ne_zero) hT hη0 hη1
      (fun z hz => by simpa using hsph z hz)
    simpa using h
  have hgamma := hbound T η hT4 hη0 hη1
  have hNev : ∀ᶠ n in atTop, M ≤ N n + 1 := by
    filter_upwards [hN.eventually_ge_atTop M] with n hn
    omega
  obtain ⟨n, hn1, hn2⟩ := (hbud.and hNev).exists
  -- the slab terms, `y_j = M log((j+2)/(j+1))`
  set y : ℕ → ℝ := fun j => M * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) with hydef
  have hyterm : ∀ j : ℕ, (2 * (1 / 2 * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)))) * T /
      (2 * Real.pi) = y j := by
    intro j; rw [hydef, hTdef]; field_simp
  -- every term is at least `y - 1`, and at least `0`
  have hge : ∀ j : ℕ, y j - 1 ≤ (((⌈y j⌉ : ℤ) : ℝ) - 1) := fun j => by
    linarith [Int.le_ceil (y j)]
  have hnonneg : ∀ j : ℕ, 0 ≤ (((⌈y j⌉ : ℤ) : ℝ) - 1) := by
    intro j
    have hy : 0 < y j := by rw [hydef]; exact mul_pos hMpos (hlogpos j)
    have h1 : (1 : ℤ) ≤ ⌈y j⌉ := Int.one_le_ceil_iff.mpr hy
    have h2 : (1 : ℝ) ≤ ((⌈y j⌉ : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  -- the window `⌈2M/3⌉ - 1 ≤ j < M - 2` gains one half
  set A : ℕ := ⌈2 * (M : ℝ) / 3⌉₊ - 1 with hAdef
  have hgain : ∀ j ∈ Finset.Ico A (M - 2), y j - 1 / 2 ≤ (((⌈y j⌉ : ℤ) : ℝ) - 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hj1 : 2 * (M : ℝ) / 3 ≤ (j : ℝ) + 1 := by
      have h := Nat.le_ceil (2 * (M : ℝ) / 3)
      have hA1 : (⌈2 * (M : ℝ) / 3⌉₊ : ℝ) ≤ (A : ℝ) + 1 := by
        have : ⌈2 * (M : ℝ) / 3⌉₊ ≤ A + 1 := by rw [hAdef]; omega
        exact_mod_cast this
      have : (A : ℝ) ≤ j := by exact_mod_cast hj.1
      linarith
    have hj2 : (j : ℝ) + 2 < M := by
      have : j + 2 < M := by omega
      exact_mod_cast this
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hupper : y j ≤ 3 / 2 := by
      have hlog : Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) ≤ 1 / ((j : ℝ) + 1) := by
        have := Real.log_le_sub_one_of_pos (show 0 < ((j : ℝ) + 2) / ((j : ℝ) + 1) by positivity)
        have he : ((j : ℝ) + 2) / ((j : ℝ) + 1) - 1 = 1 / ((j : ℝ) + 1) := by field_simp; ring
        linarith
      rw [hydef]
      calc (M : ℝ) * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) ≤ M * (1 / ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hlog hMpos.le
        _ ≤ 3 / 2 := by
          rw [mul_one_div, div_le_iff₀ hj0]
          linarith
    have hlower : 1 < y j := by
      have hlog : 1 / ((j : ℝ) + 2) ≤ Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
        have := Real.one_sub_inv_le_log_of_pos
          (show 0 < ((j : ℝ) + 2) / ((j : ℝ) + 1) by positivity)
        have he : 1 - (((j : ℝ) + 2) / ((j : ℝ) + 1))⁻¹ = 1 / ((j : ℝ) + 2) := by
          field_simp; ring
        linarith
      rw [hydef]
      calc (1 : ℝ) < M * (1 / ((j : ℝ) + 2)) := by
            rw [mul_one_div, lt_div_iff₀ (by positivity)]
            linarith
        _ ≤ M * Real.log (((j : ℝ) + 2) / ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hlog hMpos.le
    have h2 : (2 : ℤ) ≤ ⌈y j⌉ := by
      rw [Int.le_ceil_iff]
      push_cast
      linarith
    have h2' : (2 : ℝ) ≤ ((⌈y j⌉ : ℤ) : ℝ) := by exact_mod_cast h2
    linarith
  have hAM : Finset.Ico A (M - 2) ⊆ range M := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_range]
    omega
  have hcard : (M : ℝ) / 3 - 2 ≤ ((Finset.Ico A (M - 2)).card : ℝ) := by
    rw [Nat.card_Ico]
    have hceil : (⌈2 * (M : ℝ) / 3⌉₊ : ℝ) < 2 * (M : ℝ) / 3 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hceilM : ⌈2 * (M : ℝ) / 3⌉₊ ≤ M - 2 := by
      have : (⌈2 * (M : ℝ) / 3⌉₊ : ℝ) ≤ (M : ℝ) - 2 := by linarith
      have h' : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by
        rw [Nat.cast_sub (by exact_mod_cast (show (2 : ℝ) ≤ M by linarith))]; norm_num
      exact_mod_cast (h' ▸ this)
    have hsub : ((M - 2 - A : ℕ) : ℝ) = (M : ℝ) - 2 - ((⌈2 * (M : ℝ) / 3⌉₊ : ℝ) - 1) := by
      rw [hAdef]
      have h1 : 1 ≤ ⌈2 * (M : ℝ) / 3⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by exact_mod_cast
        (show (2 : ℝ) ≤ M by linarith)), Nat.cast_sub h1]
      push_cast; ring
    rw [hsub]
    linarith
  -- assemble the lower bound
  have hlow : (M : ℝ) * Real.log ((M : ℝ) + 1) - M + ((M : ℝ) / 3 - 2) / 2 ≤
      ∑ j : Fin (N n + 1), (((⌈y j⌉ : ℤ) : ℝ) - 1) := by
    have hrange : ∑ j ∈ range M, (((⌈y j⌉ : ℤ) : ℝ) - 1) ≤ ∑ j : Fin (N n + 1),
        (((⌈y j⌉ : ℤ) : ℝ) - 1) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (((⌈y j⌉ : ℤ) : ℝ) - 1)) (N n + 1)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn2)
        fun j _ _ => hnonneg j
    refine le_trans ?_ hrange
    have hsplit : ∑ j ∈ range M, (((⌈y j⌉ : ℤ) : ℝ) - 1) ≥
        ∑ j ∈ range M, (y j - 1) + ∑ j ∈ Finset.Ico A (M - 2), (1 / 2 : ℝ) := by
      rw [← Finset.sum_sdiff hAM]
      have h1 : ∑ j ∈ range M \ Finset.Ico A (M - 2), (y j - 1) ≤
          ∑ j ∈ range M \ Finset.Ico A (M - 2), (((⌈y j⌉ : ℤ) : ℝ) - 1) :=
        Finset.sum_le_sum fun j _ => hge j
      have h2 : ∑ j ∈ Finset.Ico A (M - 2), (y j - 1 / 2) ≤
          ∑ j ∈ Finset.Ico A (M - 2), (((⌈y j⌉ : ℤ) : ℝ) - 1) :=
        Finset.sum_le_sum fun j hj => hgain j hj
      have h3 : ∑ j ∈ range M, (y j - 1) = ∑ j ∈ range M \ Finset.Ico A (M - 2), (y j - 1) +
          ∑ j ∈ Finset.Ico A (M - 2), (y j - 1) := (Finset.sum_sdiff hAM).symm
      have h4 : ∑ j ∈ Finset.Ico A (M - 2), (y j - 1 / 2) =
          ∑ j ∈ Finset.Ico A (M - 2), (y j - 1) + ∑ j ∈ Finset.Ico A (M - 2), (1 / 2 : ℝ) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    have hy : ∑ j ∈ range M, (y j - 1) = M * Real.log ((M : ℝ) + 1) - M := by
      rw [Finset.sum_sub_distrib, hydef]
      simp only [← Finset.mul_sum, sum_integerClock_log, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
    have hhalf : ∑ j ∈ Finset.Ico A (M - 2), (1 / 2 : ℝ) =
        ((Finset.Ico A (M - 2)).card : ℝ) / 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    rw [hy, hhalf] at hsplit
    linarith
  -- assemble the upper bound
  have hup : ∑ j : Fin (N n + 1), (((⌈y j⌉ : ℤ) : ℝ) - 1) ≤
      M * (Real.log M - 1 + C / Real.sqrt T) := by
    have h1 := hn1.trans hcount
    simp only [hyterm] at h1
    have hTM : T / (2 * Real.pi) = M := by rw [hTdef]; field_simp
    rw [hTM] at hgamma
    have h2 : (xiZeroCount (T + η) : ℝ) ≤ M * (Real.log M - 1 + C / Real.sqrt T) := by
      have := hgamma
      rw [show 2 * Real.pi / T = 1 / M by rw [hTdef]; field_simp] at this
      rw [one_div, inv_mul_le_iff₀ hMpos] at this
      exact this
    exact h1.trans h2
  have hsqrtT : Real.sqrt M ≤ Real.sqrt T := Real.sqrt_le_sqrt (by
    rw [hTdef]; nlinarith [Real.pi_gt_three])
  have hsqrtMpos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hCT : M * (C / Real.sqrt T) ≤ C * Real.sqrt M := by
    have h1 : C / Real.sqrt T ≤ C / Real.sqrt M := div_le_div_of_nonneg_left hC hsqrtMpos hsqrtT
    have h2 : (M : ℝ) * (C / Real.sqrt M) = C * Real.sqrt M := by
      rw [mul_div_assoc', div_eq_iff hsqrtMpos.ne', mul_assoc, Real.mul_self_sqrt hMpos.le]
      ring
    calc (M : ℝ) * (C / Real.sqrt T) ≤ M * (C / Real.sqrt M) :=
          mul_le_mul_of_nonneg_left h1 hMpos.le
      _ = C * Real.sqrt M := h2
  have hlog1 : Real.log M ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log hMpos (by linarith)
  have hMsq : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hMpos.le
  nlinarith [hlow, hup, hCT, hlog1, hsqrtM, hMsq, hsqrtMpos]

/-- **Integer density law.** There is an absolute `C` such that for every lossless
stack approximant of `Ξ` and every scale `x ≥ 1`, eventually the first `K` slabs,
of total duration `S_K`, satisfy `K ≥ 2x·S_K - x·log x + x - C√x`. In
particular, once the medium reaches depth `½ log x` it has at least `x - C√x`
interfaces below that depth. The natural numbers are therefore the minimal
interface clock of a lossless Ξ-medium. -/
theorem exists_integerDensity_law : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (κ τ : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (a : ℕ → ℂ), (∀ n j, 0 < κ n j) → (∀ n j, 0 < τ n j) →
      (∀ n, a n ≠ 0) →
      TendstoLocallyUniformly (fun n k => a n * ptrLosslessStackSeq (κ n) (τ n) (N n) k 0 0)
        XiC atTop →
      ∀ x : ℝ, 1 ≤ x → ∀ᶠ n in atTop, ∀ K ≤ N n + 1,
        2 * x * ∑ j ∈ range K, τ n j - x * Real.log x + x - C * Real.sqrt x ≤ K := by
  obtain ⟨C, hC, hbound⟩ := LeeYangCount.exists_two_pi_div_mul_xiZeroCount_le
  refine ⟨C, hC, fun κ τ N a hκ hτ ha hconv x hx => ?_⟩
  have hπ := Real.pi_pos
  have hxpos : 0 < x := by linarith
  set T : ℝ := 2 * Real.pi * x with hTdef
  have hT : 0 < T := by positivity
  have hT4 : 4 ≤ T := by
    have : (2 : ℝ) * 3 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith
  obtain ⟨η, hη0, hη1, hsph⟩ := exists_admissible_eta T hT
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hbud := ptrLosslessStackSeq_eventually_budget κ τ N a hκ hτ ha hXiCd hconv hT hη0 hsph
  have hcount : (zeroSumBall XiC ((T : ℂ) / 2) (T / 2 + η)).re ≤ (xiZeroCount (T + η) : ℝ) := by
    have h := LeeYangCount.zeroSumBall_le_xiZeroCount (E := fun _ => (1 : ℂ))
      (differentiable_const _) (fun _ => one_ne_zero) hT hη0 hη1
      (fun z hz => by simpa using hsph z hz)
    simpa using h
  have hgamma := hbound T η hT4 hη0 hη1
  have hTx : T / (2 * Real.pi) = x := by rw [hTdef]; field_simp
  have hNbound : (xiZeroCount (T + η) : ℝ) ≤ x * Real.log x - x + C * Real.sqrt x := by
    rw [hTx] at hgamma
    have h1 : 2 * Real.pi / T = 1 / x := by rw [hTdef]; field_simp
    rw [h1, one_div, inv_mul_le_iff₀ hxpos] at hgamma
    have hsqrt : x * (C / Real.sqrt T) ≤ C * Real.sqrt x := by
      have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
      have hle : Real.sqrt x ≤ Real.sqrt T := Real.sqrt_le_sqrt (by
        rw [hTdef]; nlinarith [Real.pi_gt_three])
      have h2 : C / Real.sqrt T ≤ C / Real.sqrt x := div_le_div_of_nonneg_left hC hsx hle
      have h3 : x * (C / Real.sqrt x) = C * Real.sqrt x := by
        rw [mul_div_assoc', div_eq_iff hsx.ne', mul_assoc, Real.mul_self_sqrt hxpos.le]
        ring
      calc x * (C / Real.sqrt T) ≤ x * (C / Real.sqrt x) :=
            mul_le_mul_of_nonneg_left h2 hxpos.le
        _ = C * Real.sqrt x := h3
    nlinarith [hgamma, hsqrt]
  filter_upwards [hbud] with n hn K hK
  have hyterm : ∀ j : ℕ, (2 * τ n j) * T / (2 * Real.pi) = 2 * x * τ n j := by
    intro j; rw [hTdef]; field_simp
  have hnonneg : ∀ j : ℕ, 0 ≤ (((⌈(2 * τ n j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) := by
    intro j
    have hy : 0 < (2 * τ n j) * T / (2 * Real.pi) := by have := hτ n j; positivity
    have h1 : (1 : ℤ) ≤ ⌈(2 * τ n j) * T / (2 * Real.pi)⌉ := Int.one_le_ceil_iff.mpr hy
    have h2 : (1 : ℝ) ≤ ((⌈(2 * τ n j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  have hpartial : ∑ j ∈ range K, (2 * x * τ n j - 1) ≤
      ∑ j : Fin (N n + 1), (((⌈(2 * τ n j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (((⌈(2 * τ n j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1))
      (N n + 1)]
    calc ∑ j ∈ range K, (2 * x * τ n j - 1)
        ≤ ∑ j ∈ range K, (((⌈(2 * τ n j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) :=
          Finset.sum_le_sum fun j _ => by
            have := Int.le_ceil ((2 * τ n j) * T / (2 * Real.pi))
            rw [hyterm] at this ⊢
            linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hK)
          fun j _ _ => hnonneg j
  have hsum : ∑ j ∈ range K, (2 * x * τ n j - 1) = 2 * x * ∑ j ∈ range K, τ n j - K := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have := (hpartial.trans hn).trans (hcount.trans hNbound)
  rw [hsum] at this
  linarith

end

end RHTower
