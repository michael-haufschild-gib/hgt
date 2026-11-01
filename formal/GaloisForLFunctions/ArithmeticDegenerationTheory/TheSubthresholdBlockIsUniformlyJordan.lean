import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure

/-!
# The subthreshold block is uniformly Jordan

The Jordan-totient law `c⁷ E_m(c) → J(m)` holds for each fixed conductor. The degeneration is
self-similar in the conductor (`E_m(c) ≍ E₁(c/m)`), so the law should hold uniformly on the whole
**subthreshold block** `m ≪ c`, where the conductor mode has not yet reached the receiver. This file
proves it, with explicit uniformity.

* **Uniform Jordan law** (`uniform_jordan_law`): for every `ε > 0` there is `X` such that for all
  overlaps `c` and all conductors `m ≥ 1` with `X m ≤ c`,
  `|c⁷ E_m(c) − J(m)| ≤ ε J(m)`.
  In the coprime repayment series every term samples the spectral tail at `ac/m ≥ c/m ≥ X`, where
  `x⁷ T(x)` is already `ε`-close to its limit.
* **Schedules** (`tendsto_ratio_of_subthreshold`): along any pair of schedules `m_k ≥ 1`, `c_k` with
  `c_k/m_k → ∞`, the ratio `c_k⁷ E_{m_k}(c_k) / J(m_k)` tends to `1`.

So the weight structure of the degeneration is exact on the subthreshold block: there the graded
pieces carry precisely the Jordan polarization, uniformly in the conductor. The block `m ≍ c` is
where the conductor mode reaches the receiver, and the supra-threshold block `m ≫ c` is the pure
part, whose energies grow like `log m` (`CompletedArithmeticForms.completedConductorEnergy_log_lower`).
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The coprime form of the Jordan coefficient. -/
theorem jordanCoefficient_eq_coprime {m : ℕ} (hm : 0 < m) :
    jordanCoefficient m = 2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * (m : ℝ) ^ (8 : ℝ) *
      tiltedTailConstant * coprimeZetaSum 8 m := by
  have h := zetaSum_eight_mul_jordanTotient_eight hm
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hM := integral_tiltedUnitSpline_sq_pos
  unfold jordanCoefficient
  field_simp
  linear_combination (2 * tiltedTailConstant) * h

/-- **The uniform Jordan law on the subthreshold block.** -/
theorem uniform_jordan_law {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ c : ℝ, 0 < c → ∀ m : ℕ, 0 < m → X * m ≤ c →
      |c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m - jordanCoefficient m| ≤
        ε * jordanCoefficient m := by
  set A := tiltedTailConstant
  have hA := tiltedTailConstant_pos
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp tendsto_rpow_seven_mul_spectralTail_tiltedUnitSpline) (ε * A)
      (by positivity))
  refine ⟨max X₀ 1, le_max_right _ _, fun c hc m hm hXm => ?_⟩
  have hφ := contDiff_tiltedUnitSpline
  have hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → tiltedUnitSpline u = 0 :=
    fun u hu => tiltedUnitSpline_eq_zero u hu
  have hM := integral_tiltedUnitSpline_sq_pos
  set K := 2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * (m : ℝ) ^ ((7 : ℝ) + 1)
  have hK : 0 ≤ K := by
    have := Nat.totient_pos.mpr hm
    positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- the rescaled series and the limit series
  have hS := hasSum_rpow_mul_completedConductorEnergy hφ hsupp hM (β := 7) hc hm
  have hG : HasSum (fun n : ℕ => if Nat.Coprime m (n + 1) then
      K * (((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) * A) else 0) (K * A * coprimeZetaSum 8 m) := by
    have := ((summable_coprime_shift_rpow_neg (k := 8) (by norm_num) m).hasSum.mul_left (K * A))
    refine this.congr_fun fun n => ?_
    split_ifs <;> norm_num <;> ring
  have hD := hS.sub hG
  have hE : HasSum (fun n : ℕ => if Nat.Coprime m (n + 1) then
      K * ((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) * (ε * A) else 0) (K * (ε * A) * coprimeZetaSum 8 m) := by
    have := ((summable_coprime_shift_rpow_neg (k := 8) (by norm_num) m).hasSum.mul_left
      (K * (ε * A)))
    refine this.congr_fun fun n => ?_
    split_ifs <;> norm_num <;> ring
  have hbound : ∀ n : ℕ, ‖(if Nat.Coprime m (n + 1) then
      2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * (m : ℝ) ^ ((7 : ℝ) + 1) *
        (((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) * ((((n : ℝ) + 1) * c / m) ^ (7 : ℝ) *
          spectralTail tiltedUnitSpline (((n : ℝ) + 1) * c / m))) else 0) -
      (if Nat.Coprime m (n + 1) then K * (((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) * A) else 0)‖ ≤
        if Nat.Coprime m (n + 1) then K * ((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) * (ε * A) else 0 := by
    intro n
    split_ifs
    · have hx : X₀ ≤ ((n : ℝ) + 1) * c / m := by
        rw [le_div_iff₀ hm0]
        have h1 : X₀ * m ≤ c := (mul_le_mul_of_nonneg_right (le_max_left X₀ 1) hm0.le).trans hXm
        have h2 : c ≤ ((n : ℝ) + 1) * c := le_mul_of_one_le_left hc.le (by simp)
        linarith
      have hclose := hX₀ _ hx
      rw [Real.dist_eq] at hclose
      have hn : 0 ≤ ((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) := by positivity
      rw [Real.norm_eq_abs, show K * (((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) *
          ((((n : ℝ) + 1) * c / m) ^ (7 : ℝ) * spectralTail tiltedUnitSpline (((n : ℝ) + 1) * c / m))) -
          K * (((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) * A) =
          K * ((n : ℝ) + 1) ^ (-((7 : ℝ) + 1)) * ((((n : ℝ) + 1) * c / m) ^ (7 : ℝ) *
            spectralTail tiltedUnitSpline (((n : ℝ) + 1) * c / m) - A) by ring,
        abs_mul, abs_of_nonneg (mul_nonneg hK hn)]
      exact mul_le_mul_of_nonneg_left hclose.le (mul_nonneg hK hn)
    · simp
  have hle := hasSum_le (fun n => (abs_le.mp (hbound n)).2) hD hE
  have hge := hasSum_le (fun n => by
      have := (abs_le.mp (hbound n)).1
      linarith) (hE.neg) hD
  rw [jordanCoefficient_eq_coprime hm]
  have hval : 2 / ((∫ u, tiltedUnitSpline u ^ 2) * m.totient) * (m : ℝ) ^ (8 : ℝ) * A *
      coprimeZetaSum 8 m = K * A * coprimeZetaSum 8 m := by
    simp only [K]; norm_num
  rw [hval, abs_le]
  constructor <;> linarith

/-- **Schedules on the subthreshold block.** If `c_k/m_k → ∞`, the rescaled conductor energy is
asymptotic to the Jordan coefficient. -/
theorem tendsto_ratio_of_subthreshold {ι : Type*} {l : Filter ι} {c : ι → ℝ} {m : ι → ℕ}
    (hm : ∀ i, 0 < m i) (hc : ∀ i, 0 < c i)
    (hratio : Tendsto (fun i => c i / m i) l atTop) :
    Tendsto (fun i => c i ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline (c i) (m i) /
      jordanCoefficient (m i)) l (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨X, -, hX⟩ := uniform_jordan_law (ε := ε / 2) (by positivity)
  filter_upwards [hratio.eventually_ge_atTop X] with i hi
  have hm0 : (0 : ℝ) < m i := by exact_mod_cast hm i
  have hJ := jordanCoefficient_pos (hm i)
  have hXm : X * m i ≤ c i := by rwa [le_div_iff₀ hm0] at hi
  have h := hX (c i) (hc i) (m i) (hm i) hXm
  rw [Real.dist_eq, show c i ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline (c i) (m i) /
      jordanCoefficient (m i) - 1 = (c i ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline (c i)
        (m i) - jordanCoefficient (m i)) / jordanCoefficient (m i) by field_simp,
    abs_div, abs_of_pos hJ, div_lt_iff₀ hJ]
  linarith

end GaloisForLFunctions.ArithmeticDegenerationTheory
