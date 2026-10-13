import GaloisForLFunctions.HTGeometry.BandLimitedPositiveConfiguration
import GaloisForLFunctions.HTGeometry.LocallyFiniteExponentialSumRigidity

/-!
# Lag sums on all long spacings: local finiteness is the dividing line

The lag sum of a weighted configuration is `Σ_i c_i e^{s(ρ_i − ½)}`. A lag progression samples it at
`s = mℓ`, `m ∈ ℤ`.

**Theorem** (`exists_positive_lag_configuration_bandLimited`). For every `ε > 0` and `Θ > 0` there is
a countable configuration `ρ_i` with `½ < Re ρ_i < ½ + Θ` and positive summable weights `c_i` whose lag
sum vanishes at every real `s` with `|s| ≥ ε`. So every sample `m ≠ 0` of every lag progression with
spacing `ℓ ≥ ε` vanishes, simultaneously for all such spacings; the same holds for the symmetric
configuration `{ρ_i, ρ̄_i, 1 − ρ̄_i, 1 − ρ_i}` (`exists_symmetric_lag_configuration_bandLimited`).
Such a configuration has infinitely many points of bounded height.

**Theorem** (`eq_zero_of_lag_vanishing_halfLine`, `eq_zero_of_lag_vanishing_interval_spacings`). If
the ordinates are locally finite, the real parts bounded above and the weights summable, a lag sum
vanishing on a half-line `s ≥ s₀`, or on all progressions `mℓ`, `m ≥ 1`, with `ℓ` in an interval
`(c, d)`, has all weights zero.

So zero-side receivers that read the lag sum along all spacings of an interval are rigid exactly
for locally finite configurations: the rigidity comes from the Cauchy series `Σ c_i/(z − ρ_i)`
being meromorphic, and it fails as soon as the points may accumulate at finite height.

**Proofs.** The construction is `exists_positive_configuration_bandLimited` (disc packing of the
region under `sinc(εy/2)²` in `ℂ × ℝ`) shifted by `½`; conjugation and `s ↦ −s` give the symmetric
copies. The rigidity is `eq_zero_of_hasSum_cexp_eq_zero` (identity theorem for the Cauchy series off
its poles); for spacings in `(c, d)` the products `mℓ` cover `[s₀, ∞)` once `s₀ > cd/(d − c)`.
-/

open Set Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.BandLimitedPositiveConfiguration
open GaloisForLFunctions.HTGeometry.LocallyFiniteExponentialSumRigidity

/-- **Band-limited positive lag configurations.** -/
theorem exists_positive_lag_configuration_bandLimited {ε Θ : ℝ} (hε : 0 < ε) (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ),
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧ (∀ i, 0 < c i) ∧ Summable c ∧
      Nonempty ι ∧
      ∀ s : ℝ, ε ≤ |s| → HasSum (fun i => (c i : ℂ) * cexp (s * (ρ i - 1 / 2))) 0 := by
  obtain ⟨ι, hι, w, c, hw, hc, hmass, hvan⟩ :=
    exists_positive_configuration_bandLimited (x₁ := 0) (x₂ := Θ) hε hΘ
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : HasSum c 0 := hasSum_empty
    have := h0.unique hmass
    have hpos : 0 < (Θ - 0) * (2 * Real.pi / ε) := by
      have := Real.pi_pos; positivity
    linarith
  refine ⟨ι, hι, fun i => w i + 1 / 2, c, fun i => ?_, hc, hmass.summable, hne, fun s hs => ?_⟩
  · have h := hw i
    simp only [Complex.add_re, one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat]
    constructor <;> norm_num <;> linarith [h.1, h.2]
  · have h := hvan s hs
    simpa using h

/-- **Every long progression is blind.** All samples `m ≠ 0` at every spacing `ℓ ≥ ε` vanish. -/
theorem exists_positive_lag_configuration_vanishing_long_progressions {ε Θ : ℝ} (hε : 0 < ε)
    (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ),
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧ (∀ i, 0 < c i) ∧ Summable c ∧
      Nonempty ι ∧
      ∀ ℓ : ℝ, ε ≤ ℓ → ∀ m : ℤ, m ≠ 0 →
        HasSum (fun i => (c i : ℂ) * cexp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0 := by
  obtain ⟨ι, hι, ρ, c, hρ, hc, hs, hne, hvan⟩ := exists_positive_lag_configuration_bandLimited hε hΘ
  refine ⟨ι, hι, ρ, c, hρ, hc, hs, hne, fun ℓ hℓ m hm => hvan _ ?_⟩
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < ℓ)]
  nlinarith

/-- **The symmetric configuration.** With the four copies `ρ, ρ̄, 1 − ρ̄, 1 − ρ` of every point, the
lag sum still vanishes for every real `|s| ≥ ε`. -/
theorem exists_symmetric_lag_configuration_bandLimited {ε Θ : ℝ} (hε : 0 < ε) (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ),
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧ (∀ i, 0 < c i) ∧ Summable c ∧
      Nonempty ι ∧
      ∀ s : ℝ, ε ≤ |s| → HasSum (fun i => (c i : ℂ) *
        (cexp (s * (ρ i - 1 / 2)) + cexp (s * (starRingEnd ℂ (ρ i) - 1 / 2)) +
          cexp (s * (1 / 2 - starRingEnd ℂ (ρ i))) + cexp (s * (1 / 2 - ρ i)))) 0 := by
  obtain ⟨ι, hι, ρ, c, hρ, hc, hs, hne, hvan⟩ := exists_positive_lag_configuration_bandLimited hε hΘ
  refine ⟨ι, hι, ρ, c, hρ, hc, hs, hne, fun s hs' => ?_⟩
  have hs'' : ε ≤ |-s| := by rwa [abs_neg]
  have h1 := hvan s hs'
  have h2 : HasSum (fun i => (c i : ℂ) * cexp (s * (starRingEnd ℂ (ρ i) - 1 / 2))) 0 := by
    have := (hvan s hs').map (starRingEnd ℂ) (continuous_star)
    simp only [Function.comp_def, map_mul, Complex.conj_ofReal, map_zero] at this
    convert this using 2 with i
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  have h3 : HasSum (fun i => (c i : ℂ) * cexp (s * (1 / 2 - starRingEnd ℂ (ρ i)))) 0 := by
    have := (hvan (-s) hs'').map (starRingEnd ℂ) (continuous_star)
    simp only [Function.comp_def, map_mul, Complex.conj_ofReal, map_zero] at this
    convert this using 2 with i
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
    push_cast; ring_nf
  have h4 : HasSum (fun i => (c i : ℂ) * cexp (s * (1 / 2 - ρ i))) 0 := by
    convert hvan (-s) hs'' using 2 with i
    congr 1; push_cast; ring_nf
  have := ((h1.add h2).add h3).add h4
  simp only [add_zero] at this
  convert this using 2 with i
  ring

/-- **Locally finite lag sums cannot vanish on a half-line.** -/
theorem eq_zero_of_lag_vanishing_halfLine {ι : Type*} [Countable ι] {ρ : ι → ℂ} {a : ι → ℂ}
    (hinj : Function.Injective ρ) (hfin : ∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) {B : ℝ}
    (hB : ∀ i, (ρ i).re ≤ B) (ha : Summable fun i => ‖a i‖) {s₀ : ℝ}
    (hvan : ∀ s : ℝ, s₀ ≤ s → HasSum (fun i => a i * cexp (s * (ρ i - 1 / 2))) 0) (j : ι) :
    a j = 0 := by
  refine eq_zero_of_hasSum_cexp_eq_zero (w := fun i => ρ i - 1 / 2)
    (fun i k h => hinj (sub_left_injective h)) (fun R => ?_) (B := B) (fun i => ?_) ha hvan j
  · refine (hfin R).subset fun i hi => ?_
    simp only [mem_setOf_eq] at hi ⊢
    have h1 : |(ρ i - 1 / 2).im| ≤ ‖ρ i - 1 / 2‖ := Complex.abs_im_le_norm _
    have h2 : (ρ i - 1 / 2).im = (ρ i).im := by simp
    rw [h2] at h1
    exact h1.trans hi
  · simp only [Complex.sub_re, one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat]
    linarith [hB i]

/-- Products `mℓ` with `m ≥ 1` and `ℓ ∈ (c, d)` cover every `s > cd/(d − c)`. -/
theorem exists_nat_mul_mem_Ioo {c d s : ℝ} (hc : 0 < c) (hcd : c < d) (hs : c * d / (d - c) < s) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ ℓ ∈ Ioo c d, s = m * ℓ := by
  have hdc : 0 < d - c := by linarith
  have hd : 0 < d := by linarith
  have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs
  set m : ℕ := ⌊s / d⌋₊ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlow : s / d < m := by
    rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have hup : (m : ℝ) < s / c := by
    have h1 : (m : ℝ) ≤ s / d + 1 := by
      rw [hm]; push_cast; linarith [Nat.floor_le (div_nonneg hspos.le hd.le)]
    have h2 : s / d + 1 < s / c := by
      rw [div_add_one hd.ne', div_lt_div_iff₀ hd hc]
      have : c * d < s * (d - c) := by rwa [div_lt_iff₀ hdc] at hs
      nlinarith
    linarith
  refine ⟨m, hm1, s / m, ⟨?_, ?_⟩, by field_simp⟩
  · rw [lt_div_iff₀ hmpos]; rw [lt_div_iff₀ hc] at hup; linarith
  · rw [div_lt_iff₀ hmpos]; rw [div_lt_iff₀ hd] at hlow; linarith

/-- **Locally finite lag sums are determined by an interval of spacings.** If every progression
`mℓ`, `m ≥ 1`, with spacing `ℓ ∈ (c, d)` samples zero, all weights vanish. -/
theorem eq_zero_of_lag_vanishing_interval_spacings {ι : Type*} [Countable ι] {ρ : ι → ℂ}
    {a : ι → ℂ} (hinj : Function.Injective ρ) (hfin : ∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite)
    {B : ℝ} (hB : ∀ i, (ρ i).re ≤ B) (ha : Summable fun i => ‖a i‖) {c d : ℝ} (hc : 0 < c)
    (hcd : c < d)
    (hvan : ∀ ℓ ∈ Ioo c d, ∀ m : ℕ, 1 ≤ m →
      HasSum (fun i => a i * cexp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0) (j : ι) : a j = 0 := by
  refine eq_zero_of_lag_vanishing_halfLine hinj hfin hB ha (s₀ := c * d / (d - c) + 1)
    (fun s hs => ?_) j
  obtain ⟨m, hm, ℓ, hℓ, rfl⟩ := exists_nat_mul_mem_Ioo hc hcd (lt_of_lt_of_le (lt_add_one _) hs)
  exact hvan ℓ hℓ m hm

end RHTower

namespace RHTower

/-! ## Dense sampling sets -/

/-- The lag sum of a summable configuration with real parts in `[−B, B]` is continuous in `s`. -/
theorem continuous_lagSum {ι : Type*} {ρ : ι → ℂ} {a : ι → ℂ} {B : ℝ}
    (hB : ∀ i, |(ρ i - 1 / 2).re| ≤ B) (ha : Summable fun i => ‖a i‖) :
    Continuous fun s : ℝ => ∑' i, a i * Complex.exp (s * (ρ i - 1 / 2)) := by
  refine continuous_iff_continuousAt.mpr fun s₀ => ?_
  have hloc : ContinuousOn (fun s : ℝ => ∑' i, a i * Complex.exp (s * (ρ i - 1 / 2)))
      (Set.Icc (s₀ - 1) (s₀ + 1)) := by
    refine continuousOn_tsum (fun i => (continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal).mul continuous_const))).continuousOn)
      (ha.mul_right (Real.exp ((|s₀| + 1) * B))) fun i s hs => ?_
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : ((s : ℂ) * (ρ i - 1 / 2)).re = s * (ρ i - 1 / 2).re := by simp
    rw [hre]
    have hs' : |s| ≤ |s₀| + 1 := by
      have := abs_sub_abs_le_abs_sub s s₀
      have h2 : |s - s₀| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      linarith
    calc s * (ρ i - 1 / 2).re ≤ |s * (ρ i - 1 / 2).re| := le_abs_self _
      _ = |s| * |(ρ i - 1 / 2).re| := abs_mul _ _
      _ ≤ (|s₀| + 1) * B := mul_le_mul hs' (hB i) (abs_nonneg _) (by positivity)
  exact (hloc s₀ ⟨by linarith, by linarith⟩).continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- **Locally finite lag sums vanishing on a dense subset of a half-line are zero.** If the lag sum
vanishes on a set `D` whose closure contains `[s₀, ∞)`, all weights vanish. -/
theorem eq_zero_of_lag_vanishing_dense {ι : Type*} [Countable ι] {ρ : ι → ℂ} {a : ι → ℂ}
    (hinj : Function.Injective ρ) (hfin : ∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) {B : ℝ}
    (hB : ∀ i, |(ρ i - 1 / 2).re| ≤ B) (ha : Summable fun i => ‖a i‖) {D : Set ℝ} {s₀ : ℝ}
    (hD : Set.Ici s₀ ⊆ closure D)
    (hvan : ∀ s ∈ D, HasSum (fun i => a i * Complex.exp (s * (ρ i - 1 / 2))) 0) (j : ι) :
    a j = 0 := by
  have hcont := continuous_lagSum hB ha
  have hzero : ∀ s ∈ D, (fun s : ℝ => ∑' i, a i * Complex.exp (s * (ρ i - 1 / 2))) s = 0 :=
    fun s hs => (hvan s hs).tsum_eq
  have hclosed : closure D ⊆ {s | ∑' i, a i * Complex.exp (s * (ρ i - 1 / 2)) = 0} :=
    closure_minimal hzero (isClosed_eq hcont continuous_const)
  have hsum : ∀ s : ℝ, Summable fun i => a i * Complex.exp (s * (ρ i - 1 / 2)) := by
    intro s
    refine Summable.of_norm_bounded (ha.mul_right (Real.exp (|s| * B))) fun i => ?_
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : ((s : ℂ) * (ρ i - 1 / 2)).re = s * (ρ i - 1 / 2).re := by simp
    rw [hre]
    calc s * (ρ i - 1 / 2).re ≤ |s * (ρ i - 1 / 2).re| := le_abs_self _
      _ = |s| * |(ρ i - 1 / 2).re| := abs_mul _ _
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)
  refine eq_zero_of_lag_vanishing_halfLine hinj hfin (B := B + 1 / 2) (fun i => ?_) ha
    (s₀ := s₀) (fun s hs => ?_) j
  · have h := (abs_le.mp (hB i)).2
    have : (ρ i - 1 / 2).re = (ρ i).re - 1 / 2 := by simp
    linarith
  · have h0 : ∑' i, a i * Complex.exp (s * (ρ i - 1 / 2)) = 0 := hclosed (hD hs)
    rw [← h0]
    exact (hsum s).hasSum

end RHTower
