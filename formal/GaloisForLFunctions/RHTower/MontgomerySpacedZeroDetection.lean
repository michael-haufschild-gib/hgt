import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationLeadingOrder
import GaloisForLFunctions.RHTower.MontgomerySpacedDetectionCore

/-!
# Spaced off-line zeros are detected by the Montgomery pair form

Write `a_ρ = x^{Re ρ − 1/2}` for the amplitude of a zero of `ξ` at the scale `x`, and
`F(x,T) = Σ_{ρ,ρ'} x^{ρ+ρ̄'−1} w(ρ+ρ̄'−1)` for Montgomery's pair form over the zeros with
`0 < γ ≤ T`, counted with multiplicity. The form is a mean square, hence real and nonnegative
for every configuration, and its entries satisfy `Re F_ρρ ≥ a_ρ²` and
`|F_ρρ'| ≤ 4 a_ρ a_ρ' / (3 + (γ − γ')²)`.

**Theorem.** Fix `Θ > 0` and let `A(Θ)` be the set of zeros in the window with `a_ρ ≥ Θ`. If any two
distinct elements of `A(Θ)` have ordinates at distance `≥ 10`, then
`Σ_{a_ρ ≥ 200 Θ L_T} a_ρ² ≤ 2 Re F(x,T) + 25600 Θ² L_T² · #A(Θ)`, `L_T = C + log(T+4)`.
The internal cross terms of `A(Θ)` are controlled by the spacing, the cross terms with the rest by
the Lorentzian zero mass `Σ_ρ 1/(1+(t−γ)²) ≤ 8 L_T`, and the rest by positivity of its own block.

Combined with the unconditional leading-order asymptotic `F(T^α,T) ~ (T/2π) α log T`, every
`10`-spaced family of zeros with `Re ρ ≥ 1/2 + δ₀` (spaced above the threshold `Θ`) has at most
`≪ T^{1 − 2αδ₀} log² T` members up to height `T`: the density-hypothesis count for spaced
configurations, for every fixed `α < 1`.
-/

open Filter Topology Finset

namespace RHTower

/-! ## Amplitudes and pair entries -/

/-- The amplitude `a_ρ = x^{Re ρ − 1/2}` of a zero copy at the scale `x`. -/
noncomputable def zeroAmp (x : ℝ) (q : XiZeroCopy) : ℝ := x ^ ((q.1 : ℂ).re - 1 / 2)

theorem zeroAmp_nonneg {x : ℝ} (hx : 0 ≤ x) (q : XiZeroCopy) : 0 ≤ zeroAmp x q :=
  Real.rpow_nonneg hx _

/-- The pair entry `x^{ρ_j + ρ̄_k − 1} · w(ρ_j + ρ̄_k − 1)` of the Montgomery form. -/
noncomputable def pairEntry (x : ℝ) (j k : XiZeroCopy) : ℂ :=
  (x : ℂ) ^ ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) *
    montgomeryWeight ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1)

theorem montgomeryForm_eq_sum_pairEntry (s : Finset XiZeroCopy) (x : ℝ) :
    montgomeryForm s (fun q : XiZeroCopy => (q.1 : ℂ)) x = ∑ j ∈ s, ∑ k ∈ s, pairEntry x j k := rfl

theorem pairExponent_re (j k : XiZeroCopy) :
    ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1).re
      = ((j.1 : ℂ).re - 1 / 2) + ((k.1 : ℂ).re - 1 / 2) := by
  simp [Complex.sub_re, Complex.add_re, Complex.conj_re]; ring

theorem pairExponent_im (j k : XiZeroCopy) :
    ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1).im = (j.1 : ℂ).im - (k.1 : ℂ).im := by
  simp [Complex.sub_im, Complex.add_im, Complex.conj_im]; ring

theorem abs_pairExponent_re_lt_one (j k : XiZeroCopy) :
    |((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1).re| < 1 := by
  rw [pairExponent_re, abs_lt]
  have := xiZeroCopy_re_pos j
  have := xiZeroCopy_re_lt_one j
  have := xiZeroCopy_re_pos k
  have := xiZeroCopy_re_lt_one k
  constructor <;> linarith

theorem norm_cpow_pairExponent {x : ℝ} (hx : 0 < x) (j k : XiZeroCopy) :
    ‖(x : ℂ) ^ ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1)‖ = zeroAmp x j * zeroAmp x k := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, pairExponent_re, Real.rpow_add hx]
  rfl

/-- `|w(u)| ≤ 4/(3 + (Im u)²)` for `|Re u| < 1`. -/
theorem norm_montgomeryWeight_le {u : ℂ} (hu : |u.re| < 1) :
    ‖montgomeryWeight u‖ ≤ 4 / (3 + u.im ^ 2) := by
  unfold montgomeryWeight
  rw [Complex.norm_div]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  have hre : (4 - u ^ 2).re = 4 - u.re ^ 2 + u.im ^ 2 := by
    simp [Complex.sub_re, sq, Complex.mul_re]; ring
  have hlow : 3 + u.im ^ 2 ≤ ‖4 - u ^ 2‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [hre]
    have := (abs_lt.mp hu)
    nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hlow

theorem norm_pairEntry_le {x : ℝ} (hx : 0 < x) (j k : XiZeroCopy) :
    ‖pairEntry x j k‖
      ≤ 4 * zeroAmp x j * zeroAmp x k * (1 / (3 + ((j.1 : ℂ).im - (k.1 : ℂ).im) ^ 2)) := by
  unfold pairEntry
  rw [norm_mul, norm_cpow_pairExponent hx]
  have h := norm_montgomeryWeight_le (abs_pairExponent_re_lt_one j k)
  rw [pairExponent_im] at h
  have ha := zeroAmp_nonneg hx.le j
  have hb := zeroAmp_nonneg hx.le k
  calc zeroAmp x j * zeroAmp x k * ‖montgomeryWeight ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1)‖
      ≤ zeroAmp x j * zeroAmp x k * (4 / (3 + ((j.1 : ℂ).im - (k.1 : ℂ).im) ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4 * zeroAmp x j * zeroAmp x k * (1 / (3 + ((j.1 : ℂ).im - (k.1 : ℂ).im) ^ 2)) := by ring

/-- The diagonal entry is real and at least `a_ρ²`. -/
theorem zeroAmp_sq_le_pairEntry_self_re {x : ℝ} (hx : 0 < x) (j : XiZeroCopy) :
    zeroAmp x j ^ 2 ≤ (pairEntry x j j).re := by
  set r : ℝ := 2 * (j.1 : ℂ).re - 1 with hr
  have hu : (j.1 : ℂ) + (starRingEnd ℂ) (j.1 : ℂ) - 1 = (r : ℂ) := by
    apply Complex.ext
    · simp [hr, Complex.sub_re, Complex.add_re, Complex.conj_re]; ring
    · simp [Complex.sub_im, Complex.add_im, Complex.conj_im]
  have hr1 : |r| < 1 := by
    rw [hr, abs_lt]
    have := xiZeroCopy_re_pos j
    have := xiZeroCopy_re_lt_one j
    constructor <;> linarith
  have hw : montgomeryWeight (r : ℂ) = ((4 / (4 - r ^ 2) : ℝ) : ℂ) := by
    simp [montgomeryWeight]
  rw [pairEntry, hu, ← Complex.ofReal_cpow hx.le, hw, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsq : zeroAmp x j ^ 2 = x ^ r := by
    rw [zeroAmp, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, hr]
    congr 1
    push_cast; ring
  rw [hsq]
  have hr2 : r ^ 2 < 1 := by nlinarith [abs_lt.mp hr1, sq_abs r]
  have h4 : 1 ≤ 4 / (4 - r ^ 2) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hx0 := Real.rpow_nonneg hx.le r
  nlinarith

/-! ## The Lorentzian mass along the window -/

/-- `L_T = C + log(T + 4)`, the logarithmic zero-mass constant of the window `[0, T]`. -/
noncomputable def windowLog (T : ℝ) : ℝ := xiLineTwoLogDerivConstant + Real.log (T + 4)

theorem one_le_windowLog {T : ℝ} (hT : 0 ≤ T) : 1 ≤ windowLog T := by
  unfold windowLog
  have := xiLineTwoLogDerivConstant_nonneg
  have h : 1 ≤ Real.log (T + 4) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  linarith

theorem windowLog_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ windowLog T :=
  le_trans zero_le_one (one_le_windowLog hT)

/-- The Lorentzian-type sum over the window at the ordinate of a window zero is at most `8 L_T`. -/
theorem sum_window_inv_three_add_sq_le {T : ℝ} {j : XiZeroCopy}
    (hj : j ∈ zeroWindow T) :
    ∑ k ∈ zeroWindow T, 1 / (3 + ((j.1 : ℂ).im - (k.1 : ℂ).im) ^ 2) ≤ 8 * windowLog T := by
  have hjT := mem_zeroWindow.mp hj
  calc ∑ k ∈ zeroWindow T, 1 / (3 + ((j.1 : ℂ).im - (k.1 : ℂ).im) ^ 2)
      ≤ ∑ k ∈ zeroWindow T, lorentzMassTerm (j.1 : ℂ).im k := by
        refine Finset.sum_le_sum fun k _ => ?_
        unfold lorentzMassTerm
        apply one_div_le_one_div_of_le (by positivity)
        linarith
    _ ≤ lorentzMass (j.1 : ℂ).im :=
        Summable.sum_le_tsum _ (fun k _ => lorentzMassTerm_nonneg _ _) (summable_lorentzMassTerm _)
    _ ≤ 8 * (xiLineTwoLogDerivConstant + Real.log (|(j.1 : ℂ).im| + 4)) := lorentzMass_le_log _
    _ ≤ 8 * windowLog T := by
        unfold windowLog
        gcongr
        rw [abs_of_pos hjT.1]
        linarith [hjT.2]

/-! ## The detection theorem -/

/-- **Spaced zeros are detected by the pair form.** If every two distinct zeros of the window with
amplitude `≥ Θ` have ordinates at distance `≥ 10`, then the amplitudes above `200 Θ L_T` satisfy
`Σ a_ρ² ≤ 2 Re F(x,T) + 25600 Θ² L_T² · #A(Θ)`. -/
theorem spaced_zero_detection {x T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T) {Θ : ℝ} (hΘ : 0 < Θ)
    (hsp : ∀ j ∈ zeroWindow T, ∀ k ∈ zeroWindow T, Θ ≤ zeroAmp x j → Θ ≤ zeroAmp x k → j ≠ k →
      10 ≤ |(j.1 : ℂ).im - (k.1 : ℂ).im|) :
    ∑ j ∈ (zeroWindow T).filter (fun j => 200 * Θ * windowLog T ≤ zeroAmp x j), zeroAmp x j ^ 2
      ≤ 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re
        + 25600 * Θ ^ 2 * windowLog T ^ 2
          * ((zeroWindow T).filter (fun j => Θ ≤ zeroAmp x j)).card := by
  classical
  have hx0 : 0 < x := by linarith
  rw [montgomeryForm_eq_sum_pairEntry]
  refine spaced_configuration_energy (zeroWindow T) (pairEntry x) (zeroAmp x)
    (fun j k => 1 / (3 + ((j.1 : ℂ).im - (k.1 : ℂ).im) ^ 2)) hΘ (one_le_windowLog hT)
    (zeroAmp_nonneg hx0.le) (fun j k => by positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j k
    rw [show (j.1 : ℂ).im - (k.1 : ℂ).im = -((k.1 : ℂ).im - (j.1 : ℂ).im) by ring, neg_sq]
  · intro j _
    exact zeroAmp_sq_le_pairEntry_self_re hx0 j
  · intro j _ k _
    exact norm_pairEntry_le hx0 j k
  · intro R _
    rw [← montgomeryForm_eq_sum_pairEntry]
    exact montgomeryForm_re_nonneg R _ hx0 fun q _ => ⟨xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q⟩
  · intro j hj
    refine sum_inv_three_add_sq_le_of_spaced _ (fun q : XiZeroCopy => (q.1 : ℂ).im) ?_ hj
    intro j' hj' k hk hne
    obtain ⟨hj'Z, hj'Θ⟩ := Finset.mem_filter.mp hj'
    obtain ⟨hkZ, hkΘ⟩ := Finset.mem_filter.mp hk
    exact hsp j' hj'Z k hkZ hj'Θ hkΘ hne
  · intro j hj
    exact sum_window_inv_three_add_sq_le hj

/-! ## Counting corollaries -/

/-- A `10`-spaced family of zeros in the window has at most `T/10 + 1` members. -/
theorem card_spaced_le {T : ℝ} (hT : 0 ≤ T) (A : Finset XiZeroCopy) (hA : A ⊆ zeroWindow T)
    (hsp : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → 10 ≤ |(j.1 : ℂ).im - (k.1 : ℂ).im|) :
    (A.card : ℝ) ≤ T / 10 + 1 := by
  have hcard : A.card ≤ (Finset.range (⌊T / 10⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun j : XiZeroCopy => ⌊(j.1 : ℂ).im / 10⌋₊)
    · intro j hj
      have hjT := mem_zeroWindow.mp (hA hj)
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [hjT.2]))
    · intro j hj k hk heq
      by_contra hne
      have h10 := hsp j hj k hk hne
      have hj0 := (mem_zeroWindow.mp (hA hj)).1
      have hk0 := (mem_zeroWindow.mp (hA hk)).1
      have h1 : (⌊(j.1 : ℂ).im / 10⌋₊ : ℝ) ≤ (j.1 : ℂ).im / 10 := Nat.floor_le (by positivity)
      have h2 : (j.1 : ℂ).im / 10 < (⌊(j.1 : ℂ).im / 10⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h3 : (⌊(k.1 : ℂ).im / 10⌋₊ : ℝ) ≤ (k.1 : ℂ).im / 10 := Nat.floor_le (by positivity)
      have h4 : (k.1 : ℂ).im / 10 < (⌊(k.1 : ℂ).im / 10⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have heq' : (⌊(j.1 : ℂ).im / 10⌋₊ : ℝ) = ⌊(k.1 : ℂ).im / 10⌋₊ := by exact_mod_cast heq
      have hlt : |(j.1 : ℂ).im - (k.1 : ℂ).im| < 10 := by
        rw [abs_lt]; constructor <;> linarith
      linarith
  rw [Finset.card_range] at hcard
  have hfl : (⌊T / 10⌋₊ : ℝ) ≤ T / 10 := Nat.floor_le (by positivity)
  calc (A.card : ℝ) ≤ ((⌊T / 10⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (⌊T / 10⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ T / 10 + 1 := by linarith

/-- The number of window zeros with `Re ρ ≥ 1/2 + δ₀`, weighted by `x^{2δ₀}`, under the spacing
hypothesis and the threshold `x^{δ₀} ≥ 200 Θ L_T`. -/
theorem card_re_ge_mul_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T) {Θ : ℝ} (hΘ : 0 < Θ)
    (hsp : ∀ j ∈ zeroWindow T, ∀ k ∈ zeroWindow T, Θ ≤ zeroAmp x j → Θ ≤ zeroAmp x k → j ≠ k →
      10 ≤ |(j.1 : ℂ).im - (k.1 : ℂ).im|)
    {δ₀ : ℝ} (hδ₀ : 200 * Θ * windowLog T ≤ x ^ δ₀) :
    (((zeroWindow T).filter (fun j => 1 / 2 + δ₀ ≤ (j.1 : ℂ).re)).card : ℝ) * (x ^ δ₀) ^ 2
      ≤ 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re
        + 25600 * Θ ^ 2 * windowLog T ^ 2
          * ((zeroWindow T).filter (fun j => Θ ≤ zeroAmp x j)).card := by
  classical
  refine le_trans ?_ (spaced_zero_detection hx hT hΘ hsp)
  have hamp : ∀ j ∈ (zeroWindow T).filter (fun j => 1 / 2 + δ₀ ≤ (j.1 : ℂ).re),
      x ^ δ₀ ≤ zeroAmp x j := by
    intro j hj
    have := (Finset.mem_filter.mp hj).2
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hx0 : 0 ≤ x ^ δ₀ := Real.rpow_nonneg (by linarith) _
  calc (((zeroWindow T).filter (fun j => 1 / 2 + δ₀ ≤ (j.1 : ℂ).re)).card : ℝ) * (x ^ δ₀) ^ 2
      ≤ ∑ j ∈ (zeroWindow T).filter (fun j => 1 / 2 + δ₀ ≤ (j.1 : ℂ).re), zeroAmp x j ^ 2 := by
        rw [← nsmul_eq_mul]
        refine Finset.card_nsmul_le_sum _ _ _ fun j hj => ?_
        have := hamp j hj
        gcongr
    _ ≤ ∑ j ∈ (zeroWindow T).filter (fun j => 200 * Θ * windowLog T ≤ zeroAmp x j),
          zeroAmp x j ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, hδ₀.trans (hamp j (Finset.mem_filter.mpr hj))⟩
        · intros; positivity

/-! ## The density-hypothesis count for spaced configurations -/

/-- **Spaced off-line zeros obey the density-hypothesis count, unconditionally.** For fixed
`0 < α < 1`, `Θ > 0`, `δ₀ > 0`, and all large `T`: if the zeros of the window with amplitude
`(T^α)^{Re ρ − 1/2} ≥ Θ` are pairwise `10`-spaced in ordinate, then the number of zeros with
`0 < γ ≤ T` and `Re ρ ≥ 1/2 + δ₀` is at most
`(α T log T + 25600 Θ² L_T² (T/10 + 1)) / T^{2αδ₀}`. -/
theorem eventually_card_spaced_offline_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {Θ δ₀ : ℝ}
    (hΘ : 0 < Θ) (hδ₀ : 0 < δ₀) :
    ∀ᶠ T : ℝ in atTop,
      (∀ j ∈ zeroWindow T, ∀ k ∈ zeroWindow T, Θ ≤ zeroAmp (T ^ α) j → Θ ≤ zeroAmp (T ^ α) k →
        j ≠ k → 10 ≤ |(j.1 : ℂ).im - (k.1 : ℂ).im|) →
      (((zeroWindow T).filter (fun j => 1 / 2 + δ₀ ≤ (j.1 : ℂ).re)).card : ℝ)
        ≤ (α * T * Real.log T + 25600 * Θ ^ 2 * windowLog T ^ 2 * (T / 10 + 1))
            / T ^ (2 * α * δ₀) := by
  classical
  have hC := xiLineTwoLogDerivConstant_nonneg
  set C := xiLineTwoLogDerivConstant with hCdef
  -- the pair form is eventually below twice its main term
  have E1 := (tendsto_montgomeryForm_div_leadingOrder hα0 hα1).eventually
    (eventually_le_nhds (show (1 : ℝ) < 2 by norm_num))
  -- the threshold is eventually met: `log T / T^{αδ₀} → 0`
  have hpos : 0 < 200 * Θ * (C + 2) := by positivity
  have E2 := (tendsto_log_pow_div_rpow 1 (show 0 < α * δ₀ by positivity)).eventually
    (eventually_le_nhds (show (0 : ℝ) < 1 / (200 * Θ * (C + 2)) by positivity))
  filter_upwards [E1, E2, eventually_log_bounds, eventually_gt_atTop (1 : ℝ)] with T e1 e2 elog hT1
  intro hsp
  obtain ⟨hlog1, -, -, hlog4⟩ := elog
  have hT0 : 0 < T := by linarith
  have hx1 : 1 ≤ T ^ α := (Real.one_lt_rpow hT1 hα0).le
  have hlogT : 0 < Real.log T := by linarith
  have hN0 : 0 < (T / (2 * Real.pi)) * (α * Real.log T) := by positivity
  -- `2 Re F ≤ α T log T`
  have hF : 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
      ≤ α * T * Real.log T := by
    rw [div_le_iff₀ hN0] at e1
    have hπ : 2 < Real.pi := by linarith [Real.pi_gt_three]
    have : 2 * (2 * ((T / (2 * Real.pi)) * (α * Real.log T))) ≤ α * T * Real.log T := by
      rw [show 2 * (2 * ((T / (2 * Real.pi)) * (α * Real.log T))) = (α * T * Real.log T) * (2 / Real.pi)
        by field_simp]
      have h2π : 2 / Real.pi ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith
      have : 0 ≤ α * T * Real.log T := by positivity
      nlinarith
    linarith
  -- the threshold `200 Θ L_T ≤ (T^α)^{δ₀}`
  have hthr : 200 * Θ * windowLog T ≤ (T ^ α) ^ δ₀ := by
    have hL : windowLog T ≤ (C + 2) * Real.log T := by
      unfold windowLog; rw [← hCdef]; nlinarith
    have hrp : 0 < T ^ (α * δ₀) := Real.rpow_pos_of_pos hT0 _
    rw [pow_one, div_le_iff₀ hrp] at e2
    have : 200 * Θ * ((C + 2) * Real.log T) ≤ T ^ (α * δ₀) := by
      have := mul_le_mul_of_nonneg_left e2 hpos.le
      calc 200 * Θ * ((C + 2) * Real.log T) = 200 * Θ * (C + 2) * Real.log T := by ring
        _ ≤ 200 * Θ * (C + 2) * (1 / (200 * Θ * (C + 2)) * T ^ (α * δ₀)) := this
        _ = T ^ (α * δ₀) := by field_simp
    rw [← Real.rpow_mul hT0.le]
    calc 200 * Θ * windowLog T ≤ 200 * Θ * ((C + 2) * Real.log T) := by gcongr
      _ ≤ T ^ (α * δ₀) := this
  have hmain := card_re_ge_mul_le hx1 hT0.le hΘ hsp hthr
  have hcardA := card_spaced_le hT0.le ((zeroWindow T).filter (fun j => Θ ≤ zeroAmp (T ^ α) j))
    (Finset.filter_subset _ _) (by
      intro j hj k hk hne
      obtain ⟨hjZ, hjΘ⟩ := Finset.mem_filter.mp hj
      obtain ⟨hkZ, hkΘ⟩ := Finset.mem_filter.mp hk
      exact hsp j hjZ k hkZ hjΘ hkΘ hne)
  have hsq : ((T ^ α) ^ δ₀) ^ 2 = T ^ (2 * α * δ₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_mul hT0.le]
    congr 1; push_cast; ring
  have hpow0 : 0 < T ^ (2 * α * δ₀) := Real.rpow_pos_of_pos hT0 _
  rw [hsq] at hmain
  rw [le_div_iff₀ hpow0]
  have hL0 := windowLog_nonneg hT0.le
  have hΘL : 0 ≤ 25600 * Θ ^ 2 * windowLog T ^ 2 := by positivity
  calc (((zeroWindow T).filter (fun j => 1 / 2 + δ₀ ≤ (j.1 : ℂ).re)).card : ℝ) * T ^ (2 * α * δ₀)
      ≤ 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        + 25600 * Θ ^ 2 * windowLog T ^ 2
          * ((zeroWindow T).filter (fun j => Θ ≤ zeroAmp (T ^ α) j)).card := hmain
    _ ≤ α * T * Real.log T + 25600 * Θ ^ 2 * windowLog T ^ 2 * (T / 10 + 1) := by
        have := mul_le_mul_of_nonneg_left hcardA hΘL
        linarith

end RHTower
