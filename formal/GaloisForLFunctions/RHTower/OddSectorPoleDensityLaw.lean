import GaloisForLFunctions.RHTower.OddSectorPoleWeightAtMostOne

/-!
# The pole-density law for odd Weil positivity

Odd Weil positivity at pole weight `β ≥ 0` forces the Abel density of the weights at the pole to be
at least `β`: with `F(σ) = Σ_{n ≥ 2} lam(n) n^{−1−σ}`, every `ε > 0` has a `σ₀ > 0` with
`β − ε ≤ σ F(σ)` for `0 < σ < σ₀` (`abel_density_ge_of_weilPositiveOddAt`).  The input is the
far-bump Laplace bound `βJ² − O(σ) ≤ K(σ)·σF(σ)` of the pole-weight cap together with the two-sided
estimate `e^{−σ/6} J² ≤ K(σ) ≤ e^{σ/6} J²` for the far kernel's Laplace transform.

**Consequences.**
* Weights whose Abel density vanishes (`σF(σ) → 0`) are not odd Weil-positive at any positive pole
  weight (`not_weilPositiveOddAt_of_pos_of_tendsto_abel_zero`); in particular weights with
  `Σ |lam(n)|/n < ∞` (`not_weilPositiveOddAt_of_pos_of_summable_div`), and the tempered prime
  weights `c log p/√p` (`not_weilPositiveOddAt_temperedWeight`).
* So tempered sources are confined to pole weight `≤ 0`: a source at a positive pole weight must
  carry density, and at pole weight `1` the density is exactly one (with the corpus ceiling).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RHTower.OddSector
open ResonatorProfile EvenSector WeilOneSided WeilMeanSquare WeilSpectral WeilPoleWeight

/-- The far Laplace transform is bounded below near `σ = 0`: `e^{−σ/6} K(0) ≤ K(σ)`. -/
theorem farLaplace_ge {σ : ℝ} (hσ : 0 ≤ σ) :
    Real.exp (-(σ / 6)) * farLaplace 0 ≤ farLaplace σ := by
  unfold farLaplace
  rw [← integral_const_mul]
  refine integral_mono ((integrable_farKernel_mul_exp _).const_mul _)
    (integrable_farKernel_mul_exp _) fun u => ?_
  show Real.exp (-(σ / 6)) * (farKernel u * Real.exp ((1 / 2 + 0) * u)) ≤
    farKernel u * Real.exp ((1 / 2 + σ) * u)
  have hk := farKernel_nonneg u
  rcases le_or_gt (2 * (nodeBump 2).rOut) |u| with hu | hu
  · rw [farKernel_eq_zero hu]; simp
  · have hr := nodeBump_rOut_le 2
    have hu6 : -(1 / 6) ≤ u := by have := neg_abs_le u; linarith
    have he : Real.exp (-(σ / 6)) * Real.exp ((1 / 2 + 0) * u) ≤ Real.exp ((1 / 2 + σ) * u) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    calc Real.exp (-(σ / 6)) * (farKernel u * Real.exp ((1 / 2 + 0) * u))
        = farKernel u * (Real.exp (-(σ / 6)) * Real.exp ((1 / 2 + 0) * u)) := by ring
      _ ≤ farKernel u * Real.exp ((1 / 2 + σ) * u) := mul_le_mul_of_nonneg_left he hk

/-- **The Abel density is at least the pole weight.** -/
theorem abel_density_ge_of_weilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam)
    (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ < σ₀ → β - ε ≤ σ * oddDirichlet lam σ := by
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := fun σ hσ =>
    summable_abs_div_rpow_of_weilPositiveOddAt h hβ hσ
  have hJ : 0 < farJ ^ 2 := pow_pos farJ_pos 2
  set J2 : ℝ := farJ ^ 2 with hJ2
  set A : ℝ := |farArchConst| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  set Q : ℝ := 2 * (2 * β * J2 + A) + J2 * (β + ε) + 1 with hQ
  have hQ0 : 0 < Q := by positivity
  refine ⟨min 1 (ε * J2 / Q), lt_min one_pos (by positivity), fun σ hσ hσlt => ?_⟩
  have hσ1 : σ ≤ 1 := (lt_min_iff.mp hσlt).1.le
  have hσQ : σ * Q ≤ ε * J2 := by
    have := (lt_min_iff.mp hσlt).2.le
    rwa [le_div_iff₀ hQ0] at this
  have hL : β * J2 - 2 * σ * (2 * β * J2 + farArchConst) / (1 + 2 * σ) ≤
      farLaplace σ * (σ * oddDirichlet lam σ) := by
    have h2 := mul_le_mul_of_nonneg_left (farLaplace_lower h hβ hsl hσ)
      (by positivity : (0 : ℝ) ≤ 2 * σ)
    have e1 : 2 * σ * (β * farJ ^ 2 / (2 * σ) -
        (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ)) =
        β * J2 - 2 * σ * (2 * β * J2 + farArchConst) / (1 + 2 * σ) := by
      rw [hJ2]; field_simp
    have e2 : 2 * σ * (farLaplace σ / 2 * oddDirichlet lam σ) =
        farLaplace σ * (σ * oddDirichlet lam σ) := by ring
    rw [e1, e2] at h2
    exact h2
  have herr : 2 * σ * (2 * β * J2 + farArchConst) / (1 + 2 * σ) ≤ 2 * σ * (2 * β * J2 + A) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * β * J2 + farArchConst ≤ 2 * β * J2 + A := by
      linarith [le_abs_self farArchConst]
    have h2 : 0 ≤ 2 * β * J2 + A := by positivity
    have h3 : 2 * σ * (2 * β * J2 + farArchConst) ≤ 2 * σ * (2 * β * J2 + A) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 2 * σ * (2 * β * J2 + A) ≤ 2 * σ * (2 * β * J2 + A) * (1 + 2 * σ) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  by_contra hcon
  have hcon' : σ * oddDirichlet lam σ < β - ε := not_le.mp hcon
  set X := σ * oddDirichlet lam σ with hX
  have hFl := farLaplace_le hσ.le
  have hFg := farLaplace_ge hσ.le
  rw [farLaplace_zero] at hFl hFg
  have hF0 : 0 < farLaplace σ := lt_of_lt_of_le (by positivity) hFg
  have hexp_ge : 1 - σ / 6 ≤ Real.exp (-(σ / 6)) := by
    have := Real.add_one_le_exp (-(σ / 6)); linarith
  have hexp_le : Real.exp (σ / 6) ≤ 1 + σ / 3 := by
    have hprod : Real.exp (σ / 6) * Real.exp (-(σ / 6)) = 1 := by
      rw [← Real.exp_add]; simp
    have hx : 1 ≤ (1 + σ / 3) * Real.exp (-(σ / 6)) := by
      have h1 : (1 + σ / 3) * (1 - σ / 6) ≤ (1 + σ / 3) * Real.exp (-(σ / 6)) :=
        mul_le_mul_of_nonneg_left hexp_ge (by positivity)
      nlinarith
    have : Real.exp (σ / 6) * Real.exp (-(σ / 6)) ≤ (1 + σ / 3) * Real.exp (-(σ / 6)) := by
      rw [hprod]; exact hx
    exact le_of_mul_le_mul_right this (Real.exp_pos _)
  have h1 : farLaplace σ * X ≤ farLaplace σ * (β - ε) :=
    mul_le_mul_of_nonneg_left hcon'.le hF0.le
  rcases le_or_gt 0 (β - ε) with hbe | hbe
  · have h2 : farLaplace σ * (β - ε) ≤ Real.exp (σ / 6) * J2 * (β - ε) :=
      mul_le_mul_of_nonneg_right hFl hbe
    have h3 : Real.exp (σ / 6) * J2 * (β - ε) ≤ (1 + σ / 3) * J2 * (β - ε) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp_le hJ.le) hbe
    nlinarith [hσQ, mul_nonneg hσ.le hε.le, mul_nonneg hσ.le hJ.le, mul_nonneg hσ.le hbe,
      mul_nonneg (mul_nonneg hσ.le hJ.le) hε.le, mul_nonneg (mul_nonneg hσ.le hJ.le) hβ]
  · have h2 : farLaplace σ * (β - ε) ≤ Real.exp (-(σ / 6)) * J2 * (β - ε) :=
      mul_le_mul_of_nonpos_right hFg hbe.le
    have h3 : Real.exp (-(σ / 6)) * J2 * (β - ε) ≤ (1 - σ / 6) * J2 * (β - ε) :=
      mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_right hexp_ge hJ.le) hbe.le
    nlinarith [hσQ, mul_nonneg hσ.le hε.le, mul_nonneg hσ.le hJ.le, mul_nonneg hσ.le hβ,
      mul_nonneg (mul_nonneg hσ.le hJ.le) hε.le, mul_nonneg (mul_nonneg hσ.le hJ.le) hβ]

/-- **Vanishing Abel density forbids every positive pole weight.** -/
theorem not_weilPositiveOddAt_of_pos_of_tendsto_abel_zero {β : ℝ} (hβ : 0 < β) {lam : ℕ → ℝ}
    (hz : Tendsto (fun σ : ℝ => σ * oddDirichlet lam σ) (𝓝[>] 0) (𝓝 0)) :
    ¬ WeilPositiveOddAt β lam := by
  intro h
  obtain ⟨σ₀, hσ₀, hge⟩ := abel_density_ge_of_weilPositiveOddAt h hβ.le (ε := β / 2) (by positivity)
  have hev1 : ∀ᶠ σ in 𝓝[>] (0 : ℝ), σ * oddDirichlet lam σ < β / 4 :=
    hz.eventually (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ σ in 𝓝[>] (0 : ℝ), σ < σ₀ :=
    (eventually_lt_nhds hσ₀).filter_mono nhdsWithin_le_nhds
  have hev3 : ∀ᶠ σ in 𝓝[>] (0 : ℝ), σ ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  obtain ⟨σ, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  have := hge σ h3 h2
  linarith

/-- `|σ F(σ)| ≤ σ Σ |lam(n)|/n` for `σ ≥ 0` when the latter sum converges. -/
theorem abs_mul_oddDirichlet_le {lam : ℕ → ℝ}
    (hs : Summable fun n : ℕ => |lam n| / (n : ℝ)) {σ : ℝ} (hσ : 0 ≤ σ) :
    |σ * oddDirichlet lam σ| ≤ σ * ∑' n : ℕ, |lam n| / (n : ℝ) := by
  have hpt : ∀ n : ℕ, |(if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + σ)| ≤ |lam n| / (n : ℝ) := by
    intro n
    by_cases hn : 2 ≤ n
    · rw [if_pos hn, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le two_pos hn)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans one_le_two hn)
      have hpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + σ) := by
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ (1 + σ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      exact div_le_div_of_nonneg_left (abs_nonneg _) hn0 hpow
    · rw [if_neg hn, zero_div, abs_zero]
      positivity
  have hsum : Summable fun n : ℕ => (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + σ) :=
    Summable.of_norm_bounded hs fun n => by rw [Real.norm_eq_abs]; exact hpt n
  rw [abs_mul, abs_of_nonneg hσ]
  refine mul_le_mul_of_nonneg_left ?_ hσ
  unfold oddDirichlet
  calc |∑' n : ℕ, (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + σ)|
      ≤ ∑' n : ℕ, |(if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + σ)| := by
        have := norm_tsum_le_tsum_norm hsum.norm
        simp only [Real.norm_eq_abs] at this
        exact this
    _ ≤ ∑' n : ℕ, |lam n| / (n : ℝ) := hsum.abs.tsum_le_tsum hpt hs

/-- **Absolute convergence at `s = 1` forbids every positive pole weight.** -/
theorem not_weilPositiveOddAt_of_pos_of_summable_div {β : ℝ} (hβ : 0 < β) {lam : ℕ → ℝ}
    (hs : Summable fun n : ℕ => |lam n| / (n : ℝ)) : ¬ WeilPositiveOddAt β lam := by
  refine not_weilPositiveOddAt_of_pos_of_tendsto_abel_zero hβ ?_
  set S : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) with hS
  have hlim : Tendsto (fun σ : ℝ => σ * S) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ => σ * S := continuous_id.mul continuous_const
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun σ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [Real.norm_eq_abs]
  exact abs_mul_oddDirichlet_le hs (le_of_lt hσ)

/-- The tempered prime weights `c log p / √p`. -/
def temperedWeight (c : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then c * Real.log n / Real.sqrt n else 0

theorem summable_temperedWeight_div (c : ℝ) :
    Summable fun n : ℕ => |temperedWeight c n| / (n : ℝ) := by
  have hsum : Summable fun n : ℕ => 4 * |c| * ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  unfold temperedWeight
  by_cases hp : n.Prime
  · rw [if_pos hp]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_le
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) :=
      Real.log_le_rpow_div hn0.le (by norm_num)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [abs_div, abs_mul, abs_of_nonneg hlog0, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_eq_rpow, div_div]
    rw [div_le_iff₀ (by positivity)]
    have e : 4 * |c| * ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ * ((n : ℝ) ^ (1 / 2 : ℝ) * n) =
        4 * |c| * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 : (n : ℝ) ^ (1 / 2 : ℝ) * n = (n : ℝ) ^ (3 / 2 : ℝ) := by
        rw [show (n : ℝ) ^ (1 / 2 : ℝ) * n = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) by
          rw [Real.rpow_one], ← Real.rpow_add hn0]
        norm_num
      have h2 : ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ * (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
        norm_num
      rw [h1, mul_assoc, h2]
    rw [e]
    have : |c| * Real.log n ≤ |c| * ((n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg c)
    linarith
  · rw [if_neg hp, abs_zero, zero_div]
    positivity

/-- **Tempered prime weights are never odd Weil-positive at a positive pole weight.** -/
theorem not_weilPositiveOddAt_temperedWeight {β : ℝ} (hβ : 0 < β) (c : ℝ) :
    ¬ WeilPositiveOddAt β (temperedWeight c) :=
  not_weilPositiveOddAt_of_pos_of_summable_div hβ (summable_temperedWeight_div c)

end RHTower.OddSector
