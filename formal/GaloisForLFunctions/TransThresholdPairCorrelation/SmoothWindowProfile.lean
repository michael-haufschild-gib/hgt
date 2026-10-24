import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowWeightedTrace

/-!
# Window Profiles at Height `T`

A window profile with collar `ε₁` is a smooth `u : ℝ → [0, 1]` vanishing off `[ε₁, 1 − ε₁]` and
equal to `1` on `[2ε₁, 1 − 2ε₁]` (`WindowProfile`); one exists for every `0 < ε₁ ≤ 1/8`
(`exists_windowProfile`, from a smooth bump). At height `T` it gives the grid weight
`u_T(τ) = u((τ − T)/T)`, the height weight `W_T = u_T²` and the smooth window `Ω_T = u_T⁴`:

* `W_T` is a height weight with Lipschitz constant `2ℓ₀/T` (`heightWeight_profileW`);
* `Ω_T` is `C^k`, `4ℓ₀/T`-Lipschitz, supported in `[T + ε₁T, 2T − ε₁T]`, and
  `|Ω_T^{(k)}| ≤ M_k T^{−k}` (`abs_iteratedDeriv_profileΩ_le`);
* `W_T = 1` on `[T + 2ε₁T, 2T − 2ε₁T]`, so all but `4ε₁T/h + 2` grid points carry full weight
  (`card_collar_le`).
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ContDiff

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- A smooth window profile with collar `ε₁`. -/
structure WindowProfile (ε₁ : ℝ) (u : ℝ → ℝ) : Prop where
  pos : 0 < ε₁
  le : ε₁ ≤ 1 / 8
  smooth : ∀ k : ℕ, ContDiff ℝ k u
  nonneg : ∀ x, 0 ≤ u x
  le_one : ∀ x, u x ≤ 1
  zero_of : ∀ x, x ∉ Icc ε₁ (1 - ε₁) → u x = 0
  one_of : ∀ x ∈ Icc (2 * ε₁) (1 - 2 * ε₁), u x = 1

/-- **Profiles exist** for every collar `0 < ε₁ ≤ 1/8`: a smooth bump centred at `1/2`. -/
theorem exists_windowProfile {ε₁ : ℝ} (h0 : 0 < ε₁) (h1 : ε₁ ≤ 1 / 8) :
    ∃ u : ℝ → ℝ, WindowProfile ε₁ u := by
  let f : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2 - 2 * ε₁, 1 / 2 - ε₁, by linarith, by linarith⟩
  have hrIn : f.rIn = 1 / 2 - 2 * ε₁ := rfl
  have hrOut : f.rOut = 1 / 2 - ε₁ := rfl
  refine ⟨f, ⟨h0, h1, fun k => f.contDiff, fun x => f.nonneg, fun x => f.le_one, ?_, ?_⟩⟩
  · intro x hx
    refine Function.notMem_support.mp fun hs => hx ?_
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq, hrOut] at hs
    have := abs_lt.mp hs
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro x hx
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrIn]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

namespace WindowProfile

variable {ε₁ : ℝ} {u : ℝ → ℝ}

theorem hasCompactSupport (hu : WindowProfile ε₁ u) : HasCompactSupport u := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc ε₁ (1 - ε₁)) isCompact_Icc ?_
  intro x hx
  by_contra h
  exact hx (hu.zero_of x h)

theorem continuous (hu : WindowProfile ε₁ u) : Continuous u := (hu.smooth 0).continuous

/-- A profile is Lipschitz. -/
theorem exists_lipschitz (hu : WindowProfile ε₁ u) :
    ∃ ℓ₀ : ℝ, 0 ≤ ℓ₀ ∧ ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t| := by
  have hc1 : ContDiff ℝ 1 u := hu.smooth 1
  have hd : Differentiable ℝ u := hc1.differentiable one_ne_zero
  have hdc : Continuous (deriv u) := hc1.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support hu.hasCompactSupport.deriv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hL := lipschitzWith_of_nnnorm_deriv_le (C := ⟨C, hC0⟩) hd fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hC x
  refine ⟨C, hC0, fun s t => ?_⟩
  have := hL.dist_le_mul s t
  rw [Real.dist_eq, Real.dist_eq] at this
  exact this

/-- The derivatives of `u⁴` are bounded. -/
theorem exists_iteratedDeriv_pow_four_le (hu : WindowProfile ε₁ u) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |iteratedDeriv k (fun x => u x ^ 4) x| ≤ M := by
  have hv : ContDiff ℝ k (fun x => u x ^ 4) := (hu.smooth k).pow 4
  have hcs : HasCompactSupport (fun x => u x ^ 4) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc ε₁ (1 - ε₁)) isCompact_Icc ?_
    intro x hx
    by_contra h
    exact hx (by simp only; rw [hu.zero_of x h]; norm_num)
  obtain ⟨M, hM⟩ := (hv.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (hcs.iteratedFDeriv k)
  refine ⟨M, (norm_nonneg _).trans (hM 0), fun x => ?_⟩
  rw [← Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm]
  exact hM x

end WindowProfile

/-! ## The scaled weights -/

variable {ε₁ : ℝ} {u : ℝ → ℝ}

/-- The grid weight `u_T(τ) = u((τ − T)/T)`. -/
def profileU (u : ℝ → ℝ) (T τ : ℝ) : ℝ := u ((τ - T) / T)

/-- The height weight `W_T = u_T²`. -/
def profileW (u : ℝ → ℝ) (T τ : ℝ) : ℝ := profileU u T τ ^ 2

/-- The smooth window `Ω_T = u_T⁴`. -/
def profileΩ (u : ℝ → ℝ) (T τ : ℝ) : ℝ := profileU u T τ ^ 4

theorem profileΩ_eq_sq (T τ : ℝ) : profileΩ u T τ = profileW u T τ ^ 2 := by
  unfold profileΩ profileW; ring

theorem profileU_mem (hu : WindowProfile ε₁ u) (T τ : ℝ) :
    0 ≤ profileU u T τ ∧ profileU u T τ ≤ 1 := ⟨hu.nonneg _, hu.le_one _⟩

theorem profileU_eq_zero (hu : WindowProfile ε₁ u) {T : ℝ} (hT : 0 < T) {τ : ℝ}
    (hτ : τ ∉ Icc (T + ε₁ * T) (2 * T - ε₁ * T)) : profileU u T τ = 0 := by
  refine hu.zero_of _ fun h => hτ ⟨?_, ?_⟩
  · have := h.1; rw [le_div_iff₀ hT] at this; linarith
  · have := h.2; rw [div_le_iff₀ hT] at this; linarith

theorem profileU_eq_one (hu : WindowProfile ε₁ u) {T : ℝ} (hT : 0 < T) {τ : ℝ}
    (hτ : τ ∈ Icc (T + 2 * ε₁ * T) (2 * T - 2 * ε₁ * T)) : profileU u T τ = 1 := by
  refine hu.one_of _ ⟨?_, ?_⟩
  · rw [le_div_iff₀ hT]; linarith [hτ.1]
  · rw [div_le_iff₀ hT]; linarith [hτ.2]

theorem abs_profileU_sub_le {ℓ₀ : ℝ} (hℓ : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|) {T : ℝ} (hT : 0 < T)
    (s t : ℝ) : |profileU u T s - profileU u T t| ≤ ℓ₀ / T * |s - t| := by
  unfold profileU
  refine (hℓ _ _).trans (le_of_eq ?_)
  rw [show (s - T) / T - (t - T) / T = (s - t) / T by ring, abs_div, abs_of_pos hT]; ring

/-- `|a^n − b^n| ≤ n |a − b|` on `[0, 1]`. -/
theorem abs_pow_sub_pow_le {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) :
    |a ^ n - b ^ n| ≤ n * |a - b| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + b * (a ^ n - b ^ n) := by ring
    rw [e]
    have h1 : |a ^ n * (a - b)| ≤ |a - b| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg ha n)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ha ha1)
    have h2 : |b * (a ^ n - b ^ n)| ≤ n * |a - b| := by
      rw [abs_mul, abs_of_nonneg hb]
      exact (mul_le_of_le_one_left (abs_nonneg _) hb1).trans ih
    calc |a ^ n * (a - b) + b * (a ^ n - b ^ n)| ≤ |a - b| + n * |a - b| :=
          (abs_add_le _ _).trans (add_le_add h1 h2)
      _ = ((n + 1 : ℕ) : ℝ) * |a - b| := by push_cast; ring

/-- **`W_T` is a height weight** with Lipschitz constant `2ℓ₀/T`. -/
theorem heightWeight_profileW (hu : WindowProfile ε₁ u) {ℓ₀ : ℝ}
    (hℓ : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|) {T : ℝ} (hT : 0 < T) :
    HeightWeight (2 * ℓ₀ / T) (profileW u T) where
  nonneg s := sq_nonneg _
  le_one s := pow_le_one₀ (hu.nonneg _) (hu.le_one _)
  lipschitz s t := by
    have h := abs_pow_sub_pow_le (hu.nonneg ((s - T) / T)) (hu.le_one _) (hu.nonneg ((t - T) / T))
      (hu.le_one _) 2
    have h2 := abs_profileU_sub_le hℓ hT s t
    unfold profileW
    calc |profileU u T s ^ 2 - profileU u T t ^ 2| ≤ (2:ℕ) * |profileU u T s - profileU u T t| := h
      _ ≤ 2 * (ℓ₀ / T * |s - t|) := by push_cast; linarith
      _ = 2 * ℓ₀ / T * |s - t| := by ring

theorem abs_profileΩ_sub_le (hu : WindowProfile ε₁ u) {ℓ₀ : ℝ}
    (hℓ : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|) {T : ℝ} (hT : 0 < T) (s t : ℝ) :
    |profileΩ u T s - profileΩ u T t| ≤ 4 * ℓ₀ / T * |s - t| := by
  have h := abs_pow_sub_pow_le (hu.nonneg ((s - T) / T)) (hu.le_one _) (hu.nonneg ((t - T) / T))
    (hu.le_one _) 4
  have h2 := abs_profileU_sub_le hℓ hT s t
  unfold profileΩ
  calc |profileU u T s ^ 4 - profileU u T t ^ 4| ≤ (4:ℕ) * |profileU u T s - profileU u T t| := h
    _ ≤ 4 * (ℓ₀ / T * |s - t|) := by push_cast; linarith
    _ = 4 * ℓ₀ / T * |s - t| := by ring

theorem contDiff_profileΩ (hu : WindowProfile ε₁ u) (T : ℝ) (k : ℕ) :
    ContDiff ℝ k (profileΩ u T) := by
  unfold profileΩ profileU
  exact ((hu.smooth k).comp ((contDiff_id.sub contDiff_const).div_const T)).pow 4

/-- **Derivatives of the scaled window.** `|Ω_T^{(k)}(τ)| ≤ M_k T^{−k}`. -/
theorem abs_iteratedDeriv_profileΩ_le (hu : WindowProfile ε₁ u) {T : ℝ} (hT : 0 < T) (k : ℕ)
    {M : ℝ} (hM : ∀ x, |iteratedDeriv k (fun x => u x ^ 4) x| ≤ M) (τ : ℝ) :
    |iteratedDeriv k (profileΩ u T) τ| ≤ M * (T⁻¹) ^ k := by
  set v : ℝ → ℝ := fun x => u x ^ 4 with hv
  have hvk : ContDiff ℝ k v := (hu.smooth k).pow 4
  have hshift : ContDiff ℝ k (fun x => v (x - 1)) := hvk.comp (contDiff_id.sub contDiff_const)
  have e : profileΩ u T = fun τ => (fun x => v (x - 1)) (T⁻¹ * τ) := by
    funext τ; unfold profileΩ profileU; simp only [hv]
    congr 2; field_simp
  rw [e, iteratedDeriv_comp_const_mul hshift T⁻¹, iteratedDeriv_comp_sub_const]
  simp only
  rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hT), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM _) (by positivity)

/-- **The collar.** At most `4ε₁T/h + 2` grid points lie outside `[T + 2ε₁T, 2T − 2ε₁T]`. -/
theorem card_collar_le {p : Zeta23.PrimeSide.Setting} (hT : 0 < p.T) (hL : 0 < p.L) {ε₁ : ℝ}
    (hε : 0 ≤ ε₁) (hε1 : ε₁ ≤ 1 / 2) :
    ((Finset.range p.d \ (Finset.range p.d).filter
        (fun k : ℕ => p.tau k ∈ Icc (p.T + 2 * ε₁ * p.T) (2 * p.T - 2 * ε₁ * p.T))).card : ℝ)
      ≤ 4 * ε₁ * p.T / p.h + 2 := by
  have hh : 0 < p.h := by unfold Zeta23.PrimeSide.Setting.h; positivity
  have htau : ∀ k : ℕ, p.tau k = p.T + k * p.h := fun k => by
    unfold Zeta23.PrimeSide.Setting.tau; push_cast; ring
  have hd : (p.d : ℝ) * p.h ≤ p.T := by
    unfold Zeta23.PrimeSide.Setting.d Zeta23.PrimeSide.Setting.h
    have := Nat.floor_le (show 0 ≤ p.L * p.T / (2 * π) by positivity)
    calc (⌊p.L * p.T / (2 * π)⌋₊ : ℝ) * (2 * π / p.L)
        ≤ p.L * p.T / (2 * π) * (2 * π / p.L) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = p.T := by field_simp
  set S := (Finset.range p.d).filter
    (fun k : ℕ => p.tau k ∈ Icc (p.T + 2 * ε₁ * p.T) (2 * p.T - 2 * ε₁ * p.T))
  -- the left and right collars
  have hsub : Finset.range p.d \ S ⊆ (Finset.range p.d).filter (fun k : ℕ => (k : ℝ) * p.h < 2 * ε₁ * p.T)
      ∪ (Finset.range p.d).filter (fun k : ℕ => p.T - 2 * ε₁ * p.T < (k : ℝ) * p.h) := by
    intro k hk
    rw [Finset.mem_sdiff, Finset.mem_filter] at hk
    obtain ⟨hk1, hk2⟩ := hk
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_contra hc
    push Not at hc
    exact hk2 ⟨hk1, by rw [htau]; constructor <;> linarith [hc.1 hk1, hc.2 hk1]⟩
  have hc1 : (((Finset.range p.d).filter (fun k : ℕ => (k : ℝ) * p.h < 2 * ε₁ * p.T)).card : ℝ)
      ≤ 2 * ε₁ * p.T / p.h + 1 := by
    have hs : (Finset.range p.d).filter (fun k : ℕ => (k : ℝ) * p.h < 2 * ε₁ * p.T)
        ⊆ Finset.range (⌊2 * ε₁ * p.T / p.h⌋₊ + 1) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.le_floor (by rw [le_div_iff₀ hh]; linarith [hk.2])
    have := Finset.card_le_card hs
    rw [Finset.card_range] at this
    calc _ ≤ ((⌊2 * ε₁ * p.T / p.h⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ _ := by push_cast; linarith [Nat.floor_le (show 0 ≤ 2 * ε₁ * p.T / p.h by positivity)]
  have hc2 : (((Finset.range p.d).filter (fun k : ℕ => p.T - 2 * ε₁ * p.T < (k : ℝ) * p.h)).card : ℝ)
      ≤ 2 * ε₁ * p.T / p.h + 1 := by
    have hA : 0 ≤ (p.T - 2 * ε₁ * p.T) / p.h := div_nonneg (by nlinarith) hh.le
    have hAB : (p.T - 2 * ε₁ * p.T) / p.h ≤ p.T / p.h :=
      div_le_div_of_nonneg_right (by nlinarith) hh.le
    have hs : (Finset.range p.d).filter (fun k : ℕ => p.T - 2 * ε₁ * p.T < (k : ℝ) * p.h)
        ⊆ (Finset.range p.d).filter (fun k : ℕ => (p.T - 2 * ε₁ * p.T) / p.h < k ∧ (k : ℝ) < p.T / p.h) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
      refine ⟨hk.1, by rw [div_lt_iff₀ hh]; exact hk.2, ?_⟩
      have hk1 : ((k : ℕ) : ℝ) + 1 ≤ p.d := by exact_mod_cast hk.1
      rw [lt_div_iff₀ hh]; nlinarith
    have hc := card_filter_Ioo_le (Finset.range p.d) hA hAB
    have e : p.T / p.h - (p.T - 2 * ε₁ * p.T) / p.h = 2 * ε₁ * p.T / p.h := by ring
    calc _ ≤ (((Finset.range p.d).filter
          (fun k : ℕ => (p.T - 2 * ε₁ * p.T) / p.h < k ∧ (k : ℝ) < p.T / p.h)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hs
      _ ≤ _ := by linarith
  calc ((Finset.range p.d \ S).card : ℝ)
      ≤ (((Finset.range p.d).filter (fun k : ℕ => (k : ℝ) * p.h < 2 * ε₁ * p.T)
          ∪ (Finset.range p.d).filter (fun k : ℕ => p.T - 2 * ε₁ * p.T < (k : ℝ) * p.h)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((Finset.range p.d).filter (fun k : ℕ => (k : ℝ) * p.h < 2 * ε₁ * p.T)).card : ℝ)
        + (((Finset.range p.d).filter (fun k : ℕ => p.T - 2 * ε₁ * p.T < (k : ℝ) * p.h)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ 4 * ε₁ * p.T / p.h + 2 := by
        have e : 4 * ε₁ * p.T / p.h = 2 * ε₁ * p.T / p.h + 2 * ε₁ * p.T / p.h := by ring
        linarith

end GaloisForLFunctions.TransThresholdPairCorrelation
