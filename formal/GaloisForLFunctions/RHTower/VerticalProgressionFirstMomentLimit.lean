import GaloisForLFunctions.RHTower.VerticalProgressionResonantMass

/-!
# The twisted mollified first moment along a vertical progression: the limit

**Theorem** (`tendsto_firstMoment_sub_bumpSum_div`). For `φ ∈ C^∞` supported in `[1, 2]`,
`α > 0`, `β, γ ∈ ℝ`, `0 < θ ≤ ½` and `N = ⌊T^θ⌋`,

`(Σ_ℓ φ(ℓ/T) e(ℓγ) (ζ M_N)(½ + i(αℓ + β)) − Σ_ℓ φ(ℓ/T) e(ℓγ)) / T → 0`.

Hence (`tendsto_firstMoment_div_int`, `tendsto_firstMoment_div_of_not_int`) the normalized first
moment tends to `∫ φ` when `γ ∈ ℤ` and to `0` when `γ ∉ ℤ`.

**Proof.** By the Dirichlet expansion, `J − L_T(γ) = E + (a(1) − 1)L_T(γ) + Σ_{n ≥ 2} a(n) n^{−s} L_T(u_n)`
with `‖E‖ ≪ T^{15/16}`. For `n ≥ 2`, `‖L_T(u_n)‖ ≤ B` off resonance (`B ≪ T^{1 − 140/32}` after
`140` summations by parts, against `Σ |a(n)| ≪ T^{33/8}`) and `≤ (T + 1)Φ₀` on resonance, where the
resonant mass tends to `0`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.VerticalAP

noncomputable section

/-- The error of the Dirichlet expansion, divided by `T`, tends to `0`. -/
theorem tendsto_expansionError_div {α θ C Φ₀ : ℝ} (hα : 0 < α) (hθ : θ ≤ 1 / 2) (hC : 0 ≤ C)
    (hΦ₀ : 0 ≤ Φ₀) :
    Tendsto (fun T : ℝ => (T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / dirLen T +
      dirLen T ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) *
        (2 * Real.sqrt (molLen θ T)))) / T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => 4 * Φ₀ * (C * (1 + 3 * α) * T ^ (-(1 / 16 : ℝ)) +
      Real.exp (1 / 4) * (T ^ (29 / 32 : ℝ) * Real.exp (-(α / 2) * T)))) atTop (𝓝 0) := by
    have ha := (tendsto_rpow_of_neg (by norm_num : -(1 / 16 : ℝ) < 0)).const_mul (C * (1 + 3 * α))
    have hb := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (29 / 32) (α / 2) (by positivity)).const_mul
      (Real.exp (1 / 4))
    simpa using (ha.add hb).const_mul (4 * Φ₀)
  have hbound : ∀ᶠ T : ℝ in atTop, (T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / dirLen T +
      dirLen T ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) *
        (2 * Real.sqrt (molLen θ T)))) / T ≤ 4 * Φ₀ * (C * (1 + 3 * α) * T ^ (-(1 / 16 : ℝ)) +
      Real.exp (1 / 4) * (T ^ (29 / 32 : ℝ) * Real.exp (-(α / 2) * T))) := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 / α)] with T hT1 hTα
    have hT0 : 0 < T := by linarith
    have hX : dirLen T = T ^ (21 / 16 : ℝ) := rfl
    have hNm : Real.sqrt (molLen θ T) ≤ T ^ (1 / 4 : ℝ) := by
      have h1 : (molLen θ T : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
        (molLen_le hT0.le).trans (Real.rpow_le_rpow_of_exponent_le hT1 hθ)
      calc Real.sqrt (molLen θ T) ≤ Real.sqrt (T ^ (1 / 2 : ℝ)) := Real.sqrt_le_sqrt h1
        _ = T ^ (1 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]; norm_num
    have hA : C * (1 + 3 * α * T) / dirLen T ≤ C * (1 + 3 * α) * T ^ (-(5 / 16 : ℝ)) := by
      rw [hX, div_le_iff₀ (by positivity)]
      have e : T ^ (-(5 / 16 : ℝ)) * T ^ (21 / 16 : ℝ) = T := by
        rw [← Real.rpow_add hT0]; norm_num
      calc C * (1 + 3 * α * T) ≤ C * ((1 + 3 * α) * T) := by
            apply mul_le_mul_of_nonneg_left _ hC; nlinarith
        _ = C * (1 + 3 * α) * (T ^ (-(5 / 16 : ℝ)) * T ^ (21 / 16 : ℝ)) := by rw [e]; ring
        _ = C * (1 + 3 * α) * T ^ (-(5 / 16 : ℝ)) * T ^ (21 / 16 : ℝ) := by ring
    have hB : dirLen T ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2) ≤
        Real.exp (1 / 4) * (T ^ (21 / 32 : ℝ) * Real.exp (-(α / 2) * T)) := by
      rw [hX, ← Real.rpow_mul hT0.le]
      have hge : α * T / 2 ≤ (α * T / 2) ^ 2 := by
        have : 1 ≤ α * T / 2 := by
          have h' := (div_le_iff₀ hα).mp hTα; linarith
        nlinarith
      have hexp : Real.exp (1 / 4 - (α * T / 2) ^ 2) ≤ Real.exp (1 / 4) * Real.exp (-(α / 2) * T) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      calc T ^ ((21 / 16 : ℝ) * (1 / 2)) * Real.exp (1 / 4 - (α * T / 2) ^ 2)
          ≤ T ^ ((21 / 16 : ℝ) * (1 / 2)) * (Real.exp (1 / 4) * Real.exp (-(α / 2) * T)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = Real.exp (1 / 4) * (T ^ (21 / 32 : ℝ) * Real.exp (-(α / 2) * T)) := by
            norm_num; ring
    have e1 : T ^ (-(5 / 16 : ℝ)) * T ^ (1 / 4 : ℝ) = T ^ (-(1 / 16 : ℝ)) := by
      rw [← Real.rpow_add hT0]; norm_num
    have e2 : T ^ (21 / 32 : ℝ) * T ^ (1 / 4 : ℝ) = T ^ (29 / 32 : ℝ) := by
      rw [← Real.rpow_add hT0]; norm_num
    calc (T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / dirLen T +
          dirLen T ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) *
            (2 * Real.sqrt (molLen θ T)))) / T
        ≤ (2 * T) * (Φ₀ * ((C * (1 + 3 * α) * T ^ (-(5 / 16 : ℝ)) +
          Real.exp (1 / 4) * (T ^ (21 / 32 : ℝ) * Real.exp (-(α / 2) * T))) *
            (2 * T ^ (1 / 4 : ℝ)))) / T := by
          have hXnn : 0 ≤ dirLen T := Real.rpow_nonneg hT0.le _
          gcongr
          linarith
      _ = 4 * Φ₀ * (C * (1 + 3 * α) * (T ^ (-(5 / 16 : ℝ)) * T ^ (1 / 4 : ℝ)) +
          Real.exp (1 / 4) * ((T ^ (21 / 32 : ℝ) * T ^ (1 / 4 : ℝ)) * Real.exp (-(α / 2) * T))) := by
          field_simp
          ring
      _ = 4 * Φ₀ * (C * (1 + 3 * α) * T ^ (-(1 / 16 : ℝ)) +
          Real.exp (1 / 4) * (T ^ (29 / 32 : ℝ) * Real.exp (-(α / 2) * T))) := by rw [e1, e2]
  have hnonneg : ∀ᶠ T : ℝ in atTop, 0 ≤ (T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / dirLen T +
      dirLen T ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) *
        (2 * Real.sqrt (molLen θ T)))) / T := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have : 0 ≤ dirLen T := Real.rpow_nonneg hT.le _
    positivity
  exact squeeze_zero' hnonneg hbound h1

/-- The off-resonance contribution, divided by `T`, tends to `0` (`140` summations by parts). -/
theorem tendsto_offResonance_div {θ Φk K S : ℝ} (hθ : θ ≤ 1 / 2) (hΦ : 0 ≤ Φk) (hK : 0 ≤ K)
    (hS : 0 ≤ S) :
    Tendsto (fun T : ℝ => ((140 : ℕ) + 2) * Φk * T / (4 * T * T ^ (-(31 / 32 : ℝ))) ^ 140 *
      ((molLen θ T : ℝ) * (K * ((molLen θ T : ℝ) * dirLen T) ^ (2 : ℝ)) * S) / T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => ((140 : ℕ) + 2) * Φk * K * S / 4 ^ 140 * T ^ (-(1 / 4 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_of_neg (by norm_num : -(1 / 4 : ℝ) < 0)).const_mul
      (((140 : ℕ) + 2) * Φk * K * S / 4 ^ 140)
  have hbound : ∀ᶠ T : ℝ in atTop, ((140 : ℕ) + 2) * Φk * T / (4 * T * T ^ (-(31 / 32 : ℝ))) ^ 140 *
      ((molLen θ T : ℝ) * (K * ((molLen θ T : ℝ) * dirLen T) ^ (2 : ℝ)) * S) / T ≤
      ((140 : ℕ) + 2) * Φk * K * S / 4 ^ 140 * T ^ (-(1 / 4 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with T hT1
    have hT0 : 0 < T := by linarith
    have hNm : (molLen θ T : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
      (molLen_le hT0.le).trans (Real.rpow_le_rpow_of_exponent_le hT1 hθ)
    have hXd : dirLen T = T ^ (21 / 16 : ℝ) := rfl
    have hden : (4 * T * T ^ (-(31 / 32 : ℝ))) ^ 140 = 4 ^ 140 * T ^ (35 / 8 : ℝ) := by
      have : T * T ^ (-(31 / 32 : ℝ)) = T ^ (1 / 32 : ℝ) := by
        rw [← Real.rpow_one_add' hT0.le (by norm_num)]; norm_num
      rw [mul_assoc, this, mul_pow, ← Real.rpow_mul_natCast hT0.le]
      norm_num
    have hsq : ((molLen θ T : ℝ) * dirLen T) ^ (2 : ℝ) ≤ T ^ (29 / 8 : ℝ) := by
      calc ((molLen θ T : ℝ) * dirLen T) ^ (2 : ℝ) ≤ (T ^ (1 / 2 : ℝ) * T ^ (21 / 16 : ℝ)) ^ (2 : ℝ) := by
            rw [hXd]
            gcongr
          _ = T ^ (29 / 8 : ℝ) := by
            rw [← Real.rpow_add hT0, ← Real.rpow_mul hT0.le]; norm_num
    rw [hden]
    have hXnn : 0 ≤ dirLen T := Real.rpow_nonneg hT0.le _
    calc ((140 : ℕ) + 2) * Φk * T / (4 ^ 140 * T ^ (35 / 8 : ℝ)) *
          ((molLen θ T : ℝ) * (K * ((molLen θ T : ℝ) * dirLen T) ^ (2 : ℝ)) * S) / T
        ≤ ((140 : ℕ) + 2) * Φk * T / (4 ^ 140 * T ^ (35 / 8 : ℝ)) *
          (T ^ (1 / 2 : ℝ) * (K * T ^ (29 / 8 : ℝ)) * S) / T := by
          gcongr
      _ = ((140 : ℕ) + 2) * Φk * K * S / 4 ^ 140 *
          (T ^ (1 / 2 : ℝ) * T ^ (29 / 8 : ℝ) / T ^ (35 / 8 : ℝ)) := by
          field_simp
      _ = ((140 : ℕ) + 2) * Φk * K * S / 4 ^ 140 * T ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_sub hT0]; norm_num
  have hnonneg : ∀ᶠ T : ℝ in atTop, 0 ≤ ((140 : ℕ) + 2) * Φk * T /
      (4 * T * T ^ (-(31 / 32 : ℝ))) ^ 140 *
      ((molLen θ T : ℝ) * (K * ((molLen θ T : ℝ) * dirLen T) ^ (2 : ℝ)) * S) / T := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have : 0 ≤ dirLen T := Real.rpow_nonneg hT.le _
    positivity
  exact squeeze_zero' hnonneg hbound h1

/-- **The mollified first moment minus the bump sum is `o(T)`.** -/
theorem tendsto_firstMoment_sub_bumpSum_div {φ : ℝ → ℂ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {α β γ θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) :
    Tendsto (fun T => (firstMoment φ α β γ (molLen θ T) T - bumpSum φ T γ) / T) atTop (𝓝 0) := by
  classical
  obtain ⟨Φ₀, hΦ₀⟩ := exists_bound_bump hφ hsupp
  have hΦ0 : 0 ≤ Φ₀ := (norm_nonneg _).trans (hΦ₀ 0)
  obtain ⟨Φk, hΦk⟩ := exists_bound_iteratedDeriv hφ hsupp 140
  have hΦk0 : 0 ≤ Φk := (norm_nonneg _).trans (hΦk 0)
  obtain ⟨C, hC, hexp⟩ := norm_firstMoment_sub_expansion_le
  obtain ⟨K, hK, hKb⟩ := norm_mollCoeff_le_decay (A := 2) two_pos
  set S₂ : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) with hS₂def
  have hS₂ : 0 ≤ S₂ := tsum_nonneg fun n => by positivity
  have hS₂sum : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  -- the four limits
  have lE := tendsto_expansionError_div (θ := θ) (C := C) hα hθ hC hΦ0
  have lO := tendsto_offResonance_div (θ := θ) (K := K) (S := S₂) hθ hΦk0 hK hS₂
  have hT1 : Tendsto (fun T : ℝ => (T + 1) / T) atTop (𝓝 1) := by
    have : Tendsto (fun T : ℝ => 1 + T⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_inv_atTop_zero
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    field_simp
  have lQ : Tendsto (fun T : ℝ => (T + 1) * Φ₀ * resonantMass α γ θ T / T) atTop (𝓝 0) := by
    have h := ((hT1.mul_const Φ₀).mul (tendsto_resonantMass (γ := γ) hα hθ0 hθ))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    field_simp
  have lA : Tendsto (fun T : ℝ => ‖mollCoeff (molLen θ T) (dirLen T) 1 - 1‖ *
      ((T + 1) * Φ₀) / T) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T => ‖mollCoeff (molLen θ T) (dirLen T) 1 - 1‖) atTop (𝓝 0) := by
      have := (tendsto_mollCoeff_one (tendsto_molLen hθ0) tendsto_dirLen).sub_const 1
      rw [sub_self] at this
      simpa using this.norm
    have h := h0.mul (hT1.mul_const Φ₀)
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    field_simp
  have lsum := ((lE.add lA).add lO).add lQ
  simp only [add_zero] at lsum
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ lsum
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 * |β| / α),
    eventually_ge_atTop (2 / α)] with T hT1' hTβ hTα
  have hT0 : 0 < T := by linarith
  have h2β : 2 * |β| ≤ α * T := by have := (div_le_iff₀ hα).mp hTβ; linarith
  have hαT : 2 ≤ α * T := by have := (div_le_iff₀ hα).mp hTα; linarith
  set Nm : ℕ := molLen θ T with hNm
  set X : ℝ := dirLen T with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hT0 _
  have hE := hexp hsupp hΦ₀ γ Nm hα hX h2β hαT
  set c : ℕ → ℂ := fun m => mollCoeff Nm X (m + 1) * (m + 1 : ℂ) ^ (-critPt β) with hc
  set L : ℕ → ℂ := fun m => bumpSum φ T (γ - α * Real.log (m + 1) / (2 * Real.pi)) with hLdef
  have hcs : Summable c := summable_mollSeries Nm hX (s := critPt β) (by simp)
  have hcn : Summable (fun m => ‖c m‖) := summable_norm_iff.mpr hcs
  have hL : ∀ m, ‖L m‖ ≤ (T + 1) * Φ₀ := fun m => norm_bumpSum_le hsupp hΦ₀ hT0 _
  have hcL : Summable (fun m => c m * L m) :=
    (hcn.mul_right ((T + 1) * Φ₀)).of_norm_bounded fun m => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hL m) (norm_nonneg _)
  have hc0 : c 0 = mollCoeff Nm X 1 := by simp [hc]
  have hL0 : L 0 = bumpSum φ T γ := by simp [hLdef]
  -- the per-term bound
  set B : ℝ := ((140 : ℕ) + 2) * Φk * T / (4 * T * T ^ (-(31 / 32 : ℝ))) ^ 140 with hB
  have hB0 : 0 ≤ B := by positivity
  set q : ℕ → ℝ := fun m => if (∃ j : ℤ, |resFreq α γ (m + 2) - j| < T ^ (-(31 / 32 : ℝ))) then
    ‖mollCoeff (molLen θ T) (dirLen T) (m + 2)‖ * ((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) else 0
    with hq
  have hcnorm : ∀ m, ‖c (m + 1)‖ = ‖mollCoeff Nm X (m + 2)‖ * ((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro m
    simp only [hc]
    rw [norm_mul]
    congr 1
    have : ((((m + 1 : ℕ) : ℂ)) + 1) = (((m + 2 : ℕ)) : ℂ) := by push_cast; ring
    rw [this, norm_natCast_cpow_of_pos (by omega)]
    simp
  have hLarg : ∀ m, L (m + 1) = bumpSum φ T (resFreq α γ (m + 2)) := by
    intro m
    simp only [hLdef, resFreq]
    push_cast
    ring_nf
  have hterm : ∀ m, ‖c (m + 1) * L (m + 1)‖ ≤ B * ‖c (m + 1)‖ + (T + 1) * Φ₀ * q m := by
    intro m
    rw [norm_mul]
    by_cases hr : ∃ j : ℤ, |resFreq α γ (m + 2) - j| < T ^ (-(31 / 32 : ℝ))
    · have hqm : q m = ‖c (m + 1)‖ := by simp only [hq, if_pos hr]; rw [hcnorm]
      rw [hqm]
      nlinarith [hL (m + 1), norm_nonneg (c (m + 1))]
    · push Not at hr
      have hδ : 0 < T ^ (-(31 / 32 : ℝ)) := by positivity
      have hosc := norm_bumpSum_le_osc (k := 140) (hφ 140) hsupp hΦk hT1' hδ hr
      rw [← hLarg] at hosc
      have hqm : q m = 0 := by
        simp only [hq]; rw [if_neg]; push Not; exact hr
      rw [hqm, mul_zero, add_zero, mul_comm]
      exact mul_le_mul_of_nonneg_right hosc (norm_nonneg _)
  have hqs : Summable q := by
    refine (hcn.comp_injective (add_left_injective 1)).of_nonneg_of_le (fun m => ?_) fun m => ?_
    · simp only [hq]; split_ifs <;> positivity
    · simp only [hq, Function.comp]
      split_ifs
      · rw [hcnorm]
      · exact norm_nonneg _
  have htail : ‖∑' m, c (m + 1) * L (m + 1)‖ ≤ B * ∑' m, ‖c (m + 1)‖ + (T + 1) * Φ₀ *
      resonantMass α γ θ T := by
    have hn := (summable_norm_iff.mpr (hcL.comp_injective (add_left_injective 1)))
    refine (norm_tsum_le_tsum_norm hn).trans ?_
    have hcn1 : Summable (fun m : ℕ => ‖c (m + 1)‖) := hcn.comp_injective (add_left_injective 1)
    have hs1 : Summable (fun m : ℕ => B * ‖c (m + 1)‖) := hcn1.mul_left B
    have hs2 : Summable (fun m : ℕ => (T + 1) * Φ₀ * q m) := hqs.mul_left _
    have hr : ∑' m, (B * ‖c (m + 1)‖ + (T + 1) * Φ₀ * q m) =
        B * ∑' m, ‖c (m + 1)‖ + (T + 1) * Φ₀ * resonantMass α γ θ T := by
      rw [Summable.tsum_add hs1 hs2, Summable.tsum_mul_left _ hcn1, Summable.tsum_mul_left _ hqs]
      rfl
    rw [← hr]
    exact Summable.tsum_le_tsum hterm hn (hs1.add hs2)
  have hcsum : ∑' m, ‖c (m + 1)‖ ≤ (Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) * S₂ := by
    have hb : ∀ m, ‖c (m + 1)‖ ≤ (Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) *
        (((m + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
      intro m
      rw [hcnorm]
      have hm : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
      have hle1 : ((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ m + 2))
          (by norm_num)
      have hdec := hKb Nm hX (m := m + 2) (by omega)
      have heq : ((Nm : ℝ) * X / ((m + 2 : ℕ) : ℝ)) ^ (2 : ℝ) =
          ((Nm : ℝ) * X) ^ (2 : ℝ) * ((m + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
        rw [Real.div_rpow (by positivity) hm.le, Real.rpow_neg hm.le, div_eq_mul_inv]
      rw [heq] at hdec
      calc ‖mollCoeff Nm X (m + 2)‖ * ((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ ‖mollCoeff Nm X (m + 2)‖ * 1 := mul_le_mul_of_nonneg_left hle1 (norm_nonneg _)
        _ ≤ (Nm : ℝ) * (K * (((Nm : ℝ) * X) ^ (2 : ℝ) * ((m + 2 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
            rw [mul_one]; exact hdec
        _ = (Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) * (((m + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) := by ring
    have hs2 : Summable (fun m : ℕ => ((m + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
      hS₂sum.comp_injective (add_left_injective 2)
    calc ∑' m, ‖c (m + 1)‖ ≤ ∑' m, (Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) *
          (((m + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
          Summable.tsum_le_tsum hb (hcn.comp_injective (add_left_injective 1)) (hs2.mul_left _)
      _ = (Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) * ∑' m, ((m + 2 : ℕ) : ℝ) ^ (-2 : ℝ) :=
          Summable.tsum_mul_left _ hs2
      _ ≤ (Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) * S₂ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hsplit := hS₂sum.sum_add_tsum_nat_add 2
          have h0 : 0 ≤ ∑ i ∈ Finset.range 2, (i : ℝ) ^ (-2 : ℝ) :=
            Finset.sum_nonneg fun i _ => by positivity
          linarith
  -- assemble
  have hdecomp : firstMoment φ α β γ Nm T - bumpSum φ T γ =
      (firstMoment φ α β γ Nm T - ∑' m, c m * L m) + (mollCoeff Nm X 1 - 1) * bumpSum φ T γ +
        ∑' m, c (m + 1) * L (m + 1) := by
    rw [hcL.tsum_eq_zero_add, hc0, hL0]
    ring
  rw [hdecomp, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  have hA : ‖(mollCoeff Nm X 1 - 1) * bumpSum φ T γ‖ ≤ ‖mollCoeff Nm X 1 - 1‖ * ((T + 1) * Φ₀) := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_bumpSum_le hsupp hΦ₀ hT0 _) (norm_nonneg _)
  have hmain : ‖(firstMoment φ α β γ Nm T - ∑' m, c m * L m) +
      (mollCoeff Nm X 1 - 1) * bumpSum φ T γ + ∑' m, c (m + 1) * L (m + 1)‖ ≤
      (T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / X +
        X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt Nm))) +
      ‖mollCoeff Nm X 1 - 1‖ * ((T + 1) * Φ₀) +
      B * ((Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) * S₂) +
      (T + 1) * Φ₀ * resonantMass α γ θ T := by
    have hE' : ‖firstMoment φ α β γ Nm T - ∑' m, c m * L m‖ ≤
        (T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / X +
          X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt Nm))) := hE
    calc ‖(firstMoment φ α β γ Nm T - ∑' m, c m * L m) +
          (mollCoeff Nm X 1 - 1) * bumpSum φ T γ + ∑' m, c (m + 1) * L (m + 1)‖
        ≤ ‖(firstMoment φ α β γ Nm T - ∑' m, c m * L m) +
          (mollCoeff Nm X 1 - 1) * bumpSum φ T γ‖ + ‖∑' m, c (m + 1) * L (m + 1)‖ :=
          norm_add_le _ _
      _ ≤ (‖firstMoment φ α β γ Nm T - ∑' m, c m * L m‖ +
          ‖(mollCoeff Nm X 1 - 1) * bumpSum φ T γ‖) + ‖∑' m, c (m + 1) * L (m + 1)‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ((T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / X +
            X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt Nm))) +
          ‖mollCoeff Nm X 1 - 1‖ * ((T + 1) * Φ₀)) +
          (B * ∑' m, ‖c (m + 1)‖ + (T + 1) * Φ₀ * resonantMass α γ θ T) :=
          add_le_add (add_le_add hE' hA) htail
      _ ≤ ((T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / X +
            X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt Nm))) +
          ‖mollCoeff Nm X 1 - 1‖ * ((T + 1) * Φ₀)) +
          (B * ((Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) * S₂) +
            (T + 1) * Φ₀ * resonantMass α γ θ T) := by
          gcongr
      _ = _ := by ring
  calc ‖(firstMoment φ α β γ Nm T - ∑' m, c m * L m) +
        (mollCoeff Nm X 1 - 1) * bumpSum φ T γ + ∑' m, c (m + 1) * L (m + 1)‖ / T
      ≤ ((T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / X +
          X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt Nm))) +
        ‖mollCoeff Nm X 1 - 1‖ * ((T + 1) * Φ₀) +
        B * ((Nm : ℝ) * (K * ((Nm : ℝ) * X) ^ (2 : ℝ)) * S₂) +
        (T + 1) * Φ₀ * resonantMass α γ θ T) / T := by
        gcongr
    _ = _ := by
        simp only [hB]
        ring

/-- **The first moment at an integer twist:** `J(T)/T → ∫ φ`. -/
theorem tendsto_firstMoment_div_int {φ : ℝ → ℂ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) (j : ℤ) :
    Tendsto (fun T => firstMoment φ α β j (molLen θ T) T / T) atTop (𝓝 (∫ x, φ x)) := by
  obtain ⟨Φ₁, hΦ₁⟩ := exists_bound_iteratedDeriv hφ hsupp 1
  have hb := tendsto_bumpSum_div_int (hφ 1) hsupp (Φ₁ := Φ₁) (by simpa using hΦ₁) j
  have h := (tendsto_firstMoment_sub_bumpSum_div hφ hsupp (β := β) (γ := j) hα hθ0 hθ).add hb
  rw [zero_add] at h
  refine h.congr' (Eventually.of_forall fun T => ?_)
  ring

/-- **The first moment at a non-integer twist:** `J(T)/T → 0`. -/
theorem tendsto_firstMoment_div_of_not_int {φ : ℝ → ℂ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {α β γ θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) (hγ : ∀ j : ℤ, γ ≠ j) :
    Tendsto (fun T => firstMoment φ α β γ (molLen θ T) T / T) atTop (𝓝 0) := by
  obtain ⟨Φ₂, hΦ₂⟩ := exists_bound_iteratedDeriv hφ hsupp 2
  have hb := tendsto_bumpSum_div_of_not_int (hφ 2) hsupp hΦ₂ hγ
  have h := (tendsto_firstMoment_sub_bumpSum_div hφ hsupp (β := β) (γ := γ) hα hθ0 hθ).add hb
  rw [zero_add] at h
  refine h.congr' (Eventually.of_forall fun T => ?_)
  ring

end

end RHTower.VerticalAP
