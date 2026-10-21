import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumLocalConstancy
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumL4
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardRatioSeparation
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardEnergyDiscreteThirdMoment

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 11.8: the small-gcd part of the discrete third moment

For a `1`-separated `W ⊆ [T₀, T₀ + T]`, `N ≥ 1` and `D ≥ 0` (Guth–Maynard, arXiv 2405.20552,
Lemma 11.8), unconditionally:

`Σ_{n₁,n₂ ∼ N, gcd(n₁,n₂) ≤ D} |R(n₁/n₂)|³ ⪅ (DT + N²) |W|^{1/2} E(W)^{1/2}`.

Proof. In logarithmic coordinates `x = log(n₁/n₂) ∈ [−1, 1]`, Lemma 11.7 in cube form gives
`|R(e^x)|³ ≤ ‖K‖₁² (T ‖K‖_∞ ∫_{−δ}^{δ} |R(e^{x+η})|³ dη + |W|³ ∫_{|ξ|>Tδ}|K|)`, `δ = T^ε/T`.
Every point `u` lies in at most `D + 32δN²` of the windows `[x − δ, x + δ]` (the ratios with a
fixed gcd `d` are `d²/(8N²)`-separated in log scale, `GuthMaynardRatioSeparation`), so the windows
add up to `(D + 32δN²) ∫_{−2}^{2} |R(e^u)|³ du`. Cauchy–Schwarz and Lemmas 8.2, 8.3 in
logarithmic coordinates (`∫_{−2}^{2} |R|² ≤ 5π|W|`, `∫_{−2}^{2} |R|⁴ ≤ 5π E(W)`) bound the last
integral by `5π |W|^{1/2} E(W)^{1/2}`; and `T(D + 32δN²) ≤ 32 T^ε (DT + N²)`.
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Bounded overlap of windows -/

/-- **Bounded overlap.** If every point lies in at most `m` of the windows `[x_i − δ, x_i + δ]`,
all contained in `[−c, c]`, then for continuous `g ≥ 0`:
`Σ_i ∫_{−δ}^{δ} g(x_i + η) dη ≤ m ∫_{−c}^{c} g`. -/
theorem sum_intervalIntegral_le_of_overlap {ι : Type*} (P : Finset ι) (x : ι → ℝ) {δ c m : ℝ}
    (hδ : 0 ≤ δ) {g : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u) (hgc : Continuous g)
    (hx : ∀ i ∈ P, -c ≤ x i - δ ∧ x i + δ ≤ c)
    (hm : ∀ u, ((P.filter fun i => |u - x i| ≤ δ).card : ℝ) ≤ m) :
    ∑ i ∈ P, ∫ η in -δ..δ, g (x i + η) ≤ m * ∫ u in Icc (-c) c, g u := by
  classical
  have hwin : ∀ i, ∫ η in -δ..δ, g (x i + η) =
      ∫ u, (Icc (x i - δ) (x i + δ)).indicator g u := by
    intro i
    rw [intervalIntegral.integral_comp_add_left g (x i), intervalIntegral.integral_of_le
      (by linarith), ← integral_Icc_eq_integral_Ioc, integral_indicator measurableSet_Icc,
      ← sub_eq_add_neg]
  have hint : ∀ i, Integrable ((Icc (x i - δ) (x i + δ)).indicator g) := fun i =>
    (hgc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  simp_rw [hwin]
  rw [← integral_finsetSum _ fun i _ => hint i, ← integral_const_mul,
    ← integral_indicator measurableSet_Icc]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u =>
      sum_nonneg fun i _ => indicator_nonneg (fun u _ => hg u) u)
    (((continuous_const.mul hgc).integrableOn_Icc (a := -c) (b := c)).integrable_indicator
      measurableSet_Icc)
    (Filter.Eventually.of_forall fun u => ?_)
  have hmem : ∀ i, u ∈ Icc (x i - δ) (x i + δ) ↔ |u - x i| ≤ δ := fun i => by
    rw [Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hu : u ∈ Icc (-c) c
  · rw [indicator_of_mem hu]
    calc ∑ i ∈ P, (Icc (x i - δ) (x i + δ)).indicator g u
        = ∑ i ∈ P, if |u - x i| ≤ δ then g u else 0 := by
          refine sum_congr rfl fun i _ => ?_
          rw [indicator_apply]
          simp only [hmem]
      _ = ((P.filter fun i => |u - x i| ≤ δ).card : ℝ) * g u := by
          rw [← sum_filter, sum_const, nsmul_eq_mul]
      _ ≤ m * g u := mul_le_mul_of_nonneg_right (hm u) (hg u)
  · rw [indicator_of_notMem hu]
    refine le_of_eq (sum_eq_zero fun i hi => indicator_of_notMem ?_ _)
    intro hu'
    exact hu ⟨by linarith [(hx i hi).1, hu'.1], by linarith [(hx i hi).2, hu'.2]⟩

/-! ### Lemmas 8.2 and 8.3 on the logarithmic window `[−2, 2]` -/

/-- `∫_{−2}^{2} |R(e^u)|² du ≤ 5π |W|` for `1`-separated `W` (corpus window mean value). -/
theorem setIntegral_Icc_two_normSq_lagSum_exp_le {W : Finset ℝ} (hW : IsSeparated 1 W) :
    ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 2 ≤ 5 * Real.pi * W.card := by
  have h := setIntegral_Icc_normSq_unitPoly_le W (fun t => t / (2 * Real.pi)) (Real.exp 2)
  have hw := collisionWeight_le_card hW (two_pi_mul_windowScale_le (Real.exp 2))
  rw [Real.log_exp] at h
  simp_rw [← lagSum_exp_eq_finiteFrequencyPoly] at h
  rw [show max (1 : ℝ) 2 = 2 by norm_num] at h
  calc _ ≤ 5 * Real.pi / 2 * 2 *
        Sieve.finiteFrequencyCollisionWeight (fun _ => 1) W (fun t => t / (2 * Real.pi))
          (windowScale (Real.exp 2)) := h
    _ ≤ 5 * Real.pi / 2 * 2 * W.card := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 5 * Real.pi * W.card := by ring

/-- `∫_{−2}^{2} |R(e^u)|⁴ du ≤ 5π E(W)` (corpus window mean value applied to `R²`). -/
theorem setIntegral_Icc_two_lagSum_exp_pow_four_le (W : Finset ℝ) :
    ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 4 ≤ 5 * Real.pi * additiveEnergy W := by
  have h := setIntegral_Icc_normSq_unitPoly_le (W ×ˢ W) (fun p => (p.1 + p.2) / (2 * Real.pi))
    (Real.exp 2)
  have hw := pairCollisionWeight_le_additiveEnergy W (two_pi_mul_windowScale_le (Real.exp 2))
  rw [Real.log_exp, show max (1 : ℝ) 2 = 2 by norm_num] at h
  have hfour : ∀ u, ‖lagSum W (Real.exp u)‖ ^ 4
      = ‖Sieve.finiteFrequencyPoly (fun _ => 1) (W ×ˢ W)
          (fun p => (p.1 + p.2) / (2 * Real.pi)) u‖ ^ 2 := by
    intro u
    rw [← lagSum_exp_sq_eq_finiteFrequencyPoly, norm_pow]
    ring
  simp_rw [hfour]
  calc _ ≤ 5 * Real.pi / 2 * 2 * Sieve.finiteFrequencyCollisionWeight (fun _ => 1) (W ×ˢ W)
        (fun p => (p.1 + p.2) / (2 * Real.pi)) (windowScale (Real.exp 2)) := h
    _ ≤ 5 * Real.pi / 2 * 2 * additiveEnergy W := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 5 * Real.pi * additiveEnergy W := by ring

theorem continuous_norm_lagSum_exp_pow (W : Finset ℝ) (k : ℕ) :
    Continuous fun u => ‖lagSum W (Real.exp u)‖ ^ k :=
  (continuous_lagSum_exp W).norm.pow k

/-- `∫_{−2}^{2} |R(e^u)|³ du ≤ 5π |W|^{1/2} E(W)^{1/2}` (Cauchy–Schwarz). -/
theorem setIntegral_Icc_two_lagSum_exp_cube_le {W : Finset ℝ} (hW : IsSeparated 1 W) :
    ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 3 ≤
      5 * Real.pi * (Real.sqrt W.card * Real.sqrt (additiveEnergy W)) := by
  set μ := volume.restrict (Icc (-2 : ℝ) 2)
  have hf : Continuous fun u => ‖lagSum W (Real.exp u)‖ := (continuous_lagSum_exp W).norm
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := μ)
    (f := fun u => ‖lagSum W (Real.exp u)‖) (g := fun u => ‖lagSum W (Real.exp u)‖ ^ 2)
    hf.aestronglyMeasurable (hf.pow 2).aestronglyMeasurable
    ((continuous_norm_lagSum_exp_pow W 2).integrableOn_Icc)
    (((continuous_pow 2).comp (continuous_norm_lagSum_exp_pow W 2)).integrableOn_Icc)
  have e3 : ∫ u, ‖lagSum W (Real.exp u)‖ * ‖lagSum W (Real.exp u)‖ ^ 2 ∂μ =
      ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 3 := by
    congr 1; funext u; ring
  have e4 : ∫ u, (‖lagSum W (Real.exp u)‖ ^ 2) ^ 2 ∂μ =
      ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 4 := by
    congr 1; funext u; ring
  rw [e3, e4] at hcs
  have h2 := setIntegral_Icc_two_normSq_lagSum_exp_le hW
  have h4 := setIntegral_Icc_two_lagSum_exp_pow_four_le W
  have hI3 : 0 ≤ ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 3 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity
  have hI2 : 0 ≤ ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity
  have hprod : (∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 3) ^ 2 ≤
      (5 * Real.pi * (Real.sqrt W.card * Real.sqrt (additiveEnergy W))) ^ 2 := by
    calc _ ≤ (∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 2) *
          ∫ u in Icc (-2 : ℝ) 2, ‖lagSum W (Real.exp u)‖ ^ 4 := hcs
      _ ≤ (5 * Real.pi * W.card) * (5 * Real.pi * additiveEnergy W) :=
          mul_le_mul h2 h4 (setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity)
            (by positivity)
      _ = _ := by
          rw [show (5 * Real.pi * (Real.sqrt W.card * Real.sqrt (additiveEnergy W))) ^ 2 =
              25 * Real.pi ^ 2 * Real.sqrt (W.card : ℝ) ^ 2 *
                Real.sqrt (additiveEnergy W : ℝ) ^ 2 by ring,
            Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
          ring
  exact (pow_le_pow_iff_left₀ hI3 (by positivity) (by norm_num)).mp hprod

/-! ### Lemma 11.8 -/

/-- The log-ratios of `(N, 2N]²` lie in `[−1, 1]`. -/
theorem abs_logRatio_le_one {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)) : |logRatio p| ≤ 1 := by
  obtain ⟨hp1, hp2⟩ := mem_product.mp hp
  obtain ⟨a1, b1⟩ := mem_Ioc.mp hp1
  obtain ⟨a2, b2⟩ := mem_Ioc.mp hp2
  have h1 : (0 : ℝ) < p.1 := by exact_mod_cast (show 0 < p.1 by omega)
  have h2 : (0 : ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have c1 : (p.1 : ℝ) ≤ 2 * p.2 := by
    have : p.1 ≤ 2 * p.2 := by omega
    exact_mod_cast this
  have c2 : (p.2 : ℝ) ≤ 2 * p.1 := by
    have : p.2 ≤ 2 * p.1 := by omega
    exact_mod_cast this
  have hr : 0 < (p.1 : ℝ) / p.2 := div_pos h1 h2
  have hup : Real.log ((p.1 : ℝ) / p.2) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos hr
    have : (p.1 : ℝ) / p.2 ≤ 2 := by rw [div_le_iff₀ h2]; linarith
    linarith
  have hlo : -1 ≤ Real.log ((p.1 : ℝ) / p.2) := by
    have := Real.one_sub_inv_le_log_of_pos hr
    have : ((p.1 : ℝ) / p.2)⁻¹ ≤ 2 := by rw [inv_div, div_le_iff₀ h1]; linarith
    linarith
  unfold logRatio
  rw [abs_le]; exact ⟨hlo, hup⟩

/-- `|W| ≤ |W|^{1/2} E(W)^{1/2}` (as `E(W) ≥ |W|²`). -/
theorem card_le_sqrt_mul_sqrt_additiveEnergy (W : Finset ℝ) :
    (W.card : ℝ) ≤ Real.sqrt W.card * Real.sqrt (additiveEnergy W) := by
  have hE := card_sq_le_additiveEnergy W
  have hX : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hsq : Real.sqrt ((W.card : ℝ) ^ 2) ≤ Real.sqrt (additiveEnergy W) := Real.sqrt_le_sqrt hE
  rw [Real.sqrt_sq hX] at hsq
  have h1 : Real.sqrt (W.card : ℝ) * Real.sqrt (W.card : ℝ) = W.card := Real.mul_self_sqrt hX
  have h2 : Real.sqrt (W.card : ℝ) ≤ W.card ∨ (W.card : ℝ) < 1 := by
    rcases le_or_gt 1 (W.card : ℝ) with h | h
    · left
      calc Real.sqrt (W.card : ℝ) ≤ Real.sqrt (W.card : ℝ) * Real.sqrt (W.card : ℝ) :=
            le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr h)
        _ = W.card := h1
    · right; exact h
  rcases h2 with h2 | h2
  · calc (W.card : ℝ) = Real.sqrt W.card * Real.sqrt W.card := h1.symm
      _ ≤ Real.sqrt W.card * Real.sqrt (additiveEnergy W) :=
          mul_le_mul_of_nonneg_left (le_trans (by rw [h1] at *; exact h2) hsq) (Real.sqrt_nonneg _)
  · have : W.card = 0 := by
      have : W.card < 1 := by exact_mod_cast h2
      omega
    rw [this]; simp

/-- **Guth–Maynard Lemma 11.8**, unconditionally: for every `ε > 0` there is `C ≥ 0` such that
for `T ≥ 2`, `N ≥ 1`, `D ≥ 0` and every `1`-separated `W ⊆ [T₀, T₀ + T]`:
`Σ_{n₁,n₂ ∈ (N,2N], gcd(n₁,n₂) ≤ D} |R(n₁/n₂)|³ ≤ C T^ε (D T + N²) |W|^{1/2} E(W)^{1/2}`. -/
theorem guthMaynard_lemma118 {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (W : Finset ℝ) (T T₀ D : ℝ), 2 ≤ T → 1 ≤ N → 0 ≤ D →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W →
      ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
          (fun p => ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ D),
          ‖lagSum W ((p.1 : ℝ) / p.2)‖ ^ 3 ≤
        C * T ^ ε * (D * T + (N : ℝ) ^ 2) *
          (Real.sqrt W.card * Real.sqrt (additiveEnergy W)) := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  obtain ⟨C₁, hC₁, htail⟩ := exists_bandTail_rpow_le hε'0 2
  have hbm := bandMass_nonneg
  have hbs := bandSup_nonneg
  refine ⟨160 * Real.pi * bandMass ^ 2 * bandSup + 4 * bandMass ^ 2 * C₁, by positivity,
    fun N W T T₀ D hT hN hD hW hsep => ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set P := (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
    (fun p => ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ D)
  set δ := T ^ ε' / T with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hTε' : 1 ≤ T ^ ε' := Real.one_le_rpow hT1 hε'0.le
  have hTεε : T ^ ε' ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hT0]
    calc T ^ ε' ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (min_le_right _ _)
      _ = T := Real.rpow_one T
  have hTδ : T * δ = T ^ ε' := by rw [hδdef]; field_simp
  set g : ℝ → ℝ := fun u => ‖lagSum W (Real.exp u)‖ ^ 3
  have hg0 : ∀ u, 0 ≤ g u := fun u => by positivity
  have hgc : Continuous g := continuous_norm_lagSum_exp_pow W 3
  set E3 := Real.sqrt W.card * Real.sqrt (additiveEnergy W)
  have hE3 : 0 ≤ E3 := by positivity
  -- pointwise: Lemma 11.7 in cube form
  have hpt : ∀ p ∈ P, ‖lagSum W ((p.1 : ℝ) / p.2)‖ ^ 3 ≤
      bandMass ^ 2 * (T * bandSup * (∫ η in -δ..δ, g (logRatio p + η)) +
        (W.card : ℝ) ^ 3 * bandTail (T ^ ε')) := by
    intro p hp
    have hpP := (mem_filter.mp hp).1
    have hr : 0 < (p.1 : ℝ) / p.2 := by
      obtain ⟨hp1, hp2⟩ := mem_product.mp hpP
      have := (mem_Ioc.mp hp1).1
      have := (mem_Ioc.mp hp2).1
      exact div_pos (by exact_mod_cast (show 0 < p.1 by omega))
        (by exact_mod_cast (show 0 < p.2 by omega))
    have h := norm_lagSum_exp_cube_le_local hT0 hδ0 hW (logRatio p)
    rw [logRatio, Real.exp_log hr, hTδ] at h
    exact h
  -- the windows overlap at most `D + 32δN²` times
  have hover := sum_intervalIntegral_le_of_overlap P logRatio hδ0 hg0 hgc (c := 2)
    (fun p hp => by
      have := abs_le.mp (abs_logRatio_le_one (mem_filter.mp hp).1)
      constructor <;> linarith [this.1, this.2])
    (fun u => card_smallGcd_near_le hN hD hδ0 u)
  have hcube := setIntegral_Icc_two_lagSum_exp_cube_le (W := W) hsep
  have hcard := card_le_of_isSeparated_of_mem hT0.le hW hsep
  have hPcard : (P.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : P.card ≤ N ^ 2 := by
      refine (card_filter_le _ _).trans ?_
      rw [card_product, Nat.card_Ioc, show 2 * N - N = N by omega, sq]
    exact_mod_cast this
  have hW3 : (W.card : ℝ) ^ 3 ≤ 4 * T ^ 2 * W.card := by
    have hX : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    have h2 : (W.card : ℝ) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ hX (by linarith) 2
    calc (W.card : ℝ) ^ 3 = (W.card : ℝ) ^ 2 * W.card := by ring
      _ ≤ (2 * T) ^ 2 * W.card := mul_le_mul_of_nonneg_right h2 hX
      _ = 4 * T ^ 2 * W.card := by ring
  have htl := htail T hT1
  have hT2 : T ^ (-2 : ℝ) * T ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hT0]; norm_num
  have hcardE := card_le_sqrt_mul_sqrt_additiveEnergy W
  -- the main term
  have hmain : bandMass ^ 2 * T * bandSup * ∑ p ∈ P, ∫ η in -δ..δ, g (logRatio p + η) ≤
      160 * Real.pi * bandMass ^ 2 * bandSup * T ^ ε * (D * T + (N : ℝ) ^ 2) * E3 := by
    have h1 : ∑ p ∈ P, ∫ η in -δ..δ, g (logRatio p + η) ≤
        (D + 32 * δ * (N : ℝ) ^ 2) * (5 * Real.pi * E3) :=
      hover.trans (mul_le_mul_of_nonneg_left hcube (by positivity))
    have h2 : T * (D + 32 * δ * (N : ℝ) ^ 2) ≤ 32 * T ^ ε * (D * T + (N : ℝ) ^ 2) := by
      have : T * (D + 32 * δ * (N : ℝ) ^ 2) = D * T + 32 * T ^ ε' * (N : ℝ) ^ 2 := by
        rw [← hTδ]; ring
      rw [this]
      have hTε1 : 1 ≤ T ^ ε := hTε'.trans hTεε
      have hDT : 0 ≤ D * T := mul_nonneg hD hT0.le
      have a1 : D * T ≤ 32 * T ^ ε * (D * T) := by
        have : (1 : ℝ) ≤ 32 * T ^ ε := by linarith
        exact le_mul_of_one_le_left hDT this
      have a2 : 32 * T ^ ε' * (N : ℝ) ^ 2 ≤ 32 * T ^ ε * (N : ℝ) ^ 2 := by gcongr
      have e : 32 * T ^ ε * (D * T + (N : ℝ) ^ 2) =
          32 * T ^ ε * (D * T) + 32 * T ^ ε * (N : ℝ) ^ 2 := by ring
      rw [e]
      linarith
    have hc : 0 ≤ bandMass ^ 2 * bandSup := by positivity
    calc bandMass ^ 2 * T * bandSup * ∑ p ∈ P, ∫ η in -δ..δ, g (logRatio p + η)
        ≤ bandMass ^ 2 * T * bandSup * ((D + 32 * δ * (N : ℝ) ^ 2) * (5 * Real.pi * E3)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = bandMass ^ 2 * bandSup * 5 * Real.pi * E3 * (T * (D + 32 * δ * (N : ℝ) ^ 2)) := by ring
      _ ≤ bandMass ^ 2 * bandSup * 5 * Real.pi * E3 *
            (32 * T ^ ε * (D * T + (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  -- the tail term
  have herr : bandMass ^ 2 * ((P.card : ℝ) * ((W.card : ℝ) ^ 3 * bandTail (T ^ ε'))) ≤
      4 * bandMass ^ 2 * C₁ * T ^ ε * (D * T + (N : ℝ) ^ 2) * E3 := by
    have hb0 := bandTail_nonneg (T ^ ε')
    calc bandMass ^ 2 * ((P.card : ℝ) * ((W.card : ℝ) ^ 3 * bandTail (T ^ ε')))
        ≤ bandMass ^ 2 * ((N : ℝ) ^ 2 * ((4 * T ^ 2 * W.card) * (C₁ * T ^ (-2 : ℝ)))) := by
          gcongr
      _ = 4 * bandMass ^ 2 * C₁ * (N : ℝ) ^ 2 * W.card * (T ^ (-2 : ℝ) * T ^ 2) := by ring
      _ = 4 * bandMass ^ 2 * C₁ * (N : ℝ) ^ 2 * W.card := by rw [hT2, mul_one]
      _ ≤ 4 * bandMass ^ 2 * C₁ * T ^ ε * (D * T + (N : ℝ) ^ 2) * E3 := by
          have h1 : (N : ℝ) ^ 2 * W.card ≤ (D * T + (N : ℝ) ^ 2) * E3 :=
            mul_le_mul (le_add_of_nonneg_left (mul_nonneg hD hT0.le)) hcardE (Nat.cast_nonneg _)
              (by positivity)
          have h2 : 1 ≤ T ^ ε := hTε'.trans hTεε
          have h3 : 0 ≤ (D * T + (N : ℝ) ^ 2) * E3 := by positivity
          calc 4 * bandMass ^ 2 * C₁ * (N : ℝ) ^ 2 * W.card =
                (4 * bandMass ^ 2 * C₁) * ((N : ℝ) ^ 2 * W.card) := by ring
            _ ≤ (4 * bandMass ^ 2 * C₁) * (T ^ ε * ((D * T + (N : ℝ) ^ 2) * E3)) :=
                mul_le_mul_of_nonneg_left (h1.trans (le_mul_of_one_le_left h3 h2))
                  (by positivity)
            _ = _ := by ring
  calc ∑ p ∈ P, ‖lagSum W ((p.1 : ℝ) / p.2)‖ ^ 3
      ≤ ∑ p ∈ P, bandMass ^ 2 * (T * bandSup * (∫ η in -δ..δ, g (logRatio p + η)) +
          (W.card : ℝ) ^ 3 * bandTail (T ^ ε')) := sum_le_sum hpt
    _ = bandMass ^ 2 * T * bandSup * (∑ p ∈ P, ∫ η in -δ..δ, g (logRatio p + η)) +
          bandMass ^ 2 * ((P.card : ℝ) * ((W.card : ℝ) ^ 3 * bandTail (T ^ ε'))) := by
        simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
        ring
    _ ≤ 160 * Real.pi * bandMass ^ 2 * bandSup * T ^ ε * (D * T + (N : ℝ) ^ 2) * E3 +
          4 * bandMass ^ 2 * C₁ * T ^ ε * (D * T + (N : ℝ) ^ 2) * E3 := add_le_add hmain herr
    _ = _ := by ring

end

end RHTower.GuthMaynard
