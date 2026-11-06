import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.NonrealTimeOnWindows
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensityLong
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit
import GaloisForLFunctions.RHTower.Heat.HeatLocalZeroDensity
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The fourth moment of the depths

Selberg's near-line density says that the zeros of `ζ` with `γ ≍ U` and depth `≥ 2a/log U` number at most
`≪ (log U/a) (U e^{−a/14} + log U)`. Summing `δ⁴` by layers gives the fourth moment of the depths at the size of the
zeros at the critical scale, `U log U · log⁻⁴U`:

`Σ_{γ ≍ U} δ_ρ⁴ ≪ U/log³U`   (`exists_sum_mult_im_pow_four_le`, `exists_blockObs_quartic_zero_le`).

The layer inequality is `b⁴ ≤ 1 + Σ_{k ≤ b} 16k³`. The first term counts all zeros, at depth `≤ 2/log U`; the sum is
paid by the exponential decay of the density.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## Layers -/

theorem pow_four_succ_le_sum (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ 1 + ∑ k ∈ Finset.Icc 1 n, 16 * (k : ℝ) ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith only [ih, hn, mul_nonneg hn hn, mul_nonneg (mul_nonneg hn hn) hn]

/-- **The layer inequality.** `b⁴ ≤ 1 + Σ_{1 ≤ k ≤ N, k ≤ b} 16k³` for `0 ≤ b < N + 1`. -/
theorem pow_four_le_layers {N : ℕ} {b : ℝ} (hb : 0 ≤ b) (hbN : b < (N : ℝ) + 1) :
    b ^ 4 ≤ 1 + ∑ k ∈ Finset.Icc 1 N, (16 * (k : ℝ) ^ 3) * (if (k : ℝ) ≤ b then 1 else 0) := by
  classical
  set n := ⌊b⌋₊ with hn
  have hnb : (n : ℝ) ≤ b := Nat.floor_le hb
  have hbn : b < (n : ℝ) + 1 := Nat.lt_floor_add_one b
  have hnN : n ≤ N := by
    have : (n : ℝ) < (N : ℝ) + 1 := hnb.trans_lt hbN
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have h1 : b ^ 4 ≤ ((n : ℝ) + 1) ^ 4 := pow_le_pow_left₀ hb hbn.le 4
  refine h1.trans ((pow_four_succ_le_sum n).trans ?_)
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc le_rfl hnN
  have h2 : ∑ k ∈ Finset.Icc 1 n, 16 * (k : ℝ) ^ 3 =
      ∑ k ∈ Finset.Icc 1 n, (16 * (k : ℝ) ^ 3) * (if (k : ℝ) ≤ b then 1 else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    rw [if_pos (hk'.trans hnb), mul_one]
  rw [h2]
  have h3 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ =>
    (16 * (k : ℝ) ^ 3) * (if (k : ℝ) ≤ b then 1 else 0)) hsub (fun k _ _ => by
      split_ifs <;> positivity)
  linarith only [h3]

/-- The Selberg weights `k² e^{−k/14}` are summable. -/
def layerConstant : ℝ := ∑' k : ℕ, (k : ℝ) ^ 2 * Real.exp (-(1 / 14) * k)

theorem summable_layer : Summable fun k : ℕ => (k : ℝ) ^ 2 * Real.exp (-(1 / 14) * k) :=
  Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 1 / 14)

theorem sum_layer_le (s : Finset ℕ) : ∑ k ∈ s, (k : ℝ) ^ 2 * Real.exp (-(1 / 14) * k) ≤ layerConstant :=
  summable_layer.sum_le_tsum s fun _ _ => by positivity

theorem layerConstant_nonneg : 0 ≤ layerConstant := tsum_nonneg fun _ => by positivity

/-! ## Zeros of `H₀` and zeros of `ζ` -/

/-- The multiplicity of a zero of `H₀` is the order of the zero of `ζ` above it. -/
theorem zeroMult_zero_eq_zeta_order {z : ℂ} (hz : riemannHeat 0 z = 0) :
    zeroMult (riemannHeat 0) z = (analyticOrderAt riemannZeta ((1 / 2 : ℂ) + I * z)).toNat := by
  have hx : xi ((1 / 2 : ℂ) + I * z) = 0 := by rw [← riemannHeat_zero, hz]
  have hc : (((1 / 2 : ℂ) + I * z) - 1 / 2) * (-I) = z := by
    linear_combination (-z) * I_sq
  rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip (xi_zero_re_mem_open_unit hx),
    DeBruijn.riemannHeat_zero_eq_XiC, zeroMult, ← analyticOrderAt_XiC_centeredCoordinate, hc]

theorem re_half_add_I_mul (z : ℂ) : ((1 / 2 : ℂ) + I * z).re = 1 / 2 - z.im := by
  simp
  ring

theorem im_half_add_I_mul (z : ℂ) : ((1 / 2 : ℂ) + I * z).im = z.re := by
  simp

/-- The zeros of `H₀` with real part in `[T₁, T₂]`. -/
theorem exists_zero_finset (T₁ T₂ : ℝ) :
    ∃ D : Finset ℂ, ∀ z, z ∈ D ↔ riemannHeat 0 z = 0 ∧ T₁ ≤ z.re ∧ z.re ≤ T₂ := by
  classical
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have han : AnalyticOnNhd ℂ (riemannHeat 0) (closedBall 0 (|T₁| + |T₂| + 1)) := fun z _ =>
    (differentiable_riemannHeat h0).analyticAt z
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top h0 z (analyticOrderAt_eq_top.mpr h))
  refine ⟨hfin.toFinset.filter (fun z => T₁ ≤ z.re ∧ z.re ≤ T₂), fun z => ?_⟩
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h2⟩
    rw [mem_closedBall, dist_zero_right]
    have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg h0 h1
    have hre : |z.re| ≤ |T₁| + |T₂| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith only [h2.1, neg_abs_le T₁, abs_nonneg T₂]
      · linarith only [h2.2, le_abs_self T₂, abs_nonneg T₁]
    have := Complex.norm_le_abs_re_add_abs_im z
    linarith only [this, hre, him]

/-! ## Reduction of a block to the zero set -/

theorem sum_w₀_le_two (x : ℝ) (A B : ℤ) : ∑ j ∈ Finset.Icc A B, w₀ (x - j) ≤ 2 := by
  classical
  rw [← Finset.sum_filter_ne_zero]
  have hsub : (Finset.Icc A B).filter (fun j : ℤ => w₀ (x - j) ≠ 0) ⊆ Finset.Icc ⌊x⌋ (⌊x⌋ + 1) := by
    intro j hj
    have hne := (Finset.mem_filter.mp hj).2
    have hlt : |x - j| < 1 := lt_of_not_ge fun h => hne (w₀_eq_zero h)
    obtain ⟨h1, h2⟩ := abs_lt.mp hlt
    have hf1 := Int.floor_le x
    have hf2 := Int.lt_floor_add_one x
    rw [Finset.mem_Icc]
    constructor
    · have : ((⌊x⌋ : ℤ) : ℝ) < (j : ℝ) + 1 := by linarith only [h2, hf1]
      have h3 : ⌊x⌋ < j + 1 := by exact_mod_cast this
      omega
    · have : (j : ℝ) < ((⌊x⌋ : ℤ) : ℝ) + 2 := by linarith only [h1, hf2]
      have h3 : j < ⌊x⌋ + 2 := by exact_mod_cast this
      omega
  have hcard : (Finset.Icc ⌊x⌋ (⌊x⌋ + 1)).card = 2 := by
    rw [Int.card_Icc]
    omega
  calc _ ≤ ∑ _j ∈ (Finset.Icc A B).filter (fun j : ℤ => w₀ (x - j) ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => w₀_le_one _
    _ = (((Finset.Icc A B).filter (fun j : ℤ => w₀ (x - j) ≠ 0)).card : ℝ) := by simp
    _ ≤ ((Finset.Icc ⌊x⌋ (⌊x⌋ + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = 2 := by rw [hcard]; norm_num

/-- A block at time zero is at most twice the total fourth moment of the zeros it can see. -/
theorem blockObs_quartic_zero_le {T₁ T₂ : ℝ} {D : Finset ℂ}
    (hD : ∀ z, z ∈ D ↔ riemannHeat 0 z = 0 ∧ T₁ ≤ z.re ∧ z.re ≤ T₂) {A B : ℤ} (hA : T₁ + 1 ≤ A)
    (hB : (B : ℝ) ≤ T₂ - 1) :
    blockObs uQuartic A B 0 ≤ 2 * ∑ z ∈ D, (zeroMult (riemannHeat 0) z : ℝ) * z.im ^ 4 := by
  have hwin (j : ℤ) (hj : j ∈ Finset.Icc A B) :
      windowObs uQuartic j 0 =
        ∑ z ∈ D, (zeroMult (riemannHeat 0) z : ℝ) * (w₀ (z.re - j) * uQuartic z.im) := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    have hj1 : (A : ℝ) ≤ j := by exact_mod_cast h1
    have hj2 : (j : ℝ) ≤ B := by exact_mod_cast h2
    exact heatLocalizedZeroObservable_eq_sum le_rfl w₀ uQuartic (fun x hx => w₀_eq_zero hx) D
      (fun z hz hr => (hD z).mpr ⟨hz, by
        have := abs_lt.mp hr
        constructor <;> linarith only [this.1, this.2, hA, hB, hj1, hj2]⟩)
  unfold blockObs
  rw [Finset.sum_congr rfl hwin, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have hm : (0 : ℝ) ≤ zeroMult (riemannHeat 0) z := Nat.cast_nonneg _
  have hu : 0 ≤ uQuartic z.im := uQuartic_nonneg _
  have heq : ∑ j ∈ Finset.Icc A B, (zeroMult (riemannHeat 0) z : ℝ) * (w₀ (z.re - j) * uQuartic z.im) =
      (zeroMult (riemannHeat 0) z : ℝ) * uQuartic z.im * ∑ j ∈ Finset.Icc A B, w₀ (z.re - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  have := mul_le_mul_of_nonneg_left (sum_w₀_le_two z.re A B) (mul_nonneg hm hu)
  simp only [uQuartic] at this ⊢
  linarith only [this]

/-- The nonreal part of a conjugation-invariant zero set is twice its lower half. -/
theorem sum_mult_im_pow_four_eq {T₁ T₂ : ℝ} {D : Finset ℂ}
    (hD : ∀ z, z ∈ D ↔ riemannHeat 0 z = 0 ∧ T₁ ≤ z.re ∧ z.re ≤ T₂) :
    ∑ z ∈ D, (zeroMult (riemannHeat 0) z : ℝ) * z.im ^ 4 =
      2 * ∑ z ∈ D.filter (fun z => z.im < 0), (zeroMult (riemannHeat 0) z : ℝ) * z.im ^ 4 := by
  classical
  set F : ℂ → ℝ := fun z => (zeroMult (riemannHeat 0) z : ℝ) * z.im ^ 4 with hF
  have hconj (z : ℂ) (hz : z ∈ D) : (starRingEnd ℂ) z ∈ D := by
    obtain ⟨h1, h2⟩ := (hD z).mp hz
    refine (hD _).mpr ⟨?_, by simpa using h2⟩
    rw [riemannHeat_conj le_rfl, h1, map_zero]
  have hswap : ∑ z ∈ D.filter (fun z => 0 < z.im), F z = ∑ z ∈ D.filter (fun z => z.im < 0), F z := by
    refine Finset.sum_bij' (fun z _ => (starRingEnd ℂ) z) (fun z _ => (starRingEnd ℂ) z) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hconj z h1, by simpa using h2⟩
    · intro z hz
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hconj z h1, by simpa using h2⟩
    · intro z _
      simp
    · intro z _
      simp
    · intro z _
      simp only [hF, zeroMult_riemannHeat_conj le_rfl, Complex.conj_im]
      ring
  have hsplit := Finset.sum_filter_add_sum_filter_not D (fun z => z.im < 0) F
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (D.filter fun z => ¬ z.im < 0)
    (fun z => 0 < z.im) F
  have hzero : ∑ z ∈ (D.filter fun z => ¬ z.im < 0).filter (fun z => ¬ 0 < z.im), F z = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    obtain ⟨-, h3⟩ := Finset.mem_filter.mp h1
    have him : z.im = 0 := le_antisymm (not_lt.mp h2) (not_lt.mp h3)
    simp [hF, him]
  have hpos : (D.filter fun z => ¬ z.im < 0).filter (fun z => 0 < z.im) =
      D.filter fun z => 0 < z.im := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, not_lt.mpr h3.le⟩, h3⟩
  rw [hpos, hzero, hswap, add_zero] at hsplit2
  rw [← hsplit, ← hsplit2]
  ring

/-! ## Counting the zeros -/

/-- The zeros of `H₀` with real part in `[T₁, T₂]` number `≪ (T₂ − T₁ + 2) log T₂`. -/
theorem sum_mult_le_of_near_bound {C X₀ L T₁ T₂ : ℝ} {D : Finset ℂ} (hC : 0 < C)
    (hnear : ∀ X : ℝ, X₀ ≤ X → X ≤ T₂ → ∀ S : Finset ℂ, (∀ z ∈ S, riemannHeat 0 z = 0) →
      (∀ z ∈ S, |z.re - X| ≤ 1) → ((∑ z ∈ S, zeroMult (riemannHeat 0) z : ℕ) : ℝ) ≤ C * L)
    (hL : 0 ≤ L) (hT : T₁ ≤ T₂) (hT₁ : X₀ + 1 ≤ T₁)
    (hD : ∀ z, z ∈ D ↔ riemannHeat 0 z = 0 ∧ T₁ ≤ z.re ∧ z.re ≤ T₂) :
    ∑ z ∈ D, (zeroMult (riemannHeat 0) z : ℝ) ≤ (T₂ - T₁ + 2) * (C * L) := by
  classical
  set I := Finset.Icc ⌊T₁⌋ ⌊T₂⌋ with hI
  have hmaps : ∀ z ∈ D, ⌊z.re⌋ ∈ I := fun z hz => by
    obtain ⟨-, h1, h2⟩ := (hD z).mp hz
    exact Finset.mem_Icc.mpr ⟨Int.floor_le_floor h1, Int.floor_le_floor h2⟩
  have hfib := Finset.sum_fiberwise_of_maps_to (g := fun z : ℂ => ⌊z.re⌋) hmaps
    (fun z => (zeroMult (riemannHeat 0) z : ℝ))
  rw [← hfib]
  have hone (i : ℤ) (hi : i ∈ I) :
      ∑ z ∈ D.filter (fun z => ⌊z.re⌋ = i), (zeroMult (riemannHeat 0) z : ℝ) ≤ C * L := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    have hf1 := Int.floor_le T₂
    have hf2 := Int.lt_floor_add_one T₁
    have hi1 : ((⌊T₁⌋ : ℤ) : ℝ) ≤ i := by exact_mod_cast h1
    have hi2 : (i : ℝ) ≤ ((⌊T₂⌋ : ℤ) : ℝ) := by exact_mod_cast h2
    have := hnear i (by linarith only [hT₁, hf2, hi1]) (hi2.trans hf1)
      (D.filter fun z => ⌊z.re⌋ = i) (fun z hz => ((hD z).mp (Finset.mem_filter.mp hz).1).1)
      (fun z hz => by
        have hz' := (Finset.mem_filter.mp hz).2
        have h3 := Int.floor_le z.re
        have h4 := Int.lt_floor_add_one z.re
        rw [hz'] at h3 h4
        exact abs_le.mpr ⟨by linarith only [h3], by linarith only [h4]⟩)
    rwa [Nat.cast_sum] at this
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC.le hL)
  rw [hI, Int.card_Icc]
  have hle : ⌊T₁⌋ ≤ ⌊T₂⌋ := Int.floor_le_floor hT
  have hcast : (((⌊T₂⌋ + 1 - ⌊T₁⌋).toNat : ℕ) : ℝ) = ((⌊T₂⌋ : ℤ) : ℝ) + 1 - ((⌊T₁⌋ : ℤ) : ℝ) := by
    have h0 : (0 : ℤ) ≤ ⌊T₂⌋ + 1 - ⌊T₁⌋ := by omega
    have h1 : (((⌊T₂⌋ + 1 - ⌊T₁⌋).toNat : ℕ) : ℤ) = ⌊T₂⌋ + 1 - ⌊T₁⌋ := Int.toNat_of_nonneg h0
    have h2 : ((((⌊T₂⌋ + 1 - ⌊T₁⌋).toNat : ℕ) : ℤ) : ℝ) = ((⌊T₂⌋ + 1 - ⌊T₁⌋ : ℤ) : ℝ) := by rw [h1]
    push_cast at h2
    exact h2
  rw [hcast]
  linarith only [Int.floor_le T₂, Int.lt_floor_add_one T₁]

/-! ## The fourth moment -/

/-- **The fourth moment of the depths.** `Σ_{T₁ ≤ γ ≤ T₂} m(ρ) δ_ρ⁴ ≪ U/log³U`, over the zeros of `H₀`. -/
theorem exists_sum_mult_im_pow_four_le :
    ∃ C > 0, ∀ᶠ U : ℝ in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      ∀ D : Finset ℂ, (∀ z, z ∈ D ↔ riemannHeat 0 z = 0 ∧ T₁ ≤ z.re ∧ z.re ≤ T₂) →
        ∑ z ∈ D, (zeroMult (riemannHeat 0) z : ℝ) * z.im ^ 4 ≤ C * U / Real.log U ^ 3 := by
  classical
  obtain ⟨A₀, K₀, hA₀, hK₀, hsel⟩ := exists_selberg_exponential_nearLine_zeroDensity_long
  obtain ⟨Cc, hCc, Xc, hXc, hcount⟩ := exists_sum_zeroMult_riemannHeat_near_le_log
  set S₀ := layerConstant with hS₀
  have hS₀n : 0 ≤ S₀ := layerConstant_nonneg
  set C : ℝ := 2 * 16 * (Cc + 3 * A₀ * S₀ + 3 * K₀) + 1 with hCdef
  have hCpos : 0 < C := by positivity
  refine ⟨C, hCpos, ?_⟩
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hsmall : ∀ᶠ U : ℝ in atTop, Real.log U ^ 4 ≤ U := by
    have := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with U hU hU1
    simp only [one_mul, Real.norm_eq_abs, id_eq] at hU
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith only [hU1])] at hU
    exact hU
  filter_upwards [hsel, hsmall, hlog.eventually_ge_atTop 8,
    eventually_ge_atTop (8 * (Xc + 4)), eventually_ge_atTop (8 : ℝ)] with U hU hsm hL8 hUX hU8
  obtain ⟨T₁, hT₁, T₂, hT₂, hdens⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun D hD => ?_⟩
  set L := Real.log U with hLdef
  have hL : 0 < L := by linarith only [hL8]
  have hUpos : 0 < U := by linarith only [hU8]
  have hT₁U : U / 4 < T₁ := hT₁.1
  have hT₂U : T₂ < U / 2 := hT₂.2
  have hT₁₂ : T₁ < T₂ := by linarith only [hT₁.2, hT₂.1, hU8]
  have hT₁pos : 0 < T₁ := by linarith only [hT₁U, hUpos]
  have hdiff : T₂ - T₁ ≤ U := by linarith only [hT₁U, hT₂U, hUpos]
  -- the lower half and its image under `z ↦ ½ + iz`
  set D₀ := D.filter (fun z => z.im ≤ 0) with hD₀
  set φ : ℂ → ℂ := fun z => (1 / 2 : ℂ) + I * z with hφ
  have hφinj : Function.Injective φ := by
    intro a b h
    have : I * a = I * b := add_left_cancel h
    exact mul_left_cancel₀ I_ne_zero this
  set Z := D₀.image φ with hZ
  have hZmem : ∀ w : ℂ, w ∈ Z ↔ w ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta w = 0 := by
    intro w
    rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2), uIcc_of_le hT₁₂.le]
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hzD, hzim⟩ := Finset.mem_filter.mp hz
      obtain ⟨h0, h1, h2⟩ := (hD z).mp hzD
      have hxi : xi (φ z) = 0 := by rw [← riemannHeat_zero, h0]
      obtain ⟨-, hr⟩ := xi_zero_re_mem_open_unit hxi
      have hre := re_half_add_I_mul z
      have him := im_half_add_I_mul z
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1⟩
      · simp only [hφ]; rw [hre]; linarith only [hzim]
      · linarith only [hr]
      · simp only [hφ]; rw [him]; exact ⟨h1, h2⟩
    · rintro ⟨⟨hr, hi⟩, hζ⟩
      have hnt : ∀ n : ℕ, w ≠ -(2 * ((n : ℂ) + 1)) := by
        intro n h
        have him : w.im = 0 := by rw [h]; simp
        linarith only [him, hi.1, hT₁pos]
      have hxi : xi w = 0 := xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hζ, hnt⟩
      set z : ℂ := -I * (w - 1 / 2) with hz
      have hφz : φ z = w := by
        simp only [hφ, hz]
        linear_combination (-(w - 1 / 2)) * I_sq
      have hzre : z.re = w.im := by simp [hz]
      have hzim : z.im = 1 / 2 - w.re := by
        simp [hz]
      refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨(hD z).mpr ⟨?_, ?_, ?_⟩, ?_⟩, hφz⟩
      · rw [riemannHeat_zero]
        simpa only [hφ, hφz] using (show xi (φ z) = 0 by rw [hφz]; exact hxi)
      · rw [hzre]; exact hi.1
      · rw [hzre]; exact hi.2
      · rw [hzim]; linarith only [hr.1]
  -- the depth coordinate
  set b : ℂ → ℝ := fun z => -z.im * L / 2 with hb
  set N : ℕ := ⌊L⌋₊ with hN
  have hLN : L < (N : ℝ) + 1 := Nat.lt_floor_add_one L
  have hNL : (N : ℝ) ≤ L := Nat.floor_le hL.le
  set D₁ := D.filter (fun z => z.im < 0) with hD₁
  have hD₁sub : D₁ ⊆ D₀ := fun z hz => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨h1, h2.le⟩
  have hbprop (z : ℂ) (hz : z ∈ D₁) : 0 ≤ b z ∧ b z < (N : ℝ) + 1 := by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg le_rfl ((hD z).mp h1).1
    have him2 : -z.im ≤ 1 / 2 := by
      have := (abs_le.mp him).1
      linarith only [this]
    constructor
    · simp only [hb]
      have : 0 < -z.im := by linarith only [h2]
      positivity
    · simp only [hb]
      nlinarith only [him2, hL, hLN]
  have him4 (z : ℂ) : z.im ^ 4 = 16 / L ^ 4 * b z ^ 4 := by
    simp only [hb]
    field_simp
    ring
  -- count of a layer
  have hlayer (k : ℕ) (hk : k ∈ Finset.Icc 1 N)
      (hne : ((D₁.filter fun z => (k : ℝ) ≤ b z).Nonempty)) :
      (16 * (k : ℝ) ^ 3) * ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) ≤
        3 * L * ((k : ℝ) ^ 2 * ((T₂ - T₁) * (A₀ * Real.exp (-(1 / 14) * k))) + (k : ℝ) ^ 2 * (K₀ * L)) := by
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast h1
    -- a witness bounds `k` by `L/4`
    obtain ⟨z₀, hz₀⟩ := hne
    obtain ⟨hz₀D, hz₀b⟩ := Finset.mem_filter.mp hz₀
    have hkL : 2 * (k : ℝ) + 2 ≤ L := by
      obtain ⟨h3, h4⟩ := Finset.mem_filter.mp hz₀D
      have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg le_rfl ((hD z₀).mp h3).1
      have him2 : -z₀.im ≤ 1 / 2 := by
        have := (abs_le.mp him).1
        linarith only [this]
      have hbz : b z₀ ≤ L / 4 := by
        simp only [hb]
        nlinarith only [him2, hL]
      nlinarith only [hbz, hz₀b, hL8]
    have hdk := hdens k hk1 hkL Z hZmem
    -- the layer maps into the Selberg sum
    have hsub : (D₁.filter fun z => (k : ℝ) ≤ b z).image φ ⊆
        Z.filter (fun w => 1 / 2 + 2 * (k : ℝ) / Real.log U ≤ w.re) := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (hD₁sub hz1), ?_⟩
      simp only [hφ]
      rw [re_half_add_I_mul]
      have : 2 * (k : ℝ) / L ≤ -z.im := by
        rw [div_le_iff₀ hL]
        simp only [hb] at hz2
        linarith only [hz2]
      linarith only [this]
    have hsum : ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) ≤
        ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * (k : ℝ) / Real.log U ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      have heq : ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) =
          ∑ w ∈ (D₁.filter fun z => (k : ℝ) ≤ b z).image φ,
            ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
        rw [Finset.sum_image fun x _ y _ h => hφinj h]
        refine Finset.sum_congr rfl fun z hz => ?_
        have hz0 : riemannHeat 0 z = 0 :=
          ((hD z).mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1
        rw [zeroMult_zero_eq_zeta_order hz0]
      rw [heq]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    set c := ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) with hc
    have hcn : 0 ≤ c := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hkpos : (0 : ℝ) < k := by linarith only [hk1]
    have h5 : 2 * Real.pi * ((k : ℝ) / L * c) ≤ (T₂ - T₁) * (A₀ * Real.exp (-((k : ℝ) / 14))) + K₀ * L := by
      refine le_trans ?_ hdk
      have hpi := Real.pi_pos
      have hdiv : 0 ≤ (k : ℝ) / L := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hdiv) (by positivity)
    have hexp : Real.exp (-(1 / 14) * (k : ℝ)) = Real.exp (-((k : ℝ) / 14)) := by
      congr 1
      ring
    rw [hexp]
    -- `16 k³ c ≤ 3 L k² (...)`, using `8/π ≤ 3`
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    set Y := (T₂ - T₁) * (A₀ * Real.exp (-((k : ℝ) / 14))) + K₀ * L with hY
    have h6 : (k : ℝ) * c ≤ L * Y / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      have h7 : 2 * Real.pi * ((k : ℝ) / L * c) * L = 2 * Real.pi * ((k : ℝ) * c) := by
        field_simp
      have h8 := mul_le_mul_of_nonneg_right h5 hL.le
      rw [h7] at h8
      linarith only [h8]
    have hYn : 0 ≤ Y := by
      have : 0 ≤ (T₂ - T₁) * (A₀ * Real.exp (-((k : ℝ) / 14))) := by
        have : 0 ≤ T₂ - T₁ := by linarith only [hT₁₂]
        positivity
      have h9 : 0 ≤ K₀ * L := by positivity
      linarith only [this, h9]
    have h10 : L * Y / (2 * Real.pi) ≤ L * Y / 6 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith only [hpi3])
    have h11 : (k : ℝ) * c ≤ L * Y / 6 := h6.trans h10
    have h12 := mul_le_mul_of_nonneg_left h11 (by positivity : 0 ≤ 16 * (k : ℝ) ^ 2)
    have h13 : 0 ≤ (k : ℝ) ^ 2 * (L * Y) := by positivity
    calc (16 * (k : ℝ) ^ 3) * c = 16 * (k : ℝ) ^ 2 * ((k : ℝ) * c) := by ring
      _ ≤ 16 * (k : ℝ) ^ 2 * (L * Y / 6) := h12
      _ ≤ 3 * ((k : ℝ) ^ 2 * (L * Y)) := by nlinarith only [h13]
      _ = _ := by rw [hY]; ring
  -- the zeros, all of them
  have hcountD := sum_mult_le_of_near_bound (C := Cc) (X₀ := Xc) (L := L) (T₁ := T₁) (T₂ := T₂) hCc
    (fun X hX hXT S hS0 hSre => by
      have hXpos : 0 < X := by linarith only [hX, hXc]
      have hXU : X ≤ U := by linarith only [hXT, hT₂U, hUpos]
      have hlogX : Real.log X ≤ L := Real.log_le_log hXpos hXU
      exact (hcount X hX 0 le_rfl (by norm_num) (by simp) S hS0 hSre).trans
        (mul_le_mul_of_nonneg_left hlogX hCc.le))
    hL.le hT₁₂.le (by linarith only [hT₁U, hUX, hXc]) hD
  have hD₁count : ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) ≤ U * (Cc * L) := by
    have h1 : ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) ≤ ∑ z ∈ D, (zeroMult (riemannHeat 0) z : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
    refine h1.trans (hcountD.trans (mul_le_mul_of_nonneg_right ?_ (by positivity)))
    linarith only [hT₁U, hT₂U, hU8]
  -- the lower half
  have hsumD₁ : ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) * b z ^ 4 ≤
      ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) + ∑ k ∈ Finset.Icc 1 N,
        (16 * (k : ℝ) ^ 3) * ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) := by
    have hswap : ∑ k ∈ Finset.Icc 1 N, (16 * (k : ℝ) ^ 3) *
        ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) =
        ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) * ∑ k ∈ Finset.Icc 1 N,
          (16 * (k : ℝ) ^ 3) * (if (k : ℝ) ≤ b z then 1 else 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> ring
    rw [hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z hz => ?_
    obtain ⟨h1, h2⟩ := hbprop z hz
    have := mul_le_mul_of_nonneg_left (pow_four_le_layers h1 h2)
      (Nat.cast_nonneg (zeroMult (riemannHeat 0) z) : (0 : ℝ) ≤ _)
    linarith only [this]
  have hlayers : ∑ k ∈ Finset.Icc 1 N, (16 * (k : ℝ) ^ 3) *
      ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) ≤
      3 * L * (U * A₀ * S₀ + K₀ * L * L ^ 3) := by
    have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : (16 * (k : ℝ) ^ 3) *
        ∑ z ∈ D₁.filter (fun z => (k : ℝ) ≤ b z), (zeroMult (riemannHeat 0) z : ℝ) ≤
        3 * L * ((k : ℝ) ^ 2 * ((T₂ - T₁) * (A₀ * Real.exp (-(1 / 14) * k))) +
          (k : ℝ) ^ 2 * (K₀ * L)) := by
      rcases (D₁.filter fun z => (k : ℝ) ≤ b z).eq_empty_or_nonempty with he | hne
      · rw [he, Finset.sum_empty, mul_zero]
        have h1 : 0 ≤ T₂ - T₁ := by linarith only [hT₁₂]
        positivity
      · exact hlayer k hk hne
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * ((T₂ - T₁) * (A₀ * Real.exp (-(1 / 14) * k))) ≤
        U * A₀ * S₀ := by
      have hfac : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * ((T₂ - T₁) * (A₀ * Real.exp (-(1 / 14) * k))) =
          (T₂ - T₁) * A₀ * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * Real.exp (-(1 / 14) * k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hfac]
      have h2 := sum_layer_le (Finset.Icc 1 N)
      have h3 : 0 ≤ T₂ - T₁ := by linarith only [hT₁₂]
      calc (T₂ - T₁) * A₀ * ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * Real.exp (-(1 / 14) * k)
          ≤ (T₂ - T₁) * A₀ * S₀ := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ U * A₀ * S₀ := by
            have := mul_le_mul_of_nonneg_right hdiff (mul_nonneg hA₀.le hS₀n)
            nlinarith only [this]
    have h2 : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * (K₀ * L) ≤ K₀ * L * L ^ 3 := by
      have hsq : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 ≤ L ^ 3 := by
        calc ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 ≤ ∑ _k ∈ Finset.Icc 1 N, L ^ 2 := by
              refine Finset.sum_le_sum fun k hk => ?_
              have : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
              exact pow_le_pow_left₀ (Nat.cast_nonneg k) (this.trans hNL) 2
          _ = (N : ℝ) * L ^ 2 := by simp
          _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hNL (by positivity)
          _ = L ^ 3 := by ring
      rw [← Finset.sum_mul]
      calc (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2) * (K₀ * L) ≤ L ^ 3 * (K₀ * L) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = _ := by ring
    linarith only [h1, h2]
  -- assembling
  rw [sum_mult_im_pow_four_eq hD]
  have hconv : ∑ z ∈ D.filter (fun z => z.im < 0), (zeroMult (riemannHeat 0) z : ℝ) * z.im ^ 4 =
      16 / L ^ 4 * ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) * b z ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [him4 z]
    ring
  rw [hconv]
  have hL4 : 0 < L ^ 4 := by positivity
  have hmain : ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) * b z ^ 4 ≤
      L * (U * (Cc + 3 * A₀ * S₀ + 3 * K₀)) := by
    have hK3 : 3 * L * (K₀ * L * L ^ 3) ≤ L * (U * (3 * K₀)) := by
      have : K₀ * L ^ 4 ≤ K₀ * U := mul_le_mul_of_nonneg_left hsm hK₀
      nlinarith only [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 3 * L)]
    nlinarith only [hsumD₁, hD₁count, hlayers, hK3]
  have hfin : 2 * (16 / L ^ 4 * ∑ z ∈ D₁, (zeroMult (riemannHeat 0) z : ℝ) * b z ^ 4) ≤
      2 * (16 / L ^ 4 * (L * (U * (Cc + 3 * A₀ * S₀ + 3 * K₀)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain (by positivity)) (by norm_num)
  refine hfin.trans (le_of_eq_of_le ?_ (?_ : 2 * 16 * (Cc + 3 * A₀ * S₀ + 3 * K₀) * U / L ^ 3 ≤ _))
  · field_simp
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [hCdef]
    nlinarith only [hUpos]

/-- **The block form.** A block of windows inside the Selberg range has fourth moment `≪ U/log³U` at time zero. -/
theorem exists_blockObs_quartic_zero_le :
    ∃ C > 0, ∀ᶠ U : ℝ in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      ∀ A B : ℤ, T₁ + 1 ≤ A → (B : ℝ) ≤ T₂ - 1 →
        blockObs uQuartic A B 0 ≤ C * U / Real.log U ^ 3 := by
  obtain ⟨C, hC, hev⟩ := exists_sum_mult_im_pow_four_le
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hev] with U hU
  obtain ⟨T₁, hT₁, T₂, hT₂, h⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun A B hA hB => ?_⟩
  obtain ⟨D, hD⟩ := exists_zero_finset T₁ T₂
  have h1 := blockObs_quartic_zero_le hD hA hB
  have h2 := h D hD
  calc _ ≤ 2 * ∑ z ∈ D, (zeroMult (riemannHeat 0) z : ℝ) * z.im ^ 4 := h1
    _ ≤ 2 * (C * U / Real.log U ^ 3) := by gcongr
    _ = _ := by ring

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
