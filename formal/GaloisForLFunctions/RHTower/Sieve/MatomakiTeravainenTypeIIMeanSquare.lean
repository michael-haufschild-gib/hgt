import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICover

/-!
# Matomäki–Teräväinen (5.3) for Type-II pieces at `a ∈ [1.0999, 1.1]`
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter Topology Asymptotics

noncomputable section

/-- Polylogarithms times `exp(-(log X)^{1/30})` are `≤ exp(-(log X)^{1/40})/4`, eventually. -/
theorem eventually_polylog_mul_exp_neg_le (m : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ X : ℝ in atTop, C * (1 + Real.log (24 * X)) ^ m * Real.exp (-(Real.log X) ^ (1 / 30 : ℝ)) ≤
      Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) / 4 := by
  set K : ℝ := 4 * C * 25 ^ m + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 4 * C * 25 ^ m := by positivity
    rw [hK]; linarith
  have hlo := isLittleO_log_rpow_atTop (r := 1 / 30) (by norm_num)
  have hL : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ Real.log K + m * Real.log L ≤ L ^ (1 / 30 : ℝ) / 2 ∧
      2 * L ^ (1 / 40 : ℝ) ≤ L ^ (1 / 30 : ℝ) := by
    have hb := hlo.bound (c := 1 / (4 * ((m : ℝ) + 1))) (by positivity)
    have hbig := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 30)).eventually_ge_atTop
      (4 * Real.log K)
    have h120 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 120)).eventually_ge_atTop 2
    filter_upwards [hb, hbig, h120, eventually_ge_atTop (1 : ℝ)] with L hb hbig h120 hL1
    have hL0 : 0 < L := by linarith
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hr0 : 0 < L ^ (1 / 30 : ℝ) := Real.rpow_pos_of_pos hL0 _
    rw [Real.norm_of_nonneg hlogL, Real.norm_of_nonneg hr0.le] at hb
    refine ⟨hL1, ?_, ?_⟩
    · have hm : (m : ℝ) * Real.log L ≤ L ^ (1 / 30 : ℝ) / 4 := by
        have hm1 : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
        calc (m : ℝ) * Real.log L ≤ ((m : ℝ) + 1) * Real.log L :=
              mul_le_mul_of_nonneg_right hm1 hlogL
          _ ≤ ((m : ℝ) + 1) * (1 / (4 * ((m : ℝ) + 1)) * L ^ (1 / 30 : ℝ)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = L ^ (1 / 30 : ℝ) / 4 := by field_simp
      linarith
    · have hsplit : L ^ (1 / 30 : ℝ) = L ^ (1 / 120 : ℝ) * L ^ (1 / 40 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsplit]
      have : 0 ≤ L ^ (1 / 40 : ℝ) := Real.rpow_nonneg hL0.le _
      nlinarith
  filter_upwards [Real.tendsto_log_atTop.eventually hL, eventually_ge_atTop (1 : ℝ)]
    with X ⟨hL1, hL2, hL3⟩ hX1
  set L := Real.log X with hLdef
  have hL0 : 0 < L := by linarith
  have hX0 : 0 < X := by linarith
  have h24 : 1 + Real.log (24 * X) ≤ 25 * L := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24)
    linarith
  have hpos : 0 ≤ 1 + Real.log (24 * X) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 24 * X); linarith
  have hLm : L ^ m = Real.exp (m * Real.log L) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hL0 m)]
  have hKe : K = Real.exp (Real.log K) := (Real.exp_log (by linarith)).symm
  calc C * (1 + Real.log (24 * X)) ^ m * Real.exp (-L ^ (1 / 30 : ℝ))
      ≤ C * (25 * L) ^ m * Real.exp (-L ^ (1 / 30 : ℝ)) := by gcongr
    _ = (4 * C * 25 ^ m) * L ^ m * Real.exp (-L ^ (1 / 30 : ℝ)) / 4 := by ring
    _ ≤ K * L ^ m * Real.exp (-L ^ (1 / 30 : ℝ)) / 4 := by
        gcongr; rw [hK]; linarith
    _ = Real.exp (Real.log K + m * Real.log L - L ^ (1 / 30 : ℝ)) / 4 := by
        rw [hLm, sub_eq_add_neg, Real.exp_add, Real.exp_add, ← hKe]
    _ ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4 := by
        gcongr
        linarith

/-- Polylogarithms times a negative power of `X` are `≤ exp(-(log X)^{1/40})/4`, eventually. -/
theorem eventually_polylog_mul_rpow_neg_le (m : ℕ) {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, C * (1 + Real.log (24 * X)) ^ m * X ^ (-κ) ≤
      Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) / 4 := by
  have hL : ∀ᶠ L : ℝ in atTop, L ^ (1 / 30 : ℝ) ≤ κ * L := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 29 / 30)).eventually_ge_atTop (1 / κ)
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with L h hL0
    have hsplit : L = L ^ (29 / 30 : ℝ) * L ^ (1 / 30 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h1 : 1 ≤ κ * L ^ (29 / 30 : ℝ) := by rw [div_le_iff₀ hκ] at h; linarith
    have hr : 0 ≤ L ^ (1 / 30 : ℝ) := Real.rpow_nonneg hL0.le _
    calc L ^ (1 / 30 : ℝ) ≤ κ * L ^ (29 / 30 : ℝ) * L ^ (1 / 30 : ℝ) := le_mul_of_one_le_left hr h1
      _ = κ * L := by rw [mul_assoc, ← hsplit]
  filter_upwards [eventually_polylog_mul_exp_neg_le m hC, Real.tendsto_log_atTop.eventually hL,
    eventually_ge_atTop (1 : ℝ)] with X hmain hκL hX1
  have hX0 : 0 < X := by linarith
  have hpos : 0 ≤ 1 + Real.log (24 * X) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 24 * X); linarith
  have hXκ : X ^ (-κ) ≤ Real.exp (-(Real.log X) ^ (1 / 30 : ℝ)) := by
    rw [Real.rpow_def_of_pos hX0]
    exact Real.exp_le_exp.2 (by linarith)
  calc C * (1 + Real.log (24 * X)) ^ m * X ^ (-κ)
      ≤ C * (1 + Real.log (24 * X)) ^ m * Real.exp (-(Real.log X) ^ (1 / 30 : ℝ)) := by gcongr
    _ ≤ _ := hmain

theorem perronPoly_div_const (c : ℕ → ℂ) (w : ℂ) (K : ℕ) (σ t : ℝ) :
    perronPoly (fun n => c n / w) K σ t = perronPoly c K σ t / w := by
  unfold perronPoly
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- The normalised long-factor amplitude of Proposition 4.2. -/
theorem matomakiTeravainenDirichletAmplitude_long {X Y z₀ z δ ε : ℝ}
    (data : MTTypeIIPieceData X Y z₀ z δ ε) {B₂ : ℝ} (hB₂ : 0 < B₂) (t : ℝ) :
    matomakiTeravainenDirichletAmplitude ⌈2 * data.M₂⌉₊
        (fun n : Fin ⌈2 * data.M₂⌉₊ =>
          mtRealIntervalAF data.β data.M₂ (2 * data.M₂) ((n : ℕ) + 1) / (B₂ : ℂ)) t =
      ‖mtTypeIILongFactor data 1 t‖ / B₂ := by
  rw [matomakiTeravainenDirichletAmplitude_shift ⌈2 * data.M₂⌉₊
    (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n / (B₂ : ℂ)) t,
    perronPoly_div_const, norm_div, Complex.norm_real, Real.norm_of_nonneg hB₂.le]
  rfl

/-- The short-factor amplitude of Proposition 4.2. -/
theorem matomakiTeravainenDirichletAmplitude_short {X Y z₀ z δ ε : ℝ}
    (data : MTTypeIIPieceData X Y z₀ z δ ε) (t : ℝ) :
    matomakiTeravainenDirichletAmplitude ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊
        (fun n : Fin ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ =>
          mtTypeIIShortAF data ((n : ℕ) + 1)) t =
      ‖mtTypeIIPrimeFactor data 1 t‖ := by
  rw [matomakiTeravainenDirichletAmplitude_shift, mtTypeIIPrimeFactor_eq_perronPoly_shortAF]

/-- Support of the short-factor coefficient vector in `[⌈M₁⌉, 2⌈M₁⌉]`. -/
theorem mtTypeIIShortAF_shift_support {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hdil : (1 + δ) ^ data.indices.card ≤ 2) (hM₁ : 0 < data.M₁) (n : ℕ)
    (hn : mtTypeIIShortAF data (n + 1) ≠ 0) :
    ⌈data.M₁⌉₊ ≤ n + 1 ∧ n + 1 ≤ 2 * ⌈data.M₁⌉₊ := by
  obtain ⟨_, hlo, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hn
  refine ⟨Nat.ceil_le.2 hlo.le, ?_⟩
  have h2 : ((n + 1 : ℕ) : ℝ) ≤ 2 * data.M₁ := by nlinarith
  have hc := Nat.le_ceil data.M₁
  have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * ⌈data.M₁⌉₊ : ℕ) : ℝ) := by push_cast at h2 ⊢; linarith
  exact_mod_cast this

theorem ceil_dilated_le_two_mul_ceil {M d : ℝ} (hM : 0 ≤ M) (hd : d ≤ 2) :
    ⌈d * M⌉₊ ≤ 2 * ⌈M⌉₊ := by
  apply Nat.ceil_le.2
  push_cast
  have := Nat.le_ceil M
  nlinarith

/-- Support of the long-factor coefficient vector in `[⌈M₂⌉, 2⌈M₂⌉]`. -/
theorem mtTypeIILong_shift_support {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    {w : ℂ} (n : ℕ) (hn : mtRealIntervalAF data.β data.M₂ (2 * data.M₂) (n + 1) / w ≠ 0) :
    ⌈data.M₂⌉₊ ≤ n + 1 ∧ n + 1 ≤ 2 * ⌈data.M₂⌉₊ := by
  have hn' : mtRealIntervalAF data.β data.M₂ (2 * data.M₂) (n + 1) ≠ 0 :=
    fun h => hn (by rw [h, zero_div])
  obtain ⟨_, hlo, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hn'
  refine ⟨Nat.ceil_le.2 hlo.le, ?_⟩
  have hc := Nat.le_ceil data.M₂
  have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * ⌈data.M₂⌉₊ : ℕ) : ℝ) := by push_cast at hhi ⊢; linarith
  exact_mod_cast this

/-- The Proposition 4.2 region for a Type-II datum, with the long factor normalised by `B₂`. -/
def typeIIRegion {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε) (T B₂ σ₀ B₁ : ℝ) :
    Set ℝ :=
  matomakiTeravainenTypeIIRegion T ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊
    (fun n => mtTypeIIShortAF data ((n : ℕ) + 1)) ⌈2 * data.M₂⌉₊
    (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) ((n : ℕ) + 1) / (B₂ : ℂ))
    ⌈data.M₁⌉₊ ⌈data.M₂⌉₊ σ₀ B₁

/-- **§5.3 given the Proposition 4.2 bound on the region.** -/
theorem setIntegral_typeII_le_of_region {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
    (hβ : MTUniformDivisorBounded 5 data.β)
    {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P a η εU σ₀ ζ ε₁ δ₀ B₁ Bnd : ℝ} (hP : 1 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k) (hkX : (2 * P) ^ k ≤ X)
    (hlo : X ^ (1 - η) ≤ P ^ k) (hstars : (P + k) ^ k ≤ P ^ k * X ^ η)
    (hfac : (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a)) (ha1 : 1 ≤ a) (ha43 : a ≤ 4 / 3)
    (hη : 0 < η) (hη1 : η ≤ 1) (hεU : 0 ≤ εU)
    {U : Set ℝ} (hU : MeasurableSet U) (hUX : U ⊆ Set.Icc (-X) X)
    (hS : ∀ t ∈ U, P ^ (-εU / 10) ≤
      ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖)
    (hM₁2 : 2 ≤ data.M₁) (hM₂2 : 2 ≤ data.M₂) (hdil : (1 + δ) ^ data.indices.card ≤ 2)
    (hM₂X : data.M₂ ≤ 8 * X) (hM₁X : data.M₁ ^ 5 ≤ X) (hX64 : 64 ≤ X)
    (hdiv5 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 5 ≤ X ^ η)
    (hdiv4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 4 ≤ X ^ η)
    (h1 : X ^ (ε / 2) ≤ data.M₁) (h2 : data.M₁ ^ 5 ≤ X ^ (1 / a))
    (h3 : X ^ (1 - ζ) ≤ data.M₁ * data.M₂)
    (hB₂ : 3 * (1 + Real.log (3 * data.M₂)) ^ 31 ≤ X ^ ζ)
    (hσ₀ : 0 ≤ σ₀) (hσ₀' : σ₀ ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (m1 : δ₀ ≤ σ₀ * ε) (m2 : δ₀ ≤ ε₁) (m3 : 6 / a - 5 - 2 * σ₀ + 5 * ε₁ + 8 * ζ ≤ -δ₀)
    (hF₁1 : ∀ t ∈ U, ‖mtTypeIIPrimeFactor data 1 t‖ ≤ 1)
    (hF₁B : ∀ t ∈ U, ‖mtTypeIIPrimeFactor data 1 t‖ ≤ B₁)
    (hBnd : ∫ t in typeIIRegion data X (3 * (1 + Real.log (3 * data.M₂)) ^ 31) σ₀ B₁,
        matomakiTeravainenDirichletAmplitude ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊
            (fun n => mtTypeIIShortAF data ((n : ℕ) + 1)) t ^ 2 *
          matomakiTeravainenDirichletAmplitude ⌈2 * data.M₂⌉₊
            (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) ((n : ℕ) + 1) /
              ((3 * (1 + Real.log (3 * data.M₂)) ^ 31 : ℝ) : ℂ)) t ^ 2 ≤ Bnd) :
    ∫ t in U, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
      (3 * (1 + Real.log (3 * data.M₂)) ^ 31) ^ 2 * Bnd +
        2 * X * ((3 * (1 + Real.log (3 * data.M₂)) ^ 31) / X) ^ 2 +
        ((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ) *
          (typeIICellConstant η * X ^ (εU / 5 + 6 * η) * (8 * X ^ (-δ₀))) := by
  obtain ⟨B₂, hB₂def⟩ : ∃ B₂, B₂ = 3 * (1 + Real.log (3 * data.M₂)) ^ 31 := ⟨_, rfl⟩
  rw [← hB₂def] at hBnd hB₂ ⊢
  have hlog0 : 0 ≤ Real.log (3 * data.M₂) := Real.log_nonneg (by linarith)
  have hB₂1 : 1 ≤ B₂ := by
    rw [hB₂def]
    have : 1 ≤ (1 + Real.log (3 * data.M₂)) ^ 31 := one_le_pow₀ (by linarith)
    linarith
  have hB₂0 : 0 < B₂ := by linarith
  have hF₂B : ∀ t ∈ U, ‖mtTypeIILongFactor data 1 t‖ ≤ B₂ := fun t _ => by
    rw [hB₂def]; exact norm_mtTypeIILongFactor_le data (by linarith) hβ t
  have hamp₁ := matomakiTeravainenDirichletAmplitude_short data
  have hamp₂ := matomakiTeravainenDirichletAmplitude_long data hB₂0
  have hRX : typeIIRegion data X B₂ σ₀ B₁ ⊆ Set.Icc (-X) X :=
    matomakiTeravainenTypeIIRegion_subset_Icc X _ _ _ _ σ₀ B₁
  refine setIntegral_typeII_le_explicit data hprime hβ hBp hP hB hk hkX hlo hstars hfac ha1 ha43 hη
    hη1 hεU hU hUX hS hM₁2 hM₂2 hdil hM₂X hM₁X hX64 hdiv5 hdiv4 h1 h2 h3 hB₂1 hB₂ hσ₀ hσ₀' hζ
    m1 m2 m3 hRX ?_ hF₁1 hF₂B (continuous_matomakiTeravainenDirichletAmplitude _ _)
    (continuous_matomakiTeravainenDirichletAmplitude _ _) ?_ hBnd
  · intro t ht hR
    have hA1 := hamp₁ t
    have hA2 := hamp₂ t
    have hnot : ¬ ((⌈data.M₁⌉₊ : ℝ) ^ (-σ₀) ≤ ‖mtTypeIIPrimeFactor data 1 t‖ ∨
        (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀) ≤ ‖mtTypeIILongFactor data 1 t‖ / B₂) := by
      intro hor
      apply hR
      refine ⟨⟨⟨⟨hUX ht, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [Set.mem_setOf_eq, hA1]; exact hF₁1 t ht
      · rw [Set.mem_setOf_eq, hA2, div_le_one hB₂0]; exact hF₂B t ht
      · rw [Set.mem_setOf_eq, hA1]; exact hF₁B t ht
      · rcases hor with h | h
        · left; rw [Set.mem_setOf_eq, hA1]; exact h
        · right; rw [Set.mem_setOf_eq, hA2]; exact h
    push Not at hnot
    refine ⟨hnot.1.le, ?_⟩
    have := hnot.2.le
    rw [div_le_iff₀ hB₂0] at this
    linarith
  · intro t
    rw [hamp₁, hamp₂, norm_mul, mul_pow, div_pow]
    field_simp

/-- The final absorption of the four §5.3 contributions. -/
theorem typeII_four_terms_le {X L W B₂ B₁ K J κ ε' E₀ Bnd C₁ : ℝ} {e : ℕ} (hX1 : 1 ≤ X)
    (hL : L = Real.log X) (hW : W = 1 + Real.log (24 * X)) (hB₂0 : 0 ≤ B₂)
    (hB₂ : B₂ ≤ 3 * W ^ 31) (hB₁ : B₁ = Real.exp (-L ^ (1 / 30 : ℝ))) (hK0 : 0 ≤ K)
    (hJ0 : 0 ≤ J) (hJ : J ≤ 2 * W) (hκ : κ ≤ 1 / 2) (hE₀ : E₀ ≤ 8 * X ^ (-ε'))
    (hC₁ : C₁ = 9 * 2 * 16384 * 2 ^ e)
    (hBnd : Bnd = 2 * (16384 * B₁ ^ 2 * (1 + |L|) * 1 ^ 2 * (2 * (1 + |L|)) ^ e +
      X ^ (-κ) + X ^ (-(1 : ℝ) / 2)))
    (hF1 : C₁ * W ^ (63 + e) * Real.exp (-L ^ (1 / 30 : ℝ)) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4)
    (hF2 : 36 * W ^ 62 * X ^ (-κ) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4)
    (hF3 : 18 * W ^ 62 * X ^ (-(1 : ℝ)) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4)
    (hF4 : 16 * K * W ^ 1 * X ^ (-ε') ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4) :
    B₂ ^ 2 * Bnd + 2 * X * (B₂ / X) ^ 2 + J * (K * E₀) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg hX1
  have hW1 : 1 + L ≤ W := by
    rw [hW, hL, Real.log_mul (by norm_num) hX0.ne']
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 24)
    linarith only [this]
  have hW0 : 1 ≤ W := by linarith only [hW1, hL0]
  have hLW : 1 + |L| ≤ W := by rw [abs_of_nonneg hL0]; exact hW1
  have hB₂sq : B₂ ^ 2 ≤ 9 * W ^ 62 := by
    calc B₂ ^ 2 ≤ (3 * W ^ 31) ^ 2 := pow_le_pow_left₀ hB₂0 hB₂ 2
      _ = 9 * W ^ 62 := by ring
  have hB₁sq : B₁ ^ 2 ≤ Real.exp (-L ^ (1 / 30 : ℝ)) := by
    rw [hB₁, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : 0 ≤ L ^ (1 / 30 : ℝ) := Real.rpow_nonneg hL0 _
    push_cast; linarith only [this]
  have hXκ : X ^ (-(1 : ℝ) / 2) ≤ X ^ (-κ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hκ])
  have hXκ0 : 0 ≤ X ^ (-κ) := Real.rpow_nonneg hX0.le _
  have hT1 : B₂ ^ 2 * (2 * (16384 * B₁ ^ 2 * (1 + |L|) * 1 ^ 2 * (2 * (1 + |L|)) ^ e)) ≤
      Real.exp (-L ^ (1 / 40 : ℝ)) / 4 := by
    refine le_trans ?_ hF1
    have h1 : (1 + |L|) * (2 * (1 + |L|)) ^ e ≤ 2 ^ e * W ^ (1 + e) := by
      rw [mul_pow, pow_add, pow_one]
      have ha : (1 + |L|) ^ e ≤ W ^ e := pow_le_pow_left₀ (by positivity) hLW e
      calc (1 + |L|) * (2 ^ e * (1 + |L|) ^ e) ≤ W * (2 ^ e * W ^ e) := by gcongr
        _ = 2 ^ e * (W * W ^ e) := by ring
    have hB₁0 : 0 ≤ B₁ ^ 2 := sq_nonneg _
    calc B₂ ^ 2 * (2 * (16384 * B₁ ^ 2 * (1 + |L|) * 1 ^ 2 * (2 * (1 + |L|)) ^ e))
        = B₂ ^ 2 * (2 * 16384) * B₁ ^ 2 * ((1 + |L|) * (2 * (1 + |L|)) ^ e) := by ring
      _ ≤ (9 * W ^ 62) * (2 * 16384) * Real.exp (-L ^ (1 / 30 : ℝ)) * (2 ^ e * W ^ (1 + e)) := by
          gcongr
      _ = C₁ * W ^ (63 + e) * Real.exp (-L ^ (1 / 30 : ℝ)) := by
          rw [hC₁, show 63 + e = 62 + (1 + e) by omega, pow_add]; ring
  have hT2 : B₂ ^ 2 * (2 * (X ^ (-κ) + X ^ (-(1 : ℝ) / 2))) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4 := by
    refine le_trans ?_ hF2
    calc B₂ ^ 2 * (2 * (X ^ (-κ) + X ^ (-(1 : ℝ) / 2))) ≤ (9 * W ^ 62) * (2 * (2 * X ^ (-κ))) := by
          gcongr; linarith only [hXκ]
      _ = 36 * W ^ 62 * X ^ (-κ) := by ring
  have hT3 : 2 * X * (B₂ / X) ^ 2 ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4 := by
    refine le_trans ?_ hF3
    have hXinv : X ^ (-(1 : ℝ)) = 1 / X := by rw [Real.rpow_neg_one, one_div]
    rw [hXinv]
    calc 2 * X * (B₂ / X) ^ 2 = 2 * B₂ ^ 2 * (1 / X) := by field_simp
      _ ≤ 2 * (9 * W ^ 62) * (1 / X) := by gcongr
      _ = 18 * W ^ 62 * (1 / X) := by ring
  have hT4 : J * (K * E₀) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 4 := by
    refine le_trans ?_ hF4
    have hE0' : K * E₀ ≤ K * (8 * X ^ (-ε')) := mul_le_mul_of_nonneg_left hE₀ hK0
    have hpos : 0 ≤ 16 * K * W ^ 1 * X ^ (-ε') := by positivity
    by_cases hKE : 0 ≤ K * E₀
    · calc J * (K * E₀) ≤ (2 * W) * (K * (8 * X ^ (-ε'))) := mul_le_mul hJ hE0' hKE (by positivity)
        _ = 16 * K * W ^ 1 * X ^ (-ε') := by ring
    · push Not at hKE
      have : J * (K * E₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hJ0 hKE.le
      linarith only [this, hpos]
  rw [hBnd]
  have hsplit : B₂ ^ 2 * (2 * (16384 * B₁ ^ 2 * (1 + |L|) * 1 ^ 2 * (2 * (1 + |L|)) ^ e +
      X ^ (-κ) + X ^ (-(1 : ℝ) / 2))) =
      B₂ ^ 2 * (2 * (16384 * B₁ ^ 2 * (1 + |L|) * 1 ^ 2 * (2 * (1 + |L|)) ^ e)) +
        B₂ ^ 2 * (2 * (X ^ (-κ) + X ^ (-(1 : ℝ) / 2))) := by ring
  rw [hsplit]
  linarith only [hT1, hT2, hT3, hT4]

/-- The four §5.3 contributions are absorbed, eventually. -/
theorem eventually_typeII_four_terms_le {K κ ε' : ℝ} (hK0 : 0 ≤ K) (hκ : 0 < κ)
    (hκ2 : κ ≤ 1 / 2) (hε' : 0 < ε') :
    ∀ᶠ X : ℝ in atTop, ∀ B₂ J E₀ : ℝ, 0 ≤ B₂ → B₂ ≤ 3 * (1 + Real.log (24 * X)) ^ 31 →
      0 ≤ J → J ≤ 2 * (1 + Real.log (24 * X)) → E₀ ≤ 8 * X ^ (-ε') →
      B₂ ^ 2 * (2 * (16384 * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)) ^ 2 *
          (1 + |Real.log X|) * 1 ^ 2 * (2 * (1 + |Real.log X|)) ^ (2 ^ (2 * (5 + 1)) - 1) +
          X ^ (-κ) + X ^ (-(1 : ℝ) / 2))) +
        2 * X * (B₂ / X) ^ 2 + J * (K * E₀) ≤ Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = 2 ^ (2 * (5 + 1)) - 1 := ⟨_, rfl⟩
  rw [← he]
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 9 * 2 * 16384 * 2 ^ e := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  filter_upwards [eventually_polylog_mul_exp_neg_le (63 + e) hC₁0,
    eventually_polylog_mul_rpow_neg_le 62 (C := 36) (by norm_num) hκ,
    eventually_polylog_mul_rpow_neg_le 62 (C := 18) (by norm_num) one_pos,
    eventually_polylog_mul_rpow_neg_le 1 (C := 16 * K) (by linarith) hε',
    eventually_ge_atTop (1 : ℝ)] with X hf1 hf2 hf3 hf4 hX1 B₂ J E₀ hB₂0 hB₂ hJ0 hJ hE₀
  have hf1' : C₁ * (1 + Real.log (24 * X)) ^ (63 + e) *
      Real.exp (-(Real.log X) ^ (1 / 30 : ℝ)) ≤ Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) / 4 := hf1
  exact typeII_four_terms_le (L := Real.log X) (W := 1 + Real.log (24 * X))
    (B₁ := Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30))) hX1 rfl rfl hB₂0 hB₂ (by norm_num) hK0 hJ0
    hJ hκ2 hE₀ hC₁ rfl hf1' hf2 hf3 (by simpa [mul_assoc] using hf4)

/-- Polylogarithmic bounds by powers of `X`, eventually. -/
theorem eventually_polylog_le_rpow (m : ℕ) {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, C * (1 + Real.log (24 * X)) ^ m ≤ X ^ κ := by
  filter_upwards [eventually_polylog_mul_rpow_neg_le m hC hκ, eventually_gt_atTop (0 : ℝ)]
    with X h hX0
  have hXκ : 0 < X ^ κ := Real.rpow_pos_of_pos hX0 κ
  have hexp : Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    by_cases hl : 0 ≤ Real.log X
    · have := Real.rpow_nonneg hl (1 / 40 : ℝ); linarith
    · have : Real.log X ^ (1 / 40 : ℝ) = Real.exp (Real.log (Real.log X) * (1 / 40)) *
          Real.cos ((1 / 40) * Real.pi) := Real.rpow_def_of_neg (by linarith) _
      have hcos : 0 ≤ Real.cos ((1 / 40) * Real.pi) :=
        Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      rw [this]; have := Real.exp_pos (Real.log (Real.log X) * (1 / 40)); nlinarith
  have h' : C * (1 + Real.log (24 * X)) ^ m * X ^ (-κ) ≤ 1 := by linarith
  rw [Real.rpow_neg hX0.le, ← div_eq_mul_inv, div_le_one hXκ] at h'
  exact h'

/-- The scales of a Type-II datum at `Y ∈ [X/(log X)², X]`. -/
theorem typeII_datum_scales {X Y z₀ δ ε a ζ : ℝ}
    (data : MTTypeIIPieceData X Y z₀ (X ^ (2 / 11 : ℝ)) δ ε) (hX64 : 64 ≤ X)
    (hlog1 : 1 ≤ Real.log X) (hX8 : 2 ≤ X ^ (ε / 2))
    (hX9 : 4 * (1 + Real.log (24 * X)) ^ 2 ≤ X ^ (9 / 11 : ℝ))
    (hX10 : 2 * (1 + Real.log (24 * X)) ^ 2 ≤ X ^ ζ)
    (hX11 : 3 * (1 + Real.log (24 * X)) ^ 31 ≤ X ^ ζ)
    (hYlo : X / Real.log X ^ 2 ≤ Y) (hYhi : Y ≤ X) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) :
    2 ≤ data.M₁ ∧ 2 ≤ data.M₂ ∧ data.M₂ ≤ 8 * X ∧ data.M₁ ^ 5 ≤ X ∧
      data.M₁ ^ 5 ≤ X ^ (1 / a) ∧ X ^ (1 - ζ) ≤ data.M₁ * data.M₂ ∧
      3 * (1 + Real.log (3 * data.M₂)) ^ 31 ≤ X ^ ζ ∧
      X / (2 * Real.log X ^ 2) < data.M₁ * data.M₂ ∧ data.M₁ * data.M₂ ≤ 4 * X := by
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨hM₁lo, hM₁hi⟩ := data.M₁_mem
  obtain ⟨hprodlo, hprodhi⟩ := data.product_mem
  have hM₁2 : 2 ≤ data.M₁ := hX8.trans hM₁lo
  have hM₁0 : 0 < data.M₁ := by linarith
  have hLW : Real.log X ≤ 1 + Real.log (24 * X) := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 24); linarith
  have hlogsq : Real.log X ^ 2 ≤ (1 + Real.log (24 * X)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hLW 2
  have hlogpos : 0 < Real.log X ^ 2 := by positivity
  have hYhalf : X / (2 * Real.log X ^ 2) ≤ Y / 2 := by
    have heq : X / (2 * Real.log X ^ 2) = (X / Real.log X ^ 2) / 2 := by
      rw [div_div, mul_comm]
    rw [heq]; exact div_le_div_of_nonneg_right hYlo (by norm_num)
  have hprodX : X / (2 * Real.log X ^ 2) < data.M₁ * data.M₂ := hYhalf.trans_lt hprodlo
  have hX911 : X = X ^ (2 / 11 : ℝ) * X ^ (9 / 11 : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  have hM₂2 : 2 ≤ data.M₂ := by
    have h4 : 4 * Real.log X ^ 2 ≤ X ^ (9 / 11 : ℝ) := by linarith
    have h5 : 2 * data.M₁ ≤ X / (2 * Real.log X ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hz0 : 0 ≤ X ^ (2 / 11 : ℝ) := by positivity
      calc 2 * data.M₁ * (2 * Real.log X ^ 2) = data.M₁ * (4 * Real.log X ^ 2) := by ring
        _ ≤ X ^ (2 / 11 : ℝ) * X ^ (9 / 11 : ℝ) :=
            mul_le_mul hM₁hi h4 (by positivity) hz0
        _ = X := hX911.symm
    by_contra hlt
    push Not at hlt
    have : data.M₁ * data.M₂ ≤ data.M₁ * 2 := mul_le_mul_of_nonneg_left hlt.le hM₁0.le
    linarith
  have hM₂0 : 0 < data.M₂ := by linarith
  have hprod4 : data.M₁ * data.M₂ ≤ 4 * X := by linarith
  have hM₂X4 : data.M₂ ≤ 4 * X := by
    have : data.M₂ ≤ data.M₁ * data.M₂ := le_mul_of_one_le_left hM₂0.le (by linarith)
    linarith
  have hM₁5 : data.M₁ ^ 5 ≤ X ^ (10 / 11 : ℝ) := by
    calc data.M₁ ^ 5 ≤ (X ^ (2 / 11 : ℝ)) ^ 5 := pow_le_pow_left₀ hM₁0.le hM₁hi 5
      _ = X ^ (10 / 11 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hM₁X : data.M₁ ^ 5 ≤ X := hM₁5.trans (by
    calc X ^ (10 / 11 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
      _ = X := Real.rpow_one X)
  have h2 : data.M₁ ^ 5 ≤ X ^ (1 / a) := hM₁5.trans
    (Real.rpow_le_rpow_of_exponent_le hX1.le (by rw [le_div_iff₀ (by linarith)]; linarith))
  have h3 : X ^ (1 - ζ) ≤ data.M₁ * data.M₂ := by
    have hXζ : 0 < X ^ ζ := Real.rpow_pos_of_pos hX0 ζ
    have : X ^ (1 - ζ) ≤ X / (2 * Real.log X ^ 2) := by
      rw [Real.rpow_sub hX0, Real.rpow_one]
      exact div_le_div_of_nonneg_left hX0.le (by positivity) (by linarith)
    linarith
  have hB₂ : 3 * (1 + Real.log (3 * data.M₂)) ^ 31 ≤ X ^ ζ := by
    have hl : Real.log (3 * data.M₂) ≤ Real.log (24 * X) :=
      Real.log_le_log (by positivity) (by linarith)
    have h0 : 0 ≤ 1 + Real.log (3 * data.M₂) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 * data.M₂); linarith
    calc 3 * (1 + Real.log (3 * data.M₂)) ^ 31 ≤ 3 * (1 + Real.log (24 * X)) ^ 31 := by gcongr
      _ ≤ X ^ ζ := hX11
  exact ⟨hM₁2, hM₂2, by linarith, hM₁X, h2, h3, hB₂, hprodX, hprod4⟩

/-- Proposition 4.2 applied to the two factors of a Type-II datum. -/
theorem typeII_region_integral_le {X Y z₀ δ ε σ₀ B₁ B₂ T₀ : ℝ}
    (hP42 : ∀ (T : ℝ) (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ) (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ) (B₁ : ℝ),
      T₀ ≤ T → 1 ≤ N₁ → N₁ ≤ 2 * A₁ → 1 ≤ N₂ → N₂ ≤ 2 * A₂ →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) → T ^ (ε / 2) ≤ (A₁ : ℝ) →
      (A₁ : ℝ) ≤ T ^ ((2 : ℝ) / 11 + 4 * (ε / 6)) →
      T / (16 * (1 + |Real.log T|) ^ 2) ≤ (A₁ : ℝ) * (A₂ : ℝ) →
      (A₁ : ℝ) * (A₂ : ℝ) ≤ T * (16 * (1 + |Real.log T|) ^ 2) →
      (∀ n : Fin N₁, ‖a₁ n‖ ≤ 1 * ((((n : ℕ) + 1).divisors.card : ℝ) ^ 0)) →
      (∀ n : Fin N₂, ‖a₂ n‖ ≤ 1 * ((((n : ℕ) + 1).divisors.card : ℝ) ^ 5)) →
      (∀ n : Fin N₁, a₁ n ≠ 0 → A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∀ n : Fin N₂, a₂ n ≠ 0 → A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∫ t in matomakiTeravainenTypeIIRegion T N₁ a₁ N₂ a₂ A₁ A₂ σ₀ B₁,
          matomakiTeravainenDirichletAmplitude N₁ a₁ t ^ 2 *
            matomakiTeravainenDirichletAmplitude N₂ a₂ t ^ 2)
        ≤ 2 * (16384 * B₁ ^ 2 * (1 + |Real.log T|) * 1 ^ 2 *
              (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (5 + 1)) - 1)
            + T ^ (-((ε / 6) ^ 2 / 20)) + T ^ (-(1 : ℝ) / 2)))
    (hT₀X : T₀ ≤ X) (data : MTTypeIIPieceData X Y z₀ (X ^ (2 / 11 : ℝ)) δ ε)
    (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
    (hβ : MTUniformDivisorBounded 5 data.β) (hdil : (1 + δ) ^ data.indices.card ≤ 2)
    (hX1 : 1 < X) (hlog1 : 1 ≤ Real.log X) (hX8b : 2 ≤ X ^ (4 * (ε / 6)))
    (hM₁2 : 2 ≤ data.M₁) (hM₂2 : 2 ≤ data.M₂)
    (hprodX : X / (2 * Real.log X ^ 2) < data.M₁ * data.M₂)
    (hprod4 : data.M₁ * data.M₂ ≤ 4 * X) (hB₂1 : 1 ≤ B₂) :
    (∫ t in typeIIRegion data X B₂ σ₀ B₁,
        matomakiTeravainenDirichletAmplitude ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊
            (fun n => mtTypeIIShortAF data ((n : ℕ) + 1)) t ^ 2 *
          matomakiTeravainenDirichletAmplitude ⌈2 * data.M₂⌉₊
            (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) ((n : ℕ) + 1) /
              (B₂ : ℂ)) t ^ 2) ≤
      2 * (16384 * B₁ ^ 2 * (1 + |Real.log X|) * 1 ^ 2 *
            (2 * (1 + |Real.log X|)) ^ (2 ^ (2 * (5 + 1)) - 1)
          + X ^ (-((ε / 6) ^ 2 / 20)) + X ^ (-(1 : ℝ) / 2)) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨hM₁lo, hM₁hi⟩ := data.M₁_mem
  have hM₁0 : 0 < data.M₁ := by linarith
  have hM₂0 : 0 < data.M₂ := by linarith
  have hA₁ := Nat.le_ceil data.M₁
  have hA₂ := Nat.le_ceil data.M₂
  have hA₁' := Nat.ceil_lt_add_one hM₁0.le
  have hA₂' := Nat.ceil_lt_add_one hM₂0.le
  have hlogabs : |Real.log X| = Real.log X := abs_of_nonneg (by linarith)
  refine hP42 X _ _ _ _ _ _ _ hT₀X ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2
      (mul_pos (pow_pos (by linarith [data.δ_nonneg]) _) hM₁0)).ne'
  · exact ceil_dilated_le_two_mul_ceil hM₁0.le hdil
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  · exact ceil_dilated_le_two_mul_ceil hM₂0.le le_rfl
  · linarith
  · linarith
  · exact hM₁lo.trans hA₁
  · have hsplit : X ^ ((2 : ℝ) / 11 + 4 * (ε / 6)) = X ^ (2 / 11 : ℝ) * X ^ (4 * (ε / 6)) :=
      Real.rpow_add hX0 _ _
    rw [hsplit]
    have hz1 : 1 ≤ X ^ (2 / 11 : ℝ) := Real.one_le_rpow hX1.le (by norm_num)
    nlinarith
  · rw [hlogabs]
    have h1 : X / (16 * (1 + Real.log X) ^ 2) ≤ X / (2 * Real.log X ^ 2) :=
      div_le_div_of_nonneg_left hX0.le (by positivity) (by nlinarith)
    have h2 : data.M₁ * data.M₂ ≤ (⌈data.M₁⌉₊ : ℝ) * (⌈data.M₂⌉₊ : ℝ) :=
      mul_le_mul hA₁ hA₂ hM₂0.le (by positivity)
    linarith
  · rw [hlogabs]
    have h1 : (⌈data.M₁⌉₊ : ℝ) * (⌈data.M₂⌉₊ : ℝ) ≤ (2 * data.M₁) * (2 * data.M₂) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have h2 : (1 : ℝ) ≤ (1 + Real.log X) ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  · intro n
    have h := norm_mtRealIntervalAF_le_of_uniform hprime data.M₁
      ((1 + δ) ^ data.indices.card * data.M₁) ((n : ℕ) + 1)
    rw [pow_zero] at h
    rw [pow_zero, one_mul]
    exact h
  · intro n
    rw [one_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have := norm_mtRealIntervalAF_le_of_uniform hβ data.M₂ (2 * data.M₂) ((n : ℕ) + 1)
    rw [div_le_iff₀ (by linarith)]
    have hd : 0 ≤ ((((n : ℕ) + 1).divisors.card : ℝ) ^ 5) := by positivity
    nlinarith
  · intro n hn
    exact mtTypeIIShortAF_shift_support data hdil hM₁0 n hn
  · intro n hn
    exact mtTypeIILong_shift_support data n hn

/-- The per-scale content of `eventually_typeII_setIntegral_le`: every eventual fact enters as a
hypothesis at the fixed scale `X`. -/
theorem typeII_setIntegral_le_of_scale_facts {a₀ ε εU c η ζ σ₀ T₀ X : ℝ} {A : ℕ}
    (ha₀ : 10999 / 10000 ≤ a₀) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) (hεU : 0 < εU)
    (hεUε : εU ≤ ε) (hηdef : η = ε / 1000) (hζdef : ζ = ε / 1000) (hη : 0 < η) (hζ : 0 ≤ ζ)
    (hσ₀lo : 2298 / 10000 ≤ σ₀) (hσ₀hi : σ₀ ≤ 23 / 100)
    (hP42 : ∀ (T : ℝ) (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ) (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ) (B₁ : ℝ),
      T₀ ≤ T → 1 ≤ N₁ → N₁ ≤ 2 * A₁ → 1 ≤ N₂ → N₂ ≤ 2 * A₂ →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) → T ^ (ε / 2) ≤ (A₁ : ℝ) →
      (A₁ : ℝ) ≤ T ^ ((2 : ℝ) / 11 + 4 * (ε / 6)) →
      T / (16 * (1 + |Real.log T|) ^ 2) ≤ (A₁ : ℝ) * (A₂ : ℝ) →
      (A₁ : ℝ) * (A₂ : ℝ) ≤ T * (16 * (1 + |Real.log T|) ^ 2) →
      (∀ n : Fin N₁, ‖a₁ n‖ ≤ 1 * ((((n : ℕ) + 1).divisors.card : ℝ) ^ 0)) →
      (∀ n : Fin N₂, ‖a₂ n‖ ≤ 1 * ((((n : ℕ) + 1).divisors.card : ℝ) ^ 5)) →
      (∀ n : Fin N₁, a₁ n ≠ 0 → A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∀ n : Fin N₂, a₂ n ≠ 0 → A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∫ t in matomakiTeravainenTypeIIRegion T N₁ a₁ N₂ a₂ A₁ A₂ σ₀ B₁,
          matomakiTeravainenDirichletAmplitude N₁ a₁ t ^ 2 *
            matomakiTeravainenDirichletAmplitude N₂ a₂ t ^ 2)
        ≤ 2 * (16384 * B₁ ^ 2 * (1 + |Real.log T|) * 1 ^ 2 *
              (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (5 + 1)) - 1)
            + T ^ (-((ε / 6) ^ 2 / 20)) + T ^ (-(1 : ℝ) / 2)))
    (hamp : ∀ P : ℝ, Real.log X ^ a₀ ≤ P → P ≤ Real.log X ^ (6 / 5 : ℝ) →
      1 ≤ amplifierDegree X P ∧ X ^ (1 - η) ≤ P ^ amplifierDegree X P ∧
        (P + amplifierDegree X P) ^ amplifierDegree X P ≤ P ^ amplifierDegree X P * X ^ η ∧
        (amplifierDegree X P : ℝ) ≤ Real.log X)
    (hdilX : ∀ {Y z ε : ℝ}
      (data : MTTypeIIPieceData X Y (mtLowerCutoff X) z (mtPaperWidth A X) ε),
      z ≤ X → (1 + mtPaperWidth A X) ^ data.indices.card ≤ 2)
    (hd5 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 5 ≤ X ^ η)
    (hd4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 4 ≤ X ^ η)
    (hB₁X : ∀ {Y z ε : ℝ}
      (data : MTTypeIIPieceData X Y (mtLowerCutoff X) z (mtPaperWidth A X) ε) (t : ℝ),
      z ≤ X → Real.exp (c * (Real.log X) ^ ((1 : ℝ) / 2)) ≤ |t| → |t| ≤ 4 * X →
      ‖mtTypeIIPrimeFactor data 1 t‖ ≤ Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)))
    (hT₀X : T₀ ≤ X) (hz₀ : 2 ≤ mtLowerCutoff X) (hδX : mtPaperWidth A X ≤ 1 / 2)
    (hX8 : 2 ≤ X ^ (ε / 2)) (hX8b : 2 ≤ X ^ (4 * (ε / 6)))
    (hX9 : 4 * (1 + Real.log (24 * X)) ^ 2 ≤ X ^ (9 / 11 : ℝ))
    (hX10 : 2 * (1 + Real.log (24 * X)) ^ 2 ≤ X ^ ζ)
    (hX11 : 3 * (1 + Real.log (24 * X)) ^ 31 ≤ X ^ ζ)
    (habsorb : ∀ B₂ J E₀ : ℝ, 0 ≤ B₂ → B₂ ≤ 3 * (1 + Real.log (24 * X)) ^ 31 →
      0 ≤ J → J ≤ 2 * (1 + Real.log (24 * X)) → E₀ ≤ 8 * X ^ (-(ε / 50)) →
      B₂ ^ 2 * (2 * (16384 * Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)) ^ 2 *
          (1 + |Real.log X|) * 1 ^ 2 * (2 * (1 + |Real.log X|)) ^ (2 ^ (2 * (5 + 1)) - 1) +
          X ^ (-((ε / 6) ^ 2 / 20)) + X ^ (-(1 : ℝ) / 2))) +
        2 * X * (B₂ / X) ^ 2 + J * (typeIICellConstant η * E₀) ≤
          Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)))
    (hX64 : 64 ≤ X) (hlogX : Real.exp 1 ≤ Real.log X)
    (a P : ℝ) (B : Finset ℕ) (ha₀a : a₀ ≤ a) (ha11 : a ≤ 11 / 10)
    (hPa : Real.log X ^ a ≤ P) (hP65 : P ≤ Real.log X ^ (6 / 5 : ℝ))
    (hBiff : ∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) {Y : ℝ}
    (data : MTTypeIIPieceData X Y (mtLowerCutoff X) (X ^ (2 / 11 : ℝ)) (mtPaperWidth A X) ε)
    (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
    (hβ : MTUniformDivisorBounded 5 data.β)
    (hYlo : X / Real.log X ^ 2 ≤ Y) (hYhi : Y ≤ X) (U : Set ℝ) (hU : MeasurableSet U)
    (hUsub : U ⊆ Set.Icc (Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))) X)
    (hS : ∀ t ∈ U, P ^ (-εU / 10) ≤
      ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) :
    ∫ t in U, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
      Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X :=
    le_trans (by have := Real.add_one_le_exp (1 : ℝ); linarith) hlogX
  -- the amplifier
  have ha1 : 1 ≤ a := by linarith
  have hPa₀ : Real.log X ^ a₀ ≤ P :=
    (Real.rpow_le_rpow_of_exponent_le hlog1 ha₀a).trans hPa
  obtain ⟨hk, hlo, hstars, hkL⟩ := hamp P hPa₀ hP65
  have hP1 : 1 ≤ P := le_trans (Real.one_le_rpow hlog1 (by linarith)) hPa
  have hkX := two_mul_pow_amplifierDegree_le hP1 hX1.le
  have hfac : ((amplifierDegree X P).factorial : ℝ) ≤ (P ^ amplifierDegree X P) ^ (1 / a) := by
    apply factorial_le_pow_rpow_inv (by linarith)
    calc (amplifierDegree X P : ℝ) ≤ Real.log X := hkL
      _ = (Real.log X ^ a) ^ (1 / a) := by
          rw [← Real.rpow_mul (by linarith), mul_one_div_cancel (by linarith), Real.rpow_one]
      _ ≤ P ^ (1 / a) := Real.rpow_le_rpow (by positivity) hPa (by positivity)
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => ((hBiff p).1 hp).1
  have hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P := fun p hp => ((hBiff p).1 hp).2
  -- the set `U`
  have hUX : U ⊆ Set.Icc (-X) X := fun t ht =>
    ⟨by linarith [(hUsub ht).1, Real.exp_pos (c * Real.log X ^ ((1 : ℝ) / 2))], (hUsub ht).2⟩
  obtain ⟨hM₁lo, hM₁hi⟩ := data.M₁_mem
  have hzX : X ^ (2 / 11 : ℝ) ≤ X := by
    calc X ^ (2 / 11 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
      _ = X := Real.rpow_one X
  obtain ⟨hM₁2, hM₂2, hM₂X, hM₁X, h2, h3, hB₂, hprodX, hprod4⟩ :=
    typeII_datum_scales data hX64 hlog1 hX8 hX9 hX10 hX11 hYlo hYhi ha1 ha11
  have hdil := hdilX data hzX
  have hF₁1 : ∀ t ∈ U, ‖mtTypeIIPrimeFactor data 1 t‖ ≤ 1 := fun t _ =>
    norm_mtTypeIIPrimeFactor_le_one data hz₀ hδX t
  have hF₁B : ∀ t ∈ U, ‖mtTypeIIPrimeFactor data 1 t‖ ≤
      Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)) := fun t ht => by
    have hexp := Real.exp_pos (c * Real.log X ^ ((1 : ℝ) / 2))
    have ht0 : 0 < t := lt_of_lt_of_le hexp (hUsub ht).1
    refine hB₁X data t hzX ?_ ?_
    · rw [abs_of_pos ht0]; exact (hUsub ht).1
    · rw [abs_of_pos ht0]; linarith [(hUsub ht).2]
  -- scalar facts for the final step
  have hlogM₂ : 0 ≤ Real.log (3 * data.M₂) := Real.log_nonneg (by linarith)
  have hB₂1 : 1 ≤ 3 * (1 + Real.log (3 * data.M₂)) ^ 31 := by
    have : 1 ≤ (1 + Real.log (3 * data.M₂)) ^ 31 := one_le_pow₀ (by linarith)
    linarith
  have hB₂0 : 0 ≤ 3 * (1 + Real.log (3 * data.M₂)) ^ 31 := by linarith
  have hB₂W : 3 * (1 + Real.log (3 * data.M₂)) ^ 31 ≤ 3 * (1 + Real.log (24 * X)) ^ 31 := by
    have hl : Real.log (3 * data.M₂) ≤ Real.log (24 * X) :=
      Real.log_le_log (by positivity) (by linarith)
    gcongr
  have hJW : (((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℕ) : ℝ) ≤ 2 * (1 + Real.log (24 * X)) := by
    have hJ := natLog_two_floor_le hX1.le
    have hLW : Real.log X ≤ Real.log (24 * X) := Real.log_le_log hX0 (by linarith)
    push_cast
    linarith
  have hσε : σ₀ * ε ≤ 23 / 1000000 := by
    have := mul_le_mul hσ₀hi hε1 hε.le (by norm_num : (0 : ℝ) ≤ 23 / 100)
    linarith
  have hσε' : 2298 / 10000 * ε ≤ σ₀ * ε := mul_le_mul_of_nonneg_right hσ₀lo hε.le
  have h6a : 6 / a ≤ 6 / (10999 / 10000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have m2 : σ₀ * ε ≤ 1 / 2000 := by linarith
  have m3 : 6 / a - 5 - 2 * σ₀ + 5 * (1 / 2000) + 8 * ζ ≤ -(σ₀ * ε) := by
    rw [hζdef]; norm_num at h6a ⊢; linarith
  have hE₀ : X ^ (εU / 5 + 6 * η) * (8 * X ^ (-(σ₀ * ε))) ≤ 8 * X ^ (-(ε / 50)) := by
    have hexp : εU / 5 + 6 * η + -(σ₀ * ε) ≤ -(ε / 50) := by
      rw [hηdef]; linarith
    calc X ^ (εU / 5 + 6 * η) * (8 * X ^ (-(σ₀ * ε)))
        = 8 * X ^ (εU / 5 + 6 * η + -(σ₀ * ε)) := by
          rw [Real.rpow_add hX0 (εU / 5 + 6 * η) (-(σ₀ * ε))]; ring
      _ ≤ 8 * X ^ (-(ε / 50)) := by
          have := Real.rpow_le_rpow_of_exponent_le hX1.le hexp
          linarith
  have ha43 : a ≤ 4 / 3 := by linarith
  have hη1 : η ≤ 1 := by rw [hηdef]; linarith
  have hσ₀0 : 0 ≤ σ₀ := by linarith
  have hσ₀h : σ₀ ≤ 1 / 2 := by linarith
  have hmain := setIntegral_typeII_le_of_region data hprime hβ hBp hP1 hB hk hkX hlo hstars hfac
    ha1 ha43 hη hη1 hεU.le hU hUX hS hM₁2 hM₂2 hdil hM₂X hM₁X hX64 hd5 hd4 hM₁lo h2 h3 hB₂ hσ₀0
    hσ₀h hζ (le_refl (σ₀ * ε)) m2 m3 hF₁1 hF₁B
    (typeII_region_integral_le (σ₀ := σ₀) (B₁ := Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)))
      hP42 hT₀X data hprime hβ hdil hX1 hlog1 hX8b hM₁2 hM₂2 hprodX hprod4 hB₂1)
  refine hmain.trans ?_
  rw [mul_assoc (typeIICellConstant η)]
  exact habsorb _ _ _ hB₂0 hB₂W (Nat.cast_nonneg _) hJW hE₀


/-- **Matomäki–Teräväinen (5.3) for Type-II pieces**, uniformly in `a ∈ [a₀, 11/10]` with
`a₀ ≥ 1.0999`: on any measurable `U ⊆ [exp(c√log X), X]` where the prime polynomial on
`(P, 2P]`, `P ∈ [(log X)^a, (log X)^{6/5}]`, is `≥ P^{-ε_U/10}`, the mean square of a uniform
Type-II piece is `≤ exp(-(log X)^{1/40})`. -/
theorem eventually_typeII_setIntegral_le {a₀ ε εU c : ℝ} {A : ℕ} (hA : 1 ≤ A)
    (ha₀ : 10999 / 10000 ≤ a₀) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) (hεU : 0 < εU)
    (hεUε : εU ≤ ε) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ (a P : ℝ) (B : Finset ℕ), a₀ ≤ a → a ≤ 11 / 10 →
      Real.log X ^ a ≤ P → P ≤ Real.log X ^ (6 / 5 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ {Y : ℝ} (data : MTTypeIIPieceData X Y (mtLowerCutoff X) (X ^ (2 / 11 : ℝ))
          (mtPaperWidth A X) ε),
      MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block) →
      MTUniformDivisorBounded 5 data.β →
      X / Real.log X ^ 2 ≤ Y → Y ≤ X →
      ∀ U : Set ℝ, MeasurableSet U →
        U ⊆ Set.Icc (Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))) X →
        (∀ t ∈ U, P ^ (-εU / 10) ≤
          ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
        ∫ t in U, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
          Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / 1000 := ⟨_, rfl⟩
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = ε / 1000 := ⟨_, rfl⟩
  obtain ⟨σ₀, hσ₀def⟩ : ∃ σ₀ : ℝ, σ₀ = 23 / 100 - 5 * (ε / 6) - ε - (ε / 6) ^ 2 / 20 :=
    ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hζ : 0 ≤ ζ := by rw [hζdef]; positivity
  have hσ₀lo : 2298 / 10000 ≤ σ₀ := by rw [hσ₀def]; nlinarith
  have hσ₀hi : σ₀ ≤ 23 / 100 := by rw [hσ₀def]; nlinarith
  obtain ⟨T₀, -, hP42⟩ := exists_matomakiTeravainen_typeII_proposition42_integral
    (eps := ε / 6) (mu := ε / 2) (eta := ε) (sigma₀ := σ₀) (Cprod := 16) (C₁ := 1) (C₂ := 1)
    (by positivity) (by linarith) (by positivity) (by linarith) (by linarith) hε
    (by rw [hσ₀def]; linarith) (by norm_num) le_rfl le_rfl 2 0 5
  have hcut : ∀ᶠ X : ℝ in atTop, 2 ≤ mtLowerCutoff X := by
    filter_upwards [tendsto_mtLowerLogCutoff_atTop.eventually_ge_atTop 1] with X hX
    rw [mtLowerCutoff]
    have := Real.add_one_le_exp (mtLowerLogCutoff X)
    linarith
  have hwidth : ∀ᶠ X : ℝ in atTop, mtPaperWidth A X ≤ 1 / 2 := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2] with X hX
    rw [mtPaperWidth, Real.rpow_neg (by linarith), Real.rpow_natCast]
    have h1 : (2 : ℝ) ≤ Real.log X ^ (10 * A) := by
      calc (2 : ℝ) ≤ Real.log X := hX
        _ = Real.log X ^ 1 := (pow_one _).symm
        _ ≤ Real.log X ^ (10 * A) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  filter_upwards [eventually_amplifier_scale (a₀ := a₀) (by linarith) hη,
    eventually_one_add_mtPaperWidth_pow_card_le_two hA,
    eventually_card_divisors_pow_le_rpow 5 hη, eventually_card_divisors_pow_le_rpow 4 hη,
    eventually_norm_mtTypeIIPrimeFactor_le hc hA, eventually_ge_atTop T₀, hcut, hwidth,
    (tendsto_rpow_atTop (by positivity : 0 < ε / 2)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (by positivity : 0 < 4 * (ε / 6))).eventually_ge_atTop 2,
    eventually_polylog_le_rpow 2 (C := 4) (κ := 9 / 11) (by norm_num) (by norm_num),
    eventually_polylog_le_rpow 2 (C := 2) (κ := ζ) (by norm_num) (by rw [hζdef]; positivity),
    eventually_polylog_le_rpow 31 (C := 3) (κ := ζ) (by norm_num) (by rw [hζdef]; positivity),
    eventually_typeII_four_terms_le (K := typeIICellConstant η) (κ := (ε / 6) ^ 2 / 20)
      (ε' := ε / 50) (typeIICellConstant_nonneg η) (by positivity) (by nlinarith) (by positivity),
    eventually_ge_atTop (64 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)]
    with X hamp hdilX hd5 hd4 hB₁X hT₀X hz₀ hδX hX8 hX8b hX9 hX10 hX11 habsorb hX64 hlogX
  intro a P B ha₀a ha11 hPa hP65 hBiff Y data hprime hβ hYlo hYhi U hU hUsub hS
  exact typeII_setIntegral_le_of_scale_facts ha₀ hε hε1 hεU hεUε hηdef hζdef hη hζ hσ₀lo hσ₀hi
    hP42 hamp hdilX hd5 hd4 hB₁X hT₀X hz₀ hδX hX8 hX8b hX9 hX10 hX11 habsorb hX64 hlogX a P B ha₀a
    ha11 hPa hP65 hBiff data hprime hβ hYlo hYhi U hU hUsub hS

end

end RHTower.Sieve
