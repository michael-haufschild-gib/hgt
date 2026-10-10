import GaloisForLFunctions.RHTower.MoebiusAbelSmoothedSaving
import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.RectangleResidue
import GaloisForLFunctions.RHTower.DualDiagonalMellin
import GaloisForLFunctions.RHTower.KFreeExponentialMellin
import GaloisForLFunctions.HTGeometry.TwistedMobiusLambertWittSeries

/-!
# The Abel-smoothed `k`-free count below the Vinogradov–Korobov height

For `k ≥ 2` and `0 < t < 1` let `S_k(t) = Σ_{n k-free} e^{-nt}`. Its Perron integrand is
`t^{-s} Γ(s) ζ(s)/ζ(ks)`. The integrand has one pole in `Re s > 1/(2k)`, at `s = 1` with residue
`1/(ζ(k) t)`, and `Γζ` decays like `e^{-|Im s|/4}` off that pole (`exists_norm_Gamma_mul_zeta_le`).
Shifting the line `Re s = 2` to `Re s = (1 - m/4)/k` below the height `K ≍ log(1/t)` uses the
Vinogradov–Korobov zero-free region of `ζ(ks)` at height `kK`.

**Theorem** (`exists_norm_kFreeExp_sub_le`). With `K = 24 log(1/t)`,
`m = min(δ, w(kK+1))` and `w = vkHadamardWidth`,

`‖S_k(t) - 1/(ζ(k) t)‖ ≤ C (1+K) L(kK) t^{-(1 - m/4)/k}`,

where `L(T) = log(T+1)⁷ (1 + 2/w(T+1))⁷`. This is a near-power saving over the trivial exponent
`1/k` of the smoothed `k`-free count, the quantity of the quasi-RH ladder.
-/

open Complex MeasureTheory Filter Topology

namespace RHTower.KFreeAbel

noncomputable section

/-! ## Envelopes -/

/-- `Γ` is bounded by `A e^{-|t|/2}` on `a ≤ Re s ≤ 2`, for every `a > 0`. -/
theorem exists_norm_Gamma_le_exp_half_of_pos {a : ℝ} (ha : 0 < a) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ 2 →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.exp (-(|t| / 2)) := by
  obtain ⟨C, N, hC, hdec⟩ := GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip ha 2
  set Kc : Set ℂ := {z | a ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1} with hKc
  have hKcc : IsCompact Kc := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hc : IsClosed ({z : ℂ | a ≤ z.re} ∩ {z | z.re ≤ 2} ∩ {z | |z.im| ≤ 1}) :=
        ((isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const)).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
      convert hc using 1
      ext z
      simp only [hKc, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + 3)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ |a| + 3 := by
            have : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.1⟩
            linarith [hz.2.2, abs_nonneg a]
  have hcont : ContinuousOn Complex.Gamma Kc := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z fun m hm => ?_).continuousAt.continuousWithinAt
    have hre := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hz.1]
  obtain ⟨G₀, hG₀⟩ := hKcc.exists_bound_of_continuousOn hcont
  refine ⟨max (C * N.factorial) (max G₀ 0 * Real.exp (1 / 2)), le_max_of_le_right
    (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le), fun σ t hσ1 hσ2 => ?_⟩
  rcases le_or_gt 1 |t| with ht | ht
  · have h := hdec σ t hσ1 hσ2 ht
    have hpow : |t| ^ N ≤ N.factorial * Real.exp |t| := by
      have := Real.pow_div_factorial_le_exp |t| (abs_nonneg t) N
      rw [div_le_iff₀ (by exact_mod_cast N.factorial_pos)] at this
      linarith
    have hexp : Real.exp |t| * Real.exp (-(Real.pi * |t| / 2)) ≤ Real.exp (-(|t| / 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, abs_nonneg t])
    calc ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := h
      _ ≤ C * (N.factorial * Real.exp |t|) * Real.exp (-(Real.pi * |t| / 2)) := by gcongr
      _ = C * N.factorial * (Real.exp |t| * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ C * N.factorial * Real.exp (-(|t| / 2)) := by gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hz : ((σ : ℂ) + (t : ℂ) * I) ∈ Kc := by
      refine ⟨by simpa using hσ1, by simpa using hσ2, ?_⟩
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      exact ht.le
    have h := hG₀ _ hz
    have hexp : 1 ≤ Real.exp (1 / 2) * Real.exp (-(|t| / 2)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max G₀ 0 := h.trans (le_max_left _ _)
      _ ≤ max G₀ 0 * (Real.exp (1 / 2) * Real.exp (-(|t| / 2))) :=
          le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = max G₀ 0 * Real.exp (1 / 2) * Real.exp (-(|t| / 2)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- `y^N e^{-y/2} ≤ N! 4^N e^{-y/4}` for `y ≥ 0`. -/
theorem pow_mul_exp_neg_half_le {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    y ^ N * Real.exp (-(y / 2)) ≤ N.factorial * 4 ^ N * Real.exp (-(y / 4)) := by
  have h := Real.pow_div_factorial_le_exp (y / 4) (by positivity) N
  rw [div_le_iff₀ (by exact_mod_cast N.factorial_pos), div_pow] at h
  have h4 : y ^ N = 4 ^ N * (y ^ N / 4 ^ N) := by field_simp
  have hexp : Real.exp (y / 4) * Real.exp (-(y / 2)) = Real.exp (-(y / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc y ^ N * Real.exp (-(y / 2)) = 4 ^ N * (y ^ N / 4 ^ N) * Real.exp (-(y / 2)) := by
        rw [← h4]
    _ ≤ 4 ^ N * (Real.exp (y / 4) * N.factorial) * Real.exp (-(y / 2)) := by gcongr
    _ = N.factorial * 4 ^ N * (Real.exp (y / 4) * Real.exp (-(y / 2))) := by ring
    _ = _ := by rw [hexp]

/-- **The `Γζ` envelope off the pole.** On `a ≤ Re s ≤ 2`, away from the box
`|Im s| < 1, 3/4 < Re s < 3/2`, `‖Γ(s)ζ(s)‖ ≤ A e^{-|Im s|/4}`. -/
theorem exists_norm_Gamma_mul_zeta_le {a : ℝ} (ha : 0 < a) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |t| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I) * riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ A * Real.exp (-(|t| / 4)) := by
  obtain ⟨A₁, hA₁, hΓ⟩ := exists_norm_Gamma_le_exp_half_of_pos ha
  obtain ⟨Cz, N, hCz, hz⟩ := RHTower.exists_bound_norm_riemannZeta_strip 2
  set Kc : Set ℂ := {z | a ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1 ∧ (z.re ≤ 3 / 4 ∨ 3 / 2 ≤ z.re)}
    with hKc
  have hKcc : IsCompact Kc := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hc : IsClosed ({z : ℂ | a ≤ z.re} ∩ {z | z.re ≤ 2} ∩ {z | |z.im| ≤ 1} ∩
          ({z | z.re ≤ 3 / 4} ∪ {z | 3 / 2 ≤ z.re})) :=
        (((isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const)).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)).inter
          ((isClosed_le Complex.continuous_re continuous_const).union
            (isClosed_le continuous_const Complex.continuous_re))
      convert hc using 1
      ext z
      simp only [hKc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, and_assoc]
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + 3)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ |a| + 3 := by
            have : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.1⟩
            linarith [hz.2.2.1, abs_nonneg a]
  have hcont : ContinuousOn (fun z => Complex.Gamma z * riemannZeta z) Kc := by
    intro z hz
    have hne1 : z ≠ 1 := by
      intro h
      rcases hz.2.2.2 with h' | h' <;> rw [h, one_re] at h' <;> norm_num at h'
    have hG : DifferentiableAt ℂ Complex.Gamma z := by
      refine Complex.differentiableAt_Gamma z fun m hm => ?_
      have hre := congrArg Complex.re hm
      simp only [neg_re, natCast_re] at hre
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith [hz.1]
    exact (hG.continuousAt.mul (differentiableAt_riemannZeta hne1).continuousAt).continuousWithinAt
  obtain ⟨G₀, hG₀⟩ := hKcc.exists_bound_of_continuousOn hcont
  refine ⟨max (A₁ * Cz * N.factorial * 4 ^ N) (max G₀ 0 * Real.exp (1 / 4)),
    le_max_of_le_right (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le),
    fun σ t hσ1 hσ2 hcase => ?_⟩
  rcases le_or_gt 1 |t| with ht | ht
  · have hg := hΓ σ t hσ1 hσ2
    have hzt := hz σ t (abs_le.mpr ⟨by linarith, hσ2⟩) ht
    have hpe := pow_mul_exp_neg_half_le (abs_nonneg t) N
    rw [norm_mul]
    calc ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I)‖ * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ (A₁ * Real.exp (-(|t| / 2))) * (Cz * |t| ^ N) := by
          gcongr
      _ = A₁ * Cz * (|t| ^ N * Real.exp (-(|t| / 2))) := by ring
      _ ≤ A₁ * Cz * (N.factorial * 4 ^ N * Real.exp (-(|t| / 4))) := by gcongr
      _ = A₁ * Cz * N.factorial * 4 ^ N * Real.exp (-(|t| / 4)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hcase' : σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ := by
      rcases hcase with h | h
      · exact absurd h (not_le.mpr ht)
      · exact h
    have hzK : ((σ : ℂ) + (t : ℂ) * I) ∈ Kc := by
      refine ⟨by simpa using hσ1, by simpa using hσ2, ?_, by simpa using hcase'⟩
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      exact ht.le
    have h := hG₀ _ hzK
    have hexp : 1 ≤ Real.exp (1 / 4) * Real.exp (-(|t| / 4)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * I) * riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ max G₀ 0 := h.trans (le_max_left _ _)
      _ ≤ max G₀ 0 * (Real.exp (1 / 4) * Real.exp (-(|t| / 4))) :=
          le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = max G₀ 0 * Real.exp (1 / 4) * Real.exp (-(|t| / 4)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-! ## The integrand and the inversion formula -/

/-- `t^{-s} Γ(s) ζ(s)/ζ(ks)`. -/
def kFreeAbelIntegrand (k : ℕ) (t : ℝ) (s : ℂ) : ℂ :=
  (t : ℂ) ^ (-s) * (Complex.Gamma s * riemannZeta s * Sieve.invZeta ((k : ℂ) * s))

/-- The smoothed `k`-free count `Σ_{n k-free} e^{-nt}`. -/
def kFreeExp (k : ℕ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, ((mFreeIndicator k n : ℤ) : ℂ) * Complex.exp (-(((n : ℝ) * t : ℝ) : ℂ))

/-- **Exponentially smoothed Perron inversion for the `k`-free indicator.** -/
theorem kFreeExp_eq_integral {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    kFreeExp k t = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ y : ℝ, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hk0 : k ≠ 0 := by omega
  have hbd : ∀ n : ℕ, ‖((mFreeIndicator k n : ℤ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_intCast, mFreeIndicator_apply]
    split_ifs <;> norm_num
  have hsum : Summable (fun n : ℕ =>
      ‖((mFreeIndicator k n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-(2 : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (fun n => ?_)
      (Real.summable_nat_rpow.mpr (by norm_num : (-(2 : ℝ)) < -1))
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    nlinarith [hbd n]
  have h := mellinInv_gamma_mul_LSeries_eq_tsum_exp (a := fun n : ℕ =>
    ((mFreeIndicator k n : ℤ) : ℂ)) (c := 2) (by norm_num) (by simp) hsum ht
  rw [kFreeExp, ← h, mellinInv]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ,
      kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)
      = (1 / (2 * Real.pi) : ℝ) • ∫ y : ℝ,
          kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I) from (Complex.real_smul).symm]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hre : 1 < (((2 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp
  have hkre : 1 < ((k : ℂ) * (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
    simp only [mul_re, natCast_re, natCast_im, add_re, ofReal_re, ofReal_im, I_re,
      I_im, zero_mul, sub_zero, mul_zero, add_zero, mul_one]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hne : (k : ℂ) * (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro h1
    rw [h1, one_re] at hkre
    exact lt_irrefl _ hkre
  simp only [kFreeAbelIntegrand, smul_eq_mul]
  have hL : LSeries (fun n : ℕ => ((mFreeIndicator k n : ℤ) : ℂ))
      (((2 : ℝ) : ℂ) + (y : ℂ) * I) = riemannZeta (((2 : ℝ) : ℂ) + (y : ℂ) * I) /
        riemannZeta ((k : ℂ) * (((2 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    LSeries_mFree_eq_riemannZeta_div hk0 hre
  rw [hL, Sieve.invZeta_eq_inv hne, div_eq_mul_inv]
  ring

/-! ## Truncation and the residue rectangle -/

/-- The part of a line integral above height `K`, for an envelope `B e^{-r|t|}`. -/
theorem norm_integral_sub_intervalIntegral_le_rate {g : ℝ → ℂ} (hg : Integrable g) {B K r : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hB : 0 ≤ B) (hbd : ∀ t, ‖g t‖ ≤ B * Real.exp (-(r * |t|))) :
    ‖(∫ t, g t) - ∫ t in (-K)..K, g t‖
      ≤ B * Real.exp (-(r * K / 2)) * ∫ t : ℝ, Real.exp (-((r / 2) * |t|)) := by
  have hS : MeasurableSet (Set.Ioc (-K) K) := measurableSet_Ioc
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_add_compl hS hg,
    add_sub_cancel_left]
  have hint : Integrable (fun t : ℝ => B * Real.exp (-(r * K / 2)) * Real.exp (-((r / 2) * |t|))) :=
    (RHTower.integrable_exp_neg_mul_abs' (by linarith)).const_mul _
  have hpt : ∀ t ∈ (Set.Ioc (-K) K)ᶜ,
      ‖g t‖ ≤ B * Real.exp (-(r * K / 2)) * Real.exp (-((r / 2) * |t|)) := by
    intro t ht
    have hKt : K ≤ |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h.le
    calc ‖g t‖ ≤ B * Real.exp (-(r * |t|)) := hbd t
      _ = B * (Real.exp (-(r * |t| / 2)) * Real.exp (-((r / 2) * |t|))) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ B * (Real.exp (-(r * K / 2)) * Real.exp (-((r / 2) * |t|))) := by
          gcongr
      _ = _ := by ring
  calc ‖∫ t in (Set.Ioc (-K) K)ᶜ, g t‖
      ≤ ∫ t in (Set.Ioc (-K) K)ᶜ, B * Real.exp (-(r * K / 2)) * Real.exp (-((r / 2) * |t|)) :=
        norm_integral_le_of_norm_le hint.integrableOn
          ((ae_restrict_iff' hS.compl).mpr (Eventually.of_forall hpt))
    _ ≤ ∫ t : ℝ, B * Real.exp (-(r * K / 2)) * Real.exp (-((r / 2) * |t|)) :=
        setIntegral_le_integral hint (Eventually.of_forall fun t => by positivity)
    _ = _ := integral_const_mul _ _

/-- **The residue rectangle.** If `F = Φ/(s-1)` off `1` with `Φ` holomorphic on an open set
containing the rectangle `[c, 2] × [-K, K]` and `1`, then moving the line `Re s = 2` to `Re s = c`
picks up `2π Φ(1)` and the two horizontal edges. -/
theorem norm_intervalIntegral_two_sub_residue_le {F Φ : ℂ → ℂ} {c K : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) (h1 : (1 : ℂ) ∈ U)
    (hsub : Set.uIcc c 2 ×ℂ Set.uIcc (-K) K ⊆ U) (hc1 : c < 1) (hK : 0 < K)
    (hF : ∀ z : ℂ, z ≠ 1 → F z = Φ z / (z - 1)) :
    ‖(∫ y in (-K)..K, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)) - 2 * Real.pi * Φ 1‖
      ≤ ‖∫ y in (-K)..K, F ((c : ℂ) + (y : ℂ) * I)‖
        + ‖∫ σ in c..2, F ((σ : ℂ) + ((-K : ℝ) : ℂ) * I)‖
        + ‖∫ σ in c..2, F ((σ : ℂ) + (K : ℂ) * I)‖ := by
  have hR : AnalyticOnNhd ℂ (dslope Φ 1) U :=
    ((Complex.differentiableOn_dslope (hU.mem_nhds h1)).mpr hΦ).analyticOnNhd hU
  have hres := RHTower.rectIntegral_eq_two_pole_residues_of_analyticOnNhd (F := F)
    (R := dslope Φ 1) (p := 1) (q := 1 + ((K / 2 : ℝ) : ℂ) * I) (rp := Φ 1) (rq := 0)
    (z₁ := ⟨c, -K⟩) (z₂ := ⟨2, K⟩) (U := U) hsub
    (by simpa using hc1) (by norm_num) (by simp; linarith) (by simp; linarith)
    (by simpa using hc1) (by norm_num) (by simp; linarith) (by simp; linarith) hR
    (fun z hz _ => by
      rw [hF z hz, dslope_of_ne _ hz, slope_def_field]
      have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      field_simp
      ring)
  rw [add_zero] at hres
  unfold RHTower.rectIntegral at hres
  simp only at hres
  set R := ∫ y in (-K)..K, F (((2 : ℝ) : ℂ) + (y : ℂ) * I)
  set L := ∫ y in (-K)..K, F ((c : ℂ) + (y : ℂ) * I)
  set Bt := ∫ σ in c..2, F ((σ : ℂ) + ((-K : ℝ) : ℂ) * I)
  set Tp := ∫ σ in c..2, F ((σ : ℂ) + (K : ℂ) * I)
  have hR' : R - 2 * Real.pi * Φ 1 = L + I * (Bt - Tp) := by
    have h : Bt - Tp + I • R - I • L = 2 * Real.pi * I * Φ 1 := hres
    simp only [smul_eq_mul] at h
    have hI2 : I * I = -1 := Complex.I_mul_I
    linear_combination (-I) * h + (R - L - 2 * (Real.pi : ℂ) * Φ 1) * hI2
  rw [hR']
  calc ‖L + I * (Bt - Tp)‖ ≤ ‖L‖ + ‖I * (Bt - Tp)‖ := norm_add_le _ _
    _ ≤ ‖L‖ + (‖Bt‖ + ‖Tp‖) := by
        gcongr
        rw [norm_mul, norm_I, one_mul]
        exact norm_sub_le _ _
    _ = _ := by ring

/-! ## The pole factor -/

/-- `t^{-s} Γ(s) (s-1)ζ(s) ζ(ks)^{-1}`, holomorphic across `s = 1`. -/
def kFreeAbelPoleFactor (k : ℕ) (t : ℝ) (s : ℂ) : ℂ :=
  (t : ℂ) ^ (-s) * (Complex.Gamma s * RHTower.zetaResidueUnit s * Sieve.invZeta ((k : ℂ) * s))

theorem kFreeAbelIntegrand_eq_div {k : ℕ} {t : ℝ} {z : ℂ} (hz : z ≠ 1) :
    kFreeAbelIntegrand k t z = kFreeAbelPoleFactor k t z / (z - 1) := by
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hu : RHTower.zetaResidueUnit z = (z - 1) * riemannZeta z := by
    simp [RHTower.zetaResidueUnit, Function.update_of_ne hz]
  rw [kFreeAbelIntegrand, kFreeAbelPoleFactor, hu]
  field_simp

theorem kFreeAbelPoleFactor_one {k : ℕ} (hk : 2 ≤ k) {t : ℝ} :
    kFreeAbelPoleFactor k t 1 = (t : ℂ) ^ (-(1 : ℂ)) * (riemannZeta (k : ℂ))⁻¹ := by
  have hk1 : (k : ℂ) ≠ 1 := by
    intro h
    have : (k : ℝ) = 1 := by exact_mod_cast h
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [kFreeAbelPoleFactor, RHTower.zetaResidueUnit_one, Complex.Gamma_one, mul_one, mul_one,
    one_mul, Sieve.invZeta_eq_inv hk1]

/-- The open set where the pole factor is holomorphic. -/
def kFreeAbelDomain (k : ℕ) : Set ℂ :=
  {z | 0 < z.re ∧ RHTower.zetaResidueUnit ((k : ℂ) * z) ≠ 0}

theorem isOpen_kFreeAbelDomain (k : ℕ) : IsOpen (kFreeAbelDomain k) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_ne_fun (Sieve.continuous_zetaResidueUnit.comp (continuous_const.mul continuous_id))
      continuous_const)

theorem differentiableOn_kFreeAbelPoleFactor (k : ℕ) {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (kFreeAbelPoleFactor k t) (kFreeAbelDomain k) := by
  intro z hz
  have hG : DifferentiableAt ℂ Complex.Gamma z := by
    refine Complex.differentiableAt_Gamma z fun m hm => ?_
    have hre := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hz.1]
  have hP : DifferentiableAt ℂ (fun w : ℂ => (t : ℂ) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr ht.ne'))
  have hU : DifferentiableAt ℂ RHTower.zetaResidueUnit z :=
    (RHTower.analyticAt_zetaResidueUnit z).differentiableAt
  have hI : DifferentiableAt ℂ (fun w : ℂ => Sieve.invZeta ((k : ℂ) * w)) z :=
    (Sieve.differentiableAt_invZeta hz.2).comp z (differentiableAt_id.const_mul _)
  exact (hP.mul ((hG.mul hU).mul hI)).differentiableWithinAt

theorem one_mem_kFreeAbelDomain {k : ℕ} (hk : 2 ≤ k) : (1 : ℂ) ∈ kFreeAbelDomain k := by
  refine ⟨by simp, ?_⟩
  have hk1 : (k : ℂ) * 1 ≠ 1 := by
    rw [mul_one]
    intro h
    have : (k : ℝ) = 1 := by exact_mod_cast h
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hre : 1 < ((k : ℂ) * 1).re := by
    simp only [mul_one, natCast_re]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  simp only [RHTower.zetaResidueUnit, Function.update_of_ne hk1]
  exact mul_ne_zero (sub_ne_zero.mpr hk1) (riemannZeta_ne_zero_of_one_lt_re hre)

/-- The rectangle lies in the domain once `ζ(ks)` is zero-free on its image. -/
theorem rect_subset_kFreeAbelDomain {k : ℕ} (hk : 2 ≤ k) {c K : ℝ} (hc : 0 < c) (hc2 : c ≤ 2)
    (hK0 : 0 ≤ K) (hzf : ∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w ≠ 1 → riemannZeta w ≠ 0) :
    Set.uIcc c 2 ×ℂ Set.uIcc (-K) K ⊆ kFreeAbelDomain k := by
  intro s hs
  obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
  rw [Set.uIcc_of_le hc2] at hre
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  rw [Set.uIcc_of_le (by linarith)] at him
  refine ⟨by linarith [hre.1], ?_⟩
  by_cases h1 : (k : ℂ) * s = 1
  · rw [h1, RHTower.zetaResidueUnit_one]; exact one_ne_zero
  · simp only [RHTower.zetaResidueUnit, Function.update_of_ne h1]
    refine mul_ne_zero (sub_ne_zero.mpr h1) (hzf _ ?_ ?_ h1)
    · simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]
      rw [abs_mul, abs_of_pos hk0]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨him.1, him.2⟩) hk0.le
    · simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_left hre.1 hk0.le

/-! ## Edge bounds -/

theorem norm_kFreeAbelIntegrand {k : ℕ} {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖kFreeAbelIntegrand k t s‖ = t ^ (-s.re) *
      (‖Complex.Gamma s * riemannZeta s‖ * ‖Sieve.invZeta ((k : ℂ) * s)‖) := by
  rw [kFreeAbelIntegrand, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, neg_re]

theorem kmul_re_im (k : ℕ) (σ y : ℝ) :
    ((k : ℂ) * ((σ : ℂ) + (y : ℂ) * I)).re = k * σ ∧
      ((k : ℂ) * ((σ : ℂ) + (y : ℂ) * I)).im = k * y := by
  constructor <;> simp

/-- The left edge `Re s = c`. -/
theorem norm_kFree_left_edge_le {k : ℕ} (hk : 2 ≤ k) {t a c K A V : ℝ} (ht : 0 < t)
    (hca : a ≤ c) (hc34 : c ≤ 3 / 4) (hkc : k * c ≤ 2) (hK0 : 0 ≤ K) (hA : 0 ≤ A)
    (hΓζ : ∀ σ y : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |y| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) →
      ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖
        ≤ A * Real.exp (-(|y| / 4)))
    (hinvV : ∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w.re ≤ 2 → ‖Sieve.invZeta w‖ ≤ V) :
    ‖∫ y in (-K)..K, kFreeAbelIntegrand k t ((c : ℂ) + (y : ℂ) * I)‖
      ≤ t ^ (-c) * A * V * (2 * K) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpt : ∀ y ∈ Set.uIoc (-K) K,
      ‖kFreeAbelIntegrand k t ((c : ℂ) + (y : ℂ) * I)‖ ≤ t ^ (-c) * A * V := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith)] at hy
    have hyK : |y| ≤ K := abs_le.mpr ⟨hy.1.le, hy.2⟩
    have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
    rw [norm_kFreeAbelIntegrand ht, hre]
    obtain ⟨hwre, hwim⟩ := kmul_re_im k c y
    have hiv := hinvV _ (by rw [hwim, abs_mul, abs_of_nonneg hk0]; gcongr)
      (by rw [hwre]) (by rw [hwre]; exact hkc)
    have he : Real.exp (-(|y| / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := abs_nonneg y; linarith)
    have hg := (hΓζ c y hca (by linarith) (Or.inr (Or.inl hc34))).trans
      (mul_le_of_le_one_right hA he)
    have hxp : 0 ≤ t ^ (-c) := Real.rpow_nonneg ht.le _
    calc t ^ (-c) * (‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I) * riemannZeta ((c : ℂ) + (y : ℂ) * I)‖
          * ‖Sieve.invZeta ((k : ℂ) * ((c : ℂ) + (y : ℂ) * I))‖)
        ≤ t ^ (-c) * (A * V) := by gcongr
      _ = t ^ (-c) * A * V := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans (le_of_eq ?_)
  rw [show K - -K = 2 * K by ring, abs_of_nonneg (by linarith)]

/-- A horizontal edge `Im s = y`, `|y| = K ≥ 1`. -/
theorem norm_kFree_horizontal_edge_le {k : ℕ} (hk : 2 ≤ k) {t a c K A V Bz y : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hca : a ≤ c) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) (hK1 : 1 ≤ K)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hBz : 0 ≤ Bz) (hy : |y| = K)
    (hΓζ : ∀ σ y : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |y| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) →
      ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖
        ≤ A * Real.exp (-(|y| / 4)))
    (hinvV : ∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w.re ≤ 2 → ‖Sieve.invZeta w‖ ≤ V)
    (hz : ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re → ‖(riemannZeta s)⁻¹‖ ≤ Bz) :
    ‖∫ σ in c..2, kFreeAbelIntegrand k t ((σ : ℂ) + (y : ℂ) * I)‖
      ≤ t ^ (-(2 : ℝ)) * A * Real.exp (-(K / 4)) * (V + Bz) * 2 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpt : ∀ σ ∈ Set.uIoc c 2, ‖kFreeAbelIntegrand k t ((σ : ℂ) + (y : ℂ) * I)‖
      ≤ t ^ (-(2 : ℝ)) * A * Real.exp (-(K / 4)) * (V + Bz) := by
    intro σ hσ
    rw [Set.uIoc_of_le hc2] at hσ
    have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
    rw [norm_kFreeAbelIntegrand ht, hre]
    have hg := hΓζ σ y (by linarith [hσ.1]) hσ.2 (Or.inl (by rw [hy]; exact hK1))
    rw [hy] at hg
    obtain ⟨hwre, hwim⟩ := kmul_re_im k σ y
    have hiv : ‖Sieve.invZeta ((k : ℂ) * ((σ : ℂ) + (y : ℂ) * I))‖ ≤ V + Bz := by
      by_cases h2 : k * σ ≤ 2
      · have := hinvV _ (by rw [hwim, abs_mul, abs_of_nonneg hk0, hy])
          (by rw [hwre]; exact mul_le_mul_of_nonneg_left hσ.1.le hk0) (by rw [hwre]; exact h2)
        linarith
      · push Not at h2
        have hne : (k : ℂ) * ((σ : ℂ) + (y : ℂ) * I) ≠ 1 := by
          intro h1
          have := congrArg Complex.re h1
          rw [hwre, one_re] at this
          linarith
        rw [Sieve.invZeta_eq_inv hne]
        have := hz _ (by rw [hwre]; linarith)
        linarith
    have hxs : t ^ (-σ) ≤ t ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1.le (by linarith [hσ.2])
    have hxp : 0 ≤ t ^ (-σ) := Real.rpow_nonneg ht.le _
    calc t ^ (-σ) * (‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖
          * ‖Sieve.invZeta ((k : ℂ) * ((σ : ℂ) + (y : ℂ) * I))‖)
        ≤ t ^ (-(2 : ℝ)) * ((A * Real.exp (-(K / 4))) * (V + Bz)) := by
          gcongr
      _ = t ^ (-(2 : ℝ)) * A * Real.exp (-(K / 4)) * (V + Bz) := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
  have hpos : 0 ≤ t ^ (-(2 : ℝ)) * A * Real.exp (-(K / 4)) * (V + Bz) := by positivity
  rw [abs_of_nonneg (by linarith)]
  exact mul_le_mul_of_nonneg_left (by linarith) hpos

/-- The line `Re s = 2`. -/
theorem norm_kFree_line_le {k : ℕ} (hk : 2 ≤ k) {t a A Bz : ℝ} (ht : 0 < t) (ha2 : a ≤ 2)
    (hΓζ : ∀ σ y : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |y| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) →
      ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖
        ≤ A * Real.exp (-(|y| / 4)))
    (hz : ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re → ‖(riemannZeta s)⁻¹‖ ≤ Bz) (y : ℝ) :
    ‖kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ t ^ (-(2 : ℝ)) * A * Bz * Real.exp (-((1 / 4 : ℝ) * |y|)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hre : (((2 : ℝ) : ℂ) + (y : ℂ) * I).re = 2 := by simp
  rw [norm_kFreeAbelIntegrand ht, hre]
  obtain ⟨hwre, -⟩ := kmul_re_im k 2 y
  have hne : (k : ℂ) * (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [hwre, one_re] at this
    linarith
  rw [Sieve.invZeta_eq_inv hne]
  have h1 := hΓζ 2 y ha2 le_rfl (Or.inr (Or.inr (by norm_num)))
  have h2 := hz _ (by rw [hwre]; linarith)
  have hxp : 0 ≤ t ^ (-(2 : ℝ)) := Real.rpow_nonneg ht.le _
  calc t ^ (-(2 : ℝ)) * (‖Complex.Gamma (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
        riemannZeta (((2 : ℝ) : ℂ) + (y : ℂ) * I)‖ *
        ‖(riemannZeta ((k : ℂ) * (((2 : ℝ) : ℂ) + (y : ℂ) * I)))⁻¹‖)
      ≤ t ^ (-(2 : ℝ)) * ((A * Real.exp (-(|y| / 4))) * Bz) := by
        gcongr
        exact (norm_nonneg _).trans h1
    _ = t ^ (-(2 : ℝ)) * A * Bz * Real.exp (-((1 / 4 : ℝ) * |y|)) := by
        rw [show -((1 / 4 : ℝ) * |y|) = -(|y| / 4) by ring]; ring

theorem continuous_kFree_line {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    Continuous fun y : ℝ => kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hl : Continuous fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I := by fun_prop
  set z : ℂ := ((2 : ℝ) : ℂ) + (y : ℂ) * I with hz
  have hre : z.re = 2 := by rw [hz]; simp
  have hz1 : z ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre, one_re] at this; norm_num at this
  have hkz1 : (k : ℂ) * z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [one_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, hre] at this
    linarith
  have hkre : 1 < ((k : ℂ) * z).re := by
    rw [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, hre]; linarith
  have hu : RHTower.zetaResidueUnit ((k : ℂ) * z) ≠ 0 := by
    simp only [RHTower.zetaResidueUnit, Function.update_of_ne hkz1]
    exact mul_ne_zero (sub_ne_zero.mpr hkz1) (riemannZeta_ne_zero_of_one_lt_re hkre)
  have hG : DifferentiableAt ℂ Complex.Gamma z := by
    refine Complex.differentiableAt_Gamma z fun m hm => ?_
    have h := congrArg Complex.re hm
    rw [hre] at h
    simp only [neg_re, natCast_re] at h
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hP : DifferentiableAt ℂ (fun w : ℂ => (t : ℂ) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr ht.ne'))
  have hI : DifferentiableAt ℂ (fun w : ℂ => Sieve.invZeta ((k : ℂ) * w)) z :=
    (Sieve.differentiableAt_invZeta hu).comp z (differentiableAt_id.const_mul _)
  have hD : DifferentiableAt ℂ (kFreeAbelIntegrand k t) z :=
    hP.mul ((hG.mul (differentiableAt_riemannZeta hz1)).mul hI)
  exact ContinuousAt.comp (f := fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I) (x := y)
    hD.continuousAt hl.continuousAt

/-! ## Assembly -/

/-- **The contour bound at a fixed `t`.** -/
theorem norm_integral_kFree_sub_residue_le {k : ℕ} (hk : 2 ≤ k) {t a c K A V Bz : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hca : a ≤ c) (hc34 : c ≤ 3 / 4) (hkc : k * c ≤ 2)
    (hK1 : 1 ≤ K) (hA : 0 ≤ A) (hV : 0 ≤ V) (hBz : 0 ≤ Bz)
    (hΓζ : ∀ σ y : ℝ, a ≤ σ → σ ≤ 2 → (1 ≤ |y| ∨ σ ≤ 3 / 4 ∨ 3 / 2 ≤ σ) →
      ‖Complex.Gamma ((σ : ℂ) + (y : ℂ) * I) * riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖
        ≤ A * Real.exp (-(|y| / 4)))
    (hinvV : ∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w.re ≤ 2 → ‖Sieve.invZeta w‖ ≤ V)
    (hz : ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re → ‖(riemannZeta s)⁻¹‖ ≤ Bz)
    (hzf : ∀ w : ℂ, |w.im| ≤ k * K → k * c ≤ w.re → w ≠ 1 → riemannZeta w ≠ 0) :
    ‖(∫ y : ℝ, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I))
        - 2 * Real.pi * kFreeAbelPoleFactor k t 1‖
      ≤ t ^ (-c) * A * V * (2 * K)
        + 2 * (t ^ (-(2 : ℝ)) * A * Real.exp (-(K / 4)) * (V + Bz) * 2)
        + t ^ (-(2 : ℝ)) * A * Bz * Real.exp (-((1 / 4 : ℝ) * K / 2)) *
            ∫ y : ℝ, Real.exp (-(((1 / 4 : ℝ) / 2) * |y|)) := by
  have hc0 : 0 < c := lt_of_lt_of_le ha hca
  have hgbd : ∀ y, ‖(fun y : ℝ => kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)) y‖
      ≤ t ^ (-(2 : ℝ)) * A * Bz * Real.exp (-((1 / 4 : ℝ) * |y|)) :=
    fun y => norm_kFree_line_le hk ht (by linarith) hΓζ hz y
  have hgint : Integrable (fun y : ℝ => kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)) :=
    Integrable.mono' ((RHTower.integrable_exp_neg_mul_abs' (c := 1 / 4) (by norm_num)).const_mul
      (t ^ (-(2 : ℝ)) * A * Bz)) (continuous_kFree_line hk ht).aestronglyMeasurable
      (Eventually.of_forall hgbd)
  have htail := norm_integral_sub_intervalIntegral_le_rate (K := K) hgint
    (by norm_num : (0 : ℝ) < 1 / 4) (by linarith) (by positivity) hgbd
  have hsub := rect_subset_kFreeAbelDomain hk hc0 (by linarith) (by linarith) hzf
  have hres := norm_intervalIntegral_two_sub_residue_le (F := kFreeAbelIntegrand k t)
    (isOpen_kFreeAbelDomain k) (differentiableOn_kFreeAbelPoleFactor k ht)
    (one_mem_kFreeAbelDomain hk) hsub (by linarith) (by linarith)
    (fun z hz => kFreeAbelIntegrand_eq_div hz)
  have hleft := norm_kFree_left_edge_le hk ht hca hc34 hkc (by linarith) hA hΓζ hinvV
  have hbot := norm_kFree_horizontal_edge_le (y := -K) hk ht ht1 hca hc0.le (by linarith) hK1
    hA hV hBz (by rw [abs_neg, abs_of_nonneg (by linarith)]) hΓζ hinvV hz
  have htop := norm_kFree_horizontal_edge_le (y := K) hk ht ht1 hca hc0.le (by linarith) hK1
    hA hV hBz (abs_of_nonneg (by linarith)) hΓζ hinvV hz
  set Rf := ∫ y : ℝ, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)
  set Rk := ∫ y in (-K)..K, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)
  set P := 2 * (Real.pi : ℂ) * kFreeAbelPoleFactor k t 1
  have h1 : ‖Rf - P‖ ≤ ‖Rf - Rk‖ + ‖Rk - P‖ := by
    have := norm_add_le (Rf - Rk) (Rk - P)
    rwa [sub_add_sub_cancel] at this
  linarith [hres, hleft, hbot, htop, htail, h1]

/-- The arithmetic of the final bound. -/
theorem kFree_final_arith {x c K A Bz Cv LF I₈ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hK0 : 0 ≤ K)
    (hc0 : 0 ≤ c) (hA : 0 ≤ A) (hBz : 0 ≤ Bz) (hCv : 0 ≤ Cv) (hI₈ : 0 ≤ I₈) (hLF1 : 1 ≤ LF) :
    x ^ (-c) * A * (Cv * LF) * (2 * K)
        + 2 * (x ^ (-(2 : ℝ)) * A * x ^ (6 : ℝ) * (Cv * LF + Bz) * 2)
        + x ^ (-(2 : ℝ)) * A * Bz * x ^ (3 : ℝ) * I₈
      ≤ (2 * A * Cv + 4 * A * Cv + 4 * A * Bz + A * Bz * I₈) * (1 + K) * LF * x ^ (-c) := by
  have hx2 : x ^ (-(2 : ℝ)) * x ^ (6 : ℝ) = x ^ (4 : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  have hx2' : x ^ (-(2 : ℝ)) * x ^ (3 : ℝ) = x := by
    rw [← Real.rpow_add hx]; norm_num
  have hx4c : x ^ (4 : ℝ) ≤ x ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith)
  have hx1c : x ≤ x ^ (-c) := by
    have := Real.rpow_le_rpow_of_exponent_ge hx hx1.le (show -c ≤ (1 : ℝ) by linarith)
    rwa [Real.rpow_one] at this
  have hxc0 : 0 ≤ x ^ (-c) := Real.rpow_nonneg hx.le _
  have hLF0 : 0 ≤ LF := by linarith
  have e1 : x ^ (-c) * A * (Cv * LF) * (2 * K) ≤ (2 * A * Cv) * (1 + K) * LF * x ^ (-c) := by
    have h : x ^ (-c) * A * (Cv * LF) * (2 * K) = (2 * A * Cv) * K * LF * x ^ (-c) := by ring
    rw [h]
    have : 0 ≤ 2 * A * Cv := by positivity
    gcongr
    linarith
  have e2 : 2 * (x ^ (-(2 : ℝ)) * A * x ^ (6 : ℝ) * (Cv * LF + Bz) * 2)
      ≤ (4 * A * Cv + 4 * A * Bz) * (1 + K) * LF * x ^ (-c) := by
    have h : 2 * (x ^ (-(2 : ℝ)) * A * x ^ (6 : ℝ) * (Cv * LF + Bz) * 2)
        = (4 * A * (Cv * LF + Bz)) * (x ^ (-(2 : ℝ)) * x ^ (6 : ℝ)) := by ring
    rw [h, hx2]
    have hB : 4 * A * (Cv * LF + Bz) ≤ (4 * A * Cv + 4 * A * Bz) * (1 + K) * LF := by
      have hKL : 1 ≤ (1 + K) * LF := by nlinarith
      have hKL' : LF ≤ (1 + K) * LF := by nlinarith
      have h4A : 0 ≤ 4 * A := by positivity
      have hc1 : 4 * A * Cv * LF ≤ 4 * A * Cv * ((1 + K) * LF) :=
        mul_le_mul_of_nonneg_left hKL' (by positivity)
      have hc2 : 4 * A * Bz ≤ 4 * A * Bz * ((1 + K) * LF) :=
        le_mul_of_one_le_right (by positivity) hKL
      nlinarith
    have : 0 ≤ 4 * A * (Cv * LF + Bz) := by positivity
    calc 4 * A * (Cv * LF + Bz) * x ^ (4 : ℝ) ≤ 4 * A * (Cv * LF + Bz) * x ^ (-c) := by gcongr
      _ ≤ (4 * A * Cv + 4 * A * Bz) * (1 + K) * LF * x ^ (-c) := by gcongr
  have e3 : x ^ (-(2 : ℝ)) * A * Bz * x ^ (3 : ℝ) * I₈
      ≤ (A * Bz * I₈) * (1 + K) * LF * x ^ (-c) := by
    have h : x ^ (-(2 : ℝ)) * A * Bz * x ^ (3 : ℝ) * I₈
        = (A * Bz * I₈) * 1 * 1 * (x ^ (-(2 : ℝ)) * x ^ (3 : ℝ)) := by ring
    rw [h, hx2']
    have : 0 ≤ A * Bz * I₈ := by positivity
    gcongr
    linarith
  nlinarith [e1, e2, e3]

/-- The contour height `24 log(1/t)`. -/
def kFreeHeight (t : ℝ) : ℝ := 24 * Real.log (1 / t)

/-- The polylogarithmic factor at the Vinogradov–Korobov height `k K + 1`. -/
def kFreeLogFactor (k : ℕ) (t : ℝ) : ℝ :=
  Real.log (k * kFreeHeight t + 1) ^ 7 * (1 + 2 / vkHadamardWidth (k * kFreeHeight t + 1)) ^ 7

theorem exp_neg_kFreeHeight_div {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Real.exp (-(kFreeHeight t / a)) = t ^ (24 / a) := by
  rw [kFreeHeight, Real.rpow_def_of_pos ht, one_div, Real.log_inv]
  congr 1
  ring

/-- **The Abel-smoothed `k`-free count below the Vinogradov–Korobov height.** -/
theorem exists_norm_kFreeExp_sub_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C δ t₀ : ℝ, 0 < C ∧ 0 < δ ∧ 0 < t₀ ∧ t₀ < 1 ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ‖kFreeExp k t - (t : ℂ)⁻¹ * (riemannZeta (k : ℂ))⁻¹‖
        ≤ C * (1 + kFreeHeight t) * kFreeLogFactor k t *
            t ^ (-((1 - min δ (vkHadamardWidth (k * kFreeHeight t + 1)) / 4) / k)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  obtain ⟨A, hA, hΓζ⟩ := exists_norm_Gamma_mul_zeta_le (a := 1 / (2 * k)) (by positivity)
  obtain ⟨Bz, hBz, hz⟩ := RHTower.exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  obtain ⟨Cv, δ, K₀, hCv, hδ, hK₀3, hK₀e, hzf, hinv⟩ := Sieve.exists_bound_invZeta_vk_uniform
  have hI₈ : 0 ≤ ∫ y : ℝ, Real.exp (-(((1 / 4 : ℝ) / 2) * |y|)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have ht₀1 : Real.exp (-(K₀ / 24)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  refine ⟨(2 * A * Cv + 4 * A * Cv + 4 * A * Bz + A * Bz *
      ∫ y : ℝ, Real.exp (-(((1 / 4 : ℝ) / 2) * |y|))) / (2 * Real.pi) + 1, δ,
    Real.exp (-(K₀ / 24)), by positivity, hδ, Real.exp_pos _, ht₀1, fun t ht htt₀ => ?_⟩
  have ht1 : t < 1 := lt_of_le_of_lt htt₀ ht₀1
  have hlog : K₀ / 24 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht htt₀
    rw [Real.log_exp] at this
    linarith
  have hK : K₀ ≤ kFreeHeight t := by rw [kFreeHeight]; linarith
  have hkK : K₀ ≤ k * kFreeHeight t := by nlinarith
  have hK1 : 1 ≤ kFreeHeight t := by linarith
  have hee : Real.exp (Real.exp 1) ≤ k * kFreeHeight t + 1 := by
    have : Real.exp (Real.exp 1) ≤ Real.exp (Real.exp 30) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
    linarith
  set w := vkHadamardWidth (k * kFreeHeight t + 1) with hwdef
  have hw : 0 < w := vkHadamardWidth_pos hee
  have hw8 : w ≤ 1 / 10 ^ 8 := Sieve.vkHadamardWidth_le_inv hee
  set m := min δ w with hmdef
  have hm0 : 0 < m := lt_min hδ hw
  have hm1 : m ≤ 1 / 10 ^ 8 := (min_le_right _ _).trans hw8
  set c := (1 - m / 4) / k with hcdef
  have hkc : k * c = 1 - m / 4 := by rw [hcdef]; field_simp
  have hca : 1 / (2 * k) ≤ c := by
    rw [hcdef, div_le_div_iff₀ (by positivity) hk0]; nlinarith
  have hc34 : c ≤ 3 / 4 := by
    rw [hcdef, div_le_iff₀ hk0]; nlinarith
  have hc0 : 0 ≤ c := le_trans (by positivity) hca
  have hlogK : 1 ≤ Real.log (k * kFreeHeight t + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLF1 : 1 ≤ kFreeLogFactor k t := by
    have h1 : 1 ≤ Real.log (k * kFreeHeight t + 1) ^ 7 := one_le_pow₀ hlogK
    have h2 : 1 ≤ (1 + 2 / w) ^ 7 := one_le_pow₀ (by have := div_pos two_pos hw; linarith)
    rw [kFreeLogFactor]
    nlinarith
  have hcore := norm_integral_kFree_sub_residue_le hk (t := t) (a := 1 / (2 * k)) (c := c)
    (K := kFreeHeight t) (A := A) (V := Cv * kFreeLogFactor k t) (Bz := Bz) ht ht1
    (by positivity) hca hc34 (by rw [hkc]; linarith) hK1 hA (by positivity) hBz hΓζ
    (fun w' him hre hre2 => by
      have h := hinv w' (k * kFreeHeight t) hkK him (by rw [← hkc]; exact hre) hre2
      rw [kFreeLogFactor]
      linarith)
    hz
    (fun w' him hre hw1 => hzf w' (k * kFreeHeight t) hkK him (by rw [← hkc]; exact hre) hw1)
  have hx6 : Real.exp (-(kFreeHeight t / 4)) = t ^ (6 : ℝ) := by
    rw [exp_neg_kFreeHeight_div ht]; norm_num
  have hx3 : Real.exp (-((1 / 4 : ℝ) * kFreeHeight t / 2)) = t ^ (3 : ℝ) := by
    rw [show (1 / 4 : ℝ) * kFreeHeight t / 2 = kFreeHeight t / 8 by ring,
      exp_neg_kFreeHeight_div ht]; norm_num
  rw [hx6, hx3] at hcore
  have harith := kFree_final_arith (c := c) (K := kFreeHeight t) (Cv := Cv)
    (LF := kFreeLogFactor k t) ht ht1 (by linarith) hc0 hA hBz hCv.le hI₈ hLF1
  have hcomb := hcore.trans harith
  have hres : kFreeAbelPoleFactor k t 1 = (t : ℂ)⁻¹ * (riemannZeta (k : ℂ))⁻¹ := by
    rw [kFreeAbelPoleFactor_one hk, Complex.cpow_neg_one]
  rw [kFreeExp_eq_integral hk ht, ← hres]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsplit : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ y : ℝ, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I)) - kFreeAbelPoleFactor k t 1
      = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ y : ℝ, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I))
          - 2 * Real.pi * kFreeAbelPoleFactor k t 1) := by
    have h2pi : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 1 := by
      have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
      push_cast
      field_simp
    rw [mul_sub, ← mul_assoc, h2pi, one_mul]
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  set E := t ^ (-c)
  have hEeq : E = t ^ (-((1 - m / 4) / k)) := rfl
  have hpos : 0 ≤ (1 + kFreeHeight t) * kFreeLogFactor k t * E := by
    have : 0 ≤ E := Real.rpow_nonneg ht.le _
    have : 0 ≤ kFreeLogFactor k t := by linarith
    positivity
  calc 1 / (2 * Real.pi) * ‖(∫ y : ℝ, kFreeAbelIntegrand k t (((2 : ℝ) : ℂ) + (y : ℂ) * I))
        - 2 * Real.pi * kFreeAbelPoleFactor k t 1‖
      ≤ 1 / (2 * Real.pi) * ((2 * A * Cv + 4 * A * Cv + 4 * A * Bz + A * Bz *
          ∫ y : ℝ, Real.exp (-(((1 / 4 : ℝ) / 2) * |y|))) * (1 + kFreeHeight t) *
            kFreeLogFactor k t * E) := by
        gcongr
    _ = (2 * A * Cv + 4 * A * Cv + 4 * A * Bz + A * Bz *
          ∫ y : ℝ, Real.exp (-(((1 / 4 : ℝ) / 2) * |y|))) / (2 * Real.pi) *
          (1 + kFreeHeight t) * kFreeLogFactor k t * E := by ring
    _ ≤ _ := by nlinarith

/-! ## The ladder quantities -/

/-- `Σ μ(m)/m^k = ζ(k)^{-1}`. -/
theorem kDensity_eq_inv_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    ((KFreeExponential.kDensity k : ℝ) : ℂ) = (riemannZeta (k : ℂ))⁻¹ := by
  have hre : 1 < (k : ℂ).re := by
    simp only [natCast_re]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [← RHTower.LSeries_moebius_eq_inv_riemannZeta hre, KFreeExponential.kDensity,
    Complex.ofReal_tsum, LSeries]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne', Complex.cpow_natCast]
    push_cast
    rfl

/-- `‖mPart k μ n‖ ≤ 1`. -/
theorem norm_mPart_moebius_le_one {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    ‖((mPart k (ArithmeticFunction.moebius : ArithmeticFunction ℤ) n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  by_cases h : ∃ j : ℕ, j ^ k = n
  · obtain ⟨j, rfl⟩ := h
    rw [mPart_apply_pow hk]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · push Not at h
    rw [mPart_apply_of_forall_pow_ne k _ h]
    simp

/-- `e^{-u}/(1 - e^{-u}) = 1/(e^u - 1)` for `u > 0`. -/
theorem cexp_neg_div_one_sub {u : ℝ} (hu : 0 < u) :
    Complex.exp (-(u : ℂ)) / (1 - Complex.exp (-(u : ℂ))) =
      ((KFreeExponential.bose u : ℝ) : ℂ) := by
  have hE : (Real.exp u : ℂ) - 1 ≠ 0 := by
    have : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
    exact sub_ne_zero.mpr (by exact_mod_cast this.ne')
  rw [KFreeExponential.bose, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_exp,
    Complex.ofReal_one]
  rw [Complex.ofReal_exp] at hE
  have hne : Complex.exp (u : ℂ) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.exp_neg]
  field_simp

/-- **The smoothed `k`-free count is the ladder profile.** -/
theorem kFreeExp_eq_kProfile {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    kFreeExp k t = ((KFreeExponential.kProfile k t : ℝ) : ℂ) := by
  have hk0 : k ≠ 0 := by omega
  set z : ℂ := Complex.exp (-(t : ℂ)) with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, Complex.norm_exp]
    simp only [neg_re, ofReal_re]
    exact Real.exp_lt_one_iff.mpr (by linarith) |>.trans_le' le_rfl
  have hzpow : ∀ n : ℕ, z ^ n = Complex.exp (-(((n : ℝ) * t : ℝ) : ℂ)) := by
    intro n
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hL := GaloisForLFunctions.HTGeometry.tsum_lambert_eq_tsum_divisorSum (B := 1)
    (f := fun n : ℕ => ((mPart k (ArithmeticFunction.moebius : ArithmeticFunction ℤ) n : ℤ) : ℂ))
    (norm_mPart_moebius_le_one hk0) hzn
  have hR : (∑' m : ℕ, (∑ d ∈ m.divisors,
      ((mPart k (ArithmeticFunction.moebius : ArithmeticFunction ℤ) d : ℤ) : ℂ)) * z ^ m)
      = kFreeExp k t := by
    rw [kFreeExp]
    refine tsum_congr fun m => ?_
    rw [hzpow, ← Int.cast_sum, sum_divisors_mPart_moebius hk0]
  rw [← hR, ← hL]
  -- reindex the Lambert side along `m ↦ m^k`
  have hinj : Function.Injective fun m : ℕ => m ^ k := Nat.pow_left_injective hk0
  have hsupp : Function.support (fun n : ℕ =>
      ((mPart k (ArithmeticFunction.moebius : ArithmeticFunction ℤ) n : ℤ) : ℂ) *
        (z ^ n / (1 - z ^ n))) ⊆ Set.range fun m : ℕ => m ^ k := by
    intro n hn
    by_contra h
    apply hn
    have h' : ∀ j : ℕ, j ^ k ≠ n := fun j hj => h ⟨j, hj⟩
    simp only [mPart_apply_of_forall_pow_ne k _ h', Int.cast_zero, zero_mul]
  rw [← hinj.tsum_eq hsupp, KFreeExponential.kProfile, Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  simp only [mPart_apply_pow hk0]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hu : 0 < (m : ℝ) ^ k * t := by positivity
    have : (((m ^ k : ℕ) : ℝ) * t : ℝ) = (m : ℝ) ^ k * t := by push_cast; ring
    rw [hzpow (m ^ k), this, cexp_neg_div_one_sub hu]
    push_cast
    ring

/-- **Near-power saving for the ladder profile.** With `K = 24 log(1/t)`,
`|A_k(t) - c_k/t| ≤ C (1+K) L(kK) t^{-(1 - min(δ, w(kK+1))/4)/k}`. -/
theorem exists_abs_kProfile_sub_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C δ t₀ : ℝ, 0 < C ∧ 0 < δ ∧ 0 < t₀ ∧ t₀ < 1 ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      |KFreeExponential.kProfile k t - KFreeExponential.kDensity k / t|
        ≤ C * (1 + kFreeHeight t) * kFreeLogFactor k t *
            t ^ (-((1 - min δ (vkHadamardWidth (k * kFreeHeight t + 1)) / 4) / k)) := by
  obtain ⟨C, δ, t₀, hC, hδ, ht₀, ht₀1, hbd⟩ := exists_norm_kFreeExp_sub_le hk
  refine ⟨C, δ, t₀, hC, hδ, ht₀, ht₀1, fun t ht htt₀ => ?_⟩
  have h := hbd t ht htt₀
  rw [kFreeExp_eq_kProfile hk ht, ← kDensity_eq_inv_riemannZeta hk] at h
  have he : ((KFreeExponential.kProfile k t : ℝ) : ℂ) - (t : ℂ)⁻¹ *
      ((KFreeExponential.kDensity k : ℝ) : ℂ)
      = ((KFreeExponential.kProfile k t - KFreeExponential.kDensity k / t : ℝ) : ℂ) := by
    push_cast; ring
  rwa [he, Complex.norm_real, Real.norm_eq_abs] at h

end

end RHTower.KFreeAbel
