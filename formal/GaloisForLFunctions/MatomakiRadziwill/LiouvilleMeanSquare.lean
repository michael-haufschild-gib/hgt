import GaloisForLFunctions.MatomakiRadziwill.LiouvilleLowFrequency
import GaloisForLFunctions.MatomakiRadziwill.LadderMeanSquare

/-!
# Matomäki–Radziwiłł in mean square for `λ`

`λ = λχ₁` for the character `χ₁` mod 1 (`twLiouville_trivial`).  Split the frequencies at
`T = (log X)^{19}/2π`:

* below `T` (`exists_lowFreq_bound`): summation by parts against `1/n` and the twisted Liouville
  partial sums give `|F(w)| ≤ 8ε(X)`, `ε(X) = 2K e^{-((log X)/4)^{1/20}} + 4X^{-1/4}`, so
  `∫_{|w|≤T} |F|² ≤ 2T(8ε(X))² → 0` (`tendsto_lowPart`);
* above `T` the ladder runs on `A = [−W, W] ∖ (−T, T)` (`integral_fullPoly_on_le`, from
  `ladder_rough_le` on `A` and `ladder_nonrough_le`), the top blocks being bounded by `ζ` Route T
  (`exists_norm_blockQ_liouville_le`).

Together (`exists_mean_square_liouville_le`): for every `ε > 0` there is `L₀` such that for
`L ≥ L₀` there is `X₀` with `∫_{|w|≤W} |Σ_{X<n≤4X} λ(n)/n · n^{2πiw}|² ≤ ε` for `X ≥ X₀`,
`W ≤ X e^{-L/2}`.
-/

open Finset Filter Topology Complex ArithmeticFunction RHTower.Sieve MeasureTheory Set

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem twLiouville_trivial (n : ℕ) :
    twLiouville (1 : DirichletCharacter ℂ 1) n = (liouville n : ℂ) := by
  rw [twLiouville, trivialChar_apply, mul_one]

/-- The polynomial `F(w)` of `λ` as a weighted twisted sum. -/
theorem fullPoly_liouville_eq (X : ℕ) (w : ℝ) :
    fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X w
      = ∑ n ∈ Finset.Ioc X (4 * X),
          ((liouville n : ℂ) * (n : ℂ) ^ (-(((-(2 * Real.pi * w) : ℝ) : ℂ) * I)))
            * (((1 / (n : ℝ)) : ℝ) : ℂ) := by
  rw [fullPoly, logPoly]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by rw [Finset.mem_Ioc] at hn; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [coefA, twLiouville_trivial]
  have hc : (n : ℂ) ^ (-(((-(2 * Real.pi * w) : ℝ) : ℂ) * I))
      = Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hnR.le]
    congr 1
    push_cast
    ring
  rw [hc]
  push_cast
  field_simp

/-- **Summation by parts for `F(w)`.** -/
theorem norm_fullPoly_liouville_le {X : ℕ} (hX : 1 ≤ X) {w B : ℝ}
    (hB : ∀ t : ℕ, X ≤ t → t ≤ 4 * X →
      ‖∑ n ∈ Finset.Icc 1 t,
          (liouville n : ℂ) * (n : ℂ) ^ (-(((-(2 * Real.pi * w) : ℝ) : ℂ) * I))‖ ≤ B) :
    ‖fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X w‖ ≤ 2 * B / X := by
  rw [fullPoly_liouville_eq]
  set a : ℕ → ℂ := fun n =>
    (liouville n : ℂ) * (n : ℂ) ^ (-(((-(2 * Real.pi * w) : ℝ) : ℂ) * I)) with ha
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hIoc : ∀ t : ℕ, X ≤ t → ∑ m ∈ Finset.Ioc X t, a m
      = ∑ n ∈ Finset.Icc 1 t, a n - ∑ n ∈ Finset.Icc 1 X, a n := by
    intro t hXt
    have e1 : Finset.Icc 1 t = Finset.Ioc 0 t := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e2 : Finset.Icc 1 X = Finset.Ioc 0 X := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e1, e2, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le X) hXt]
    ring
  have hB2 : ∀ t, X ≤ t → t ≤ 4 * X → ‖∑ m ∈ Finset.Ioc X t, a m‖ ≤ 2 * B := by
    intro t hXt ht
    rw [hIoc t hXt]
    have h1 := hB t hXt ht
    have h2 := hB X le_rfl (by omega)
    calc ‖∑ n ∈ Finset.Icc 1 t, a n - ∑ n ∈ Finset.Icc 1 X, a n‖
        ≤ B + B := le_trans (norm_sub_le _ _) (add_le_add h1 h2)
      _ = 2 * B := by ring
  have habel := PrimeExponentialSums.norm_sum_mul_le_of_partial a
    (fun n => (((1 / (n : ℝ)) : ℝ) : ℂ)) (show X ≤ 4 * X by omega) hB2
  refine le_trans habel (le_of_eq ?_)
  -- the weight `1/n` has total variation `1/X` on `[X, 4X]`
  have hterm : ∀ n ∈ Finset.Ico X (4 * X),
      ‖(((1 / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) - (((1 / (n : ℝ)) : ℝ) : ℂ)‖
        = 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg]
    push_cast
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hn0 (by linarith)
  rw [sum_congr rfl hterm]
  have htel : ∑ n ∈ Finset.Ico X (4 * X), (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))
      = 1 / (X : ℝ) - 1 / ((4 * X : ℕ) : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have := Finset.sum_range_sub' (fun k : ℕ => 1 / (((X + k : ℕ) : ℝ))) (4 * X - X)
    have e : ∀ k ∈ Finset.range (4 * X - X),
        1 / (((X + k : ℕ) : ℝ)) - 1 / (((X + k + 1 : ℕ) : ℝ))
          = 1 / (((X + k : ℕ) : ℝ)) - 1 / (((X + (k + 1) : ℕ) : ℝ)) := by
      intro k _; rfl
    rw [sum_congr rfl e, this]
    have e2 : X + (4 * X - X) = 4 * X := by omega
    rw [e2]
    simp
  rw [htel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  push_cast
  field_simp
  ring

/-- The relative error of the twisted Liouville sums at scale `X`. -/
def liouvilleRate (K X : ℝ) : ℝ :=
  2 * K * Real.exp (-((Real.log X / 4) ^ ((1 : ℝ) / 20))) + 4 * X ^ (-(1 / 4 : ℝ))

/-- **Low frequencies for `λ`.** -/
theorem exists_lowFreq_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ X : ℕ, N₀ ≤ X → 1 ≤ X → ∀ w : ℝ,
      4 * Real.pi * |w| ≤ Real.sqrt X →
        ‖fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X w‖ ≤ 8 * liouvilleRate K X := by
  obtain ⟨K, hK, N₀, hN₀⟩ := exists_norm_sum_liouvilleTwist_le
  refine ⟨K, hK, N₀, fun X hX hX1 w hw => ?_⟩
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hB : ∀ t : ℕ, X ≤ t → t ≤ 4 * X →
      ‖∑ n ∈ Finset.Icc 1 t,
          (liouville n : ℂ) * (n : ℂ) ^ (-(((-(2 * Real.pi * w) : ℝ) : ℂ) * I))‖
        ≤ 4 * X * liouvilleRate K X := by
    intro t hXt ht
    have htX : (X : ℝ) ≤ t := by exact_mod_cast hXt
    have ht4 : (t : ℝ) ≤ 4 * X := by exact_mod_cast ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hτ : 2 * |(-(2 * Real.pi * w))| ≤ Real.sqrt t := by
      rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have : Real.sqrt X ≤ Real.sqrt t := Real.sqrt_le_sqrt htX
      linarith
    have h := hN₀ t (le_trans hX hXt) _ hτ
    refine le_trans h ?_
    have hlog : Real.log X / 4 ≤ Real.log t / 4 := by
      have := Real.log_le_log hX0 htX; linarith
    have hlogX0 : 0 ≤ Real.log X / 4 := by
      have := Real.log_nonneg (by exact_mod_cast hX1 : (1 : ℝ) ≤ X); linarith
    have hexp : Real.exp (-((Real.log t / 4) ^ ((1 : ℝ) / 20)))
        ≤ Real.exp (-((Real.log X / 4) ^ ((1 : ℝ) / 20))) :=
      Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow hlogX0 hlog (by norm_num)))
    have h34 : (t : ℝ) ^ ((3 : ℝ) / 4) ≤ 4 * X * (X : ℝ) ^ (-(1 / 4 : ℝ)) := by
      have e : (t : ℝ) ^ ((3 : ℝ) / 4) = t * (t : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_one_add' ht0.le (by norm_num)]; norm_num
      have h1 : (t : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (X : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hX0 htX (by norm_num)
      rw [e]
      exact mul_le_mul ht4 h1 (Real.rpow_nonneg ht0.le _) (by positivity)
    unfold liouvilleRate
    have h1 : 2 * K * t * Real.exp (-((Real.log t / 4) ^ ((1 : ℝ) / 20)))
        ≤ 2 * K * (4 * X) * Real.exp (-((Real.log X / 4) ^ ((1 : ℝ) / 20))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht4 (by positivity)) hexp (Real.exp_pos _).le
        (by positivity)
    nlinarith
  have h := norm_fullPoly_liouville_le hX1 hB
  calc ‖fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X w‖ ≤ 2 * (4 * X * liouvilleRate K X) / X := h
    _ = 8 * liouvilleRate K X := by field_simp; ring

/-- The low-frequency part `(log X)^{19}/π · (8ε(X))²` tends to zero. -/
theorem tendsto_lowPart (K : ℝ) :
    Tendsto (fun X : ℝ => Real.log X ^ 19 / Real.pi * (8 * liouvilleRate K X) ^ 2) atTop (𝓝 0) := by
  -- `ℓ^{19} e^{-2u} ≤ 4^{19} u^{380} e^{-u}`, `u = (ℓ/4)^{1/20}`
  have hu : Tendsto (fun ℓ : ℝ => (ℓ / 4) ^ ((1 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_id.atTop_div_const (by norm_num))
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 380).comp hu).const_mul (4 ^ 19 : ℝ)
  rw [mul_zero] at h1
  have hA : Tendsto (fun ℓ : ℝ => ℓ ^ 19 * Real.exp (-(2 * (ℓ / 4) ^ ((1 : ℝ) / 20))))
      atTop (𝓝 0) := by
    refine squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono fun ℓ hℓ =>
      mul_nonneg (pow_nonneg hℓ 19) (Real.exp_pos _).le) ?_ h1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ℓ hℓ
      simp only [Function.comp]
      set u := (ℓ / 4) ^ ((1 : ℝ) / 20) with hudef
      have hu0 : 0 ≤ u := Real.rpow_nonneg (by linarith) _
      have hℓu : ℓ = 4 * u ^ 20 := by
        rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num; ring
      have e : ℓ ^ 19 = 4 ^ 19 * u ^ 380 := by rw [hℓu]; ring
      rw [e]
      have : Real.exp (-(2 * u)) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
      have h0 : 0 ≤ (4 : ℝ) ^ 19 * u ^ 380 := by positivity
      calc 4 ^ 19 * u ^ 380 * Real.exp (-(2 * u)) ≤ 4 ^ 19 * u ^ 380 * Real.exp (-u) :=
            mul_le_mul_of_nonneg_left this h0
        _ = 4 ^ 19 * (u ^ 380 * Real.exp (-u)) := by ring
  have hB : Tendsto (fun ℓ : ℝ => ℓ ^ 19 * Real.exp (-(1 / 2) * ℓ)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_mul 19 (by norm_num)
  -- the majorant `(128/π)(4K² ℓ^{19}e^{-2u} + 16 ℓ^{19} e^{-ℓ/2})`
  have hmaj := ((hA.const_mul (4 * K ^ 2)).add (hB.const_mul 16)).const_mul (128 / Real.pi)
  simp only [mul_zero, add_zero] at hmaj
  have hmajX := hmaj.comp Real.tendsto_log_atTop
  refine squeeze_zero' ?_ ?_ hmajX
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have := Real.log_nonneg hX.le
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    simp only [Function.comp]
    have hX0 : 0 < X := by linarith
    have hℓ : 0 ≤ Real.log X := Real.log_nonneg hX.le
    have hXq : X ^ (-(1 / 4 : ℝ)) = Real.exp (-(1 / 4) * Real.log X) := by
      rw [Real.rpow_def_of_pos hX0]; ring_nf
    unfold liouvilleRate
    rw [hXq]
    set a := Real.exp (-((Real.log X / 4) ^ ((1 : ℝ) / 20))) with hadef
    set b := Real.exp (-(1 / 4) * Real.log X) with hbdef
    have ha2 : a ^ 2 = Real.exp (-(2 * (Real.log X / 4) ^ ((1 : ℝ) / 20))) := by
      rw [hadef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hb2 : b ^ 2 = Real.exp (-(1 / 2) * Real.log X) := by
      rw [hbdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsq : (8 * (2 * K * a + 4 * b)) ^ 2 ≤ 128 * (4 * K ^ 2 * a ^ 2 + 16 * b ^ 2) := by
      nlinarith [sq_nonneg (2 * K * a - 4 * b)]
    have hL : 0 ≤ Real.log X ^ 19 / Real.pi := by positivity
    calc Real.log X ^ 19 / Real.pi * (8 * (2 * K * a + 4 * b)) ^ 2
        ≤ Real.log X ^ 19 / Real.pi * (128 * (4 * K ^ 2 * a ^ 2 + 16 * b ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq hL
      _ = 128 / Real.pi * (4 * K ^ 2 * (Real.log X ^ 19 * a ^ 2)
            + 16 * (Real.log X ^ 19 * b ^ 2)) := by ring
      _ = _ := by rw [ha2, hb2]

/-- **The mean square on a set of frequencies above the low range.** -/
theorem integral_fullPoly_on_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) {L : ℝ} (hL : 2 ^ 20 ≤ L)
    (hstep : ∀ x : ℝ, L / 2 ≤ x →
      144 * Real.exp 1 * 2 ^ 48 * x ^ 66 * Real.exp (-(152 / 100) * x) ≤ Real.exp (-x))
    (hlogL : 0 < Real.log L)
    (h0 : Real.log L / 4 ≤ Real.log (seqB L 0 / seqA L 0) - mertensScaleConst)
    (h1 : 2 * mertensScaleConst + 2 * (Real.log L / 2) ≤ Real.log (seqA L 1))
    {X : ℕ} (hXe : Real.exp 1 ≤ (X : ℝ)) (hJb : seqB L 1 ≤ ladderTopLow X)
    (hlarge : 864 * Real.log X
      ≤ (Real.log X ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ) * Real.log X ^ (93 / 100 : ℝ))
    (htop1 : 1 ≤ ladderTopLow X) (htop2 : ladderTopLow X + 1 ≤ ladderTopHigh X)
    (htop3 : 0 < 3 / 100 * Real.log (Real.log X) - mertensScaleConst)
    {W : ℝ} (hWe : Real.exp 1 ≤ W) (hWX : W ≤ X * Real.exp (-(L / 2))) {A : Set ℝ}
    (hAm : MeasurableSet A) (hAs : A ⊆ Icc (-W) W)
    (hρ : ∀ v ∈ (ladderConfig hL (X : ℝ)).topBlocks (Real.log X), ∀ w ∈ A,
      ‖blockQ f (ladderConfig hL (X : ℝ)).top (Real.log X) v w‖ ≤ 1 / Real.log X ^ (3 : ℝ)) :
    (∫ w in A, ‖fullPoly f X w‖ ^ 2) ≤ ladderHPart L + ladderXPart X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hJ : 2 ≤ ladderJ hL (X : ℝ) := ladderJ_pos hL hJb
  have hexpL : Real.exp (-(L / 2)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hWX' : W ≤ X := le_trans hWX (by nlinarith)
  have hW1 : 1 ≤ W := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  have hrough := ladder_rough_le hf hmul hL hstep hXe hJ hlarge hWe hWX hAm hAs hρ
  have hnon := ladder_nonrough_le hf hL hlogL h0 h1 hXe htop1 htop2 htop3 hW1 hWX'
  set R := logPoly (coefA f) ((ladderConfig hL (X : ℝ)).ladderS X) with hRdef
  have hcF : Continuous (fullPoly f X) := continuous_logPoly _ _
  have hcR : Continuous R := continuous_logPoly _ _
  have hiA0 : IntegrableOn (fun w => ‖fullPoly f X w‖ ^ 2) A :=
    ((hcF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set hAs
  have hiA1 : IntegrableOn (fun w => ‖fullPoly f X w - R w‖ ^ 2) A :=
    (((hcF.sub hcR).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set hAs
  have hiA2 : IntegrableOn (fun w => ‖R w‖ ^ 2) A :=
    ((hcR.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set hAs
  have hsplit : (∫ w in A, ‖fullPoly f X w‖ ^ 2)
      ≤ 2 * (∫ w in A, ‖fullPoly f X w - R w‖ ^ 2) + 2 * (∫ w in A, ‖R w‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hiA1.const_mul 2) (hiA2.const_mul 2)]
    exact setIntegral_mono hiA0 ((hiA1.const_mul 2).add (hiA2.const_mul 2))
      fun w => normSq_le_two_mul_add _ _
  have hIcc1 : IntegrableOn (fun w => ‖fullPoly f X w - R w‖ ^ 2) (Icc (-W) W) :=
    ((hcF.sub hcR).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hmono : (∫ w in A, ‖fullPoly f X w - R w‖ ^ 2)
      ≤ ∫ w in Icc (-W) W, ‖fullPoly f X w - R w‖ ^ 2 :=
    setIntegral_mono_set hIcc1 (ae_of_all _ fun w => sq_nonneg _) hAs.eventuallyLE
  unfold ladderHPart ladderXPart
  linarith

/-- The extra conditions on `X` for `λ`. -/
theorem eventually_liouville_conditions (K : ℝ) {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∀ᶠ X : ℝ in atTop, (N₀ : ℝ) ≤ X ∧ 2 * Real.log X ^ 19 ≤ Real.sqrt X
      ∧ Real.log X ^ (92 / 100 : ℝ) ≤ ladderTopLow X - 1
      ∧ Real.log X ^ 19 / Real.pi * (8 * liouvilleRate K X) ^ 2 ≤ ε := by
  have hsq : ∀ᶠ ℓ : ℝ in atTop, ℓ ^ 19 * Real.exp (-(1 / 2) * ℓ) ≤ 1 / 2 :=
    (tendsto_pow_mul_exp_neg_mul 19 (by norm_num)).eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop (N₀ : ℝ), eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually hsq,
    Real.tendsto_log_atTop.eventually (eventually_rpow_add_one_le (by norm_num : (0 : ℝ) < 92 / 100)
      (by norm_num : (92 / 100 : ℝ) < 93 / 100)),
    (tendsto_lowPart K).eventually (ge_mem_nhds hε)] with X hN hX1 h1 h2 h3
  refine ⟨hN, ?_, by unfold ladderTopLow; linarith, h3⟩
  have hX0 : 0 < X := by linarith
  have hs : Real.sqrt X = Real.exp ((1 / 2) * Real.log X) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]; ring_nf
  have hE := Real.exp_pos ((1 / 2) * Real.log X)
  have e : Real.exp (-(1 / 2) * Real.log X) * Real.exp ((1 / 2) * Real.log X) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [hs]
  have := mul_le_mul_of_nonneg_right h1 hE.le
  rw [mul_assoc, e, mul_one] at this
  linarith

/-- `ζ` Route T on the high frequencies `T ≤ |w|`, `2πT = (log X)^{19}`. -/
theorem rho_on_high {X₁ : ℝ}
    (hX₁ : ∀ X : ℝ, X₁ ≤ X → ∀ (Pa Pb : ℕ) (H : ℝ), 2 ≤ H →
      Real.log X ^ (92 / 100 : ℝ) ≤ Real.log Pa → (Pb : ℝ) ≤ X → ∀ v : ℕ, ∀ w : ℝ,
        Real.log X ^ 19 ≤ 2 * Real.pi * |w| → 2 * Real.pi * |w| ≤ X →
          ‖blockQ (twLiouville (1 : DirichletCharacter ℂ 1)) ((Finset.Ioc Pa Pb).filter Nat.Prime)
            H v w‖ ≤ 1 / Real.log X ^ (3 : ℝ))
    {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℕ} (hXX₁ : X₁ ≤ X) (hXe : Real.exp 1 ≤ (X : ℝ))
    (hlog2 : 2 ≤ Real.log X) (htop1 : 1 ≤ ladderTopLow X)
    (h92 : Real.log X ^ (92 / 100 : ℝ) ≤ ladderTopLow X - 1) {W' T : ℝ}
    (hW'X : W' ≤ X * Real.exp (-(L / 2))) (hT : 2 * Real.pi * T = Real.log X ^ 19) :
    ∀ v ∈ (ladderConfig hL (X : ℝ)).topBlocks (Real.log X), ∀ w ∈ Icc (-W') W' \ Ioo (-T) T,
      ‖blockQ (twLiouville (1 : DirichletCharacter ℂ 1)) (ladderConfig hL (X : ℝ)).top
        (Real.log X) v w‖ ≤ 1 / Real.log X ^ (3 : ℝ) := by
  intro v _ w hw
  obtain ⟨hwI, hwT⟩ := hw
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogPa : Real.log X ^ (92 / 100 : ℝ)
      ≤ Real.log (⌊Real.exp (ladderTopLow (X : ℝ))⌋₊ : ℝ) :=
    le_trans h92 (log_floor_exp_ge htop1)
  have hPb : ((⌊Real.exp (ladderTopHigh (X : ℝ))⌋₊ : ℕ) : ℝ) ≤ X := by
    obtain ⟨-, hhX⟩ := ladderTop_le (one_le_log_of_exp_le hXe)
    calc ((⌊Real.exp (ladderTopHigh (X : ℝ))⌋₊ : ℕ) : ℝ) ≤ Real.exp (ladderTopHigh X) :=
          Nat.floor_le (Real.exp_pos _).le
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hhX
      _ = X := Real.exp_log hX0
  have hpi := Real.pi_pos
  have hwlo : Real.log X ^ 19 ≤ 2 * Real.pi * |w| := by
    have hT' : T ≤ |w| := by
      by_contra h
      push Not at h
      exact hwT ⟨by linarith [neg_abs_le w], by linarith [le_abs_self w]⟩
    rw [← hT]
    exact mul_le_mul_of_nonneg_left hT' (by positivity)
  have hwhi : 2 * Real.pi * |w| ≤ X := by
    have h1' : |w| ≤ W' := abs_le.mpr ⟨by linarith [hwI.1], hwI.2⟩
    have h2π : 2 * Real.pi * Real.exp (-(L / 2)) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      linarith [Real.add_one_le_exp (L / 2), Real.pi_lt_d2]
    calc 2 * Real.pi * |w| ≤ 2 * Real.pi * (X * Real.exp (-(L / 2))) :=
          mul_le_mul_of_nonneg_left (le_trans h1' hW'X) (by positivity)
      _ = X * (2 * Real.pi * Real.exp (-(L / 2))) := by ring
      _ ≤ X * 1 := mul_le_mul_of_nonneg_left h2π hX0.le
      _ = X := mul_one _
  exact hX₁ X hXX₁ _ _ (Real.log X) hlog2 hlogPa hPb v w hwlo hwhi

/-- The low frequencies against a pointwise bound. -/
theorem lowFreq_integral_le {F : ℝ → ℂ} (hF : Continuous F) {T W' c : ℝ} (hT0 : 0 ≤ T)
    (hpt : ∀ w ∈ Icc (-T) T, ‖F w‖ ≤ c) :
    (∫ w in Icc (-W') W' ∩ Ioo (-T) T, ‖F w‖ ^ 2) ≤ 2 * T * c ^ 2 := by
  have hiT : IntegrableOn (fun w => ‖F w‖ ^ 2) (Icc (-T) T) :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have h1 : (∫ w in Icc (-W') W' ∩ Ioo (-T) T, ‖F w‖ ^ 2) ≤ ∫ w in Icc (-T) T, ‖F w‖ ^ 2 :=
    setIntegral_mono_set hiT (ae_of_all _ fun w => sq_nonneg _)
      (Set.inter_subset_right.trans Set.Ioo_subset_Icc_self).eventuallyLE
  have h2 : (∫ w in Icc (-T) T, ‖F w‖ ^ 2) ≤ ∫ _w in Icc (-T) T, c ^ 2 :=
    setIntegral_mono_on hiT (integrableOn_const (by simp)) measurableSet_Icc fun w hw =>
      pow_le_pow_left₀ (norm_nonneg _) (hpt w hw) 2
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h2
  linarith

/-- The frequency split `[−W, W] ⊆ ([−W', W'] ∩ (−T, T)) ∪ ([−W', W'] ∖ (−T, T))`. -/
theorem integral_split_le {F : ℝ → ℂ} (hF : Continuous F) {W W' T : ℝ} (hWW' : W ≤ W') :
    (∫ w in Icc (-W) W, ‖F w‖ ^ 2)
      ≤ (∫ w in Icc (-W') W' ∩ Ioo (-T) T, ‖F w‖ ^ 2)
        + ∫ w in Icc (-W') W' \ Ioo (-T) T, ‖F w‖ ^ 2 := by
  have hiW : IntegrableOn (fun w => ‖F w‖ ^ 2) (Icc (-W') W') :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_inter_add_sdiff (μ := volume) (measurableSet_Ioo (a := -T) (b := T)) hiW]
  exact setIntegral_mono_set hiW (ae_of_all _ fun w => sq_nonneg _)
    (Icc_subset_Icc (by linarith) hWW').eventuallyLE

/-- **Matomäki–Radziwiłł in mean square for `λ`.** -/
theorem exists_mean_square_liouville_le {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ (X : ℝ) → ∀ W : ℝ, 0 ≤ W →
      W ≤ X * Real.exp (-(L / 2)) →
        (∫ w in Icc (-W) W, ‖fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X w‖ ^ 2)
          ≤ ε := by
  obtain ⟨x₀, -, hx₀⟩ := exists_poly_exp_le (144 * Real.exp 1 * 2 ^ 48) 66
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    ((eventually_ladderHPart_le hε3).and (eventually_ladder_L_conditions x₀))
  refine ⟨L₀, fun L hLL => ?_⟩
  obtain ⟨hHP, hL, hx₀L, hlogL, h0, h1⟩ := hL₀ L hLL
  obtain ⟨K, -, N₀, hlowF⟩ := exists_lowFreq_bound
  obtain ⟨X₁, hX₁⟩ := exists_norm_blockQ_liouville_le
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((eventually_ladderXPart_le hε3).and ((eventually_top_conditions (seqB L 1)).and
      ((eventually_liouville_conditions K hε3 N₀).and ((eventually_ge_atTop X₁).and
        (eventually_ge_atTop (Real.exp 1 * Real.exp (L / 2)))))))
  refine ⟨X₀, fun X hX W hW0 hWX => ?_⟩
  obtain ⟨hXP, ⟨hXe, hlog2, htop1, htop2, htop3, hlarge, hJb, -⟩, ⟨hXN, hsqrt, h92, hlow⟩,
    hXX₁, hXL⟩ := hX₀ X hX
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hXe
    exact_mod_cast this
  have hstep : ∀ x : ℝ, L / 2 ≤ x →
      144 * Real.exp 1 * 2 ^ 48 * x ^ 66 * Real.exp (-(152 / 100) * x) ≤ Real.exp (-x) :=
    fun x hx => hx₀ x (le_trans hx₀L hx)
  have heX : Real.exp 1 ≤ X * Real.exp (-(L / 2)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]; exact hXL
  have hW'X : max W (Real.exp 1) ≤ X * Real.exp (-(L / 2)) := max_le hWX heX
  set T : ℝ := Real.log X ^ 19 / (2 * Real.pi) with hTdef
  have hT : 2 * Real.pi * T = Real.log X ^ 19 := by rw [hTdef]; field_simp
  have hT0 : 0 ≤ T := by
    have := Real.log_nonneg (by exact_mod_cast hX1 : (1 : ℝ) ≤ X); positivity
  have hρ := rho_on_high hX₁ hL hXX₁ hXe hlog2 htop1 h92 hW'X hT
  have hon := integral_fullPoly_on_le (norm_twLiouville_le _) (twLiouville_mul _) hL hstep hlogL
    h0 h1 hXe hJb hlarge htop1 htop2 htop3 (le_max_right _ _) hW'X
    (measurableSet_Icc.diff measurableSet_Ioo) diff_subset hρ
  have hXN' : N₀ ≤ X := by exact_mod_cast hXN
  have hlowpt : ∀ w ∈ Icc (-T) T,
      ‖fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X w‖ ≤ 8 * liouvilleRate K X := by
    intro w hw
    have hwT : |w| ≤ T := abs_le.mpr hw
    have h4 : 4 * Real.pi * |w| ≤ Real.sqrt X := by
      have hpi := Real.pi_pos
      have : 4 * Real.pi * |w| ≤ 4 * Real.pi * T := mul_le_mul_of_nonneg_left hwT (by positivity)
      linarith
    exact hlowF X hXN' hX1 w h4
  have hlowInt := lowFreq_integral_le (F := fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X)
    (W' := max W (Real.exp 1)) (continuous_logPoly _ _) hT0 hlowpt
  have hsplit := integral_split_le (F := fullPoly (twLiouville (1 : DirichletCharacter ℂ 1)) X)
    (T := T) (continuous_logPoly _ _) (le_max_left W (Real.exp 1))
  have e : 2 * T * (8 * liouvilleRate K X) ^ 2
      = Real.log X ^ 19 / Real.pi * (8 * liouvilleRate K X) ^ 2 := by
    rw [hTdef]; field_simp
  linarith

end

end GaloisForLFunctions.MatomakiRadziwill
