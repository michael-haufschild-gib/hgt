import GaloisForLFunctions.RHTower.ZetaGateProductAFEHighBlockPieces
import GaloisForLFunctions.RHTower.HighBlockAsymptotics

/-!
# The high blocks of the crude mollified mean square

For `a ≥ U^{1/8}` the block `[a, v]`, `v ≤ 2a`, is windowed with the parameters
`u = a^{1/100}`, `x = a`, `η = u^{95}`, and the mollifier `Ψ = Σ_{n ≤ N} (b_N(n)/log N) n^{-s}` of
length `N = ⌊U^{1/100}⌋`.  The block inequality gives

  `∫_a^v ‖ζΨ‖² ≤ (c₀(R) + ε)(v − a) + ε U / log U`

for every displacement `d ∈ [R/log U, 2R/log U]` once `U` is large, with
`c₀(R) = 200 M_R / R`, `M_R = 128 e C_L² e^{R/25 + 4R}` (`C_L` the coprime log-Möbius constant).
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## The real window -/

theorem blockWindow_eq_zero_of_notMem {p q η : ℝ} (hη : 0 < η) {t : ℝ}
    (ht : t ∉ Set.Icc (p - η) (q + η)) : blockWindow p q η t = 0 := by
  have := blockWindowC_eq_zero hη ht
  unfold blockWindowC at this
  exact_mod_cast this

theorem integrable_blockWindow_mul_real {p q η : ℝ} (hη : 0 < η) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (p - η) (q + η))) :
    Integrable (fun t => blockWindow p q η t * g t) := by
  have hcont : ContinuousOn (fun t => blockWindow p q η t * g t) (Set.Icc (p - η) (q + η)) :=
    (contDiff_blockWindow p q η).continuous.continuousOn.mul hg
  refine (hcont.integrableOn_compact isCompact_Icc).integrable_of_forall_notMem_eq_zero ?_
  intro t ht
  rw [blockWindow_eq_zero_of_notMem hη ht, zero_mul]

/-- The interval integral of a nonnegative function is at most its window integral. -/
theorem intervalIntegral_le_window_integral {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (p - η) (q + η))) (hg0 : ∀ t, 0 ≤ g t) :
    ∫ t in p..q, g t ≤ ∫ t, blockWindow p q η t * g t := by
  rw [intervalIntegral.integral_of_le hpq]
  calc ∫ t in Set.Ioc p q, g t = ∫ t in Set.Ioc p q, blockWindow p q η t * g t := by
        refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
        rw [blockWindow_eq_one hη ht.1.le ht.2, one_mul]
    _ ≤ ∫ t, blockWindow p q η t * g t :=
        setIntegral_le_integral (integrable_blockWindow_mul_real hη hg)
          (Filter.Eventually.of_forall fun t => mul_nonneg (blockWindow_nonneg p q η t) (hg0 t))

/-- `‖ζΨ‖²` is continuous away from height zero. -/
theorem continuousOn_normSq_zeta_mul_edPoly {d p q η : ℝ} (hL : 4 ≤ p - η) (b : ℕ → ℂ) (N : ℕ) :
    ContinuousOn (fun t : ℝ => ‖riemannZeta (displacedLinePt d t)
      * edPoly b (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2) (Set.Icc (p - η) (q + η)) := by
  intro t ht
  have ht0 : t ≠ 0 := by
    have := ht.1
    intro h0
    rw [h0] at this
    linarith
  have hne : displacedLinePt d t ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [displacedLinePt] at this
    exact ht0 this
  have hζ : ContinuousAt (fun t : ℝ => riemannZeta (displacedLinePt d t)) t :=
    ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
      (continuous_displacedLinePt d).continuousAt
  have hΨ : ContinuousAt (fun t : ℝ => edPoly b (Finset.Icc 1 N) (displacedLinePt d t)) t :=
    ContinuousAt.comp (g := edPoly b (Finset.Icc 1 N))
      ((differentiable_edPoly b fun n hn => (Finset.mem_Icc.mp hn).1) _).continuousAt
      (continuous_displacedLinePt d).continuousAt
  exact ((hζ.mul hΨ).norm.pow 2).continuousWithinAt

/-! ## The mollifier length `⌊U^{1/100}⌋` -/

/-- The mollifier length `N = ⌊U^{1/100}⌋`. -/
def mollN (U : ℝ) : ℕ := ⌊U ^ ((1 : ℝ) / 100)⌋₊

theorem mollN_le {U : ℝ} (hU : 0 ≤ U) : (mollN U : ℝ) ≤ U ^ ((1 : ℝ) / 100) :=
  Nat.floor_le (by positivity)

theorem mollN_gt (U : ℝ) : U ^ ((1 : ℝ) / 100) - 1 < (mollN U : ℝ) := by
  have := Nat.lt_floor_add_one (U ^ ((1 : ℝ) / 100))
  unfold mollN
  linarith

/-! ## The main-term constant -/

/-- `M_R = 128 e C_L² e^{R/25} e^{4R}`. -/
def mainStar (R : ℝ) : ℝ :=
  128 * Real.exp 1 * Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (R / 25) * Real.exp (4 * R)

theorem mainStar_nonneg (R : ℝ) : 0 ≤ mainStar R := by
  unfold mainStar
  positivity

/-- `y^{2d} ≤ 2 e^{4R}` for `0 ≤ y ≤ 3U` and `d log U ≤ 2R`, `d ≤ 1/8`. -/
theorem rpow_two_mul_le_two_exp {d U y R : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hU1 : 1 ≤ U)
    (hdU : d * Real.log U ≤ 2 * R) (hy0 : 0 ≤ y) (hy : y ≤ 3 * U) :
    y ^ (2 * d) ≤ 2 * Real.exp (4 * R) := by
  have h3U : 0 < 3 * U := by linarith
  calc y ^ (2 * d) ≤ (3 * U) ^ (2 * d) := Real.rpow_le_rpow hy0 hy (by linarith)
    _ = Real.exp (Real.log (3 * U) * (2 * d)) := Real.rpow_def_of_pos h3U _
    _ ≤ 2 * Real.exp (4 * R) := by
        rw [Real.log_mul (by norm_num) (by linarith)]
        have hlog3 : Real.log 3 ≤ 4 * Real.log 2 := by
          rw [← Real.log_rpow (by norm_num)]
          exact Real.log_le_log (by norm_num) (by norm_num)
        have hlog3' : Real.log 3 * (2 * d) ≤ Real.log 2 := by
          have h0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith
        calc Real.exp ((Real.log 3 + Real.log U) * (2 * d))
            = Real.exp (Real.log 3 * (2 * d)) * Real.exp (Real.log U * (2 * d)) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp (Real.log 2) * Real.exp (4 * R) :=
              mul_le_mul (Real.exp_le_exp.mpr hlog3') (Real.exp_le_exp.mpr (by nlinarith))
                (Real.exp_pos _).le (Real.exp_pos _).le
          _ = 2 * Real.exp (4 * R) := by rw [Real.exp_log (by norm_num)]

/-- `((q+η)/2π)^{2d} ≤ 2 e^{4R}` on a block below `U` with `d log U ≤ 2R`. -/
theorem chi_weight_factor_le {d U q η R : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hU1 : 1 ≤ U)
    (hdU : d * Real.log U ≤ 2 * R) (hq0 : 0 ≤ q + η) (hq : q + η ≤ 3 * U) :
    ((q + η) / (2 * Real.pi)) ^ (2 * d) ≤ 2 * Real.exp (4 * R) := by
  have h1 : (q + η) / (2 * Real.pi) ≤ 3 * U := by
    have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc (q + η) / (2 * Real.pi) ≤ (q + η) / 1 :=
          div_le_div_of_nonneg_left hq0 one_pos hπ
      _ = q + η := div_one _
      _ ≤ 3 * U := hq
  exact rpow_two_mul_le_two_exp hd hd8 hU1 hdU (by positivity) h1

/-- `N^{2d} ≤ e^{R/25}` for `N ≤ U^{1/100}` and `d log U ≤ 2R`. -/
theorem mollN_rpow_le {d U R : ℝ} (hd : 0 < d) (hU1 : 1 ≤ U) (hdU : d * Real.log U ≤ 2 * R)
    {N : ℕ} (hN : (N : ℝ) ≤ U ^ ((1 : ℝ) / 100)) :
    (N : ℝ) ^ (2 * d) ≤ Real.exp (R / 25) := by
  have hU0 : 0 < U := by linarith
  calc (N : ℝ) ^ (2 * d) ≤ (U ^ ((1 : ℝ) / 100)) ^ (2 * d) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)
    _ = Real.exp (Real.log U * ((1 / 100) * (2 * d))) := by
        rw [← Real.rpow_mul hU0.le, Real.rpow_def_of_pos hU0]
    _ ≤ Real.exp (R / 25) := by
        apply Real.exp_le_exp.mpr
        nlinarith

/-- `(1 + L)/L² ≤ 400 / L_U` when `1 ≤ L` and `L_U ≤ 200 L`. -/
theorem log_factor_le {L LU : ℝ} (hL1 : 1 ≤ L) (hLU : 0 < LU) (hNU : LU ≤ 200 * L) :
    (1 + L) / L ^ 2 ≤ 400 / LU := by
  have hL0 : 0 < L := by linarith
  rw [div_le_div_iff₀ (by positivity) hLU]
  have : (1 + L) * LU ≤ (2 * L) * (200 * L) :=
    mul_le_mul (by linarith) hNU hLU.le (by linarith)
  nlinarith

/-- `1/(2d) ≤ log U/(2R)` when `R ≤ d log U`. -/
theorem inv_two_mul_le {d U R : ℝ} (hd : 0 < d) (hR : 0 < R) (hRd : R ≤ d * Real.log U) :
    1 / (2 * d) ≤ Real.log U / (2 * R) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## The high-block bound -/

/-- **The high-block bound for the crude mollified mean square.**  For `U` large, every
displacement `d ∈ [R/log U, 2R/log U]` and every block `[a, v]` with `U^{1/8} ≤ a ≤ v ≤ 2a`,
`v ≤ U`, the mean square of `ζΨ` on the displaced line is at most `(c₀ + ε)(v − a) + ε a`. -/
theorem exists_highBlock_bound_productAFE {R : ℝ} (hR : 0 < R) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log U ≤ 2 * R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((1 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (hbCoeff (mollN U)) (Finset.Icc 1 (mollN U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c₀ + ε) * (v - a) + ε * a := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 20) (by norm_num)
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ :=
    exists_tsum_dualOffDiagTerm_le_split 20 (K'' := 40) (by norm_num)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_smoothDiagonal_left_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_dualDiagonal_left_le
  have hM0 := mainStar_nonneg R
  refine ⟨200 * mainStar R / R, by positivity, fun ε hε => ?_⟩
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 800), eventually_ge_atTop (Real.exp 200),
    eventually_ge_atTop (Real.exp (1200 * mainStar R / ε)),
    eventually_const_mul_rpow_neg_le (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R))
      ((1 : ℝ) / 160) (by norm_num) (half_pos hε),
    eventually_const_mul_rpow_neg_le (4 * (200 * mainStar R / R + ε) / ε) ((1 : ℝ) / 160)
      (by norm_num) one_pos]
    with U hU2 hUe hUM hUerr hUη
  intro d hd hd8 hRd hdU a v ha haU hav hv2 hvU
  -- consequences of `2^(800 : ℕ) ≤ U`; the hypothesis itself is cleared (its numeral is too large for
  -- the linear-arithmetic preprocessing)
  have hU1 : (1 : ℝ) ≤ U := le_trans (one_le_pow₀ (by norm_num)) hU2
  have hU100 : (256 : ℝ) ≤ U ^ ((1 : ℝ) / 100) := by
    have e : ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 100) = 256 := by
      rw [← Real.rpow_natCast (2 : ℝ) 800, ← Real.rpow_mul (by norm_num),
        show ((800 : ℕ) : ℝ) * (1 / 100) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
  have h2100 : (2 : ℝ) ^ 100 ≤ a := by
    have e : ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ 100 := by
      rw [← Real.rpow_natCast (2 : ℝ) 800, ← Real.rpow_mul (by norm_num),
        show ((800 : ℕ) : ℝ) * (1 / 8) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (2 : ℝ) ^ 100 = ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 8) := e.symm
      _ ≤ U ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
      _ ≤ a := haU
  clear hU2
  have hd4 : d ≤ 1 / 4 := by linarith
  -- facts about `U`
  have hU0 : 0 < U := by linarith
  have hlogU : 200 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 200) hUe
    rwa [Real.log_exp] at this
  have hlogU0 : 0 < Real.log U := by linarith
  have hlogUM : 1200 * mainStar R / ε ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos _) hUM
    rwa [Real.log_exp] at this
  -- the mollifier length
  have hNle : (mollN U : ℝ) ≤ U ^ ((1 : ℝ) / 100) := mollN_le hU0.le
  have hNgt := mollN_gt U
  have hN2 : 2 ≤ mollN U := by
    have : (2 : ℝ) ≤ mollN U := by linarith
    exact_mod_cast this
  have hNhalf : U ^ ((1 : ℝ) / 100) / 2 ≤ mollN U := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log U / 200 ≤ Real.log (mollN U) := by
    have h1 : Real.log (U ^ ((1 : ℝ) / 100) / 2) ≤ Real.log (mollN U) :=
      Real.log_le_log (by positivity) hNhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hU0] at h1
    linarith
  have hlogN1 : 1 ≤ Real.log (mollN U) := by linarith
  -- the parameter `u = a^{1/100}`
  have ha0 : 0 < a := by linarith

  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = a ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hu2 : 2 ≤ u := by
    have e : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 100, ← Real.rpow_mul (by norm_num),
        show ((100 : ℕ) : ℝ) * (1 / 100) = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [hudef, ← e]
    exact Real.rpow_le_rpow (by positivity) h2100 (by norm_num)
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hNu : (mollN U : ℝ) ≤ u ^ 8 := by
    have hUa : U ≤ a ^ 8 := by
      calc U = (U ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
            norm_num
        _ ≤ a ^ 8 := pow_le_pow_left₀ (by positivity) haU 8
    calc (mollN U : ℝ) ≤ U ^ ((1 : ℝ) / 100) := hNle
      _ ≤ (a ^ 8) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hU0.le hUa (by norm_num)
      _ = u ^ 8 := by
          rw [hudef, ← Real.rpow_natCast a 8, ← Real.rpow_mul ha0.le, ← Real.rpow_natCast,
            ← Real.rpow_mul ha0.le]
          norm_num
  have hu5 : U ^ ((1 : ℝ) / 160) ≤ u ^ 5 := by
    calc U ^ ((1 : ℝ) / 160) = (U ^ ((1 : ℝ) / 8)) ^ ((1 : ℝ) / 100 * 5) := by
          rw [← Real.rpow_mul hU0.le]
          norm_num
      _ ≤ a ^ ((1 : ℝ) / 100 * 5) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
      _ = u ^ 5 := by
          rw [hudef, Real.rpow_mul ha0.le, ← Real.rpow_natCast]
          norm_num
  -- the block parameters
  have hu100 : u ^ 100 = a := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num
  have hp : a = u ^ 100 := hu100.symm
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu2 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hη : 0 < u ^ 95 := by positivity
  have hL : u ^ 100 / 2 ≤ a - u ^ 95 := by rw [hp]; linarith
  have h4 : (4 : ℝ) ≤ a - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu2 100
    have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
    linarith
  have hq2 : v ≤ 2 * u ^ 100 := by rw [← hp]; exact hv2
  have hηa : u ^ 95 ≤ a := by
    rw [hp]
    linarith [pow_pos hu0 100]
  have hq3 : v + u ^ 95 ≤ 3 * U := by linarith
  have hlen : 0 ≤ v - a + 2 * u ^ 95 := by linarith
  -- Step A: window domination
  have hA := intervalIntegral_le_window_integral hη hav
    (continuousOn_normSq_zeta_mul_edPoly (d := d) (q := v) h4 (hbCoeff (mollN U)) (mollN U))
    (fun t => by positivity)
  -- Step B: the block inequality
  have hB := integral_window_normSq_le hd hd8 (x := u ^ 100) (by positivity) hη h4 hav
    (N := mollN U) (b := hbCoeff (mollN U)) (a := hbReal (mollN U))
    (fun n _ => hbCoeff_eq_ofReal (mollN U) n)
  -- Step C: the main term
  have hS := gcdSum₂_hbReal_le hd.le hN2
  have hζ := norm_riemannZeta_one_add_le (by linarith only [hd] : 0 < 2 * d)
  have hχ := norm_integral_window_chiPairWeight_le hd hd4 hη h4 hav
  have hN2d := mollN_rpow_le hd hU1 hdU hNle
  have hlogf := log_factor_le hlogN1 hlogU0 (by linarith only [hlogN])
  have hχf := chi_weight_factor_le hd hd8 hU1 hdU (by linarith only [hav, ha, hη]) hq3
  have h1d := inv_two_mul_le hd hR hRd
  have hS' : gcdSum₂ d (mollN U) (hbReal (mollN U))
      ≤ Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (R / 25) * (64 * (400 / Real.log U)) := by
    have hCL := Sieve.coprimeLogMoebiusConst_nonneg
    calc gcdSum₂ d (mollN U) (hbReal (mollN U))
        ≤ Sieve.coprimeLogMoebiusConst ^ 2 * (mollN U : ℝ) ^ (2 * d)
          * (64 * (1 + Real.log (mollN U))) / (Real.log (mollN U)) ^ 2 := hS
      _ = Sieve.coprimeLogMoebiusConst ^ 2 * (mollN U : ℝ) ^ (2 * d)
          * (64 * ((1 + Real.log (mollN U)) / (Real.log (mollN U)) ^ 2)) := by ring
      _ ≤ Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (R / 25) * (64 * (400 / Real.log U)) := by
          gcongr
  have hζ' : ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ ≤ 3 / 2 + Real.log U / (2 * R) :=
    hζ.trans (by linarith only [h1d])
  have hχ' : ‖∫ t, blockWindowC a v (u ^ 95) t * chiPairWeight d t‖
      ≤ (v - a + 2 * u ^ 95) * (Real.exp 1 * (2 * Real.exp (4 * R))) := by
    refine hχ.trans ?_
    gcongr
  have hS0 : 0 ≤ gcdSum₂ d (mollN U) (hbReal (mollN U)) := gcdSum₂_nonneg hd.le _ _
  have hmain : gcdSum₂ d (mollN U) (hbReal (mollN U)) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v (u ^ 95) t * chiPairWeight d t‖)
      ≤ (v - a + 2 * u ^ 95) * (200 * mainStar R / R + ε / 2) := by
    have hCL := Sieve.coprimeLogMoebiusConst_nonneg
    calc gcdSum₂ d (mollN U) (hbReal (mollN U)) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v (u ^ 95) t * chiPairWeight d t‖)
        ≤ (Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (R / 25) * (64 * (400 / Real.log U)))
          * ((3 / 2 + Real.log U / (2 * R))
            * ((v - a + 2 * u ^ 95) * (Real.exp 1 * (2 * Real.exp (4 * R))))) := by
          gcongr
      _ = (v - a + 2 * u ^ 95) * (200 * mainStar R / R + 600 * mainStar R / Real.log U) := by
          unfold mainStar
          field_simp
          ring
      _ ≤ (v - a + 2 * u ^ 95) * (200 * mainStar R / R + ε / 2) := by
          have : 600 * mainStar R / Real.log U ≤ ε / 2 := by
            rw [div_le_iff₀ hlogU0]
            have := (div_le_iff₀ hε).mp hlogUM
            linarith only [this]
          gcongr
  -- Step D: the error
  have herr : ∑ h ∈ Finset.Icc 1 (mollN U), ∑ k ∈ Finset.Icc 1 (mollN U),
        ‖hbCoeff (mollN U) h‖ * ‖hbCoeff (mollN U) k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (v - a + 2 * u ^ 95) * (ε / 2) := by
    have hLf : (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * Real.exp (4 * R) :=
      rpow_two_mul_le_two_exp hd hd8 hU1 hdU (by linarith only [h4])
        (by linarith only [hav, hvU, hU1, hη])
    have hpair : ∀ h ∈ Finset.Icc 1 (mollN U), ∀ k ∈ Finset.Icc 1 (mollN U),
        ‖hbCoeff (mollN U) h‖ * ‖hbCoeff (mollN U) k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
        ≤ (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
      intro h hh k hk
      have hb := norm_pairError_le_param hd hd8 hu2 hp hav hq2 hNu hh hk hCA0 hCA hC₁ hC₂ hsplit
        hK₁0 hK₂0 hK₁ hK₂
      have h1 : ‖hbCoeff (mollN U) h‖ * ‖hbCoeff (mollN U) k‖ ≤ 1 := by
        calc ‖hbCoeff (mollN U) h‖ * ‖hbCoeff (mollN U) k‖ ≤ 1 * 1 :=
              mul_le_mul (norm_hbCoeff_le hN2 hh) (norm_hbCoeff_le hN2 hk) (norm_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1
      calc ‖hbCoeff (mollN U) h‖ * ‖hbCoeff (mollN U) k‖
            * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
          ≤ 1 * ((v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 21)) :=
            mul_le_mul h1 hb (norm_nonneg _) zero_le_one
        _ ≤ (v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
            rw [one_mul]
            have h2 : 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * K₂ * (2 * Real.exp (4 * R)) :=
              mul_le_mul_of_nonneg_left hLf (by positivity)
            have : pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)
                ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by linarith only [h2]
            gcongr
    have hsum := Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun k hk => hpair h hh k hk
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul,
      Nat.add_sub_cancel]
    have hN16 : ((mollN U : ℝ)) * (mollN U : ℝ) ≤ u ^ 16 := by
      calc ((mollN U : ℝ)) * (mollN U : ℝ) ≤ u ^ 8 * u ^ 8 :=
            mul_le_mul hNu hNu (Nat.cast_nonneg _) (by positivity)
        _ = u ^ 16 := by ring
    have hK0 : 0 ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by positivity
    have hfin : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 ≤ ε / 2 := by
      have h1 : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5
          ≤ (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) * U ^ (-((1 : ℝ) / 160)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hU0.le]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hu5) hK0
      exact h1.trans hUerr
    calc (mollN U : ℝ) * ((mollN U : ℝ) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)))
        = ((mollN U : ℝ) * (mollN U : ℝ)) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) := by ring
      _ ≤ u ^ 16 * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) :=
          mul_le_mul_of_nonneg_right hN16 (mul_nonneg hlen (div_nonneg hK0 (by positivity)))
      _ = (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5) := by
          have e : u ^ 16 * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)
              = (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 := by
            rw [mul_div_assoc', div_eq_div_iff (pow_ne_zero _ hu0.ne') (pow_ne_zero _ hu0.ne')]
            ring
          rw [← e]
          ring
      _ ≤ (v - a + 2 * u ^ 95) * (ε / 2) := mul_le_mul_of_nonneg_left hfin hlen
  -- Step E: combine
  have hη' : (200 * mainStar R / R + ε) * (2 * u ^ 95) ≤ ε * a := by
    have h1 : 4 * (200 * mainStar R / R + ε) / ε * U ^ (-((1 : ℝ) / 160)) ≤ 1 := hUη
    have hpos : 0 < 4 * (200 * mainStar R / R + ε) / ε := by positivity
    have h2 : 4 * (200 * mainStar R / R + ε) / ε ≤ U ^ ((1 : ℝ) / 160) := by
      rw [Real.rpow_neg hU0.le] at h1
      have hUp : 0 < U ^ ((1 : ℝ) / 160) := by positivity
      rwa [mul_inv_le_iff₀ hUp, one_mul] at h1
    have h3 : 4 * (200 * mainStar R / R + ε) ≤ ε * u ^ 5 := by
      have := (div_le_iff₀ hε).mp (h2.trans hu5)
      linarith only [this]
    have h4' : (200 * mainStar R / R + ε) * (2 * u ^ 95) ≤ (ε / 2) * (u ^ 95 * u ^ 5) := by
      have h5 := mul_le_mul_of_nonneg_right h3 (pow_pos hu0 95).le
      linarith only [h5]
    have hεa : 0 ≤ ε * a := mul_nonneg hε.le ha0.le
    calc (200 * mainStar R / R + ε) * (2 * u ^ 95) ≤ (ε / 2) * (u ^ 95 * u ^ 5) := h4'
      _ = (ε / 2) * a := by rw [← hu100]; ring
      _ ≤ ε * a := by linarith only [hεa]
  calc (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
          * edPoly (hbCoeff (mollN U)) (Finset.Icc 1 (mollN U)) (displacedLinePt d τ)‖ ^ 2)
      ≤ ∫ t, blockWindow a v (u ^ 95) t * ‖riemannZeta (displacedLinePt d t)
          * edPoly (hbCoeff (mollN U)) (Finset.Icc 1 (mollN U)) (displacedLinePt d t)‖ ^ 2 := hA
    _ ≤ _ := hB
    _ ≤ (v - a + 2 * u ^ 95) * (200 * mainStar R / R + ε / 2)
        + (v - a + 2 * u ^ 95) * (ε / 2) := add_le_add hmain herr
    _ = (200 * mainStar R / R + ε) * (v - a) + (200 * mainStar R / R + ε) * (2 * u ^ 95) := by
        ring
    _ ≤ (200 * mainStar R / R + ε) * (v - a) + ε * a := by linarith only [hη']

end RHTower.ZetaGateProductAFE

end
