import GaloisForLFunctions.RHTower.Sieve.MoebiusAveragedMeanSquareAllLengths
import GaloisForLFunctions.RHTower.Sieve.DyadicMeanSquareTail

/-!
# Integer-start Möbius windows

The plain Möbius spectral head controls additive windows after a geometric partition of their
starting points. The partition width tends to zero with the actual spectral error, preserving
uniformity over every integer window length between `log N` and `N`.
-/

namespace TwinPrime

open Filter Topology Finset MeasureTheory RHTower.Sieve

noncomputable section

private def integerHeadSeed (x : ℝ) : ℝ := Real.log (Real.sqrt x / 4)

private theorem tendsto_integerHeadSeed : Tendsto integerHeadSeed atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_sqrt_atTop.atTop_div_const (by norm_num))

private theorem integerHeadSeed_le_sqrt :
    ∀ᶠ x : ℝ in atTop, integerHeadSeed x ≤ Real.sqrt x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 4 by positivity)
  dsimp [integerHeadSeed]
  linarith

private def integerRealHead (x : ℝ) : ℝ :=
  ∫ w in Set.Icc
      (-(headT₀ x (integerHeadSeed x) (Real.sqrt (integerHeadSeed x))))
      (headT₀ x (integerHeadSeed x) (Real.sqrt (integerHeadSeed x))),
    ‖logPoly moebiusCoeff (fibreIndex x (integerHeadSeed x)) w‖ ^ 2

/-- The normalized plain Möbius spectral head tends to zero. -/
private theorem tendsto_integerRealHead_div :
    Tendsto (fun x : ℝ => integerRealHead x /
      ((⌊Real.sqrt x + integerHeadSeed x⌋₊ : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have htop := headTop_facts
  obtain ⟨A₀, δ₀, Ctot, -, hCtot, hhigh, hlim⟩ :=
    exists_top_high_bound (a := 19 / 20) (b := 99 / 100) (c' := 3) (A₃ := 8)
      (top := headTop) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (htop.mono fun x hx => hx.1)
      (htop.mono fun x hx => hx.2.1) (htop.mono fun x hx => hx.2.2)
  obtain ⟨K, -, hdiscr⟩ := exists_setIntegral_disc_normSq_logPoly_moebius_le_rate
  have hρ : Tendsto (fun x => (Real.log x) ^ ((1497 : ℝ) / 200)
      * topHighRho A₀ δ₀ Ctot (19 / 20) (99 / 100) 3 8 headTop x) atTop (𝓝 0) :=
    hlim _ (by norm_num) (by norm_num)
  have hbudget := tendsto_headBudget (K := K) tendsto_integerHeadSeed hρ
  have hkey := eventually_integral_head_le_budget tendsto_integerHeadSeed
    integerHeadSeed_le_sqrt hCtot hdiscr hhigh
  refine squeeze_zero' ?_ ?_ hbudget
  · filter_upwards with x
    exact div_nonneg (setIntegral_nonneg measurableSet_Icc fun w _ => by positivity)
      (sq_nonneg _)
  · filter_upwards [hkey, eventually_ge_atTop (4 : ℝ),
      tendsto_integerHeadSeed.eventually_ge_atTop 1] with x hx hx4 hh1
    have hs : (2 : ℝ) ≤ Real.sqrt x := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
      exact Real.sqrt_le_sqrt hx4
    have hM : (0 : ℝ) < ((⌊Real.sqrt x + integerHeadSeed x⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (Real.sqrt x + integerHeadSeed x)
      linarith
    rw [div_le_iff₀ (by positivity), mul_comm]
    exact hx

/-- The polynomial includes every window starting in `[N,2N)` of length at most `N`. -/
def integerWindowHeadLength (N : ℕ) : ℕ := ⌊4 * (N : ℝ) + Real.log N⌋₊

/-- The head height is `M / sqrt(log N)` at positive logarithms. -/
def integerWindowHeadHeight (N : ℕ) : ℝ :=
  (integerWindowHeadLength N : ℝ) / Real.log N * Real.sqrt (Real.log N)

/-- The actual Möbius spectral mass at the selected height. -/
def integerWindowHead (N : ℕ) : ℝ :=
  ∫ w in Set.Icc (-(integerWindowHeadHeight N)) (integerWindowHeadHeight N),
    ‖logPoly moebiusCoeff (Finset.Icc 1 (integerWindowHeadLength N)) w‖ ^ 2

theorem integerWindowHead_nonneg (N : ℕ) : 0 ≤ integerWindowHead N :=
  setIntegral_nonneg measurableSet_Icc fun w _ => by positivity

private theorem integerRealHead_nat (N : ℕ) :
    integerRealHead ((4 * (N : ℝ)) ^ 2) = integerWindowHead N := by
  have hs : Real.sqrt ((4 * (N : ℝ)) ^ 2) = 4 * (N : ℝ) :=
    Real.sqrt_sq (by positivity)
  have hh : integerHeadSeed ((4 * (N : ℝ)) ^ 2) = Real.log N := by
    rw [integerHeadSeed, hs]
    congr 1
    ring
  simp only [integerRealHead, hh, headT₀, headG, hs, fibreIndex,
    integerWindowHead, integerWindowHeadHeight, integerWindowHeadLength]

/-- Relative head mass vanishes along the integer horizons. -/
theorem tendsto_integerWindowHead_div :
    Tendsto (fun N : ℕ => integerWindowHead N / (integerWindowHeadLength N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => (4 * (N : ℝ)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have h := tendsto_integerRealHead_div.comp hx
  refine h.congr fun N => ?_
  rw [Function.comp_apply, integerRealHead_nat]
  have hs : Real.sqrt ((4 * (N : ℝ)) ^ 2) = 4 * (N : ℝ) :=
    Real.sqrt_sq (by positivity)
  simp only [integerHeadSeed, hs, show 4 * (N : ℝ) / 4 = N by ring,
    integerWindowHeadLength]

/-- The three paid costs: coefficient mass, spectral tail, and actual spectral head. -/
def integerWindowError (N : ℕ) : ℝ :=
  270 / Real.log N + 180 / Real.sqrt (Real.log N)
    + 81 * (integerWindowHead N / (integerWindowHeadLength N : ℝ) ^ 2)

theorem tendsto_integerWindowError : Tendsto integerWindowError atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h₁ : Tendsto (fun N : ℕ => 270 / Real.log N) atTop (𝓝 0) :=
    hlog.const_div_atTop 270
  have h₂ : Tendsto (fun N : ℕ => 180 / Real.sqrt (Real.log N)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp hlog).const_div_atTop 180
  unfold integerWindowError
  simpa only [mul_zero, add_zero] using
    (h₁.add h₂).add (tendsto_integerWindowHead_div.const_mul 81)
private theorem integerWindowHeadLength_bounds {N : ℕ} (hN : 0 < N)
    (hlog : 1 ≤ Real.log N) :
    4 * (N : ℝ) ≤ integerWindowHeadLength N ∧
      (integerWindowHeadLength N : ℝ) ≤ 5 * N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : 4 * N ≤ integerWindowHeadLength N := by
    unfold integerWindowHeadLength
    apply Nat.le_floor
    push_cast
    linarith
  have hhi := Nat.floor_le (show 0 ≤ 4 * (N : ℝ) + Real.log N by positivity)
  have hl : Real.log N ≤ (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos hNr
    linarith
  constructor
  · exact_mod_cast hlo
  · dsimp [integerWindowHeadLength]
    linarith

/-- The actual spectral head pays each logarithmic window before the starting-point partition. -/
private theorem integerWindow_logWindowSum_le {N ℓ : ℕ} (hN : 0 < N)
    (hlog : 1 ≤ Real.log N) (hlow : Real.log N ≤ ℓ) (hhigh : ℓ ≤ N)
    {Y : ℝ} (hY : (N : ℝ) ≤ Y) (E : Set ℝ) :
    (∫ u in E, ‖logWindowSum moebiusCoeff (Finset.Icc 1 (integerWindowHeadLength N))
      (Real.log (1 + (ℓ : ℝ) / Y)) u‖ ^ 2)
      ≤ (ℓ : ℝ) ^ 2 * integerWindowError N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓ : (0 : ℝ) < ℓ := by linarith
  have hlog0 : 0 < Real.log N := by linarith
  have hs : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog0
  have hss : Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N :=
    Real.mul_self_sqrt hlog0.le
  have hsle : Real.sqrt (Real.log N) ≤ Real.log N := by
    nlinarith only [hlog, hs, hss]
  obtain ⟨hMlo, hMhi⟩ := integerWindowHeadLength_bounds hN hlog
  set M : ℝ := (integerWindowHeadLength N : ℝ) with hMdef
  have hM0 : 0 < M := by dsimp [M]; linarith
  have hℓN : (ℓ : ℝ) ≤ N := by exact_mod_cast hhigh
  set G : ℝ := M / (3 * ℓ) with hGdef
  set ω : ℝ := 3 * ℓ / Real.sqrt (Real.log N) with hωdef
  have hG1 : 1 ≤ G := by
    rw [hGdef, one_le_div (by positivity)]
    dsimp [M]
    linarith
  have hω1 : 1 ≤ ω := by
    rw [hωdef, one_le_div hs]
    linarith
  have hheight : integerWindowHeadHeight N = G * ω := by
    have hleft : M / Real.log N * Real.sqrt (Real.log N)
        = M / Real.sqrt (Real.log N) := by
      apply (eq_div_iff hs.ne').mpr
      rw [mul_assoc, hss, div_mul_cancel₀ _ hlog0.ne']
    rw [integerWindowHeadHeight, ← hMdef, hleft, hGdef, hωdef]
    field_simp
  have hGT : G ≤ integerWindowHeadHeight N := by
    rw [hheight]
    exact le_mul_of_one_le_right (by linarith) hω1
  have hT0 : 0 < integerWindowHeadHeight N := lt_of_lt_of_le (by linarith) hGT
  set α : ℝ := 5 * Real.pi / 2 * M
    + 5 * Real.exp 1 / 2 * M * M / integerWindowHeadHeight N with hαdef
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hI : 0 ≤ integerWindowHead N := integerWindowHead_nonneg N
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 (integerWindowHeadLength N) := by simp
  have hsN : ∀ n ∈ Finset.Icc 1 (integerWindowHeadLength N), n ≤ integerWindowHeadLength N :=
    fun n hn => (Finset.mem_Icc.mp hn).2
  have haff := integral_Icc_normSq_logPoly_affine_of_head moebiusCoeff
    norm_moebius_complex_le_one_moebiusHeadGate hs0 hsN hG1 hGT hI
    (show (∫ w in Set.Icc (-(integerWindowHeadHeight N)) (integerWindowHeadHeight N),
      ‖logPoly moebiusCoeff (Finset.Icc 1 (integerWindowHeadLength N)) w‖ ^ 2)
        ≤ integerWindowHead N from le_rfl)
  have haff' : ∀ T : ℝ, G ≤ T →
      (∫ w in Set.Icc (-T) T,
        ‖logPoly moebiusCoeff (Finset.Icc 1 (integerWindowHeadLength N)) w‖ ^ 2)
        ≤ α * T + integerWindowHead N := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel, hαdef, hMdef] using haff
  set δ : ℝ := Real.log (1 + (ℓ : ℝ) / Y) with hδdef
  have hY0 : 0 < Y := lt_of_lt_of_le hNr hY
  have hδ0 : 0 < δ := by
    apply Real.log_pos
    have hdiv : 0 < (ℓ : ℝ) / Y := div_pos hℓ hY0
    linarith only [hdiv]
  have hδN : δ ≤ (ℓ : ℝ) / N := by
    have hlog' := Real.log_le_sub_one_of_pos (show 0 < 1 + (ℓ : ℝ) / Y by positivity)
    have hdiv := div_le_div_of_nonneg_left hℓ.le hNr hY
    dsimp [δ]
    linarith
  have hδ : δ ≤ 2 * (3 * ℓ) / M := by
    refine hδN.trans ?_
    rw [div_le_div_iff₀ hNr hM0]
    have hm := mul_le_mul_of_nonneg_left hMhi hℓ.le
    dsimp [M]
    nlinarith only [hm, mul_nonneg hℓ.le hNr.le]
  set C : ℝ := 2 * δ ^ 2 * (α * G + integerWindowHead N)
    + (4 * α / (Real.pi ^ 2 * G)
      + 4 * integerWindowHead N / (3 * Real.pi ^ 2 * G ^ 2)) with hCdef
  have hgal : (∫ u in E,
      ‖logWindowSum moebiusCoeff (Finset.Icc 1 (integerWindowHeadLength N)) δ u‖ ^ 2) ≤ C := by
    refine (setIntegral_le_integral
      (integrable_normSq_logWindowSum _ _ _)
      (Filter.Eventually.of_forall fun u => sq_nonneg _)).trans ?_
    exact gallagher_split_integral_dyadic _ _ hδ0 (by linarith) haff'
  have hbudget := headBudget_le (M := M) (δ := δ) (h := 3 * ℓ) (ω := ω)
    (B := integerWindowHead N) hM0 (by linarith) hω1 hδ0.le hδ hI
  have hbudget' : C / (3 * ℓ : ℝ) ^ 2
      ≤ 90 / (3 * ℓ) + 60 / ω + 9 * (integerWindowHead N / M ^ 2) := by
    simpa only [hCdef, hαdef, hheight, hGdef] using hbudget
  have hid : 9 * (90 / (3 * ℓ) + 60 / ω + 9 * (integerWindowHead N / M ^ 2))
      = 270 / (ℓ : ℝ) + 180 * Real.sqrt (Real.log N) / ℓ
        + 81 * (integerWindowHead N / M ^ 2) := by
    rw [hωdef]
    field_simp
    ring
  have hscale : C / (ℓ : ℝ) ^ 2 = 9 * (C / (3 * ℓ : ℝ) ^ 2) := by
    field_simp
    ring
  have hfirst : 270 / (ℓ : ℝ) ≤ 270 / Real.log N :=
    div_le_div_of_nonneg_left (by norm_num) hlog0 hlow
  have hsecond : 180 * Real.sqrt (Real.log N) / ℓ ≤ 180 / Real.sqrt (Real.log N) := by
    rw [div_le_div_iff₀ hℓ hs]
    nlinarith only [hss, hlow]
  have hC : C / (ℓ : ℝ) ^ 2 ≤ integerWindowError N := by
    have hb := mul_le_mul_of_nonneg_left hbudget' (by norm_num : (0 : ℝ) ≤ 9)
    rw [← hscale, hid] at hb
    dsimp [integerWindowError]
    rw [← hMdef]
    linarith
  have hC' := (div_le_iff₀ (sq_pos_of_pos hℓ)).mp hC
  exact hgal.trans (by nlinarith only [hC'])

private theorem geometric_partition_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 ≤ (1 + ε) ^ ⌈1 / ε⌉₊ ∧ (1 + ε) ^ ⌈1 / ε⌉₊ ≤ 9 ∧
      (⌈1 / ε⌉₊ : ℝ) ≤ 2 / ε := by
  set K : ℕ := ⌈1 / ε⌉₊ with hKdef
  have hKlo : 1 / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hKhi : (K : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKe1 : 1 ≤ (K : ℝ) * ε := by
    have h := mul_le_mul_of_nonneg_right hKlo hε.le
    rwa [div_mul_cancel₀ _ hε.ne'] at h
  have hKe2 : (K : ℝ) * ε ≤ 2 := by
    have h := mul_lt_mul_of_pos_right hKhi hε
    rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at h
    linarith
  have hBern : ∀ k : ℕ, 1 + (k : ℝ) * ε ≤ (1 + ε) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 + ε by linarith)
        rw [pow_succ]
        push_cast
        nlinarith only [h, mul_nonneg (Nat.cast_nonneg k) (sq_nonneg ε)]
  refine ⟨by linarith [hBern K], ?_, (le_div_iff₀ hε).mpr hKe2⟩
  have hbase : 1 + ε ≤ Real.exp ε := by linarith [Real.add_one_le_exp ε]
  have hexp2 : Real.exp (2 : ℝ) ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have := Real.exp_one_lt_d9
    nlinarith only [this, Real.exp_pos 1]
  calc (1 + ε) ^ K ≤ (Real.exp ε) ^ K :=
      pow_le_pow_left₀ (by linarith) hbase K
    _ = Real.exp ((K : ℝ) * ε) := (Real.exp_nat_mul ε K).symm
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr hKe2
    _ ≤ 9 := hexp2

/-- An explicit vanishing receiver rate, defined from the actual spectral mass. -/
def integerWindowRate (N : ℕ) : ℝ :=
  36 * Real.sqrt (integerWindowError N) + 144 * integerWindowError N

theorem tendsto_integerWindowRate : Tendsto integerWindowRate atTop (𝓝 0) := by
  have hs := (Real.continuous_sqrt.tendsto 0).comp tendsto_integerWindowError
  unfold integerWindowRate
  simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero, add_zero] using
    (hs.const_mul 36).add (tendsto_integerWindowError.const_mul 144)

/-- Integer-start Möbius mean square is uniformly small for `log N ≤ ℓ ≤ N`. -/
theorem eventually_dyadicMeanSquare_moebius_le_integerWindowRate :
    ∀ᶠ N : ℕ in atTop, ∀ ℓ : ℕ, Real.log N ≤ ℓ → ℓ ≤ N →
      dyadicMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ℓ N (2 * N - 1)
        ≤ integerWindowRate N * N * (ℓ : ℝ) ^ 2 := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop 1,
    tendsto_integerWindowError.eventually_le_const (show (0 : ℝ) < 1 by norm_num)]
    with N hN hlog1 hE1
  intro ℓ hlow hhigh
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hℓ : (0 : ℝ) < ℓ := by linarith
  have hℓn : 0 < ℓ := by exact_mod_cast hℓ
  have hlog0 : 0 < Real.log N := by linarith
  have hslog : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog0
  have hI : 0 ≤ integerWindowHead N / (integerWindowHeadLength N : ℝ) ^ 2 :=
    div_nonneg (integerWindowHead_nonneg N) (sq_nonneg _)
  have hEpos : 0 < integerWindowError N := by
    have hfirst : 0 < 270 / Real.log N := by positivity
    have hsecond : 0 ≤ 180 / Real.sqrt (Real.log N) := by positivity
    dsimp [integerWindowError]
    linarith
  have hinvE : 1 / Real.log N ≤ integerWindowError N := by
    have hfirst : 1 / Real.log N ≤ 270 / Real.log N :=
      div_le_div_of_nonneg_right (by norm_num) hlog0.le
    have hsecond : 0 ≤ 180 / Real.sqrt (Real.log N) := by positivity
    dsimp [integerWindowError]
    linarith
  set ε : ℝ := Real.sqrt (integerWindowError N) with hεdef
  have hε : 0 < ε := Real.sqrt_pos.mpr hEpos
  have hεsq : ε ^ 2 = integerWindowError N := Real.sq_sqrt hEpos.le
  have hε1 : ε ≤ 1 := by
    have h := Real.sqrt_le_sqrt hE1
    simpa only [Real.sqrt_one] using h
  have hEe : integerWindowError N ≤ ε := by nlinarith only [hεsq, hε1, hε]
  set K : ℕ := ⌈1 / ε⌉₊ with hKdef
  obtain ⟨hpow2, hpow9, hK⟩ := geometric_partition_bounds hε hε1
  have hKn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hpow0 : 0 ≤ (1 + ε) ^ K := by positivity
  have hcover : (N : ℝ) + ((2 * N - 1 + 1 - N : ℕ) : ℝ) ≤ (N : ℝ) * (1 + ε) ^ K := by
    have hidx : 2 * N - 1 + 1 - N = N := by omega
    rw [hidx]
    nlinarith only [hpow2, hNr]
  have hMlo : 4 * N ≤ integerWindowHeadLength N := by
    have h := (integerWindowHeadLength_bounds hN0 hlog1).1
    exact_mod_cast h
  have hM : 2 * N - 1 + 1 + ℓ < integerWindowHeadLength N + 1 := by omega
  have hcoef : (fun n : ℕ => (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ)) = moebiusCoeff := by
    funext n
    simp only [moebiusCoeff, Complex.ofReal_intCast]
  have hraw := dyadicMeanSquare_le_gen
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) abs_moebius_real_le_one
    (M := integerWindowHeadLength N) (K' := K) (G := (ℓ : ℝ) ^ 2 * integerWindowError N)
    hℓn hN0 (by omega) hε.le (by positivity) hM hcover (by
      intro Y hY E
      rw [hcoef]
      exact integerWindow_logWindowSum_le hN0 hlog1 hlow hhigh hY E)
  have hlogε : Real.log (1 + ε) ≤ ε := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ε by linarith)
    linarith
  have hlogε0 : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
  have hcost : 0 ≤ 2 * integerWindowError N
      + 2 * (ε + 1 / (ℓ : ℝ)) ^ 2 * Real.log (1 + ε) := by positivity
  have hmain :
      dyadicMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ℓ N (2 * N - 1)
          / ((N : ℝ) * (ℓ : ℝ) ^ 2)
        ≤ 36 * ε + 144 * integerWindowError N := by
    calc _ ≤ ((N : ℝ) * (1 + ε) ^ K)
            * ((K : ℝ) * blockCostG (ℓ : ℝ) ε ((ℓ : ℝ) ^ 2 * integerWindowError N))
              / ((N : ℝ) * (ℓ : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hraw (by positivity)
      _ = (1 + ε) ^ K * (K : ℝ) *
          (2 * integerWindowError N + 2 * (ε + 1 / (ℓ : ℝ)) ^ 2 * Real.log (1 + ε)) := by
            rw [blockCostG]
            field_simp
      _ ≤ 9 * (2 / ε) * (2 * integerWindowError N + 2 * (ε + 1 / (ℓ : ℝ)) ^ 2 * ε) := by
            apply mul_le_mul
            · exact mul_le_mul hpow9 hK hKn (by norm_num)
            · nlinarith only [mul_le_mul_of_nonneg_left hlogε
                (show 0 ≤ 2 * (ε + 1 / (ℓ : ℝ)) ^ 2 by positivity)]
            · exact hcost
            · positivity
      _ = 36 * (integerWindowError N / ε) + 36 * (ε + 1 / (ℓ : ℝ)) ^ 2 := by
            field_simp
            ring
      _ ≤ 36 * ε + 144 * integerWindowError N := by
            have heq : integerWindowError N / ε = ε := by
              apply (div_eq_iff hε.ne').mpr
              nlinarith only [hεsq]
            have hinv : 1 / (ℓ : ℝ) ≤ ε :=
              (one_div_le_one_div_of_le hlog0 hlow).trans (hinvE.trans hEe)
            have hsq : (ε + 1 / (ℓ : ℝ)) ^ 2 ≤ 4 * integerWindowError N := by
              have h := pow_le_pow_left₀ (show 0 ≤ ε + 1 / (ℓ : ℝ) by positivity)
                (show ε + 1 / (ℓ : ℝ) ≤ 2 * ε by linarith) 2
              nlinarith only [h, hεsq]
            rw [heq]
            linarith
  have hfinal := (div_le_iff₀ (show 0 < (N : ℝ) * (ℓ : ℝ) ^ 2 by positivity)).mp hmain
  simpa only [integerWindowRate, hεdef, mul_assoc] using hfinal

end

end TwinPrime
