import GaloisForLFunctions.RHTower.PrimeLagLandauPrimesOnly

/-!
# The growth exponent of the lag sequence at the primes

Under `¬RH`, with `Θ` the supremum of the real parts of the zeros, the lag values at the primes
exceed `M + p^a` for some prime `p`, for every `M` and every `a < Θ − ½`.  Together with the
upper bound `|a_p| ≤ W p^{Θ−½}` this identifies the one-sided growth exponent of `a_p` along the
primes as exactly `Θ − ½`.  The proof is the prime-only Landau argument with the ceiling `M`
replaced by `M + p^a`; the extra Dirichlet series `Σ_p (log p) p^{a−1−s}` continues to
`−ζ'/ζ(1 + s − a)` minus a proper-power series analytic on `Re s > a − ½`, and both are analytic
on every box and ray used, since `a < Θ − ½`.
-/

open Complex Filter Topology Set Metric
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The shifted von Mangoldt series -/

/-- The shifted coefficient `Λ(n) n^a / n`. -/
def shiftedVonMangoldt (a : ℝ) (n : ℕ) : ℝ := vonMangoldt n * (n : ℝ) ^ a / n

theorem shiftedVonMangoldt_term_eq (a : ℝ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun n => (shiftedVonMangoldt a n : ℂ)) s n
      = LSeries.term vonMangoldtC (1 + s - a) n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hne : ∀ z : ℂ, (n : ℂ) ^ z ≠ 0 := fun z => by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hnC h.1
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  unfold shiftedVonMangoldt vonMangoldtC
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_natCast]
  rw [div_div, div_eq_div_iff (mul_ne_zero hnC (hne _)) (hne _)]
  have e : (n : ℂ) ^ (1 + s - (a : ℂ)) = (n : ℂ) * (n : ℂ) ^ s / (n : ℂ) ^ (a : ℂ) := by
    rw [show (1 : ℂ) + s - a = 1 + s - (a : ℂ) from rfl, Complex.cpow_sub _ _ hnC,
      Complex.cpow_add _ _ hnC, Complex.cpow_one]
  rw [e]
  have h1 := hne (a : ℂ)
  have h2 := hne s
  field_simp

theorem shiftedVonMangoldt_LSeriesSummable {a : ℝ} {s : ℂ} (hs : a < s.re) :
    LSeriesSummable (fun n => (shiftedVonMangoldt a n : ℂ)) s := by
  have h : 1 < (1 + s - (a : ℂ)).re := by simp; linarith
  refine (summable_term_vonMangoldtC h).congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · exact (shiftedVonMangoldt_term_eq a s hn.ne').symm

theorem LSeries_shiftedVonMangoldt_eq {a : ℝ} {s : ℂ} (hs : a < s.re) :
    LSeries (fun n => (shiftedVonMangoldt a n : ℂ)) s = -logDeriv riemannZeta (1 + s - a) := by
  have h : 1 < (1 + s - (a : ℂ)).re := by simp; linarith
  rw [← tsum_term_vonMangoldtC_eq h]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · exact shiftedVonMangoldt_term_eq a s hn.ne'

/-- The proper-power part of the shifted series. -/
def properShift (a : ℝ) (n : ℕ) : ℝ := if n.Prime then 0 else shiftedVonMangoldt a n

/-- The prime part of the shifted series. -/
def primeShiftCoeff (a : ℝ) (n : ℕ) : ℝ := if n.Prime then shiftedVonMangoldt a n else 0

theorem shiftedVonMangoldt_eq_primeShift_add_properShift (a : ℝ) (n : ℕ) :
    shiftedVonMangoldt a n = primeShiftCoeff a n + properShift a n := by
  unfold primeShiftCoeff properShift
  split_ifs <;> ring

theorem properShift_eq_zero {a : ℝ} {n : ℕ} (h : ¬ IsProperPrimePow n) : properShift a n = 0 := by
  unfold properShift
  split_ifs with hp
  · rfl
  · unfold shiftedVonMangoldt
    have hΛ : vonMangoldt n = 0 := by
      by_contra hne
      exact h ⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne, hp⟩
    rw [hΛ]; ring

/-- `|properShift a n| ≤ [proper n] · log n · n^{a − 1}`. -/
theorem abs_properShift_le (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |properShift a n| ≤ (if IsProperPrimePow n then Real.log n * (n : ℝ) ^ (a - 1) else 0) := by
  classical
  by_cases h : IsProperPrimePow n
  · rw [if_pos h]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : |properShift a n| ≤ |shiftedVonMangoldt a n| := by
      unfold properShift
      split_ifs
      · simp
      · exact le_rfl
    refine h1.trans ?_
    unfold shiftedVonMangoldt
    have hΛ0 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    rw [abs_of_nonneg (by positivity), Real.rpow_sub_one hn0.ne']
    have : 0 ≤ (n : ℝ) ^ a / n := by positivity
    calc vonMangoldt n * (n : ℝ) ^ a / n = vonMangoldt n * ((n : ℝ) ^ a / n) := by ring
      _ ≤ Real.log n * ((n : ℝ) ^ a / n) := by gcongr
  · rw [if_neg h, properShift_eq_zero h, abs_zero]

/-- The proper-power shifted series converges for `Re s > a − 1/2`. -/
theorem properShift_LSeriesSummable {a : ℝ} {s : ℂ} (hs : a - 1 / 2 < s.re) :
    LSeriesSummable (fun n => (properShift a n : ℂ)) s := by
  classical
  set x : ℝ := 1 + s.re - a with hx
  have hx12 : 1 / 2 < x := by rw [hx]; linarith
  refine Summable.of_norm_bounded (summable_properPrimePow_log_rpow hx12) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero, properLogTerm, not_isProperPrimePow_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_real, Real.norm_eq_abs]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := abs_properShift_le a hn
    rw [div_le_iff₀ (by positivity)]
    refine hb.trans (le_of_eq ?_)
    unfold properLogTerm
    by_cases h : IsProperPrimePow n
    · rw [if_pos h, if_pos h]
      have e : (n : ℝ) ^ (-x) * (n : ℝ) ^ s.re = (n : ℝ) ^ (a - 1) := by
        rw [← Real.rpow_add hn0]; congr 1; rw [hx]; ring
      rw [← e]
      ring
    · rw [if_neg h, if_neg h]
      simp

theorem differentiableAt_LSeries_properShift {a : ℝ} {s : ℂ} (hs : a - 1 / 2 < s.re) :
    DifferentiableAt ℂ (LSeries (fun n => (properShift a n : ℂ))) s := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (properShift a n : ℂ)) ≤ ((a - 1 / 2 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      properShift_LSeriesSummable (by simpa using hy)
  exact (LSeries_analyticOnNhd _ s (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt

/-! ## The growth coefficient -/

/-- The coefficient `(M + p^a − a_p) Λ(p)/p` at the primes. -/
def primeGrowthCoeff (a M : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (M + (n : ℝ) ^ a - integerLag n) * vonMangoldt n / n else 0

theorem primeGrowthCoeff_eq (a M : ℝ) (n : ℕ) :
    primeGrowthCoeff a M n = primeOnlyCoeff M n + primeShiftCoeff a n := by
  unfold primeGrowthCoeff primeOnlyCoeff primeShiftCoeff primeLagCoeff shiftedVonMangoldt
  split_ifs <;> ring

theorem primeGrowthCoeff_nonneg {a M : ℝ} (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M + (p : ℝ) ^ a)
    (n : ℕ) : 0 ≤ primeGrowthCoeff a M n := by
  unfold primeGrowthCoeff
  split_ifs with hp
  · have h1 : 0 ≤ M + (n : ℝ) ^ a - integerLag n := by linarith [hM n hp]
    have h2 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    positivity
  · exact le_rfl

theorem primeGrowthCoeff_fun_eq (a M : ℝ) :
    (fun n => (primeGrowthCoeff a M n : ℂ))
      = (fun n => (primeOnlyCoeff M n : ℂ)) + ((fun n => (shiftedVonMangoldt a n : ℂ))
          - (fun n => (properShift a n : ℂ))) := by
  funext n
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [primeGrowthCoeff_eq, shiftedVonMangoldt_eq_primeShift_add_properShift]
  push_cast
  ring

/-- The growth continuation `G_M − T + (−ζ'/ζ)(1 + s − a) − T_a`. -/
def growthG (a M : ℝ) (s : ℂ) : ℂ :=
  primeOnlyG M s + (-logDeriv riemannZeta (1 + s - a) - LSeries (fun n => (properShift a n : ℂ)) s)

theorem primeGrowthCoeff_LSeriesSummable {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {a M : ℝ} (ha : a < θ - 1 / 2) {s : ℂ} (hs : θ - 1 / 2 < s.re) :
    LSeriesSummable (fun n => (primeGrowthCoeff a M n : ℂ)) s := by
  rw [primeGrowthCoeff_fun_eq]
  exact (primeOnlyCoeff_LSeriesSummable hθ hθ2 hs).add
    ((shiftedVonMangoldt_LSeriesSummable (by linarith)).sub (properShift_LSeriesSummable (by linarith)))

theorem LSeries_primeGrowthCoeff_eq {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {a M : ℝ} (ha : a < θ - 1 / 2) {s : ℂ} (hs : θ - 1 / 2 < s.re) :
    LSeries (fun n => (primeGrowthCoeff a M n : ℂ)) s = growthG a M s := by
  rw [primeGrowthCoeff_fun_eq,
    LSeries_add (primeOnlyCoeff_LSeriesSummable hθ hθ2 hs)
      ((shiftedVonMangoldt_LSeriesSummable (by linarith)).sub (properShift_LSeriesSummable (by linarith))),
    LSeries_sub (shiftedVonMangoldt_LSeriesSummable (by linarith)) (properShift_LSeriesSummable (by linarith)),
    LSeries_primeOnlyCoeff_eq hθ hθ2 hs, LSeries_shiftedVonMangoldt_eq (by linarith)]
  rfl

theorem differentiableOn_growthG {θ η t₀ r a M : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1)
    (ha : a < θ - 1 / 2 - η) {U : Set ℂ}
    (hUbox : U ⊆ landauBox θ η t₀ r) (hpos : ∀ s ∈ U, 0 < s.re)
    (hnear : ∀ q ∈ nearSet t₀, ∀ s ∈ U, s + 3 / 2 - (q.1 : ℂ) ≠ 1) :
    DifferentiableOn ℂ (growthG a M) U := by
  have h1 := differentiableOn_primeOnlyG (M := M) hθ hθ2 hθ34 hη hr1 hUbox hpos hnear
  have h2 : DifferentiableOn ℂ (fun s : ℂ => -logDeriv riemannZeta (1 + s - a)) U := by
    intro s hs
    have hre := (hUbox hs).1
    have hw1 : (1 : ℂ) + s - a ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hζ : riemannZeta (1 + s - a) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
    have hd := differentiableAt_logDeriv_zeta hw1 hζ
    have hc : DifferentiableAt ℂ (fun s : ℂ => (1 : ℂ) + s - a) s := by fun_prop
    exact ((hd.comp s hc).neg).differentiableWithinAt
  have h3 : DifferentiableOn ℂ (LSeries (fun n => (properShift a n : ℂ))) U := by
    intro s hs
    have := (hUbox hs).1
    exact (differentiableAt_LSeries_properShift (a := a) (by linarith)).differentiableWithinAt
  exact h1.add (h2.sub h3)

/-! ## The strip from a power ceiling at the primes -/

/-- If `a_p ≤ M + p^a` for every prime `p` (`a ≥ 0`), then `Φ(L) ≤ M₃ e^{bL}` with
`b = max a (1/4)`. -/
theorem exists_growth_bound_of_primeLag_le_rpow {M a : ℝ} (ha0 : 0 ≤ a)
    (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M + (p : ℝ) ^ a) :
    ∃ M₃ : ℝ, ∀ L : ℝ, 0 ≤ L → weilLagFunctionReal L ≤ M₃ * Real.exp (max a (1 / 4) * L) := by
  obtain ⟨X₀, hX₀4, hX₀⟩ := exists_prime_short_gap
  set b : ℝ := max a (1 / 4) with hb
  have hb4 : 1 / 4 ≤ b := le_max_right _ _
  have hba : a ≤ b := le_max_left _ _
  set L₀ : ℝ := Real.log X₀ with hL₀
  have hL₀0 : 0 ≤ L₀ := Real.log_nonneg (by linarith)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L₀)).bddAbove_image
    continuous_weilLagFunctionReal.continuousOn
  refine ⟨|M| + 1 + 457776 + max B 0, fun L hL => ?_⟩
  have hE : 1 ≤ Real.exp (b * L) := Real.one_le_exp (by positivity)
  have hE0 : 0 < Real.exp (b * L) := Real.exp_pos _
  rcases le_or_gt L L₀ with hLL₀ | hLL₀
  · have h1 : weilLagFunctionReal L ≤ B := hB ⟨L, ⟨hL, hLL₀⟩, rfl⟩
    have h2 : B ≤ max B 0 := le_max_left _ _
    have h3 : max B 0 ≤ max B 0 * Real.exp (b * L) :=
      le_mul_of_one_le_right (le_max_right _ _) hE
    have h4 : 0 ≤ (|M| + 1 + 457776) * Real.exp (b * L) := by positivity
    nlinarith
  · set X : ℝ := Real.exp L with hX
    have hXX₀ : X₀ ≤ X := by
      rw [hX, ← Real.exp_log (by linarith : (0:ℝ) < X₀)]
      exact Real.exp_le_exp.mpr hLL₀.le
    obtain ⟨p, hp, hpX, hgap⟩ := hX₀ X hXX₀
    have hp2 : 2 ≤ p := hp.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hlogp : Real.log p ≤ L := by
      rw [← Real.log_exp L]; exact Real.log_le_log hp0 hpX
    have hpow_le : (p : ℝ) ^ (71 / 100 : ℝ) ≤ p := Real.rpow_le_self_of_one_le hp1 (by norm_num)
    have hm2p : ⌊X⌋₊ ≤ 2 * p := by
      have h1 : (⌊X⌋₊ : ℝ) < 2 * p := by linarith
      exact_mod_cast h1.le
    have hgapℕ : ((⌊X⌋₊ - p : ℕ) : ℝ) ≤ (p : ℝ) ^ (71 / 100 : ℝ) := by
      have hpm : p ≤ ⌊X⌋₊ := Nat.le_floor hpX
      rw [Nat.cast_sub hpm]
      linarith
    have hbound := abs_weilLagFunctionReal_sub_integerLag_le_of_gap hp2 hlogp hm2p
    rw [← hX] at hbound
    have hfactor : 11 * ((⌊X⌋₊ - p : ℕ) + 1) * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p
        ≤ 11 * ((p : ℝ) ^ (71 / 100 : ℝ) + 1) * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p := by
      gcongr
    have hgf := gap_factor_le hp2'
    have hpL : (p : ℝ) ^ (23 / 100 : ℝ) ≤ Real.exp ((23 / 100) * L) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hpa : (p : ℝ) ^ a ≤ Real.exp (b * L) := by
      rw [Real.rpow_def_of_pos hp0]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg hp1])
    have hexp : Real.exp ((23 / 100) * L) ≤ Real.exp (b * L) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hM' : M ≤ |M| * Real.exp (b * L) := by
      have := le_abs_self M
      have : |M| ≤ |M| * Real.exp (b * L) := le_mul_of_one_le_right (abs_nonneg M) hE
      linarith
    have h1 := (abs_le.mp hbound).2
    have hmax0 : 0 ≤ max B 0 * Real.exp (b * L) := by positivity
    calc weilLagFunctionReal L ≤ integerLag p + 11 * ((⌊X⌋₊ - p : ℕ) + 1)
          * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p := by linarith
      _ ≤ M + (p : ℝ) ^ a + 457776 * Real.exp (b * L) := by
          have := hM p hp
          linarith
      _ ≤ (|M| + 1 + 457776 + max B 0) * Real.exp (b * L) := by nlinarith

/-- A power ceiling at the primes with exponent `a ∈ [0, 1/2)` forces `Re ρ ≤ 1/2 + max a (1/4)`. -/
theorem re_le_half_add_max_of_primeLag_le_rpow {M a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M + (p : ℝ) ^ a) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + max a (1 / 4) := by
  obtain ⟨M₃, hM₃⟩ := exists_growth_bound_of_primeLag_le_rpow ha0 hM
  exact re_le_half_add_of_weilLagFunctionReal_le_exp (a := max a (1 / 4)) (M := M₃)
    (by positivity) (max_lt ha (by norm_num)) hM₃ q

/-! ## The Landau transfer step -/

theorem growth_transfer_step {a M : ℝ} (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M + (p : ℝ) ^ a)
    (hRH : ¬ RiemannHypothesis) (ha : a < zeroReSup - 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 20 ∧ η < zeroReSup - 1 / 2 ∧ a < zeroReSup - 1 / 2 - η ∧
      (∀ q : XiZeroCopy, |zeroOrdinate q| ≤ 6 → 3 * η ≤ |zeroOrdinate q| / 2) ∧
      LSeriesSummable (fun n => (primeGrowthCoeff a M n : ℂ)) ((zeroReSup - 1 / 2 - η / 4 : ℝ) : ℂ) := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁ (re_le_zeroReSup q₁)
  have hΘ1 : Θ ≤ 1 := zeroReSup_le fun q => (xiZeroCopy_re_lt_one q).le
  have hΘ34 : Θ ≤ 3 / 4 := by
    rcases le_or_gt a 0 with ha0 | ha0
    · have hM' : ∀ p : ℕ, p.Prime → integerLag p ≤ M + 1 := fun p hp => by
        have := hM p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
        have : (p : ℝ) ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 ha0
        linarith
      exact zeroReSup_le (re_le_three_quarters_of_primeLag_le hM')
    · have hstrip := re_le_half_add_max_of_primeLag_le_rpow ha0.le (by linarith) hM
      rcases le_or_gt a (1 / 4) with ha4 | ha4
      · refine zeroReSup_le fun q => ?_
        have := hstrip q
        rw [max_eq_right ha4] at this
        linarith
      · exfalso
        obtain ⟨q, hq⟩ := exists_re_gt_of_lt_zeroReSup (b := 1 / 2 + a) (by linarith)
        have := hstrip q
        rw [max_eq_left ha4.le] at this
        linarith
  obtain ⟨γmin, hγpos, hγmin⟩ := exists_pos_le_abs_ordinate
  set η : ℝ := min (1 / 20) (min ((Θ - 1 / 2 - a) / 2) (min ((Θ - 1 / 2) / 2) (γmin / 6))) with hη
  have hηpos : 0 < η :=
    lt_min (by norm_num) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hη20 : η ≤ 1 / 20 := min_le_left _ _
  have hηa : η ≤ (Θ - 1 / 2 - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηΘ : η ≤ (Θ - 1 / 2) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηγ : η ≤ γmin / 6 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηΘ' : η < Θ - 1 / 2 := by linarith
  have haη : a < Θ - 1 / 2 - η := by linarith
  refine ⟨η, hηpos, hη20, hηΘ', haη, fun q hq => by linarith [hγmin q hq], ?_⟩
  have hsum : LSeriesSummable (fun n => (primeGrowthCoeff a M n : ℂ)) ((Θ - 1 / 2 + η : ℝ) : ℂ) :=
    primeGrowthCoeff_LSeriesSummable hθ hΘ12.le ha (by simp; linarith)
  set R : NNReal := ⟨5 * η / 2, by positivity⟩ with hR
  have hRval : (R : ℝ) = 5 * η / 2 := rfl
  have hball : closedBall (((Θ - 1 / 2 + η) + η : ℝ) : ℂ) (R : ℝ) ⊆ landauBox Θ η 0 (3 * η) := by
    intro s hs
    rw [mem_closedBall, Complex.dist_eq] at hs
    have hre := Complex.abs_re_le_norm (s - (((Θ - 1 / 2 + η) + η : ℝ) : ℂ))
    have him := Complex.abs_im_le_norm (s - (((Θ - 1 / 2 + η) + η : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    rw [hRval] at hs
    have h1 := (abs_le.mp (hre.trans hs)).1
    have h2 := (abs_le.mp (hre.trans hs)).2
    refine ⟨by linarith, by linarith, ?_⟩
    rw [sub_zero]
    linarith [him.trans hs]
  have hGd : DifferentiableOn ℂ (growthG a M)
      (closedBall (((Θ - 1 / 2 + η) + η : ℝ) : ℂ) (R : ℝ)) := by
    refine (differentiableOn_growthG (θ := Θ) (η := η) (t₀ := 0) (r := 3 * η) (a := a) (M := M) hθ
      hΘ12.le hΘ34 hη20 (by linarith) haη (U := landauBox Θ η 0 (3 * η)) le_rfl ?_ ?_).mono hball
    · intro s hs
      have := hs.1
      linarith
    · intro q hq s hs h1
      have hqn : |zeroOrdinate q - 0| < 5 := hq
      rw [sub_zero] at hqn
      have hq6 : |zeroOrdinate q| ≤ 6 := by linarith
      have hγ := hγmin q hq6
      have him : (s + 3 / 2 - (q.1 : ℂ)).im = s.im - zeroOrdinate q := by simp [zeroOrdinate]
      rw [h1, Complex.one_im] at him
      have hs3 := hs.2.2
      rw [sub_zero] at hs3
      have habs : |zeroOrdinate q| = |s.im| := by
        rw [show zeroOrdinate q = s.im by linarith]
      linarith
  have hagree : ∀ s : ℂ, Θ - 1 / 2 + η < s.re →
      growthG a M s = LSeries (fun n => (primeGrowthCoeff a M n : ℂ)) s := by
    intro s hs
    exact (LSeries_primeGrowthCoeff_eq hθ hΘ12.le ha (by linarith)).symm
  exact landau_local_summability_transfer (a := primeGrowthCoeff a M) (primeGrowthCoeff_nonneg hM)
    (σ₁ := Θ - 1 / 2 + η) (h := η) hηpos hsum (R := R) (G := growthG a M) hGd hagree
    (σ := Θ - 1 / 2 - η / 4) (by rw [hRval]; linarith)

/-! ## The growth exponent -/

/-- **Under `¬RH` the lag values at the primes exceed every `M + p^a` with `a < Θ − ½`.** -/
theorem exists_primeLag_gt_rpow_of_not_rh (hRH : ¬ RiemannHypothesis) {a : ℝ}
    (ha : a < zeroReSup - 1 / 2) (M : ℝ) :
    ∃ p : ℕ, p.Prime ∧ M + (p : ℝ) ^ a < integerLag p := by
  by_contra hcon
  push Not at hcon
  have hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M + (p : ℝ) ^ a := hcon
  obtain ⟨η, hηpos, hη20, hηΘ, haη, -, hsumσ⟩ := growth_transfer_step hM hRH ha
  obtain ⟨q₁', hq₁'⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁'⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁' (re_le_zeroReSup q₁')
  have hΘ1 : Θ ≤ 1 := zeroReSup_le fun q => (xiZeroCopy_re_lt_one q).le
  have hΘ34 : Θ ≤ 3 / 4 := by
    rcases le_or_gt a 0 with ha0 | ha0
    · have hM' : ∀ p : ℕ, p.Prime → integerLag p ≤ M + 1 := fun p hp => by
        have := hM p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
        have : (p : ℝ) ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 ha0
        linarith
      exact zeroReSup_le (re_le_three_quarters_of_primeLag_le hM')
    · have hstrip := re_le_half_add_max_of_primeLag_le_rpow ha0.le (by linarith) hM
      rcases le_or_gt a (1 / 4) with ha4 | ha4
      · refine zeroReSup_le fun q => ?_
        have := hstrip q
        rw [max_eq_right ha4] at this
        linarith
      · exfalso
        obtain ⟨q, hq⟩ := exists_re_gt_of_lt_zeroReSup (b := 1 / 2 + a) (by linarith)
        have := hstrip q
        rw [max_eq_left ha4.le] at this
        linarith
  set c : ℕ → ℂ := fun n => (primeGrowthCoeff a M n : ℂ) with hc
  set σ : ℝ := Θ - 1 / 2 - η / 4 with hσ
  have habs : LSeries.abscissaOfAbsConv c ≤ (σ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsumσ.of_re_le_re (by simp; linarith)
  have hFd : ∀ z : ℂ, σ < z.re → DifferentiableAt ℂ (LSeries c) z := fun z hz =>
    (LSeries_analyticOnNhd c z
      (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz))).differentiableAt
  obtain ⟨q₁, hq₁⟩ := exists_re_gt_of_lt_zeroReSup (b := Θ - η / 8) (by linarith)
  set ρ₁ : ℂ := (q₁.1 : ℂ) with hρ₁
  set K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀mem.1
  have hρ₀K := hρ₀mem.2
  rw [hK, Complex.mem_reProdIm] at hρ₀K
  have hre₀ : Θ - η / 8 < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := by have := xiZeroCopy_re_lt_one q₀; rwa [hq₀] at this
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  have hmaxq : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ →
      (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    intro q hq
    rw [hq₀]
    by_contra hlt
    push Not at hlt
    have hmemK : (q.1 : ℂ) ∈ xiZeroSet ∩ K := by
      refine ⟨xi_xiZeroCopy_eq_zero q, ?_⟩
      rw [hK, Complex.mem_reProdIm]
      refine ⟨⟨by linarith [hρ₀K.1.1], (xiZeroCopy_re_lt_one q).le⟩, ?_⟩
      have : (q.1 : ℂ).im = ρ₁.im := by
        unfold zeroOrdinate at hq; rw [hq, hq₀, him₀]
      rw [this]; exact ⟨le_rfl, le_rfl⟩
    have := hmax _ hmemK hlt.le
    linarith
  have hβ₀ : Θ - η < (q₀.1 : ℂ).re := by rw [hq₀]; linarith
  have hβ₀' : 1 / 2 < (q₀.1 : ℂ).re := by rw [hq₀]; linarith
  obtain ⟨C, hC⟩ := landauG_ray_lower_bound (M := M) hθ hΘ34 hη20 hηpos q₀ hβ₀ hβ₀' hmaxq
  -- the three analytic corrections are bounded on the closed ray segment
  have hray_re : ∀ t : ℝ, 0 ≤ t → ρ₀.re - 1 / 2 ≤ ((q₀.1 : ℂ) - 1 / 2 + t).re := by
    intro t ht; simp [hq₀]; linarith
  have hTc : ContinuousOn (fun t : ℝ => LSeries (fun n => (properCoeff M n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hd : DifferentiableAt ℂ (LSeries (fun n => (properCoeff M n : ℂ))) ((q₀.1 : ℂ) - 1 / 2 + t) := by
      apply differentiableAt_LSeries_properCoeff hθ hΘ12.le
      have := hray_re t ht.1; linarith
    have hc : ContinuousAt (fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) t :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    exact (ContinuousAt.comp (g := LSeries (fun n => (properCoeff M n : ℂ)))
      (f := fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) hd.continuousAt hc).continuousWithinAt
  obtain ⟨BT, hBT⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hTc
  have hZc : ContinuousOn (fun t : ℝ => -logDeriv riemannZeta (1 + ((q₀.1 : ℂ) - 1 / 2 + t) - a))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have ht0 := ht.1
    have hw1 : (1 : ℂ) + ((q₀.1 : ℂ) - 1 / 2 + t) - a ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; rw [hq₀] at this
      linarith [hre₀]
    have hζ : riemannZeta (1 + ((q₀.1 : ℂ) - 1 / 2 + t) - a) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; rw [hq₀]; linarith [hre₀])
    have hd := (differentiableAt_logDeriv_zeta hw1 hζ).continuousAt
    have hc : ContinuousAt (fun t : ℝ => (1 : ℂ) + ((q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) - a) t := by fun_prop
    exact ((ContinuousAt.comp (g := logDeriv riemannZeta)
      (f := fun t : ℝ => (1 : ℂ) + ((q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) - a) hd hc).neg).continuousWithinAt
  obtain ⟨BZ, hBZ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hZc
  have hSc : ContinuousOn (fun t : ℝ => LSeries (fun n => (properShift a n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hd : DifferentiableAt ℂ (LSeries (fun n => (properShift a n : ℂ))) ((q₀.1 : ℂ) - 1 / 2 + t) := by
      apply differentiableAt_LSeries_properShift
      have := hray_re t ht.1; linarith
    have hc : ContinuousAt (fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) t :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    exact (ContinuousAt.comp (g := LSeries (fun n => (properShift a n : ℂ)))
      (f := fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) hd.continuousAt hc).continuousWithinAt
  obtain ⟨BS, hBS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hSc
  have hC' : ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      ‖aliasedWeight q₀‖ / t - (C + BT + BZ + BS) ≤ ‖growthG a M ((q₀.1 : ℂ) - 1 / 2 + t)‖ := by
    intro t ht ht4
    have h1 := hC t ht ht4
    have h2 := hBT t ⟨ht.le, ht4⟩
    have h3 := hBZ t ⟨ht.le, ht4⟩
    have h4 := hBS t ⟨ht.le, ht4⟩
    unfold growthG primeOnlyG
    set G := landauG M ((q₀.1 : ℂ) - 1 / 2 + t) with hG
    set T := LSeries (fun n => (properCoeff M n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t) with hT
    set Z := -logDeriv riemannZeta (1 + ((q₀.1 : ℂ) - 1 / 2 + t) - a) with hZ
    set Sa := LSeries (fun n => (properShift a n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t) with hSa
    have e : G - T + (Z - Sa) = G - (T - Z + Sa) := by ring
    rw [e]
    have := norm_sub_norm_le G (T - Z + Sa)
    have h5 : ‖T - Z + Sa‖ ≤ ‖T‖ + ‖Z‖ + ‖Sa‖ := by
      calc ‖T - Z + Sa‖ ≤ ‖T - Z‖ + ‖Sa‖ := norm_add_le _ _
        _ ≤ ‖T‖ + ‖Z‖ + ‖Sa‖ := by linarith [norm_sub_le T Z]
    linarith
  -- the ray box
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  have hγ₀im : ρ₀.im = γ₀ := by rw [hγ₀]; unfold zeroOrdinate; rw [hq₀]
  obtain ⟨r, hrpos, hr1, hrgap⟩ := exists_pos_le_ordinate_gap γ₀
  set U₀ : Set ℂ := landauBox ρ₀.re 0 γ₀ r with hU₀
  have hU₀open : IsOpen U₀ := isOpen_landauBox _ _ _ _
  have hGd : DifferentiableOn ℂ (growthG a M) U₀ := by
    refine differentiableOn_growthG (θ := Θ) (η := η) (t₀ := γ₀) (r := r) (a := a) (M := M) hθ
      hΘ12.le hΘ34 hη20 hr1 haη (U := U₀) ?_ ?_ ?_
    · intro s hs
      exact ⟨by linarith [hs.1], hs.2.1, hs.2.2⟩
    · intro s hs
      linarith [hs.1]
    · intro q hq s hs h1
      have him : s.im = zeroOrdinate q := by
        have := congrArg Complex.im h1
        simp at this
        unfold zeroOrdinate
        linarith
      have hre : s.re = (q.1 : ℂ).re - 1 / 2 := by
        have := congrArg Complex.re h1
        simp at this
        linarith
      by_cases hord : zeroOrdinate q = γ₀
      · have := hmaxq q hord
        rw [hq₀] at this
        have hs1 := hs.1
        linarith
      · have hgap := hrgap q hq hord
        have hs3 := hs.2.2
        rw [him] at hs3
        linarith
  set p₀ : ℂ := ρ₀ - 1 / 2 with hp₀
  set ℓ : ℝ → ℂ := fun t => p₀ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  have hℓeq : ∀ t : ℝ, ℓ t = (q₀.1 : ℂ) - 1 / 2 + t := fun t => by rw [hℓ, hp₀, hq₀]
  have hℓre : ∀ t : ℝ, (ℓ t).re = ρ₀.re - 1 / 2 + t := fun t => by rw [hℓ, hp₀]; simp
  have hℓim : ∀ t : ℝ, (ℓ t).im = γ₀ := fun t => by rw [hℓ, hp₀]; simp [hγ₀im]
  set U : Set ℝ := Ioo (0 : ℝ) (1 / 4) with hU
  have hℓU₀ : ∀ t ∈ U, ℓ t ∈ U₀ := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [hℓre]; linarith [ht.1]
    · rw [hℓre]; linarith [ht.2]
    · rw [hℓim, sub_self, abs_zero]; exact hrpos
  set V : Set ℂ := {z : ℂ | σ < z.re} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hFdiff : DifferentiableOn ℂ (LSeries c) V := fun z hz => (hFd z hz).differentiableWithinAt
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    show σ < (ℓ t).re
    rw [hℓre]; linarith [ht.1]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => LSeries c (ℓ t)) U := fun t ht =>
    ((hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))).restrictScalars).comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => growthG a M (ℓ t)) U := fun t ht =>
    ((hGd.analyticAt (hU₀open.mem_nhds (hℓU₀ t ht))).restrictScalars).comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h18U : (1 / 8 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hagree : ∀ s : ℂ, Θ - 1 / 2 < s.re → LSeries c s = growthG a M s := fun s hs =>
    LSeries_primeGrowthCoeff_eq hθ hΘ12.le ha hs
  have hfg : (fun t : ℝ => LSeries c (ℓ t)) =ᶠ[𝓝 (1 / 8 : ℝ)]
      (fun t : ℝ => growthG a M (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (by linarith : η / 8 < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 4))
      fun t ht => ?_
    apply hagree
    rw [hℓre]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h18U hfg
  have hp₀σ : σ < p₀.re := by rw [hp₀]; simp; linarith
  have hFcont : ContinuousAt (LSeries c) p₀ := (hFd p₀ hp₀σ).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ)) (𝓝 0) (𝓝 (p₀ + ((0 : ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    rwa [Complex.ofReal_zero, add_zero] at this
  have hcomp : Tendsto (fun t : ℝ => LSeries c (ℓ t)) (𝓝 0) (𝓝 (LSeries c p₀)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  obtain ⟨C', hC0, h3⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C + BT + BZ + BS ≤ C' :=
    ⟨max (C + BT + BZ + BS) 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = ‖LSeries c p₀‖ + 1 := ⟨_, rfl⟩
  have hw : 0 < ‖aliasedWeight q₀‖ := norm_aliasedWeight_pos q₀
  have hBpos : 0 < Bd + C' + 1 := by rw [hBd]; positivity
  obtain ⟨t₀, ht₀pos, ht₀δ, ht₀t₁, ht₀4, h2⟩ :=
    exists_small_ray_parameter hδ (one_pos : (0 : ℝ) < 1) hw hBpos
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, ht₀4⟩
  have hFb : ‖LSeries c (ℓ t₀)‖ ≤ Bd := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖LSeries c (ℓ t₀)‖
        = ‖(LSeries c (ℓ t₀) - LSeries c p₀) + LSeries c p₀‖ := by congr 1; ring
      _ ≤ ‖LSeries c (ℓ t₀) - LSeries c p₀‖ + ‖LSeries c p₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖LSeries c p₀‖ := by linarith
      _ = Bd := by rw [hBd]; ring
  have hGb : Bd < ‖growthG a M (ℓ t₀)‖ := by
    have h1 := hC' t₀ ht₀pos ht₀4.le
    rw [← hℓeq] at h1
    have h4 : ‖aliasedWeight q₀‖ / t₀ = 2 * (‖aliasedWeight q₀‖ / (2 * t₀)) := by
      field_simp
    linarith
  have hEq : LSeries c (ℓ t₀) = growthG a M (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-- **The growth exponent law at the primes.**  Under `¬RH`, for every `a < Θ − ½`, every `M`, and
every `X`, some prime `p > X` has `a_p > M + p^a`; and always `a_p ≤ W p^{Θ−½}`. -/
theorem exists_prime_gt_primeLag_gt_rpow_of_not_rh (hRH : ¬ RiemannHypothesis) {a : ℝ}
    (ha : a < zeroReSup - 1 / 2) (M X : ℝ) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ M + (p : ℝ) ^ a < integerLag p := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁⟩
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ zeroReSup := re_le_zeroReSup
  have hW0 := lagWeightTotal_nonneg
  set M' : ℝ := max M 0 + lagWeightTotal * (max X 1) ^ (zeroReSup - 1 / 2) with hM'
  obtain ⟨p, hp, hlt⟩ := exists_primeLag_gt_rpow_of_not_rh hRH ha M'
  refine ⟨p, hp, ?_, ?_⟩
  · by_contra hpX
    push Not at hpX
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hbound := abs_integerLag_le_rpow hθ hp1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpa : 0 ≤ (p : ℝ) ^ a := by positivity
    have hΘ12 : 0 ≤ zeroReSup - 1 / 2 := by
      have := re_le_zeroReSup q₁; linarith
    have hmono : (p : ℝ) ^ (zeroReSup - 1 / 2) ≤ (max X 1) ^ (zeroReSup - 1 / 2) :=
      Real.rpow_le_rpow hp0.le (hpX.trans (le_max_left _ _)) hΘ12
    have h1 := (abs_le.mp hbound).2
    have h2 : lagWeightTotal * (p : ℝ) ^ (zeroReSup - 1 / 2)
        ≤ lagWeightTotal * (max X 1) ^ (zeroReSup - 1 / 2) := by gcongr
    have := le_max_right M 0
    linarith
  · have := le_max_left M 0
    have : 0 ≤ lagWeightTotal * (max X 1) ^ (zeroReSup - 1 / 2) := by positivity
    linarith

end

end RHTower
