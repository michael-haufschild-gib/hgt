import GaloisForLFunctions.RHTower.JointAncestrySinglePrimeLevel

/-!
# The power-saving prime-lag criterion

If the lag values `a_p = Φ(log p)` satisfy `a_p ≤ M p^σ` on the primes `p > X`, with `0 ≤ σ ≤ ¼`,
then every zero satisfies `Re ρ ≤ ½ + σ` (`re_le_half_add_of_primeLag_le_rpow`).  The case `σ = 0`
is the prime-lag criterion `riemannHypothesis_of_primeLag_le`.

The proof is the Landau argument of the prime-lag criterion.  The nonnegative coefficients are
`c_p = (M p^σ − a_p) Λ(p)/p` on the primes `p > X`.  Their Dirichlet series splits as follows.
* `M · Σ_{p > X} p^σ Λ(p)/p · p^{−s}` converges absolutely, hence is analytic, on `Re s > σ`.
* The prime-only series at `M = 0` has the zero-side continuation `primeOnlyG 0`.
* A finite sum over the primes `p ≤ X` is entire.

Suppose `Θ = sup Re ρ > ½ + σ`.  Every point used in the argument lies in `Re s > σ`, so the shifted
part is harmless.  Landau's theorem pushes convergence to the left of `Θ − ½`.  There the series is
analytic on a half-plane containing a pole `ρ₀ − ½` of the zero-side continuation, a contradiction.

With the growth bound (single-prime positivity at `σ ≥ ¼` already gives `Re ρ ≤ ½ + σ`), single-prime
JAS positivity at a level `σ ∈ [0, ½)` on large primes gives the half-plane `Re ρ ≤ ½ + σ`
exactly (`xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove_sharp`).  So the single-prime JAS
level is `sup Re ρ − ½`.
-/

open Complex Filter Topology Set Metric
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The coefficients -/

/-- `c_n = (M n^σ − a_n) Λ(n)/n` on the primes `n > X`, and `0` otherwise. -/
def powerPrimeLagCoeff (M σ : ℝ) (X n : ℕ) : ℝ :=
  if n.Prime ∧ X < n then (M * Real.exp (σ * Real.log n) - integerLag n) * vonMangoldt n / n else 0

/-- `n^σ Λ(n)/n` on the primes `n > X`, and `0` otherwise. -/
def shiftedPrimeCoeff (σ : ℝ) (X n : ℕ) : ℝ :=
  if n.Prime ∧ X < n then Real.exp (σ * Real.log n) * vonMangoldt n / n else 0

/-- The prime-only coefficient at `M = 0` on `n ≤ X`. -/
def smallPrimeOnlyCoeff (X n : ℕ) : ℝ := if n ≤ X then primeOnlyCoeff 0 n else 0

theorem powerPrimeLagCoeff_eq (M σ : ℝ) (X n : ℕ) :
    powerPrimeLagCoeff M σ X n =
      primeOnlyCoeff 0 n - smallPrimeOnlyCoeff X n + M * shiftedPrimeCoeff σ X n := by
  unfold powerPrimeLagCoeff shiftedPrimeCoeff smallPrimeOnlyCoeff primeOnlyCoeff primeLagCoeff
  by_cases hp : n.Prime
  · by_cases hX : X < n
    · have hnX : ¬ n ≤ X := by omega
      simp only [hp, hX, and_self, if_true, hnX, if_false]; ring
    · have hnX : n ≤ X := by omega
      simp only [hp, hX, and_false, if_false, hnX, if_true]; ring
  · simp only [hp, false_and, if_false]
    split_ifs <;> ring

theorem powerPrimeLagCoeff_nonneg {X : ℕ} {M σ : ℝ}
    (hM : ∀ p : ℕ, p.Prime → X < p → integerLag p ≤ M * Real.exp (σ * Real.log p)) (n : ℕ) :
    0 ≤ powerPrimeLagCoeff M σ X n := by
  unfold powerPrimeLagCoeff
  split_ifs with h
  · have h1 : 0 ≤ M * Real.exp (σ * Real.log n) - integerLag n := by linarith [hM n h.1 h.2]
    have h2 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    positivity
  · exact le_rfl

/-! ## Summability and analyticity of the pieces -/

theorem shiftedPrimeCoeff_LSeriesSummable {σ : ℝ} {X : ℕ} {s : ℂ} (hs : σ < s.re) :
    LSeriesSummable (fun n => (shiftedPrimeCoeff σ X n : ℂ)) s := by
  have hΛ : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) ((1 + s.re - σ : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith)
  refine Summable.of_norm_bounded hΛ.norm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', norm_div, norm_div,
      Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_real,
      Complex.norm_real]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hΛ0 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    simp only [Complex.ofReal_re]
    unfold shiftedPrimeCoeff
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, abs_of_nonneg hΛ0]
      have hexp : Real.exp (σ * Real.log n) = (n : ℝ) ^ σ := by
        rw [Real.rpow_def_of_pos hn0, mul_comm]
      have e : (n : ℝ) ^ (1 + s.re - σ) = (n : ℝ) * (n : ℝ) ^ s.re / (n : ℝ) ^ σ := by
        rw [Real.rpow_sub hn0, Real.rpow_add hn0, Real.rpow_one]
      rw [hexp, e]
      apply le_of_eq
      have h1 : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 _
      have h2 : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn0 _
      field_simp
    · simp only [norm_zero, zero_div]
      positivity

theorem differentiableAt_LSeries_shiftedPrimeCoeff {σ : ℝ} {X : ℕ} {s : ℂ} (hs : σ < s.re) :
    DifferentiableAt ℂ (LSeries (fun n => (shiftedPrimeCoeff σ X n : ℂ))) s := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (shiftedPrimeCoeff σ X n : ℂ)) ≤ (σ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      shiftedPrimeCoeff_LSeriesSummable (by simpa using hy)
  exact (LSeries_analyticOnNhd _ s (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt

theorem smallPrimeOnlyCoeff_LSeriesSummable (X : ℕ) (s : ℂ) :
    LSeriesSummable (fun n => (smallPrimeOnlyCoeff X n : ℂ)) s := by
  refine summable_of_ne_finset_zero (s := Finset.range (X + 1)) fun n hn => ?_
  have hnX : ¬ n ≤ X := fun h => hn (Finset.mem_range.mpr (by omega))
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · simp [smallPrimeOnlyCoeff, hnX]

theorem differentiable_LSeries_smallPrimeOnlyCoeff (X : ℕ) :
    Differentiable ℂ (LSeries (fun n => (smallPrimeOnlyCoeff X n : ℂ))) := by
  intro s
  have habs : LSeries.abscissaOfAbsConv (fun n => (smallPrimeOnlyCoeff X n : ℂ)) ≤
      ((s.re - 1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y _ =>
      smallPrimeOnlyCoeff_LSeriesSummable X y
  exact (LSeries_analyticOnNhd _ s (lt_of_le_of_lt habs
    (EReal.coe_lt_coe_iff.mpr (by linarith)))).differentiableAt

/-- The continuation `G(s) = primeOnlyG 0 s − (small primes) + M · (shifted primes)`. -/
def powerLagG (M σ : ℝ) (X : ℕ) (s : ℂ) : ℂ :=
  primeOnlyG 0 s - LSeries (fun n => (smallPrimeOnlyCoeff X n : ℂ)) s +
    (M : ℂ) * LSeries (fun n => (shiftedPrimeCoeff σ X n : ℂ)) s

theorem powerPrimeLagCoeff_fun_eq (M σ : ℝ) (X : ℕ) :
    (fun n => (powerPrimeLagCoeff M σ X n : ℂ)) =
      (fun n => (primeOnlyCoeff 0 n : ℂ)) - (fun n => (smallPrimeOnlyCoeff X n : ℂ)) +
        (M : ℂ) • (fun n => (shiftedPrimeCoeff σ X n : ℂ)) := by
  funext n
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [powerPrimeLagCoeff_eq]
  push_cast
  ring

theorem powerPrimeLagCoeff_LSeriesSummable {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {M σ : ℝ} {X : ℕ} {s : ℂ} (hs : θ - 1 / 2 < s.re) (hσ : σ < s.re) :
    LSeriesSummable (fun n => (powerPrimeLagCoeff M σ X n : ℂ)) s := by
  rw [powerPrimeLagCoeff_fun_eq]
  exact ((primeOnlyCoeff_LSeriesSummable hθ hθ2 hs).sub (smallPrimeOnlyCoeff_LSeriesSummable X s)).add
    ((shiftedPrimeCoeff_LSeriesSummable hσ).smul (M : ℂ))

theorem LSeries_powerPrimeLagCoeff_eq {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {M σ : ℝ} {X : ℕ} {s : ℂ} (hs : θ - 1 / 2 < s.re) (hσ : σ < s.re) :
    LSeries (fun n => (powerPrimeLagCoeff M σ X n : ℂ)) s = powerLagG M σ X s := by
  rw [powerPrimeLagCoeff_fun_eq, LSeries_add ((primeOnlyCoeff_LSeriesSummable hθ hθ2 hs).sub
      (smallPrimeOnlyCoeff_LSeriesSummable X s)) ((shiftedPrimeCoeff_LSeriesSummable hσ).smul (M : ℂ)),
    LSeries_sub (primeOnlyCoeff_LSeriesSummable hθ hθ2 hs) (smallPrimeOnlyCoeff_LSeriesSummable X s),
    LSeries_smul, LSeries_primeOnlyCoeff_eq hθ hθ2 hs, powerLagG]

theorem differentiableOn_powerLagG {θ η t₀ r M σ : ℝ} {X : ℕ}
    (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1) {U : Set ℂ}
    (hUbox : U ⊆ landauBox θ η t₀ r) (hpos : ∀ s ∈ U, 0 < s.re) (hσU : ∀ s ∈ U, σ < s.re)
    (hnear : ∀ q ∈ nearSet t₀, ∀ s ∈ U, s + 3 / 2 - (q.1 : ℂ) ≠ 1) :
    DifferentiableOn ℂ (powerLagG M σ X) U := by
  have h1 := differentiableOn_primeOnlyG (M := 0) hθ hθ2 hθ34 hη hr1 hUbox hpos hnear
  have h2 : DifferentiableOn ℂ (LSeries (fun n => (smallPrimeOnlyCoeff X n : ℂ))) U :=
    (differentiable_LSeries_smallPrimeOnlyCoeff X).differentiableOn
  have h3 : DifferentiableOn ℂ (LSeries (fun n => (shiftedPrimeCoeff σ X n : ℂ))) U := fun s hs =>
    (differentiableAt_LSeries_shiftedPrimeCoeff (hσU s hs)).differentiableWithinAt
  exact (h1.sub h2).add (h3.const_mul _)

/-! ## The Landau argument -/

/-- **Landau transfer.**  If `sup Re ρ > ½ + σ`, the coefficient series converges at a real point
to the left of `sup Re ρ − ½`. -/
theorem powerLag_transfer_step {X : ℕ} {M σ : ℝ} (hσ0 : 0 ≤ σ)
    (hM : ∀ p : ℕ, p.Prime → X < p → integerLag p ≤ M * Real.exp (σ * Real.log p))
    [Nonempty XiZeroCopy] (hΘ34 : zeroReSup ≤ 3 / 4) (hΘσ : 1 / 2 + σ < zeroReSup) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 20 ∧ η < zeroReSup - 1 / 2 ∧ 2 * η ≤ zeroReSup - 1 / 2 - σ ∧
      (∀ q : XiZeroCopy, |zeroOrdinate q| ≤ 6 → 3 * η ≤ |zeroOrdinate q| / 2) ∧
      LSeriesSummable (fun n => (powerPrimeLagCoeff M σ X n : ℂ))
        ((zeroReSup - 1 / 2 - η / 4 : ℝ) : ℂ) := by
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := by linarith
  obtain ⟨γmin, hγpos, hγmin⟩ := exists_pos_le_abs_ordinate
  set η : ℝ := min (1 / 20) (min ((Θ - 1 / 2 - σ) / 2) (γmin / 6)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hη20 : η ≤ 1 / 20 := min_le_left _ _
  have hηΘ : η ≤ (Θ - 1 / 2 - σ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηγ : η ≤ γmin / 6 := (min_le_right _ _).trans (min_le_right _ _)
  have hηΘ' : η < Θ - 1 / 2 := by linarith
  refine ⟨η, hηpos, hη20, hηΘ', by linarith, fun q hq => by linarith [hγmin q hq], ?_⟩
  have hsum : LSeriesSummable (fun n => (powerPrimeLagCoeff M σ X n : ℂ)) ((Θ - 1 / 2 + η : ℝ) : ℂ) :=
    powerPrimeLagCoeff_LSeriesSummable hθ hΘ12.le (by simp; linarith) (by simp; linarith)
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
  have hGd : DifferentiableOn ℂ (powerLagG M σ X)
      (closedBall (((Θ - 1 / 2 + η) + η : ℝ) : ℂ) (R : ℝ)) := by
    refine (differentiableOn_powerLagG (θ := Θ) (η := η) (t₀ := 0) (r := 3 * η) (M := M) (σ := σ)
      (X := X) hθ hΘ12.le hΘ34 hη20 (by linarith) (U := landauBox Θ η 0 (3 * η)) le_rfl ?_ ?_
      ?_).mono hball
    · intro s hs
      have := hs.1
      linarith
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
      powerLagG M σ X s = LSeries (fun n => (powerPrimeLagCoeff M σ X n : ℂ)) s := by
    intro s hs
    exact (LSeries_powerPrimeLagCoeff_eq hθ hΘ12.le (by linarith) (by linarith)).symm
  exact landau_local_summability_transfer (a := powerPrimeLagCoeff M σ X)
    (powerPrimeLagCoeff_nonneg hM)
    (σ₁ := Θ - 1 / 2 + η) (h := η) hηpos hsum (R := R) (G := powerLagG M σ X) hGd hagree
    (σ := Θ - 1 / 2 - η / 4) (by rw [hRval]; linarith)

/-! ## The criterion -/


/-- **The power-saving prime-lag criterion.**  If `a_p ≤ M p^σ` on the primes `p > X` with
`0 ≤ σ ≤ ¼`, every zero satisfies `Re ρ ≤ ½ + σ`. -/
theorem re_le_half_add_of_primeLag_le_rpow {X : ℕ} {M σ₀ : ℝ} (hσ0 : 0 ≤ σ₀) (hσ4 : σ₀ ≤ 1 / 4)
    (hM : ∀ p : ℕ, p.Prime → X < p → integerLag p ≤ M * Real.exp (σ₀ * Real.log p))
    (q' : XiZeroCopy) : (q'.1 : ℂ).re ≤ 1 / 2 + σ₀ := by
  by_contra hq'
  push Not at hq'
  haveI : Nonempty XiZeroCopy := ⟨q'⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘσ : 1 / 2 + σ₀ < Θ := lt_of_lt_of_le hq' (re_le_zeroReSup q')
  have hΘ12 : 1 / 2 < Θ := by linarith
  have hΘ34 : Θ ≤ 3 / 4 := by
    obtain ⟨M₃, hM₃⟩ := exists_growth_bound_of_primeLag_le_rpow (X := X) hσ0 hM
    refine zeroReSup_le fun q => ?_
    have h := re_le_half_add_of_weilLagFunctionReal_le_exp (le_max_of_le_left hσ0)
      (max_lt (by linarith) (by norm_num)) hM₃ q
    rw [max_eq_right hσ4] at h
    linarith
  obtain ⟨η, hηpos, hη20, hηΘ, hησ, -, hsumσ⟩ := powerLag_transfer_step hσ0 hM hΘ34 hΘσ
  set c : ℕ → ℂ := fun n => (powerPrimeLagCoeff M σ₀ X n : ℂ) with hc
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
  have hfin : (xiZeroSet_weilLagFunctionCriterion ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet_weilLagFunctionCriterion ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
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
    have hmemK : (q.1 : ℂ) ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
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
  obtain ⟨C, hC⟩ := landauG_ray_lower_bound (M := 0) hθ hΘ34 hη20 hηpos q₀ hβ₀ hβ₀' hmaxq
  -- the proper-power series is bounded on the closed ray segment
  have hTc : ContinuousOn (fun t : ℝ => LSeries (fun n => (properCoeff 0 n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hd : DifferentiableAt ℂ (LSeries (fun n => (properCoeff 0 n : ℂ))) ((q₀.1 : ℂ) - 1 / 2 + t) := by
      apply differentiableAt_LSeries_properCoeff hθ hΘ12.le
      simp [hq₀]; linarith [ht.1]
    have hc : ContinuousAt (fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) t :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    exact (ContinuousAt.comp (g := LSeries (fun n => (properCoeff 0 n : ℂ)))
      (f := fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) hd.continuousAt hc).continuousWithinAt
  obtain ⟨BT, hBT⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hTc
  -- the small-prime and shifted series are bounded on the closed ray segment
  have hEc : ContinuousOn (fun t : ℝ =>
      LSeries (fun n => (smallPrimeOnlyCoeff X n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t) -
        (M : ℂ) * LSeries (fun n => (shiftedPrimeCoeff σ₀ X n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hd1 := differentiable_LSeries_smallPrimeOnlyCoeff X ((q₀.1 : ℂ) - 1 / 2 + t)
    have hd2 : DifferentiableAt ℂ (LSeries (fun n => (shiftedPrimeCoeff σ₀ X n : ℂ)))
        ((q₀.1 : ℂ) - 1 / 2 + t) := by
      apply differentiableAt_LSeries_shiftedPrimeCoeff
      simp [hq₀]; linarith [ht.1]
    have hc : ContinuousAt (fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) t :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    have h1 := ContinuousAt.comp (g := LSeries (fun n => (smallPrimeOnlyCoeff X n : ℂ)))
      (f := fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) hd1.continuousAt hc
    have h2 := ContinuousAt.comp (g := LSeries (fun n => (shiftedPrimeCoeff σ₀ X n : ℂ)))
      (f := fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) hd2.continuousAt hc
    exact (h1.sub (h2.const_mul (M : ℂ))).continuousWithinAt
  obtain ⟨BE, hBE⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hEc
  have hC' : ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      ‖aliasedWeight q₀‖ / t - (C + BT + BE) ≤ ‖powerLagG M σ₀ X ((q₀.1 : ℂ) - 1 / 2 + t)‖ := by
    intro t ht ht4
    have h1 := hC t ht ht4
    have h2 := hBT t ⟨ht.le, ht4⟩
    have h3 := hBE t ⟨ht.le, ht4⟩
    have e : powerLagG M σ₀ X ((q₀.1 : ℂ) - 1 / 2 + t) =
        (landauG 0 ((q₀.1 : ℂ) - 1 / 2 + t) -
          LSeries (fun n => (properCoeff 0 n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t)) -
        (LSeries (fun n => (smallPrimeOnlyCoeff X n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t) -
          (M : ℂ) * LSeries (fun n => (shiftedPrimeCoeff σ₀ X n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t)) := by
      unfold powerLagG primeOnlyG; ring
    rw [e]
    have h4 := norm_sub_norm_le (landauG 0 ((q₀.1 : ℂ) - 1 / 2 + t))
      (LSeries (fun n => (properCoeff 0 n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
    have h5 := norm_sub_norm_le (landauG 0 ((q₀.1 : ℂ) - 1 / 2 + t) -
          LSeries (fun n => (properCoeff 0 n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
        (LSeries (fun n => (smallPrimeOnlyCoeff X n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t) -
          (M : ℂ) * LSeries (fun n => (shiftedPrimeCoeff σ₀ X n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
    linarith
  -- the ray box
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  have hγ₀im : ρ₀.im = γ₀ := by rw [hγ₀]; unfold zeroOrdinate; rw [hq₀]
  obtain ⟨r, hrpos, hr1, hrgap⟩ := exists_pos_le_ordinate_gap γ₀
  set U₀ : Set ℂ := landauBox ρ₀.re 0 γ₀ r with hU₀
  have hU₀open : IsOpen U₀ := isOpen_landauBox _ _ _ _
  have hGd : DifferentiableOn ℂ (powerLagG M σ₀ X) U₀ := by
    refine differentiableOn_powerLagG (θ := Θ) (η := η) (t₀ := γ₀) (r := r) hθ hΘ12.le hΘ34 hη20
      hr1 (U := U₀) ?_ ?_ ?_ ?_
    · intro s hs
      exact ⟨by linarith [hs.1], hs.2.1, hs.2.2⟩
    · intro s hs
      linarith [hs.1]
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
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => powerLagG M σ₀ X (ℓ t)) U := fun t ht =>
    ((hGd.analyticAt (hU₀open.mem_nhds (hℓU₀ t ht))).restrictScalars).comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h18U : (1 / 8 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hagree : ∀ s : ℂ, Θ - 1 / 2 < s.re → LSeries c s = powerLagG M σ₀ X s := fun s hs =>
    LSeries_powerPrimeLagCoeff_eq hθ hΘ12.le hs (by linarith)
  have hfg : (fun t : ℝ => LSeries c (ℓ t)) =ᶠ[𝓝 (1 / 8 : ℝ)]
      (fun t : ℝ => powerLagG M σ₀ X (ℓ t)) := by
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
  obtain ⟨C', hC0, h3⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C + BT + BE ≤ C' :=
    ⟨max (C + BT + BE) 0, le_max_right _ _, le_max_left _ _⟩
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
  have hGb : Bd < ‖powerLagG M σ₀ X (ℓ t₀)‖ := by
    have h1 := hC' t₀ ht₀pos ht₀4.le
    rw [← hℓeq] at h1
    -- `‖W₀‖/(2t₀) ≥ 2(Bd + C' + 1)` gives `‖W₀‖/t₀ ≥ 4(Bd + C' + 1)`
    have h4 : ‖aliasedWeight q₀‖ / t₀ = 2 * (‖aliasedWeight q₀‖ / (2 * t₀)) := by
      field_simp
    linarith
  have hEq : LSeries c (ℓ t₀) = powerLagG M σ₀ X (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith


/-- **The power-saving prime-lag criterion on `[0, ½)`.**  If `a_p ≤ M p^σ` on the primes `p > X`
with `0 ≤ σ < ½`, every zero satisfies `Re ρ ≤ ½ + σ`.  For `σ ≤ ¼` this is the Landau argument;
for `σ ≥ ¼` it is the growth bound. -/
theorem re_le_half_add_of_primeLag_le_rpow' {X : ℕ} {M σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (hM : ∀ p : ℕ, p.Prime → X < p → integerLag p ≤ M * Real.exp (σ * Real.log p))
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 1 / 2 + σ := by
  rcases le_or_gt σ (1 / 4) with h4 | h4
  · exact re_le_half_add_of_primeLag_le_rpow hσ0 h4 hM q
  · obtain ⟨M₃, hM₃⟩ := exists_growth_bound_of_primeLag_le_rpow (X := X) hσ0 hM
    have h := re_le_half_add_of_weilLagFunctionReal_le_exp (le_max_of_le_left hσ0)
      (max_lt hσ (by norm_num)) hM₃ q
    rwa [max_eq_left h4.le] at h

/-- **The single-prime JAS level is exactly the half-plane level.**  Single-prime positivity on
the primes `p > X` at a level `0 ≤ σ < ½` gives `Re ρ ≤ ½ + σ` for every zero. -/
theorem xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove_sharp {X : ℕ} {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < 1 / 2) (h : JasSinglePrimePositiveAbove X σ) : XiZeroHalfPlaneBound σ := by
  have hb := jasSinglePrimePositiveAbove_iff.mp h
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  exact re_le_half_add_of_primeLag_le_rpow' (X := X) (M := poleSharpConstant) hσ0 hσ
    (fun p hp hpX => (le_abs_self _).trans (hb ⟨p, hp⟩ hpX)) q

/-- **The single-prime JAS abscissa is `sup Re ρ − ½`.**  For `0 ≤ σ < ½`: single-prime positivity
at level `σ` on large primes gives the half-plane bound `σ`, and every half-plane bound `α < σ`
gives single-prime positivity at level `σ` on large primes. -/
theorem jasSinglePrime_level_eq_halfPlane_level_sharp {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    ((∃ X : ℕ, JasSinglePrimePositiveAbove X σ) → XiZeroHalfPlaneBound σ) ∧
      (∀ alpha : ℝ, alpha < σ → XiZeroHalfPlaneBound alpha →
        ∃ X : ℕ, JasSinglePrimePositiveAbove X σ) :=
  ⟨fun ⟨_, hX⟩ => xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove_sharp hσ0 hσ hX,
    fun _ h1 hXi => exists_jasSinglePrimePositiveAbove_of_xiZeroHalfPlaneBound_of_lt h1 hXi⟩

end

end RHTower
