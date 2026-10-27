import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensBudgetOfACurveIsTheRepulsionEnergyOfItsSpectrum

/-!
# A Mertens budget is purity with a simple spectrum

The converse of P48, in every genus: the `𝔽_q` form of P45. Let `h_m` be the Mertens row of a
spectrum `β` (coefficients of `Π_i (1 − β_i u)⁻¹`) and suppose a budget
`Σ_{m ≤ M} |h_m|² ≤ S M + B`. Then `|h_m|² ≤ K(m + 1)`, so `H(z) = Σ h_m z^m` converges on the
unit disc, and there `H(z) Π_i (1 − β_i z) = 1` (`tsum_spectralMertensRow_mul_eval`).

* **No eigenvalue outside the circle** (`norm_le_one_of_spectralMertens_budget`): at `z = β_i⁻¹`
  the product vanishes.
* **No collision on the circle** (`norm_lt_one_of_spectralMertens_budget_of_eq`): if
  `β_i = β_j`, `i ≠ j`, `|β_i| = 1`, then at `z = (1 − ε) β̄_i` the product is `O(ε²)`, so
  `|H(z)| ≥ 2^{−n} ε⁻²`, while `|h_m| ≤ |h_m|²/(2t) + t/2` gives `|H(z)| ≤ K/(2t ε²) + t/(2ε)`;
  `t = 2^{−n}/ε` forces `1 ≤ K ε 4^n`.
* **The genus-free budget law** (`curveMertens_budget_iff`). For a curve datum, a Mertens budget
  exists exactly for a pure simple spectrum, and then its slope is the repulsion energy (P48).

So over `𝔽_q` the Mertens budget is purity together with simplicity of the Frobenius spectrum, as
over `ℤ` a Mertens budget forces RH and simple zeros (P45); the prime-error budget is purity alone
and counts multiplicities (P42).
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {ι : Type*} [Fintype ι]

/-- The polynomial `P(u) = Π_i (1 − β_i u)`. -/
def spectralPolynomial (β : ι → ℂ) : Polynomial ℂ := ∏ i, (1 - Polynomial.C (β i) * Polynomial.X)

theorem prod_geom_mul_spectralPolynomial (β : ι → ℂ) :
    (∏ i, PowerSeries.mk fun k => β i ^ k) * (spectralPolynomial β : PowerSeries ℂ) = 1 := by
  have hP : (spectralPolynomial β : PowerSeries ℂ) =
      ∏ i, (1 - PowerSeries.C (β i) * PowerSeries.X) := by
    have := map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
      (fun i => 1 - Polynomial.C (β i) * Polynomial.X) univ
    simp only [map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X] at this
    exact this
  rw [hP, ← prod_mul_distrib]
  simp_rw [geom_mul_one_sub]
  exact prod_const_one

/-- **The generating function inverts `P`.** If `Σ h_m z^m` converges absolutely, then
`(Σ h_m z^m) Π_i (1 − β_i z) = 1`. -/
theorem tsum_spectralMertensRow_mul_eval {β : ι → ℂ} {z : ℂ}
    (hs : Summable fun m => ‖spectralMertensRow β m * z ^ m‖) :
    (∑' m, spectralMertensRow β m * z ^ m) * ∏ i, (1 - β i * z) = 1 := by
  have hfin : ∀ m ∉ range ((spectralPolynomial β).natDegree + 1),
      (spectralPolynomial β).coeff m * z ^ m = 0 := fun m hm => by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hm), zero_mul]
  have hQs : Summable fun m => ‖(spectralPolynomial β).coeff m * z ^ m‖ :=
    summable_of_ne_finset_zero (s := range ((spectralPolynomial β).natDegree + 1))
      fun m hm => by rw [hfin m hm, norm_zero]
  have hQ : ∑' m, (spectralPolynomial β).coeff m * z ^ m = ∏ i, (1 - β i * z) := by
    rw [tsum_eq_sum hfin, ← Polynomial.eval_eq_sum_range, spectralPolynomial,
      Polynomial.eval_prod]
    simp
  rw [← hQ, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hQs]
  have hterm : ∀ n, ∑ kl ∈ antidiagonal n, spectralMertensRow β kl.1 * z ^ kl.1 *
      ((spectralPolynomial β).coeff kl.2 * z ^ kl.2) = if n = 0 then 1 else 0 := by
    intro n
    have hc := congrArg (PowerSeries.coeff n) (prod_geom_mul_spectralPolynomial β)
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at hc
    have hkl : ∀ kl ∈ antidiagonal n, spectralMertensRow β kl.1 * z ^ kl.1 *
        ((spectralPolynomial β).coeff kl.2 * z ^ kl.2) =
        PowerSeries.coeff kl.1 (∏ i, PowerSeries.mk fun k => β i ^ k) *
          PowerSeries.coeff kl.2 (spectralPolynomial β : PowerSeries ℂ) * z ^ n := by
      intro kl hkl
      rw [Polynomial.coeff_coe, ← mem_antidiagonal.mp hkl, pow_add, spectralMertensRow]
      ring
    rw [sum_congr rfl hkl, ← sum_mul, hc]
    split_ifs with h
    · rw [h, pow_zero, one_mul]
    · rw [zero_mul]
  simp_rw [hterm]
  exact tsum_ite_eq 0 (fun _ => (1 : ℂ))

/-- `h_0 = 1`. -/
theorem spectralMertensRow_zero (β : ι → ℂ) : spectralMertensRow β 0 = 1 := by
  simp [spectralMertensRow, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]

/-- A budget bounds every coefficient: `|h_m|² ≤ K(m + 1)`. -/
theorem exists_norm_sq_le_of_spectralMertens_budget {β : ι → ℂ} {S B : ℝ}
    (hE : ∀ M : ℕ, ∑ m ∈ Icc 1 M, ‖spectralMertensRow β m‖ ^ 2 ≤ S * M + B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ‖spectralMertensRow β m‖ ^ 2 ≤ K * (m + 1) := by
  refine ⟨|S| + |B| + 1, by positivity, fun m => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [spectralMertensRow_zero, norm_one]
    have := abs_nonneg S; have := abs_nonneg B
    push_cast; nlinarith
  · have h1 : ‖spectralMertensRow β m‖ ^ 2 ≤ ∑ k ∈ Icc 1 m, ‖spectralMertensRow β k‖ ^ 2 :=
      single_le_sum (f := fun k => ‖spectralMertensRow β k‖ ^ 2) (fun _ _ => sq_nonneg _)
        (mem_Icc.mpr ⟨hm, le_rfl⟩)
    have h2 := hE m
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [le_abs_self S, le_abs_self B, abs_nonneg S, abs_nonneg B]

/-- On the unit disc the generating series converges absolutely. -/
theorem summable_spectralMertensRow_mul {β : ι → ℂ} {K : ℝ}
    (hb : ∀ m : ℕ, ‖spectralMertensRow β m‖ ^ 2 ≤ K * (m + 1)) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun m => ‖spectralMertensRow β m * z ^ m‖ := by
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (((summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left K).add
      ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (K + 1)))
  have h1 : ‖spectralMertensRow β m‖ ≤ ‖spectralMertensRow β m‖ ^ 2 + 1 := by
    nlinarith [sq_nonneg (‖spectralMertensRow β m‖ - 1)]
  rw [norm_mul, norm_pow]
  calc ‖spectralMertensRow β m‖ * ‖z‖ ^ m ≤ (K * (m + 1) + 1) * ‖z‖ ^ m :=
        mul_le_mul_of_nonneg_right (h1.trans (by linarith [hb m])) (by positivity)
    _ = K * ((m : ℝ) ^ 1 * ‖z‖ ^ m) + (K + 1) * ‖z‖ ^ m := by ring

/-- **No eigenvalue outside the circle.** -/
theorem norm_le_one_of_spectralMertens_budget {β : ι → ℂ} {S B : ℝ}
    (hE : ∀ M : ℕ, ∑ m ∈ Icc 1 M, ‖spectralMertensRow β m‖ ^ 2 ≤ S * M + B) (i : ι) :
    ‖β i‖ ≤ 1 := by
  by_contra h
  simp only [not_le] at h
  obtain ⟨K, hK, hb⟩ := exists_norm_sq_le_of_spectralMertens_budget hE
  have hβ0 : β i ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
  have hz : ‖(β i)⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have := tsum_spectralMertensRow_mul_eval (summable_spectralMertensRow_mul hb hz)
  rw [prod_eq_zero (mem_univ i) (by rw [mul_inv_cancel₀ hβ0, sub_self]), mul_zero] at this
  exact zero_ne_one this

/-- The AM–GM majorant: for `|z| = s < 1` and `t > 0`,
`|H(z)| ≤ K/(2t(1 − s)²) + t/(2(1 − s))`. -/
theorem norm_tsum_spectralMertensRow_le {β : ι → ℂ} {K : ℝ}
    (hb : ∀ m : ℕ, ‖spectralMertensRow β m‖ ^ 2 ≤ K * (m + 1)) {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : ‖z‖ < 1) :
    ‖∑' m, spectralMertensRow β m * z ^ m‖ ≤
      K / (2 * t) / (1 - ‖z‖) ^ 2 + t / 2 / (1 - ‖z‖) := by
  have hs := summable_spectralMertensRow_mul hb hz
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hmaj : HasSum (fun m : ℕ => K / (2 * t) * ((m : ℝ) * ‖z‖ ^ m) +
      (K / (2 * t) + t / 2) * ‖z‖ ^ m)
      (K / (2 * t) * (‖z‖ / (1 - ‖z‖) ^ 2) + (K / (2 * t) + t / 2) * (1 - ‖z‖)⁻¹) :=
    ((hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left _).add
      ((hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_left _)
  have hle : ∀ m : ℕ, ‖spectralMertensRow β m * z ^ m‖ ≤
      K / (2 * t) * ((m : ℝ) * ‖z‖ ^ m) + (K / (2 * t) + t / 2) * ‖z‖ ^ m := by
    intro m
    have hamgm : ‖spectralMertensRow β m‖ ≤ ‖spectralMertensRow β m‖ ^ 2 / (2 * t) + t / 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖spectralMertensRow β m‖ - t)]
    rw [norm_mul, norm_pow]
    calc ‖spectralMertensRow β m‖ * ‖z‖ ^ m
        ≤ (K * (m + 1) / (2 * t) + t / 2) * ‖z‖ ^ m := by
          refine mul_le_mul_of_nonneg_right (hamgm.trans ?_) (by positivity)
          gcongr
          exact hb m
      _ = K / (2 * t) * ((m : ℝ) * ‖z‖ ^ m) + (K / (2 * t) + t / 2) * ‖z‖ ^ m := by ring
  calc ‖∑' m, spectralMertensRow β m * z ^ m‖
      ≤ ∑' m, ‖spectralMertensRow β m * z ^ m‖ := norm_tsum_le_tsum_norm hs
    _ ≤ K / (2 * t) * (‖z‖ / (1 - ‖z‖) ^ 2) + (K / (2 * t) + t / 2) * (1 - ‖z‖)⁻¹ :=
        (hs.tsum_le_tsum hle hmaj.summable).trans_eq hmaj.tsum_eq
    _ = K / (2 * t) / (1 - ‖z‖) ^ 2 + t / 2 / (1 - ‖z‖) := by
        have h1 : 1 - ‖z‖ ≠ 0 := by linarith
        field_simp
        ring

/-- **No collision on the circle.** A unimodular eigenvalue of a spectrum with a Mertens budget
is simple. -/
theorem norm_lt_one_of_spectralMertens_budget_of_eq [DecidableEq ι] {β : ι → ℂ} {S B : ℝ}
    (hE : ∀ M : ℕ, ∑ m ∈ Icc 1 M, ‖spectralMertensRow β m‖ ^ 2 ≤ S * M + B) {i j : ι}
    (hij : i ≠ j) (heq : β i = β j) : ‖β i‖ < 1 := by
  by_contra h
  have hu : ‖β i‖ = 1 := le_antisymm (norm_le_one_of_spectralMertens_budget hE i) (not_lt.mp h)
  have hle := norm_le_one_of_spectralMertens_budget hE
  obtain ⟨K, hK, hb⟩ := exists_norm_sq_le_of_spectralMertens_budget hE
  -- a small `ε` with `K ε 4ⁿ < 1`
  set N : ℝ := (2 : ℝ) ^ Fintype.card ι with hN
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  set ε : ℝ := min (1 / 2) (1 / (2 * (K * N ^ 2 + 1))) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεK : K * N ^ 2 * ε < 1 := by
    have h1 : ε * (2 * (K * N ^ 2 + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [mul_nonneg hK (sq_nonneg N)]
  -- the point `z = (1 − ε) β̄_i`
  set z : ℂ := ((1 - ε : ℝ) : ℂ) * starRingEnd ℂ (β i) with hz
  have hzn : ‖z‖ = 1 - ε := by
    rw [hz, norm_mul, Complex.norm_conj, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hz1 : ‖z‖ < 1 := by rw [hzn]; linarith
  have hfac : ∀ k, β k = β i → 1 - β k * z = (ε : ℂ) := by
    intro k hk
    rw [hk, hz, ← mul_assoc, mul_comm (β i), mul_assoc, Complex.mul_conj', hu]
    push_cast; ring
  have hfac2 : ∀ k, ‖1 - β k * z‖ ≤ 2 := fun k => by
    calc ‖1 - β k * z‖ ≤ ‖(1 : ℂ)‖ + ‖β k * z‖ := norm_sub_le _ _
      _ ≤ 2 := by
          rw [norm_one, norm_mul, hzn]
          nlinarith [hle k, norm_nonneg (β k)]
  -- `|Π (1 − β_k z)| ≤ ε² 2ⁿ`
  have hprod : ‖∏ k, (1 - β k * z)‖ ≤ ε * ε * N := by
    rw [← mul_prod_erase univ _ (mem_univ i), ← mul_prod_erase _ _ (mem_erase.mpr ⟨hij.symm,
      mem_univ j⟩), hfac i rfl, hfac j heq.symm, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε0, ← mul_assoc]
    gcongr
    rw [norm_prod]
    calc ∏ k ∈ (univ.erase i).erase j, ‖1 - β k * z‖ ≤ ∏ _k ∈ (univ.erase i).erase j, (2 : ℝ) :=
          prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => hfac2 k
      _ = 2 ^ ((univ.erase i).erase j).card := prod_const _
      _ ≤ N := pow_le_pow_right₀ (by norm_num)
          ((card_le_card ((erase_subset _ _).trans (erase_subset _ _))).trans (by simp))
  -- `1 = |H(z)| |Π| ≤ |H(z)| ε² 2ⁿ`
  have hH := tsum_spectralMertensRow_mul_eval (summable_spectralMertensRow_mul hb hz1)
  have hone : 1 ≤ ‖∑' m, spectralMertensRow β m * z ^ m‖ * (ε * ε * N) := by
    have := congrArg norm hH
    rw [norm_mul, norm_one] at this
    rw [← this]
    exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
  -- the majorant at `t = 1/(N ε)`
  have hup := norm_tsum_spectralMertensRow_le hb (t := 1 / (N * ε)) (by positivity) hz1
  rw [hzn, show 1 - (1 - ε) = ε by ring] at hup
  have hval : (K / (2 * (1 / (N * ε))) / ε ^ 2 + 1 / (N * ε) / 2 / ε) * (ε * ε * N) =
      K * N ^ 2 * ε / 2 + 1 / 2 := by
    field_simp
  have := (hone.trans (mul_le_mul_of_nonneg_right hup (by positivity))).trans_eq hval
  linarith

/-- **The genus-free Mertens budget law.** A curve datum has a Mertens budget exactly when it is pure
with a simple spectrum; the slope is then the repulsion energy (P48). -/
theorem curveMertens_budget_iff [DecidableEq ι] [Nonempty ι]
    (D : ArithmeticCastelnuovoSeveri.CurveDatum ι) :
    (∃ S B : ℝ, ∀ M : ℕ, ∑ m ∈ Icc 1 M, ‖spectralMertensRow D.β m‖ ^ 2 ≤ S * M + B) ↔
      (∀ i, ‖D.β i‖ = 1) ∧ Function.Injective D.β := by
  constructor
  · rintro ⟨S, B, hE⟩
    have hle := norm_le_one_of_spectralMertens_budget hE
    have hu : ∀ i, ‖D.β i‖ = 1 := fun i => by
      have hfe := congrArg norm (D.β_fePerm i)
      rw [norm_mul, norm_one] at hfe
      have h1 := hle (D.fePerm i)
      refine le_antisymm (hle i) ?_
      nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i))]
    refine ⟨hu, fun i j h => ?_⟩
    by_contra hij
    have := norm_lt_one_of_spectralMertens_budget_of_eq hE hij h
    rw [hu i] at this
    exact lt_irrefl _ this
  · rintro ⟨hu, hinj⟩
    exact ⟨_, 0, fun M => by simpa using spectralMertens_energy_le hinj hu M⟩

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
