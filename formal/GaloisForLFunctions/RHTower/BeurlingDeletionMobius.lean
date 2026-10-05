import GaloisForLFunctions.RHTower.BeurlingDeletionPerron
import GaloisForLFunctions.HTGeometry.MellinTwistedTestBound

/-!
# The Möbius function of a deletion set

Let `S` be a deletion set (`DeletionData α`, `0 < α < 1`).  Write `λ_S` for the indicator of the
`S`-numbers (integers all of whose prime factors lie in `S`; `lamS`) and `μ_S = μ λ_S` (`mobS`).

* **Euler product** (`LSeries_lamS_eq`).  For `Re s > 1`,
  `Σ λ_S(n) n^{−s} = ζ(s + 1 − α) exp(corr(s) + rem₁(s) − rem₂(s))`.
* `λ_S ⋆ μ_S = δ` (`convolution_lamS_mobS`), hence `L(μ_S, s) = E(s) Q(s)` with `E` and `Q` the
  factors of the Perron numerator (`LSeries_mobS_eq`).
* **Continuations.**  `L(μ_S, s) = E(s)Q(s)` is holomorphic on `Re s > α/2` under RH, and
  `L(λ_S, s) = H(α)/(s − α) + dslope H α s` with `H(s) = ζ_u(s + 1 − α) exp(corr + rem₁ − rem₂)`
  holomorphic on `Re s > α/2` (`LSeries_lamS_eq_residue`).
* **Möbius partial sums** (`exists_norm_sum_mobS_le`).  Under RH, `Σ_{n ≤ X} μ_S(n) ≪ X^{α/2 + η}`.
* **Rankin** (`sum_norm_mobS_mul_rpow_le`).  For `σ > α`,
  `Σ_{n ≤ N} |μ_S(n)| n^{−σ} ≤ exp(Σ_{p ∈ S} p^{−σ})`; so `Σ_{n ≤ y} |μ_S(n)| ≪ y^σ` and
  `Σ |μ_S(n)|/n < ∞`.
-/

open Complex Finset Filter Topology

noncomputable section

namespace RHTower.BeurlingDeletion

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

open Classical in
/-- `n` is an `S`-number: all of its prime factors lie in `S`. -/
def sNum (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∈ D.S

open Classical in
/-- The indicator `λ_S` of the `S`-numbers. -/
def lamR (n : ℕ) : ℝ := if D.sNum n then 1 else 0

/-- `λ_S` with complex values. -/
def lamS (n : ℕ) : ℂ := (D.lamR n : ℂ)

/-- `μ_S = μ λ_S`. -/
def mobS (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ) * D.lamS n

theorem sNum_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    D.sNum (m * n) ↔ D.sNum m ∧ D.sNum n := by
  unfold sNum
  rw [Nat.primeFactors_mul hm hn]
  simp only [ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

theorem lamR_nonneg (n : ℕ) : 0 ≤ D.lamR n := by
  classical
  unfold lamR; split_ifs <;> norm_num

theorem lamR_le_one (n : ℕ) : D.lamR n ≤ 1 := by
  classical
  unfold lamR; split_ifs <;> norm_num

theorem lamR_zero : D.lamR 0 = 0 := by
  classical
  simp [lamR, sNum]

theorem lamS_zero : D.lamS 0 = 0 := by simp [lamS, lamR_zero]

theorem mobS_zero : D.mobS 0 = 0 := by simp [mobS]

theorem norm_lamS_le (n : ℕ) : ‖D.lamS n‖ ≤ 1 := by
  rw [lamS, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (D.lamR_nonneg n)]
  exact D.lamR_le_one n

theorem norm_mobS_le_lamR (n : ℕ) : ‖D.mobS n‖ ≤ D.lamR n := by
  rw [mobS, norm_mul, lamS, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (D.lamR_nonneg n)]
  have : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [show ((ArithmeticFunction.moebius n : ℤ) : ℂ) = ((ArithmeticFunction.moebius n : ℤ) : ℝ) by
      push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * D.lamR n ≤ 1 * D.lamR n :=
        mul_le_mul_of_nonneg_right this (D.lamR_nonneg n)
    _ = D.lamR n := one_mul _

theorem norm_mobS_le (n : ℕ) : ‖D.mobS n‖ ≤ 1 := (D.norm_mobS_le_lamR n).trans (D.lamR_le_one n)

theorem lamS_mul (m n : ℕ) : D.lamS (m * n) = D.lamS m * D.lamS n := by
  classical
  rcases eq_or_ne m 0 with rfl | hm
  · simp [lamS_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [lamS_zero]
  unfold lamS lamR
  rw [D.sNum_mul hm hn]
  split_ifs <;> simp_all

/-! ## The Euler product of `λ_S` -/

/-- The completely multiplicative summand `λ_S(n) n^{−s}`. -/
def lamHom (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := D.lamS n * (n : ℂ) ^ (-s)
  map_zero' := by simp [lamS_zero]
  map_one' := by classical simp [lamS, lamR, sNum]
  map_mul' m n := by
    rw [D.lamS_mul, Nat.cast_mul]
    rcases eq_or_ne m 0 with rfl | hm
    · simp [lamS_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [lamS_zero]
    rw [Complex.natCast_mul_natCast_cpow]
    ring

theorem lamHom_apply (s : ℂ) (n : ℕ) : D.lamHom s n = D.lamS n * (n : ℂ) ^ (-s) := rfl

theorem lamHom_prime (s : ℂ) (p : Nat.Primes) :
    D.lamHom s p = D.ind p * ((p : ℕ) : ℂ) ^ (-s) := by
  classical
  rw [lamHom_apply]
  congr 1
  unfold lamS lamR sNum ind
  rw [p.2.primeFactors, Set.indicator_apply]
  by_cases h : (p : ℕ) ∈ D.S
  · rw [if_pos ⟨p.2.ne_zero, by simpa using h⟩, if_pos h]; simp
  · rw [if_neg (by simp [h]), if_neg h]; simp

theorem summable_norm_lamHom {s : ℂ} (hs : 1 < s.re) : Summable fun n => ‖D.lamHom s n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith))
  rw [lamHom_apply, norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lamS_zero, Real.zero_rpow (show -s.re ≠ 0 by linarith)]
  · rw [norm_natCast_cpow_neg n hn]
    calc ‖D.lamS n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (D.norm_lamS_le n) (by positivity)
      _ = _ := one_mul _

theorem LSeries_lamS_eq_tsum (s : ℂ) : LSeries D.lamS s = ∑' n, D.lamHom s n := by
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lamHom_apply, lamS_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', lamHom_apply, div_eq_mul_inv, Complex.cpow_neg]

/-- **The Euler product of `λ_S`.**  For `Re s > 1`,
`Σ λ_S(n) n^{−s} = ζ(s + 1 − α) exp(corr(s) + rem₁(s) − rem₂(s))`. -/
theorem LSeries_lamS_eq (hα0 : 0 < α) (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries D.lamS s = riemannZeta (s + ((1 - α : ℝ) : ℂ)) *
      Complex.exp (D.corr s + D.rem₁ s - rem₂ α s) := by
  classical
  set w : ℂ := s + ((1 - α : ℝ) : ℂ) with hw
  have hw1 : 1 < w.re := by rw [hw]; simp; linarith
  set A : Nat.Primes → ℂ := fun p => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) with hA
  set B : Nat.Primes → ℂ := fun p => D.ind p * A p with hB
  have h1 : LSeries D.lamS s = Complex.exp (∑' p : Nat.Primes, B p) := by
    rw [D.LSeries_lamS_eq_tsum s, ← EulerProduct.exp_tsum_primes_log_eq_tsum
      (D.summable_norm_lamHom hs)]
    congr 1
    refine tsum_congr fun p => ?_
    rw [lamHom_prime, hB, hA]
    simp only
    unfold ind
    rw [Set.indicator_apply]
    split_ifs <;> simp
  set P : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w) with hP
  set Lw : Nat.Primes → ℂ := fun p => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-w)) with hLw
  have hPs : Summable P := by
    refine Summable.of_norm_bounded (summable_prime_rpow hw1) fun p => ?_
    rw [hP, norm_natCast_cpow_neg _ p.2.pos]
  have hLws : Summable Lw := (summable_neg_log w hw1).of_norm
  have hcoeff : Summable fun p : Nat.Primes => D.coeff p * ((p : ℕ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded ((summable_prime_rpow hs).mul_left 2) fun p => ?_
    rw [norm_mul, norm_natCast_cpow_neg _ p.2.pos]
    exact mul_le_mul_of_nonneg_right (D.norm_coeff_le hα p) (by positivity)
  have hr1 : Summable fun p : Nat.Primes =>
      D.S.indicator (fun n : ℕ => logRem ((n : ℂ) ^ (-(s + 0)))) (p : ℕ) :=
    Summable.of_norm_bounded (D.summable_maj₁ hα0 hα (δ := 1 / 2)
      (by norm_num)) fun p => D.norm_rem₁_term_le hα0 (by norm_num) p (by linarith)
  have hr2 : Summable fun p : Nat.Primes => logRem (((p : ℕ) : ℂ) ^ (-w)) :=
    Summable.of_norm_bounded (summable_maj₂ hα (δ := 1 / 2) (by norm_num)) fun p =>
      norm_rem₂_term_le hα (by norm_num) p (by linarith)
  have hBdec : ∀ p : Nat.Primes, B p = P p + D.coeff p * ((p : ℕ) : ℂ) ^ (-s) +
      D.S.indicator (fun n : ℕ => logRem ((n : ℂ) ^ (-(s + 0)))) (p : ℕ) := by
    intro p
    have hcf : D.coeff p = D.ind p - (delWeight α p : ℂ) := by
      unfold coeff ind; rw [if_pos p.2]
    have hdw := cpow_delWeight (α := α) (p : ℕ) p.2.pos s
    rw [← hw] at hdw
    simp only [hB, hA, hP]
    rw [hcf, ← hdw]
    unfold ind logRem
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp only [add_zero] <;> ring
  have hPdec : ∀ p : Nat.Primes, P p = Lw p - logRem (((p : ℕ) : ℂ) ^ (-w)) := by
    intro p; simp only [hP, hLw, logRem]; ring
  have hsumB : ∑' p, B p = (∑' p, Lw p) - rem₂ α s + D.corr s + D.rem₁ s := by
    rw [tsum_congr hBdec, (hPs.add hcoeff).tsum_add hr1, hPs.tsum_add hcoeff,
      tsum_congr hPdec, hLws.tsum_sub hr2, tsum_primes_eq_LSeries D.coeff
        (fun n hn => by unfold coeff; rw [if_neg hn]) s, ← D.corr_eq_LSeries hα0 hα hs]
    unfold rem₂ rem₁
    rw [← hw]
  rw [h1, hsumB, show (∑' p, Lw p) - rem₂ α s + D.corr s + D.rem₁ s =
      (∑' p, Lw p) + (D.corr s + D.rem₁ s - rem₂ α s) by ring, Complex.exp_add,
    riemannZeta_eulerProduct_exp_log hw1]

/-! ## `μ_S` -/

theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

/-- `λ_S ⋆ μ_S = δ`. -/
theorem convolution_lamS_mobS : LSeries.convolution D.lamS D.mobS = LSeries.delta := by
  funext n
  rw [LSeries.convolution_def]
  simp only
  have hterm : ∀ x ∈ n.divisorsAntidiagonal, D.lamS x.1 * D.mobS x.2 =
      D.lamS n * (ArithmeticFunction.moebius x.2 : ℂ) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rw [mobS, ← hx.1, D.lamS_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [Nat.sum_divisorsAntidiagonal (fun _ b => (ArithmeticFunction.moebius b : ℂ))]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.delta]
  have hsum : ∑ i ∈ n.divisors, (ArithmeticFunction.moebius (n / i) : ℂ) =
      ∑ i ∈ n.divisors, (ArithmeticFunction.moebius i : ℂ) :=
    Nat.sum_div_divisors n fun d => (ArithmeticFunction.moebius d : ℂ)
  rw [hsum, sum_divisors_moebius]
  unfold LSeries.delta
  split_ifs with h1
  · subst h1; classical simp [lamS, lamR, sNum]
  · simp

theorem lseriesSummable_lamS {s : ℂ} (hs : 1 < s.re) : LSeriesSummable D.lamS s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) (by linarith)
    ⟨1, fun n _ => by simpa using D.norm_lamS_le n⟩

theorem lseriesSummable_mobS {s : ℂ} (hs : 1 < s.re) : LSeriesSummable D.mobS s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) (by linarith)
    ⟨1, fun n _ => by simpa using D.norm_mobS_le n⟩

theorem LSeries_lamS_mul_mobS {s : ℂ} (hs : 1 < s.re) :
    LSeries D.lamS s * LSeries D.mobS s = 1 := by
  rw [← LSeries_convolution' (D.lseriesSummable_lamS hs) (D.lseriesSummable_mobS hs),
    convolution_lamS_mobS, LSeries_delta, Pi.one_apply]

/-- `L(μ_S, s) = E(s) Q(s)` on `Re s > 1`. -/
theorem LSeries_mobS_eq (hα0 : 0 < α) (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries D.mobS s = D.eFactor s * qFactor α s := by
  have h := D.LSeries_lamS_mul_mobS hs
  rw [D.LSeries_lamS_eq hα0 hα hs] at h
  have hsα : s ≠ (α : ℂ) := fun h' => by rw [h'] at hs; simp at hs; linarith
  have hw1 : 1 < (s + ((1 - α : ℝ) : ℂ)).re := by simp; linarith
  have hz : riemannZeta (s + ((1 - α : ℝ) : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw1.le
  rw [qFactor_eq hsα, eFactor]
  have he : Complex.exp (D.corr s + D.rem₁ s - rem₂ α s) ≠ 0 := Complex.exp_ne_zero _
  have hneg : -D.corr s - D.rem₁ s + rem₂ α s = -(D.corr s + D.rem₁ s - rem₂ α s) := by ring
  rw [hneg, Complex.exp_neg]
  field_simp
  linear_combination h

/-! ## Continuations -/

/-- A function continuous on a closed strip away from the band `|Im s| < 1`, of growth
`c (|t| + 3)^κ` for `|t| ≥ T`, is bounded by `K |t|^κ` on the strip where `|t| ≥ 1`. -/
theorem exists_strip_bound {G : ℂ → ℂ} {σ₀ σ₁ : ℝ}
    (hG : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| → ContinuousAt G s) {c κ T : ℝ}
    (hκ : 0 ≤ κ)
    (hT : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → T ≤ |s.im| → ‖G s‖ ≤ c * (|s.im| + 3) ^ κ) :
    ∃ K : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| → ‖G s‖ ≤ K * |s.im| ^ κ := by
  set T' := max T 1 with hT'
  set Kset : Set ℂ := Set.Icc σ₀ σ₁ ×ℂ (Set.Icc (-T') (-1) ∪ Set.Icc 1 T') with hKset
  have hK : IsCompact Kset := isCompact_Icc.reProdIm (isCompact_Icc.union isCompact_Icc)
  have hmem : ∀ s : ℂ, s ∈ Kset ↔ (σ₀ ≤ s.re ∧ s.re ≤ σ₁) ∧
      ((-T' ≤ s.im ∧ s.im ≤ -1) ∨ (1 ≤ s.im ∧ s.im ≤ T')) := by
    intro s; rw [hKset, Complex.mem_reProdIm]; simp [Set.mem_Icc]
  have hcont : ContinuousOn G Kset := by
    intro s hs
    rw [hmem] at hs
    refine (hG s hs.1.1 hs.1.2 ?_).continuousWithinAt
    rcases hs.2 with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h.1
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨|B| + |c| * 4 ^ κ, fun s h1 h2 h3 => ?_⟩
  have hpow1 : 1 ≤ |s.im| ^ κ := Real.one_le_rpow h3 hκ
  have hpos : 0 ≤ |s.im| ^ κ := by positivity
  by_cases hs : T' ≤ |s.im|
  · have h := hT s h1 h2 (le_trans (le_max_left _ _) hs)
    have h4 : (|s.im| + 3) ^ κ ≤ 4 ^ κ * |s.im| ^ κ := by
      rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hκ
    calc ‖G s‖ ≤ c * (|s.im| + 3) ^ κ := h
      _ ≤ |c| * (|s.im| + 3) ^ κ := mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (4 ^ κ * |s.im| ^ κ) := mul_le_mul_of_nonneg_left h4 (abs_nonneg c)
      _ ≤ (|B| + |c| * 4 ^ κ) * |s.im| ^ κ := by
          have : 0 ≤ |B| * |s.im| ^ κ := by positivity
          nlinarith
  · push Not at hs
    have hsK : s ∈ Kset := by
      rw [hmem]
      refine ⟨⟨h1, h2⟩, ?_⟩
      rcases le_or_gt 0 s.im with h | h
      · right; rw [abs_of_nonneg h] at h3 hs; exact ⟨h3, hs.le⟩
      · left; rw [abs_of_neg h] at h3 hs; constructor <;> linarith
    have hb := hB s hsK
    calc ‖G s‖ ≤ |B| := hb.trans (le_abs_self B)
      _ ≤ |B| * |s.im| ^ κ := le_mul_of_one_le_right (abs_nonneg B) hpow1
      _ ≤ (|B| + |c| * 4 ^ κ) * |s.im| ^ κ := by
          have : 0 ≤ |c| * 4 ^ κ * |s.im| ^ κ := by positivity
          nlinarith

theorem differentiableOn_eFactor (hα0 : 0 < α) (hα : α < 1) :
    DifferentiableOn ℂ D.eFactor {s | α / 2 < s.re} := by
  intro s hs
  have hU : IsOpen {s : ℂ | α / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 := (D.differentiableOn_corr hα0).differentiableAt (hU.mem_nhds hs)
  have h2 := (D.differentiableOn_rem₁ hα0 hα).differentiableAt (hU.mem_nhds hs)
  have h3 := (differentiableOn_rem₂ hα0 hα).differentiableAt (hU.mem_nhds hs)
  exact ((h1.neg.sub h2).add h3).cexp.differentiableWithinAt

/-- Under RH, `E(s) Q(s)` is holomorphic on `Re s > α/2`. -/
theorem differentiableOn_eFactor_mul_qFactor (hRH : RiemannHypothesis) (hα0 : 0 < α)
    (hα : α < 1) : DifferentiableOn ℂ (fun s => D.eFactor s * qFactor α s) {s | α / 2 < s.re} := by
  intro s hs
  have hs' : α / 2 < s.re := hs
  have hU : IsOpen {s : ℂ | α / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE := (D.differentiableOn_eFactor hα0 hα).differentiableAt (hU.mem_nhds hs)
  have hz := (analyticAt_zetaResidueUnit (s + ((1 - α : ℝ) : ℂ))).differentiableAt
  have hz' : DifferentiableAt ℂ (fun s : ℂ => zetaResidueUnit (s + ((1 - α : ℝ) : ℂ))) s :=
    hz.comp s (differentiableAt_id.add_const _)
  have hQ : DifferentiableAt ℂ (qFactor α) s :=
    (differentiableAt_id.sub_const _).div hz' (zetaResidueUnit_shift_ne_zero hRH hα hs')
  exact (hE.mul hQ).differentiableWithinAt

/-- The numerator `H(s) = ζ_u(s + 1 − α) exp(corr(s) + rem₁(s) − rem₂(s))` of `L(λ_S)`. -/
def lamNum (s : ℂ) : ℂ :=
  zetaResidueUnit (s + ((1 - α : ℝ) : ℂ)) * Complex.exp (D.corr s + D.rem₁ s - rem₂ α s)

theorem differentiableOn_lamNum (hα0 : 0 < α) (hα : α < 1) :
    DifferentiableOn ℂ D.lamNum {s | α / 2 < s.re} := by
  intro s hs
  have hU : IsOpen {s : ℂ | α / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 := (D.differentiableOn_corr hα0).differentiableAt (hU.mem_nhds hs)
  have h2 := (D.differentiableOn_rem₁ hα0 hα).differentiableAt (hU.mem_nhds hs)
  have h3 := (differentiableOn_rem₂ hα0 hα).differentiableAt (hU.mem_nhds hs)
  have hz := (analyticAt_zetaResidueUnit (s + ((1 - α : ℝ) : ℂ))).differentiableAt
  have hz' : DifferentiableAt ℂ (fun s : ℂ => zetaResidueUnit (s + ((1 - α : ℝ) : ℂ))) s :=
    hz.comp s (differentiableAt_id.add_const _)
  exact (hz'.mul ((h1.add h2).sub h3).cexp).differentiableWithinAt

theorem differentiableOn_dslope_lamNum (hα0 : 0 < α) (hα : α < 1) :
    DifferentiableOn ℂ (dslope D.lamNum (α : ℂ)) {s | α / 2 < s.re} := by
  have hU : IsOpen {s : ℂ | α / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (differentiableOn_dslope (hU.mem_nhds (by simp; linarith))).mpr
    (D.differentiableOn_lamNum hα0 hα)

theorem lamNum_div_eq {s : ℂ} (hs : s ≠ (α : ℂ)) :
    D.lamNum s / (s - α) = riemannZeta (s + ((1 - α : ℝ) : ℂ)) *
      Complex.exp (D.corr s + D.rem₁ s - rem₂ α s) := by
  have hw : s + ((1 - α : ℝ) : ℂ) ≠ 1 := by
    intro h; apply hs; push_cast at h; linear_combination h
  rw [lamNum, zetaResidueUnit_of_ne hw, show s + ((1 - α : ℝ) : ℂ) - 1 = s - α by push_cast; ring]
  have : s - α ≠ 0 := sub_ne_zero.mpr hs
  field_simp

theorem residue_add_dslope_eq {s : ℂ} (hs : s ≠ (α : ℂ)) :
    D.lamNum α / (s - α) + dslope D.lamNum (α : ℂ) s = D.lamNum s / (s - α) := by
  rw [dslope_of_ne _ hs, slope_def_field]
  have : s - α ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-- `L(λ_S, s) = H(α)/(s − α) + dslope H α s` on `Re s > 1`. -/
theorem LSeries_lamS_eq_residue (hα0 : 0 < α) (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    D.lamNum α / (s - α) + dslope D.lamNum (α : ℂ) s = LSeries D.lamS s := by
  have hsα : s ≠ (α : ℂ) := fun h' => by rw [h'] at hs; simp at hs; linarith
  rw [D.residue_add_dslope_eq hsα, D.lamNum_div_eq hsα, D.LSeries_lamS_eq hα0 hα hs]

/-- `|exp(corr + rem₁ − rem₂)| ≪_κ (|t| + 2)^κ` on `Re s ≥ α/2 + δ`. -/
theorem exists_norm_exp_corr_le (hα0 : 0 < α) (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, α / 2 + δ ≤ s.re →
      ‖Complex.exp (D.corr s + D.rem₁ s - rem₂ α s)‖ ≤ c * (|s.im| + 2) ^ κ := by
  set b : ℝ := 3 * D.baseConst (δ / 2) with hb
  set R : ℝ := (∑' p, D.maj₁ δ p) + ∑' p, maj₂ α δ p with hR
  refine ⟨Real.exp R * Real.exp (b ^ 2 / (4 * κ)), by positivity, fun s hs => ?_⟩
  have h1 := D.norm_corr_le hα0 hδ hs
  have h2 := D.norm_rem₁_le hα0 hα hδ hs
  have h3 := norm_rem₂_le hα hδ hs
  have hy : 1 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  rw [Complex.norm_exp]
  calc Real.exp (D.corr s + D.rem₁ s - rem₂ α s).re
      ≤ Real.exp (R + b * Real.sqrt (Real.log (|s.im| + 2))) := by
        refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
        calc ‖D.corr s + D.rem₁ s - rem₂ α s‖ ≤ ‖D.corr s‖ + ‖D.rem₁ s‖ + ‖rem₂ α s‖ :=
              (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
          _ ≤ 3 * D.baseConst (δ / 2) * Real.sqrt (Real.log (|s.im| + 2)) +
                (∑' p, D.maj₁ δ p) + ∑' p, maj₂ α δ p := by gcongr
          _ = R + b * Real.sqrt (Real.log (|s.im| + 2)) := by rw [hR, hb]; ring
    _ = Real.exp R * Real.exp (b * Real.sqrt (Real.log (|s.im| + 2))) := Real.exp_add _ _
    _ ≤ Real.exp R * (Real.exp (b ^ 2 / (4 * κ)) * (|s.im| + 2) ^ κ) := by
        gcongr; exact exp_mul_sqrt_log_le hκ hy
    _ = _ := by ring

/-- Under RH, `|L(λ_S, s)| ≪ (|t| + 3)^{2κ}` on `α/2 + δ ≤ Re s ≤ 3/2`, `|t| ≥ T`. -/
theorem exists_norm_lamS_cont_le (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : δ < α / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ c T : ℝ, 0 < c ∧ 1 ≤ T ∧ ∀ s : ℂ, α / 2 + δ ≤ s.re → s.re ≤ 3 / 2 → T ≤ |s.im| →
      ‖D.lamNum α / (s - α) + dslope D.lamNum (α : ℂ) s‖ ≤ c * (|s.im| + 3) ^ (2 * κ) := by
  obtain ⟨c, hc, hE⟩ := D.exists_norm_exp_corr_le hα0 hα hδ hκ
  obtain ⟨T₀, hT₀⟩ := ZetaGrowth.exists_norm_riemannZeta_two_sided hRH
    (δ := 1 / 2 - α / 2 + δ) (by linarith) (by linarith) hκ
  refine ⟨c, max T₀ 1, hc, le_max_right _ _, fun s hs1 hs2 hT => ?_⟩
  have him : s.im ≠ 0 := by
    intro h; rw [h, abs_zero] at hT; linarith [le_max_right T₀ 1]
  have hsα : s ≠ (α : ℂ) := fun h => him (by rw [h]; simp)
  rw [D.residue_add_dslope_eq hsα, D.lamNum_div_eq hsα, norm_mul]
  have hw : s + ((1 - α : ℝ) : ℂ) = ((s.re + (1 - α) : ℝ) : ℂ) + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hw]
  have hz := (hT₀ s.im (le_trans (le_max_left _ _) hT) (s.re + (1 - α)) (by linarith)
    (by linarith)).2
  have h3 : 0 < |s.im| + 3 := by positivity
  have hE' : ‖Complex.exp (D.corr s + D.rem₁ s - rem₂ α s)‖ ≤ c * (|s.im| + 3) ^ κ :=
    (hE s hs1).trans (by gcongr; linarith)
  rw [show 2 * κ = κ + κ by ring, Real.rpow_add h3]
  calc ‖riemannZeta (((s.re + (1 - α) : ℝ) : ℂ) + (s.im : ℂ) * I)‖ *
        ‖Complex.exp (D.corr s + D.rem₁ s - rem₂ α s)‖
      ≤ (|s.im| + 3) ^ κ * (c * (|s.im| + 3) ^ κ) := mul_le_mul hz hE' (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

/-! ## Möbius partial sums -/

/-- **Under RH, `Σ_{n ≤ X} μ_S(n) ≪ X^{α/2 + η}`.** -/
theorem exists_norm_sum_mobS_le (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → ‖∑ n ∈ Finset.Iic ⌊X⌋₊, D.mobS n‖ ≤ C * X ^ (α / 2 + η) := by
  set τ : ℝ := min (η / 8) (min (α / 8) ((1 - α) / 8)) with hτ
  have hτ0 : 0 < τ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hτη : τ ≤ η / 8 := min_le_left _ _
  have hτα : τ ≤ α / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hτα' : τ ≤ (1 - α) / 8 := (min_le_right _ _).trans (min_le_right _ _)
  set σ₀ : ℝ := α / 2 + τ with hσ₀
  obtain ⟨c, T, hc, hT1, hEQ⟩ := D.exists_norm_eFactor_mul_qFactor_le hRH hα0 hα
    (δ := τ) hτ0 (by linarith) hτ0
  have hcont : ∀ s : ℂ, α / 2 < s.re →
      ContinuousAt (fun s => D.eFactor s * qFactor α s) s := fun s hs =>
    ((D.differentiableOn_eFactor_mul_qFactor hRH hα0 hα).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).continuousAt
  obtain ⟨K, hK⟩ := exists_strip_bound (G := fun s => D.eFactor s * qFactor α s)
    (σ₀ := σ₀) (σ₁ := 3 / 2) (fun s h1 _ _ => hcont s (by linarith)) (by positivity : (0 : ℝ) ≤ 2 * τ)
    hEQ
  -- the left line
  have hlinecont : Continuous fun t : ℝ =>
      ‖D.eFactor ((σ₀ : ℂ) + t * I) * qFactor α ((σ₀ : ℂ) + t * I)‖ :=
    (continuous_iff_continuousAt.mpr fun t => (hcont _ (by simp; linarith)).comp
      (by fun_prop)).norm
  obtain ⟨K₀, hK₀0, hK₀⟩ := GaloisForLFunctions.HTGeometry.TestFunctionPerron.exists_bound_line
    hlinecont (by positivity : (0 : ℝ) ≤ 2 * τ) (K := c * 4 ^ (2 * τ)) (T := T) fun t ht => by
      have h := hEQ ((σ₀ : ℂ) + t * I) (by simp [hσ₀]) (by simp; linarith) (by simpa using ht)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at h
      have ht1 : 1 ≤ |t| := le_trans hT1 ht
      refine h.trans ?_
      rw [mul_assoc]
      gcongr
      rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hH : DifferentiableOn ℂ (fun s => (s - 1) * (D.eFactor s * qFactor α s))
      {s | α / 2 < s.re} :=
    (differentiableOn_id.sub_const 1).mul (D.differentiableOn_eFactor_mul_qFactor hRH hα0 hα)
  have hdiv : ∀ s : ℂ, s ≠ 1 → (s - 1) * (D.eFactor s * qFactor α s) / (s - 1) =
      D.eFactor s * qFactor α s := fun s hs => by
    field_simp [sub_ne_zero.mpr hs]
  obtain ⟨C, hC⟩ := GaloisForLFunctions.HTGeometry.SmoothedPerron.exists_norm_sum_sub_le
    D.mobS D.mobS_zero D.norm_mobS_le (a := α / 2) (σ₀ := σ₀) (by linarith) (by positivity)
    (by linarith) hH
    (fun s hs => by
      rw [hdiv s (fun h => by rw [h] at hs; simp at hs), D.LSeries_mobS_eq hα0 hα hs])
    (K := K) (T₀ := 1) (κ₁ := 2 * τ) (by linarith)
    (fun s h1 h2 h3 => by
      have hs1 : s ≠ 1 := fun h => by rw [h] at h3; norm_num at h3
      rw [hdiv s hs1]; exact hK s h1 h2 h3)
    (K₀ := K₀) (θ := 2 * τ) (by positivity) (by linarith)
    (fun t => by
      have hs1 : (σ₀ : ℂ) + t * I ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      rw [hdiv _ hs1]; exact hK₀ t)
    (κ := τ) hτ0
  refine ⟨max C 0, fun X hX => ?_⟩
  have h := hC X hX
  have hexp : (2 * τ + σ₀) / (1 + 2 * τ) + τ ≤ α / 2 + η := by
    have : (2 * τ + σ₀) / (1 + 2 * τ) ≤ 2 * τ + σ₀ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hH1 : (1 - 1) * (D.eFactor 1 * qFactor α 1) = 0 := by ring
  rw [hH1, zero_mul, sub_zero] at h
  calc ‖∑ n ∈ Finset.Iic ⌊X⌋₊, D.mobS n‖ ≤ C * X ^ ((2 * τ + σ₀) / (1 + 2 * τ) + τ) := h
    _ ≤ max C 0 * X ^ ((2 * τ + σ₀) / (1 + 2 * τ) + τ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * X ^ (α / 2 + η) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) (le_max_right _ _)

/-! ## Rankin's bound -/

theorem squarefree_sNum_of_mobS_ne_zero {n : ℕ} (h : D.mobS n ≠ 0) :
    Squarefree n ∧ D.sNum n := by
  classical
  unfold mobS lamS lamR at h
  by_cases hs : D.sNum n
  · refine ⟨?_, hs⟩
    rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree]
    intro hm; apply h; simp [hm]
  · simp [hs] at h

theorem norm_mobS_of_ne_zero {n : ℕ} (h : D.mobS n ≠ 0) : ‖D.mobS n‖ = 1 := by
  classical
  obtain ⟨hsq, hs⟩ := D.squarefree_sNum_of_mobS_ne_zero h
  rw [mobS, lamS, lamR, if_pos hs, ArithmeticFunction.moebius_apply_of_squarefree hsq]
  simp

/-- **Rankin's bound.**  For `σ > α`, `Σ_{n ≤ N} |μ_S(n)| n^{−σ} ≤ exp(Σ_{p ∈ S} p^{−σ})`. -/
theorem sum_norm_mobS_mul_rpow_le (hα0 : 0 < α) (hα : α < 1) {σ : ℝ} (hσ : α < σ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖D.mobS n‖ * (n : ℝ) ^ (-σ) ≤
      Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-σ)) n) := by
  classical
  set P : Finset ℕ := (Finset.Icc 1 N).filter (fun p => p ∈ D.S) with hP
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => D.prime p (Finset.mem_filter.mp hp).2
  set A : Finset ℕ := (Finset.Icc 1 N).filter (fun n => D.mobS n ≠ 0) with hA
  have hsum1 : ∑ n ∈ Finset.Icc 1 N, ‖D.mobS n‖ * (n : ℝ) ^ (-σ) =
      ∑ n ∈ A, (n : ℝ) ^ (-σ) := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rw [D.norm_mobS_of_ne_zero h, one_mul]
    · push Not at h; rw [h, norm_zero, zero_mul]
  have hinj : Set.InjOn Nat.primeFactors (A : Set ℕ) := by
    intro m hm n hn hmn
    have hm' := D.squarefree_sNum_of_mobS_ne_zero (Finset.mem_filter.mp hm).2
    have hn' := D.squarefree_sNum_of_mobS_ne_zero (Finset.mem_filter.mp hn).2
    rw [← Nat.prod_primeFactors_of_squarefree hm'.1, ← Nat.prod_primeFactors_of_squarefree hn'.1,
      hmn]
  have hsub : A.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨n, hn, rfl⟩ := hT
    obtain ⟨hnI, hn0⟩ := Finset.mem_filter.mp hn
    have hs := (D.squarefree_sNum_of_mobS_ne_zero hn0).2
    rw [Finset.mem_powerset]
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Icc]
    have hpn := Nat.le_of_mem_primeFactors hp
    refine ⟨⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le, hpn.trans (Finset.mem_Icc.mp hnI).2⟩,
      hs.2 p hp⟩
  have hsum2 : ∑ n ∈ A, (n : ℝ) ^ (-σ) =
      ∑ T ∈ A.image Nat.primeFactors, ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Nat.prod_primeFactors_of_squarefree
      (D.squarefree_sNum_of_mobS_ne_zero (Finset.mem_filter.mp hn).2).1]
  have hsum3 : ∑ T ∈ A.image Nat.primeFactors, ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ) ≤
      ∑ T ∈ P.powerset, ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hsum4 : ∑ T ∈ P.powerset, ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ) =
      ∏ p ∈ P, (1 + (p : ℝ) ^ (-σ)) := by
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  have hsum5 : ∏ p ∈ P, (1 + (p : ℝ) ^ (-σ)) ≤ Real.exp (∑ p ∈ P, (p : ℝ) ^ (-σ)) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => by positivity)
      fun p _ => by linarith [Real.add_one_le_exp ((p : ℝ) ^ (-σ))]
  have hsum6 : ∑ p ∈ P, (p : ℝ) ^ (-σ) ≤ ∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-σ)) n := by
    have hsumm := D.summable_indicator_rpow hα0 hα hσ
    calc ∑ p ∈ P, (p : ℝ) ^ (-σ) = ∑ p ∈ P, D.S.indicator (fun n => (n : ℝ) ^ (-σ)) p := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Set.indicator_of_mem (Finset.mem_filter.mp hp).2]
      _ ≤ _ := hsumm.sum_le_tsum _ fun n _ => by
          rw [Set.indicator_apply]; split_ifs <;> positivity
  rw [hsum1, hsum2]
  calc _ ≤ _ := hsum3
    _ = _ := hsum4
    _ ≤ _ := hsum5
    _ ≤ _ := Real.exp_le_exp.mpr hsum6

/-- `Σ_{n ≤ y} |μ_S(n)| ≤ y^σ exp(Σ_{p ∈ S} p^{−σ})` for `σ > α`, `y ≥ 1`. -/
theorem sum_norm_mobS_le (hα0 : 0 < α) (hα : α < 1) {σ : ℝ} (hσ : α < σ) {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖D.mobS n‖ ≤
      y ^ σ * Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-σ)) n) := by
  have hσ0 : 0 < σ := by linarith
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖D.mobS n‖ ≤
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, y ^ σ * (‖D.mobS n‖ * (n : ℝ) ^ (-σ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hn1, hny⟩ := Finset.mem_Icc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hny' : (n : ℝ) ≤ y := (Nat.le_floor_iff (by linarith)).mp hny
        have : 1 ≤ y ^ σ * (n : ℝ) ^ (-σ) := by
          rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, one_le_div (by positivity)]
          exact Real.rpow_le_rpow hn0.le hny' hσ0.le
        nlinarith [norm_nonneg (D.mobS n)]
    _ = y ^ σ * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖D.mobS n‖ * (n : ℝ) ^ (-σ) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (D.sum_norm_mobS_mul_rpow_le hα0 hα hσ _) (by positivity)

/-- `Σ |μ_S(n)|/n` converges. -/
theorem summable_norm_mobS_div (hα0 : 0 < α) (hα : α < 1) :
    Summable fun n : ℕ => ‖D.mobS n‖ / n := by
  have h := fun N => D.sum_norm_mobS_mul_rpow_le hα0 hα (σ := 1) hα N
  refine summable_of_sum_range_le (c := Real.exp (∑' n : ℕ,
    D.S.indicator (fun n => (n : ℝ) ^ (-(1 : ℝ))) n)) (fun n => by positivity) fun N => ?_
  have hf : ∀ n : ℕ, ‖D.mobS n‖ / n = ‖D.mobS n‖ * (n : ℝ) ^ (-(1 : ℝ)) := fun n => by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  simp_rw [hf]
  refine le_trans ?_ (h N)
  rw [Finset.range_eq_Ico]
  calc ∑ i ∈ Finset.Ico 0 N, ‖D.mobS i‖ * (i : ℝ) ^ (-(1 : ℝ))
      ≤ ∑ i ∈ Finset.Ico 0 (N + 1), ‖D.mobS i‖ * (i : ℝ) ^ (-(1 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
          fun _ _ _ => by positivity
    _ = ‖D.mobS 0‖ * ((0 : ℕ) : ℝ) ^ (-(1 : ℝ)) +
          ∑ i ∈ Finset.Ico 1 (N + 1), ‖D.mobS i‖ * (i : ℝ) ^ (-(1 : ℝ)) :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) _
    _ = ∑ i ∈ Finset.Icc 1 N, ‖D.mobS i‖ * (i : ℝ) ^ (-(1 : ℝ)) := by
        rw [D.mobS_zero, norm_zero, zero_mul, zero_add]
        rfl

end DeletionData

end RHTower.BeurlingDeletion
