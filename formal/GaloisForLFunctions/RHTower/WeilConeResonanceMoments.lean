import GaloisForLFunctions.RHTower.ZetaLineResonatorLargeValues
import GaloisForLFunctions.RHTower.WeilConeZetaPoleProducerObstruction
import GaloisForLFunctions.RHTower.ArgumentVariation

/-!
# Twisted first moments of the Dirichlet series of a Weil-positive system

Let `λ` be full-cone Weil-positive with Herglotz continuation `Φ`, and write
`D(s) = G(s) + 1/(s − 1) − Φ(s)` with `G` the archimedean datum. On `Re s > 1`, `D` is the
Dirichlet series `Σ_{n≥2} λ(n) n^{−s}` (`lamSeriesCont_eq_LSeries`). It continues analytically to
`Re s > ½`, `s ≠ 1`, with `Re D ≤ Re(G + 1/(s − 1))` (`re_lamSeriesCont_le`).

* **Growth** (`exists_norm_lamSeriesCont_le`). On `½ + δ ≤ Re s ≤ 5/4`, `|Im s| ≥ 2`:
  `|D(s)| ≤ C (1 + log(|Im s| + 4))`. This is Borel–Carathéodory on discs centred at `5/4 + iY`,
  from `Re D ≤ K log(|Im s| + 3) + 1` (`exists_log_bound_zetaArchimedeanDatum`) and
  `|D(5/4 + iY)| ≤ Σ |λ(n)| n^{−5/4}`.
* **Twisted moments** (`norm_integral_lamSeriesCont_sub_le`). For `m, d ≥ 1`, `T ≥ 2` and
  `½ < σ₀ ≤ 3/4`:
  `∫_T^{2T} D(σ₀ + it)(m/d)^{it} dt = [d ∣ m] λ(m/d)(m/d)^{−σ₀} T + O((md)⁴ (1 + log(T + 2)))`.
  On `Re s = 5/4` the series converges absolutely. There only `dn = m` survives, since
  `|log m − log(dn)|^{−1} ≤ 4m²`. The rectangle `[σ₀, 5/4] × [T, 2T]` moves the line.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation

namespace RHTower.WeilResonance

local notation "eχ" => _root_.GaloisForLFunctions.expChar

variable {lam : ℕ → ℝ}

/-- The continuation `D = G + 1/(s − 1) − Φ` of `Σ_{n≥2} λ(n) n^{−s}`. -/
def lamSeriesCont (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  zetaArchimedeanDatum s + 1 / (s - 1) - weilContinuation hW s

theorem lamSeriesCont_eq_LSeries (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    lamSeriesCont hW s = LSeries (lamC lam) s := by
  unfold lamSeriesCont
  rw [weilContinuation_eq hW hs, weilFunction]
  unfold zetaArchimedeanDatum
  ring

theorem differentiableAt_lamSeriesCont (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (lamSeriesCont hW) s := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΦ : DifferentiableAt ℂ (weilContinuation hW) s :=
    (differentiableOn_weilContinuation hW).differentiableAt (hU.mem_nhds hs)
  have hG := differentiableAt_zetaArchimedeanDatum (s := s) (by linarith)
  have hinv : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) s :=
    (differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)
  exact (hG.add hinv).sub hΦ

theorem re_lamSeriesCont_le (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 / 2 < s.re) :
    (lamSeriesCont hW s).re ≤ (zetaArchimedeanDatum s + 1 / (s - 1)).re := by
  unfold lamSeriesCont
  rw [Complex.sub_re]
  linarith [re_weilContinuation_nonneg hW hs]

theorem exists_re_lamSeriesCont_le (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      (lamSeriesCont hW s).re ≤ K * Real.log (|s.im| + 3) + 1 := by
  obtain ⟨K, hK0, hK⟩ := exists_log_bound_zetaArchimedeanDatum
  refine ⟨K, hK0, fun s hs1 hs2 him => ?_⟩
  have h1 := re_lamSeriesCont_le hW hs1
  have h2 : (zetaArchimedeanDatum s + 1 / (s - 1)).re ≤
      ‖zetaArchimedeanDatum s‖ + ‖1 / (s - 1)‖ :=
    (Complex.re_le_norm _).trans (norm_add_le _ _)
  have h3 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    exact div_le_one_of_le₀ this (norm_nonneg _)
  linarith [hK s hs1 hs2]

/-- `Σ |λ(n)| n^{−σ}` for `σ > 1`. -/
def absMass (lam : ℕ → ℝ) (σ : ℝ) : ℝ := ∑' n, ‖LSeries.term (lamC lam) σ n‖

theorem summable_norm_term_lamC (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n => ‖LSeries.term (lamC lam) σ n‖ :=
  (summable_term_lamC hW (s := σ) (by simpa using hσ)).norm

theorem absMass_nonneg (lam : ℕ → ℝ) (σ : ℝ) : 0 ≤ absMass lam σ :=
  tsum_nonneg fun _ => norm_nonneg _

theorem norm_lamSeriesCont_le_absMass (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    ‖lamSeriesCont hW s‖ ≤ absMass lam s.re := by
  rw [lamSeriesCont_eq_LSeries hW hs]
  have hsum := summable_norm_term_lamC hW hs
  have hle : ∀ n, ‖LSeries.term (lamC lam) s n‖ = ‖LSeries.term (lamC lam) s.re n‖ := fun n => by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact hsum.congr fun n => (hle n).symm
  · exact tsum_congr hle

/-- **Growth on the strip** `½ + δ ≤ Re s ≤ 5/4`, `|Im s| ≥ 2`. -/
theorem exists_norm_lamSeriesCont_le (hW : WeilPositiveFull lam) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 5 / 4 → 2 ≤ |s.im| →
      ‖lamSeriesCont hW s‖ ≤ C * (1 + Real.log (|s.im| + 4)) := by
  obtain ⟨K, hK0, hK⟩ := exists_re_lamSeriesCont_le hW
  set L := absMass lam (5 / 4) with hL
  have hL0 : 0 ≤ L := absMass_nonneg _ _
  refine ⟨L + 4 / δ * (K + 2 + 2 * L), by positivity, fun s hs1 hs2 him => ?_⟩
  set Y := s.im with hY
  set c : ℂ := (5 / 4 : ℂ) + (Y : ℂ) * I with hc
  have hcre : c.re = 5 / 4 := by simp [hc]
  have hcim : c.im = Y := by simp [hc]
  set R : ℝ := 3 / 4 - δ / 2 with hR
  have hR0 : 0 < R := by rw [hR]; linarith
  have hzc : ‖s - c‖ ≤ 3 / 4 - δ := by
    have e : s - c = ((s.re - 5 / 4 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc, hY]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hzball : s ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  -- the ball avoids `s = 1` and lies in `½ < Re ≤ 2`, `|Im| ≥ 1`
  have hball : ∀ w ∈ Metric.ball c R, 1 / 2 < w.re ∧ w.re ≤ 2 ∧ 1 ≤ |w.im| ∧
      |w.im| + 3 ≤ |Y| + 4 := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre := Complex.abs_re_le_norm (w - c)
    have him' := Complex.abs_im_le_norm (w - c)
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him'
    have hre' := abs_lt.mp (lt_of_le_of_lt hre hw)
    have him'' := abs_lt.mp (lt_of_le_of_lt him' hw)
    have h1 : |w.im - Y| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · have := abs_sub_abs_le_abs_sub Y w.im
      rw [abs_sub_comm] at this
      linarith
    · have := abs_sub_abs_le_abs_sub w.im Y
      linarith
  have hdiff : DifferentiableOn ℂ (lamSeriesCont hW) (Metric.ball c R) := fun w hw => by
    obtain ⟨h1, -, h3, -⟩ := hball w hw
    have hw1 : w ≠ 1 := by
      intro h; rw [h, Complex.one_im, abs_zero] at h3; linarith
    exact (differentiableAt_lamSeriesCont hW h1 hw1).differentiableWithinAt
  set A : ℝ := K * Real.log (|Y| + 4) + 2 + L with hA
  have hlogY : 0 ≤ Real.log (|Y| + 4) := Real.log_nonneg (by linarith [abs_nonneg Y])
  have hRe : ∀ w ∈ Metric.ball c R, (lamSeriesCont hW w).re ≤ A := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hball w hw
    have := hK w h1 h2 h3
    have hlog : Real.log (|w.im| + 3) ≤ Real.log (|Y| + 4) :=
      Real.log_le_log (by positivity) h4
    nlinarith
  have hcnorm : ‖lamSeriesCont hW c‖ ≤ L := by
    have := norm_lamSeriesCont_le_absMass hW (s := c) (by rw [hcre]; norm_num)
    rwa [hcre] at this
  have hRec : (lamSeriesCont hW c).re < A := by
    have := (Complex.re_le_norm _).trans hcnorm
    rw [hA]; linarith [mul_nonneg hK0 hlogY]
  have hBC := borel_caratheodory hdiff hRe hRec hzball
  have hgap : R - ‖s - c‖ ≥ δ / 2 := by rw [hR]; linarith
  have hfrac : 2 * ‖s - c‖ / (R - ‖s - c‖) ≤ 4 / δ := by
    rw [div_le_div_iff₀ (by linarith) hδ]
    nlinarith [norm_nonneg (s - c)]
  have hAre : A - (lamSeriesCont hW c).re ≤ K * Real.log (|Y| + 4) + 2 + 2 * L := by
    have := neg_le_abs (lamSeriesCont hW c).re
    have h2 := (Complex.abs_re_le_norm (lamSeriesCont hW c)).trans hcnorm
    rw [hA]; linarith
  have hAre0 : 0 ≤ A - (lamSeriesCont hW c).re := by linarith
  calc ‖lamSeriesCont hW s‖ ≤ ‖lamSeriesCont hW c‖ + ‖lamSeriesCont hW s - lamSeriesCont hW c‖ := by
        have := norm_sub_norm_le (lamSeriesCont hW s) (lamSeriesCont hW c); linarith
    _ ≤ L + 4 / δ * (K * Real.log (|Y| + 4) + 2 + 2 * L) := by
        refine add_le_add hcnorm (hBC.trans ?_)
        exact mul_le_mul hfrac hAre hAre0 (by positivity)
    _ ≤ (L + 4 / δ * (K + 2 + 2 * L)) * (1 + Real.log (|Y| + 4)) := by
        have h4δ : 0 ≤ 4 / δ := by positivity
        have h1 : K * Real.log (|Y| + 4) + 2 + 2 * L ≤
            (K + 2 + 2 * L) * (1 + Real.log (|Y| + 4)) := by
          nlinarith [mul_nonneg hL0 hlogY]
        have h2 := mul_le_mul_of_nonneg_left h1 h4δ
        nlinarith [mul_nonneg hL0 hlogY]

/-! ## The line `Re s = 5/4` -/

theorem inv_abs_log_sub_le {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hmk : m ≠ k) :
    1 / |Real.log m - Real.log k| ≤ 4 * (m : ℝ) ^ 2 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < |Real.log m - Real.log k| := by
    have := ZetaResonator.inv_mul_le_abs_log_sub hm hk hmk
    have h0 : (0 : ℝ) < 1 / ((m : ℝ) * k) := by positivity
    linarith
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hm2 : (1 : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
  rw [div_le_iff₀ hpos]
  by_cases h1 : 2 * (m : ℝ) ≤ k
  · have : Real.log 2 ≤ Real.log k - Real.log m := by
      rw [← Real.log_div (by positivity) (by positivity)]
      exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ (by positivity)]; linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    nlinarith
  by_cases h2 : 2 * (k : ℝ) ≤ m
  · have : Real.log 2 ≤ Real.log m - Real.log k := by
      rw [← Real.log_div (by positivity) (by positivity)]
      exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ (by positivity)]; linarith)
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  push Not at h1 h2
  have hsep := ZetaResonator.inv_mul_le_abs_log_sub hm hk hmk
  rw [div_le_iff₀ (by positivity)] at hsep
  nlinarith

/-- The real coefficient `λ(n)` for `n ≥ 2`, and `0` below. -/
def lamR (lam : ℕ → ℝ) (n : ℕ) : ℝ := if 2 ≤ n then lam n else 0

theorem lamC_eq_lamR (lam : ℕ → ℝ) (n : ℕ) : lamC lam n = (lamR lam n : ℂ) := by
  simp [lamC, lamR]

theorem term_lamC_five_four (lam : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    LSeries.term (lamC lam) ((5 / 4 : ℂ) + (t : ℂ) * I) n =
      ((lamR lam n * (n : ℝ) ^ (-(5 / 4 : ℝ)) : ℝ) : ℂ) * eχ (-Real.log n) t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero (by omega), lamC_eq_lamR]
  unfold _root_.GaloisForLFunctions.expChar
  rw [show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by norm_cast, Complex.cpow_def_of_ne_zero
    (by exact_mod_cast hn0.ne'), ← Complex.ofReal_log hn0.le,
    Real.rpow_def_of_pos hn0]
  push_cast
  rw [div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem norm_term_lamC_eq (lam : ℕ → ℝ) (n : ℕ) (σ : ℝ) :
    ‖LSeries.term (lamC lam) σ n‖ = |lamR lam n| * (n : ℝ) ^ (-σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lamR]
  rw [LSeries.norm_term_eq, if_neg hn.ne', lamC_eq_lamR, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- **The twisted moment on `Re s = 5/4`.** -/
theorem norm_integral_lamSeriesCont_five_four_sub_le (hW : WeilPositiveFull lam) {m d : ℕ}
    (hm : 1 ≤ m) (hd : 1 ≤ d) (T : ℝ) :
    ‖(∫ t in T..(2 * T), lamSeriesCont hW ((5 / 4 : ℂ) + (t : ℂ) * I) *
        eχ (Real.log m - Real.log d) t) -
      (if d ∣ m then ((lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) * T : ℝ) : ℂ)
        else 0)‖ ≤ 8 * (m : ℝ) ^ 2 * absMass lam (5 / 4) := by
  classical
  set a : ℕ → ℝ := fun n => |lamR lam n| * (n : ℝ) ^ (-(5 / 4 : ℝ)) with ha
  have hsa : Summable a := by
    have := summable_norm_term_lamC hW (σ := 5 / 4) (by norm_num)
    refine this.congr fun n => ?_
    rw [norm_term_lamC_eq]
  have hLa : absMass lam (5 / 4) = ∑' n, a n := by
    unfold absMass; exact tsum_congr fun n => by rw [norm_term_lamC_eq]
  -- the integrand as a series
  set g : ℕ → ℝ → ℂ := fun n t => ((lamR lam n * (n : ℝ) ^ (-(5 / 4 : ℝ)) : ℝ) : ℂ) *
    eχ (Real.log m - Real.log (d * n : ℕ)) t with hg
  have hcont : ∀ ξ, Continuous (eχ ξ) := fun ξ => by
    unfold _root_.GaloisForLFunctions.expChar; fun_prop
  have hpt : ∀ t : ℝ, HasSum (fun n => g n t)
      (lamSeriesCont hW ((5 / 4 : ℂ) + (t : ℂ) * I) * eχ (Real.log m - Real.log d) t) := by
    intro t
    have hre : 1 < ((5 / 4 : ℂ) + (t : ℂ) * I).re := by norm_num
    have hs := (summable_term_lamC hW hre).hasSum
    rw [← LSeries, ← lamSeriesCont_eq_LSeries hW hre] at hs
    have e1 : (fun n => g n t) = fun n => LSeries.term (lamC lam) ((5 / 4 : ℂ) + (t : ℂ) * I) n *
        eχ (Real.log m - Real.log d) t := by
      funext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hg, lamR]
      rw [term_lamC_five_four lam hn, hg]
      simp only
      rw [mul_assoc, _root_.GaloisForLFunctions.expChar_add]
      congr 2
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Nat.cast_mul, Real.log_mul hdR.ne' hnR.ne']; ring
    rw [e1]
    exact hs.mul_right _
  have hbound : ∀ n t, ‖g n t‖ ≤ a n := fun n t => by
    rw [hg]; simp only
    rw [norm_mul, _root_.GaloisForLFunctions.norm_expChar, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hHas : HasSum (fun n => ∫ t in T..(2 * T), g n t)
      (∫ t in T..(2 * T), lamSeriesCont hW ((5 / 4 : ℂ) + (t : ℂ) * I) *
        eχ (Real.log m - Real.log d) t) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => a n)
      (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · exact ((continuous_const.mul (hcont _)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall fun t _ => hbound n t
    · exact Filter.Eventually.of_forall fun t _ => hsa
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ => hpt t
  -- each term: the diagonal `dn = m` and the rest
  set main : ℕ → ℂ := fun n => if d * n = m then
    ((lamR lam n * (n : ℝ) ^ (-(5 / 4 : ℝ)) * T : ℝ) : ℂ) else 0 with hmain
  have hterm : ∀ n, ‖(∫ t in T..(2 * T), g n t) - main n‖ ≤ 8 * (m : ℝ) ^ 2 * a n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hg, hmain, lamR, ha]
    have hdn : 1 ≤ d * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hint : (∫ t in T..(2 * T), g n t) = ((lamR lam n * (n : ℝ) ^ (-(5 / 4 : ℝ)) : ℝ) : ℂ) *
        ∫ t in T..(2 * T), eχ (Real.log m - Real.log (d * n : ℕ)) t := by
      rw [hg]; exact intervalIntegral.integral_const_mul _ _
    rw [hint, hmain]
    simp only
    split_ifs with h
    · have h0 : ∀ t, eχ (Real.log m - Real.log (d * n : ℕ)) t = 1 := fun t => by
        rw [h]; unfold _root_.GaloisForLFunctions.expChar; simp
      simp only [h0, intervalIntegral.integral_const, Complex.real_smul, mul_one]
      rw [show ((lamR lam n * (n : ℝ) ^ (-(5 / 4 : ℝ)) : ℝ) : ℂ) * ((2 * T - T : ℝ) : ℂ) -
          ((lamR lam n * (n : ℝ) ^ (-(5 / 4 : ℝ)) * T : ℝ) : ℂ) = 0 by push_cast; ring,
        norm_zero]
      have : 0 ≤ a n := by rw [ha]; positivity
      positivity
    · rw [sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      have hne : m ≠ d * n := fun h' => h h'.symm
      have hξ : Real.log m - Real.log (d * n : ℕ) ≠ 0 := by
        intro h0
        have := inv_abs_log_sub_le hm hdn hne
        rw [h0, abs_zero, div_zero] at this
        exact absurd (ZetaResonator.inv_mul_le_abs_log_sub hm hdn hne) (by
          rw [h0, abs_zero, not_le]; positivity)
      have hI := ZetaResonator.norm_integral_expChar_le hξ T (2 * T)
      have hinv := inv_abs_log_sub_le hm hdn hne
      have hI' : ‖∫ t in T..(2 * T), eχ (Real.log m - Real.log (d * n : ℕ)) t‖ ≤
          8 * (m : ℝ) ^ 2 := by
        refine hI.trans ?_
        rw [div_eq_mul_one_div 2]; linarith
      calc |lamR lam n| * (n : ℝ) ^ (-(5 / 4 : ℝ)) *
            ‖∫ t in T..(2 * T), eχ (Real.log m - Real.log (d * n : ℕ)) t‖
          ≤ |lamR lam n| * (n : ℝ) ^ (-(5 / 4 : ℝ)) * (8 * (m : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hI' (by positivity)
        _ = 8 * (m : ℝ) ^ 2 * a n := by rw [ha]; ring
  -- sum of the main terms
  have hmainsum : HasSum main (if d ∣ m then
      ((lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) * T : ℝ) : ℂ) else 0) := by
    split_ifs with h
    · have hmd : d * (m / d) = m := Nat.mul_div_cancel' h
      have := hasSum_ite_eq (m / d) (((lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) *
        T : ℝ) : ℂ))
      convert this using 1
      funext n
      rw [hmain]; simp only
      by_cases hn : n = m / d
      · subst hn; simp [hmd]
      · have : d * n ≠ m := by
          intro h'; apply hn
          rw [← h', Nat.mul_div_cancel_left n (by omega)]
        simp [this, hn]
    · convert hasSum_zero using 1
      funext n
      rw [hmain]; simp only
      have : d * n ≠ m := fun h' => h (h' ▸ Dvd.intro n rfl)
      simp [this]
  have hdiff := hHas.sub hmainsum
  rw [← hdiff.tsum_eq]
  have hs8 : Summable fun n => 8 * (m : ℝ) ^ 2 * a n := hsa.mul_left _
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hs8
  · rw [hLa, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hs8)
      hs8

/-! ## Moving the line -/

theorem exp_mul_log_ratio_le {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 5 / 4) : Real.exp (x * (Real.log m - Real.log d)) ≤ ((m : ℝ) * d) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd1
  have h1 : x * (Real.log m - Real.log d) ≤ 2 * Real.log ((m : ℝ) * d) := by
    rw [Real.log_mul (by positivity) (by positivity)]; nlinarith
  calc Real.exp (x * (Real.log m - Real.log d)) ≤ Real.exp (2 * Real.log ((m : ℝ) * d)) :=
        Real.exp_le_exp.mpr h1
    _ = ((m : ℝ) * d) ^ 2 := by
        rw [show 2 * Real.log ((m : ℝ) * d) = Real.log (((m : ℝ) * d) ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem exp_neg_mul_log_ratio_le {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 5 / 4) : Real.exp (-(x * (Real.log m - Real.log d))) ≤ ((m : ℝ) * d) ^ 2 := by
  have := exp_mul_log_ratio_le hd hm hx0 hx
  rw [mul_comm (d : ℝ)] at this
  calc Real.exp (-(x * (Real.log m - Real.log d)))
      = Real.exp (x * (Real.log d - Real.log m)) := by ring_nf
    _ ≤ _ := this

/-- The horizontal edge bound: `|D(x + iY) e^{(x+iY)ξ}| ≤ C_g (1 + log(2T + 4)) (md)²`. -/
theorem norm_horizontal_le (hW : WeilPositiveFull lam) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ s : ℂ, 1 / 2 + (σ₀ - 1 / 2) ≤ s.re → s.re ≤ 5 / 4 → 2 ≤ |s.im| →
      ‖lamSeriesCont hW s‖ ≤ Cg * (1 + Real.log (|s.im| + 4)))
    {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) {ξ : ℝ} (hξ : ξ = Real.log m - Real.log d)
    {T Y : ℝ} (hT : 2 ≤ T) (hY1 : T ≤ Y) (hY2 : Y ≤ 2 * T)
    {x : ℝ} (hx1 : σ₀ ≤ x) (hx2 : x ≤ 5 / 4) :
    ‖lamSeriesCont hW ((x : ℂ) + (Y : ℂ) * I) *
        Complex.exp (((x : ℂ) + (Y : ℂ) * I) * (ξ : ℂ))‖ ≤
      Cg * (1 + Real.log (2 * T + 4)) * ((m : ℝ) * d) ^ 2 := by
  have hre : ((x : ℂ) + (Y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (Y : ℂ) * I).im = Y := by simp
  have hYabs : |((x : ℂ) + (Y : ℂ) * I).im| = Y := by rw [him]; exact abs_of_nonneg (by linarith)
  have hD := hCg ((x : ℂ) + (Y : ℂ) * I) (by rw [hre]; linarith) (by rw [hre]; exact hx2)
    (by rw [hYabs]; linarith)
  rw [hYabs] at hD
  have hlog : Real.log (Y + 4) ≤ Real.log (2 * T + 4) := Real.log_le_log (by linarith) (by linarith)
  have hD' : ‖lamSeriesCont hW ((x : ℂ) + (Y : ℂ) * I)‖ ≤ Cg * (1 + Real.log (2 * T + 4)) :=
    hD.trans (mul_le_mul_of_nonneg_left (by linarith) hCg0)
  have hE : ‖Complex.exp (((x : ℂ) + (Y : ℂ) * I) * (ξ : ℂ))‖ ≤ ((m : ℝ) * d) ^ 2 := by
    rw [Complex.norm_exp]
    have : (((x : ℂ) + (Y : ℂ) * I) * (ξ : ℂ)).re = x * ξ := by simp
    rw [this, hξ]
    exact exp_mul_log_ratio_le hm hd (by linarith) hx2
  have hlogT : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
  rw [norm_mul]
  exact mul_le_mul hD' hE (norm_nonneg _) (mul_nonneg hCg0 (by linarith))

/-- **Twisted first moments of `D` on `Re s = σ₀`**, `½ < σ₀ ≤ 3/4`. -/
theorem exists_norm_integral_lamSeriesCont_sub_le (hW : WeilPositiveFull lam) {σ₀ : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ₀' : σ₀ ≤ 3 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m d : ℕ}, 1 ≤ m → 1 ≤ d → ∀ {T : ℝ}, 2 ≤ T →
      ‖(∫ t in T..(2 * T), lamSeriesCont hW ((σ₀ : ℂ) + (t : ℂ) * I) *
          eχ (Real.log m - Real.log d) t) -
        (if d ∣ m then ((lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-σ₀) * T : ℝ) : ℂ) else 0)‖ ≤
        C * ((m : ℝ) * d) ^ 4 * (1 + Real.log (2 * T + 4)) := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_lamSeriesCont_le hW (δ := σ₀ - 1 / 2) (by linarith)
    (by linarith)
  obtain ⟨L, hL⟩ : ∃ L, L = absMass lam (5 / 4) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hL ▸ absMass_nonneg _ _
  refine ⟨8 * L + 3 * Cg, by positivity, fun {m d} hm hd {T} hT => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmd1 : (1 : ℝ) ≤ (m : ℝ) * d := by nlinarith
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = Real.log m - Real.log d := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun s => lamSeriesCont hW s * Complex.exp (s * (ξ : ℂ)) :=
    ⟨_, rfl⟩
  have hdiff : DifferentiableOn ℂ f (Set.uIcc ((σ₀ : ℂ) + (T : ℂ) * I).re
      (((5 / 4 : ℝ) : ℂ) + ((2 * T : ℝ) : ℂ) * I).re ×ℂ
      Set.uIcc ((σ₀ : ℂ) + (T : ℂ) * I).im (((5 / 4 : ℝ) : ℂ) + ((2 * T : ℝ) : ℂ) * I).im) := by
    intro s hs
    have hre := (Complex.mem_reProdIm.mp hs).1
    have him := (Complex.mem_reProdIm.mp hs).2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im, Complex.mul_im,
      zero_add] at hre him
    rw [Set.uIcc_of_le (by linarith)] at hre
    rw [Set.uIcc_of_le (by linarith)] at him
    have hs1 : s ≠ 1 := by
      intro h; rw [h, Complex.one_im] at him; linarith [him.1]
    rw [hf]
    exact ((differentiableAt_lamSeriesCont hW (by linarith [hre.1]) hs1).mul
      (Complex.differentiable_exp.differentiableAt.comp s
        (differentiableAt_id.mul (differentiableAt_const _)))).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f _ _ hdiff
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im, Complex.mul_im,
    zero_add] at hrect
  -- the vertical lines
  have hline : ∀ x : ℝ, (∫ y in T..(2 * T), f ((x : ℂ) + (y : ℂ) * I)) =
      (Real.exp (x * ξ) : ℂ) *
        ∫ y in T..(2 * T), lamSeriesCont hW ((x : ℂ) + (y : ℂ) * I) * eχ ξ y := by
    intro x
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hf]
    simp only
    unfold _root_.GaloisForLFunctions.expChar
    rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [hline σ₀, hline (5 / 4)] at hrect
  -- the horizontal edges
  have hhor : ∀ Y : ℝ, T ≤ Y → Y ≤ 2 * T →
      ‖∫ x in σ₀..(5 / 4), f ((x : ℂ) + (Y : ℂ) * I)‖ ≤
        Cg * (1 + Real.log (2 * T + 4)) * ((m : ℝ) * d) ^ 2 := by
    intro Y hY1 hY2
    have hb : ∀ x ∈ Set.uIoc σ₀ (5 / 4), ‖f ((x : ℂ) + (Y : ℂ) * I)‖ ≤
        Cg * (1 + Real.log (2 * T + 4)) * ((m : ℝ) * d) ^ 2 := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      rw [hf]
      exact norm_horizontal_le hW hσ₀ hCg0 hCg hm hd hξ hT hY1 hY2 hx.1.le hx.2
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    rw [abs_of_nonneg (by linarith)]
    have hlogT : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
    have h0 : 0 ≤ Cg * (1 + Real.log (2 * T + 4)) * ((m : ℝ) * d) ^ 2 :=
      mul_nonneg (mul_nonneg hCg0 (by linarith)) (by positivity)
    nlinarith
  obtain ⟨H1, hH1d⟩ : ∃ H, H = ∫ x in σ₀..(5 / 4), f ((x : ℂ) + (T : ℂ) * I) := ⟨_, rfl⟩
  obtain ⟨H2, hH2d⟩ : ∃ H, H = ∫ x in σ₀..(5 / 4), f ((x : ℂ) + ((2 * T : ℝ) : ℂ) * I) :=
    ⟨_, rfl⟩
  have hH1 : ‖H1‖ ≤ Cg * (1 + Real.log (2 * T + 4)) * ((m : ℝ) * d) ^ 2 := by
    rw [hH1d]; exact hhor T le_rfl (by linarith)
  have hH2 : ‖H2‖ ≤ Cg * (1 + Real.log (2 * T + 4)) * ((m : ℝ) * d) ^ 2 := by
    rw [hH2d]; exact hhor (2 * T) (by linarith) le_rfl
  obtain ⟨Iσ, hIσ⟩ : ∃ J, J = ∫ y in T..(2 * T),
      lamSeriesCont hW ((σ₀ : ℂ) + (y : ℂ) * I) * eχ ξ y := ⟨_, rfl⟩
  obtain ⟨I54, hI54⟩ : ∃ J, J = ∫ y in T..(2 * T),
      lamSeriesCont hW (((5 / 4 : ℝ) : ℂ) + (y : ℂ) * I) * eχ ξ y := ⟨_, rfl⟩
  have hsolve : (Real.exp (σ₀ * ξ) : ℂ) * Iσ =
      (Real.exp (5 / 4 * ξ) : ℂ) * I54 - I * (H1 - H2) := by
    rw [hIσ, hI54, hH1d, hH2d]
    simp only [smul_eq_mul] at hrect
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination I * hrect + ((Real.exp (σ₀ * ξ) : ℂ) *
      (∫ y in T..(2 * T), lamSeriesCont hW ((σ₀ : ℂ) + (y : ℂ) * I) * eχ ξ y) -
      (Real.exp (5 / 4 * ξ) : ℂ) *
        (∫ y in T..(2 * T), lamSeriesCont hW (((5 / 4 : ℝ) : ℂ) + (y : ℂ) * I) * eχ ξ y)) * hI
  have hinv : (Real.exp (-(σ₀ * ξ)) : ℂ) * (Real.exp (σ₀ * ξ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  have hcomb : (Real.exp (-(σ₀ * ξ)) : ℂ) * (Real.exp (5 / 4 * ξ) : ℂ) =
      (Real.exp ((5 / 4 - σ₀) * ξ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  have hIσ_eq : Iσ = (Real.exp ((5 / 4 - σ₀) * ξ) : ℂ) * I54 -
      (Real.exp (-(σ₀ * ξ)) : ℂ) * (I * (H1 - H2)) := by
    linear_combination (Real.exp (-(σ₀ * ξ)) : ℂ) * hsolve - Iσ * hinv + I54 * hcomb
  -- the `5/4` line
  have h54 := norm_integral_lamSeriesCont_five_four_sub_le hW hm hd T
  have e54 : ((5 / 4 : ℂ)) = ((5 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [e54, ← hξ, ← hI54] at h54
  obtain ⟨M54, hM54⟩ : ∃ M : ℂ, M = if d ∣ m then
      ((lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) * T : ℝ) : ℂ) else 0 := ⟨_, rfl⟩
  rw [← hM54, ← hL] at h54
  have hmain : (Real.exp ((5 / 4 - σ₀) * ξ) : ℂ) * M54 =
      if d ∣ m then ((lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-σ₀) * T : ℝ) : ℂ) else 0 := by
    rw [hM54]
    split_ifs with h
    · have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hq : ((m / d : ℕ) : ℝ) = (m : ℝ) / d := Nat.cast_div h (by positivity)
      have hq0 : (0 : ℝ) < ((m / d : ℕ) : ℝ) := by rw [hq]; positivity
      have hexpq : Real.exp ((5 / 4 - σ₀) * ξ) = ((m / d : ℕ) : ℝ) ^ (5 / 4 - σ₀) := by
        rw [hξ, ← Real.log_div (by positivity) (by positivity), ← hq,
          Real.rpow_def_of_pos hq0, mul_comm]
      rw [← Complex.ofReal_mul, hexpq]
      congr 1
      have hpow : ((m / d : ℕ) : ℝ) ^ (5 / 4 - σ₀) * ((m / d : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) =
          ((m / d : ℕ) : ℝ) ^ (-σ₀) := by
        rw [← Real.rpow_add hq0]; ring_nf
      calc ((m / d : ℕ) : ℝ) ^ (5 / 4 - σ₀) *
            (lamR lam (m / d) * ((m / d : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) * T)
          = lamR lam (m / d) * (((m / d : ℕ) : ℝ) ^ (5 / 4 - σ₀) *
              ((m / d : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) * T := by ring
        _ = _ := by rw [hpow]
    · simp
  have hE1 : Real.exp ((5 / 4 - σ₀) * ξ) ≤ ((m : ℝ) * d) ^ 2 := by
    rw [hξ]; exact exp_mul_log_ratio_le hm hd (by linarith) (by linarith)
  have hE2 : Real.exp (-(σ₀ * ξ)) ≤ ((m : ℝ) * d) ^ 2 := by
    rw [hξ]; exact exp_neg_mul_log_ratio_le hm hd (by linarith) (by linarith)
  have hlogT : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
  have hmd2 : ((m : ℝ) * d) ^ 2 ≤ ((m : ℝ) * d) ^ 4 := pow_le_pow_right₀ hmd1 (by norm_num)
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) * d) ^ 2 := by
    rw [mul_pow]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hd1)
  rw [← hξ, ← hIσ, ← hmain, hIσ_eq]
  have key : (Real.exp ((5 / 4 - σ₀) * ξ) : ℂ) * I54 - (Real.exp (-(σ₀ * ξ)) : ℂ) *
      (I * (H1 - H2)) - (Real.exp ((5 / 4 - σ₀) * ξ) : ℂ) * M54 =
      (Real.exp ((5 / 4 - σ₀) * ξ) : ℂ) * (I54 - M54) -
        (Real.exp (-(σ₀ * ξ)) : ℂ) * (I * (H1 - H2)) := by ring
  rw [key]
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = Cg * (1 + Real.log (2 * T + 4)) * ((m : ℝ) * d) ^ 2 := ⟨_, rfl⟩
  rw [← hG] at hH1 hH2
  have hG0 : 0 ≤ G := by rw [hG]; exact mul_nonneg (mul_nonneg hCg0 (by linarith)) (by positivity)
  have hA : ‖(Real.exp ((5 / 4 - σ₀) * ξ) : ℂ) * (I54 - M54)‖ ≤
      ((m : ℝ) * d) ^ 2 * (8 * (m : ℝ) ^ 2 * L) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hE1 h54 (norm_nonneg _) (by positivity)
  have hB : ‖(Real.exp (-(σ₀ * ξ)) : ℂ) * (I * (H1 - H2))‖ ≤ ((m : ℝ) * d) ^ 2 * (2 * G) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul hE2 ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ((add_le_add hA hB).trans ?_)
  rw [hG]
  have h4 : ((m : ℝ) * d) ^ 2 * (m : ℝ) ^ 2 ≤ ((m : ℝ) * d) ^ 4 := by
    have := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ ((m : ℝ) * d) ^ 2)
    nlinarith
  have hX : 0 ≤ ((m : ℝ) * d) ^ 4 := by positivity
  have h1L : 0 ≤ Real.log (2 * T + 4) * ((m : ℝ) * d) ^ 4 := mul_nonneg hlogT hX
  nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 8 * L),
    mul_nonneg hL0 h1L, mul_nonneg hCg0 h1L, mul_nonneg hCg0 hX]

end RHTower.WeilResonance
