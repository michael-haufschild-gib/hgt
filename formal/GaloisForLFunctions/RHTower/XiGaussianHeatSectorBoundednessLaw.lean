import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalLineReceiver

/-!
# Sectors of boundedness of the heat trace and conical zero-free regions

The complex-time heat trace `ν(τ) = Σ_q exp(-τ w_q)`, `w_q = z_q²`, is bounded on one vertical line
iff RH holds (`riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line`).  This module
records the angular version, which interpolates between the unconditional and the RH regime.

**Theorem** (`xiGaussianHeatTraceC_sector_bounded_iff`).  For `a > 0` and slope `T ≥ 0`, `ν` is
bounded on the sector `{a ≤ Re τ, |Im τ| ≤ T (Re τ - a)}` iff every squared spectral point satisfies
`T |Im w_q| ≤ Re w_q`.  In zero coordinates this reads
`2T |γ| |β - 1/2| ≤ γ² - (β - 1/2)²` (`xiGaussianHeatTraceC_sector_bounded_iff_xi_zeros`).  This is a
conical zero-free region: as `T` grows it forces the zeros up to height about `T` onto the line.

* Unconditionally `ν` is bounded on the sector of slope `6`, because every zero has `‖z‖² > 150`
  (`xiGaussianHeatTraceC_sector_bounded_six`).
* RH holds iff `ν` is bounded on every sector, equivalently iff the boundedness slope `T*` is infinite
  (`riemannHypothesis_iff_forall_xiGaussianHeatTraceC_sector_bounded`).

Mechanism.  `⇐` is termwise: for `τ - a` in the sector, `Re((τ - a) w) ≥ Re(τ - a)(Re w - T|Im w|) ≥ 0`.
`⇒`: along the boundary ray `a + r e^{iθ}`, `tan θ = T`, a copy violating the inequality (after line
conjugation, with `Im w > 0`) has `Re(e^{iθ} w) < 0`.  Only finitely many copies do, because
`Re w > ‖z‖²/2` and `|Im w| ≤ ‖z‖`.  The light-cone lemma then contradicts boundedness on the ray.
No Phragmén–Lindelöf step is needed, since the ray lies inside the sector.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- On a sector with vertex `a` the termwise exponent never exceeds the real-time one. -/
theorem norm_xiGaussianHeatTermC_le_of_sector {a T : ℝ} {τ : ℂ} (hre : a ≤ τ.re)
    (him : |τ.im| ≤ T * (τ.re - a)) {q : XiZeroCopy}
    (hq : T * |(xiSpectralPoint q ^ (2 : ℕ)).im| ≤ (xiSpectralPoint q ^ (2 : ℕ)).re) :
    ‖xiGaussianHeatTermC τ q‖ ≤ Real.exp (-(a * (xiSpectralPoint q ^ (2 : ℕ)).re)) := by
  rw [norm_xiGaussianHeatTermC]
  apply Real.exp_le_exp.2
  set A := (xiSpectralPoint q ^ (2 : ℕ)).re
  set B := (xiSpectralPoint q ^ (2 : ℕ)).im
  have hs : 0 ≤ τ.re - a := by linarith
  have hbB : τ.im * B ≤ (τ.re - a) * A := by
    calc τ.im * B ≤ |τ.im * B| := le_abs_self _
      _ = |τ.im| * |B| := abs_mul _ _
      _ ≤ T * (τ.re - a) * |B| := mul_le_mul_of_nonneg_right him (abs_nonneg _)
      _ = (τ.re - a) * (T * |B|) := by ring
      _ ≤ (τ.re - a) * A := mul_le_mul_of_nonneg_left hq hs
  nlinarith

/-- **Sector law.**  For `a > 0` and `T ≥ 0`, the heat trace is bounded on the sector of slope `T`
with vertex `a` iff every squared spectral point satisfies `T |Im w| ≤ Re w`. -/
theorem xiGaussianHeatTraceC_sector_bounded_iff {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∃ C : ℝ, ∀ τ : ℂ, a ≤ τ.re → |τ.im| ≤ T * (τ.re - a) → ‖xiGaussianHeatTraceC τ‖ ≤ C) ↔
      ∀ q : XiZeroCopy, T * |(xiSpectralPoint q ^ (2 : ℕ)).im| ≤ (xiSpectralPoint q ^ (2 : ℕ)).re := by
  have hsumm : Summable (fun q : XiZeroCopy => Real.exp (-(a * (xiSpectralPoint q ^ (2 : ℕ)).re))) := by
    have h := summable_norm_xiGaussianHeatTermC (τ := (a : ℂ)) (by simpa using ha)
    refine h.congr fun q => ?_
    rw [norm_xiGaussianHeatTermC]
    simp
  constructor
  · rintro ⟨C, hC⟩
    by_contra hbad
    push Not at hbad
    obtain ⟨q₀, hq₀⟩ := hbad
    -- a violating copy with `Im w > 0`
    obtain ⟨q₁, hq₁⟩ : ∃ q₁ : XiZeroCopy, 0 < (xiSpectralPoint q₁ ^ (2 : ℕ)).im ∧
        (xiSpectralPoint q₁ ^ (2 : ℕ)).re < T * (xiSpectralPoint q₁ ^ (2 : ℕ)).im := by
      have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q₀
      have hN : 0 < ‖xiSpectralPoint q₀‖ ^ (2 : ℕ) := by
        have := xiSpectralPoint_ne_zero q₀
        positivity
      have hA : 0 < (xiSpectralPoint q₀ ^ (2 : ℕ)).re := by linarith
      rcases lt_trichotomy 0 (xiSpectralPoint q₀ ^ (2 : ℕ)).im with hpos | hzero | hneg
      · exact ⟨q₀, hpos, by rwa [abs_of_pos hpos] at hq₀⟩
      · rw [← hzero, abs_zero, mul_zero] at hq₀; linarith
      · refine ⟨xiZeroCopyLineConjEquiv q₀, ?_, ?_⟩
        · rw [xiSpectralPoint_lineConj, ← map_pow, Complex.conj_im]; linarith
        · rw [xiSpectralPoint_lineConj, ← map_pow, Complex.conj_im, Complex.conj_re]
          rwa [abs_of_neg hneg] at hq₀
    obtain ⟨hB₁, hA₁⟩ := hq₁
    set θ : ℝ := Real.arctan T
    have hcos : 0 < Real.cos θ := Real.cos_arctan_pos T
    have hsinT : Real.sin θ = T * Real.cos θ := by
      rw [← Real.tan_arctan T, Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hcos.ne']
    have hsin0 : 0 ≤ Real.sin θ := by rw [hsinT]; positivity
    set e : ℂ := Complex.exp ((θ : ℂ) * I)
    have he_re : e.re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ
    have he_im : e.im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
    have hw_re : ∀ q : XiZeroCopy, (e * xiSpectralPoint q ^ (2 : ℕ)).re =
        Real.cos θ * ((xiSpectralPoint q ^ (2 : ℕ)).re - T * (xiSpectralPoint q ^ (2 : ℕ)).im) :=
      fun q => by rw [Complex.mul_re, he_re, he_im, hsinT]; ring
    have hray : ∀ r : ℝ, 0 ≤ r → ‖xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e)‖ ≤ C := by
      intro r hr
      apply hC
      · simp only [add_re, ofReal_re, re_ofReal_mul, he_re]
        nlinarith
      · simp only [add_im, add_re, ofReal_im, ofReal_re, im_ofReal_mul, re_ofReal_mul, he_im,
          he_re, zero_add, add_sub_cancel_left]
        rw [abs_of_nonneg (mul_nonneg hr hsin0), hsinT]
        nlinarith
    have hterm : ∀ (q : XiZeroCopy) (r : ℝ),
        Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
            Complex.exp (-(r : ℂ) * (e * xiSpectralPoint q ^ (2 : ℕ))) =
          xiGaussianHeatTermC ((a : ℂ) + (r : ℂ) * e) q := fun q r => by
      rw [xiGaussianHeatTermC, ← Complex.exp_add]
      congr 1
      ring
    have hτre : ∀ r : ℝ, 0 ≤ r → 0 < ((a : ℂ) + (r : ℂ) * e).re := fun r hr => by
      simp only [add_re, ofReal_re, re_ofReal_mul, he_re]
      nlinarith
    have hfin : {q : XiZeroCopy | (e * xiSpectralPoint q ^ (2 : ℕ)).re < 0}.Finite := by
      have hc : 0 < 1 / (4 * (T ^ 2 + 1)) := by positivity
      have hev := (xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero).eventually
        (gt_mem_nhds hc)
      refine (Filter.eventually_cofinite.1 hev).subset fun q hq => ?_
      simp only [mem_setOf_eq] at hq ⊢
      rw [hw_re] at hq
      have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
      have hBq := xiSpectralSq_im_sq_le_norm_sq q
      have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        have := xiSpectralPoint_ne_zero q
        positivity
      set A := (xiSpectralPoint q ^ (2 : ℕ)).re
      set B := (xiSpectralPoint q ^ (2 : ℕ)).im
      set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
      have hlt : A < T * B := by
        by_contra h
        push Not at h
        have := mul_nonneg hcos.le (sub_nonneg.2 h)
        linarith
      have hsq : (N / 2) ^ 2 < T ^ 2 * N := by
        have h1 : N / 2 < T * B := by linarith
        have h2 : 0 ≤ N / 2 := by positivity
        have h3 : (N / 2) ^ 2 < (T * B) ^ 2 := pow_lt_pow_left₀ h1 h2 two_ne_zero
        nlinarith [sq_nonneg T]
      have hN4 : N < 4 * T ^ 2 := by nlinarith
      rw [not_lt, le_div_iff₀ hN, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    obtain ⟨r, hr0, hr⟩ := GaloisForLFunctions.HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg
      (w := fun q : XiZeroCopy => e * xiSpectralPoint q ^ (2 : ℕ))
      (c := fun q : XiZeroCopy => Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)))
      (ε₀ := 0) le_rfl
      (fun i j hij => by
        have hne : e ≠ 0 := Complex.exp_ne_zero _
        have : xiSpectralPoint i ^ (2 : ℕ) = xiSpectralPoint j ^ (2 : ℕ) :=
          mul_left_cancel₀ hne hij
        simp only [this])
      (fun _ _ => Complex.exp_ne_zero _) hfin
      (m := fun q => Real.exp (-(a * (xiSpectralPoint q ^ (2 : ℕ)).re)))
      (fun q => (Real.exp_pos _).le) hsumm
      (fun q hq ε hε => by
        rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
        have hre1 : (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)).re =
            -(a * (xiSpectralPoint q ^ (2 : ℕ)).re) := by
          rw [neg_mul, neg_re, re_ofReal_mul]
        have hre2 : (-(ε : ℂ) * (e * xiSpectralPoint q ^ (2 : ℕ))).re =
            -(ε * (e * xiSpectralPoint q ^ (2 : ℕ)).re) := by
          rw [neg_mul, neg_re, re_ofReal_mul]
        rw [hre1, hre2]
        have hq' : 0 ≤ (e * xiSpectralPoint q ^ (2 : ℕ)).re := hq
        have : Real.exp (-(ε * (e * xiSpectralPoint q ^ (2 : ℕ)).re)) ≤ 1 := by
          rw [Real.exp_le_one_iff, neg_nonpos]; exact mul_nonneg hε hq'
        exact mul_le_of_le_one_right (Real.exp_pos _).le this)
      (fun ε hε => by
        simp only [hterm]
        exact summable_norm_xiGaussianHeatTermC (hτre ε hε))
      ⟨q₁, by
        show (e * xiSpectralPoint q₁ ^ (2 : ℕ)).re < 0
        rw [hw_re]
        exact mul_neg_of_pos_of_neg hcos (by linarith)⟩ C
    have hsum : ∑' q : XiZeroCopy, Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
        Complex.exp (-(r : ℂ) * (e * xiSpectralPoint q ^ (2 : ℕ))) =
          xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e) := by
      rw [xiGaussianHeatTraceC]
      exact tsum_congr fun q => hterm q r
    rw [hsum] at hr
    linarith [hray r hr0]
  · intro hall
    refine ⟨∑' q : XiZeroCopy, Real.exp (-(a * (xiSpectralPoint q ^ (2 : ℕ)).re)),
      fun τ hre him => ?_⟩
    have hτ : 0 < τ.re := ha.trans_le hre
    refine (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC hτ)).trans
      (Summable.tsum_le_tsum (fun q => norm_xiGaussianHeatTermC_le_of_sector hre him (hall q))
        (summable_norm_xiGaussianHeatTermC hτ) hsumm)

/-- **Unconditional sector of slope `6`.**  Every copy satisfies `6 |Im w| ≤ Re w`. -/
theorem six_mul_abs_xiSpectralSq_im_le_re (q : XiZeroCopy) :
    6 * |(xiSpectralPoint q ^ (2 : ℕ)).im| ≤ (xiSpectralPoint q ^ (2 : ℕ)).re := by
  have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
  have hB := xiSpectralSq_im_sq_le_norm_sq q
  have h150 := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  set A := (xiSpectralPoint q ^ (2 : ℕ)).re
  set B := (xiSpectralPoint q ^ (2 : ℕ)).im
  set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  have hBN : |B| ≤ N / 12 := by
    have hsq : B ^ 2 ≤ (N / 12) ^ 2 := by nlinarith
    have := sq_le_sq.1 hsq
    rwa [abs_of_pos (by linarith : (0 : ℝ) < N / 12)] at this
  linarith

theorem xiGaussianHeatTraceC_sector_bounded_six {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ τ : ℂ, a ≤ τ.re → |τ.im| ≤ 6 * (τ.re - a) → ‖xiGaussianHeatTraceC τ‖ ≤ C :=
  (xiGaussianHeatTraceC_sector_bounded_iff ha (by norm_num)).2 six_mul_abs_xiSpectralSq_im_le_re

/-- **RH as an infinite opening angle.**  RH holds iff the heat trace is bounded on the sector of every
slope `T`. -/
theorem riemannHypothesis_iff_forall_xiGaussianHeatTraceC_sector_bounded {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ T : ℝ, 0 ≤ T →
      ∃ C : ℝ, ∀ τ : ℂ, a ≤ τ.re → |τ.im| ≤ T * (τ.re - a) → ‖xiGaussianHeatTraceC τ‖ ≤ C := by
  constructor
  · intro hRH T hT
    refine (xiGaussianHeatTraceC_sector_bounded_iff ha hT).2 fun q => ?_
    have him : (xiSpectralPoint q ^ (2 : ℕ)).im = 0 := by
      rw [xiSpectralSq_eq_ofReal_re_of_rh hRH q, Complex.ofReal_im]
    have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
    have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      have := xiSpectralPoint_ne_zero q
      positivity
    rw [him, abs_zero, mul_zero]
    linarith
  · intro h
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_sq_im_pos_of_not_riemannHypothesis hRH
    set A := (xiSpectralPoint q ^ (2 : ℕ)).re
    set B := (xiSpectralPoint q ^ (2 : ℕ)).im
    have hT : 0 ≤ (A + 1) / B := by
      have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
      have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        have := xiSpectralPoint_ne_zero q
        positivity
      have : 0 < A := by simp only [A]; linarith
      positivity
    have hall := (xiGaussianHeatTraceC_sector_bounded_iff ha hT).1 (h _ hT) q
    rw [abs_of_pos hq, div_mul_cancel₀ _ hq.ne'] at hall
    linarith

/-- The sector condition in zero coordinates: `T |Im z²| ≤ Re z²` reads
`2T |γ| |β - 1/2| ≤ γ² - (β - 1/2)²`. -/
theorem xiSpectralSq_re_im (q : XiZeroCopy) :
    (xiSpectralPoint q ^ (2 : ℕ)).re = (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      |(xiSpectralPoint q ^ (2 : ℕ)).im| = 2 * |(q.1 : ℂ).im| * |(q.1 : ℂ).re - 1 / 2| := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  refine ⟨?_, ?_⟩
  · rw [pow_two, Complex.mul_re, hre, him]; ring
  · rw [pow_two, Complex.mul_im, hre, him,
      show (q.1 : ℂ).im * -((q.1 : ℂ).re - 1 / 2) + -((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im =
        -(2 * (q.1 : ℂ).im * ((q.1 : ℂ).re - 1 / 2)) by ring, abs_neg, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- **Conical zero-free region form.**  For `a > 0` and `T ≥ 0`, the heat trace is bounded on the
sector of slope `T` iff every zero `ρ` of `ξ` satisfies `2T|Im ρ||Re ρ - 1/2| ≤ (Im ρ)² - (Re ρ - 1/2)²`. -/
theorem xiGaussianHeatTraceC_sector_bounded_iff_xi_zeros {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∃ C : ℝ, ∀ τ : ℂ, a ≤ τ.re → |τ.im| ≤ T * (τ.re - a) → ‖xiGaussianHeatTraceC τ‖ ≤ C) ↔
      ∀ ρ : ℂ, xi ρ = 0 →
        2 * T * |ρ.im| * |ρ.re - 1 / 2| ≤ ρ.im ^ 2 - (ρ.re - 1 / 2) ^ 2 := by
  rw [xiGaussianHeatTraceC_sector_bounded_iff ha hT]
  constructor
  · intro h ρ hρ
    have hmem := mem_xi_divisor_support_of_eq_zero hρ
    have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) ρ := xi_divisor_pos_on_support ⟨ρ, hmem⟩
    have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) ρ) := by omega
    have hq := h ⟨⟨ρ, hmem⟩, ⟨0, hn⟩⟩
    obtain ⟨hre, him⟩ := xiSpectralSq_re_im ⟨⟨ρ, hmem⟩, ⟨0, hn⟩⟩
    rw [hre, him] at hq
    calc 2 * T * |ρ.im| * |ρ.re - 1 / 2| = T * (2 * |ρ.im| * |ρ.re - 1 / 2|) := by ring
      _ ≤ _ := hq
  · intro h q
    obtain ⟨hre, him⟩ := xiSpectralSq_re_im q
    rw [hre, him]
    have := h _ (xi_eq_zero_of_mem_divisor_support q.1)
    calc T * (2 * |(q.1 : ℂ).im| * |(q.1 : ℂ).re - 1 / 2|) =
        2 * T * |(q.1 : ℂ).im| * |(q.1 : ℂ).re - 1 / 2| := by ring
      _ ≤ _ := this

end

end RHTower
