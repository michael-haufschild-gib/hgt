import GaloisForLFunctions.RHTower.XiGaussianHeatPrimeChirpReceiver
import GaloisForLFunctions.RHTower.XiStripEdgeHeightFloorRatioGate

/-!
# Exponential type of the heat trace on a vertical line ⇔ hyperbolic zero-free region

For complex time `τ = a + ib` the Gaussian heat trace of the Xi divisor is
`ν(τ) = Σ_q exp(-τ w_q)`, with `w_q = z_q²` and `z_q = -i(ρ_q - 1/2)`.  Here
`Im w_q = -2 γ_q (β_q - 1/2)`, where `ρ_q = β_q + iγ_q`.

**Theorem** (`xiGaussianHeatTraceC_exponentialType_iff`).  For `a > 0` and `κ ≥ 0`:

`ν(a + ib) = O(e^{κ|b|})`  ⇔  every zero satisfies `2 |γ| |β - 1/2| ≤ κ`.

So the exponential type of `ν` along one vertical line is exactly the width of the horizontal strip
containing all squared spectral points.  Equivalently, the zeros lie in the hyperbolic region
`|β - 1/2| ≤ κ/(2|γ|)` (`xiGaussianHeatTraceC_exponentialType_iff_xi_zeros`).  For `κ = 0` this is
RH.  For `κ > 0` it is a one-parameter ladder of weakenings of RH: each forces every zero within
`O(1/γ)` of the critical line.

Prime form (`gaussianPrimeChirpSum_exponentialType_iff`):
`Σ_n Λ(n) n^{-1/2} exp(-(log n)²/(4τ)) = O(|τ|^{1/2} e^{κ|b|})` on `Re τ = a` iff the same
hyperbolic region contains every zero.

Mechanism.  The `⇐` direction is termwise.  For `⇒`, Phragmén–Lindelöf on the strip
`π/4 < Im s < π/2` with the multiplier `exp(iκe^s)` (modulus `≤ 1` there) transfers
`‖ν(a+ib)‖ ≤ C e^{κb}` from the vertical line to the sector
(`norm_xiGaussianHeatTraceC_le_of_vertical_exp`).  A copy with `Im w > κ` then grows faster than
`e^{κ r sin φ}` along a ray `a + r e^{iφ}` with `φ` close to `π/2`.  The light-cone lemma, applied to
the shifted exponents `e^{iφ} w + κ sin φ`, makes the damped trace unbounded.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Phragmén–Lindelöf with an exponential multiplier.**  A bound `C e^{κ b}` on the upper half of
the vertical line `Re τ = a` propagates to the sector between the 45° ray from `a` and that line. -/
theorem norm_xiGaussianHeatTraceC_le_of_vertical_exp {a κ C : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ)
    (hC : ∀ b : ℝ, 0 ≤ b → ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (κ * b))
    {s : ℂ} (h1 : Real.pi / 4 ≤ s.im) (h2 : s.im ≤ Real.pi / 2) :
    ‖xiGaussianHeatTraceC ((a : ℂ) + Complex.exp s)‖ ≤
      max C (3 / a * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) *
        Real.exp (κ * (Complex.exp s).im) := by
  set K := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  have hK : 0 ≤ K := tsum_nonneg fun _ => by positivity
  have hpi := Real.pi_pos
  set g : ℂ → ℂ := fun s => xiGaussianHeatTraceC ((a : ℂ) + Complex.exp s) *
    Complex.exp (I * (κ : ℂ) * Complex.exp s)
  have hmul : ∀ s : ℂ, ‖Complex.exp (I * (κ : ℂ) * Complex.exp s)‖ =
      Real.exp (-(κ * (Complex.exp s).im)) := by
    intro s
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have him0 : ∀ s : ℂ, Real.pi / 4 ≤ s.im → s.im ≤ Real.pi / 2 → 0 ≤ (Complex.exp s).im := by
    intro s h1 h2
    rw [Complex.exp_im]
    exact mul_nonneg (Real.exp_pos _).le
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  have hre : ∀ s : ℂ, Real.pi / 4 ≤ s.im → s.im ≤ Real.pi / 2 →
      a ≤ ((a : ℂ) + Complex.exp s).re := by
    intro s h1 h2
    have hcos : 0 ≤ Real.cos s.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩
    simp only [add_re, ofReal_re, Complex.exp_re]
    have := mul_nonneg (Real.exp_pos s.re).le hcos
    linarith
  have hdiffAt : ∀ s : ℂ, Real.pi / 4 ≤ s.im → s.im ≤ Real.pi / 2 → DifferentiableAt ℂ g s := by
    intro s h1 h2
    have hτ : 0 < ((a : ℂ) + Complex.exp s).re := ha.trans_le (hre s h1 h2)
    exact ((differentiableAt_xiGaussianHeatTraceC hτ).comp s
      ((differentiableAt_const _).add differentiableAt_exp)).mul
        ((differentiableAt_const _).mul differentiableAt_exp).cexp
  have hd : DiffContOnCl ℂ g (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine ⟨fun s hs => (hdiffAt s hs.1.le hs.2.le).differentiableWithinAt, ?_⟩
    have hcl : closure (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2)) ⊆
        Complex.im ⁻¹' Icc (Real.pi / 4) (Real.pi / 2) :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_im)
    exact fun s hs => (hdiffAt s (hcl hs).1 (hcl hs).2).continuousAt.continuousWithinAt
  have hgrowth : ∃ c < Real.pi / (Real.pi / 2 - Real.pi / 4), ∃ B,
      g =O[comap (abs ∘ Complex.re) atTop ⊓ 𝓟 (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2))]
        fun s => Real.exp (B * Real.exp (c * |s.re|)) := by
    have h4 : Real.pi / (Real.pi / 2 - Real.pi / 4) = 4 := by field_simp; ring
    refine ⟨2, by rw [h4]; norm_num, 1 / a, Asymptotics.IsBigO.of_bound (4 / a * K) ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun s hs => ?_)
    have hres := hre s hs.1.le hs.2.le
    have hτ : 0 < ((a : ℂ) + Complex.exp s).re := ha.trans_le hres
    have hm : ‖Complex.exp (I * (κ : ℂ) * Complex.exp s)‖ ≤ 1 := by
      rw [hmul, Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hκ (him0 s hs.1.le hs.2.le)
    simp only [g]
    rw [norm_mul]
    refine (mul_le_of_le_one_right (norm_nonneg _) hm).trans ?_
    refine (norm_xiGaussianHeatTraceC_le_growth hτ).trans ?_
    set σ := ((a : ℂ) + Complex.exp s).re
    set b := ((a : ℂ) + Complex.exp s).im
    have hb : b ^ 2 ≤ Real.exp (2 * |s.re|) := by
      have hbim : b = Real.exp s.re * Real.sin s.im := by
        simp only [b, add_im, ofReal_im, Complex.exp_im, zero_add]
      rw [hbim, mul_pow]
      have hs2 : Real.sin s.im ^ 2 ≤ 1 := Real.sin_sq_le_one _
      have he2 : Real.exp s.re ^ 2 ≤ Real.exp (2 * |s.re|) := by
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.2 (by push_cast; linarith [le_abs_self s.re])
      nlinarith [sq_nonneg (Real.exp s.re), Real.exp_pos (2 * |s.re|)]
    have hexp : Real.exp (b ^ 2 / σ) ≤ Real.exp (1 / a * Real.exp (2 * |s.re|)) := by
      apply Real.exp_le_exp.2
      calc b ^ 2 / σ ≤ b ^ 2 / a := div_le_div_of_nonneg_left (sq_nonneg _) ha hres
        _ ≤ Real.exp (2 * |s.re|) / a := div_le_div_of_nonneg_right hb ha.le
        _ = 1 / a * Real.exp (2 * |s.re|) := by ring
    have h4σ : 4 / σ ≤ 4 / a := div_le_div_of_nonneg_left (by norm_num) ha hres
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (b ^ 2 / σ) * (4 / σ) * K
        ≤ Real.exp (1 / a * Real.exp (2 * |s.re|)) * (4 / a) * K := by gcongr
      _ = 4 / a * K * Real.exp (1 / a * Real.exp (2 * |s.re|)) := by ring
  have hPL := PhragmenLindelof.horizontal_strip (f := g) (z := s) (C := max C (3 / a * K))
    hd hgrowth ?_ ?_ h1 h2
  · simp only [g] at hPL
    rw [norm_mul, hmul] at hPL
    have hpos : 0 < Real.exp (-(κ * (Complex.exp s).im)) := Real.exp_pos _
    rw [← le_div_iff₀ hpos, div_eq_mul_inv, ← Real.exp_neg, neg_neg] at hPL
    exact hPL
  · -- the 45° ray
    intro z hz
    simp only [g]
    rw [norm_mul, hmul]
    have hm : Real.exp (-(κ * (Complex.exp z).im)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hκ (him0 z hz.ge (by rw [hz]; linarith))
    refine (mul_le_of_le_one_right (norm_nonneg _) hm).trans
      (le_max_of_le_right (norm_xiGaussianHeatTraceC_le_of_abs_im_le ha (hre z hz.ge (by
        rw [hz]; linarith)) ?_))
    have hcs : Real.sin z.im = Real.cos z.im := by
      rw [hz, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hcos : 0 ≤ Real.cos z.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    simp only [add_im, add_re, ofReal_im, ofReal_re, Complex.exp_im, Complex.exp_re, zero_add]
    rw [hcs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hcos)]
    linarith
  · -- the vertical line
    intro z hz
    have hexp : Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [Complex.exp_re, hz, Real.cos_pi_div_two]
      · rw [Complex.exp_im, hz, Real.sin_pi_div_two, mul_one, Complex.mul_I_im, Complex.ofReal_re]
    simp only [g]
    rw [norm_mul, hmul, hexp]
    have him : (((Real.exp z.re : ℝ) : ℂ) * I).im = Real.exp z.re := by
      rw [Complex.mul_I_im, Complex.ofReal_re]
    rw [him]
    refine le_max_of_le_left ?_
    have h := hC (Real.exp z.re) (Real.exp_pos _).le
    calc ‖xiGaussianHeatTraceC ((a : ℂ) + ((Real.exp z.re : ℝ) : ℂ) * I)‖ *
          Real.exp (-(κ * Real.exp z.re))
        ≤ C * Real.exp (κ * Real.exp z.re) * Real.exp (-(κ * Real.exp z.re)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = C := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- A copy whose squared spectral coordinate has `|Im| > κ` yields one with `Im > κ`. -/
theorem exists_xiZeroCopy_sq_im_gt {κ : ℝ} {q : XiZeroCopy}
    (hq : κ < |(xiSpectralPoint q ^ (2 : ℕ)).im|) :
    ∃ q₁ : XiZeroCopy, κ < (xiSpectralPoint q₁ ^ (2 : ℕ)).im := by
  rcases le_or_gt 0 (xiSpectralPoint q ^ (2 : ℕ)).im with hpos | hneg
  · exact ⟨q, by rwa [abs_of_nonneg hpos] at hq⟩
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_⟩
    rw [xiSpectralPoint_lineConj, ← map_pow, Complex.conj_im]
    rwa [abs_of_neg hneg] at hq

/-- **Exponential type law.**  For `a > 0` and `κ ≥ 0`, the heat trace has exponential type at most
`κ` along the vertical line `Re τ = a` iff every squared spectral point lies in the strip
`|Im w| ≤ κ`. -/
theorem xiGaussianHeatTraceC_exponentialType_iff {a κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ) :
    (∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (κ * |b|)) ↔
      ∀ q : XiZeroCopy, |(xiSpectralPoint q ^ (2 : ℕ)).im| ≤ κ := by
  set K := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  constructor
  · rintro ⟨C, hC⟩
    by_contra hbad
    push Not at hbad
    obtain ⟨q₀, hq₀⟩ := hbad
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_sq_im_gt hq₀
    set C' := max C (3 / a * K)
    set A₁ := (xiSpectralPoint q₁ ^ (2 : ℕ)).re
    set B₁ := (xiSpectralPoint q₁ ^ (2 : ℕ)).im
    have hpi := Real.pi_pos
    obtain ⟨φ, hφ1, hφ2, hφneg⟩ : ∃ φ : ℝ, Real.pi / 4 < φ ∧ φ < Real.pi / 2 ∧
        Real.cos φ * A₁ - Real.sin φ * (B₁ - κ) < 0 := by
      have hcont : ContinuousAt (fun φ : ℝ => Real.cos φ * A₁ - Real.sin φ * (B₁ - κ))
          (Real.pi / 2) := by fun_prop
      have hval : (fun φ : ℝ => Real.cos φ * A₁ - Real.sin φ * (B₁ - κ)) (Real.pi / 2) < 0 := by
        simp only [Real.cos_pi_div_two, Real.sin_pi_div_two]
        linarith
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hval))
      refine ⟨Real.pi / 2 - min (δ / 2) (Real.pi / 8), ?_, ?_, hball ?_⟩
      · have := min_le_right (δ / 2) (Real.pi / 8)
        linarith
      · have : 0 < min (δ / 2) (Real.pi / 8) := lt_min (by linarith) (by linarith)
        linarith
      · have h0 : 0 < min (δ / 2) (Real.pi / 8) := lt_min (by linarith) (by linarith)
        rw [Real.dist_eq, show Real.pi / 2 - min (δ / 2) (Real.pi / 8) - Real.pi / 2 =
          -min (δ / 2) (Real.pi / 8) by ring, abs_neg, abs_of_pos h0]
        linarith [min_le_left (δ / 2) (Real.pi / 8)]
    have hcosφ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ2⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsin1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
    set e : ℂ := Complex.exp ((φ : ℂ) * I)
    have he_re : e.re = Real.cos φ := Complex.exp_ofReal_mul_I_re φ
    have he_im : e.im = Real.sin φ := Complex.exp_ofReal_mul_I_im φ
    set W : XiZeroCopy → ℂ := fun q => e * xiSpectralPoint q ^ (2 : ℕ) + ((κ * Real.sin φ : ℝ) : ℂ)
    have hW_re : ∀ q : XiZeroCopy, (W q).re =
        Real.cos φ * (xiSpectralPoint q ^ (2 : ℕ)).re -
          Real.sin φ * ((xiSpectralPoint q ^ (2 : ℕ)).im - κ) := fun q => by
      simp only [W, add_re, ofReal_re, Complex.mul_re, he_re, he_im]
      ring
    -- the damped trace along the ray is bounded
    have hray : ∀ r : ℝ, 0 ≤ r → ‖xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e)‖ ≤
        C' * Real.exp (κ * (r * Real.sin φ)) := by
      intro r hr
      have hCup : ∀ b : ℝ, 0 ≤ b →
          ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (κ * b) := fun b hb => by
        have := hC b
        rwa [abs_of_nonneg hb] at this
      rcases hr.eq_or_lt with h0 | hpos
      · rw [← h0, ofReal_zero, zero_mul, add_zero, zero_mul, mul_zero, Real.exp_zero, mul_one]
        exact le_max_of_le_right (norm_xiGaussianHeatTraceC_le_of_abs_im_le ha (by simp)
          (by simp [ha.le]))
      · have hs : (r : ℂ) * e = Complex.exp ((Real.log r : ℂ) + (φ : ℂ) * I) := by
          rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
        have hsim : (Complex.exp ((Real.log r : ℂ) + (φ : ℂ) * I)).im = r * Real.sin φ := by
          rw [← hs, Complex.im_ofReal_mul, he_im]
        have h := norm_xiGaussianHeatTraceC_le_of_vertical_exp ha hκ hCup
          (s := (Real.log r : ℂ) + (φ : ℂ) * I) (by simp; linarith) (by simp; linarith)
        rw [hsim, ← hs] at h
        exact h
    have hterm : ∀ (q : XiZeroCopy) (r : ℝ),
        Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) * Complex.exp (-(r : ℂ) * W q) =
          xiGaussianHeatTermC ((a : ℂ) + (r : ℂ) * e) q *
            ((Real.exp (-(κ * (r * Real.sin φ))) : ℝ) : ℂ) := fun q r => by
      rw [xiGaussianHeatTermC, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [W]
      push_cast
      ring
    have hτre : ∀ r : ℝ, 0 ≤ r → 0 < ((a : ℂ) + (r : ℂ) * e).re := fun r hr => by
      simp only [add_re, ofReal_re, re_ofReal_mul, he_re]
      nlinarith
    have hfin : {q : XiZeroCopy | (W q).re < 0}.Finite := by
      have hc2 : 0 < Real.cos φ ^ 2 / 4 := by positivity
      have hev := (xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero).eventually
        (gt_mem_nhds hc2)
      refine (Filter.eventually_cofinite.1 hev).subset fun q hq => ?_
      simp only [mem_setOf_eq] at hq ⊢
      rw [hW_re] at hq
      have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
      have hB := xiSpectralSq_im_sq_le_norm_sq q
      have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        have := xiSpectralPoint_ne_zero q
        positivity
      set A := (xiSpectralPoint q ^ (2 : ℕ)).re
      set B := (xiSpectralPoint q ^ (2 : ℕ)).im
      set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
      have hlt : Real.cos φ * N / 2 < |B| := by
        have h1 : Real.sin φ * (B - κ) ≤ |B| := by
          calc Real.sin φ * (B - κ) ≤ Real.sin φ * |B| := by
                apply mul_le_mul_of_nonneg_left _ hsinφ
                linarith [le_abs_self B]
            _ ≤ 1 * |B| := mul_le_mul_of_nonneg_right hsin1 (abs_nonneg B)
            _ = |B| := one_mul _
        nlinarith
      have hsq : (Real.cos φ * N / 2) ^ 2 < B ^ 2 := by
        rw [← sq_abs B]
        exact pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
      rw [not_lt, le_div_iff₀ hN]
      nlinarith
    obtain ⟨r, hr0, hr⟩ := GaloisForLFunctions.HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg
      (w := W) (c := fun q : XiZeroCopy => Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)))
      (ε₀ := 0) le_rfl
      (fun i j hij => by
        have hne : e ≠ 0 := Complex.exp_ne_zero _
        have h' : e * xiSpectralPoint i ^ (2 : ℕ) = e * xiSpectralPoint j ^ (2 : ℕ) := by
          simpa only [W, add_left_inj] using hij
        have : xiSpectralPoint i ^ (2 : ℕ) = xiSpectralPoint j ^ (2 : ℕ) :=
          mul_left_cancel₀ hne h'
        simp only [this])
      (fun _ _ => Complex.exp_ne_zero _) hfin
      (m := fun q => (2 / a) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
      (fun q => by positivity) (xiSpectralPoint_inv_sq_summable.mul_left _)
      (fun q hq ε hε => by
        rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
        have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
        have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
          have := xiSpectralPoint_ne_zero q
          positivity
        have hre1 : (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)).re =
            -(a * (xiSpectralPoint q ^ (2 : ℕ)).re) := by
          rw [neg_mul, neg_re, re_ofReal_mul]
        have hre2 : (-(ε : ℂ) * W q).re = -(ε * (W q).re) := by
          rw [neg_mul, neg_re, re_ofReal_mul]
        rw [hre1, hre2, ← Real.exp_add]
        set A := (xiSpectralPoint q ^ (2 : ℕ)).re
        set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
        have hA : 0 < a * A := mul_pos ha (by linarith)
        calc Real.exp (-(a * A) + -(ε * (W q).re))
            ≤ Real.exp (-(a * A)) := Real.exp_le_exp.2 (by nlinarith [mul_nonneg hε hq])
          _ ≤ 1 / (a * A) := exp_neg_le_inv_of_pos hA
          _ ≤ 2 / a * (1 / N) := by
            rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hA (mul_pos ha hN)]
            nlinarith)
      (fun ε hε => by
        simp only [hterm, norm_mul]
        exact (summable_norm_xiGaussianHeatTermC (hτre ε hε)).mul_right _)
      ⟨q₁, by rw [hW_re]; exact hφneg⟩ C'
    have hsum : ∑' q : XiZeroCopy, Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
        Complex.exp (-(r : ℂ) * W q) =
          xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e) *
            ((Real.exp (-(κ * (r * Real.sin φ))) : ℝ) : ℂ) := by
      rw [xiGaussianHeatTraceC, ← tsum_mul_right]
      exact tsum_congr fun q => hterm q r
    rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hr
    have hb := hray r hr0
    have hpos : 0 < Real.exp (-(κ * (r * Real.sin φ))) := Real.exp_pos _
    have : ‖xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e)‖ * Real.exp (-(κ * (r * Real.sin φ))) ≤
        C' := by
      calc ‖xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e)‖ * Real.exp (-(κ * (r * Real.sin φ)))
          ≤ C' * Real.exp (κ * (r * Real.sin φ)) * Real.exp (-(κ * (r * Real.sin φ))) :=
            mul_le_mul_of_nonneg_right hb hpos.le
        _ = C' := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    linarith
  · intro hstrip
    refine ⟨2 / a * K, fun b => ?_⟩
    have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
    rw [← tsum_mul_left, ← tsum_mul_right]
    refine (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC hτ)).trans
      (Summable.tsum_le_tsum (fun q => ?_) (summable_norm_xiGaussianHeatTermC hτ)
        ((xiSpectralPoint_inv_sq_summable.mul_left _).mul_right _))
    rw [norm_xiGaussianHeatTermC]
    have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
    have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      have := xiSpectralPoint_ne_zero q
      positivity
    have hBq := hstrip q
    set A := (xiSpectralPoint q ^ (2 : ℕ)).re
    set B := (xiSpectralPoint q ^ (2 : ℕ)).im
    set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
    have hre' : ((a : ℂ) + b * I).re = a := by simp
    have him' : ((a : ℂ) + b * I).im = b := by simp
    rw [hre', him']
    have hA : 0 < a * A := mul_pos ha (by linarith)
    have hbB : b * B ≤ κ * |b| := by
      calc b * B ≤ |b * B| := le_abs_self _
        _ = |b| * |B| := abs_mul _ _
        _ ≤ |b| * κ := mul_le_mul_of_nonneg_left hBq (abs_nonneg _)
        _ = κ * |b| := mul_comm _ _
    calc Real.exp (-(a * A - b * B))
        ≤ Real.exp (κ * |b|) * Real.exp (-(a * A)) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
      _ ≤ Real.exp (κ * |b|) * (1 / (a * A)) :=
          mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos hA) (Real.exp_pos _).le
      _ ≤ Real.exp (κ * |b|) * (2 / a * (1 / N)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hA (mul_pos ha hN)]
          nlinarith
      _ = 2 / a * (1 / N) * Real.exp (κ * |b|) := by ring

/-- The squared spectral coordinate of a copy has `|Im| = 2 |γ| |β - 1/2|`. -/
theorem abs_xiSpectralSq_im (q : XiZeroCopy) :
    |(xiSpectralPoint q ^ (2 : ℕ)).im| = 2 * |(q.1 : ℂ).im| * |(q.1 : ℂ).re - 1 / 2| := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  rw [pow_two, Complex.mul_im, hre, him]
  rw [show (q.1 : ℂ).im * -((q.1 : ℂ).re - 1 / 2) + -((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im =
    -(2 * (q.1 : ℂ).im * ((q.1 : ℂ).re - 1 / 2)) by ring, abs_neg, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- **Hyperbolic zero-free region form.**  For `a > 0` and `κ ≥ 0`, `ν(a + ib) = O(e^{κ|b|})` iff
every zero `ρ` of `ξ` satisfies `2 |Im ρ| |Re ρ - 1/2| ≤ κ`. -/
theorem xiGaussianHeatTraceC_exponentialType_iff_xi_zeros {a κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ) :
    (∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (κ * |b|)) ↔
      ∀ ρ : ℂ, xi ρ = 0 → 2 * |ρ.im| * |ρ.re - 1 / 2| ≤ κ := by
  rw [xiGaussianHeatTraceC_exponentialType_iff ha hκ]
  constructor
  · intro h ρ hρ
    have hmem := mem_xi_divisor_support_of_eq_zero hρ
    have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) ρ := xi_divisor_pos_on_support ⟨ρ, hmem⟩
    have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) ρ) := by omega
    have := h ⟨⟨ρ, hmem⟩, ⟨0, hn⟩⟩
    rwa [abs_xiSpectralSq_im] at this
  · intro h q
    rw [abs_xiSpectralSq_im]
    exact h _ (xi_eq_zero_of_mem_divisor_support q.1)

/-- **Prime form of the hyperbolic ladder.**  For `a > 0` and `κ ≥ 0`, the Gaussian–von Mangoldt chirp
sum satisfies `S(a + ib) = O(|a + ib|^{1/2} e^{κ|b|})` iff every zero of `ξ` satisfies
`2 |Im ρ| |Re ρ - 1/2| ≤ κ`.  The case `κ = 0` is RH. -/
theorem gaussianPrimeChirpSum_exponentialType_iff {a κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ) :
    (∃ C : ℝ, ∀ b : ℝ, ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ ≤
        C * Real.sqrt ‖(a : ℂ) + b * I‖ * Real.exp (κ * |b|)) ↔
      ∀ ρ : ℂ, xi ρ = 0 → 2 * |ρ.im| * |ρ.re - 1 / 2| ≤ κ := by
  rw [← xiGaussianHeatTraceC_exponentialType_iff_xi_zeros ha hκ]
  set A : ℝ := ∫ x : ℝ, ‖xiGaussianCenteredArchIntegrand a 0 x‖
  set P : ℝ := 2 * Real.pi * Real.exp (a / 4)
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hP : 0 ≤ P := by positivity
  have hre : ∀ b : ℝ, 0 < ((a : ℂ) + b * I).re := fun b => by simpa using ha
  have hid := fun b : ℝ => pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime (hre b)
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsq : ∀ b : ℝ, 0 < Real.sqrt ‖(a : ℂ) + b * I‖ := fun b => by
    apply Real.sqrt_pos.2
    apply norm_pos_iff.2
    intro h0
    have := congrArg Complex.re h0; simp at this; linarith
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hfac : ∀ b : ℝ, ‖gaussianPrimeChirpC ((a : ℂ) + b * I)‖ =
      Real.sqrt Real.pi * (‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ /
        Real.sqrt ‖(a : ℂ) + b * I‖) := fun b => by
    have hτ0 : (a : ℂ) + b * I ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have hne : (Real.pi : ℂ) / ((a : ℂ) + b * I) ≠ 0 :=
      div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hτ0
    rw [gaussianPrimeChirpC, norm_mul, Complex.norm_cpow_of_ne_zero hne]
    have him : (1 / 2 : ℂ).im = 0 := by norm_num
    have hre2 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [him, hre2, mul_zero, Real.exp_zero, div_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Real.div_rpow Real.pi_pos.le (norm_nonneg _), ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
    ring
  have hE : ∀ b : ℝ, 1 ≤ Real.exp (κ * |b|) := fun b =>
    Real.one_le_exp (mul_nonneg hκ (abs_nonneg b))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(A + P + Real.sqrt Real.pi * |C|) / Real.pi, fun b => ?_⟩
    set τb : ℂ := (a : ℂ) + b * I
    have hEb := hE b
    have hprime : ‖gaussianPrimeChirpC τb‖ ≤ Real.sqrt Real.pi * |C| * Real.exp (κ * |b|) := by
      rw [hfac b]
      have h1 : ‖gaussianPrimeChirpSum τb‖ / Real.sqrt ‖τb‖ ≤ |C| * Real.exp (κ * |b|) := by
        rw [div_le_iff₀ (hsq b)]
        calc ‖gaussianPrimeChirpSum τb‖ ≤ C * Real.sqrt ‖τb‖ * Real.exp (κ * |b|) := hC b
          _ ≤ |C| * Real.sqrt ‖τb‖ * Real.exp (κ * |b|) := by
            gcongr
            exact le_abs_self C
          _ = |C| * Real.exp (κ * |b|) * Real.sqrt ‖τb‖ := by ring
      calc Real.sqrt Real.pi * (‖gaussianPrimeChirpSum τb‖ / Real.sqrt ‖τb‖)
          ≤ Real.sqrt Real.pi * (|C| * Real.exp (κ * |b|)) :=
            mul_le_mul_of_nonneg_left h1 hspi.le
        _ = Real.sqrt Real.pi * |C| * Real.exp (κ * |b|) := by ring
    have hpiν : Real.pi * ‖xiGaussianHeatTraceC τb‖ ≤
        A + P + Real.sqrt Real.pi * |C| * Real.exp (κ * |b|) := by
      have h0 : Real.pi * ‖xiGaussianHeatTraceC τb‖ =
          ‖gaussianArchCriticalC τb + gaussianArchPoleC τb - gaussianPrimeChirpC τb‖ := by
        rw [← hid b, norm_mul, hpi]
      rw [h0]
      calc ‖gaussianArchCriticalC τb + gaussianArchPoleC τb - gaussianPrimeChirpC τb‖
          ≤ ‖gaussianArchCriticalC τb + gaussianArchPoleC τb‖ + ‖gaussianPrimeChirpC τb‖ :=
            norm_sub_le _ _
        _ ≤ ‖gaussianArchCriticalC τb‖ + ‖gaussianArchPoleC τb‖ + ‖gaussianPrimeChirpC τb‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ A + P + Real.sqrt Real.pi * |C| * Real.exp (κ * |b|) := by
            gcongr
            · exact norm_gaussianArchCriticalC_le a b
            · exact (norm_gaussianArchPoleC a b).le
    rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left hEb (add_nonneg hA hP)]
  · rintro ⟨C, hC⟩
    refine ⟨(A + P + Real.pi * |C|) / Real.sqrt Real.pi, fun b => ?_⟩
    have hprime : gaussianPrimeChirpC ((a : ℂ) + b * I) =
        gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I) -
          (Real.pi : ℂ) * xiGaussianHeatTraceC ((a : ℂ) + b * I) := by
      rw [hid b]; ring
    have hbound : ‖gaussianPrimeChirpC ((a : ℂ) + b * I)‖ ≤
        (A + P + Real.pi * |C|) * Real.exp (κ * |b|) := by
      rw [hprime]
      have h1 := norm_sub_le (gaussianArchCriticalC ((a : ℂ) + b * I) +
        gaussianArchPoleC ((a : ℂ) + b * I))
        ((Real.pi : ℂ) * xiGaussianHeatTraceC ((a : ℂ) + b * I))
      have h2 := norm_add_le (gaussianArchCriticalC ((a : ℂ) + b * I))
        (gaussianArchPoleC ((a : ℂ) + b * I))
      have h3 := norm_gaussianArchCriticalC_le a b
      have h4 := norm_gaussianArchPoleC a b
      rw [norm_mul, hpi] at h1
      have h5 : Real.pi * ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤
          Real.pi * (|C| * Real.exp (κ * |b|)) := by
        refine mul_le_mul_of_nonneg_left ((hC b).trans ?_) Real.pi_pos.le
        gcongr; exact le_abs_self C
      have hEb := hE b
      nlinarith [mul_le_mul_of_nonneg_left hEb (add_nonneg hA hP)]
    rw [hfac b] at hbound
    have h' : ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ / Real.sqrt ‖(a : ℂ) + b * I‖ ≤
        (A + P + Real.pi * |C|) / Real.sqrt Real.pi * Real.exp (κ * |b|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hspi]
      linarith
    rw [div_le_iff₀ (hsq b)] at h'
    linarith

/-- **Exponential type zero suffices.**  For `a > 0`, RH holds iff the heat trace has exponential type
zero along the vertical line `Re τ = a`: `ν(a + ib) = O(e^{ε|b|})` for every `ε > 0`. -/
theorem riemannHypothesis_iff_xiGaussianHeatTraceC_subexponential {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ b : ℝ,
      ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (ε * |b|) := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC⟩ := (riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha).1 hRH
    refine ⟨|C|, fun b => (hC b).trans ?_⟩
    calc C ≤ |C| := le_abs_self C
      _ = |C| * 1 := (mul_one _).symm
      _ ≤ |C| * Real.exp (ε * |b|) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (abs_nonneg C)
  · intro h
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_sq_im_pos_of_not_riemannHypothesis hRH
    set B := (xiSpectralPoint q ^ (2 : ℕ)).im
    have hstrip := (xiGaussianHeatTraceC_exponentialType_iff ha (by positivity : (0 : ℝ) ≤ B / 2)).1
      (h (B / 2) (by positivity)) q
    rw [abs_of_pos hq] at hstrip
    linarith

/-- **Prime form of exponential type zero.**  For `a > 0`, RH holds iff for every `ε > 0`
`Σ_n Λ(n) n^{-1/2} exp(-(log n)²/(4(a+ib))) = O(|a+ib|^{1/2} e^{ε|b|})`, that is,
`log |S(a+ib)| = o(|b|)`. -/
theorem riemannHypothesis_iff_gaussianPrimeChirpSum_subexponential {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ b : ℝ,
      ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ ≤
        C * Real.sqrt ‖(a : ℂ) + b * I‖ * Real.exp (ε * |b|) := by
  rw [riemannHypothesis_iff_xiGaussianHeatTraceC_subexponential ha]
  refine forall_congr' fun ε => imp_congr_right fun hε => ?_
  rw [xiGaussianHeatTraceC_exponentialType_iff_xi_zeros ha hε.le,
    gaussianPrimeChirpSum_exponentialType_iff ha hε.le]

/-- **Finite exponential type gives a zero-free half-plane.**  If the heat trace has exponential type
at most `κ` on one vertical line, then every zero of `ξ` satisfies `|Re ρ - 1/2| ≤ κ/18`. -/
theorem abs_re_sub_half_le_of_xiGaussianHeatTraceC_exponentialType {a κ : ℝ} (ha : 0 < a)
    (hκ : 0 ≤ κ)
    (h : ∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (κ * |b|))
    {ρ : ℂ} (hρ : xi ρ = 0) : |ρ.re - 1 / 2| ≤ κ / 18 := by
  have hz := (xiGaussianHeatTraceC_exponentialType_iff_xi_zeros ha hκ).1 h ρ hρ
  have hfloor := xi_zero_im_sq_gt_floor hρ
  have h9 : 9 < |ρ.im| := by
    by_contra h'
    push Not at h'
    have := sq_le_sq' (abs_le.1 h').1 (abs_le.1 h').2
    nlinarith
  have hd := abs_nonneg (ρ.re - 1 / 2)
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

end

end RHTower
