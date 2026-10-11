import GaloisForLFunctions.RHTower.JointAncestryAbscissaGap
import GaloisForLFunctions.RHTower.JointAncestryDressingTwoExistence
import GaloisForLFunctions.RHTower.ZetaPoleBoundExplicit
import GaloisForLFunctions.RHTower.WeilShiftPairLandau

/-!
# A half-plane bound gives JAS positivity just above `σ = 1`

**Theorem** (`jasDressedPSD_one_add_three_mul_of_xiZeroHalfPlaneBound`).  If every Xi zero has
`Re ρ ≤ ½ + α` with `0 ≤ α ≤ 1/20`, then the dressed JAS aggregate is positive semidefinite at
`σ = 1 + 3α`.

Together with the chain exclusion this pins the JAS abscissa between two multiples of the
off-line distance `δ* = sup |Re ρ − ½|`: off RH, under a half-plane bound below `½` and with
`δ* ≤ 1/20`,

`1 + δ* ≤ σ* ≤ 1 + 3δ*`   (`one_add_sSup_le_jasAbscissa_and_le`).

So the abscissa above `1` measures the distance of the zeros from the critical line, while RH is
the isolated value `σ* = 0`.

**Proof.**  Per-zero phase budgets suffice for positivity.  At `σ = 1 + 3α` a zero with
`|Re ρ − ½| = δ ≤ α` has radii `r_{1,2} = p^{−(1 + 3α ± δ)}`, so
`|r₁ − r₂| ≤ 2δ log p · p^{−(1 + 3α − δ)} ≤ 2α log p · p^{−(1 + 2α)}` and both radii are at
most `½`.  The width is at most `(4/3)|r₁ − r₂|`, and
`Σ_p log p · p^{−s} ≤ −ζ'/ζ(s) ≤ 1/(s − 1) + 1`.  The budget is therefore at most
`1/14 + (8/3)α(1/(2α) + 1) < π/2`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The prime part of `−ζ'/ζ`: `Σ_{p ∈ P} log p · p^{−s} ≤ 1/(s − 1) + 1` for `1 < s ≤ 2`. -/
theorem sum_log_mul_exp_neg_le (P : Finset Nat.Primes) {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    ∑ p ∈ P, Real.log p * Real.exp (-s * Real.log p) ≤ 1 / (s - 1) + 1 := by
  classical
  have hsum := WeilOneSided.summable_vonMangoldt_rpow hs1
  have heq : ∀ p ∈ P, Real.log p * Real.exp (-s * Real.log p) =
      (if 2 ≤ ((p : ℕ)) then (ArithmeticFunction.vonMangoldt (p : ℕ) : ℝ) else 0) *
        (((p : ℕ) : ℝ)) ^ (-s) := by
    intro p _
    rw [if_pos p.2.two_le, ArithmeticFunction.vonMangoldt_apply_prime p.2,
      Real.rpow_def_of_pos (by exact_mod_cast p.2.pos), mul_comm (Real.log _) (-s)]
  rw [Finset.sum_congr rfl heq]
  have hmap : ∑ p ∈ P, (if 2 ≤ ((p : ℕ)) then (ArithmeticFunction.vonMangoldt (p : ℕ) : ℝ)
        else 0) * (((p : ℕ) : ℝ)) ^ (-s) =
      ∑ n ∈ P.map (Function.Embedding.subtype _),
        (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) * ((n : ℝ)) ^ (-s) := by
    rw [Finset.sum_map]; rfl
  rw [hmap]
  refine (hsum.sum_le_tsum _ (fun n _ => WeilOneSided.vonMangoldt_rpow_nonneg s n)).trans ?_
  have h3 := neg_re_logDeriv_riemannZeta_real_le hs1 hs2
  rw [← WeilOneSided.tsum_vonMangoldt_rpow_eq hs1, Complex.ofReal_re] at h3
  exact h3

/-- `|e^{−x} − e^{x}| ≤ 2|x| e^{|x|}`. -/
theorem abs_exp_neg_sub_exp_le (x : ℝ) : |Real.exp (-x) - Real.exp x| ≤ 2 * |x| * Real.exp |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.exp y - Real.exp (-y) ≤ 2 * y * Real.exp y := by
    intro y hy
    have h1 := Real.add_one_le_exp (-(2 * y))
    have h2 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    have := Real.exp_pos y
    nlinarith
  rcases le_total 0 x with hx | hx
  · have hle : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg hx]
    linarith [key x hx]
  · have hle : Real.exp x ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos hx]
    have := key (-x) (by linarith)
    rw [neg_neg] at this
    linarith

/-- **Phase width under a half-plane bound.**  At `σ = 1 + Kα` a zero with `|Re ρ − ½| ≤ α`
has width at most `(8/3) α · log p · p^{−(1 + (K − 1)α)}`. -/
theorem jasPhaseWidth_le_of_abs_re_sub_half_le {ρ : ℂ} {alpha K : ℝ}
    (hρ : |ρ.re - 1 / 2| ≤ alpha) (hK : 1 ≤ K) (halpha : 0 ≤ alpha) (p : Nat.Primes) :
    jasPhaseWidth (jasR1 (ρ + ((1 / 2 + K * alpha : ℝ) : ℂ)) p)
        (jasR2 (ρ - ((1 / 2 + K * alpha : ℝ) : ℂ)) p) ≤
      8 / 3 * alpha * (Real.log p * Real.exp (-(1 + (K - 1) * alpha) * Real.log p)) := by
  rw [jasR1_dressed, jasR2_dressed]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ρ.re - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log p := ⟨_, rfl⟩
  have hL2 : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  have hL0 : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2
  rw [← hL]
  have hre : ρ.re = 1 / 2 + δ := by rw [hδ]; ring
  rw [hre]
  have hδa : |δ| ≤ alpha := by rw [hδ]; exact hρ
  obtain ⟨r₁, hr₁⟩ : ∃ r, r = Real.exp (-(1 / 2 + δ + (1 / 2 + K * alpha)) * L) := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r, r = Real.exp (-(1 - (1 / 2 + δ) + (1 / 2 + K * alpha)) * L) :=
    ⟨_, rfl⟩
  rw [← hr₁, ← hr₂]
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(1 + (K - 1) * alpha) * L) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hEhalf : E ≤ 1 / 2 := by
    rw [hE]
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [← h2]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ (K - 1) * alpha * L := by
      have := mul_nonneg (sub_nonneg.mpr hK) halpha
      positivity
    nlinarith
  have hδ1 : -alpha ≤ δ := (abs_le.mp hδa).1
  have hδ2 : δ ≤ alpha := (abs_le.mp hδa).2
  have hr₁E : r₁ ≤ E := by
    rw [hr₁, hE]; refine Real.exp_le_exp.mpr ?_; nlinarith
  have hr₂E : r₂ ≤ E := by
    rw [hr₂, hE]; refine Real.exp_le_exp.mpr ?_; nlinarith
  have hr₁0 : 0 < r₁ := by rw [hr₁]; exact Real.exp_pos _
  have hr₂0 : 0 < r₂ := by rw [hr₂]; exact Real.exp_pos _
  -- the difference of the radii
  have hdiff : |r₁ - r₂| ≤ 2 * alpha * L * E := by
    have hsplit : r₁ - r₂ = Real.exp (-(1 + K * alpha) * L) *
        (Real.exp (-(δ * L)) - Real.exp (δ * L)) := by
      rw [hr₁, hr₂, mul_sub, ← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [hsplit, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hb := abs_exp_neg_sub_exp_le (δ * L)
    have habs : |δ * L| ≤ alpha * L := by
      rw [abs_mul, abs_of_pos hL0]; exact mul_le_mul_of_nonneg_right hδa hL0.le
    have hb2 : 2 * |δ * L| * Real.exp |δ * L| ≤ 2 * (alpha * L) * Real.exp (alpha * L) := by
      have he : Real.exp |δ * L| ≤ Real.exp (alpha * L) := Real.exp_le_exp.mpr habs
      have := abs_nonneg (δ * L)
      have := Real.exp_pos |δ * L|
      nlinarith
    have hprod : Real.exp (-(1 + K * alpha) * L) * Real.exp (alpha * L) = E := by
      rw [hE, ← Real.exp_add]; ring_nf
    calc Real.exp (-(1 + K * alpha) * L) * |Real.exp (-(δ * L)) - Real.exp (δ * L)|
        ≤ Real.exp (-(1 + K * alpha) * L) * (2 * (alpha * L) * Real.exp (alpha * L)) :=
          mul_le_mul_of_nonneg_left (hb.trans hb2) (Real.exp_pos _).le
      _ = 2 * alpha * L * (Real.exp (-(1 + K * alpha) * L) * Real.exp (alpha * L)) := by ring
      _ = 2 * alpha * L * E := by rw [hprod]
  -- the denominator
  have hden : (3 / 4 : ℝ) ≤ Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
    refine Real.le_sqrt_of_sq_le ?_
    have a : (3 / 4 : ℝ) ≤ 1 - r₁ ^ 2 := by nlinarith
    have b : (3 / 4 : ℝ) ≤ 1 - r₂ ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by linarith
  unfold jasPhaseWidth
  refine (arctan_le_self_of_nonneg' (div_nonneg (abs_nonneg _) hpos.le)).trans ?_
  rw [div_le_iff₀ hpos]
  have h0 : 0 ≤ 2 * alpha * L * E := by positivity
  nlinarith

/-- **JAS positivity just above `σ = 1` under a half-plane bound.** -/
theorem jasDressedPSD_one_add_three_mul_of_xiZeroHalfPlaneBound {alpha : ℝ} (h0 : 0 ≤ alpha)
    (h1 : alpha ≤ 1 / 20) (hXi : XiZeroHalfPlaneBound alpha) : JasDressedPSD (1 + 3 * alpha) := by
  rcases h0.lt_or_eq with hpos | hzero
  · have h := jasDressedPSD_of_phaseBudget (c := 1 / 2 + 3 * alpha) (by linarith) fun q P => by
      have harg := abs_arg_jasWeight_le q
      have hq := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q
      have hw : ∑ p ∈ P, jasPhaseWidth (jasR1 ((q.1 : ℂ) + ((1 / 2 + 3 * alpha : ℝ) : ℂ)) p)
          (jasR2 ((q.1 : ℂ) - ((1 / 2 + 3 * alpha : ℝ) : ℂ)) p) ≤
          ∑ p ∈ P, 8 / 3 * alpha *
            (Real.log p * Real.exp (-(1 + (3 - 1) * alpha) * Real.log p)) :=
        Finset.sum_le_sum fun p _ =>
          jasPhaseWidth_le_of_abs_re_sub_half_le hq (by norm_num) h0 p
      rw [← Finset.mul_sum] at hw
      have hs := sum_log_mul_exp_neg_le P (s := 1 + (3 - 1) * alpha) (by nlinarith)
        (by nlinarith)
      have hinv : 1 / (1 + (3 - 1) * alpha - 1) = 1 / (2 * alpha) := by ring_nf
      rw [hinv] at hs
      have hmul : 8 / 3 * alpha * (1 / (2 * alpha) + 1) = 4 / 3 + 8 / 3 * alpha := by
        field_simp; ring
      have hb : 8 / 3 * alpha * ∑ p ∈ P, Real.log p *
          Real.exp (-(1 + (3 - 1) * alpha) * Real.log p) ≤ 4 / 3 + 8 / 3 * alpha := by
        rw [← hmul]; exact mul_le_mul_of_nonneg_left hs (by positivity)
      have hpi := Real.pi_gt_d2
      linarith
    have he : (1 / 2 + (1 / 2 + 3 * alpha) : ℝ) = 1 + 3 * alpha := by ring
    rwa [he] at h
  · subst hzero
    rw [mul_zero, add_zero]
    exact jasDressedPSD_of_riemannHypothesis
      (riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr hXi) (by norm_num)

/-- `σ* ≤ 1 + 3α` under a half-plane bound `α ≤ 1/20`. -/
theorem jasAbscissa_le_one_add_three_mul {alpha : ℝ} (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1 / 20)
    (hXi : XiZeroHalfPlaneBound alpha) : jasAbscissa ≤ 1 + 3 * alpha :=
  jasDressedPSD_iff_jasAbscissa_le.mp (jasDressedPSD_one_add_three_mul_of_xiZeroHalfPlaneBound h0 h1 hXi)

/-- **The two-sided abscissa law.**  Off RH, under a half-plane bound `α < ½`, with
`δ* = sup |Re ρ − ½| ≤ 1/20`: `1 + δ* ≤ σ* ≤ 1 + 3δ*`. -/
theorem one_add_sSup_le_jasAbscissa_and_le {alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) (hRH : ¬ RiemannHypothesis)
    (hsmall : sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ 1 / 20) :
    1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ jasAbscissa ∧
      jasAbscissa ≤ 1 + 3 * sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) := by
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  have hS0 : 0 ≤ sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) := by
    obtain ⟨q, _⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
    exact le_trans (abs_nonneg _) (le_csSup hbdd ⟨q, rfl⟩)
  have hXiS : XiZeroHalfPlaneBound
      (sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|)) := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have h := le_csSup hbdd ⟨q, rfl⟩
    simp only at h
    have := le_abs_self ((q.1 : ℂ).re - 1 / 2)
    linarith
  refine ⟨?_, jasAbscissa_le_one_add_three_mul hS0 hsmall hXiS⟩
  rcases jasAbscissa_eq_zero_or_one_add_sSup_le halpha0 halpha hXi with h | h
  · exact absurd (riemannHypothesis_iff_jasAbscissa_eq_zero.mpr h) hRH
  · exact h

end

end RHTower
