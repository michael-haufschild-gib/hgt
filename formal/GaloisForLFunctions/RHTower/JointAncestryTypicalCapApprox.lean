import GaloisForLFunctions.RHTower.JointAncestryTypicalCapTail

/-!
# The shifted aggregate is the rotating coherent model up to a controlled error

Let `T` be the copies with `|Re ρ − ½| = Θ` and `F` a finite set of other copies.  Put
`sc = X^Θ`, `ζ = sc·Z(k)` and `ξ = ω^{−j} ζ`.  For a top copy the coherent exponent is
`g_ρ ξ` (`Re ρ = ½ + Θ`) or `conj(g_ρ ξ)` (`Re ρ = ½ − Θ`), up to `X^{−2Θ}|ζ|`, where
`g_ρ = e^{i γ log X}`.  The copies of `F` freeze to their weights.  Hence
`|D(k + j·1) − (Re Σ_F w + Re Σ_T b_ρ e^{g_ρ ξ})|` is bounded by the model errors plus the high
part (`abs_shifted_sub_model_le`), with `b_ρ = w_ρ` for `Re ρ = ½ + Θ` and `b_ρ = w̄_ρ` otherwise.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The top frequency `g_ρ = e^{iγ log X}`. -/
def capFreq (X : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp ((((q.1 : ℂ).im * Real.log X : ℝ) : ℂ) * Complex.I)

/-- The top coefficient. -/
def capCoeffTop (Θ : ℝ) (q : XiZeroCopy) : ℂ :=
  if (q.1 : ℂ).re = 1 / 2 + Θ then lagWeight q else conj (lagWeight q)

theorem norm_capFreq (X : ℝ) (q : XiZeroCopy) : ‖capFreq X q‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem norm_capXc (X : ℝ) (q : XiZeroCopy) :
    ‖capXc X q‖ = Real.exp (((q.1 : ℂ).re - 1 / 2) * Real.log X) := by
  unfold capXc; rw [Complex.norm_exp]
  generalize Real.log X = L
  congr 1; simp

theorem norm_capYc (X : ℝ) (q : XiZeroCopy) :
    ‖capYc X q‖ = Real.exp ((1 / 2 - (q.1 : ℂ).re) * Real.log X) := by
  unfold capYc; rw [Complex.norm_exp]
  generalize Real.log X = L
  congr 1; simp

theorem capXc_of_top {X Θ : ℝ} {q : XiZeroCopy} (h : (q.1 : ℂ).re = 1 / 2 + Θ) :
    capXc X q = (Real.exp (Θ * Real.log X) : ℂ) * capFreq X q := by
  unfold capXc capFreq
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  generalize Real.log X = L
  apply Complex.ext <;> simp [h]

theorem capYc_of_bot {X Θ : ℝ} {q : XiZeroCopy} (h : (q.1 : ℂ).re = 1 / 2 - Θ) :
    capYc X q = (Real.exp (Θ * Real.log X) : ℂ) * conj (capFreq X q) := by
  unfold capYc capFreq
  rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  generalize Real.log X = L
  apply Complex.ext <;> simp [h]

theorem norm_model_le {X : ℝ} (hX : 1 ≤ X) {q : XiZeroCopy} {θ : ℝ}
    (hq : |(q.1 : ℂ).re - 1 / 2| ≤ θ) (Z : ℂ) (j : ℂ) (hj : ‖j‖ = 1) :
    ‖conj j * (capXc X q * Z) + j * (capYc X q * conj Z)‖ ≤
      2 * (Real.exp (θ * Real.log X) * ‖Z‖) := by
  have hLX := Real.log_nonneg hX
  have h1 : ‖capXc X q‖ ≤ Real.exp (θ * Real.log X) := by
    rw [norm_capXc]; exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (abs_le.mp hq).2 hLX)
  have h2 : ‖capYc X q‖ ≤ Real.exp (θ * Real.log X) := by
    rw [norm_capYc]; exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hq).1]) hLX)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hj, one_mul,
    one_mul]
  have := norm_nonneg Z
  nlinarith

/-! ## The model for one copy -/

section Model

variable {σ Θ X R₁ δ : ℝ} {N : ℕ} {P : Finset Nat.Primes}

/-- The coherent exponent `m_ρ(k, j)`. -/
def capModel (σ X : ℝ) {N : ℕ} {P : Finset Nat.Primes} (q : XiZeroCopy) (k : ↥P → Fin N)
    (j : Fin N) : ℂ :=
  conj (unitRoot N ^ (j : ℕ)) * (capXc X q * linearPhaseSum (capCoef σ) k) +
    unitRoot N ^ (j : ℕ) * (capYc X q * conj (linearPhaseSum (capCoef σ) k))

theorem norm_capModel_le (hX : 1 ≤ X) {q : XiZeroCopy} {θ : ℝ}
    (hq : |(q.1 : ℂ).re - 1 / 2| ≤ θ) (k : ↥P → Fin N) (j : Fin N) :
    ‖capModel σ X q k j‖ ≤ 2 * (Real.exp (θ * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖) := by
  unfold capModel
  exact norm_model_le hX hq _ _ (norm_unitRoot_pow N _)

/-- `‖∏ − e^m‖ ≤ 2 e^{2R₁} δ` for one low copy. -/
theorem norm_prod_sub_exp_capModel_le (hN : 0 < N) (hX : 1 ≤ X) {q : XiZeroCopy}
    (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hAB : ∀ p : ↥P, 1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖) ≤ 1 / 2) (k : ↥P → Fin N) (j : Fin N)
    (hζ : Real.exp (Θ * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖ ≤ R₁)
    (hδ : capDelta σ X P q k ≤ δ) (hδ1 : δ ≤ 1) :
    ‖∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p) -
        Complex.exp (capModel σ X q k j)‖ ≤ 2 * Real.exp (2 * R₁) * δ := by
  have h := norm_prod_phaseFactor_shift_sub_exp_le hN (fun p : ↥P => typCapA σ q p)
    (fun p : ↥P => typCapB σ q p) (fun p : ↥P => capCoef σ p) (capXc X q) (capYc X q) k j hAB (by
      have : capDelta σ X P q k ≤ 1 := hδ.trans hδ1
      unfold capDelta at this; exact this)
  have hm := norm_capModel_le (σ := σ) hX hq k j
  have hm2 : ‖capModel σ X q k j‖ ≤ 2 * R₁ := by linarith
  unfold capModel at hm2
  refine h.trans ?_
  have hD : capDelta σ X P q k ≤ δ := hδ
  unfold capDelta at hD
  have hD0 : 0 ≤ capDelta σ X P q k := by unfold capDelta; positivity
  unfold capDelta at hD0
  have he := Real.exp_le_exp.mpr hm2
  unfold linearPhaseSum at he
  have he0 := Real.exp_pos (2 * R₁)
  calc _ ≤ 2 * Real.exp (2 * R₁) * (‖∑ p : ↥P, 1 / 2 * typCapB σ q p *
        conj (unitRoot N ^ ((k p : Fin N) : ℕ)) -
        capXc X q * ∑ p : ↥P, (capCoef σ p : ℂ) * conj (unitRoot N ^ ((k p : Fin N) : ℕ))‖ +
      ‖∑ p : ↥P, 1 / 2 * typCapA σ q p * unitRoot N ^ ((k p : Fin N) : ℕ) -
        capYc X q * conj (∑ p : ↥P, (capCoef σ p : ℂ) * conj (unitRoot N ^ ((k p : Fin N) : ℕ)))‖ +
      1 / 2 * ‖∑ p : ↥P, (1 / 2 * typCapB σ q p) ^ 2 * conj (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2‖ +
      1 / 2 * ‖∑ p : ↥P, (1 / 2 * typCapA σ q p) ^ 2 * (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2‖ +
      1 / 4 * ‖∑ p : ↥P, typCapA σ q p * typCapB σ q p‖ +
      2 / 3 * ∑ p : ↥P, (1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖)) ^ 3) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hD0
    _ ≤ 2 * Real.exp (2 * R₁) * δ := mul_le_mul_of_nonneg_left hD (by positivity)

end Model

/-! ## Top copies, frozen copies and the high part -/

section Pieces

variable {σ Θ X R₁ δ : ℝ} {N : ℕ} {P : Finset Nat.Primes}

theorem norm_exp_sub_exp_capModel_le {m m' : ℂ} {R₁ ε : ℝ} (hm' : ‖m'‖ ≤ R₁)
    (hd : ‖m - m'‖ ≤ ε) (hε : ε ≤ 1) :
    ‖Complex.exp m - Complex.exp m'‖ ≤ 2 * Real.exp R₁ * ε := by
  refine (norm_cexp_sub_cexp_le_two_mul (hd.trans hε)).trans ?_
  have h1 : Real.exp m'.re ≤ Real.exp R₁ :=
    Real.exp_le_exp.mpr ((Complex.re_le_norm m').trans hm')
  have := Real.exp_pos m'.re
  have := norm_nonneg (m - m')
  nlinarith

/-- **A top copy.** -/
theorem abs_re_top_sub_le (hN : 0 < N) (hX : 1 ≤ X) {s : XiZeroCopy}
    (hs : |(s.1 : ℂ).re - 1 / 2| = Θ)
    (hAB : ∀ p : ↥P, 1 / 2 * (‖typCapA σ s p‖ + ‖typCapB σ s p‖) ≤ 1 / 2) (k : ↥P → Fin N) (j : Fin N)
    (hζ : Real.exp (Θ * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖ ≤ R₁)
    (hδ : capDelta σ X P s k ≤ δ) (hδ1 : δ ≤ 1)
    (hs1 : Real.exp (-(2 * Θ) * Real.log X) * R₁ ≤ 1) :
    |(lagWeight s * ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ s p) (typCapB σ s p)
        (phaseShift j k p)).re -
      (capCoeffTop Θ s * Complex.exp (capFreq X s * (conj (unitRoot N ^ (j : ℕ)) *
        ((Real.exp (Θ * Real.log X) : ℂ) * linearPhaseSum (capCoef σ) k)))).re| ≤
      ‖lagWeight s‖ * (2 * Real.exp (2 * R₁) * δ +
        2 * Real.exp R₁ * (Real.exp (-(2 * Θ) * Real.log X) * R₁)) := by
  set Z := linearPhaseSum (capCoef σ) k with hZ
  set sc := Real.exp (Θ * Real.log X) with hsc
  set w := unitRoot N ^ (j : ℕ) with hw
  set ξ := conj w * ((sc : ℂ) * Z) with hξ
  have hnw : ‖w‖ = 1 := norm_unitRoot_pow N _
  have hsc0 : 0 < sc := Real.exp_pos _
  have hξn : ‖capFreq X s * ξ‖ ≤ R₁ := by
    rw [norm_mul, norm_capFreq, one_mul, hξ, norm_mul, Complex.norm_conj, hnw, one_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsc0]
    exact hζ
  have hq : |(s.1 : ℂ).re - 1 / 2| ≤ Θ := hs.le
  have hprod := norm_prod_sub_exp_capModel_le hN hX hq hAB k j hζ hδ hδ1
  have hsmall : Real.exp (-Θ * Real.log X) * ‖Z‖ ≤ Real.exp (-(2 * Θ) * Real.log X) * R₁ := by
    have : Real.exp (-Θ * Real.log X) * ‖Z‖ =
        Real.exp (-(2 * Θ) * Real.log X) * (sc * ‖Z‖) := by
      rw [hsc, ← mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hζ (Real.exp_pos _).le
  by_cases htop : (s.1 : ℂ).re = 1 / 2 + Θ
  · rw [capCoeffTop, if_pos htop]
    have hmodel : capModel σ X s k j = capFreq X s * ξ + w * (capYc X s * conj Z) := by
      unfold capModel; rw [capXc_of_top htop, ← hZ, ← hsc, ← hw, hξ]; ring
    have hr : ‖w * (capYc X s * conj Z)‖ ≤ Real.exp (-(2 * Θ) * Real.log X) * R₁ := by
      rw [norm_mul, hnw, one_mul, norm_mul, norm_capYc, Complex.norm_conj]
      refine le_trans (le_of_eq ?_) hsmall
      congr 2; rw [htop]; ring
    have hd : ‖capModel σ X s k j - capFreq X s * ξ‖ ≤
        Real.exp (-(2 * Θ) * Real.log X) * R₁ := by
      rw [hmodel, add_sub_cancel_left]; exact hr
    have h2 := norm_exp_sub_exp_capModel_le hξn hd hs1
    have htot : ‖∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ s p) (typCapB σ s p) (phaseShift j k p) -
        Complex.exp (capFreq X s * ξ)‖ ≤ 2 * Real.exp (2 * R₁) * δ +
          2 * Real.exp R₁ * (Real.exp (-(2 * Θ) * Real.log X) * R₁) := by
      have := norm_sub_le_norm_sub_add_norm_sub
        (∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ s p) (typCapB σ s p) (phaseShift j k p))
        (Complex.exp (capModel σ X s k j)) (Complex.exp (capFreq X s * ξ))
      linarith
    rw [← Complex.sub_re, ← mul_sub]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left htot (norm_nonneg _)
  · rw [capCoeffTop, if_neg htop]
    have hbot : (s.1 : ℂ).re = 1 / 2 - Θ := by
      rcases abs_eq (by linarith [abs_nonneg ((s.1 : ℂ).re - 1 / 2)] : 0 ≤ Θ) |>.mp hs with h | h
      · exact absurd (by linarith) htop
      · linarith
    have hmodel : capModel σ X s k j = conj w * (capXc X s * Z) + conj (capFreq X s * ξ) := by
      unfold capModel; rw [capYc_of_bot hbot, ← hZ, ← hsc, ← hw, hξ]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]; ring
    have hr : ‖conj w * (capXc X s * Z)‖ ≤ Real.exp (-(2 * Θ) * Real.log X) * R₁ := by
      rw [norm_mul, Complex.norm_conj, hnw, one_mul, norm_mul, norm_capXc]
      refine le_trans (le_of_eq ?_) hsmall
      congr 2; rw [hbot]; ring
    have hξn' : ‖conj (capFreq X s * ξ)‖ ≤ R₁ := by rw [Complex.norm_conj]; exact hξn
    have hd : ‖capModel σ X s k j - conj (capFreq X s * ξ)‖ ≤
        Real.exp (-(2 * Θ) * Real.log X) * R₁ := by
      rw [hmodel, add_sub_cancel_right]; exact hr
    have h2 := norm_exp_sub_exp_capModel_le hξn' hd hs1
    have htot : ‖∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ s p) (typCapB σ s p) (phaseShift j k p) -
        Complex.exp (conj (capFreq X s * ξ))‖ ≤ 2 * Real.exp (2 * R₁) * δ +
          2 * Real.exp R₁ * (Real.exp (-(2 * Θ) * Real.log X) * R₁) := by
      have := norm_sub_le_norm_sub_add_norm_sub
        (∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ s p) (typCapB σ s p) (phaseShift j k p))
        (Complex.exp (capModel σ X s k j)) (Complex.exp (conj (capFreq X s * ξ)))
      linarith
    have hre : (conj (lagWeight s) * Complex.exp (capFreq X s * ξ)).re =
        (lagWeight s * Complex.exp (conj (capFreq X s * ξ))).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, ← Complex.exp_conj]
    rw [hre, ← Complex.sub_re, ← mul_sub]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left htot (norm_nonneg _)

/-- **A frozen copy.** -/
theorem abs_re_low_sub_le (hN : 0 < N) (hX : 1 ≤ X) {q : XiZeroCopy} {ΘF : ℝ}
    (hqF : |(q.1 : ℂ).re - 1 / 2| ≤ ΘF) (hΘF : ΘF ≤ Θ)
    (hAB : ∀ p : ↥P, 1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖) ≤ 1 / 2) (k : ↥P → Fin N) (j : Fin N)
    (hζ : Real.exp (Θ * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖ ≤ R₁)
    (hδ : capDelta σ X P q k ≤ δ) (hδ1 : δ ≤ 1)
    (hs2 : 2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁) ≤ 1) :
    |(lagWeight q * ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p)
        (phaseShift j k p)).re - (lagWeight q).re| ≤
      ‖lagWeight q‖ * (2 * Real.exp (2 * R₁) * δ +
        2 * (2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁))) := by
  have hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ := hqF.trans hΘF
  have hprod := norm_prod_sub_exp_capModel_le hN hX hq hAB k j hζ hδ hδ1
  have hm := norm_capModel_le (σ := σ) (N := N) (P := P) hX hqF k j
  have hm2 : ‖capModel σ X q k j‖ ≤ 2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁) := by
    refine hm.trans ?_
    have : Real.exp (ΘF * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖ =
        Real.exp ((ΘF - Θ) * Real.log X) *
          (Real.exp (Θ * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖) := by
      rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hζ (Real.exp_pos _).le)
      (by norm_num)
  have hexp1 : ‖Complex.exp (capModel σ X q k j) - 1‖ ≤
      2 * (2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁)) :=
    (Complex.norm_exp_sub_one_le (hm2.trans hs2)).trans (by linarith)
  have htot : ‖∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p) - 1‖
      ≤ 2 * Real.exp (2 * R₁) * δ + 2 * (2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁)) := by
    have := norm_sub_le_norm_sub_add_norm_sub
      (∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p))
      (Complex.exp (capModel σ X q k j)) 1
    linarith
  rw [show (lagWeight q).re = (lagWeight q * 1).re by rw [mul_one], ← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left htot (norm_nonneg _)

end Pieces

/-! ## The whole shifted aggregate -/

section Whole

variable {σ Θ X R₁ δ : ℝ} {N : ℕ} {P : Finset Nat.Primes}

theorem summable_lagWeight_mul_prod {Θ : ℝ} (hΘσ : Θ ≤ σ)
    (habs : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ Θ) (k : ↥P → Fin N) :
    Summable fun q : XiZeroCopy => lagWeight q *
      ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (k p) := by
  refine Summable.of_norm_bounded (summable_norm_lagWeight.mul_right ((2 : ℝ) ^ P.card))
    fun q => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_prod_phaseFactor_le_two_pow _ _
    (fun p => norm_capA_le_one hΘσ (habs q) p) (fun p => norm_capB_le_one hΘσ (habs q) p) k)
    (norm_nonneg _)

theorem norm_high_sum_le {Θ : ℝ} (hΘσ : Θ ≤ σ)
    (habs : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ Θ) (Low : Finset XiZeroCopy)
    (k : ↥P → Fin N) (j : Fin N) :
    ‖∑' q : ↑((Low : Set XiZeroCopy)ᶜ), lagWeight q *
        ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p)‖ ≤
      capHigh σ N P Low k := by
  have hs : Summable fun q : ↑((Low : Set XiZeroCopy)ᶜ) => ‖lagWeight q *
      ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p)‖ :=
    ((summable_lagWeight_mul_prod hΘσ habs (phaseShift j k)).subtype _).norm
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  unfold capHigh
  refine Summable.tsum_le_tsum (fun q => ?_) hs (summable_capHigh_term hΘσ habs N P Low k)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.single_le_sum (f := fun j' : Fin N => ‖∏ p : ↥P, phaseFactor N (1 / 2)
    (typCapA σ q p) (typCapB σ q p) (phaseShift j' k p)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- **The approximation of the shifted aggregate.** -/
theorem abs_shifted_sub_model_le (hN : 0 < N) (hX : 1 ≤ X) (hΘσ : Θ ≤ σ)
    (habs : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hAB : ∀ q : XiZeroCopy, ∀ p : ↥P, 1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖) ≤ 1 / 2)
    {T F : Finset XiZeroCopy} (hTF : Disjoint T F) (hT : ∀ s ∈ T, |(s.1 : ℂ).re - 1 / 2| = Θ)
    {ΘF : ℝ} (hΘF : ΘF ≤ Θ) (hF : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| ≤ ΘF)
    (k : ↥P → Fin N) (j : Fin N)
    (hζ : Real.exp (Θ * Real.log X) * ‖linearPhaseSum (capCoef σ) k‖ ≤ R₁)
    (hδ : ∀ q ∈ T ∪ F, capDelta σ X P q k ≤ δ) (hδ1 : δ ≤ 1)
    (hs1 : Real.exp (-(2 * Θ) * Real.log X) * R₁ ≤ 1)
    (hs2 : 2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁) ≤ 1) :
    |(∑' q : XiZeroCopy, lagWeight q *
        ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p)).re -
      ((∑ q ∈ F, lagWeight q).re + (∑ s ∈ T, capCoeffTop Θ s *
        Complex.exp (capFreq X s * (conj (unitRoot N ^ (j : ℕ)) *
          ((Real.exp (Θ * Real.log X) : ℂ) * linearPhaseSum (capCoef σ) k)))).re)| ≤
      (∑ s ∈ T, ‖lagWeight s‖) * (2 * Real.exp (2 * R₁) * δ +
          2 * Real.exp R₁ * (Real.exp (-(2 * Θ) * Real.log X) * R₁)) +
        (∑ q ∈ F, ‖lagWeight q‖) * (2 * Real.exp (2 * R₁) * δ +
          2 * (2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁))) +
        capHigh σ N P (T ∪ F) k := by
  set f : XiZeroCopy → ℂ := fun q => lagWeight q *
    ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p) with hf
  have hsum : Summable f := summable_lagWeight_mul_prod hΘσ habs (phaseShift j k)
  rw [← hsum.sum_add_tsum_compl (s := T ∪ F), Finset.sum_union hTF]
  have hhigh := norm_high_sum_le (σ := σ) hΘσ habs (T ∪ F) k j
  have htop : ∀ s ∈ T, |(f s).re - (capCoeffTop Θ s *
      Complex.exp (capFreq X s * (conj (unitRoot N ^ (j : ℕ)) *
        ((Real.exp (Θ * Real.log X) : ℂ) * linearPhaseSum (capCoef σ) k)))).re| ≤
      ‖lagWeight s‖ * (2 * Real.exp (2 * R₁) * δ +
        2 * Real.exp R₁ * (Real.exp (-(2 * Θ) * Real.log X) * R₁)) := fun s hs =>
    abs_re_top_sub_le hN hX (hT s hs) (hAB s) k j hζ (hδ s (Finset.mem_union_left _ hs)) hδ1 hs1
  have hlow : ∀ q ∈ F, |(f q).re - (lagWeight q).re| ≤
      ‖lagWeight q‖ * (2 * Real.exp (2 * R₁) * δ +
        2 * (2 * (Real.exp ((ΘF - Θ) * Real.log X) * R₁))) := fun q hq =>
    abs_re_low_sub_le hN hX (hF q hq) hΘF (hAB q) k j hζ (hδ q (Finset.mem_union_right _ hq))
      hδ1 hs2
  have hT' := Finset.abs_sum_le_sum_abs (fun s => (f s).re - (capCoeffTop Θ s *
      Complex.exp (capFreq X s * (conj (unitRoot N ^ (j : ℕ)) *
        ((Real.exp (Θ * Real.log X) : ℂ) * linearPhaseSum (capCoef σ) k)))).re) T
  have hF' := Finset.abs_sum_le_sum_abs (fun q => (f q).re - (lagWeight q).re) F
  have hTs := Finset.sum_le_sum htop
  have hFs := Finset.sum_le_sum hlow
  rw [← Finset.sum_mul] at hTs hFs
  have hH := (Complex.abs_re_le_norm (∑' q : ↑((↑(T ∪ F) : Set XiZeroCopy)ᶜ), f q)).trans hhigh
  have hexp : (∑ x ∈ T, f x + ∑ x ∈ F, f x + ∑' x : ↑((↑(T ∪ F) : Set XiZeroCopy)ᶜ), f x).re -
      ((∑ q ∈ F, lagWeight q).re + (∑ s ∈ T, capCoeffTop Θ s *
        Complex.exp (capFreq X s * (conj (unitRoot N ^ (j : ℕ)) *
          ((Real.exp (Θ * Real.log X) : ℂ) * linearPhaseSum (capCoef σ) k)))).re) =
      (∑ s ∈ T, ((f s).re - (capCoeffTop Θ s *
        Complex.exp (capFreq X s * (conj (unitRoot N ^ (j : ℕ)) *
          ((Real.exp (Θ * Real.log X) : ℂ) * linearPhaseSum (capCoef σ) k)))).re)) +
      (∑ q ∈ F, ((f q).re - (lagWeight q).re)) +
      (∑' x : ↑((↑(T ∪ F) : Set XiZeroCopy)ᶜ), f x).re := by
    simp only [Complex.add_re, Complex.re_sum, Finset.sum_sub_distrib]
    ring
  rw [hexp]
  set A := ∑ s ∈ T, ((f s).re - (capCoeffTop Θ s *
        Complex.exp (capFreq X s * (conj (unitRoot N ^ (j : ℕ)) *
          ((Real.exp (Θ * Real.log X) : ℂ) * linearPhaseSum (capCoef σ) k)))).re)
  set B := ∑ q ∈ F, ((f q).re - (lagWeight q).re)
  set C := (∑' x : ↑((↑(T ∪ F) : Set XiZeroCopy)ᶜ), f x).re
  have a1 := abs_add_le (A + B) C
  have a2 := abs_add_le A B
  linarith

end Whole

end

end RHTower
