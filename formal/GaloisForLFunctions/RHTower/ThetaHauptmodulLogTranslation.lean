import GaloisForLFunctions.RHTower.ThetaPowerFamily
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeWindowLaw

/-!
# The translation law of the Hauptmodul logarithm

Near `i∞`, `h = θ₂⁴θ₄⁴/θ₃⁸ = 16 e^{πiτ} Q(τ)` with `Q = (J/2)⁴θ₄⁴/θ₃⁸`, `J(τ) = ϑ(τ/2, τ)`, and
`|Q - 1| < 1/2` for `Im τ ≥ 6`.  Hence on `Im τ > 6` the holomorphic logarithm of `h` is
`log h = log 16 + πiτ + Log Q` (both sides are logarithms of `h` and agree on `iℝ₊`, where both are real).
Since `Q(τ+2) = Q(τ)`, this gives `log h(τ+2) = log h(τ) + 2πi` on `Im τ > 6`, hence on all of `ℍ`, and

  `F_a(τ+2) = e^{πia/2} F_a(τ)`.
-/

open Complex Real

namespace RHTower

noncomputable section

open Bottcher

/-- The normalized Hauptmodul at `i∞`: `Q(τ) = h(τ)/(16 e^{πiτ})`. -/
def cuspInfQuot (τ : ℂ) : ℂ := thetaGroupHauptmodul τ / (16 * Complex.exp (π * I * τ))

theorem cuspInfQuot_eq (τ : ℂ) :
    cuspInfQuot τ = (jacobiTheta₂ (τ / 2) τ / 2) ^ 4 * thetaFour τ ^ 4 / thetaThree τ ^ 8 := by
  unfold cuspInfQuot thetaGroupHauptmodul thetaTwo
  have h4 : Complex.exp ((π : ℂ) * I * τ / 4) ^ 4 = Complex.exp (π * I * τ) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hne : Complex.exp (π * I * τ) ≠ 0 := Complex.exp_ne_zero _
  rw [mul_pow, h4]
  field_simp
  ring

theorem cuspInfQuot_add_two (τ : ℂ) : cuspInfQuot (τ + 2) = cuspInfQuot τ := by
  unfold cuspInfQuot
  rw [thetaGroupHauptmodul_add_two]
  congr 2
  rw [show (π : ℂ) * I * (τ + 2) = π * I * τ + 2 * π * I by ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

/-- `‖z^n - 1‖ ≤ (1+ε)^n - 1` when `‖z - 1‖ ≤ ε`. -/
theorem norm_pow_sub_one_le {z : ℂ} {ε : ℝ} (hz : ‖z - 1‖ ≤ ε) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (1 + ε) ^ n - 1 := by
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) hz
  have hzn : ‖z‖ ≤ 1 + ε := by
    calc ‖z‖ = ‖(z - 1) + 1‖ := by ring_nf
      _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + ε := by rw [norm_one]; linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : ‖z ^ n‖ ≤ (1 + ε) ^ n := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hzn n
    calc ‖z ^ (n + 1) - 1‖ = ‖z ^ n * (z - 1) + (z ^ n - 1)‖ := by ring_nf
      _ ≤ ‖z ^ n‖ * ‖z - 1‖ + ‖z ^ n - 1‖ := by
          refine le_trans (norm_add_le _ _) ?_; rw [norm_mul]
      _ ≤ (1 + ε) ^ n * ε + ((1 + ε) ^ n - 1) := by
          gcongr
      _ = (1 + ε) ^ (n + 1) - 1 := by ring

/-- Three factors within `1/1000` of `1` keep `u⁴v⁴/w⁸` within `1/2` of `1`. -/
theorem norm_quot_sub_one_le_half {u v w : ℂ} (hu : ‖u - 1‖ ≤ 1 / 1000) (hv : ‖v - 1‖ ≤ 1 / 1000)
    (hw : ‖w - 1‖ ≤ 1 / 1000) : ‖u ^ 4 * v ^ 4 / w ^ 8 - 1‖ ≤ 1 / 2 := by
  have hvn : ‖v‖ ≤ 1 + 1 / 1000 := by
    calc ‖v‖ = ‖(v - 1) + 1‖ := by ring_nf
      _ ≤ ‖v - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 / 1000 := by rw [norm_one]; linarith
  have huv : ‖u * v - 1‖ ≤ 3 / 1000 := by
    calc ‖u * v - 1‖ = ‖(u - 1) * v + (v - 1)‖ := by ring_nf
      _ ≤ ‖u - 1‖ * ‖v‖ + ‖v - 1‖ := by refine le_trans (norm_add_le _ _) ?_; rw [norm_mul]
      _ ≤ 1 / 1000 * (1 + 1 / 1000) + 1 / 1000 := by gcongr
      _ ≤ 3 / 1000 := by norm_num
  have h4 := norm_pow_sub_one_le huv 4
  have h8 := norm_pow_sub_one_le hw 8
  norm_num at h4 h8
  have hw8 : (991 : ℝ) / 1000 ≤ ‖w ^ 8‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - w ^ 8)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  have hw8pos : 0 < ‖w ^ 8‖ := by linarith
  have hw8ne : w ^ 8 ≠ 0 := norm_pos_iff.mp hw8pos
  have heq : u ^ 4 * v ^ 4 / w ^ 8 - 1 = (((u * v) ^ 4 - 1) - (w ^ 8 - 1)) / w ^ 8 := by
    rw [eq_div_iff hw8ne, sub_mul, div_mul_cancel₀ _ hw8ne]; ring
  rw [heq, norm_div]
  rw [div_le_iff₀ hw8pos]
  calc ‖((u * v) ^ 4 - 1) - (w ^ 8 - 1)‖ ≤ ‖(u * v) ^ 4 - 1‖ + ‖w ^ 8 - 1‖ := norm_sub_le _ _
    _ ≤ 1 / 2 * ‖w ^ 8‖ := by nlinarith

theorem exp_neg_pi_mul_le_of_six_le {y : ℝ} (hy : 6 ≤ y) :
    Real.exp (-(π * y)) ≤ (1 / 20) ^ 6 := by
  have h := exp_neg_pi_lt_twentieth
  have h6 : Real.exp (-(π * y)) ≤ Real.exp (-π) ^ 6 := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
    have := Real.pi_pos; push_cast; nlinarith
  exact h6.trans (pow_le_pow_left₀ (Real.exp_pos _).le h.le 6)

/-- **`Q` is close to `1` near `i∞`.** -/
theorem norm_cuspInfQuot_sub_one_le {τ : ℂ} (hτ : 6 ≤ τ.im) : ‖cuspInfQuot τ - 1‖ ≤ 1 / 2 := by
  rw [cuspInfQuot_eq]
  have hτ1 : 1 ≤ τ.im := by linarith
  have hT := jacobiThetaTailConstant_le_three
  have hE := exp_neg_pi_mul_le_of_six_le hτ
  have hJ := norm_jacobiTheta₂_half_sub_two_le_exp (τ := τ) (by linarith)
  have hJ' : Real.exp (-(π / 2 * τ.im)) ≤ (1 / 20) ^ 3 := by
    have h := exp_neg_pi_lt_twentieth
    have h3 : Real.exp (-(π / 2 * τ.im)) ≤ Real.exp (-π) ^ 3 := by
      rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
      have := Real.pi_pos; push_cast; nlinarith
    exact h3.trans (pow_le_pow_left₀ (Real.exp_pos _).le h.le 3)
  refine norm_quot_sub_one_le_half ?_ ?_ ?_
  · have : jacobiTheta₂ (τ / 2) τ / 2 - 1 = (jacobiTheta₂ (τ / 2) τ - 2) / 2 := by ring
    rw [this, norm_div, Complex.norm_two]
    have : 3 * Real.exp (-(π / 2 * τ.im)) ≤ 3 * (1 / 20) ^ 3 := by gcongr
    have : ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 3 * (1 / 20) ^ 3 := hJ.trans this
    norm_num at this ⊢; linarith
  · have h := norm_thetaFour_sub_one_le hτ1
    rw [show -π * τ.im = -(π * τ.im) by ring] at h
    have hC0 := jacobiThetaTailConstant_pos
    have : jacobiThetaTailConstant * Real.exp (-π * τ.im) ≤ 3 * (1 / 20) ^ 6 := by
      rw [show -π * τ.im = -(π * τ.im) by ring]
      exact mul_le_mul hT hE (Real.exp_pos _).le (by norm_num)
    norm_num at this ⊢; linarith
  · have h := norm_thetaThree_sub_one_le hτ1
    rw [show -π * τ.im = -(π * τ.im) by ring] at h
    have hC0 := jacobiThetaTailConstant_pos
    have : jacobiThetaTailConstant * Real.exp (-π * τ.im) ≤ 3 * (1 / 20) ^ 6 := by
      rw [show -π * τ.im = -(π * τ.im) by ring]
      exact mul_le_mul hT hE (Real.exp_pos _).le (by norm_num)
    norm_num at this ⊢; linarith

theorem cuspInfQuot_re_pos {τ : ℂ} (hτ : 6 ≤ τ.im) : 0 < (cuspInfQuot τ).re := by
  have h := norm_cuspInfQuot_sub_one_le hτ
  have hre : |(cuspInfQuot τ - 1).re| ≤ 1 / 2 := (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re, Complex.one_re] at hre
  linarith [(abs_le.mp hre).1]

/-- The upper region `Im τ > 6`. -/
def upperSixSet : Set ℂ := {τ : ℂ | 6 < τ.im}

theorem isOpen_upperSixSet : IsOpen upperSixSet := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_upperSixSet : IsPreconnected upperSixSet := by
  have hc : Convex ℝ (Complex.imLm ⁻¹' Set.Ioi (6 : ℝ)) := (convex_Ioi (6 : ℝ)).linear_preimage _
  exact hc.isPreconnected

theorem differentiableOn_cuspInfQuot : DifferentiableOn ℂ cuspInfQuot upperSixSet := by
  intro τ hτ
  have hτ0 : 0 < τ.im := lt_trans (by norm_num) (show 6 < τ.im from hτ)
  have hh := differentiableAt_thetaGroupHauptmodul hτ0
  have he : DifferentiableAt ℂ (fun σ : ℂ => 16 * Complex.exp (π * I * σ)) τ := by fun_prop
  have hne : (16 : ℂ) * Complex.exp (π * I * τ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  exact (hh.div he hne).differentiableWithinAt

/-- **Branch at `i∞`.** -/
theorem hauptmodulLog_eq_cuspInf {τ : ℂ} (hτ : 6 < τ.im) :
    hauptmodulLog τ = Real.log 16 + π * I * τ + Complex.log (cuspInfQuot τ) := by
  set L₂ : ℂ → ℂ := fun σ => Real.log 16 + π * I * σ + Complex.log (cuspInfQuot σ) with hL₂
  have hmem : ∀ σ ∈ upperSixSet, 0 < σ.im := fun σ hσ => by
    have : 6 < σ.im := hσ; linarith
  have hslit : ∀ σ ∈ upperSixSet, cuspInfQuot σ ∈ Complex.slitPlane := fun σ hσ =>
    Or.inl (cuspInfQuot_re_pos (le_of_lt hσ))
  have h1 : DifferentiableOn ℂ hauptmodulLog upperSixSet :=
    differentiableOn_hauptmodulLog.mono fun σ hσ => hmem σ hσ
  have h2 : DifferentiableOn ℂ L₂ upperSixSet := by
    intro σ hσ
    have hq := (differentiableOn_cuspInfQuot σ hσ).differentiableAt
      (isOpen_upperSixSet.mem_nhds hσ)
    exact ((by fun_prop : DifferentiableAt ℂ (fun σ : ℂ => (Real.log 16 : ℂ) + π * I * σ) σ).add
      (hq.clog (hslit σ hσ))).differentiableWithinAt
  have hexp : ∀ σ ∈ upperSixSet, Complex.exp (hauptmodulLog σ) = Complex.exp (L₂ σ) := by
    intro σ hσ
    rw [exp_hauptmodulLog (hmem σ hσ), hL₂]
    simp only
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (by
        intro h; have := cuspInfQuot_re_pos (le_of_lt hσ); rw [h] at this; simp at this)]
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    unfold cuspInfQuot
    push_cast
    field_simp
  have hI : (7 : ℂ) * I ∈ upperSixSet := by show 6 < ((7 : ℂ) * I).im; norm_num
  have hconst := log_sub_eq_const isOpen_upperSixSet isPreconnected_upperSixSet h1 h2 hexp hI
  have h0 : hauptmodulLog ((7 : ℂ) * I) - L₂ ((7 : ℂ) * I) = 0 := by
    set d := hauptmodulLog ((7 : ℂ) * I) - L₂ ((7 : ℂ) * I) with hd
    have hed : Complex.exp d = 1 := by
      rw [hd, Complex.exp_sub, hexp _ hI, div_self (Complex.exp_ne_zero _)]
    have h7 : (7 : ℂ) * I = I * ((7 : ℝ) : ℂ) := by push_cast; ring
    have hreal1 : (hauptmodulLog ((7 : ℂ) * I)).im = 0 := by
      rw [h7]; exact hauptmodulLog_I_mul_im (by norm_num)
    have hQpos := thetaGroupHauptmodul_I_mul_pos (y := 7) (by norm_num)
    have hQreal : (cuspInfQuot ((7 : ℂ) * I)).im = 0 := by
      unfold cuspInfQuot
      rw [h7, hQpos.1]
      have hexp7 : Complex.exp (π * I * (I * ((7 : ℝ) : ℂ))) = ((Real.exp (-(π * 7)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hexp7, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_im]
    have hQre : 0 < (cuspInfQuot ((7 : ℂ) * I)).re := cuspInfQuot_re_pos (by norm_num)
    have hreal2 : (L₂ ((7 : ℂ) * I)).im = 0 := by
      rw [hL₂]
      simp only [Complex.add_im, Complex.ofReal_im, zero_add]
      have hlogim : (Complex.log (cuspInfQuot ((7 : ℂ) * I))).im = 0 := by
        rw [Complex.log_im]
        exact Complex.arg_eq_zero_iff.mpr ⟨hQre.le, hQreal⟩
      rw [hlogim]; simp
    have hdim : d.im = 0 := by rw [hd, Complex.sub_im, hreal1, hreal2, sub_zero]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hed
    have hnim : d.im = n * (2 * π) := by rw [hn]; simp
    have hn0 : (n : ℝ) = 0 := by
      rw [hdim] at hnim
      have := Real.pi_pos
      have h2 : (n : ℝ) * (2 * π) = 0 := hnim.symm
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · linarith
    have : n = 0 := by exact_mod_cast hn0
    rw [hn, this]; simp
  have h := hconst τ hτ
  rw [h0] at h
  exact sub_eq_zero.mp h

/-- **Translation law.** `log h(τ+2) = log h(τ) + 2πi` on `ℍ`. -/
theorem hauptmodulLog_add_two {τ : ℂ} (hτ : 0 < τ.im) :
    hauptmodulLog (τ + 2) = hauptmodulLog τ + 2 * π * I := by
  have hshift : ∀ σ ∈ modUpperSet, σ + 2 ∈ modUpperSet := fun σ hσ => by
    have h' : 0 < σ.im := hσ
    show 0 < (σ + 2).im; simpa using h'
  have h1 : DifferentiableOn ℂ (fun σ => hauptmodulLog (σ + 2)) modUpperSet :=
    differentiableOn_hauptmodulLog.comp (by fun_prop) hshift
  have h2 : DifferentiableOn ℂ (fun σ => hauptmodulLog σ + 2 * π * I) modUpperSet :=
    differentiableOn_hauptmodulLog.add_const _
  have hexp : ∀ σ ∈ modUpperSet, Complex.exp (hauptmodulLog (σ + 2)) =
      Complex.exp (hauptmodulLog σ + 2 * π * I) := by
    intro σ hσ
    rw [exp_hauptmodulLog (hshift σ hσ), Complex.exp_add, exp_hauptmodulLog hσ,
      Complex.exp_two_pi_mul_I, mul_one, thetaGroupHauptmodul_add_two]
  have hI : (7 : ℂ) * I ∈ modUpperSet := by show (0 : ℝ) < ((7 : ℂ) * I).im; simp
  have hconst := log_sub_eq_const isOpen_modUpperSet isPreconnected_modUpperSet h1 h2 hexp hI
  have h0 : hauptmodulLog ((7 : ℂ) * I + 2) - (hauptmodulLog ((7 : ℂ) * I) + 2 * π * I) = 0 := by
    rw [hauptmodulLog_eq_cuspInf (by norm_num), hauptmodulLog_eq_cuspInf (by norm_num),
      cuspInfQuot_add_two]
    ring
  have h := hconst τ hτ
  rw [h0] at h
  exact sub_eq_zero.mp h

/-- **`F_a(τ+2) = e^{πia/2} F_a(τ)`.** -/
theorem thetaPowerForm_add_two (a : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaPowerForm a (τ + 2) = Complex.exp (π * I * (a / 2 : ℝ)) * thetaPowerForm a τ := by
  unfold thetaPowerForm
  rw [thetaThree_add_two, hauptmodulLog_add_two hτ, mul_add, Complex.exp_add]
  have : ((a / 4 : ℝ) : ℂ) * (2 * π * I) = π * I * ((a / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]; ring

/-- **Cusp form of `F_a` at `i∞`.** -/
theorem thetaPowerForm_eq_cuspInf (a : ℝ) {τ : ℂ} (hτ : 6 < τ.im) :
    thetaPowerForm a τ = (2 : ℂ) ^ (a : ℂ) * Complex.exp (π * I * (a / 4 : ℝ) * τ) *
      (thetaThree τ * Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot τ))) := by
  unfold thetaPowerForm
  rw [hauptmodulLog_eq_cuspInf hτ, mul_add, mul_add, Complex.exp_add, Complex.exp_add]
  have h16 : Complex.exp (((a / 4 : ℝ) : ℂ) * (Real.log 16 : ℂ)) = (2 : ℂ) ^ (a : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]
    congr 1
    have hl2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow, hl2]
    push_cast; ring
  rw [h16]
  have : ((a / 4 : ℝ) : ℂ) * (π * I * τ) = π * I * ((a / 4 : ℝ) : ℂ) * τ := by ring
  rw [this]; ring

end

end RHTower
