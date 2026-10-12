import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage

/-!
# The de Bruijn–Newman flow of the dense single-defect model

Let `F(z) = (z² + δ²) cos(Lz/2)` (`cosDefect`): real zeros `±(2k+1)π/L` of density `L/2π` and one
off-line pair `±iδ`.  Its de Bruijn–Newman flow at time `λ > 0` is the Gaussian average
`H_λ(z) = E[F(z − iU)]`, `U` of variance `2λ` (`cosDefectFlow`), i.e. `e^{−λD²}F`.

**Closed form** (`cosDefectFlow_eq`).

  `H_λ(z) = ½ e^{λL²/4} (Q₊(z) e^{iLz/2} + Q₋(z) e^{−iLz/2})`,  `Q_±(z) = (z ∓ iλL)² + δ² − 2λ`.

**Collision time.**
* If `δ² − 2λ ≤ (λL)²`, every zero of `H_λ` is real (`im_eq_zero_of_cosDefectFlow_eq_zero`).
* If `0 ≤ λ` and `(λL)² < δ² − 2λ`, `H_λ` has a zero on the positive imaginary axis
  (`exists_cosDefectFlow_imaginary_zero`).

So the de Bruijn–Newman constant of the model is the root of `(λL)² = δ² − 2λ`,
`Λ = (√(1 + δ²L²) − 1)/L² ∼ δ/L`.

Proof.  The tilt `g(u) e^{au} = e^{λa²} g(u − 2λa)` and the quadratic Gaussian average
`E[(c − iU)² + δ²] = c² + δ² − 2λ` give the closed form.  Real zeros: with `c = δ² − 2λ` and `z = x + iy`,

  `|Q₋(z)|² − |Q₊(z)|² = 8 y λL (x² + y² + λ²L² − c)`,

which has the sign of `y` when `c ≤ λ²L²`.  Since `|e^{−iLz/2}| = e^{Ly/2}`, the two terms of `H_λ`
cannot cancel off the real axis (Hermite–Biehler).  Imaginary zero: on `z = iY` the flow is real.  It is
`≥ 0` at `Y₀ = √c − λL`, where `Q₋(iY₀) = 0` and `Q₊(iY₀) = 4λL·Y₀`, and `< 0` at `Y₀ + √c + 1`.
-/

open MeasureTheory Filter Topology Complex

namespace RHTower.DeBruijn

noncomputable section

/-- The dense single-defect model `F(z) = (z² + δ²) cos(Lz/2)`. -/
def cosDefect (δ L : ℝ) (z : ℂ) : ℂ := (z ^ 2 + (δ : ℂ) ^ 2) * Complex.cos ((L : ℂ) * z / 2)

/-- The de Bruijn–Newman flow of the model at time `λ`: `E[F(z − iU)]`, `U` of variance `2λ`. -/
def cosDefectFlow (δ L lam : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (gaussDensity lam u : ℂ) * cosDefect δ L (z - I * u)

/-- The closed-form factor `½(Q₊ e^{iLz/2} + Q₋ e^{−iLz/2})`. -/
def cosDefectFlowCore (δ L lam : ℝ) (z : ℂ) : ℂ :=
  ((z - I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam) * Complex.exp (I * L * z / 2) / 2
    + ((z + I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam) * Complex.exp (-(I * L * z / 2)) / 2

/-- `E[(c − iU)² + δ²] = c² + δ² − 2λ`. -/
theorem integrable_and_integral_gaussDensity_quadratic {lam : ℝ} (hlam : 0 < lam) (δ : ℝ) (c : ℂ) :
    Integrable (fun v : ℝ => (gaussDensity lam v : ℂ) * ((c - I * v) ^ 2 + (δ : ℂ) ^ 2)) ∧
      ∫ v : ℝ, (gaussDensity lam v : ℂ) * ((c - I * v) ^ 2 + (δ : ℂ) ^ 2)
        = c ^ 2 + (δ : ℂ) ^ 2 - 2 * lam := by
  have hI : ∀ k : ℕ, Integrable (fun v : ℝ => (gaussDensity lam v : ℂ) * (v : ℂ) ^ k) := fun k =>
    ((integrable_gaussDensity_mul_pow hlam k).ofReal).congr
      (Eventually.of_forall fun v => by push_cast; rfl)
  have hm0 : ∫ v : ℝ, (gaussDensity lam v : ℂ) * (v : ℂ) ^ 0 = 1 := by
    rw [integral_gaussDensity_mul_ofReal_pow]
    have h := integral_gaussDensity_mul_pow_even hlam 0
    simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] at h ⊢
    rw [h]; simp
  have hm1 : ∫ v : ℝ, (gaussDensity lam v : ℂ) * (v : ℂ) ^ 1 = 0 := by
    rw [integral_gaussDensity_mul_ofReal_pow]
    have h := integral_gaussDensity_mul_pow_odd lam 0
    simp only [mul_zero, zero_add] at h
    rw [h]; simp
  have hm2 : ∫ v : ℝ, (gaussDensity lam v : ℂ) * (v : ℂ) ^ 2 = 2 * lam := by
    rw [integral_gaussDensity_mul_ofReal_pow]
    have h := integral_gaussDensity_mul_pow_even hlam 1
    simp only [mul_one, pow_one, Nat.factorial] at h
    rw [h]; push_cast; ring
  have hfun : (fun v : ℝ => (gaussDensity lam v : ℂ) * ((c - I * v) ^ 2 + (δ : ℂ) ^ 2))
      = fun v => (c ^ 2 + (δ : ℂ) ^ 2) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 0)
        + (-2 * I * c) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 1)
        + (-1) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 2) := by
    funext v
    have hI2 : I ^ 2 = -1 := I_sq
    linear_combination (gaussDensity lam v : ℂ) * (v : ℂ) ^ 2 * hI2
  have hint : Integrable (fun v : ℝ => (c ^ 2 + (δ : ℂ) ^ 2) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 0)
      + (-2 * I * c) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 1)
      + (-1) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 2)) :=
    (((hI 0).const_mul _).add ((hI 1).const_mul _)).add ((hI 2).const_mul _)
  refine ⟨hfun ▸ hint, ?_⟩
  have h01 : Integrable (fun v : ℝ => (c ^ 2 + (δ : ℂ) ^ 2) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 0)
      + (-2 * I * c) * ((gaussDensity lam v : ℂ) * (v : ℂ) ^ 1)) :=
    ((hI 0).const_mul _).add ((hI 1).const_mul _)
  rw [hfun, integral_add h01 ((hI 2).const_mul _),
    integral_add ((hI 0).const_mul _) ((hI 1).const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hm0, hm1, hm2]
  ring

/-- **Gaussian tilt.**  `E[e^{aU}((z − iU)² + δ²)] = e^{λa²}((z − 2iλa)² + δ² − 2λ)`. -/
theorem integrable_and_integral_gaussDensity_tilt_quadratic {lam : ℝ} (hlam : 0 < lam) (δ a : ℝ)
    (z : ℂ) :
    Integrable (fun u : ℝ => (gaussDensity lam u : ℂ) * ((Real.exp (a * u) : ℝ) : ℂ)
        * ((z - I * u) ^ 2 + (δ : ℂ) ^ 2)) ∧
      ∫ u : ℝ, (gaussDensity lam u : ℂ) * ((Real.exp (a * u) : ℝ) : ℂ) * ((z - I * u) ^ 2 + (δ : ℂ) ^ 2)
        = ((Real.exp (lam * a ^ 2) : ℝ) : ℂ)
          * ((z - I * (2 * lam * a)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam) := by
  obtain ⟨hint, hval⟩ := integrable_and_integral_gaussDensity_quadratic hlam δ (z - I * (2 * lam * a))
  have htilt : ∀ u : ℝ, gaussDensity lam u * Real.exp (a * u)
      = Real.exp (lam * a ^ 2) * gaussDensity lam (u - 2 * lam * a) := by
    intro u
    unfold gaussDensity
    have hexp : -(u ^ 2 / (4 * lam)) + a * u = lam * a ^ 2 + -((u - 2 * lam * a) ^ 2 / (4 * lam)) := by
      field_simp; ring
    calc (4 * Real.pi * lam) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u ^ 2 / (4 * lam))) * Real.exp (a * u)
        = (4 * Real.pi * lam) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u ^ 2 / (4 * lam)) + a * u) := by
          rw [mul_assoc, ← Real.exp_add]
      _ = (4 * Real.pi * lam) ^ (-(1 / 2 : ℝ))
          * Real.exp (lam * a ^ 2 + -((u - 2 * lam * a) ^ 2 / (4 * lam))) := by rw [hexp]
      _ = _ := by rw [Real.exp_add]; ring
  have hpt : ∀ u : ℝ, (gaussDensity lam u : ℂ) * ((Real.exp (a * u) : ℝ) : ℂ) * ((z - I * u) ^ 2 + (δ : ℂ) ^ 2)
      = ((Real.exp (lam * a ^ 2) : ℝ) : ℂ) * ((fun v : ℝ => (gaussDensity lam v : ℂ)
        * (((z - I * (2 * lam * a)) - I * v) ^ 2 + (δ : ℂ) ^ 2)) (u - 2 * lam * a)) := by
    intro u
    have h1 : ((gaussDensity lam u : ℝ) : ℂ) * ((Real.exp (a * u) : ℝ) : ℂ)
        = ((Real.exp (lam * a ^ 2) : ℝ) : ℂ) * (gaussDensity lam (u - 2 * lam * a) : ℂ) := by
      rw [← Complex.ofReal_mul, htilt, Complex.ofReal_mul]
    have h2 : (z - I * (2 * lam * a)) - I * ((u - 2 * lam * a : ℝ) : ℂ) = z - I * u := by
      push_cast; ring
    simp only
    rw [h2, h1]
    ring
  have hfun : (fun u : ℝ => (gaussDensity lam u : ℂ) * ((Real.exp (a * u) : ℝ) : ℂ)
      * ((z - I * u) ^ 2 + (δ : ℂ) ^ 2))
      = fun u => ((Real.exp (lam * a ^ 2) : ℝ) : ℂ) * ((fun v : ℝ => (gaussDensity lam v : ℂ)
        * (((z - I * (2 * lam * a)) - I * v) ^ 2 + (δ : ℂ) ^ 2)) (u - 2 * lam * a)) := funext hpt
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hint.comp_sub_right _).const_mul _
  · rw [hfun, integral_const_mul, integral_sub_right_eq_self
      (fun v : ℝ => (gaussDensity lam v : ℂ) * (((z - I * (2 * lam * a)) - I * v) ^ 2 + (δ : ℂ) ^ 2)),
      hval]

/-- **Closed form of the flow.** -/
theorem cosDefectFlow_eq {lam : ℝ} (hlam : 0 < lam) (δ L : ℝ) (z : ℂ) :
    cosDefectFlow δ L lam z = ((Real.exp (lam * L ^ 2 / 4) : ℝ) : ℂ) * cosDefectFlowCore δ L lam z := by
  obtain ⟨h1, v1⟩ := integrable_and_integral_gaussDensity_tilt_quadratic hlam δ (L / 2) z
  obtain ⟨h2, v2⟩ := integrable_and_integral_gaussDensity_tilt_quadratic hlam δ (-(L / 2)) z
  have hpt : ∀ u : ℝ, (gaussDensity lam u : ℂ) * cosDefect δ L (z - I * u)
      = Complex.exp (I * L * z / 2) / 2 * ((gaussDensity lam u : ℂ)
          * ((Real.exp (L / 2 * u) : ℝ) : ℂ) * ((z - I * u) ^ 2 + (δ : ℂ) ^ 2))
        + Complex.exp (-(I * L * z / 2)) / 2 * ((gaussDensity lam u : ℂ)
          * ((Real.exp (-(L / 2) * u) : ℝ) : ℂ) * ((z - I * u) ^ 2 + (δ : ℂ) ^ 2)) := by
    intro u
    unfold cosDefect
    rw [Complex.cos, Complex.ofReal_exp, Complex.ofReal_exp]
    have e1 : (L : ℂ) * (z - I * u) / 2 * I = I * L * z / 2 + ((L / 2 * u : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    have e2 : -((L : ℂ) * (z - I * u) / 2) * I = -(I * L * z / 2) + ((-(L / 2) * u : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [e1, e2, Complex.exp_add, Complex.exp_add]
    ring
  unfold cosDefectFlow
  rw [show (fun u : ℝ => (gaussDensity lam u : ℂ) * cosDefect δ L (z - I * u)) = _ from funext hpt,
    integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul, v1, v2]
  unfold cosDefectFlowCore
  have hsq : lam * (L / 2) ^ 2 = lam * L ^ 2 / 4 := by ring
  have hsq' : lam * (-(L / 2)) ^ 2 = lam * L ^ 2 / 4 := by ring
  rw [hsq, hsq']
  have e3 : z - I * ((2 * lam * (L / 2) : ℝ) : ℂ) = z - I * (lam * L) := by push_cast; ring
  have e4 : z - I * ((2 * lam * -(L / 2) : ℝ) : ℂ) = z + I * (lam * L) := by push_cast; ring
  push_cast at e3 e4 ⊢
  rw [e3, e4]
  ring

/-- The Hermite–Biehler identity `|Q₋|² − |Q₊|² = 8yλL(x² + y² + λ²L² − c)`. -/
theorem normSq_cosDefectQ_sub (δ L lam : ℝ) (z : ℂ) :
    Complex.normSq ((z + I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam)
      - Complex.normSq ((z - I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam)
      = 8 * z.im * (lam * L) * (z.re ^ 2 + z.im ^ 2 + (lam * L) ^ 2 - (δ ^ 2 - 2 * lam)) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    sq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **Real zeros past the collision.**  If `δ² − 2λ ≤ (λL)²` and `L > 0`, `δ ≠ 0`, every zero of the
closed-form flow is real. -/
theorem im_eq_zero_of_cosDefectFlowCore_eq_zero {δ L lam : ℝ} (hδ : δ ≠ 0) (hL : 0 < L)
    (hlam : 0 ≤ lam) (hcol : δ ^ 2 - 2 * lam ≤ (lam * L) ^ 2) {z : ℂ}
    (hz : cosDefectFlowCore δ L lam z = 0) : z.im = 0 := by
  set P := (z - I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam with hP
  set M := (z + I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam with hM
  have hlam0 : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hcol; simp at hcol; exact hδ (by nlinarith [sq_nonneg δ])
  have hdiff := normSq_cosDefectQ_sub δ L lam z
  rw [← hP, ← hM] at hdiff
  have hbr : 0 ≤ z.re ^ 2 + z.im ^ 2 + (lam * L) ^ 2 - (δ ^ 2 - 2 * lam) := by
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have heq : P * Complex.exp (I * L * z / 2) = -(M * Complex.exp (-(I * L * z / 2))) := by
    unfold cosDefectFlowCore at hz
    rw [← hP, ← hM] at hz
    linear_combination 2 * hz
  have hn := congrArg (fun w => ‖w‖) heq
  simp only [norm_mul, norm_neg, Complex.norm_exp] at hn
  have r1 : (I * L * z / 2).re = -(L * z.im / 2) := by simp [Complex.mul_re]; ring
  have r2 : (-(I * L * z / 2)).re = L * z.im / 2 := by simp [Complex.mul_re]; ring
  rw [r1, r2] at hn
  have hPn : ‖P‖ ^ 2 = Complex.normSq P := by rw [Complex.sq_norm]
  have hMn : ‖M‖ ^ 2 = Complex.normSq M := by rw [Complex.sq_norm]
  have hlamL : 0 < lam * L := mul_pos hlam0 hL
  by_contra hy
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · -- lower half-plane: `‖P‖ ≥ ‖M‖`, `e^{−Ly/2} > e^{Ly/2}`
    have hle : Complex.normSq M ≤ Complex.normSq P := by
      have : 8 * z.im * (lam * L) * (z.re ^ 2 + z.im ^ 2 + (lam * L) ^ 2 - (δ ^ 2 - 2 * lam)) ≤ 0 := by
        have h8 : 8 * z.im * (lam * L) ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonpos_of_nonneg h8 hbr
      linarith
    have hMP : ‖M‖ ≤ ‖P‖ := by
      rw [← hPn, ← hMn] at hle
      nlinarith [norm_nonneg M, norm_nonneg P, sq_nonneg (‖M‖ - ‖P‖)]
    have hexp : Real.exp (L * z.im / 2) < Real.exp (-(L * z.im / 2)) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    have hP0 : ‖P‖ = 0 := by
      by_contra hP0
      have hPp : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hP0)
      have : ‖M‖ * Real.exp (L * z.im / 2) < ‖P‖ * Real.exp (-(L * z.im / 2)) :=
        calc ‖M‖ * Real.exp (L * z.im / 2) ≤ ‖P‖ * Real.exp (L * z.im / 2) :=
              mul_le_mul_of_nonneg_right hMP (Real.exp_pos _).le
          _ < ‖P‖ * Real.exp (-(L * z.im / 2)) := mul_lt_mul_of_pos_left hexp hPp
      linarith
    have hM0 : ‖M‖ = 0 := by
      have := hn; rw [hP0, zero_mul] at this
      have hE := Real.exp_pos (L * z.im / 2)
      rcases mul_eq_zero.mp this.symm with h | h
      · exact h
      · exact absurd h hE.ne'
    have hPz : P = 0 := norm_eq_zero.mp hP0
    have hMz : M = 0 := norm_eq_zero.mp hM0
    have hsub : M - P = 4 * I * (lam * L) * z := by rw [hM, hP]; ring
    rw [hMz, hPz, sub_zero] at hsub
    have hz0 : z = 0 := by
      have h4 : (4 * I * ((lam * L : ℝ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) ?_
        exact_mod_cast hlamL.ne'
      have : (4 * I * ((lam * L : ℝ) : ℂ)) * z = 0 := by push_cast; rw [← hsub]
      exact (mul_eq_zero.mp this).resolve_left h4
    rw [hz0] at hneg; simp at hneg
  · -- upper half-plane: `‖M‖ ≥ ‖P‖`, `e^{Ly/2} > e^{−Ly/2}`
    have hle : Complex.normSq P ≤ Complex.normSq M := by
      have : 0 ≤ 8 * z.im * (lam * L) * (z.re ^ 2 + z.im ^ 2 + (lam * L) ^ 2 - (δ ^ 2 - 2 * lam)) :=
        mul_nonneg (by positivity) hbr
      linarith
    have hPM : ‖P‖ ≤ ‖M‖ := by
      rw [← hPn, ← hMn] at hle
      nlinarith [norm_nonneg M, norm_nonneg P, sq_nonneg (‖M‖ - ‖P‖)]
    have hexp : Real.exp (-(L * z.im / 2)) < Real.exp (L * z.im / 2) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    have hM0 : ‖M‖ = 0 := by
      by_contra hM0
      have hMp : 0 < ‖M‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hM0)
      have : ‖P‖ * Real.exp (-(L * z.im / 2)) < ‖M‖ * Real.exp (L * z.im / 2) :=
        calc ‖P‖ * Real.exp (-(L * z.im / 2)) ≤ ‖M‖ * Real.exp (-(L * z.im / 2)) :=
              mul_le_mul_of_nonneg_right hPM (Real.exp_pos _).le
          _ < ‖M‖ * Real.exp (L * z.im / 2) := mul_lt_mul_of_pos_left hexp hMp
      linarith
    have hP0 : ‖P‖ = 0 := by
      have := hn; rw [hM0, zero_mul] at this
      have hE := Real.exp_pos (-(L * z.im / 2))
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hE.ne'
    have hPz : P = 0 := norm_eq_zero.mp hP0
    have hMz : M = 0 := norm_eq_zero.mp hM0
    have hsub : M - P = 4 * I * (lam * L) * z := by rw [hM, hP]; ring
    rw [hMz, hPz, sub_zero] at hsub
    have hz0 : z = 0 := by
      have h4 : (4 * I * ((lam * L : ℝ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) ?_
        exact_mod_cast hlamL.ne'
      have : (4 * I * ((lam * L : ℝ) : ℂ)) * z = 0 := by push_cast; rw [← hsub]
      exact (mul_eq_zero.mp this).resolve_left h4
    rw [hz0] at hpos; simp at hpos

/-- The flow and its closed-form factor have the same zeros. -/
theorem cosDefectFlow_eq_zero_iff {lam : ℝ} (hlam : 0 < lam) (δ L : ℝ) (z : ℂ) :
    cosDefectFlow δ L lam z = 0 ↔ cosDefectFlowCore δ L lam z = 0 := by
  rw [cosDefectFlow_eq hlam]
  have h : ((Real.exp (lam * L ^ 2 / 4) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  exact ⟨fun hz => (mul_eq_zero.mp hz).resolve_left h, fun hz => by rw [hz, mul_zero]⟩

/-- On the imaginary axis the closed-form factor is real:
`2·core(iY) = (c − (Y − λL)²) e^{−LY/2} + (c − (Y + λL)²) e^{LY/2}`, `c = δ² − 2λ`. -/
theorem cosDefectFlowCore_imag (δ L lam Y : ℝ) :
    cosDefectFlowCore δ L lam (I * Y) = ((((δ ^ 2 - 2 * lam) - (Y - lam * L) ^ 2)
      * Real.exp (-(L * Y / 2)) + ((δ ^ 2 - 2 * lam) - (Y + lam * L) ^ 2) * Real.exp (L * Y / 2)) / 2
        : ℝ) := by
  unfold cosDefectFlowCore
  have e1 : I * (L : ℂ) * (I * Y) / 2 = ((-(L * Y / 2) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have e2 : -(I * (L : ℂ) * (I * Y) / 2) = ((L * Y / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have q1 : (I * (Y : ℂ) - I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam
      = (((δ ^ 2 - 2 * lam) - (Y - lam * L) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have q2 : (I * (Y : ℂ) + I * (lam * L)) ^ 2 + (δ : ℂ) ^ 2 - 2 * lam
      = (((δ ^ 2 - 2 * lam) - (Y + lam * L) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e2, e1, q1, q2, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast
  ring

/-- **A non-real zero before the collision.**  If `0 ≤ λ`, `L > 0` and `(λL)² < δ² − 2λ`, the flow has a
zero on the positive imaginary axis. -/
theorem exists_cosDefectFlowCore_imaginary_zero {δ L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam)
    (hpre : (lam * L) ^ 2 < δ ^ 2 - 2 * lam) :
    ∃ Y : ℝ, 0 < Y ∧ cosDefectFlowCore δ L lam (I * Y) = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = δ ^ 2 - 2 * lam := ⟨_, rfl⟩
  rw [← hc] at hpre
  have hc0 : 0 < c := lt_of_le_of_lt (sq_nonneg _) hpre
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt c := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hc0
  have hss : s ^ 2 = c := by rw [hs]; exact Real.sq_sqrt hc0.le
  have hlamL0 : 0 ≤ lam * L := mul_nonneg hlam hL.le
  have hlt : lam * L < s := by
    by_contra hge
    have : s ^ 2 ≤ (lam * L) ^ 2 := pow_le_pow_left₀ hs0.le (not_lt.mp hge) 2
    linarith
  let h : ℝ → ℝ := fun Y => (c - (Y - lam * L) ^ 2) * Real.exp (-(L * Y / 2))
      + (c - (Y + lam * L) ^ 2) * Real.exp (L * Y / 2)
  have hcont : Continuous h := by fun_prop
  have hY0 : 0 < s - lam * L := by linarith
  have hh0 : 0 ≤ h (s - lam * L) := by
    have e1 : c - (s - lam * L + lam * L) ^ 2 = 0 := by rw [← hss]; ring
    have e2 : c - (s - lam * L - lam * L) ^ 2 = 4 * (lam * L) * (s - lam * L) := by
      rw [← hss]; ring
    show 0 ≤ (c - (s - lam * L - lam * L) ^ 2) * Real.exp (-(L * (s - lam * L) / 2))
      + (c - (s - lam * L + lam * L) ^ 2) * Real.exp (L * (s - lam * L) / 2)
    rw [e1, e2, zero_mul, add_zero]
    have : 0 ≤ 4 * (lam * L) * (s - lam * L) := by positivity
    positivity
  have hh1 : h (2 * s - lam * L + 1) < 0 := by
    have e1 : c - (2 * s - lam * L + 1 + lam * L) ^ 2 = -(3 * s ^ 2 + 4 * s + 1) := by
      rw [← hss]; ring
    have hE : Real.exp (-(L * (2 * s - lam * L + 1) / 2)) ≤ Real.exp (L * (2 * s - lam * L + 1) / 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hfirst : (c - (2 * s - lam * L + 1 - lam * L) ^ 2) * Real.exp (-(L * (2 * s - lam * L + 1) / 2))
        ≤ s ^ 2 * Real.exp (L * (2 * s - lam * L + 1) / 2) := by
      calc (c - (2 * s - lam * L + 1 - lam * L) ^ 2) * Real.exp (-(L * (2 * s - lam * L + 1) / 2))
          ≤ c * Real.exp (-(L * (2 * s - lam * L + 1) / 2)) :=
            mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (2 * s - lam * L + 1 - lam * L)])
              (Real.exp_pos _).le
        _ ≤ c * Real.exp (L * (2 * s - lam * L + 1) / 2) := mul_le_mul_of_nonneg_left hE hc0.le
        _ = s ^ 2 * Real.exp (L * (2 * s - lam * L + 1) / 2) := by rw [hss]
    have hpos := Real.exp_pos (L * (2 * s - lam * L + 1) / 2)
    show (c - (2 * s - lam * L + 1 - lam * L) ^ 2) * Real.exp (-(L * (2 * s - lam * L + 1) / 2))
      + (c - (2 * s - lam * L + 1 + lam * L) ^ 2) * Real.exp (L * (2 * s - lam * L + 1) / 2) < 0
    rw [e1]
    nlinarith
  have hle : s - lam * L ≤ 2 * s - lam * L + 1 := by linarith
  obtain ⟨Y, hYmem, hY⟩ := intermediate_value_Icc' hle hcont.continuousOn ⟨hh1.le, hh0⟩
  refine ⟨Y, lt_of_lt_of_le hY0 hYmem.1, ?_⟩
  rw [cosDefectFlowCore_imag, ← hc]
  have : ((c - (Y - lam * L) ^ 2) * Real.exp (-(L * Y / 2))
      + (c - (Y + lam * L) ^ 2) * Real.exp (L * Y / 2)) = 0 := hY
  rw [this]; simp

/-- **Collision time of the model.**  With `λ = μ/L`: for `μ ≥ δ > 0` every zero of the flow is real;
for `0 < μ < δ` and `L > 2μ/(δ² − μ²)` the flow has a zero on the positive imaginary axis.  So
`L · Λ_model → δ`. -/
theorem cosDefectFlow_collision {δ L μ : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    (δ ≤ μ → ∀ z : ℂ, cosDefectFlow δ L (μ / L) z = 0 → z.im = 0) ∧
      (0 < μ → μ < δ → 2 * μ / (δ ^ 2 - μ ^ 2) < L →
        ∃ Y : ℝ, 0 < Y ∧ cosDefectFlow δ L (μ / L) (I * Y) = 0) := by
  have hμL : μ / L * L = μ := by field_simp
  refine ⟨fun hμ z hz => ?_, fun hμ0 hμδ hLbig => ?_⟩
  · have hμ0 : 0 < μ / L := div_pos (lt_of_lt_of_le hδ hμ) hL
    rw [cosDefectFlow_eq_zero_iff hμ0] at hz
    refine im_eq_zero_of_cosDefectFlowCore_eq_zero hδ.ne' hL hμ0.le ?_ hz
    rw [hμL]
    have : δ ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hδ.le hμ 2
    have : 0 ≤ 2 * (μ / L) := by positivity
    linarith
  · have hd : 0 < δ ^ 2 - μ ^ 2 := by nlinarith
    have hpre : (μ / L * L) ^ 2 < δ ^ 2 - 2 * (μ / L) := by
      rw [hμL]
      have h1 : 2 * μ < L * (δ ^ 2 - μ ^ 2) := by rw [div_lt_iff₀ hd] at hLbig; linarith
      have h2 : 2 * (μ / L) < δ ^ 2 - μ ^ 2 := by
        rw [show 2 * (μ / L) = 2 * μ / L by ring, div_lt_iff₀ hL]; linarith
      linarith
    obtain ⟨Y, hY, hz⟩ := exists_cosDefectFlowCore_imaginary_zero hL (by positivity) hpre
    refine ⟨Y, hY, ?_⟩
    rw [cosDefectFlow_eq_zero_iff (div_pos hμ0 hL)]; exact hz

end

end RHTower.DeBruijn
