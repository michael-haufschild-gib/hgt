import GaloisForLFunctions.RHTower.EvenSectorCosineBochner
import GaloisForLFunctions.HTGeometry.EvenSqrtHolomorphy

/-!
# Consistency of the cosine-shift measures

For an even strip function `Φ` let `ν_Φ` be its cosine-shift measure (`exists_cosineShift_measure`):
`charFun ν_Φ (y) = L(cos(yρ) Φ Φ^#)`, `ρ(z) = (z² + 2)^{1/2}`, where `L` is the even Weil functional
`L(K) = Re(K(i/2) + K(−i/2)) + (1/2π) ∫ Re K · γ − Σ_n (lam_n/√n) (1/π) ∫ Re K(r) cos(r log n) dr`.

**Kernel identity** (`evenWeilDensity_specSq_mul_kernel`).  Let `κ` be continuous with
`|κ(t)| ≤ C e^{−b|t|}`, `b > 5/4`, and `τ(ρ) = ∫ κ(t) cos(tρ) dt`.  Then
`L(Φ Φ^# · τ(ρ)) = ∫ τ dν_Φ`.  Proof: Fubini in each of the three parts of `L`
(`evenPolePart_mul_integral`, `evenArchPart_mul_integral`, `evenPrimePart_mul_integral`; the prime
part needs `∫ |κ(t)| e^{5|t|/4} dt < ∞` and the growth `|lam_n| ≤ C √n log n`), which gives
`∫ κ(t) φ_Φ(t) dt`, and then Fubini against `ν_Φ`.  Every even `τ`, holomorphic, real on the line
and decaying on `|Im ρ| ≤ b`, has this form with `κ = stripTest τ` (`integral_stripTest_mul_cos`).

For a *multiplier* `h` (even, holomorphic and exponentially decaying on `|Im z| ≤ 9/4`, with
`h(z̄) = conj h(z)`) put `h̃(ρ) = h((ρ² − 2)^{1/2})`.  `h̃` is holomorphic on `|Im ρ| ≤ 3/2`
because `h` is even (`differentiableAt_comp_sqrtPrincipal`), and decays exponentially there.

**Theorem** (`cosineShift_measure_mul`).  `ν_{Φ h} = σ_h · ν_Φ`, `σ_h(ρ) = |h̃(ρ)|²`.

Proof.  At the points where `L` reads its argument (`z` real or `z = ±i/2`) `ρ(z)` is real and
`h h^#(z) = σ_h(ρ(z))`.  The kernel identity with the shifted kernel `½(κ(t − y) + κ(t + y))`,
`κ = stripTest(h̃ h̃^#)`, gives `charFun ν_{Φh}(y) = ∫ cos(yρ) σ_h dν_Φ`.  A measure with real
characteristic function is symmetric (`map_neg_eq_of_charFun_im`), so the sine part of
`charFun(σ_h ν_Φ)` vanishes, and the characteristic functions agree.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry

/-! ## The principal square root: real and imaginary parts -/

theorem sq_im_sqrtPrincipal (w : ℂ) : (sqrtPrincipal w).im ^ 2 = (‖w‖ - w.re) / 2 := by
  have h1 := sqrtPrincipal_sq w
  have h2 := norm_sqrtPrincipal w
  set p := sqrtPrincipal w
  have hre : w.re = p.re ^ 2 - p.im ^ 2 := by rw [← h1]; simp [sq]
  have hn : ‖w‖ = p.re ^ 2 + p.im ^ 2 := by
    rw [← h1, norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hre, hn]; ring

theorem sq_re_sqrtPrincipal (w : ℂ) : (sqrtPrincipal w).re ^ 2 = (‖w‖ + w.re) / 2 := by
  have h1 := sqrtPrincipal_sq w
  set p := sqrtPrincipal w
  have hre : w.re = p.re ^ 2 - p.im ^ 2 := by rw [← h1]; simp [sq]
  have hn : ‖w‖ = p.re ^ 2 + p.im ^ 2 := by
    rw [← h1, norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hre, hn]; ring

/-- `|Im (ρ² − 2)^{1/2}|² ≤ (Im ρ)² + 2`. -/
theorem sq_im_sqrtPrincipal_sub_two_le (ρ : ℂ) :
    (sqrtPrincipal (ρ ^ 2 - 2)).im ^ 2 ≤ ρ.im ^ 2 + 2 := by
  rw [sq_im_sqrtPrincipal]
  have hn : ‖ρ ^ 2 - 2‖ ≤ ρ.re ^ 2 + ρ.im ^ 2 + 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
    simp; nlinarith
  have hre : (ρ ^ 2 - 2).re = ρ.re ^ 2 - ρ.im ^ 2 - 2 := by simp [sq]
  rw [hre]; linarith

/-- `|Re (ρ² − 2)^{1/2}| ≥ |Re ρ| − √((Im ρ)² + 2)`. -/
theorem abs_re_sqrtPrincipal_sub_two_ge (ρ : ℂ) :
    |ρ.re| - Real.sqrt (ρ.im ^ 2 + 2) ≤ |(sqrtPrincipal (ρ ^ 2 - 2)).re| := by
  have h := sq_re_sqrtPrincipal (ρ ^ 2 - 2)
  have hre : (ρ ^ 2 - 2).re = ρ.re ^ 2 - ρ.im ^ 2 - 2 := by simp [sq]
  have hn : |(ρ ^ 2 - 2).re| ≤ ‖ρ ^ 2 - 2‖ := Complex.abs_re_le_norm _
  have hsq : ρ.re ^ 2 - ρ.im ^ 2 - 2 ≤ (sqrtPrincipal (ρ ^ 2 - 2)).re ^ 2 := by
    rw [h, hre] at *; rw [hre] at hn
    have := le_abs_self (ρ.re ^ 2 - ρ.im ^ 2 - 2)
    linarith
  set c := Real.sqrt (ρ.im ^ 2 + 2)
  have hc : c ^ 2 = ρ.im ^ 2 + 2 := Real.sq_sqrt (by positivity)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  by_cases hle : |ρ.re| ≤ c
  · linarith [abs_nonneg (sqrtPrincipal (ρ ^ 2 - 2)).re]
  · push Not at hle
    have h1 : (|ρ.re| - c) ^ 2 ≤ (sqrtPrincipal (ρ ^ 2 - 2)).re ^ 2 := by
      have : (|ρ.re| - c) ^ 2 ≤ ρ.re ^ 2 - c ^ 2 := by
        rw [← sq_abs ρ.re]; nlinarith
      linarith
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_pos (by linarith : 0 < |ρ.re| - c)] at h2


/-! ## Multipliers and their `ρ`-lifts -/

/-- A multiplier: even, holomorphic and exponentially decaying on `|Im z| ≤ 9/4`, and
conjugation-symmetric. -/
structure Multiplier (h : ℂ → ℂ) : Prop where
  strip : ∃ ε C : ℝ, 0 < ε ∧ StripDecay h (9 / 4) ε C
  even : ∀ z, h (-z) = h z
  conj_symm : ∀ z, h (conj z) = conj (h z)

/-- The lift `h̃(ρ) = h((ρ² − 2)^{1/2})`. -/
def rhoLift (h : ℂ → ℂ) (ρ : ℂ) : ℂ := h (sqrtPrincipal (ρ ^ 2 - 2))

theorem abs_im_sqrtPrincipal_sub_two_lt {ρ : ℂ} (hρ : |ρ.im| ≤ 3 / 2) :
    |(sqrtPrincipal (ρ ^ 2 - 2)).im| < 9 / 4 := by
  have h := sq_im_sqrtPrincipal_sub_two_le ρ
  have h1 : ρ.im ^ 2 ≤ 9 / 4 := by
    have := sq_abs ρ.im
    nlinarith [abs_nonneg ρ.im]
  exact abs_lt_of_sq_lt_sq (by nlinarith) (by norm_num)

theorem abs_im_sqrtPrincipal_sub_two_le {ρ : ℂ} (hρ : |ρ.im| ≤ 3 / 2) :
    Real.sqrt (ρ.im ^ 2 + 2) ≤ Real.sqrt (17 / 4) := by
  refine Real.sqrt_le_sqrt ?_
  have := sq_abs ρ.im
  nlinarith [abs_nonneg ρ.im]

theorem sqrtPrincipal_eq_or_neg {a b : ℂ} (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  sq_eq_sq_iff_eq_or_eq_neg.mp h

theorem stripDecay_rhoLift {h : ℂ → ℂ} (hh : Multiplier h) :
    ∃ ε C : ℝ, 0 < ε ∧ StripDecay (rhoLift h) (3 / 2) ε C := by
  obtain ⟨ε, C, hε, hs⟩ := hh.strip
  have hC := hs.const_nonneg (by norm_num)
  refine ⟨ε, C * Real.exp (ε * Real.sqrt (17 / 4)), hε, fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · have hd := differentiableAt_comp_sqrtPrincipal hh.even
      (fun z hz => hs.diff z hz.le) (abs_im_sqrtPrincipal_sub_two_lt hρ)
    have hg : DifferentiableAt ℂ (fun ρ : ℂ => ρ ^ 2 - 2) ρ :=
      (differentiableAt_id.pow 2).sub_const 2
    show DifferentiableAt ℂ ((fun v => h (sqrtPrincipal v)) ∘ fun ρ : ℂ => ρ ^ 2 - 2) ρ
    exact hd.comp ρ hg
  · unfold rhoLift
    have hb := hs.bound _ (abs_im_sqrtPrincipal_sub_two_lt hρ).le
    have hre := abs_re_sqrtPrincipal_sub_two_ge ρ
    have hsq := abs_im_sqrtPrincipal_sub_two_le hρ
    refine hb.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith

theorem rhoLift_neg (h : ℂ → ℂ) (ρ : ℂ) : rhoLift h (-ρ) = rhoLift h ρ := by
  unfold rhoLift; rw [neg_sq]

theorem rhoLift_conj {h : ℂ → ℂ} (hh : Multiplier h) (ρ : ℂ) :
    rhoLift h (conj ρ) = conj (rhoLift h ρ) := by
  unfold rhoLift
  have hw : conj ρ ^ 2 - 2 = conj (ρ ^ 2 - 2) := by
    rw [map_sub, map_pow, map_ofNat]
  rw [hw]
  have hsq : sqrtPrincipal (conj (ρ ^ 2 - 2)) ^ 2 = (conj (sqrtPrincipal (ρ ^ 2 - 2))) ^ 2 := by
    rw [sqrtPrincipal_sq, ← map_pow, sqrtPrincipal_sq]
  rcases sqrtPrincipal_eq_or_neg hsq with h1 | h1
  · rw [h1, hh.conj_symm]
  · rw [h1, hh.even, hh.conj_symm]

theorem rhoLift_im_ofReal {h : ℂ → ℂ} (hh : Multiplier h) (ρ : ℝ) : (rhoLift h ρ).im = 0 := by
  have := rhoLift_conj hh ρ
  rw [Complex.conj_ofReal] at this
  exact Complex.conj_eq_iff_im.mp this.symm

/-- Where `ρ(z)` is real the lift recovers `h`: `h̃(ρ(z)) = h(z)` for `z` real or imaginary. -/
theorem rhoLift_rhoC {h : ℂ → ℂ} (hh : Multiplier h) (z : ℂ) : rhoLift h (rhoC z) = h z := by
  unfold rhoLift
  rw [rhoC_sq, add_sub_cancel_right]
  have hsq : sqrtPrincipal (z ^ 2) ^ 2 = z ^ 2 := sqrtPrincipal_sq _
  rcases sqrtPrincipal_eq_or_neg hsq with h1 | h1
  · rw [h1]
  · rw [h1, hh.even]


/-! ## The shifted cosine family of a good density -/

theorem stripDecay_cos_mul (t : ℝ) {K : ℂ → ℂ} {ε C : ℝ} (hs : StripDecay K (5 / 4) ε C) :
    StripDecay (fun z => Complex.cos (t * rhoC z) * K z) (5 / 4) ε
      (Real.exp (|t| * (5 / 4)) * C) := by
  have hC := hs.const_nonneg (by norm_num)
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact ((differentiableAt_rhoC (abs_im_lt_sqrt_two hz)).const_mul (t : ℂ)).ccos.mul
      (hs.diff z hz)
  · rw [norm_mul]
    have h1 : ‖Complex.cos (t * rhoC z)‖ ≤ Real.exp (|t| * (5 / 4)) :=
      (norm_cos_mul_rhoC_le t).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hz (abs_nonneg t)))
    calc ‖Complex.cos (t * rhoC z)‖ * ‖K z‖
        ≤ Real.exp (|t| * (5 / 4)) * (C * Real.exp (-(ε * |z.re|))) :=
          mul_le_mul h1 (hs.bound z hz) (norm_nonneg _) (by positivity)
      _ = Real.exp (|t| * (5 / 4)) * C * Real.exp (-(ε * |z.re|)) := by ring

theorem goodDensity_cos_mul (t : ℝ) {K : ℂ → ℂ} (hK : GoodDensity K) :
    GoodDensity (fun z => Complex.cos (t * rhoC z) * K z) := by
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  refine ⟨⟨ε, _, hε, stripDecay_cos_mul t hs⟩, fun z => ?_, fun r => ?_⟩
  · simp only [rhoC_neg, hK.even]
  · rw [Complex.mul_im, cos_mul_rhoC_ofReal_im, hK.real]; ring

theorem cos_mul_rhoC_ofReal (t r : ℝ) :
    Complex.cos (t * rhoC r) = ((Real.cos (t * Real.sqrt (r ^ 2 + 2)) : ℝ) : ℂ) := by
  rw [rhoC_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_cos]

theorem rhoC_I_div_two : rhoC (I / 2) = ((Real.sqrt (7 / 4) : ℝ) : ℂ) := by
  unfold rhoC
  rw [show (I / 2) ^ 2 + 2 = ((7 / 4 : ℝ) : ℂ) by
      rw [div_pow, Complex.I_sq]; push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by norm_num), Real.sqrt_eq_rpow]

theorem rhoC_neg_I_div_two : rhoC (-I / 2) = ((Real.sqrt (7 / 4) : ℝ) : ℂ) := by
  rw [show -I / 2 = -(I / 2) by ring, rhoC_neg, rhoC_I_div_two]

/-- The pole part `Re(K(i/2) + K(−i/2))` of the even functional. -/
def evenPolePart (K : ℂ → ℂ) : ℝ := (K (I / 2) + K (-I / 2)).re

/-- The archimedean part `∫ Re K · γ` of the even functional. -/
def evenArchPart (K : ℂ → ℂ) : ℝ := ∫ r : ℝ, (K r).re * EF.gammaBracket r

/-- The prime part `Σ_n (lam_n/√n) (1/π) ∫ Re K(r) cos(r log n) dr` of the even functional. -/
def evenPrimePart (lam : ℕ → ℝ) (K : ℂ → ℂ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
    (1 / Real.pi * ∫ r : ℝ, (K r).re * Real.cos (r * Real.log n))

theorem evenWeilDensity_eq_parts (lam : ℕ → ℝ) (K : ℂ → ℂ) :
    evenWeilDensity lam K =
      evenPolePart K + 1 / (2 * Real.pi) * evenArchPart K - evenPrimePart lam K := rfl


/-! ## Fubini inside the even functional -/

theorem integrable_of_exp_bound {κ : ℝ → ℝ} (hκc : Continuous κ) {Cκ b : ℝ} (hb : 0 < b)
    (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) : Integrable κ :=
  ((integrable_exp_neg_rate_abs hb).const_mul Cκ).mono' hκc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hκb t)

theorem integral_kappa_cos_ofReal (κ : ℝ → ℝ) (s : ℝ) :
    ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * (s : ℂ)) =
      ((∫ t : ℝ, κ t * Real.cos (t * s) : ℝ) : ℂ) := by
  refine Eq.trans ?_ integral_ofReal
  congr 1
  funext t
  change _ = ((κ t * Real.cos (t * s) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_mul]

theorem re_cos_mul_ofReal (t r : ℝ) (K : ℂ → ℂ) :
    (Complex.cos (t * rhoC r) * K r).re = Real.cos (t * Real.sqrt (r ^ 2 + 2)) * (K r).re := by
  rw [cos_mul_rhoC_ofReal, Complex.re_ofReal_mul]

theorem evenPolePart_mul_integral (K : ℂ → ℂ) (κ : ℝ → ℝ) :
    evenPolePart (fun z => K z * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z)) =
      ∫ t : ℝ, κ t * evenPolePart (fun z => Complex.cos (t * rhoC z) * K z) := by
  unfold evenPolePart
  simp only [rhoC_I_div_two, rhoC_neg_I_div_two, integral_kappa_cos_ofReal]
  have e : ∀ t : ℝ, κ t * (Complex.cos (t * ((Real.sqrt (7 / 4) : ℝ) : ℂ)) * K (I / 2) +
      Complex.cos (t * ((Real.sqrt (7 / 4) : ℝ) : ℂ)) * K (-I / 2)).re =
      (κ t * Real.cos (t * Real.sqrt (7 / 4))) * (K (I / 2) + K (-I / 2)).re := by
    intro t
    rw [← mul_add, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul]
    ring
  simp_rw [e]
  rw [integral_mul_const, ← add_mul, Complex.re_mul_ofReal]
  ring

theorem integrable_prod_bound {K : ℂ → ℂ} (hK : GoodDensity K) {κ : ℝ → ℝ} (hκc : Continuous κ)
    (hκ : Integrable κ) {P : ℝ → ℝ} (hP : Continuous P) {M : ℝ} (hPb : ∀ r, |P r| ≤ M * (1 + |r|))
    (φ : ℝ → ℝ → ℝ) (hφ : Continuous (Function.uncurry φ)) (hφb : ∀ r t, |φ r t| ≤ 1) :
    Integrable (Function.uncurry fun (r t : ℝ) => κ t * (φ r t * (K r).re * P r))
      (volume.prod volume) := by
  have hint := (hK.integrable_mul hP hPb).norm.mul_prod hκ.norm
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hc : Continuous fun p : ℝ × ℝ => κ p.2 * (φ p.1 p.2 * (K p.1).re * P p.1) := by
      refine (hκc.comp continuous_snd).mul (((hφ.comp (continuous_fst.prodMk continuous_snd)).mul
        ((Complex.continuous_re.comp hK.continuous_ofReal).comp continuous_fst)).mul
          (hP.comp continuous_fst))
    exact hc.aestronglyMeasurable
  · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    have := hφb p.1 p.2
    calc |κ p.2| * (|φ p.1 p.2| * |(K p.1).re| * |P p.1|)
        ≤ |κ p.2| * (1 * |(K p.1).re| * |P p.1|) := by gcongr
      _ = |(K p.1).re| * |P p.1| * |κ p.2| := by ring

theorem evenArchPart_mul_integral {K : ℂ → ℂ} (hK : GoodDensity K) {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκ : Integrable κ) :
    evenArchPart (fun z => K z * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z)) =
      ∫ t : ℝ, κ t * evenArchPart (fun z => Complex.cos (t * rhoC z) * K z) := by
  unfold evenArchPart
  have e1 : ∀ r : ℝ, (K r * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC r)).re *
      EF.gammaBracket r =
      ∫ t : ℝ, κ t * (Real.cos (t * Real.sqrt (r ^ 2 + 2)) * (K r).re * EF.gammaBracket r) := by
    intro r
    simp only [rhoC_ofReal, integral_kappa_cos_ofReal]
    rw [Complex.re_mul_ofReal,
      show ∀ a b c : ℝ, (a * b) * c = b * (a * c) from fun a b c => by ring,
      ← integral_mul_const]
    congr 1; funext t; ring
  have e2 : ∀ t : ℝ, κ t * ∫ r : ℝ, (Complex.cos (t * rhoC r) * K r).re * EF.gammaBracket r =
      ∫ r : ℝ, κ t * (Real.cos (t * Real.sqrt (r ^ 2 + 2)) * (K r).re * EF.gammaBracket r) := by
    intro t
    rw [← integral_const_mul]
    congr 1; funext r; rw [re_cos_mul_ofReal]
  simp_rw [e1, e2]
  refine integral_integral_swap ?_
  exact integrable_prod_bound hK hκc hκ WeilHerglotz.continuous_gammaBracket
    (M := |gammaLogConst| + 2) (fun r => by
      have := abs_abs_gammaBracket_le_linear r; rwa [abs_abs] at this)
    (fun r t => Real.cos (t * Real.sqrt (r ^ 2 + 2))) (by fun_prop)
    (fun r t => Real.abs_cos_le_one _)

theorem abs_primeTerm_cos_mul_le {K : ℂ → ℂ} (hK : GoodDensity K) {ε C : ℝ} (hε : 0 < ε)
    (hs : StripDecay K (5 / 4) ε C) (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |1 / Real.pi * ∫ r : ℝ, (Complex.cos (t * rhoC r) * K r).re * Real.cos (r * Real.log n)| ≤
      2 * (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi)) *
        ((n : ℝ) ^ (-(5 / 4 : ℝ)) * Real.exp (5 / 4 * |t|)) := by
  have h := abs_prime_le_of_strip hε (stripDecay_cos_mul t hs) (goodDensity_cos_mul t hK) hn
  rw [mul_comm |t| (5 / 4 : ℝ)] at h
  refine h.trans (le_of_eq ?_)
  ring

theorem nonneg_of_abs_le_exp {κ : ℝ → ℝ} {Cκ b : ℝ}
    (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) : 0 ≤ Cκ := by
  have := (abs_nonneg (κ 0)).trans (hκb 0)
  simpa using this

/-- **Fubini in the prime part.** -/
theorem evenPrimePart_mul_integral {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K : ℂ → ℂ}
    (hK : GoodDensity K) {κ : ℝ → ℝ} (hκc : Continuous κ) {Cκ b : ℝ} (hb : 5 / 4 < b)
    (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) :
    evenPrimePart lam (fun z => K z * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z)) =
      ∫ t : ℝ, κ t * evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * K z) := by
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  have hC := hs.const_nonneg (by norm_num)
  have hκ : Integrable κ := integrable_of_exp_bound hκc (by linarith) hκb
  have hCκ := nonneg_of_abs_le_exp hκb
  have hCg := growthConst_nonneg hg
  set D := 2 * (C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi)) with hD
  have hD0 : 0 ≤ D := by
    have : 0 ≤ ∫ r : ℝ, Real.exp (-(ε * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
    positivity
  set I₀ := ∫ t : ℝ, Real.exp (-((b - 5 / 4) * |t|)) with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  -- the product integrands
  have hint : ∀ n : ℕ, Integrable (Function.uncurry fun (r t : ℝ) =>
      κ t * (Real.cos (t * Real.sqrt (r ^ 2 + 2)) * (K r).re * Real.cos (r * Real.log n)))
      (volume.prod volume) := fun n =>
    integrable_prod_bound hK hκc hκ (P := fun r => Real.cos (r * Real.log n)) (by fun_prop)
      (M := 1) (fun r => by
        have := Real.abs_cos_le_one (r * Real.log n)
        have := abs_nonneg r
        linarith) (fun r t => Real.cos (t * Real.sqrt (r ^ 2 + 2))) (by fun_prop)
      (fun r t => Real.abs_cos_le_one _)
  have hY : ∀ (n : ℕ) (t : ℝ), κ t * (1 / Real.pi * ∫ r : ℝ,
      (Complex.cos (t * rhoC r) * K r).re * Real.cos (r * Real.log n)) =
      1 / Real.pi * ∫ r : ℝ, κ t * (Real.cos (t * Real.sqrt (r ^ 2 + 2)) * (K r).re *
        Real.cos (r * Real.log n)) := by
    intro n t
    simp_rw [re_cos_mul_ofReal]
    simp only [← integral_const_mul]
    congr 1; funext r; ring
  -- each prime term, by Fubini
  have hterm : ∀ n : ℕ, (1 / Real.pi * ∫ r : ℝ,
      (K r * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC r)).re * Real.cos (r * Real.log n)) =
      ∫ t : ℝ, κ t * (1 / Real.pi * ∫ r : ℝ,
        (Complex.cos (t * rhoC r) * K r).re * Real.cos (r * Real.log n)) := by
    intro n
    have e1 : ∀ r : ℝ, (K r * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC r)).re *
        Real.cos (r * Real.log n) = ∫ t : ℝ, κ t * (Real.cos (t * Real.sqrt (r ^ 2 + 2)) *
          (K r).re * Real.cos (r * Real.log n)) := by
      intro r
      simp only [rhoC_ofReal, integral_kappa_cos_ofReal]
      rw [Complex.re_mul_ofReal,
        show ∀ a b c : ℝ, (a * b) * c = b * (a * c) from fun a b c => by ring,
        ← integral_mul_const]
      congr 1; funext t; ring
    simp_rw [e1, hY]
    rw [integral_integral_swap (hint n), integral_const_mul]
  -- integrability and size of each term
  set F : ℕ → ℝ → ℝ := fun n t => (if 2 ≤ n then lam n / Real.sqrt n else 0) *
    (κ t * (1 / Real.pi * ∫ r : ℝ,
      (Complex.cos (t * rhoC r) * K r).re * Real.cos (r * Real.log n))) with hF
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    refine Integrable.const_mul ?_ _
    have := ((hint n).integral_prod_right).const_mul (1 / Real.pi)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hY]
  have hFle : ∀ n t, ‖F n t‖ ≤ Cg * (1 + Real.log n) * Cκ * D *
      ((n : ℝ) ^ (-(5 / 4 : ℝ)) * Real.exp (-((b - 5 / 4) * |t|))) := by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    rw [Real.norm_eq_abs, hF, abs_mul, abs_mul]
    have h1 := abs_weight_le hg n
    have h2 := hκb t
    have h3 := abs_primeTerm_cos_mul_le hK hε hs t hn
    have he : Real.exp (-(b * |t|)) * Real.exp (5 / 4 * |t|) =
        Real.exp (-((b - 5 / 4) * |t|)) := by rw [← Real.exp_add]; ring_nf
    calc |(if 2 ≤ n then lam n / Real.sqrt n else 0)| * (|κ t| *
          |1 / Real.pi * ∫ r : ℝ, (Complex.cos (t * rhoC r) * K r).re *
            Real.cos (r * Real.log n)|)
        ≤ (Cg * (1 + Real.log n)) * ((Cκ * Real.exp (-(b * |t|))) *
          (D * ((n : ℝ) ^ (-(5 / 4 : ℝ)) * Real.exp (5 / 4 * |t|)))) := by
          have := Real.log_natCast_nonneg n
          gcongr
      _ = Cg * (1 + Real.log n) * Cκ * D * ((n : ℝ) ^ (-(5 / 4 : ℝ)) *
          (Real.exp (-(b * |t|)) * Real.exp (5 / 4 * |t|))) := by ring
      _ = _ := by rw [he]
  have hsum : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => ?_) (((summable_one_add_log_mul_rpow (b₁ := 5 / 4) (by norm_num)).mul_left
        (Cg * Cκ * D * I₀)))
    have hexp : Integrable fun t : ℝ => Real.exp (-((b - 5 / 4) * |t|)) :=
      integrable_exp_neg_rate_abs (by linarith)
    calc ∫ t : ℝ, ‖F n t‖ ≤ ∫ t : ℝ, Cg * (1 + Real.log n) * Cκ * D *
          ((n : ℝ) ^ (-(5 / 4 : ℝ)) * Real.exp (-((b - 5 / 4) * |t|))) :=
          integral_mono (hFint n).norm ((hexp.const_mul _).const_mul _) (hFle n)
      _ = Cg * Cκ * D * I₀ * ((1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by
          rw [integral_const_mul, integral_const_mul]; ring
  unfold evenPrimePart
  simp_rw [hterm]
  have e2 : ∀ n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) * ∫ t : ℝ, κ t *
      (1 / Real.pi * ∫ r : ℝ, (Complex.cos (t * rhoC r) * K r).re * Real.cos (r * Real.log n)) =
      ∫ t : ℝ, F n t := fun n => by rw [← integral_const_mul]
  simp_rw [e2]
  rw [integral_tsum_of_summable_integral_norm hFint hsum]
  congr 1; funext t
  rw [← tsum_mul_left]
  congr 1; funext n
  simp only [hF]
  ring


/-! ## The kernel identity against the cosine-shift measure -/

theorem integrable_cexp_mul_I (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun ρ : ℝ => cexp ((t : ℂ) * ρ * I)) ν := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun ρ => ?_)
  rw [show (t : ℂ) * ρ * I = ((t * ρ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem re_charFun_eq_integral_cos_of_finite (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    (charFun ν t).re = ∫ ρ, Real.cos (t * ρ) ∂ν := by
  rw [charFun_apply_real]
  have h := integral_re (integrable_cexp_mul_I ν t)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  congr 1; funext ρ
  rw [show (t : ℂ) * ρ * I = ((t * ρ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

theorem integrable_mul_cos_of_integrable {κ : ℝ → ℝ} (hκc : Continuous κ) (hκ : Integrable κ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable fun t => κ t * Real.cos (g t) :=
  hκ.norm.mono' (by fun_prop) (Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have := Real.abs_cos_le_one (g t)
    have := abs_nonneg (κ t)
    nlinarith)

theorem abs_cosineShiftFn_le {lam : ℕ → ℝ} {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ y, charFun ν y = (cosineShiftFn lam Φ y : ℂ)) (t : ℝ) :
    |cosineShiftFn lam Φ t| ≤ ν.real univ := by
  have h : cosineShiftFn lam Φ t = ∫ ρ, Real.cos (t * ρ) ∂ν := by
    rw [← re_charFun_eq_integral_cos_of_finite, hν, Complex.ofReal_re]
  rw [h]
  calc |∫ ρ, Real.cos (t * ρ) ∂ν| ≤ ∫ _ρ, (1 : ℝ) ∂ν := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (integrable_const 1) (Eventually.of_forall fun ρ => ?_)
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    _ = ν.real univ := by simp

/-- **The kernel identity.**  If `τ(ρ) = ∫ κ(t) cos(tρ) dt` with `|κ(t)| ≤ C e^{−b|t|}`,
`b > 5/4`, then `L(Φ Φ^# τ(ρ)) = ∫ τ dν_Φ`. -/
theorem evenWeilDensity_specSq_mul_kernel {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ y, charFun ν y = (cosineShiftFn lam Φ y : ℂ)) {κ : ℝ → ℝ} (hκc : Continuous κ)
    {Cκ b : ℝ} (hb : 5 / 4 < b) (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) :
    evenWeilDensity lam (fun z => specSq Φ z * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z)) =
      ∫ ρ, (∫ t : ℝ, κ t * Real.cos (t * ρ)) ∂ν := by
  have hK := goodDensity_specSq hΦ
  have hκ : Integrable κ := integrable_of_exp_bound hκc (by linarith) hκb
  set P : ℝ → ℝ := fun t => evenPolePart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) with hP
  set A : ℝ → ℝ := fun t => evenArchPart (fun z => Complex.cos (t * rhoC z) * specSq Φ z) with hA
  set Q : ℝ → ℝ := fun t => evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * specSq Φ z)
    with hQ
  have hsplit : ∀ t, cosineShiftFn lam Φ t = P t + 1 / (2 * Real.pi) * A t - Q t :=
    fun t => rfl
  -- integrability of the three parts against `κ`
  have hPe : ∀ t, P t = Real.cos (t * Real.sqrt (7 / 4)) *
      (specSq Φ (I / 2) + specSq Φ (-I / 2)).re := fun t => by
    simp only [hP, evenPolePart, rhoC_I_div_two, rhoC_neg_I_div_two]
    rw [← mul_add, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul]
  have hPi : Integrable fun t => κ t * P t := by
    simp_rw [hPe, ← mul_assoc]
    exact (integrable_mul_cos_of_integrable hκc hκ _ (by fun_prop)).mul_const _
  have hAi : Integrable fun t => κ t * A t := by
    have hint := integrable_prod_bound hK hκc hκ WeilHerglotz.continuous_gammaBracket
      (M := |gammaLogConst| + 2) (fun r => by
        have := abs_abs_gammaBracket_le_linear r; rwa [abs_abs] at this)
      (fun r t => Real.cos (t * Real.sqrt (r ^ 2 + 2))) (by fun_prop)
      (fun r t => Real.abs_cos_le_one _)
    refine hint.integral_prod_right.congr (Eventually.of_forall fun t => ?_)
    simp only [Function.uncurry_apply_pair, hA, evenArchPart]
    rw [← integral_const_mul]
    congr 1; funext r
    rw [re_cos_mul_ofReal]
  have hφi : Integrable fun t => κ t * cosineShiftFn lam Φ t :=
    (hκ.norm.mul_const (ν.real univ)).mono'
      ((hκc.mul (continuous_cosineShiftFn hg hΦ)).aestronglyMeasurable)
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (abs_cosineShiftFn_le hν t) (abs_nonneg _))
  have hQi : Integrable fun t => κ t * Q t := by
    have := (hPi.add (hAi.const_mul (1 / (2 * Real.pi)))).sub hφi
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hsplit]
    ring
  -- the measure side
  have hφ : ∀ t, cosineShiftFn lam Φ t = ∫ ρ, Real.cos (t * ρ) ∂ν := fun t => by
    rw [← re_charFun_eq_integral_cos_of_finite, hν, Complex.ofReal_re]
  have hswap : ∫ ρ, (∫ t : ℝ, κ t * Real.cos (t * ρ)) ∂ν =
      ∫ t : ℝ, κ t * cosineShiftFn lam Φ t := by
    have hint : Integrable (Function.uncurry fun (ρ t : ℝ) => κ t * Real.cos (t * ρ))
        (ν.prod volume) := by
      refine ((integrable_const (1 : ℝ)).mul_prod hκ.norm).mono'
        (by unfold Function.uncurry; fun_prop) (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, one_mul]
      have := Real.abs_cos_le_one (p.2 * p.1)
      have := abs_nonneg (κ p.2)
      nlinarith
    rw [integral_integral_swap hint]
    congr 1; funext t
    rw [hφ, integral_const_mul]
  rw [hswap, evenWeilDensity_eq_parts, evenPolePart_mul_integral,
    evenArchPart_mul_integral hK hκc hκ, evenPrimePart_mul_integral hg hK hκc hb hκb]
  simp_rw [hsplit]
  have e : ∀ t, κ t * (P t + 1 / (2 * Real.pi) * A t - Q t) =
      κ t * P t + 1 / (2 * Real.pi) * (κ t * A t) - κ t * Q t := fun t => by ring
  simp_rw [e]
  have h1 : Integrable fun t => κ t * P t + 1 / (2 * Real.pi) * (κ t * A t) :=
    hPi.add (hAi.const_mul _)
  rw [integral_sub h1 hQi, integral_add hPi (hAi.const_mul _), integral_const_mul]


/-! ## Cosine form of the strip inversion and the shifted kernel -/

theorem abs_stripTest_le {τ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hτ : StripDecay τ b ε C) (t : ℝ) :
    |stripTest τ t| ≤
      C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) * Real.exp (-(b * |t|)) :=
  (Complex.abs_re_le_norm _).trans (norm_stripInvFT_le hb hε hτ t)

/-- `∫ κ(t) cos(ts) dt = τ(s)` for `κ = stripTest τ`, `τ` even and real on the line. -/
theorem integral_stripTest_mul_cos {τ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hτ : StripDecay τ b ε C) (heven : ∀ z, τ (-z) = τ z) (hreal : ∀ r : ℝ, (τ r).im = 0)
    (s : ℝ) : ∫ t : ℝ, stripTest τ t * Real.cos (t * s) = (τ s).re := by
  have hsym : ∀ r : ℝ, τ (-(r : ℂ)) = conj (τ r) := fun r => by
    rw [heven, Complex.conj_eq_iff_im.mpr (hreal r)]
  have hκ : Integrable (stripTest τ) :=
    integrable_of_exp_bound (continuous_stripTest hb.le hε hτ) hb (abs_stripTest_le hb.le hε hτ)
  have hint : Integrable fun t : ℝ => (stripTest τ t : ℂ) * cexp (I * s * t) := by
    refine hκ.norm.mono' (by
      have := continuous_stripTest hb.le hε hτ
      fun_prop) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real,
      show I * (s : ℂ) * (t : ℂ) = ((s * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have h := paperFT_stripTest_ofReal hb hε hτ hsym s
  rw [← h]
  unfold Zeta23.paperFT
  have h2 := integral_re hint
  simp only [RCLike.re_to_complex] at h2
  rw [← h2]
  congr 1; funext t
  rw [show I * (s : ℂ) * (t : ℂ) = ((t * s : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The shifted kernel `½(κ(t − y) + κ(t + y))`. -/
def cosShiftKernel (κ : ℝ → ℝ) (y t : ℝ) : ℝ := (κ (t - y) + κ (t + y)) / 2

theorem continuous_cosShiftKernel {κ : ℝ → ℝ} (hκc : Continuous κ) (y : ℝ) :
    Continuous (cosShiftKernel κ y) := by
  unfold cosShiftKernel; fun_prop

theorem abs_cosShiftKernel_le {κ : ℝ → ℝ} {Cκ b : ℝ} (hb : 0 ≤ b)
    (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) (y t : ℝ) :
    |cosShiftKernel κ y t| ≤ Cκ * Real.exp (b * |y|) * Real.exp (-(b * |t|)) := by
  have hCκ := nonneg_of_abs_le_exp hκb
  have h1 : ∀ u, Real.exp (-(b * |t + u|)) ≤ Real.exp (b * |u|) * Real.exp (-(b * |t|)) := by
    intro u
    rw [← Real.exp_add, Real.exp_le_exp]
    have h2 : |t| ≤ |t + u| + |u| := by
      calc |t| = |(t + u) + (-u)| := by ring_nf
        _ ≤ |t + u| + |-u| := abs_add_le _ _
        _ = |t + u| + |u| := by rw [abs_neg]
    nlinarith
  unfold cosShiftKernel
  rw [abs_div, abs_two]
  have f1 := h1 (-y)
  rw [← sub_eq_add_neg, abs_neg] at f1
  have f2 := h1 y
  calc |κ (t - y) + κ (t + y)| / 2 ≤ (|κ (t - y)| + |κ (t + y)|) / 2 := by
        gcongr; exact abs_add_le _ _
    _ ≤ (Cκ * (Real.exp (b * |y|) * Real.exp (-(b * |t|))) +
        Cκ * (Real.exp (b * |y|) * Real.exp (-(b * |t|)))) / 2 := by
        gcongr
        · exact (hκb _).trans (mul_le_mul_of_nonneg_left f1 hCκ)
        · exact (hκb _).trans (mul_le_mul_of_nonneg_left f2 hCκ)
    _ = _ := by ring

theorem integral_cosShiftKernel_mul_cos {κ : ℝ → ℝ} (hκc : Continuous κ) (hκ : Integrable κ)
    (y s : ℝ) :
    ∫ t : ℝ, cosShiftKernel κ y t * Real.cos (t * s) =
      Real.cos (y * s) * ∫ t : ℝ, κ t * Real.cos (t * s) := by
  have hi : ∀ c : ℝ, Integrable fun t => κ t * Real.cos ((t + c) * s) := fun c =>
    integrable_mul_cos_of_integrable hκc hκ _ (by fun_prop)
  have e1 : ∫ t : ℝ, κ (t - y) * Real.cos (t * s) = ∫ t : ℝ, κ t * Real.cos ((t + y) * s) := by
    rw [← integral_sub_right_eq_self (fun t => κ t * Real.cos ((t + y) * s)) y]
    congr 1; funext t; simp
  have e2 : ∫ t : ℝ, κ (t + y) * Real.cos (t * s) =
      ∫ t : ℝ, κ t * Real.cos ((t + -y) * s) := by
    rw [← integral_add_right_eq_self (fun t => κ t * Real.cos ((t + -y) * s)) y]
    congr 1; funext t; simp
  have hs1 : Integrable fun t => κ (t - y) * Real.cos (t * s) :=
    integrable_mul_cos_of_integrable (hκc.comp (by fun_prop)) (hκ.comp_sub_right y) _
      (by fun_prop)
  have hs2 : Integrable fun t => κ (t + y) * Real.cos (t * s) :=
    integrable_mul_cos_of_integrable (hκc.comp (by fun_prop)) (hκ.comp_add_right y) _
      (by fun_prop)
  unfold cosShiftKernel
  have e3 : ∀ t, (κ (t - y) + κ (t + y)) / 2 * Real.cos (t * s) =
      (κ (t - y) * Real.cos (t * s) + κ (t + y) * Real.cos (t * s)) / 2 := fun t => by ring
  simp_rw [e3]
  rw [integral_div, integral_add hs1 hs2, e1, e2, ← integral_add (hi y) (hi (-y)),
    ← integral_const_mul, ← integral_div]
  congr 1; funext t
  rw [show (t + y) * s = t * s + y * s by ring, show (t + -y) * s = t * s - y * s by ring,
    Real.cos_add, Real.cos_sub]
  ring


/-! ## Real characteristic functions -/

theorem map_neg_eq_of_charFun_im {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : ∀ t, (charFun ν t).im = 0) : ν.map (fun x => -1 * x) = ν := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_mul, neg_one_mul, charFun_neg, Complex.conj_eq_iff_im.mpr (h t)]

/-- A measure with real characteristic function integrates `sin(yρ) g(ρ)` to `0`, `g` even. -/
theorem integral_sin_mul_eq_zero {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : ∀ t, (charFun ν t).im = 0) {g : ℝ → ℝ} (hgc : Continuous g) (hg : ∀ ρ, g (-ρ) = g ρ)
    (y : ℝ) : ∫ ρ, Real.sin (y * ρ) * g ρ ∂ν = 0 := by
  have hm := map_neg_eq_of_charFun_im h
  have e : ∫ ρ, Real.sin (y * ρ) * g ρ ∂ν = -∫ ρ, Real.sin (y * ρ) * g ρ ∂ν := by
    conv_lhs => rw [← hm]
    rw [integral_map (by fun_prop) (by fun_prop), ← integral_neg]
    congr 1; funext ρ
    rw [show y * (-1 * ρ) = -(y * ρ) by ring, Real.sin_neg, neg_one_mul, hg]
    ring
  linarith


/-! ## Consistency -/

theorem Multiplier.real {h : ℂ → ℂ} (hh : Multiplier h) (r : ℝ) : (h r).im = 0 := by
  have := hh.conj_symm r
  rw [Complex.conj_ofReal] at this
  exact Complex.conj_eq_iff_im.mp this.symm

theorem Multiplier.evenStrip {h : ℂ → ℂ} (hh : Multiplier h) : EvenStrip h := by
  obtain ⟨ε, C, hε, hs⟩ := hh.strip
  exact ⟨⟨ε, C, hε, fun z hz => hs.diff z (by linarith), fun z hz => hs.bound z (by linarith)⟩,
    hh.even, hh.real⟩

theorem EvenStrip.mul_multiplier {Φ h : ℂ → ℂ} (hΦ : EvenStrip Φ) (hh : Multiplier h) :
    EvenStrip fun z => Φ z * h z := by
  obtain ⟨ε₁, C₁, hε₁, h₁⟩ := hΦ.strip
  obtain ⟨ε₂, C₂, hε₂, h₂⟩ := hh.evenStrip.strip
  have hC₁ := h₁.const_nonneg (by norm_num)
  refine ⟨⟨ε₁ + ε₂, C₁ * C₂, by linarith, fun z hz => (h₁.diff z hz).mul (h₂.diff z hz),
    fun z hz => ?_⟩, fun z => by rw [hΦ.even, hh.even], fun r => ?_⟩
  · rw [norm_mul]
    calc ‖Φ z‖ * ‖h z‖ ≤ (C₁ * Real.exp (-(ε₁ * |z.re|))) * (C₂ * Real.exp (-(ε₂ * |z.re|))) :=
          mul_le_mul (h₁.bound z hz) (h₂.bound z hz) (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * Real.exp (-((ε₁ + ε₂) * |z.re|)) := by
          rw [show C₁ * C₂ * Real.exp (-((ε₁ + ε₂) * |z.re|)) = C₁ * C₂ *
            (Real.exp (-(ε₁ * |z.re|)) * Real.exp (-(ε₂ * |z.re|))) by
              rw [← Real.exp_add]; ring_nf]
          ring
  · rw [Complex.mul_im, hΦ.real, hh.real]; ring

theorem specSq_mul (Φ h : ℂ → ℂ) (z : ℂ) :
    specSq (fun w => Φ w * h w) z = specSq Φ z * specSq h z := by
  unfold specSq; rw [map_mul]; ring

/-- The spectral square of the lift, `σ_h = h̃ h̃^#`, as a strip function in `ρ`. -/
theorem stripDecay_specSq_rhoLift {h : ℂ → ℂ} (hh : Multiplier h) :
    ∃ ε C : ℝ, 0 < ε ∧ StripDecay (specSq (rhoLift h)) (3 / 2) ε C := by
  obtain ⟨ε, C, hε, hs⟩ := stripDecay_rhoLift hh
  exact ⟨2 * ε, C ^ 2, by linarith, fun z hz => differentiableAt_specSq hs hz,
    fun z hz => norm_specSq_le hs hz⟩

theorem specSq_rhoLift_re (h : ℂ → ℂ) (s : ℝ) :
    (specSq (rhoLift h) s).re = ‖rhoLift h s‖ ^ 2 := specSq_re_ofReal _ s

/-- At a node `z` (real, or `±i/2`) where `ρ(z) = s` is real, the cosine shift of `Φ h` is the
cosine shift of `Φ` against the kernel of `σ_h`. -/
theorem rhoCosShift_mul_eq_kernel {Φ h : ℂ → ℂ} (hh : Multiplier h) {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκ : Integrable κ)
    (hκs : ∀ s : ℝ, ∫ t : ℝ, κ t * Real.cos (t * s) = ‖rhoLift h s‖ ^ 2) (y : ℝ) {z : ℂ}
    {s : ℝ} (hzs : rhoC z = s) (hsq : specSq h z = ((‖h z‖ ^ 2 : ℝ) : ℂ)) :
    rhoCosShift y (fun w => Φ w * h w) z =
      specSq Φ z * ∫ t : ℝ, (cosShiftKernel κ y t : ℂ) * Complex.cos (t * rhoC z) := by
  have hl : rhoLift h s = h z := by rw [← hzs, rhoLift_rhoC hh]
  unfold rhoCosShift
  rw [specSq_mul, hsq, hzs, integral_kappa_cos_ofReal, integral_cosShiftKernel_mul_cos hκc hκ,
    hκs, hl, ← Complex.ofReal_mul, ← Complex.ofReal_cos]
  push_cast
  ring

theorem specSq_ofReal_eq (h : ℂ → ℂ) (r : ℝ) : specSq h r = ((‖h r‖ ^ 2 : ℝ) : ℂ) := by
  unfold specSq
  rw [Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem specSq_I_div_two_eq {h : ℂ → ℂ} (heven : ∀ z, h (-z) = h z) :
    specSq h (I / 2) = ((‖h (I / 2)‖ ^ 2 : ℝ) : ℂ) := by
  unfold specSq
  rw [show conj (I / 2) = -(I / 2) by rw [map_div₀, Complex.conj_I, map_ofNat]; ring, heven,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem specSq_neg_I_div_two_eq {h : ℂ → ℂ} (heven : ∀ z, h (-z) = h z) :
    specSq h (-I / 2) = ((‖h (-I / 2)‖ ^ 2 : ℝ) : ℂ) := by
  unfold specSq
  rw [show conj (-I / 2) = -(-I / 2) by
      rw [map_div₀, map_neg, Complex.conj_I, map_ofNat]; ring, heven,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Consistency of the cosine-shift measures.**  For an even strip function `Φ` and a multiplier
`h`, the cosine-shift measure of `Φ h` is `σ_h ν_Φ`, `σ_h(ρ) = |h((ρ² − 2)^{1/2})|²`. -/
theorem cosineShift_measure_mul {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ h : ℂ → ℂ}
    (hΦ : EvenStrip Φ) (hh : Multiplier h) {ν μ : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (hν : ∀ y, charFun ν y = (cosineShiftFn lam Φ y : ℂ))
    (hμ : ∀ y, charFun μ y = (cosineShiftFn lam (fun z => Φ z * h z) y : ℂ)) :
    μ = ν.withDensity fun ρ => ENNReal.ofReal (‖rhoLift h ρ‖ ^ 2) := by
  obtain ⟨ε, C, hε, hs⟩ := stripDecay_specSq_rhoLift hh
  have hτe : ∀ z, specSq (rhoLift h) (-z) = specSq (rhoLift h) z :=
    specSq_neg_of_even (rhoLift_neg h)
  set κ := stripTest (specSq (rhoLift h)) with hκdef
  have hκc : Continuous κ := continuous_stripTest (by norm_num) hε hs
  set Cκ := C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) with hCκ
  have hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(3 / 2 * |t|)) := abs_stripTest_le (by norm_num) hε hs
  have hκ : Integrable κ := integrable_of_exp_bound hκc (by norm_num) hκb
  have hκs : ∀ s : ℝ, ∫ t : ℝ, κ t * Real.cos (t * s) = ‖rhoLift h s‖ ^ 2 := fun s => by
    rw [integral_stripTest_mul_cos (by norm_num) hε hs hτe (fun r => specSq_im_ofReal r),
      specSq_rhoLift_re]
  -- the density
  set σ : ℝ → ℝ := fun ρ => ‖rhoLift h ρ‖ ^ 2 with hσ
  show μ = ν.withDensity fun ρ => ENNReal.ofReal (σ ρ)
  have hσc : Continuous σ := by
    have := continuous_ofReal_comp_of_stripDecay (stripDecay_rhoLift hh).choose_spec.choose_spec.2
      (by norm_num)
    exact this.norm.pow 2
  obtain ⟨ε₁, C₁, hε₁, hs₁⟩ := stripDecay_rhoLift hh
  have hC₁ := hs₁.const_nonneg (by norm_num)
  have hσb : ∀ ρ : ℝ, σ ρ ≤ C₁ ^ 2 := fun ρ => by
    have hb := hs₁.bound ρ (by norm_num)
    have : ‖rhoLift h ρ‖ ≤ C₁ :=
      hb.trans (mul_le_of_le_one_right hC₁ (Real.exp_le_one_iff.mpr (by
        have := abs_nonneg (ρ : ℂ).re; nlinarith)))
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hσi : Integrable σ ν :=
    (integrable_const (C₁ ^ 2)).mono' hσc.aestronglyMeasurable (Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hσb ρ)
  haveI : IsFiniteMeasure (ν.withDensity fun ρ => ENNReal.ofReal (σ ρ)) :=
    isFiniteMeasure_withDensity_ofReal hσi.hasFiniteIntegral
  refine Measure.ext_of_charFun (funext fun y => ?_)
  rw [hμ]
  -- the left side through the kernel identity
  have hL : cosineShiftFn lam (fun z => Φ z * h z) y = ∫ ρ, Real.cos (y * ρ) * σ ρ ∂ν := by
    have hshift := evenWeilDensity_specSq_mul_kernel hg hΦ hν (continuous_cosShiftKernel hκc y)
      (by norm_num : (5 / 4 : ℝ) < 3 / 2) (abs_cosShiftKernel_le (by norm_num) hκb y)
    unfold cosineShiftFn
    rw [evenWeilDensity_congr (K₂ := fun z => specSq Φ z * ∫ t : ℝ, (cosShiftKernel κ y t : ℂ) *
        Complex.cos (t * rhoC z))
      (rhoCosShift_mul_eq_kernel hh hκc hκ hκs y (rhoC_I_div_two) (specSq_I_div_two_eq hh.even))
      (rhoCosShift_mul_eq_kernel hh hκc hκ hκs y (rhoC_neg_I_div_two)
        (specSq_neg_I_div_two_eq hh.even))
      (fun r => rhoCosShift_mul_eq_kernel hh hκc hκ hκs y (rhoC_ofReal r) (specSq_ofReal_eq h r)),
      hshift]
    congr 1; funext ρ
    rw [integral_cosShiftKernel_mul_cos hκc hκ, hκs]
  -- the right side
  have hreal : ∀ t, (charFun ν t).im = 0 := fun t => by rw [hν, Complex.ofReal_im]
  have hσe : ∀ ρ, σ (-ρ) = σ ρ := fun ρ => by
    simp only [hσ]
    rw [Complex.ofReal_neg, rhoLift_neg]
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul
    hσc.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), hL]
  have hint : Integrable (fun ρ : ℝ => (σ ρ : ℂ) * cexp ((y : ℂ) * ρ * I)) ν := by
    refine (hσi.norm).mono' (by fun_prop) (Eventually.of_forall fun ρ => ?_)
    rw [norm_mul, Complex.norm_real,
      show (y : ℂ) * ρ * I = ((y * ρ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have e1 : ∀ ρ, (ENNReal.ofReal (σ ρ)).toReal • cexp ((y : ℂ) * ρ * I) =
      (σ ρ : ℂ) * cexp ((y : ℂ) * ρ * I) := fun ρ => by
    rw [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  simp_rw [e1]
  apply Complex.ext
  · have h2 := integral_re hint
    simp only [RCLike.re_to_complex] at h2
    rw [← h2, Complex.ofReal_re]
    congr 1; funext ρ
    rw [show (y : ℂ) * ρ * I = ((y * ρ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    ring
  · have h2 := integral_im hint
    simp only [RCLike.im_to_complex] at h2
    rw [← h2, Complex.ofReal_im]
    have e2 : ∀ ρ : ℝ, ((σ ρ : ℂ) * cexp ((y : ℂ) * ρ * I)).im = Real.sin (y * ρ) * σ ρ :=
      fun ρ => by
        rw [show (y : ℂ) * ρ * I = ((y * ρ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
        ring
    simp_rw [e2]
    exact (integral_sin_mul_eq_zero hreal hσc hσe y).symm

end RHTower.EvenSector

end
