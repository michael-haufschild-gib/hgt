import GaloisForLFunctions.RHTower.ThetaGroupHauptmodulForms
import GaloisForLFunctions.RHTower.ModularAxisSourceTransform
import GaloisForLFunctions.HTGeometry.BallLogarithm
import GaloisForLFunctions.Bottcher.QuarticCusp

/-!
# A holomorphic logarithm of the `Γ_θ` Hauptmodul on the upper half-plane

`h = θ₂⁴θ₄⁴/θ₃⁸` has no zeros on the upper half-plane, which is simply connected, so it has a
holomorphic logarithm there.  We transport the disc logarithm through the Cayley chart and normalize
it to be real at `i`.  Two holomorphic logarithms of the same function on a preconnected open set
differ by a constant; this gives

* `log h(-1/τ) = log h(τ)` (the `S`-invariance of `h`),
* `log h(-τ̄) = conj (log h(τ))` (real Fourier coefficients),

hence `log h` is real on the imaginary axis and on the unit circle.  Near the pole cusp `1` the
logarithm is `iπ - 8 log 2 - 2πiv + Log Q(v)` exactly, with `Q → 1`: the unit circle, where `h > 0`,
fixes the branch.  Real powers `h^s = exp(s log h)` are then holomorphic with `|h^s| = |h|^s`.
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

open Bottcher

/-! ## The Cayley chart and logarithms on the upper half-plane -/

/-- Cayley map from the upper half-plane to the unit disc. -/
def cayleyToDisc (τ : ℂ) : ℂ := (τ - I) / (τ + I)

/-- Its inverse, from the unit disc to the upper half-plane. -/
def cayleyFromDisc (z : ℂ) : ℂ := I * (1 + z) / (1 - z)

theorem add_I_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : τ + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem cayleyToDisc_mem {τ : ℂ} (hτ : 0 < τ.im) : cayleyToDisc τ ∈ Metric.ball (0 : ℂ) 1 := by
  have hne := add_I_ne_zero_of_im_pos hτ
  rw [Metric.mem_ball, dist_zero_right, cayleyToDisc, norm_div,
    div_lt_one (norm_pos_iff.mpr hne)]
  have h1 : ‖τ - I‖ ^ 2 < ‖τ + I‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

theorem one_sub_ne_zero_of_mem_ball {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, Metric.mem_ball, dist_zero_right, norm_one] at hz
  exact lt_irrefl _ hz

theorem cayleyFromDisc_im_pos {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    0 < (cayleyFromDisc z).im := by
  have hne := one_sub_ne_zero_of_mem_ball hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hsq : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg z]
  have hN : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hne
  have e : (cayleyFromDisc z).im = (1 - z.re ^ 2 - z.im ^ 2) / Complex.normSq (1 - z) := by
    rw [cayleyFromDisc, mul_div_assoc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_add, Complex.div_re]
    simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
      Complex.sub_im]
    field_simp
    ring
  rw [e]
  exact div_pos (by linarith) hN

theorem cayleyFromDisc_cayleyToDisc {τ : ℂ} (hτ : 0 < τ.im) :
    cayleyFromDisc (cayleyToDisc τ) = τ := by
  have hne := add_I_ne_zero_of_im_pos hτ
  unfold cayleyFromDisc cayleyToDisc
  have h2 : 1 - (τ - I) / (τ + I) = 2 * I / (τ + I) := by field_simp; ring
  have h1 : 1 + (τ - I) / (τ + I) = 2 * τ / (τ + I) := by field_simp; ring
  rw [h1, h2]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

theorem cayleyFromDisc_zero : cayleyFromDisc 0 = I := by simp [cayleyFromDisc]

theorem differentiableOn_cayleyFromDisc :
    DifferentiableOn ℂ cayleyFromDisc (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold cayleyFromDisc
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id) (one_sub_ne_zero_of_mem_ball hz)

theorem differentiableOn_cayleyToDisc : DifferentiableOn ℂ cayleyToDisc modUpperSet := by
  intro τ hτ
  apply DifferentiableAt.differentiableWithinAt
  unfold cayleyToDisc
  exact (differentiableAt_id.sub (differentiableAt_const _)).div
    (differentiableAt_id.add (differentiableAt_const _)) (add_I_ne_zero_of_im_pos hτ)

theorem convex_modUpperSet : Convex ℝ modUpperSet := by
  intro x hx y hy a b ha hb hab
  show 0 < (a • x + b • y).im
  have hx' : 0 < x.im := hx
  have hy' : 0 < y.im := hy
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp at hab; subst hab; simpa using hy'
  · nlinarith [mul_pos h hx', mul_nonneg hb hy'.le]

/-- **Logarithm on the upper half-plane.**  A zero-free holomorphic function on the upper
half-plane is the exponential of a holomorphic function. -/
theorem exists_log_on_upperHalfPlane {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f modUpperSet)
    (hne : ∀ τ ∈ modUpperSet, f τ ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L modUpperSet ∧
      ∀ τ ∈ modUpperSet, Complex.exp (L τ) = f τ := by
  have hmaps : Set.MapsTo cayleyFromDisc (Metric.ball (0 : ℂ) 1) modUpperSet :=
    fun z hz => cayleyFromDisc_im_pos hz
  have hg : DifferentiableOn ℂ (f ∘ cayleyFromDisc) (Metric.ball (0 : ℂ) 1) :=
    hf.comp differentiableOn_cayleyFromDisc hmaps
  have hgne : ∀ z ∈ Metric.ball (0 : ℂ) 1, (f ∘ cayleyFromDisc) z ≠ 0 :=
    fun z hz => hne _ (hmaps hz)
  obtain ⟨G, hG, _, hGf⟩ := GaloisForLFunctions.HTGeometry.exists_log_on_ball one_pos hg hgne
  have hI : f I ≠ 0 := hne I (by show (0 : ℝ) < I.im; simp)
  refine ⟨fun τ => Complex.log (f I) + G (cayleyToDisc τ), ?_, ?_⟩
  · have hmaps' : Set.MapsTo cayleyToDisc modUpperSet (Metric.ball (0 : ℂ) 1) :=
      fun τ hτ => cayleyToDisc_mem hτ
    exact (differentiableOn_const _).add (hG.comp differentiableOn_cayleyToDisc hmaps')
  · intro τ hτ
    have h := hGf (cayleyToDisc τ) (cayleyToDisc_mem hτ)
    simp only [Function.comp_apply, cayleyFromDisc_cayleyToDisc hτ, cayleyFromDisc_zero] at h
    rw [Complex.exp_add, Complex.exp_log hI, h]

/-- Two holomorphic logarithms of the same function on a preconnected open set differ by a
constant. -/
theorem log_sub_eq_const {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {L₁ L₂ : ℂ → ℂ} (h1 : DifferentiableOn ℂ L₁ U) (h2 : DifferentiableOn ℂ L₂ U)
    (he : ∀ τ ∈ U, Complex.exp (L₁ τ) = Complex.exp (L₂ τ)) {τ₀ : ℂ} (hτ₀ : τ₀ ∈ U) :
    ∀ τ ∈ U, L₁ τ - L₂ τ = L₁ τ₀ - L₂ τ₀ := by
  have hd : DifferentiableOn ℂ (fun τ => L₁ τ - L₂ τ) U := h1.sub h2
  have hderiv : Set.EqOn (deriv fun τ => L₁ τ - L₂ τ) 0 U := by
    intro τ hτ
    have hn := hU.mem_nhds hτ
    have d1 : HasDerivAt L₁ (deriv L₁ τ) τ := ((h1 τ hτ).differentiableAt hn).hasDerivAt
    have d2 : HasDerivAt L₂ (deriv L₂ τ) τ := ((h2 τ hτ).differentiableAt hn).hasDerivAt
    have e1 := d1.cexp
    have e2 := d2.cexp
    have heq : (fun z => Complex.exp (L₁ z)) =ᶠ[nhds τ] (fun z => Complex.exp (L₂ z)) :=
      Filter.eventually_of_mem hn (fun z hz => he z hz)
    have hdd : deriv (fun z => Complex.exp (L₁ z)) τ = deriv (fun z => Complex.exp (L₂ z)) τ :=
      heq.deriv_eq
    rw [e1.deriv, e2.deriv, he τ hτ] at hdd
    have hne : Complex.exp (L₂ τ) ≠ 0 := Complex.exp_ne_zero _
    have hLL : deriv L₁ τ = deriv L₂ τ := mul_left_cancel₀ hne hdd
    have h3 : HasDerivAt (fun x => L₁ x - L₂ x) (deriv L₁ τ - deriv L₂ τ) τ := d1.sub d2
    rw [h3.deriv, hLL, sub_self]
    rfl
  intro τ hτ
  exact hU.is_const_of_deriv_eq_zero hUc hd hderiv hτ hτ₀

theorem isPreconnected_modUpperSet : IsPreconnected modUpperSet :=
  convex_modUpperSet.isPreconnected

theorem I_mem_modUpperSet : I ∈ modUpperSet := by show (0 : ℝ) < I.im; simp

/-! ## Conjugation symmetry of the theta constants -/

theorem thetaThree_conj (τ : ℂ) : (starRingEnd ℂ) (thetaThree τ) = thetaThree (-(starRingEnd ℂ) τ) := by
  unfold thetaThree; rw [jacobiTheta₂_conj]; simp

theorem thetaFour_conj (τ : ℂ) : (starRingEnd ℂ) (thetaFour τ) = thetaFour (-(starRingEnd ℂ) τ) := by
  unfold thetaFour; rw [jacobiTheta₂_conj]
  have : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [this]

theorem thetaTwo_conj (τ : ℂ) : (starRingEnd ℂ) (thetaTwo τ) = thetaTwo (-(starRingEnd ℂ) τ) := by
  unfold thetaTwo
  rw [map_mul, jacobiTheta₂_conj, ← Complex.exp_conj]
  have h1 : (starRingEnd ℂ) ((Real.pi : ℂ) * I * τ / 4) =
      (Real.pi : ℂ) * I * (-(starRingEnd ℂ) τ) / 4 := by
    rw [map_div₀, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
  have h2 : (starRingEnd ℂ) (τ / 2) = -(-(starRingEnd ℂ) τ / 2) := by
    rw [map_div₀, map_ofNat]; ring
  rw [h1, h2, jacobiTheta₂_neg_left]

theorem thetaGroupHauptmodul_conj (τ : ℂ) :
    (starRingEnd ℂ) (thetaGroupHauptmodul τ) = thetaGroupHauptmodul (-(starRingEnd ℂ) τ) := by
  unfold thetaGroupHauptmodul
  simp only [map_div₀, map_mul, map_pow, thetaTwo_conj, thetaThree_conj, thetaFour_conj]

theorem neg_conj_I_mul_ofReal (y : ℝ) : -(starRingEnd ℂ) (I * (y : ℂ)) = I * (y : ℂ) := by
  simp [Complex.conj_ofReal]

theorem thetaGroupHauptmodul_I_mul_real (y : ℝ) :
    (starRingEnd ℂ) (thetaGroupHauptmodul (I * (y : ℂ))) = thetaGroupHauptmodul (I * (y : ℂ)) := by
  rw [thetaGroupHauptmodul_conj, neg_conj_I_mul_ofReal]

theorem theta_I_mul_real_eq_re {f : ℂ → ℂ}
    (hf : ∀ τ, (starRingEnd ℂ) (f τ) = f (-(starRingEnd ℂ) τ)) (y : ℝ) :
    f (I * (y : ℂ)) = ((f (I * (y : ℂ))).re : ℂ) := by
  have h := hf (I * (y : ℂ))
  rw [neg_conj_I_mul_ofReal] at h
  exact (Complex.conj_eq_iff_re.mp h).symm

/-- `h` is positive on the positive imaginary axis. -/
theorem thetaGroupHauptmodul_I_mul_pos {y : ℝ} (hy : 0 < y) :
    thetaGroupHauptmodul (I * (y : ℂ)) = ((thetaGroupHauptmodul (I * (y : ℂ))).re : ℂ) ∧
      0 < (thetaGroupHauptmodul (I * (y : ℂ))).re := by
  have him : 0 < (I * (y : ℂ)).im := by simpa using hy
  set r2 := (thetaTwo (I * (y : ℂ))).re
  set r3 := (thetaThree (I * (y : ℂ))).re
  set r4 := (thetaFour (I * (y : ℂ))).re
  have e2 : thetaTwo (I * (y : ℂ)) = (r2 : ℂ) := theta_I_mul_real_eq_re thetaTwo_conj y
  have e3 : thetaThree (I * (y : ℂ)) = (r3 : ℂ) := theta_I_mul_real_eq_re thetaThree_conj y
  have e4 : thetaFour (I * (y : ℂ)) = (r4 : ℂ) := theta_I_mul_real_eq_re thetaFour_conj y
  have n2 : r2 ≠ 0 := by
    intro h; apply thetaTwo_ne_zero_of_im_pos him; rw [e2, h]; simp
  have n3 : r3 ≠ 0 := by
    intro h; apply thetaThree_ne_zero_of_im_pos him; rw [e3, h]; simp
  have n4 : r4 ≠ 0 := by
    intro h; apply thetaFour_ne_zero_of_im_pos him; rw [e4, h]; simp
  have hval : thetaGroupHauptmodul (I * (y : ℂ)) = ((r2 ^ 4 * r4 ^ 4 / r3 ^ 8 : ℝ) : ℂ) := by
    unfold thetaGroupHauptmodul; rw [e2, e3, e4]; push_cast; ring
  have hpos : 0 < r2 ^ 4 * r4 ^ 4 / r3 ^ 8 := by
    have a : 0 < r2 ^ 4 := by positivity
    have b : 0 < r4 ^ 4 := by positivity
    have c : 0 < r3 ^ 8 := by positivity
    positivity
  rw [hval, Complex.ofReal_re]
  exact ⟨rfl, hpos⟩

/-! ## The Hauptmodul logarithm -/

theorem differentiableOn_thetaGroupHauptmodul :
    DifferentiableOn ℂ thetaGroupHauptmodul modUpperSet :=
  fun _ hτ => (differentiableAt_thetaGroupHauptmodul hτ).differentiableWithinAt

theorem thetaGroupHauptmodul_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : thetaGroupHauptmodul τ ≠ 0 := by
  unfold thetaGroupHauptmodul
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (thetaTwo_ne_zero_of_im_pos hτ))
    (pow_ne_zero _ (thetaFour_ne_zero_of_im_pos hτ))) (pow_ne_zero _ (thetaThree_ne_zero_of_im_pos hτ))

theorem exists_hauptmodulLog :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L modUpperSet ∧
      ∀ τ ∈ modUpperSet, Complex.exp (L τ) = thetaGroupHauptmodul τ :=
  exists_log_on_upperHalfPlane differentiableOn_thetaGroupHauptmodul
    (fun _ hτ => thetaGroupHauptmodul_ne_zero hτ)

/-- Some holomorphic logarithm of `h`. -/
def hauptmodulLogRaw : ℂ → ℂ := Classical.choose exists_hauptmodulLog

/-- **The Hauptmodul logarithm**, normalized by `log h(i) ∈ ℝ`. -/
def hauptmodulLog (τ : ℂ) : ℂ :=
  hauptmodulLogRaw τ - hauptmodulLogRaw I + Complex.log (thetaGroupHauptmodul I)

theorem differentiableOn_hauptmodulLog : DifferentiableOn ℂ hauptmodulLog modUpperSet :=
  ((Classical.choose_spec exists_hauptmodulLog).1.sub_const _).add_const _

theorem exp_hauptmodulLog {τ : ℂ} (hτ : 0 < τ.im) :
    Complex.exp (hauptmodulLog τ) = thetaGroupHauptmodul τ := by
  have hspec := (Classical.choose_spec exists_hauptmodulLog).2
  have hτ' : Complex.exp (hauptmodulLogRaw τ) = thetaGroupHauptmodul τ := hspec τ hτ
  have hI' : Complex.exp (hauptmodulLogRaw I) = thetaGroupHauptmodul I := hspec I I_mem_modUpperSet
  have hIne : thetaGroupHauptmodul I ≠ 0 := thetaGroupHauptmodul_ne_zero (by simp)
  unfold hauptmodulLog
  rw [Complex.exp_add, Complex.exp_sub, hτ', hI', Complex.exp_log hIne]
  field_simp

theorem hauptmodulLog_I : hauptmodulLog I = Complex.log (thetaGroupHauptmodul I) := by
  unfold hauptmodulLog; ring

theorem hauptmodulLog_I_im : (hauptmodulLog I).im = 0 := by
  rw [hauptmodulLog_I]
  have h := thetaGroupHauptmodul_I_mul_pos (y := 1) one_pos
  simp only [Complex.ofReal_one, mul_one] at h
  rw [h.1, Complex.log_im, Complex.arg_ofReal_of_nonneg h.2.le]

/-- `log h(-1/τ) = log h(τ)`. -/
theorem hauptmodulLog_S {τ : ℂ} (hτ : 0 < τ.im) : hauptmodulLog (-1 / τ) = hauptmodulLog τ := by
  have hS : ∀ σ ∈ modUpperSet, (-1 / σ) ∈ modUpperSet := by
    intro σ hσ
    have hσ' : 0 < σ.im := hσ
    show 0 < (-1 / σ).im
    have hne : σ ≠ 0 := fun h => by rw [h] at hσ'; simp at hσ'
    rw [neg_div, Complex.neg_im, one_div, Complex.inv_im]
    have : 0 < Complex.normSq σ := Complex.normSq_pos.mpr hne
    rw [neg_div, neg_neg]
    exact div_pos hσ' this
  have hd : DifferentiableOn ℂ (fun σ => hauptmodulLog (-1 / σ)) modUpperSet := by
    intro σ hσ
    have hσ' : 0 < σ.im := hσ
    have hne : σ ≠ 0 := fun h => by rw [h] at hσ'; simp at hσ'
    have hinner : DifferentiableAt ℂ (fun σ : ℂ => -1 / σ) σ :=
      (differentiableAt_const _).div differentiableAt_id hne
    have houter : DifferentiableAt ℂ hauptmodulLog (-1 / σ) :=
      (differentiableOn_hauptmodulLog _ (hS σ hσ)).differentiableAt
        (isOpen_modUpperSet.mem_nhds (hS σ hσ))
    exact (houter.comp σ hinner).differentiableWithinAt
  have he : ∀ σ ∈ modUpperSet,
      Complex.exp (hauptmodulLog (-1 / σ)) = Complex.exp (hauptmodulLog σ) := by
    intro σ hσ
    rw [exp_hauptmodulLog (hS σ hσ), exp_hauptmodulLog hσ, thetaGroupHauptmodul_S hσ]
  have h := log_sub_eq_const isOpen_modUpperSet isPreconnected_modUpperSet hd
    differentiableOn_hauptmodulLog he I_mem_modUpperSet τ hτ
  have hII : (-1 / I : ℂ) = I := by field_simp; rw [Complex.I_sq]
  rw [hII, sub_self] at h
  exact sub_eq_zero.mp h

/-- `log h(-τ̄) = conj (log h(τ))`. -/
theorem hauptmodulLog_neg_conj {τ : ℂ} (hτ : 0 < τ.im) :
    hauptmodulLog (-(starRingEnd ℂ) τ) = (starRingEnd ℂ) (hauptmodulLog τ) := by
  have hmem : ∀ σ ∈ modUpperSet, -(starRingEnd ℂ) σ ∈ modUpperSet := by
    intro σ hσ
    have hσ' : 0 < σ.im := hσ
    show 0 < (-(starRingEnd ℂ) σ).im; simpa using hσ'
  set Lt : ℂ → ℂ := fun σ => (starRingEnd ℂ) (hauptmodulLog (-(starRingEnd ℂ) σ)) with hLt
  have hd : DifferentiableOn ℂ Lt modUpperSet := by
    intro σ hσ
    have hm : -(starRingEnd ℂ) σ ∈ modUpperSet := hmem σ hσ
    have h0 : DifferentiableAt ℂ hauptmodulLog (-(starRingEnd ℂ) σ) :=
      (differentiableOn_hauptmodulLog _ hm).differentiableAt (isOpen_modUpperSet.mem_nhds hm)
    have h1 : DifferentiableAt ℂ (fun z => hauptmodulLog (-z)) ((starRingEnd ℂ) σ) := by
      have := h0.comp ((starRingEnd ℂ) σ) (differentiableAt_neg_iff.mpr differentiableAt_id)
      simpa [Function.comp_def] using this
    have h2 := h1.conj_conj
    simp only [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have he : ∀ σ ∈ modUpperSet, Complex.exp (Lt σ) = Complex.exp (hauptmodulLog σ) := by
    intro σ hσ
    have hσ' : 0 < σ.im := hσ
    rw [hLt]; simp only
    rw [Complex.exp_conj, exp_hauptmodulLog (hmem σ hσ), thetaGroupHauptmodul_conj,
      map_neg, Complex.conj_conj, neg_neg, exp_hauptmodulLog hσ']
  have h := log_sub_eq_const isOpen_modUpperSet isPreconnected_modUpperSet hd
    differentiableOn_hauptmodulLog he I_mem_modUpperSet τ hτ
  have hI : Lt I = hauptmodulLog I := by
    rw [hLt]; simp only
    have : -(starRingEnd ℂ) I = I := by simp
    rw [this]
    exact Complex.conj_eq_iff_im.mpr hauptmodulLog_I_im
  rw [hI, sub_self] at h
  have h' : Lt τ = hauptmodulLog τ := sub_eq_zero.mp h
  rw [hLt] at h'
  simp only at h'
  rw [← h', Complex.conj_conj]

/-- `log h` is real on the positive imaginary axis. -/
theorem hauptmodulLog_I_mul_im {y : ℝ} (hy : 0 < y) : (hauptmodulLog (I * (y : ℂ))).im = 0 := by
  have h := hauptmodulLog_neg_conj (τ := I * (y : ℂ)) (by simpa using hy)
  rw [neg_conj_I_mul_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- `log h` is real on the unit circle. -/
theorem hauptmodulLog_im_of_norm_eq_one {τ : ℂ} (hτ : 0 < τ.im) (h1 : ‖τ‖ = 1) :
    (hauptmodulLog τ).im = 0 := by
  have hne : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hinv : -1 / τ = -(starRingEnd ℂ) τ := by
    have hmul : τ * (starRingEnd ℂ) τ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
    have hc : (starRingEnd ℂ) τ = 1 / τ := by
      rw [eq_div_iff hne]; linear_combination hmul
    rw [hc]; ring
  have hS := hauptmodulLog_S hτ
  rw [hinv, hauptmodulLog_neg_conj hτ] at hS
  exact Complex.conj_eq_iff_im.mp hS

/-- `|exp(s log h)| = |h|^s`. -/
theorem norm_exp_mul_hauptmodulLog {τ : ℂ} (hτ : 0 < τ.im) (s : ℝ) :
    ‖Complex.exp ((s : ℂ) * hauptmodulLog τ)‖ = ‖thetaGroupHauptmodul τ‖ ^ s := by
  have hne := thetaGroupHauptmodul_ne_zero hτ
  have hre : (hauptmodulLog τ).re = Real.log ‖thetaGroupHauptmodul τ‖ := by
    have h := congrArg (fun z => ‖z‖) (exp_hauptmodulLog hτ)
    simp only [Complex.norm_exp] at h
    rw [← h, Real.log_exp]
  rw [Complex.norm_exp, Complex.re_ofReal_mul, hre,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hne), mul_comm]

end

end RHTower
