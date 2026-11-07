import GaloisForLFunctions.RigidArithmeticOfCuts.TheZeroOfMaximalAngle
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The Stieltjes sign of the extremal zero

At the zero `w₀` of maximal angle the function `t ↦ Q(t w₀)` is of Hermite–Biehler class, with a zero at `t = 1` on the
boundary. The modulus inequality `‖Q(t̄ w₀)‖ < ‖Q(t w₀)‖` holds for all `Im t > 0`, and its first order at `t = 1` is a
sign.

**If `w₀` is simple, then `Im(w₀ Q″(w₀)/Q′(w₀)) ≤ 0`.**

By the Hadamard product, `Q″/Q′(w₀) = 2 Σ_{w ≠ w₀} 1/(w₀ − w)`, so this is the angular component of the Stieltjes force of the
other zeros on the extremal one. Under RH no zero has `Im w₀ > 0`, so the statement is a necessary law of a counterexample: the
extremal position takes the place of a sign.
-/

open Complex Filter Topology RHTower

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- On the unit circle a boundary zero at `1` factors out with equal modulus on both sides. -/
private lemma norm_exp_sub_one_conj (θ : ℝ) :
    ‖Complex.exp ((-θ : ℝ) * I) - 1‖ = ‖Complex.exp ((θ : ℝ) * I) - 1‖ := by
  have h : Complex.exp ((-θ : ℝ) * I) - 1 = star (Complex.exp ((θ : ℝ) * I) - 1) := by
    rw [star_sub, star_one]
    congr 1
    have h1 : star (Complex.exp ((θ : ℝ) * I)) = Complex.exp (star ((θ : ℝ) * I)) := by
      simpa using (Complex.exp_conj ((θ : ℝ) * I)).symm
    rw [h1]
    congr 1
    simp
  rw [h, norm_star]

/-- **A boundary zero of an entire function with the modulus inequality has a Stieltjes sign.** -/
theorem im_second_div_first_nonpos {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h1 : f 1 = 0)
    (hsimple : deriv f 1 ≠ 0) (hmod : ∀ t : ℂ, 0 < t.im → ‖f (star t)‖ ≤ ‖f t‖) :
    (deriv (deriv f) 1 / deriv f 1).im ≤ 0 := by
  -- The cofactor at the boundary zero.
  set g : ℂ → ℂ := dslope f 1 with hg
  have hgd : Differentiable ℂ g := by
    have h := (Complex.differentiableOn_dslope (s := Set.univ) (c := (1 : ℂ)) (f := f) Filter.univ_mem).mpr
      hf.differentiableOn
    exact differentiableOn_univ.mp h
  have hfac : ∀ z, f z = (z - 1) * g z := by
    intro z
    have := sub_smul_dslope f (1 : ℂ) z
    rw [h1, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hg1 : g 1 = deriv f 1 := dslope_same f 1
  -- The second derivative of `f` is twice the first of `g`.
  have hderiv : deriv f = fun z => g z + (z - 1) * deriv g z := by
    funext z
    have hd : HasDerivAt f (1 * g z + (z - 1) * deriv g z) z := by
      have h2 := ((hasDerivAt_id z).sub_const 1).mul (hgd z).hasDerivAt
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun w => hfac w)
    rw [hd.deriv, one_mul]
  have hgdd : Differentiable ℂ (deriv g) := by
    have h := (hgd.differentiableOn (s := Set.univ)).deriv isOpen_univ
    exact differentiableOn_univ.mp h
  have hsecond : deriv (deriv f) 1 = 2 * deriv g 1 := by
    rw [hderiv]
    have hd : HasDerivAt (fun z => g z + (z - 1) * deriv g z)
        (deriv g 1 + (1 * deriv g 1 + (1 - 1) * deriv (deriv g) 1)) 1 :=
      (hgd 1).hasDerivAt.add (((hasDerivAt_id (1 : ℂ)).sub_const 1).mul (hgdd 1).hasDerivAt)
    rw [hd.deriv]
    ring
  -- The modulus inequality on the circle, for the cofactor.
  set φ : ℝ → ℂ := fun θ => g (Complex.exp ((θ : ℂ) * I)) with hφ
  have hineq : ∀ θ : ℝ, 0 < θ → θ < Real.pi → ‖φ (-θ)‖ ^ 2 ≤ ‖φ θ‖ ^ 2 := by
    intro θ h0 hπ
    have him : 0 < (Complex.exp ((θ : ℂ) * I)).im := by
      rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi h0 hπ
    have hst : star (Complex.exp ((θ : ℂ) * I)) = Complex.exp (((-θ : ℝ) : ℂ) * I) := by
      have h3 : star (Complex.exp ((θ : ℂ) * I)) = Complex.exp (star ((θ : ℂ) * I)) := by
        simpa using (Complex.exp_conj ((θ : ℂ) * I)).symm
      rw [h3]
      congr 1
      simp
    have hm := hmod _ him
    rw [hst, hfac, hfac, norm_mul, norm_mul, norm_exp_sub_one_conj] at hm
    have hne : Complex.exp ((θ : ℂ) * I) - 1 ≠ 0 := by
      intro h0'
      have h4 : Complex.exp ((θ : ℂ) * I) = 1 := sub_eq_zero.mp h0'
      rw [h4] at him
      simp at him
    have hpos : 0 < ‖Complex.exp ((θ : ℂ) * I) - 1‖ := norm_pos_iff.mpr hne
    have hle := le_of_mul_le_mul_left hm hpos
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  -- The derivative of the squared modulus along the circle.
  have hφd : HasDerivAt φ (deriv g 1 * I) 0 := by
    have he : HasDerivAt (fun z : ℂ => Complex.exp (z * I)) I 0 := by
      have h3 := ((hasDerivAt_id (0 : ℂ)).mul_const I).cexp
      simpa using h3
    have hgat : HasDerivAt g (deriv g 1) (Complex.exp ((0 : ℂ) * I)) := by
      simpa using (hgd 1).hasDerivAt
    have hcomp := hgat.comp (0 : ℂ) he
    have hreal := hcomp.comp_ofReal
    simpa using hreal
  have hφ0 : φ 0 = g 1 := by simp [hφ]
  have hG : HasDerivAt (fun θ : ℝ => ‖φ θ‖ ^ 2) (2 * inner ℝ (φ 0) (deriv g 1 * I)) 0 := hφd.norm_sq
  have hGneg : HasDerivAt (fun θ : ℝ => ‖φ (-θ)‖ ^ 2) (-(2 * inner ℝ (φ 0) (deriv g 1 * I))) 0 := by
    have hG' : HasDerivAt (fun θ : ℝ => ‖φ θ‖ ^ 2) (2 * inner ℝ (φ 0) (deriv g 1 * I)) (Neg.neg (0 : ℝ)) := by
      simpa using hG
    have h3 := hG'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have h4 : (2 * inner ℝ (φ 0) (deriv g 1 * I)) * (-1 : ℝ) = -(2 * inner ℝ (φ 0) (deriv g 1 * I)) := by ring
    rw [h4] at h3
    exact h3
  set ψ : ℝ → ℝ := fun θ => ‖φ θ‖ ^ 2 - ‖φ (-θ)‖ ^ 2 with hψdef
  have hψ : HasDerivAt ψ (2 * inner ℝ (φ 0) (deriv g 1 * I) - -(2 * inner ℝ (φ 0) (deriv g 1 * I))) 0 :=
    hG.sub hGneg
  have hψ0 : ψ 0 = 0 := by simp [hψdef]
  have hslope := hψ.tendsto_slope_zero_right
  have hnonneg : 0 ≤ 2 * inner ℝ (φ 0) (deriv g 1 * I) - -(2 * inner ℝ (φ 0) (deriv g 1 * I)) := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
    have h3 := hineq θ hθ.1 hθ.2
    rw [zero_add, hψ0, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hθ.1.le) (sub_nonneg.mpr h3)
  have hinner : 0 ≤ inner ℝ (g 1) (deriv g 1 * I) := by
    rw [hφ0] at hnonneg
    linarith
  -- Reading the inner product.
  have hg1ne : g 1 ≠ 0 := by rwa [hg1]
  rw [Complex.inner] at hinner
  have hnsq : 0 < Complex.normSq (g 1) := Complex.normSq_pos.mpr hg1ne
  have hval : (deriv g 1 / g 1).im = -((deriv g 1 * I * (starRingEnd ℂ) (g 1)).re) / Complex.normSq (g 1) := by
    rw [Complex.div_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  have hle : (deriv g 1 / g 1).im ≤ 0 := by
    rw [hval]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hnsq.le
  rw [hsecond, ← hg1, mul_div_assoc, Complex.mul_im]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  linarith

/-- **The Stieltjes sign of the extremal zero.** At a simple zero of maximal angle, `Im(w₀ Q″(w₀)/Q′(w₀)) ≤ 0`. -/
theorem im_stieltjes_nonpos {q₀ : XiZeroCopy} (h : ∀ q, 0 ≤ (zeroSq q₀ / zeroSq q).im)
    (hstrict : ∃ q₁, 0 < (zeroSq q₀ / zeroSq q₁).im) (hsimple : deriv squaredXi (zeroSq q₀) ≠ 0) :
    (zeroSq q₀ * deriv (deriv squaredXi) (zeroSq q₀) / deriv squaredXi (zeroSq q₀)).im ≤ 0 := by
  set w₀ := zeroSq q₀ with hw₀
  have hQ : Differentiable ℂ squaredXi := differentiable_xiSquaredSeamEntireQuotient
  have hQ' : Differentiable ℂ (deriv squaredXi) := by
    have h1 := (hQ.differentiableOn (s := Set.univ)).deriv isOpen_univ
    exact differentiableOn_univ.mp h1
  set f : ℂ → ℂ := fun t => squaredXi (t * w₀) with hf
  have hscale : ∀ t : ℂ, HasDerivAt (fun t : ℂ => t * w₀) w₀ t := by
    intro t
    simpa using (hasDerivAt_id t).mul_const w₀
  have hf1 : ∀ t, HasDerivAt f (deriv squaredXi (t * w₀) * w₀) t := fun t =>
    HasDerivAt.comp (h₂ := squaredXi) (h := fun t => t * w₀) t (hQ (t * w₀)).hasDerivAt (hscale t)
  have hfd : Differentiable ℂ f := fun t => (hf1 t).differentiableAt
  have hderiv : deriv f = fun t => deriv squaredXi (t * w₀) * w₀ := funext fun t => (hf1 t).deriv
  have hf2 : deriv (deriv f) 1 = deriv (deriv squaredXi) w₀ * w₀ * w₀ := by
    rw [hderiv]
    have h3 : HasDerivAt (fun t => deriv squaredXi (t * w₀)) (deriv (deriv squaredXi) (1 * w₀) * w₀) 1 :=
      HasDerivAt.comp (h₂ := deriv squaredXi) (h := fun t => t * w₀) 1 (hQ' (1 * w₀)).hasDerivAt (hscale 1)
    have h2 := h3.mul_const w₀
    rw [h2.deriv, one_mul]
  have hf1' : deriv f 1 = deriv squaredXi w₀ * w₀ := by
    rw [hderiv]
    simp only [one_mul]
  have hw₀ne : w₀ ≠ 0 := zeroSq_ne_zero q₀
  have hzero : f 1 = 0 := by
    simp only [hf, one_mul]
    exact (squaredXi_eq_zero_iff _).mpr ⟨q₀, rfl⟩
  have hmod : ∀ t : ℂ, 0 < t.im → ‖f (star t)‖ ≤ ‖f t‖ := fun t ht =>
    (norm_squaredXi_conj_lt h hstrict ht).le
  have hmain := im_second_div_first_nonpos hfd hzero
    (by rw [hf1']; exact mul_ne_zero hsimple hw₀ne) hmod
  rw [hf2, hf1'] at hmain
  have hval : deriv (deriv squaredXi) w₀ * w₀ * w₀ / (deriv squaredXi w₀ * w₀) =
      w₀ * deriv (deriv squaredXi) w₀ / deriv squaredXi w₀ := by
    field_simp
  rwa [hval] at hmain

end GaloisForLFunctions.RigidArithmeticOfCuts
