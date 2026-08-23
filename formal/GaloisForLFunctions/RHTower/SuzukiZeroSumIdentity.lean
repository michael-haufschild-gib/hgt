import GaloisForLFunctions.RHTower.SuzukiModelKernel
import GaloisForLFunctions.RHTower.SuzukiCauchyGram
import GaloisForLFunctions.RHTower.SuzukiFGammaOrthonormal
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH

noncomputable section

/-!
# Parseval's sum for the reproducing kernel

The completeness of `{F_γ}` in `K(Θ_ξ)` reduces to a single scalar identity: for every `w` in the
upper half-plane the squared values `|F_γ(w)|²` sum to the diagonal value `k_w(w)` of the
reproducing kernel.  That identity is not Clark theory but algebra plus the Hadamard partial
fraction the corpus already owns.

Two ingredients.  Under the Riemann hypothesis every Xi zero is real, so the imaginary part of the
multiplicity-exact partial fraction `logDeriv A(w) = Σ_q (γ_q⁻¹ - (γ_q - w)⁻¹)` is
`-Im(w) Σ_q |w - γ_q|⁻²`; summing the divisor copies over each support point converts that into the
multiplicity-weighted sum.  And with `A = a + bi`, `A' = c + di`, both `Re(A/E) - |A/E|²` and
`-|A/E|² Im(A'/A)` equal `(bc - ad)/|E|²`, so the defect of the boundary energy identity off the
axis is exactly that logarithmic derivative.

Combining, and using `k_w(w) = (Re(A/E) - |A/E|²)/(π Im w)`, gives the sum.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

theorem XiC_ne_zero_of_im_pos (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    XiC w ≠ 0 := by
  intro h
  have hz := (riemannHypothesis_iff_XiC_zeros_real.mp hRH) w h
  linarith

theorem im_xiRelativeResolventTerm (hRH : RiemannHypothesis) (w : ℂ) (q : XiZeroCopy) :
    (xiRelativeResolventTerm w q).im = -(w.im / ‖w - xiSpectralPoint q‖ ^ 2) := by
  have hreal := xiSpectralPoint_eq_ofReal_of_rh hRH q
  rw [xiRelativeResolventTerm, hreal, Complex.sub_im, Complex.inv_im, Complex.inv_im]
  have h1 : (((xiRealSpectralPoint q : ℝ) : ℂ)).im = 0 := by simp
  have h2 : (((xiRealSpectralPoint q : ℝ) : ℂ) - w).im = -w.im := by simp
  rw [h1, h2]
  have h3 : ‖w - ((xiRealSpectralPoint q : ℝ) : ℂ)‖ ^ 2
      = Complex.normSq (((xiRealSpectralPoint q : ℝ) : ℂ) - w) := by
    rw [Complex.sq_norm, ← Complex.normSq_neg]
    congr 1
    ring
  rw [h3]
  simp

theorem hasSum_xiZeroCopy_inv_normSq (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun q : XiZeroCopy => 1 / ‖w - xiSpectralPoint q‖ ^ 2)
      (-((logDeriv XiC w).im) / w.im) := by
  have hXi := XiC_ne_zero_of_im_pos hRH hw
  have hls : HasSum (xiRelativeResolventTerm w) (logDeriv XiC w) := by
    rw [logDeriv_XiC_eq_relativeResolventTrace hXi, xiRelativeResolventTrace]
    exact (summable_xiRelativeResolventTerm hXi).hasSum
  have him := Complex.hasSum_im hls
  have hcong : HasSum (fun q : XiZeroCopy => (-w.im) * (1 / ‖w - xiSpectralPoint q‖ ^ 2))
      ((logDeriv XiC w).im) := by
    refine him.congr_fun ?_
    intro q
    rw [im_xiRelativeResolventTerm hRH w q]
    ring
  have hne : (-w.im) ≠ 0 := by
    intro h
    have : w.im = 0 := by linarith [neg_eq_zero.mp h]
    linarith
  have hscaled := hcong.mul_left (-w.im)⁻¹
  have hval : (-w.im)⁻¹ * (logDeriv XiC w).im = -((logDeriv XiC w).im) / w.im := by
    field_simp
  rw [← hval]
  refine hscaled.congr_fun ?_
  intro q
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **The zero-sum identity.**  The multiplicity-weighted inverse-square sum over the (real) Xi
zeros is the imaginary part of the logarithmic derivative, divided by the height. -/
theorem hasSum_xiSupport_mult_inv_normSq (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun ρ : XiDivisorSupport =>
        (xiSupportMult ρ : ℝ) / ‖w - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ 2)
      (-((logDeriv XiC w).im) / w.im) := by
  refine (hasSum_xiZeroCopy_inv_normSq hRH hw).sigma ?_
  intro ρ
  have hbase := hasSum_fintype (fun _i : Fin (xiSupportMult ρ) =>
    (1 : ℝ) / ‖w - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ 2)
  have hsum : (∑ _i : Fin (xiSupportMult ρ),
      (1 : ℝ) / ‖w - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ 2)
      = (xiSupportMult ρ : ℝ) / ‖w - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at hbase
  refine hbase.congr_fun ?_
  intro i
  rw [xiSpectralPoint_eq_support, ← ofReal_xiRealSpectralPointSupport hRH]

/-- The real algebra behind the energy identity: with `A = a + bi` and `A' = c + di`, both
`Re(A/E) - |A/E|²` and `-|A/E|² Im(A'/A)` equal `(bc - ad)/|E|²`. -/
theorem halfInner_algebraic (a b c d : ℝ) (hp : a ^ 2 + b ^ 2 ≠ 0)
    (hE : (a - d) ^ 2 + (b + c) ^ 2 ≠ 0) :
    (a * (a - d) + b * (b + c)) / ((a - d) ^ 2 + (b + c) ^ 2)
        - (a ^ 2 + b ^ 2) / ((a - d) ^ 2 + (b + c) ^ 2)
      = -((a ^ 2 + b ^ 2) / ((a - d) ^ 2 + (b + c) ^ 2)
          * ((d * a - c * b) / (a ^ 2 + b ^ 2))) := by
  field_simp
  ring

/-- **The energy identity.**  On the upper half-plane the defect `Re(A/E) - |A/E|²` is the
logarithmic derivative of `A` weighted by that same energy. -/
theorem re_sub_normSq_suzukiHalfInner (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    (suzukiHalfInner w).re - ‖suzukiHalfInner w‖ ^ 2
      = -(‖suzukiHalfInner w‖ ^ 2 * (logDeriv XiC w).im) := by
  have hp : XiC w ≠ 0 := XiC_ne_zero_of_im_pos hRH hw
  have hEne : xiHedenmalmDeBrangesE w ≠ 0 :=
    xiHedenmalmDeBrangesE_ne_zero_upperHalf_of_rh hRH hw
  set a : ℝ := (XiC w).re with ha
  set b : ℝ := (XiC w).im with hb
  set c : ℝ := (deriv XiC w).re with hc
  set d : ℝ := (deriv XiC w).im with hd
  have hEre : (xiHedenmalmDeBrangesE w).re = a - d := by
    rw [xiHedenmalmDeBrangesE]
    simp [Complex.add_re, Complex.mul_re, ha, hd]
    ring
  have hEim : (xiHedenmalmDeBrangesE w).im = b + c := by
    rw [xiHedenmalmDeBrangesE]
    simp [Complex.add_im, Complex.mul_im, hb, hc]
  have hpsq : a ^ 2 + b ^ 2 ≠ 0 := by
    have := (map_ne_zero Complex.normSq).mpr hp
    rw [Complex.normSq_apply] at this
    rw [← ha, ← hb] at this
    intro h
    exact this (by nlinarith)
  have hEsq : (a - d) ^ 2 + (b + c) ^ 2 ≠ 0 := by
    have := (map_ne_zero Complex.normSq).mpr hEne
    rw [Complex.normSq_apply, hEre, hEim] at this
    intro h
    exact this (by nlinarith)
  have hnsq : Complex.normSq (xiHedenmalmDeBrangesE w) = (a - d) ^ 2 + (b + c) ^ 2 := by
    rw [Complex.normSq_apply, hEre, hEim]
    ring
  have hnp : Complex.normSq (XiC w) = a ^ 2 + b ^ 2 := by
    rw [Complex.normSq_apply, ← ha, ← hb]
    ring
  have hre : (suzukiHalfInner w).re
      = (a * (a - d) + b * (b + c)) / ((a - d) ^ 2 + (b + c) ^ 2) := by
    rw [suzukiHalfInner, Complex.div_re, hnsq, hEre, hEim, ← ha, ← hb]
    ring
  have hnorm : ‖suzukiHalfInner w‖ ^ 2
      = (a ^ 2 + b ^ 2) / ((a - d) ^ 2 + (b + c) ^ 2) := by
    rw [suzukiHalfInner, Complex.sq_norm, Complex.normSq_div, hnsq, hnp]
  have hlog : (logDeriv XiC w).im = (d * a - c * b) / (a ^ 2 + b ^ 2) := by
    rw [logDeriv_apply, Complex.div_im, hnp, ← ha, ← hb, ← hc, ← hd]
    ring
  rw [hre, hnorm, hlog]
  exact halfInner_algebraic a b c d hpsq hEsq


/-- **The diagonal value of the kernel.**  `k_w(w) = (Re(A/E) - |A/E|²)/(π Im w)`, a real
number. -/
theorem suzukiModelKernel_self {w : ℂ} (hw : 0 < w.im) :
    suzukiModelKernel w w
      = ((((suzukiHalfInner w).re - ‖suzukiHalfInner w‖ ^ 2) / (Real.pi * w.im) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have hsub : w - (starRingEnd ℂ) w = 2 * I * ((w.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
      ring
  have hmul : (starRingEnd ℂ) (suzukiThetaMero w) * suzukiThetaMero w
      = ((Complex.normSq (suzukiThetaMero w) : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have hnorm : Complex.normSq (suzukiThetaMero w)
      = 4 * ‖suzukiHalfInner w‖ ^ 2 - 4 * (suzukiHalfInner w).re + 1 := by
    rw [suzukiThetaMero, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  set r : ℝ := (suzukiHalfInner w).re with hr
  set s : ℝ := ‖suzukiHalfInner w‖ ^ 2 with hs
  set t : ℝ := w.im with ht
  have him : ((t : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, ht]
    exact ne_of_gt hw
  have hpic : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.pi_ne_zero
  rw [suzukiModelKernel, hmul, hnorm, hsub]
  have hcast : ((4 * s - 4 * r + 1 : ℝ) : ℂ) = 4 * (s : ℂ) - 4 * (r : ℂ) + 1 := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul]
  field_simp
  ring

theorem normSq_suzukiFGammaFun_upper (hRH : RiemannHypothesis) (ρ : XiDivisorSupport)
    {w : ℂ} (hw : 0 < w.im) :
    ‖suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) w‖ ^ 2
      = (‖suzukiHalfInner w‖ ^ 2 / Real.pi)
        * ((xiSupportMult ρ : ℝ) / ‖w - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ 2) := by
  have hpi := Real.pi_pos
  have hγ := XiC_xiRealSpectralPointSupport hRH ρ
  have hne : w ≠ ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
    intro h
    rw [h] at hw
    simp at hw
  have hmnn : (0 : ℝ) ≤ (xiSupportMult ρ : ℝ) / Real.pi := by positivity
  rw [suzukiFGammaFun, dslope_suzukiHalfInner_apply hγ hne]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_div, mul_pow, div_pow,
    Real.sq_sqrt hmnn]
  field_simp

/-- **Parseval's sum for the kernel.**  The squared values of the orthonormal family at `w` sum to
the diagonal value of the reproducing kernel. -/
theorem hasSum_normSq_suzukiFGammaFun (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun ρ : XiDivisorSupport =>
        ‖suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) w‖ ^ 2)
      ((suzukiModelKernel w w).re) := by
  have hpi := Real.pi_pos
  have hbase := (hasSum_xiSupport_mult_inv_normSq hRH hw).mul_left
    (‖suzukiHalfInner w‖ ^ 2 / Real.pi)
  have hval : (‖suzukiHalfInner w‖ ^ 2 / Real.pi) * (-((logDeriv XiC w).im) / w.im)
      = (suzukiModelKernel w w).re := by
    rw [suzukiModelKernel_self hw, Complex.ofReal_re,
      re_sub_normSq_suzukiHalfInner hRH hw]
    field_simp
  rw [hval] at hbase
  refine hbase.congr_fun ?_
  intro ρ
  exact normSq_suzukiFGammaFun_upper hRH ρ hw


end RHTower
