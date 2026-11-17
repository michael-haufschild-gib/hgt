import GaloisForLFunctions.CompactHyperbolicSurfaces.EntireSelbergZeta
import GaloisForLFunctions.HTGeometry.EulerLogTail
import GaloisForLFunctions.RHTower.ThetaRelativeSourceRigidity
import GaloisForLFunctions.ZeroForcingCalculus.WittMonomialsShiftedConvolutionsAndBrauerCancellation

/-!
# A Selberg shift quotient with nonnegative Euler logarithm

For the Selberg zeta of a compact surface, the quotient
`Z(s+ih) Z(s−ih) / Z(s)²` gives each primitive Euler factor the nonnegative logarithmic
coefficients `2(1−cos(nhℓ))/n`. Reflection exchanges the two shifts. In the open strip a real
exceptional zero produces two nonreal zeros of the same order and a pole of twice that order.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.ZeroForcingCalculus

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-- Symmetric vertical quotient at displacement `c`. -/
def shiftQuotient (f : ℂ → ℂ) (c s : ℂ) : ℂ := f (s + c) * f (s - c) / f s ^ 2

/-- Logarithmic Taylor coefficients of the quotient of one primitive Euler factor. -/
def shiftLogCoeff (θ : ℝ) (n : ℕ) : ℝ := 2 * (1 - Real.cos (n * θ)) / n

theorem shiftLogCoeff_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ shiftLogCoeff θ n :=
  div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))) (Nat.cast_nonneg _)

private def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * I)

private theorem norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

private theorem phase_pow_sum (θ : ℝ) (n : ℕ) :
    phase θ ^ n + phase (-θ) ^ n = 2 * (Real.cos (n * θ) : ℂ) := by
  rw [phase, phase, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- Exponentiating the positive coefficient series gives the local factor itself. -/
theorem exp_shiftEulerLog {z : ℂ} (hz : ‖z‖ < 1) (θ : ℝ) :
    Complex.exp (∑' n : ℕ, (shiftLogCoeff θ n : ℂ) * z ^ n) =
      (1 - z * phase θ) * (1 - z * phase (-θ)) / (1 - z) ^ 2 := by
  have hsmall (φ : ℝ) : ‖z * phase φ‖ < 1 := by simpa only [norm_mul, norm_phase, mul_one] using hz
  have hne {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hw
    exact lt_irrefl _ hw
  have h := HTGeometry.hasSum_neg_log_sub hz
  have hs := ((h.add h).sub (HTGeometry.hasSum_neg_log_sub (hsmall θ))).sub
    (HTGeometry.hasSum_neg_log_sub (hsmall (-θ)))
  have hsum : HasSum (fun n : ℕ => (shiftLogCoeff θ n : ℂ) * z ^ n) _ := by
    apply hs.congr_fun
    intro n
    simp only [shiftLogCoeff, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_natCast, mul_pow]
    linear_combination -(z ^ n / (n : ℂ)) * (phase_pow_sum θ n)
  rw [hsum.tsum_eq]
  simp only [sub_neg_eq_add, Complex.exp_add, Complex.exp_neg, Complex.exp_log (hne hz),
    Complex.exp_log (hne (hsmall θ)), Complex.exp_log (hne (hsmall (-θ)))]
  ring

namespace CompactQuotient

/-- The original local Euler variable at the primitive length and its integer translate. -/
def shiftEulerVariable (X : CompactQuotient) (x : X.PClass × ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-((s + x.2) * X.classLen x.1.1))

private theorem local_shift (X : CompactQuotient) (x : X.PClass × ℕ) (h : ℝ) (s : ℂ) :
    X.eulerFactor x (s + h * I) = 1 - X.shiftEulerVariable x s * phase (-(h * X.classLen x.1.1)) := by
  unfold eulerFactor shiftEulerVariable phase
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The product of exponentials of the nonnegative local logarithms converges to the quotient. -/
theorem hasProd_shiftEulerLog {X : CompactQuotient} (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|)
    (h : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun x : X.PClass × ℕ => Complex.exp (∑' n : ℕ,
      (shiftLogCoeff (h * X.classLen x.1.1) n : ℂ) * X.shiftEulerVariable x s ^ n))
      (shiftQuotient X.eulerZeta (h * I) s) := by
  have hp := hasProd_eulerZeta (X := X) hhyp (s := s + h * I) (by simpa using hs)
  have hm := hasProd_eulerZeta (X := X) hhyp (s := s - h * I) (by simpa using hs)
  have ho := hasProd_eulerZeta (X := X) hhyp hs
  have hn := eulerZeta_ne_zero (X := X) hhyp hs
  have hprod : HasProd (fun x => X.eulerFactor x (s + h * I) * X.eulerFactor x (s - h * I) /
      (X.eulerFactor x s * X.eulerFactor x s)) (shiftQuotient X.eulerZeta (h * I) s) := by
    unfold HasProd at *
    simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib, shiftQuotient, sq] using
      (hp.mul hm).div (ho.mul ho) (mul_ne_zero hn hn)
  apply hprod.congr
  intro x
  have hz : ‖X.shiftEulerVariable x s‖ < 1 := by
    rw [shiftEulerVariable, norm_eulerTerm]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos
      (add_pos_of_pos_of_nonneg (lt_trans zero_lt_one hs) (Nat.cast_nonneg _))
      (pLen_pos hhyp _)))
  have he := local_shift X x (-h) s
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, neg_neg] at he
  rw [exp_shiftEulerLog hz, local_shift, he]
  unfold eulerFactor shiftEulerVariable
  ring

/-- The multiplier in the Selberg reflection formula on the open strip. -/
def reflectionFactor (X : CompactQuotient) (s : ℂ) : ℂ :=
  Complex.exp (-(X.area * ∫ t in (0 : ℝ)..1, (s - 1 / 2) *
    (((t : ℂ) * (s - 1 / 2)) * Complex.tan (Real.pi * ((t : ℂ) * (s - 1 / 2))))))

end CompactQuotient

/-- Interior off-line points of the critical strip. -/
def inExceptionalStrip (s : ℂ) : Prop := 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2

private theorem exceptional_translate (s : ℂ) (h : ℝ) :
    inExceptionalStrip (s + h * I) ↔ inExceptionalStrip s := by simp [inExceptionalStrip]

private theorem exceptional_sub_translate (s : ℂ) (h : ℝ) :
    inExceptionalStrip (s - h * I) ↔ inExceptionalStrip s := by simp [inExceptionalStrip]

private theorem quotient_reflects {Z G : ℂ → ℂ} (hFE : ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Z (1 - s) = Z s * G s) (h : ℝ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    shiftQuotient Z (h * I) (1 - s) = shiftQuotient Z (h * I) s * shiftQuotient G (h * I) s := by
  unfold shiftQuotient
  rw [show 1 - s + h * I = 1 - (s - h * I) by ring,
    show 1 - s - h * I = 1 - (s + h * I) by ring,
    hFE _ (by simpa using h0) (by simpa using h1),
    hFE _ (by simpa using h0) (by simpa using h1), hFE _ h0 h1, mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem quotient_meromorphic {Z : ℂ → ℂ} (hd : Differentiable ℂ Z) (c s : ℂ) :
    MeromorphicAt (shiftQuotient Z c) s := by
  have hp : AnalyticAt ℂ (fun z => Z (z + c)) s := (hd.analyticAt _).comp (by fun_prop)
  have hm : AnalyticAt ℂ (fun z => Z (z - c)) s := (hd.analyticAt _).comp (by fun_prop)
  exact (hp.mul hm).meromorphicAt.div ((hd.analyticAt s).pow 2).meromorphicAt

/-- At a zero of the unshifted denominator the two nonzero shifted factors leave a genuine pole. -/
private theorem quotient_pole {Z : ℂ → ℂ} (hd : Differentiable ℂ Z) (hne : ∃ z, Z z ≠ 0)
    {s c : ℂ} (hz : Z s = 0) (hp : Z (s + c) ≠ 0) (hm : Z (s - c) ≠ 0) :
    meromorphicOrderAt (shiftQuotient Z c) s < 0 := by
  have hnum : AnalyticAt ℂ (fun z => Z (z + c) * Z (z - c)) s :=
    ((hd.analyticAt _).comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z + c) s)).mul
      ((hd.analyticAt _).comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - c) s))
  have hn := meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hnum (mul_ne_zero hp hm)
  have hpos := meromorphicOrderAt_pos_of_analyticAt_eq_zero (hd.analyticAt s) hz
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
    (_root_.RHTower.meromorphicOrderAt_ne_top_of_differentiable hd hne s)
  rw [← hk] at hpos
  have hkpos : 0 < k := by exact_mod_cast hpos
  change meromorphicOrderAt ((fun z => Z (z + c) * Z (z - c)) / Z ^ 2) s < 0
  rw [meromorphicOrderAt_div hnum.meromorphicAt ((hd.analyticAt s).meromorphicAt.pow 2), hn,
    meromorphicOrderAt_pow (hd.analyticAt s).meromorphicAt, ← hk]
  exact_mod_cast (by omega : (0 : ℤ) - 2 * k < 0)

private theorem quotient_divisor_sign {Z : ℂ → ℂ} (hd : Differentiable ℂ Z) (hne : ∃ z, Z z ≠ 0)
    (hreal : ∀ s, inExceptionalStrip s → Z s = 0 → s.im = 0)
    {s : ℂ} (hs : inExceptionalStrip s) {h : ℝ} (hh : 0 < h) :
    (0 < meromorphicOrderAt (shiftQuotient Z (h * I)) s ↔
      Z (s + h * I) = 0 ∨ Z (s - h * I) = 0) ∧
    (meromorphicOrderAt (shiftQuotient Z (h * I)) s < 0 ↔ Z s = 0) := by
  let c : ℂ := h * I
  by_cases hz : Z s = 0
  · have hIm := hreal s hs hz
    have hp : Z (s + h * I) ≠ 0 := fun hp => by
      have hi := hreal _ ((exceptional_translate s h).mpr hs) hp
      simp [hIm, hh.ne'] at hi
    have hm : Z (s - h * I) ≠ 0 := fun hm => by
      have hi := hreal _ ((exceptional_sub_translate s h).mpr hs) hm
      simp [hIm, hh.ne'] at hi
    have hneg := quotient_pole hd hne hz hp hm
    simp [not_lt.mpr hneg.le, hp, hm, hz, hneg]
  · have hq : AnalyticAt ℂ (shiftQuotient Z c) s := by
      have hP := (hd.analyticAt (s + c)).comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z + c) s)
      have hM := (hd.analyticAt (s - c)).comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - c) s)
      exact (hP.mul hM).div ((hd.analyticAt s).pow 2) (pow_ne_zero _ hz)
    by_cases hnum : Z (s + c) = 0 ∨ Z (s - c) = 0
    · have hzero : shiftQuotient Z c s = 0 := by
        simp only [shiftQuotient, div_eq_zero_iff, mul_eq_zero]; exact Or.inl hnum
      have hpos := meromorphicOrderAt_pos_of_analyticAt_eq_zero hq hzero
      exact ⟨iff_of_true hpos hnum, iff_of_false (not_lt.mpr hpos.le) hz⟩
    · have hunit : shiftQuotient Z c s ≠ 0 := div_ne_zero
          (mul_ne_zero (fun hp => hnum (Or.inl hp)) (fun hm => hnum (Or.inr hm))) (pow_ne_zero _ hz)
      have ho := meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hq hunit
      exact ⟨iff_of_false (by rw [← show c = h * I from rfl, ho]; exact lt_irrefl _) hnum,
        iff_of_false (by rw [← show c = h * I from rfl, ho]; exact lt_irrefl _) hz⟩

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
