import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.TraceHankelConverse
import GaloisForLFunctions.RHTower.CCMTwoPoleSourceCriterion
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Finite prime--Gamma contour Hermite criterion for RH

The continued Guinand--Weil source trace already recovers the multiplicity-weighted value of every
entire test on the Xi divisor inside an admissible rectangle.  This module chooses cofinal rectangles
symmetric about both axes and tests them with the translated Hermite polynomial

`z ↦ (R + 1 + z) * P(R + 1 + z)^2`.

Translation by `R + 1` puts every real point of the packet on the positive real axis.  The finite
trace--Hankel converse then shows that nonnegativity of all these source-contour values forces every
enclosed centered Xi zero to be real.  Cofinality closes the chain to RH.  The remaining input is a
source-side contour sign; no Xi zero enumeration or limiting spectral measure appears in it.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Translating a finite conjugation-closed spectrum does not weaken the finite trace--Hankel
reality detector. -/
theorem finite_shifted_traceHankel_nonneg_implies_real
    (F : Finset ℂ) (w : ℂ → ℝ) (A : ℝ)
    (hw : ∀ z ∈ F, 0 < w z)
    (hconj : ∀ z ∈ F, (starRingEnd ℂ) z ∈ F)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
        evalRealPolynomial p ((A : ℂ) + z) ^ 2).re) :
    ∀ z ∈ F, z.im = 0 := by
  let shift : ℂ → ℂ := fun z => (A : ℂ) + z
  let F' : Finset ℂ := F.image shift
  let w' : ℂ → ℝ := fun u => w (u - (A : ℂ))
  have hshift_inj : Set.InjOn shift F := by
    intro x hx y hy hxy
    dsimp only [shift] at hxy
    exact add_left_cancel hxy
  have hw' : ∀ u ∈ F', 0 < w' u := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    simpa [w', shift] using hw z hz
  have hconj' : ∀ u ∈ F', (starRingEnd ℂ) u ∈ F' := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    apply Finset.mem_image.mpr
    refine ⟨(starRingEnd ℂ) z, hconj z hz, ?_⟩
    simp [shift]
  have hpos' : ∀ p : Polynomial ℝ,
      0 ≤ (∑ u ∈ F', ((w' u : ℝ) : ℂ) * u *
        evalRealPolynomial p u ^ 2).re := by
    intro p
    change 0 ≤ (∑ u ∈ F.image shift, ((w' u : ℝ) : ℂ) * u *
      evalRealPolynomial p u ^ 2).re
    rw [Finset.sum_image hshift_inj]
    simpa [w', shift] using hpos p
  have hreal := finite_traceHankel_nonneg_implies_real F' w' hw' hconj' hpos'
  intro z hz
  have hs : shift z ∈ F' := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hzreal := hreal (shift z) hs
  simpa [shift] using hzreal

/-- Finite shifted trace--Hankel value as a quadratic function of a fixed-length coefficient
vector. -/
def finiteShiftedTraceHankelVector (F : Finset ℂ) (w : ℂ → ℝ) (A : ℝ)
    (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
    evalRealPolynomial (Polynomial.ofFn n a) ((A : ℂ) + z) ^ 2).re

private theorem evalRealPolynomial_ofFn_eq_sum (n : ℕ) (a : Fin n → ℝ) (z : ℂ) :
    evalRealPolynomial (Polynomial.ofFn n a) z =
      ∑ i : Fin n, ((a i : ℝ) : ℂ) * z ^ (i : ℕ) := by
  rw [evalRealPolynomial, Polynomial.ofFn_eq_sum_monomial]
  simp

/-- At fixed degree, the finite shifted trace--Hankel value is continuous in all real
coefficients. -/
theorem continuous_finiteShiftedTraceHankelVector
    (F : Finset ℂ) (w : ℂ → ℝ) (A : ℝ) (n : ℕ) :
    Continuous (finiteShiftedTraceHankelVector F w A n) := by
  rw [show finiteShiftedTraceHankelVector F w A n = fun a : Fin n → ℝ =>
      (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
        (∑ i : Fin n, ((a i : ℝ) : ℂ) * ((A : ℂ) + z) ^ (i : ℕ)) ^ 2).re by
    funext a
    simp only [finiteShiftedTraceHankelVector, evalRealPolynomial_ofFn_eq_sum]]
  fun_prop

/-- Homogeneity of the finite shifted trace--Hankel coefficient form. -/
theorem finiteShiftedTraceHankelVector_smul
    (F : Finset ℂ) (w : ℂ → ℝ) (A : ℝ)
    (n : ℕ) (c : ℝ) (a : Fin n → ℝ) :
    finiteShiftedTraceHankelVector F w A n (c • a) =
      c ^ 2 * finiteShiftedTraceHankelVector F w A n a := by
  have heval (z : ℂ) :
      evalRealPolynomial (Polynomial.ofFn n (c • a)) z =
        (c : ℂ) * evalRealPolynomial (Polynomial.ofFn n a) z := by
    rw [evalRealPolynomial_ofFn_eq_sum, evalRealPolynomial_ofFn_eq_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  simp only [finiteShiftedTraceHankelVector, heval]
  have hcomplex :
      (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
          ((c : ℂ) * evalRealPolynomial (Polynomial.ofFn n a) ((A : ℂ) + z)) ^ 2) =
        (((c ^ 2 : ℝ) : ℂ) *
          ∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
            evalRealPolynomial (Polynomial.ofFn n a) ((A : ℂ) + z) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    push_cast
    ring
  rw [hcomplex]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem denseRange_ratCast_fin (n : ℕ) :
    DenseRange (fun a : Fin n → ℚ => fun i => (a i : ℝ)) := by
  simpa [Pi.map_apply] using!
    (DenseRange.piMap (fun _ : Fin n => Rat.denseRange_cast))

/-- Integer-polynomial positivity already gives every real-polynomial finite shifted
trace--Hankel inequality. -/
theorem finite_shifted_traceHankel_nonnegative_of_int
    (F : Finset ℂ) (w : ℂ → ℝ) (A : ℝ)
    (hint : ∀ p : Polynomial ℤ,
      0 ≤ (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
        evalRealPolynomial (p.map (Int.castRingHom ℝ)) ((A : ℂ) + z) ^ 2).re) :
    ∀ p : Polynomial ℝ,
      0 ≤ (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
        evalRealPolynomial p ((A : ℂ) + z) ^ 2).re := by
  intro p
  let n := p.natDegree + 1
  let a : Fin n → ℝ := Polynomial.toFn n p
  have hp : Polynomial.ofFn n a = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have hclosed : IsClosed
      {x : Fin n → ℝ | 0 ≤ finiteShiftedTraceHankelVector F w A n x} :=
    isClosed_Ici.preimage (continuous_finiteShiftedTraceHankelVector F w A n)
  have hrat : ∀ q : Fin n → ℚ,
      0 ≤ finiteShiftedTraceHankelVector F w A n (fun i => (q i : ℝ)) := by
    intro q
    obtain ⟨D, hDpos, z, hz⟩ := exists_nat_pos_int_scale_rat_vector q
    let pz : Polynomial ℤ := Polynomial.ofFn n z
    have hpzmap : pz.map (Int.castRingHom ℝ) =
        Polynomial.ofFn n (fun i => (z i : ℝ)) := by
      ext k
      by_cases hk : k < n
      · simp [pz, hk]
      · have hnk : n ≤ k := Nat.le_of_not_gt hk
        simp [pz, hnk]
    have hzreal : (fun i => (z i : ℝ)) = fun i => (D : ℝ) * (q i : ℝ) := by
      funext i
      exact_mod_cast hz i
    have hscaled := hint pz
    rw [hpzmap] at hscaled
    change 0 ≤ finiteShiftedTraceHankelVector F w A n (fun i => (z i : ℝ)) at hscaled
    rw [hzreal, show (fun i => (D : ℝ) * (q i : ℝ)) =
        (D : ℝ) • (fun i => (q i : ℝ)) by rfl,
      finiteShiftedTraceHankelVector_smul] at hscaled
    have hDsq : 0 < (D : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hDpos)
    exact nonneg_of_mul_nonneg_right hscaled hDsq
  have hall : ∀ x : Fin n → ℝ,
      0 ≤ finiteShiftedTraceHankelVector F w A n x := by
    intro x
    exact (denseRange_ratCast_fin n).induction_on x hclosed hrat
  have ha := hall a
  rw [finiteShiftedTraceHankelVector, hp] at ha
  exact ha

/-- Countably many integer-polynomial tests suffice in the finite shifted trace--Hankel
reality detector. -/
theorem finite_shifted_traceHankel_int_nonneg_implies_real
    (F : Finset ℂ) (w : ℂ → ℝ) (A : ℝ)
    (hw : ∀ z ∈ F, 0 < w z)
    (hconj : ∀ z ∈ F, (starRingEnd ℂ) z ∈ F)
    (hpos : ∀ p : Polynomial ℤ,
      0 ≤ (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((A : ℂ) + z) *
        evalRealPolynomial (p.map (Int.castRingHom ℝ)) ((A : ℂ) + z) ^ 2).re) :
    ∀ z ∈ F, z.im = 0 :=
  finite_shifted_traceHankel_nonneg_implies_real F w A hw hconj
    (finite_shifted_traceHankel_nonnegative_of_int F w A hpos)

private theorem exists_ratCast_Ioo_not_mem_finset {a b : ℝ} (hab : a < b)
    (F : Finset ℝ) :
    ∃ x ∈ Set.Ioo a b, x ∉ F ∧ ∃ q : ℚ, x = (q : ℝ) := by
  let U : Set ℝ := Set.Ioo a b \ (F : Set ℝ)
  have hIoo : IsOpen (Set.Ioo a b) := _root_.isOpen_Ioo
  have hUopen : IsOpen U := IsOpen.sdiff hIoo F.finite_toSet.isClosed
  have hUinfinite : U.Infinite := (Set.Ioo_infinite hab).sdiff F.finite_toSet
  have hUne : U.Nonempty := hUinfinite.nonempty
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hUopen hUne
  refine ⟨(q : ℝ), hq.1, ?_, q, rfl⟩
  simpa using hq.2

/-- Lower-left corner of the rectangle `[-R,R] × [-c,c]`. -/
def symmetricRectangleLower (R c : ℝ) : ℂ := (-R : ℂ) - (c : ℂ) * I

/-- Upper-right corner of the rectangle `[-R,R] × [-c,c]`. -/
def symmetricRectangleUpper (R c : ℝ) : ℂ := (R : ℂ) + (c : ℂ) * I

/-- Every point on the four symmetric rectangle edges lies in the continued explicit-formula
domain. -/
def XiSymmetricRectangleExplicitAdmissible (R c : ℝ) : Prop :=
  (∀ x ∈ Set.uIcc (-R) R,
    XiExplicitAdmissible ((x : ℂ) - (c : ℂ) * I)) ∧
  (∀ x ∈ Set.uIcc (-R) R,
    XiExplicitAdmissible ((x : ℂ) + (c : ℂ) * I)) ∧
  (∀ y ∈ Set.uIcc (-c) c,
    XiExplicitAdmissible ((R : ℂ) + (y : ℂ) * I)) ∧
  (∀ y ∈ Set.uIcc (-c) c,
    XiExplicitAdmissible ((-R : ℂ) + (y : ℂ) * I))

/-- Every multiplicity copy of the Xi divisor lies strictly inside a symmetric rectangle whose
whole boundary is admissible for the continued prime--archimedean source formula. -/
theorem exists_admissible_symmetric_rectangle_containing_xiZeroCopy
    (q : XiZeroCopy) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ c < 1 / 2 ∧
      -R < (xiSpectralPoint q).re ∧ (xiSpectralPoint q).re < R ∧
      -c < (xiSpectralPoint q).im ∧ (xiSpectralPoint q).im < c ∧
      XiSymmetricRectangleExplicitAdmissible R c ∧
      ∃ Rq cq : ℚ, R = (Rq : ℝ) ∧ c = (cq : ℝ) := by
  classical
  let alpha : ℂ := xiSpectralPoint q
  have halphaIm : |alpha.im| < 1 / 2 := by
    rw [abs_lt]
    have h := xiSpectralPoint_im_mem_openHalf q
    change -(1 / 2 : ℝ) < (xiSpectralPoint q).im ∧
      (xiSpectralPoint q).im < 1 / 2
    norm_num at h ⊢
    exact h
  let R₀ : ℝ := |alpha.re| + 1
  let c₀ : ℝ := (|alpha.im| + 1 / 2) / 2
  let R₁ : ℝ := R₀ + 1
  let c₁ : ℝ := (c₀ + 1 / 2) / 2
  have hR₀pos : 0 < R₀ := by dsimp only [R₀]; positivity
  have hR₀R₁ : R₀ < R₁ := by dsimp only [R₁]; linarith
  have hc₀pos : 0 < c₀ := by dsimp only [c₀]; positivity
  have habsc₀ : |alpha.im| < c₀ := by
    dsimp only [c₀]
    linarith
  have hc₀half : c₀ < 1 / 2 := by
    dsimp only [c₀]
    linarith
  have hc₀c₁ : c₀ < c₁ := by dsimp only [c₁]; linarith
  have hc₁half : c₁ < 1 / 2 := by dsimp only [c₁]; linarith
  let raw₁ : ℂ := (-R₁ : ℂ) - (c₁ : ℂ) * I
  let raw₂ : ℂ := (R₁ : ℂ) + (c₁ : ℂ) * I
  let Z : Finset ℂ := xiCClosedRectangleZeros raw₁ raw₂
  let Fre : Finset ℝ := Z.image (fun z => |z.re|)
  let Fim : Finset ℝ := Z.image (fun z => |z.im|)
  obtain ⟨R, hRI, hRavoid, Rq, hRq⟩ :=
    exists_ratCast_Ioo_not_mem_finset hR₀R₁ Fre
  obtain ⟨c, hcI, hcavoid, cq, hcq⟩ :=
    exists_ratCast_Ioo_not_mem_finset hc₀c₁ Fim
  have hRpos : 0 < R := hR₀pos.trans hRI.1
  have hcpos : 0 < c := hc₀pos.trans hcI.1
  have hchalf : c < 1 / 2 := hcI.2.trans hc₁half
  have hraw_mem {z : ℂ} (hre : |z.re| ≤ R₁) (him : |z.im| ≤ c₁) :
      z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
    apply Complex.mem_reProdIm.mpr
    have hR₁pos : 0 < R₁ := hR₀pos.trans hR₀R₁
    have hc₁pos : 0 < c₁ := hc₀pos.trans hc₀c₁
    rw [Set.uIcc_of_le (by simp [raw₁, raw₂]; linarith),
      Set.uIcc_of_le (by simp [raw₁, raw₂]; linarith)]
    constructor
    · simpa [raw₁, raw₂] using (abs_le.mp hre)
    · simpa [raw₁, raw₂] using (abs_le.mp him)
  have hzero_mem_Z {z : ℂ}
      (hraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im))
      (hz : XiC z = 0) : z ∈ Z :=
    mem_xiCClosedRectangleZeros.mpr ⟨hraw, hz⟩
  have hbottomZero : ∀ x ∈ Set.uIcc (-R) R,
      XiC ((x : ℂ) - (c : ℂ) * I) ≠ 0 := by
    intro x hx hzero
    have hxI : -R ≤ x ∧ x ≤ R := by
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact hx
    let z : ℂ := (x : ℂ) - (c : ℂ) * I
    have hzraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
      apply hraw_mem
      · dsimp only [z]
        simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, zero_mul, I_im,
          mul_zero, sub_zero]
        rw [abs_le]
        constructor <;> linarith [hxI.1, hxI.2, hRI.2]
      · dsimp only [z]
        have hzIm : ((x : ℂ) - (c : ℂ) * I).im = -c := by
          simp [Complex.mul_im]
        rw [hzIm, abs_neg, abs_of_pos hcpos]
        exact le_of_lt hcI.2
    have hzZ := hzero_mem_Z hzraw hzero
    apply hcavoid
    exact Finset.mem_image.mpr ⟨z, hzZ, by simp [z, abs_of_pos hcpos]⟩
  have htopZero : ∀ x ∈ Set.uIcc (-R) R,
      XiC ((x : ℂ) + (c : ℂ) * I) ≠ 0 := by
    intro x hx hzero
    have hxI : -R ≤ x ∧ x ≤ R := by
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact hx
    let z : ℂ := (x : ℂ) + (c : ℂ) * I
    have hzraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
      apply hraw_mem
      · dsimp only [z]
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, zero_mul, I_im,
          mul_zero]
        rw [abs_le]
        constructor <;> linarith [hxI.1, hxI.2, hRI.2]
      · dsimp only [z]
        have hzIm : ((x : ℂ) + (c : ℂ) * I).im = c := by
          simp [Complex.mul_im]
        rw [hzIm, abs_of_pos hcpos]
        exact le_of_lt hcI.2
    have hzZ := hzero_mem_Z hzraw hzero
    apply hcavoid
    exact Finset.mem_image.mpr ⟨z, hzZ, by simp [z, abs_of_pos hcpos]⟩
  have hrightZero : ∀ y ∈ Set.uIcc (-c) c,
      XiC ((R : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -c ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    let z : ℂ := (R : ℂ) + (y : ℂ) * I
    have hzraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
      apply hraw_mem
      · dsimp only [z]
        have hzRe : ((R : ℂ) + (y : ℂ) * I).re = R := by
          simp [Complex.mul_re]
        rw [hzRe, abs_of_pos hRpos]
        exact le_of_lt hRI.2
      · dsimp only [z]
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
          zero_mul, zero_add]
        rw [abs_le]
        constructor <;> linarith [hyI.1, hyI.2, hcI.2]
    have hzZ := hzero_mem_Z hzraw hzero
    apply hRavoid
    exact Finset.mem_image.mpr ⟨z, hzZ, by simp [z, abs_of_pos hRpos]⟩
  have hleftZero : ∀ y ∈ Set.uIcc (-c) c,
      XiC ((-R : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -c ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    let z : ℂ := (-R : ℂ) + (y : ℂ) * I
    have hzraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
      apply hraw_mem
      · dsimp only [z]
        have hzRe : ((-R : ℂ) + (y : ℂ) * I).re = -R := by
          simp [Complex.mul_re]
        rw [hzRe, abs_neg, abs_of_pos hRpos]
        exact le_of_lt hRI.2
      · dsimp only [z]
        simp only [add_im, neg_im, ofReal_im, neg_zero, mul_im, ofReal_re, I_im,
          mul_one, I_re, zero_mul, zero_add]
        rw [abs_le]
        constructor <;> linarith [hyI.1, hyI.2, hcI.2]
    have hzZ := hzero_mem_Z hzraw hzero
    apply hRavoid
    exact Finset.mem_image.mpr ⟨z, hzZ, by simp [z, abs_of_pos hRpos]⟩
  have hne_one_of_im_ne {z : ℂ} (hzim : z.im ≠ -1 / 2) :
      (1 / 2 + z * I) ≠ 1 := by
    intro h
    have hreEq := congrArg Complex.re h
    simp [Complex.mul_re] at hreEq
    apply hzim
    linarith
  have hne_one_of_re_ne_zero {z : ℂ} (hzre : z.re ≠ 0) :
      (1 / 2 + z * I) ≠ 1 := by
    intro h
    have himEq := congrArg Complex.im h
    simp [Complex.mul_im] at himEq
    exact hzre himEq
  have hbottomAdm : ∀ x ∈ Set.uIcc (-R) R,
      XiExplicitAdmissible ((x : ℂ) - (c : ℂ) * I) := by
    intro x hx
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp; linarith
    · apply hne_one_of_im_ne
      simp
      linarith
    · exact hbottomZero x hx
  have htopAdm : ∀ x ∈ Set.uIcc (-R) R,
      XiExplicitAdmissible ((x : ℂ) + (c : ℂ) * I) := by
    intro x hx
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      norm_num at hchalf ⊢
      exact hchalf
    · apply hne_one_of_im_ne
      simp
      linarith
    · exact htopZero x hx
  have hrightAdm : ∀ y ∈ Set.uIcc (-c) c,
      XiExplicitAdmissible ((R : ℂ) + (y : ℂ) * I) := by
    intro y hy
    have hyI : -c ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      norm_num at hchalf ⊢
      exact hyI.2.trans_lt hchalf
    · apply hne_one_of_re_ne_zero
      simp [ne_of_gt hRpos]
    · exact hrightZero y hy
  have hleftAdm : ∀ y ∈ Set.uIcc (-c) c,
      XiExplicitAdmissible ((-R : ℂ) + (y : ℂ) * I) := by
    intro y hy
    have hyI : -c ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      norm_num at hchalf ⊢
      exact hyI.2.trans_lt hchalf
    · apply hne_one_of_re_ne_zero
      simp [ne_of_gt hRpos]
    · exact hleftZero y hy
  have halphaRe : |alpha.re| < R := by
    dsimp only [R₀] at hRI
    exact (lt_add_one |alpha.re|).trans hRI.1
  have halphaIm' : |alpha.im| < c := habsc₀.trans hcI.1
  refine ⟨R, c, hRpos, hcpos, hchalf, ?_, ?_, ?_, ?_, ?_, Rq, cq, hRq, hcq⟩
  · rw [show xiSpectralPoint q = alpha from rfl]
    exact (abs_lt.mp halphaRe).1
  · rw [show xiSpectralPoint q = alpha from rfl]
    exact (abs_lt.mp halphaRe).2
  · rw [show xiSpectralPoint q = alpha from rfl]
    exact (abs_lt.mp halphaIm').1
  · rw [show xiSpectralPoint q = alpha from rfl]
    exact (abs_lt.mp halphaIm').2
  · exact ⟨hbottomAdm, htopAdm, hrightAdm, hleftAdm⟩

/-- Rational endpoints already suffice for the cofinal admissible symmetric-rectangle selector. -/
theorem exists_admissible_rational_symmetric_rectangle_containing_xiZeroCopy
    (q : XiZeroCopy) :
    ∃ R c : ℚ, 0 < (R : ℝ) ∧ 0 < (c : ℝ) ∧ (c : ℝ) < 1 / 2 ∧
      -(R : ℝ) < (xiSpectralPoint q).re ∧ (xiSpectralPoint q).re < (R : ℝ) ∧
      -(c : ℝ) < (xiSpectralPoint q).im ∧ (xiSpectralPoint q).im < (c : ℝ) ∧
      XiSymmetricRectangleExplicitAdmissible (R : ℝ) (c : ℝ) := by
  obtain ⟨R, c, hR, hc, hchalf, hqreL, hqreR, hqimL, hqimR, hadm,
      Rq, cq, hRq, hcq⟩ :=
    exists_admissible_symmetric_rectangle_containing_xiZeroCopy q
  subst R
  subst c
  exact ⟨Rq, cq, hR, hc, hchalf, hqreL, hqreR, hqimL, hqimR, hadm⟩

/-- Entire Hermite test translated to the positive side of a symmetric rectangle. -/
def xiSymmetricRectangleHermiteTest (R : ℝ) (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  ((((R + 1 : ℝ) : ℂ) + z) *
    evalRealPolynomial p (((R + 1 : ℝ) : ℂ) + z) ^ 2)

/-- The translated Hermite test is entire. -/
theorem xiSymmetricRectangleHermiteTest_analyticOnNhd (R : ℝ) (p : Polynomial ℝ) :
    AnalyticOnNhd ℂ (xiSymmetricRectangleHermiteTest R p) Set.univ := by
  have hshift : Differentiable ℂ (fun z : ℂ => (((R + 1 : ℝ) : ℂ) + z)) :=
    (differentiable_const _).add differentiable_id
  have hpoly : Differentiable ℂ
      (fun z : ℂ => evalRealPolynomial p (((R + 1 : ℝ) : ℂ) + z)) :=
    (Polynomial.differentiable (p.map (algebraMap ℝ ℂ))).comp hshift
  exact (hshift.mul (hpoly.pow 2)).differentiableOn.analyticOnNhd isOpen_univ

/-- Exact finite value relation: the normalized continued prime--Gamma contour of a translated
Hermite test is the multiplicity-weighted trace--Hankel value of the enclosed Xi divisor packet. -/
theorem normalized_symmetricPrimeArchHermiteContour_eq_closedRectangleTraceHankel
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hadm : XiSymmetricRectangleExplicitAdmissible R c) (p : Polynomial ℝ) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        rectIntegral
          (fun z => xiSymmetricRectangleHermiteTest R p z *
            continuedPrimeArchSourceRelativeTrace z)
          (symmetricRectangleLower R c) (symmetricRectangleUpper R c) =
      ∑ z ∈ xiCClosedRectangleZeros (symmetricRectangleLower R c)
          (symmetricRectangleUpper R c),
        ((analyticOrderAt XiC z).toNat : ℂ) * (((R + 1 : ℝ) : ℂ) + z) *
          evalRealPolynomial p (((R + 1 : ℝ) : ℂ) + z) ^ 2 := by
  let z₁ := symmetricRectangleLower R c
  let z₂ := symmetricRectangleUpper R c
  have hzre : z₁.re < z₂.re := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have hzim : z₁.im < z₂.im := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have hbottom : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I) := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-R) R := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hx
    simpa [z₁, symmetricRectangleLower, sub_eq_add_neg] using! hadm.1 x hx'
  have htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I) := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-R) R := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hx
    simpa [z₂, symmetricRectangleUpper] using hadm.2.1 x hx'
  have hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-c) c := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hy
    simpa [z₂, symmetricRectangleUpper] using hadm.2.2.1 y hy'
  have hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-c) c := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hy
    simpa [z₁, symmetricRectangleLower] using hadm.2.2.2 y hy'
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
      (xiSymmetricRectangleHermiteTest_analyticOnNhd R p)
      hzre hzim hbottom htop hright hleft
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  change (2 * Real.pi * I : ℂ)⁻¹ *
      rectIntegral
        (fun z => xiSymmetricRectangleHermiteTest R p z *
          continuedPrimeArchSourceRelativeTrace z) z₁ z₂ = _
  rw [hcontour]
  rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [xiSymmetricRectangleHermiteTest]
  push_cast
  ring

/-- Source-pure finite Hermite positivity on every admissible symmetric prime--Gamma contour. -/
def XiSymmetricPrimeArchTraceHankelNonnegative : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → c < 1 / 2 →
    XiSymmetricRectangleExplicitAdmissible R c →
    ∀ p : Polynomial ℝ,
      0 ≤ (((2 * Real.pi * I : ℂ)⁻¹ *
        rectIntegral
          (fun z => xiSymmetricRectangleHermiteTest R p z *
            continuedPrimeArchSourceRelativeTrace z)
          (symmetricRectangleLower R c) (symmetricRectangleUpper R c)).re)

/-- A countable source test family: rational symmetric rectangles and integer Hermite
polynomials. -/
def XiCountableSymmetricPrimeArchTraceHankelNonnegative : Prop :=
  ∀ (R c : ℚ), 0 < (R : ℝ) → 0 < (c : ℝ) → (c : ℝ) < 1 / 2 →
    XiSymmetricRectangleExplicitAdmissible (R : ℝ) (c : ℝ) →
    ∀ p : Polynomial ℤ,
      0 ≤ (((2 * Real.pi * I : ℂ)⁻¹ *
        rectIntegral
          (fun z => xiSymmetricRectangleHermiteTest (R : ℝ)
              (p.map (Int.castRingHom ℝ)) z *
            continuedPrimeArchSourceRelativeTrace z)
          (symmetricRectangleLower (R : ℝ) (c : ℝ))
          (symmetricRectangleUpper (R : ℝ) (c : ℝ))).re)

/-- The Xi zero packet in a symmetric rectangle is closed under ordinary conjugation. -/
theorem symmetricRectangleZeros_conj_closed
    {R c : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c) :
    ∀ z ∈ xiCClosedRectangleZeros (symmetricRectangleLower R c)
        (symmetricRectangleUpper R c),
      (starRingEnd ℂ) z ∈ xiCClosedRectangleZeros (symmetricRectangleLower R c)
        (symmetricRectangleUpper R c) := by
  intro z hz
  obtain ⟨hzK, hz0⟩ := mem_xiCClosedRectangleZeros.mp hz
  apply mem_xiCClosedRectangleZeros.mpr
  constructor
  · apply Complex.mem_reProdIm.mpr
    obtain ⟨hzre, hzim⟩ := Complex.mem_reProdIm.mp hzK
    have hre : (symmetricRectangleLower R c).re ≤
        (symmetricRectangleUpper R c).re := by
      simp [symmetricRectangleLower, symmetricRectangleUpper]
      linarith
    have him : (symmetricRectangleLower R c).im ≤
        (symmetricRectangleUpper R c).im := by
      simp [symmetricRectangleLower, symmetricRectangleUpper]
      linarith
    rw [Set.uIcc_of_le hre] at hzre
    rw [Set.uIcc_of_le him] at hzim
    rw [Set.uIcc_of_le hre, Set.uIcc_of_le him]
    have hzre' : -R ≤ z.re ∧ z.re ≤ R := by
      simpa [symmetricRectangleLower, symmetricRectangleUpper] using hzre
    have hzim' : -c ≤ z.im ∧ z.im ≤ c := by
      simpa [symmetricRectangleLower, symmetricRectangleUpper] using hzim
    constructor
    · simpa [symmetricRectangleLower, symmetricRectangleUpper] using hzre'
    · have hcj : -c ≤ -z.im ∧ -z.im ≤ c := by
        constructor <;> linarith [hzim'.1, hzim'.2]
      simpa [symmetricRectangleLower, symmetricRectangleUpper] using hcj
  · rw [XiC_conj, hz0, map_zero]

/-- The finite, source-contour Hermite condition forces RH. -/
theorem riemannHypothesis_of_symmetricPrimeArchTraceHankelNonnegative
    (hsource : XiSymmetricPrimeArchTraceHankelNonnegative) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  obtain ⟨R, c, hR, hc, hchalf, hqreL, hqreR, hqimL, hqimR, hadm, _⟩ :=
    exists_admissible_symmetric_rectangle_containing_xiZeroCopy q
  let z₁ := symmetricRectangleLower R c
  let z₂ := symmetricRectangleUpper R c
  let F := xiCClosedRectangleZeros z₁ z₂
  let w : ℂ → ℝ := fun z => ((analyticOrderAt XiC z).toNat : ℝ)
  have hzre : z₁.re < z₂.re := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have hzim : z₁.im < z₂.im := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have hw : ∀ z ∈ F, 0 < w z := by
    intro z hz
    have hz0 : XiC z = 0 := (mem_xiCClosedRectangleZeros.mp hz).2
    have hmult := xiSpectralMultiplicity_pos_of_XiC_eq_zero hz0
    rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hz0] at hmult
    change (0 : ℝ) < ((analyticOrderAt XiC z).toNat : ℝ)
    exact_mod_cast hmult
  have hconj : ∀ z ∈ F, (starRingEnd ℂ) z ∈ F := by
    intro z hz
    exact symmetricRectangleZeros_conj_closed hR.le hc.le z hz
  have hbottom : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I) := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-R) R := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hx
    simpa [z₁, symmetricRectangleLower, sub_eq_add_neg] using! hadm.1 x hx'
  have htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I) := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-R) R := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hx
    simpa [z₂, symmetricRectangleUpper] using hadm.2.1 x hx'
  have hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-c) c := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hy
    simpa [z₂, symmetricRectangleUpper] using hadm.2.2.1 y hy'
  have hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-c) c := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hy
    simpa [z₁, symmetricRectangleLower] using hadm.2.2.2 y hy'
  have hpos : ∀ p : Polynomial ℝ,
      0 ≤ (∑ z ∈ F, ((w z : ℝ) : ℂ) * (((R + 1 : ℝ) : ℂ) + z) *
        evalRealPolynomial p (((R + 1 : ℝ) : ℂ) + z) ^ 2).re := by
    intro p
    have hcontour :=
      rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
        (xiSymmetricRectangleHermiteTest_analyticOnNhd R p)
        hzre hzim hbottom htop hright hleft
    have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact_mod_cast Real.pi_ne_zero
      · exact I_ne_zero
    have hnormalized :
        (2 * Real.pi * I : ℂ)⁻¹ *
            rectIntegral
              (fun z => xiSymmetricRectangleHermiteTest R p z *
                continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
          ∑ z ∈ F, ((w z : ℝ) : ℂ) * (((R + 1 : ℝ) : ℂ) + z) *
            evalRealPolynomial p (((R + 1 : ℝ) : ℂ) + z) ^ 2 := by
      rw [hcontour]
      rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [xiSymmetricRectangleHermiteTest, w]
      push_cast
      ring
    rw [← hnormalized]
    exact hsource R c hR hc hchalf hadm p
  have hreal := finite_shifted_traceHankel_nonneg_implies_real
    F w (R + 1) hw hconj hpos
  have hqF : xiSpectralPoint q ∈ F := by
    apply mem_xiCClosedRectangleZeros.mpr
    constructor
    · apply Complex.mem_reProdIm.mpr
      rw [Set.uIcc_of_le hzre.le, Set.uIcc_of_le hzim.le]
      dsimp only [z₁, z₂]
      simpa [symmetricRectangleLower, symmetricRectangleUpper] using
        And.intro (And.intro hqreL.le hqreR.le) (And.intro hqimL.le hqimR.le)
    · exact XiC_xiSpectralPoint_eq_zero q
  have himzero := hreal (xiSpectralPoint q) hqF
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using himzero

/-- The countable rational-rectangle, integer-polynomial continued prime--Gamma contour family
already forces RH. -/
theorem riemannHypothesis_of_countableSymmetricPrimeArchTraceHankelNonnegative
    (hsource : XiCountableSymmetricPrimeArchTraceHankelNonnegative) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  obtain ⟨R, c, hR, hc, hchalf, hqreL, hqreR, hqimL, hqimR, hadm⟩ :=
    exists_admissible_rational_symmetric_rectangle_containing_xiZeroCopy q
  have hRrat : 0 < R := by exact_mod_cast hR
  have hcrat : 0 < c := by exact_mod_cast hc
  let z₁ := symmetricRectangleLower (R : ℝ) (c : ℝ)
  let z₂ := symmetricRectangleUpper (R : ℝ) (c : ℝ)
  let F := xiCClosedRectangleZeros z₁ z₂
  let w : ℂ → ℝ := fun z => ((analyticOrderAt XiC z).toNat : ℝ)
  have hzre : z₁.re < z₂.re := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith [hRrat]
  have hzim : z₁.im < z₂.im := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith [hcrat]
  have hw : ∀ z ∈ F, 0 < w z := by
    intro z hz
    have hz0 : XiC z = 0 := (mem_xiCClosedRectangleZeros.mp hz).2
    have hmult := xiSpectralMultiplicity_pos_of_XiC_eq_zero hz0
    rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hz0] at hmult
    change (0 : ℝ) < ((analyticOrderAt XiC z).toNat : ℝ)
    exact_mod_cast hmult
  have hconj : ∀ z ∈ F, (starRingEnd ℂ) z ∈ F := by
    intro z hz
    exact symmetricRectangleZeros_conj_closed hR.le hc.le z hz
  have hpos : ∀ p : Polynomial ℤ,
      0 ≤ (∑ z ∈ F, ((w z : ℝ) : ℂ) * ((((R : ℝ) + 1 : ℝ) : ℂ) + z) *
        evalRealPolynomial (p.map (Int.castRingHom ℝ))
          (((((R : ℝ) + 1 : ℝ) : ℂ) + z)) ^ 2).re := by
    intro p
    have hs := hsource R c hR hc hchalf hadm p
    have heq :=
      normalized_symmetricPrimeArchHermiteContour_eq_closedRectangleTraceHankel
        hR hc hadm (p.map (Int.castRingHom ℝ))
    rw [heq] at hs
    simpa [F, w, z₁, z₂] using hs
  have hreal := finite_shifted_traceHankel_int_nonneg_implies_real
    F w ((R : ℝ) + 1) hw hconj hpos
  have hqF : xiSpectralPoint q ∈ F := by
    apply mem_xiCClosedRectangleZeros.mpr
    constructor
    · apply Complex.mem_reProdIm.mpr
      rw [Set.uIcc_of_le hzre.le, Set.uIcc_of_le hzim.le]
      dsimp only [z₁, z₂]
      simpa [symmetricRectangleLower, symmetricRectangleUpper] using
        And.intro (And.intro hqreL.le hqreR.le) (And.intro hqimL.le hqimR.le)
    · exact XiC_xiSpectralPoint_eq_zero q
  have himzero := hreal (xiSpectralPoint q) hqF
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using himzero

/-- Under RH every enclosed centered Xi zero is real.  The translated Hermite coordinate is then
positive on the whole symmetric rectangle, so the exact contour/value identity makes every real
polynomial test nonnegative. -/
theorem symmetricPrimeArchTraceHankelNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiSymmetricPrimeArchTraceHankelNonnegative := by
  intro R c hR hc _hchalf hadm p
  rw [normalized_symmetricPrimeArchHermiteContour_eq_closedRectangleTraceHankel
    hR hc hadm p]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro z hz
  have hz0 : XiC z = 0 := (mem_xiCClosedRectangleZeros.mp hz).2
  let rho : XiDivisorSupport :=
    ⟨1 / 2 + z * I, mem_xi_divisor_support_of_eq_zero (by simpa [XiC] using hz0)⟩
  have hrho := xi_divisor_support_re_eq_half_of_rh hRH rho
  have hzim : z.im = 0 := by
    dsimp only [rho] at hrho
    norm_num [Complex.div_re, Complex.mul_re] at hrho
    linarith
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hzim
  have hzmem := (mem_xiCClosedRectangleZeros.mp hz).1
  have hzre : -R ≤ z.re := by
    obtain ⟨hzre, _hzim⟩ := Complex.mem_reProdIm.mp hzmem
    have hbounds : z.re ∈ Set.uIcc (-R) R := by
      simpa [symmetricRectangleLower, symmetricRectangleUpper] using hzre
    rw [Set.uIcc_of_le (by linarith)] at hbounds
    exact hbounds.1
  have hshiftpos : 0 < R + 1 + z.re := by linarith
  rw [hzreal]
  have hshift : (((R + 1 : ℝ) : ℂ) + (z.re : ℂ)) =
      ((R + 1 + z.re : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hshift, evalRealPolynomial_ofReal]
  have hterm :
      ((analyticOrderAt XiC (z.re : ℂ)).toNat : ℂ) *
          ((R + 1 + z.re : ℝ) : ℂ) *
          (((Polynomial.eval (R + 1 + z.re) p : ℝ) : ℂ)) ^ 2 =
        (((analyticOrderAt XiC (z.re : ℂ)).toNat : ℝ) *
          (R + 1 + z.re) * (Polynomial.eval (R + 1 + z.re) p) ^ 2 : ℝ) := by
    push_cast
    ring
  rw [hterm]
  simp only [Complex.ofReal_re]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hshiftpos.le) (sq_nonneg _)

/-- The rational-rectangle, integer-polynomial interface is a literal specialization of the full
finite Hermite source-sign condition. -/
theorem countableSymmetricPrimeArchTraceHankelNonnegative_of_full
    (hfull : XiSymmetricPrimeArchTraceHankelNonnegative) :
    XiCountableSymmetricPrimeArchTraceHankelNonnegative := by
  intro R c hR hc hchalf hadm p
  exact hfull (R : ℝ) (c : ℝ) hR hc hchalf hadm
    (p.map (Int.castRingHom ℝ))

/-- RH discharges the countable symmetric source-contour interface. -/
theorem countableSymmetricPrimeArchTraceHankelNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCountableSymmetricPrimeArchTraceHankelNonnegative :=
  countableSymmetricPrimeArchTraceHankelNonnegative_of_full
    (symmetricPrimeArchTraceHankelNonnegative_of_riemannHypothesis hRH)

/-- **Exact finite-Hermite RH law.** -/
theorem symmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis :
    XiSymmetricPrimeArchTraceHankelNonnegative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_symmetricPrimeArchTraceHankelNonnegative,
    symmetricPrimeArchTraceHankelNonnegative_of_riemannHypothesis⟩

/-- **Exact countable finite-Hermite RH law.** -/
theorem countableSymmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis :
    XiCountableSymmetricPrimeArchTraceHankelNonnegative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_countableSymmetricPrimeArchTraceHankelNonnegative,
    countableSymmetricPrimeArchTraceHankelNonnegative_of_riemannHypothesis⟩

end

end RHTower
