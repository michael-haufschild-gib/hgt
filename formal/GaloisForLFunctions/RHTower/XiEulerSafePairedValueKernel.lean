import GaloisForLFunctions.RHTower.XiEulerSafePairedClosure
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate

/-!
# The exact absolute-Euler paired value kernel

The Weil polarization of two centred Cauchy tests is a divided difference of the Xi relative
resolvent trace, and that trace is the centred logarithmic derivative.  Schwarz conjugation and
evenness of the centred Xi function collapse the four blocks of a Schwarz-paired pole into one
block and one reflected block together with their conjugates, so the paired Weil kernel is twice
the real part of an explicit difference of two divided differences.

Every value entering the kernel is taken at a point of absolute Euler convergence, so no
meromorphic continuation into the critical strip is used.
-/

open Complex

namespace RHTower

noncomputable section

local notation "XiLp" => lp (fun _ : XiZeroCopy => ℂ) 2

/-! ## Regularity and separation on the absolute-Euler quadrant -/

theorem XiC_conj_xiEulerCentered_ne_zero {w : ℂ} (hw : 1 / 2 < w.re) :
    XiC ((starRingEnd ℂ) (xiEulerCentered w)) ≠ 0 := by
  have hre : 1 / 2 < ((starRingEnd ℂ) w).re := by simpa using hw
  have h : (starRingEnd ℂ) (xiEulerCentered w) = -xiEulerCentered ((starRingEnd ℂ) w) := by
    rw [xiEulerCentered_conj]; ring
  rw [h, XiC_even]
  exact XiC_xiEulerCentered_ne_zero hre

/-- Two absolute-Euler poles are never Schwarz reflections of one another. -/
theorem xiEulerCentered_ne_conj {a b : ℂ} (ha : 1 / 2 < a.re) (hb : 1 / 2 < b.re) :
    xiEulerCentered a ≠ (starRingEnd ℂ) (xiEulerCentered b) := by
  intro h
  rw [xiEulerCentered, xiEulerCentered, map_mul, map_neg, Complex.conj_I] at h
  have key : a + (starRingEnd ℂ) b = 0 := by
    linear_combination Complex.I * h + (a + (starRingEnd ℂ) b) * Complex.I_mul_I
  have hre := congrArg Complex.re key
  rw [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
  linarith

/-! ## Trace symmetries -/

/-- The centred Xi relative trace is odd. -/
theorem xiRelativeResolventTrace_neg {z : ℂ} (hz : XiC z ≠ 0) :
    xiRelativeResolventTrace (-z) = -xiRelativeResolventTrace z := by
  have hneg : XiC (-z) ≠ 0 := by rw [XiC_even]; exact hz
  rw [← logDeriv_XiC_eq_relativeResolventTrace hneg, logDeriv_XiC_neg,
    logDeriv_XiC_eq_relativeResolventTrace hz]

/-- The absolute-Euler logarithmic derivative `L(w) = X'(w)/X(w)` of `X(w) = xi(1/2+w)`. -/
def xiEulerLogDeriv (w : ℂ) : ℂ :=
  -Complex.I * xiRelativeResolventTrace (xiEulerCentered w)

theorem xiRelativeResolventTrace_eulerCentered (w : ℂ) :
    xiRelativeResolventTrace (xiEulerCentered w) = Complex.I * xiEulerLogDeriv w := by
  rw [xiEulerLogDeriv, ← mul_assoc,
    show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I]; ring, one_mul]

theorem trace_conj_eulerCentered (w : ℂ) :
    xiRelativeResolventTrace ((starRingEnd ℂ) (xiEulerCentered w)) =
      (starRingEnd ℂ) (Complex.I * xiEulerLogDeriv w) := by
  rw [xiRelativeResolventTrace_conj, xiRelativeResolventTrace_eulerCentered]

theorem trace_conj_eulerCentered_conj {w : ℂ} (hw : 1 / 2 < w.re) :
    xiRelativeResolventTrace ((starRingEnd ℂ) (xiEulerCentered ((starRingEnd ℂ) w))) =
      -(Complex.I * xiEulerLogDeriv w) := by
  have h : (starRingEnd ℂ) (xiEulerCentered ((starRingEnd ℂ) w)) = -xiEulerCentered w := by
    rw [xiEulerCentered_conj, map_neg, Complex.conj_conj]
  rw [h, xiRelativeResolventTrace_neg (XiC_xiEulerCentered_ne_zero hw),
    xiRelativeResolventTrace_eulerCentered]

theorem trace_eulerCentered_conj {u : ℂ} (hu : 1 / 2 < u.re) :
    xiRelativeResolventTrace (xiEulerCentered ((starRingEnd ℂ) u)) =
      -(starRingEnd ℂ) (Complex.I * xiEulerLogDeriv u) := by
  rw [xiEulerCentered_conj, xiRelativeResolventTrace_neg (XiC_conj_xiEulerCentered_ne_zero hu),
    trace_conj_eulerCentered]

/-! ## The four blocks -/

theorem inner_lineConj_cauchyLp {z v : ℂ} (hz : XiC z ≠ 0) (hv : XiC v ≠ 0)
    (hcz : XiC ((starRingEnd ℂ) z) ≠ 0) (hsep : v ≠ (starRingEnd ℂ) z) :
    inner ℂ (xiWeilLineConjLp (xiWeilCauchyLp ⟨z, hz⟩)) (xiWeilCauchyLp ⟨v, hv⟩) =
      (xiRelativeResolventTrace ((starRingEnd ℂ) z) - xiRelativeResolventTrace v) /
        (v - (starRingEnd ℂ) z) := by
  rw [xiWeilCauchyLp, xiWeilCauchyLp, inner_xiWeilLineConjLp_evaluation_eq_polarization,
    xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference hv hcz hsep]

/-- The paired vector with both poles in centred form. -/
theorem xiEulerPairedCauchyLp_eq_centered {w : ℂ} (hw : 1 / 2 < w.re) :
    xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero hw)
        (XiC_neg_conj_xiEulerCentered_ne_zero hw) =
      xiWeilCauchyLp ⟨xiEulerCentered w, XiC_xiEulerCentered_ne_zero hw⟩ -
        xiWeilCauchyLp ⟨xiEulerCentered ((starRingEnd ℂ) w),
          XiC_xiEulerCentered_ne_zero (by simpa using hw)⟩ := by
  rw [xiEulerPairedCauchyLp]
  congr 1
  congr 1
  exact Subtype.ext (xiEulerCentered_conj w).symm

/-! ## The kernel -/

/-- **Equation `(14)`.**  The exact absolute-Euler paired value kernel. -/
def xiEulerPairedKernel (w u : ℂ) : ℝ :=
  2 * ((xiEulerLogDeriv w + (starRingEnd ℂ) (xiEulerLogDeriv u)) / (w + (starRingEnd ℂ) u) -
        (xiEulerLogDeriv w + xiEulerLogDeriv u) / (w + u)).re

/-! ## The two-node identity -/

theorem add_ne_zero_of_half_lt_re {a b : ℂ} (ha : 1 / 2 < a.re) (hb : 1 / 2 < b.re) :
    a + b ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.zero_re] at hre
  linarith

theorem negI_div_negI (a b : ℂ) :
    (-Complex.I * a) / (-Complex.I * b) = a / b :=
  mul_div_mul_left a b (neg_ne_zero.mpr Complex.I_ne_zero)

theorem xiEulerCentered_sub_conj (a b : ℂ) :
    xiEulerCentered a - (starRingEnd ℂ) (xiEulerCentered b) =
      -Complex.I * (a + (starRingEnd ℂ) b) := by
  rw [xiEulerCentered, xiEulerCentered, map_mul, map_neg, Complex.conj_I]
  ring

/-- **Equation `(15)`, two-node form.**  The reflected Hermitian product of two absolute-Euler
paired Cauchy vectors has real part the paired value kernel. -/
theorem inner_lineConj_xiEulerPaired {w u : ℂ} (hw : 1 / 2 < w.re) (hu : 1 / 2 < u.re) :
    (inner ℂ (xiWeilLineConjLp (xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero hw)
        (XiC_neg_conj_xiEulerCentered_ne_zero hw)))
      (xiEulerPairedCauchyLp u (XiC_xiEulerCentered_ne_zero hu)
        (XiC_neg_conj_xiEulerCentered_ne_zero hu))).re = xiEulerPairedKernel w u := by
  have hwc : 1 / 2 < ((starRingEnd ℂ) w).re := by simpa using hw
  have huc : 1 / 2 < ((starRingEnd ℂ) u).re := by simpa using hu
  set A : ℂ := xiEulerLogDeriv w with hA
  set B : ℂ := xiEulerLogDeriv u with hB
  have hb1 : inner ℂ (xiWeilLineConjLp
        (xiWeilCauchyLp ⟨xiEulerCentered w, XiC_xiEulerCentered_ne_zero hw⟩))
        (xiWeilCauchyLp ⟨xiEulerCentered u, XiC_xiEulerCentered_ne_zero hu⟩) =
      ((starRingEnd ℂ) A + B) / (u + (starRingEnd ℂ) w) := by
    rw [inner_lineConj_cauchyLp _ _ (XiC_conj_xiEulerCentered_ne_zero hw)
        (xiEulerCentered_ne_conj hu hw), trace_conj_eulerCentered,
      xiRelativeResolventTrace_eulerCentered, xiEulerCentered_sub_conj,
      show (starRingEnd ℂ) (Complex.I * A) - Complex.I * B =
          -Complex.I * ((starRingEnd ℂ) A + B) by
        rw [map_mul, Complex.conj_I]; ring,
      negI_div_negI]
  have hb2 : inner ℂ (xiWeilLineConjLp
        (xiWeilCauchyLp ⟨xiEulerCentered w, XiC_xiEulerCentered_ne_zero hw⟩))
        (xiWeilCauchyLp ⟨xiEulerCentered ((starRingEnd ℂ) u),
          XiC_xiEulerCentered_ne_zero huc⟩) =
      ((starRingEnd ℂ) A + (starRingEnd ℂ) B) /
        ((starRingEnd ℂ) u + (starRingEnd ℂ) w) := by
    rw [inner_lineConj_cauchyLp _ _ (XiC_conj_xiEulerCentered_ne_zero hw)
        (xiEulerCentered_ne_conj huc hw), trace_conj_eulerCentered,
      trace_eulerCentered_conj hu, xiEulerCentered_sub_conj,
      show (starRingEnd ℂ) (Complex.I * A) - -(starRingEnd ℂ) (Complex.I * B) =
          -Complex.I * ((starRingEnd ℂ) A + (starRingEnd ℂ) B) by
        rw [map_mul, map_mul, Complex.conj_I]; ring,
      negI_div_negI]
  have hb3 : inner ℂ (xiWeilLineConjLp
        (xiWeilCauchyLp ⟨xiEulerCentered ((starRingEnd ℂ) w),
          XiC_xiEulerCentered_ne_zero hwc⟩))
        (xiWeilCauchyLp ⟨xiEulerCentered u, XiC_xiEulerCentered_ne_zero hu⟩) =
      (A + B) / (u + w) := by
    rw [inner_lineConj_cauchyLp _ _ (XiC_conj_xiEulerCentered_ne_zero hwc)
        (xiEulerCentered_ne_conj hu hwc), trace_conj_eulerCentered_conj hw,
      xiRelativeResolventTrace_eulerCentered, xiEulerCentered_sub_conj,
      Complex.conj_conj,
      show -(Complex.I * A) - Complex.I * B = -Complex.I * (A + B) by ring,
      negI_div_negI]
  have hb4 : inner ℂ (xiWeilLineConjLp
        (xiWeilCauchyLp ⟨xiEulerCentered ((starRingEnd ℂ) w),
          XiC_xiEulerCentered_ne_zero hwc⟩))
        (xiWeilCauchyLp ⟨xiEulerCentered ((starRingEnd ℂ) u),
          XiC_xiEulerCentered_ne_zero huc⟩) =
      (A + (starRingEnd ℂ) B) / ((starRingEnd ℂ) u + w) := by
    rw [inner_lineConj_cauchyLp _ _ (XiC_conj_xiEulerCentered_ne_zero hwc)
        (xiEulerCentered_ne_conj huc hwc), trace_conj_eulerCentered_conj hw,
      trace_eulerCentered_conj hu, xiEulerCentered_sub_conj, Complex.conj_conj,
      show -(Complex.I * A) - -(starRingEnd ℂ) (Complex.I * B) =
          -Complex.I * (A + (starRingEnd ℂ) B) by
        rw [map_mul, Complex.conj_I]; ring,
      negI_div_negI]
  rw [xiEulerPairedCauchyLp_eq_centered hw, xiEulerPairedCauchyLp_eq_centered hu,
    xiWeilLineConjLp_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    hb1, hb2, hb3, hb4]
  have hXc : ((starRingEnd ℂ) A + B) / (u + (starRingEnd ℂ) w) =
      (starRingEnd ℂ) ((A + (starRingEnd ℂ) B) / (w + (starRingEnd ℂ) u)) := by
    rw [map_div₀, map_add, map_add]
    simp only [Complex.conj_conj]
    ring
  have hCc : ((starRingEnd ℂ) A + (starRingEnd ℂ) B) /
      ((starRingEnd ℂ) u + (starRingEnd ℂ) w) =
      (starRingEnd ℂ) ((A + B) / (w + u)) := by
    rw [map_div₀, map_add, map_add]
    ring
  have hb3' : (A + B) / (u + w) = (A + B) / (w + u) := by ring
  have hb4' : (A + (starRingEnd ℂ) B) / ((starRingEnd ℂ) u + w) =
      (A + (starRingEnd ℂ) B) / (w + (starRingEnd ℂ) u) := by ring
  rw [hXc, hCc, hb3', hb4', xiEulerPairedKernel]
  simp only [Complex.sub_re, Complex.conj_re]
  ring


/-! ## The packet identity -/

theorem realSmul_eq_ofReal_smul (r : ℝ) (v : XiLp) :
    r • v = ((r : ℝ) : ℂ) • v := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

/-- **Equation `(15)`.**  The unconditional Weil Hilbert quadratic value of a real finite
absolute-Euler paired packet is the paired-kernel quadratic form of its coefficients. -/
theorem xiWeilHilbertQuadratic_eulerPairedPacket {n : ℕ} (r : Fin n → ℝ) (w : Fin n → ℂ)
    (hw : ∀ j, 1 / 2 < (w j).re) :
    xiWeilHilbertQuadratic (∑ j, (r j) • xiEulerPairedCauchyLp (w j)
        (XiC_xiEulerCentered_ne_zero (hw j)) (XiC_neg_conj_xiEulerCentered_ne_zero (hw j))) =
      ∑ j, ∑ k, r j * r k * xiEulerPairedKernel (w j) (w k) := by
  classical
  have hsum : (∑ j, (r j) • xiEulerPairedCauchyLp (w j)
        (XiC_xiEulerCentered_ne_zero (hw j)) (XiC_neg_conj_xiEulerCentered_ne_zero (hw j))) =
      ∑ j, ((r j : ℝ) : ℂ) • xiEulerPairedCauchyLp (w j)
        (XiC_xiEulerCentered_ne_zero (hw j)) (XiC_neg_conj_xiEulerCentered_ne_zero (hw j)) :=
    Finset.sum_congr rfl (fun j _ => realSmul_eq_ofReal_smul _ _)
  have hexp : inner ℂ (xiWeilLineConjLinearIsometry (∑ j, ((r j : ℝ) : ℂ) •
          xiEulerPairedCauchyLp (w j) (XiC_xiEulerCentered_ne_zero (hw j))
            (XiC_neg_conj_xiEulerCentered_ne_zero (hw j))))
        (∑ k, ((r k : ℝ) : ℂ) • xiEulerPairedCauchyLp (w k)
          (XiC_xiEulerCentered_ne_zero (hw k))
          (XiC_neg_conj_xiEulerCentered_ne_zero (hw k))) =
      ∑ j, ∑ k, (((r j : ℝ) : ℂ) * ((r k : ℝ) : ℂ)) *
        inner ℂ (xiWeilLineConjLp (xiEulerPairedCauchyLp (w j)
          (XiC_xiEulerCentered_ne_zero (hw j))
          (XiC_neg_conj_xiEulerCentered_ne_zero (hw j))))
          (xiEulerPairedCauchyLp (w k) (XiC_xiEulerCentered_ne_zero (hw k))
            (XiC_neg_conj_xiEulerCentered_ne_zero (hw k))) := by
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [inner_smul_right, xiWeilLineConjLinearIsometry_apply, Complex.conj_ofReal]
    ring
  rw [hsum, xiWeilHilbertQuadratic, hexp, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul,
    inner_lineConj_xiEulerPaired (hw j) (hw k)]

/-! ## The restricted observability splice -/

/-- Equation `(21)`: the Cauchy--Laplace observability kernel of the absolute-Euler half plane. -/
def xiEulerObservabilityKernel (w u : ℂ) : ℂ :=
  (xiEulerLogDeriv w + (starRingEnd ℂ) (xiEulerLogDeriv u)) / (w + (starRingEnd ℂ) u)

/-- The absolute-Euler logarithmic derivative is Schwarz real. -/
theorem xiEulerLogDeriv_conj {w : ℂ} (hw : 1 / 2 < w.re) :
    xiEulerLogDeriv ((starRingEnd ℂ) w) = (starRingEnd ℂ) (xiEulerLogDeriv w) := by
  have hkey : (-Complex.I) * (-((-Complex.I) * (starRingEnd ℂ) (xiEulerLogDeriv w))) =
      (starRingEnd ℂ) (xiEulerLogDeriv w) := by
    linear_combination (-(starRingEnd ℂ) (xiEulerLogDeriv w)) * Complex.I_mul_I
  rw [xiEulerLogDeriv, trace_eulerCentered_conj hw, map_mul, Complex.conj_I, hkey]

/-- **Equation `(22)`.**  The paired value kernel is the doubled conjugation-odd restriction of the
Cauchy--Laplace observability kernel. -/
theorem xiEulerPairedKernel_eq_doubled {w u : ℂ} (hw : 1 / 2 < w.re) (hu : 1 / 2 < u.re) :
    xiEulerPairedKernel w u =
      (xiEulerObservabilityKernel w u).re
        - (xiEulerObservabilityKernel w ((starRingEnd ℂ) u)).re
        - (xiEulerObservabilityKernel ((starRingEnd ℂ) w) u).re
        + (xiEulerObservabilityKernel ((starRingEnd ℂ) w) ((starRingEnd ℂ) u)).re := by
  rw [xiEulerObservabilityKernel, xiEulerObservabilityKernel, xiEulerObservabilityKernel,
    xiEulerObservabilityKernel, xiEulerLogDeriv_conj hw, xiEulerLogDeriv_conj hu]
  simp only [Complex.conj_conj]
  have h2 : (xiEulerLogDeriv w + xiEulerLogDeriv u) / (w + u) =
      (xiEulerLogDeriv w + xiEulerLogDeriv u) / (w + u) := rfl
  have h3 : ((starRingEnd ℂ) (xiEulerLogDeriv w) + (starRingEnd ℂ) (xiEulerLogDeriv u)) /
        ((starRingEnd ℂ) w + (starRingEnd ℂ) u) =
      (starRingEnd ℂ) ((xiEulerLogDeriv w + xiEulerLogDeriv u) / (w + u)) := by
    rw [map_div₀, map_add, map_add]
  have h4 : ((starRingEnd ℂ) (xiEulerLogDeriv w) + xiEulerLogDeriv u) /
        ((starRingEnd ℂ) w + u) =
      (starRingEnd ℂ) ((xiEulerLogDeriv w + (starRingEnd ℂ) (xiEulerLogDeriv u)) /
        (w + (starRingEnd ℂ) u)) := by
    rw [map_div₀, map_add, map_add]
    simp only [Complex.conj_conj]
  rw [h3, h4, xiEulerPairedKernel]
  simp only [Complex.sub_re, Complex.conj_re]
  ring


end

end RHTower
