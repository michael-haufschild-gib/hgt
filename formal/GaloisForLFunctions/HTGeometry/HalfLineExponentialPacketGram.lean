import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Half-line Gram identities for finite exponential packets

A **half-line exponential packet** is a finite sum `P(x) = ∑ⱼ cⱼ e^{-wⱼ x}` with all
`Re wⱼ > 0`.  Two such packets pair on `(0,∞)` through the Cauchy kernel:

```text
∫_0^∞ P_c(x) P_d(x) dx      = ∑_{j,k} cⱼ d_k / (wⱼ + w_k),
∫_0^∞ conj(P_c(x)) P_d(x) dx = ∑_{j,k} conj(cⱼ) d_k / (conj wⱼ + w_k).
```

Both are exact; no estimate is involved.  Together with the pointwise identity
`‖F‖² - Re(F²) = 2 (Im F)²` they turn every "Hermitian square minus bilinear square" expression
into the half-line energy of the *imaginary part* of the packet, which is the shape every
paired-Cauchy source computation needs.

This module is source-independent: it is pure half-line Laplace algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex
open scoped BigOperators

noncomputable section

/-! ## The single Cauchy atom -/

theorem integrableOn_exp_atom_mul {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) :
    IntegrableOn
      (fun x : ℝ => Complex.exp (-α * (x : ℂ)) * Complex.exp (-β * (x : ℂ))) (Ioi 0) := by
  have hfun : (fun x : ℝ => Complex.exp (-α * (x : ℂ)) * Complex.exp (-β * (x : ℂ)))
      = fun x : ℝ => Complex.exp ((-(α + β)) * (x : ℂ)) := by
    funext x
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hfun]
  refine integrableOn_exp_mul_complex_Ioi ?_ 0
  simp only [Complex.neg_re, Complex.add_re]
  linarith

/-- **The half-line Cauchy atom.**  Two decaying exponentials pair to the Cauchy kernel. -/
theorem integral_exp_atom_mul {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) :
    ∫ x in Ioi (0 : ℝ), Complex.exp (-α * (x : ℂ)) * Complex.exp (-β * (x : ℂ))
      = (α + β)⁻¹ := by
  have hfun : (fun x : ℝ => Complex.exp (-α * (x : ℂ)) * Complex.exp (-β * (x : ℂ)))
      = fun x : ℝ => Complex.exp ((-(α + β)) * (x : ℂ)) := by
    funext x
    rw [← Complex.exp_add]
    congr 1
    ring
  have hre : ((-(α + β)) : ℂ).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re]
    linarith
  rw [hfun, integral_exp_mul_complex_Ioi hre 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [neg_div_neg_eq, one_div]

/-! ## Packets -/

/-- The half-line exponential packet `P(x) = ∑ⱼ cⱼ e^{-wⱼ x}`. -/
def halfLineExpPacket {n : ℕ} (w c : Fin n → ℂ) (x : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (-(w j) * (x : ℂ))

theorem conj_expPacket {n : ℕ} (w c : Fin n → ℂ) (x : ℝ) :
    (starRingEnd ℂ) (halfLineExpPacket w c x)
      = halfLineExpPacket (fun j => (starRingEnd ℂ) (w j)) (fun j => (starRingEnd ℂ) (c j)) x := by
  unfold halfLineExpPacket
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp

theorem integrableOn_expPacket_mul {n : ℕ} {w v c d : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (hv : ∀ j, 0 < (v j).re) :
    IntegrableOn (fun x : ℝ => halfLineExpPacket w c x * halfLineExpPacket v d x) (Ioi 0) := by
  have hfun : (fun x : ℝ => halfLineExpPacket w c x * halfLineExpPacket v d x)
      = fun x : ℝ => ∑ j, ∑ k, (c j * d k) *
        (Complex.exp (-(w j) * (x : ℂ)) * Complex.exp (-(v k) * (x : ℂ))) := by
    funext x
    unfold halfLineExpPacket
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun]
  refine integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => ?_
  exact (integrableOn_exp_atom_mul (hw j) (hv k)).const_mul _

/-- **The bilinear half-line Gram identity.** -/
theorem integral_expPacket_mul {n : ℕ} {w v c d : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (hv : ∀ j, 0 < (v j).re) :
    ∫ x in Ioi (0 : ℝ), halfLineExpPacket w c x * halfLineExpPacket v d x
      = ∑ j, ∑ k, c j * d k / (w j + v k) := by
  have hfun : (fun x : ℝ => halfLineExpPacket w c x * halfLineExpPacket v d x)
      = fun x : ℝ => ∑ j, ∑ k, (c j * d k) *
        (Complex.exp (-(w j) * (x : ℂ)) * Complex.exp (-(v k) * (x : ℂ))) := by
    funext x
    unfold halfLineExpPacket
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun]
  rw [integral_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => (integrableOn_exp_atom_mul (hw j) (hv k)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => (integrableOn_exp_atom_mul (hw j) (hv k)).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_exp_atom_mul (hw j) (hv k), div_eq_mul_inv]

/-- **The Hermitian half-line Gram identity.** -/
theorem integral_conj_expPacket_mul {n : ℕ} {w v c d : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (hv : ∀ j, 0 < (v j).re) :
    ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket v d x
      = ∑ j, ∑ k, (starRingEnd ℂ) (c j) * d k / ((starRingEnd ℂ) (w j) + v k) := by
  have hconj : ∀ j, 0 < ((starRingEnd ℂ) (w j)).re := by
    intro j
    simpa using hw j
  have hfun : (fun x : ℝ => (starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket v d x)
      = fun x : ℝ => halfLineExpPacket (fun j => (starRingEnd ℂ) (w j))
        (fun j => (starRingEnd ℂ) (c j)) x * halfLineExpPacket v d x := by
    funext x
    rw [conj_expPacket]
  rw [hfun, integral_expPacket_mul hconj hv]

theorem integrableOn_conj_expPacket_mul {n : ℕ} {w v c d : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (hv : ∀ j, 0 < (v j).re) :
    IntegrableOn
      (fun x : ℝ => (starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket v d x) (Ioi 0) := by
  have hconj : ∀ j, 0 < ((starRingEnd ℂ) (w j)).re := by
    intro j
    simpa using hw j
  have hfun : (fun x : ℝ => (starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket v d x)
      = fun x : ℝ => halfLineExpPacket (fun j => (starRingEnd ℂ) (w j))
        (fun j => (starRingEnd ℂ) (c j)) x * halfLineExpPacket v d x := by
    funext x
    rw [conj_expPacket]
  rw [hfun]
  exact integrableOn_expPacket_mul hconj hv

/-! ## Hermitian square minus bilinear square -/

/-- The pointwise identity `‖F‖² - Re(F²) = 2 (Im F)²`. -/
theorem normSq_sub_re_sq (F : ℂ) : ‖F‖ ^ (2 : ℕ) - (F ^ (2 : ℕ)).re = 2 * F.im ^ (2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, pow_two, Complex.mul_re]
  ring

/-- **The imaginary-part energy identity.**  The Hermitian half-line square minus the bilinear
half-line square is twice the half-line energy of the imaginary part of the packet. -/
theorem integral_im_sq_expPacket {n : ℕ} {w c : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) :
    2 * ∫ x in Ioi (0 : ℝ), ((halfLineExpPacket w c x).im) ^ (2 : ℕ)
      = (∑ j, ∑ k, (starRingEnd ℂ) (c j) * c k / ((starRingEnd ℂ) (w j) + w k)).re
        - (∑ j, ∑ k, c j * c k / (w j + w k)).re := by
  have hint1 := integrableOn_conj_expPacket_mul (w := w) (v := w) (c := c) (d := c) hw hw
  have hint2 := integrableOn_expPacket_mul (w := w) (v := w) (c := c) (d := c) hw hw
  have hpoint : ∀ x : ℝ,
      2 * ((halfLineExpPacket w c x).im) ^ (2 : ℕ)
        = (((starRingEnd ℂ) (halfLineExpPacket w c x)) * halfLineExpPacket w c x).re
          - ((halfLineExpPacket w c x * halfLineExpPacket w c x)).re := by
    intro x
    set F : ℂ := halfLineExpPacket w c x with hF
    have h1 : ((starRingEnd ℂ) F * F).re = ‖F‖ ^ (2 : ℕ) := by
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      ring
    have h2 : (F * F).re = (F ^ (2 : ℕ)).re := by rw [pow_two]
    rw [h1, h2]
    exact (normSq_sub_re_sq F).symm
  have hEq : (fun x : ℝ => 2 * ((halfLineExpPacket w c x).im) ^ (2 : ℕ))
      = fun x : ℝ => (((starRingEnd ℂ) (halfLineExpPacket w c x)) * halfLineExpPacket w c x).re
        - ((halfLineExpPacket w c x * halfLineExpPacket w c x)).re := funext hpoint
  rw [← integral_expPacket_mul (w := w) (v := w) (c := c) (d := c) hw hw,
    ← integral_conj_expPacket_mul (w := w) (v := w) (c := c) (d := c) hw hw]
  have hre1 : (∫ x in Ioi (0 : ℝ),
        ((starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w c x).re)
      = (∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w c x).re :=
    integral_re (μ := volume.restrict (Ioi 0)) hint1
  have hre2 : (∫ x in Ioi (0 : ℝ), (halfLineExpPacket w c x * halfLineExpPacket w c x).re)
      = (∫ x in Ioi (0 : ℝ), halfLineExpPacket w c x * halfLineExpPacket w c x).re :=
    integral_re (μ := volume.restrict (Ioi 0)) hint2
  have hsub : (∫ x in Ioi (0 : ℝ),
        (((starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w c x).re
          - (halfLineExpPacket w c x * halfLineExpPacket w c x).re))
      = (∫ x in Ioi (0 : ℝ), ((starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w c x).re)
        - ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w c x * halfLineExpPacket w c x).re :=
    MeasureTheory.integral_sub hint1.re hint2.re
  rw [← MeasureTheory.integral_const_mul, ← hre1, ← hre2, ← hsub]
  exact congrArg _ hEq


/-- The pointwise cross identity `Re(conj F · G) - Re(F · G) = 2 (Im F)(Im G)`. -/
theorem re_conj_mul_sub_re_mul (F G : ℂ) :
    ((starRingEnd ℂ) F * G).re - (F * G).re = 2 * F.im * G.im := by
  rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **The cross imaginary-part energy identity.**  For two packets with the same frequencies, the
Hermitian half-line pairing minus the bilinear half-line pairing is twice the half-line pairing of
their imaginary parts. -/
theorem integral_im_mul_im_expPacket {n : ℕ} {w : Fin n → ℂ} (c d : Fin n → ℂ)
    (hw : ∀ j, 0 < (w j).re) :
    2 * ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w c x).im * (halfLineExpPacket w d x).im
      = (∑ j, ∑ k, (starRingEnd ℂ) (c j) * d k / ((starRingEnd ℂ) (w j) + w k)).re
        - (∑ j, ∑ k, c j * d k / (w j + w k)).re := by
  have hint1 := integrableOn_conj_expPacket_mul (w := w) (v := w) (c := c) (d := d) hw hw
  have hint2 := integrableOn_expPacket_mul (w := w) (v := w) (c := c) (d := d) hw hw
  have hEq : (fun x : ℝ => 2 * ((halfLineExpPacket w c x).im * (halfLineExpPacket w d x).im))
      = fun x : ℝ => (((starRingEnd ℂ) (halfLineExpPacket w c x)) * halfLineExpPacket w d x).re
        - ((halfLineExpPacket w c x * halfLineExpPacket w d x)).re := by
    funext x
    rw [re_conj_mul_sub_re_mul]
    ring
  have hre1 : (∫ x in Ioi (0 : ℝ),
        ((starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w d x).re)
      = (∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w d x).re :=
    integral_re (μ := volume.restrict (Ioi 0)) hint1
  have hre2 : (∫ x in Ioi (0 : ℝ), (halfLineExpPacket w c x * halfLineExpPacket w d x).re)
      = (∫ x in Ioi (0 : ℝ), halfLineExpPacket w c x * halfLineExpPacket w d x).re :=
    integral_re (μ := volume.restrict (Ioi 0)) hint2
  have hsub : (∫ x in Ioi (0 : ℝ),
        (((starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w d x).re
          - (halfLineExpPacket w c x * halfLineExpPacket w d x).re))
      = (∫ x in Ioi (0 : ℝ), ((starRingEnd ℂ) (halfLineExpPacket w c x) * halfLineExpPacket w d x).re)
        - ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w c x * halfLineExpPacket w d x).re :=
    MeasureTheory.integral_sub hint1.re hint2.re
  rw [← integral_conj_expPacket_mul (w := w) (v := w) (c := c) (d := d) hw hw,
    ← integral_expPacket_mul (w := w) (v := w) (c := c) (d := d) hw hw,
    ← MeasureTheory.integral_const_mul, ← hre1, ← hre2, ← hsub]
  exact congrArg _ hEq

/-- The half-line pairing of imaginary parts is integrable. -/
theorem integrableOn_im_mul_im_expPacket {n : ℕ} {w : Fin n → ℂ} (c d : Fin n → ℂ)
    (hw : ∀ j, 0 < (w j).re) :
    IntegrableOn (fun x : ℝ => (halfLineExpPacket w c x).im * (halfLineExpPacket w d x).im) (Ioi 0) := by
  have hint1 := (integrableOn_conj_expPacket_mul (w := w) (v := w) (c := c) (d := d) hw hw).re
  have hint2 := (integrableOn_expPacket_mul (w := w) (v := w) (c := c) (d := d) hw hw).re
  have hEq : (fun x : ℝ => (halfLineExpPacket w c x).im * (halfLineExpPacket w d x).im)
      = fun x : ℝ => (1 / 2 : ℝ) *
        ((((starRingEnd ℂ) (halfLineExpPacket w c x)) * halfLineExpPacket w d x).re
          - ((halfLineExpPacket w c x * halfLineExpPacket w d x)).re) := by
    funext x
    rw [re_conj_mul_sub_re_mul]
    ring
  rw [hEq]
  exact (hint1.sub hint2).const_mul _

end

end GaloisForLFunctions.HTGeometry
