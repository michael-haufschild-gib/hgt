import GaloisForLFunctions.RHTower.PairedInfiniteApertureCurrent

/-!
# The autocorrelation Laplace transform is the translation-resolvent pairing

For the finite damped-exponential core, the half-line pairing of the profile with its tail
resolvent is the Laplace transform of the autocorrelation:

```text
⟨y, R_c y⟩ = ∫_0^∞ e^{-c h} C_y(h) dh.
```

Both sides are explicit rational expressions in the nodes, so the identity is exact algebra.  At
`c = ±1/2` the two values add to the polar half of the infinite-aperture Stieltjes pairing, because
`e^{-h/2} + e^{h/2} = 2 cosh(h/2)`.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Complex Filter
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

/-- The Laplace transform of the packet autocorrelation. -/
def autocorrLaplace (w : Fin n → ℂ) (r : Fin n → ℝ) (c : ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), Real.exp (-(c * h)) * packetAutocorrelation w r h

theorem integral_exp_neg_mul_halfLineExpPacket {w q : Fin n → ℂ} {c : ℝ}
    (hwc : ∀ j, 0 < (w j + (c : ℂ)).re) :
    (∫ h in Ioi (0 : ℝ), ((Real.exp (-(c * h)) : ℝ) : ℂ) * halfLineExpPacket w q h)
      = ∑ k, q k / (w k + (c : ℂ)) := by
  classical
  have hE : ∀ (h : ℝ) (k : Fin n), ((Real.exp (-(c * h)) : ℝ) : ℂ)
        * (q k * Complex.exp (-(w k) * (h : ℂ)))
      = q k * Complex.exp (-(w k + (c : ℂ)) * (h : ℂ)) := by
    intro h k
    rw [Complex.ofReal_exp]
    rw [show (Complex.exp ((-(c * h) : ℝ) : ℂ) * (q k * Complex.exp (-(w k) * (h : ℂ))))
        = q k * Complex.exp (((-(c * h) : ℝ) : ℂ) + -(w k) * (h : ℂ)) from by
      rw [Complex.exp_add]; ring]
    congr 2
    push_cast
    ring
  have hpoint : ∀ h : ℝ, ((Real.exp (-(c * h)) : ℝ) : ℂ) * halfLineExpPacket w q h
      = ∑ k, q k * Complex.exp (-(w k + (c : ℂ)) * (h : ℂ)) := by
    intro h
    unfold halfLineExpPacket
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hE h k
  have hintj : ∀ k : Fin n, IntegrableOn
      (fun h : ℝ => q k * Complex.exp (-(w k + (c : ℂ)) * (h : ℂ))) (Ioi 0) :=
    fun k => (integrableOn_exp_neg_atom (hwc k)).const_mul _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_finsetSum _ fun k _ => hintj k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_exp_neg_atom (hwc k)]
  field_simp

theorem integrableOn_exp_neg_mul_packetAutocorrelation {w : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {c : ℝ}
    (hwc : ∀ j, 0 < (w j + (c : ℂ)).re) :
    IntegrableOn (fun h : ℝ => Real.exp (-(c * h)) * packetAutocorrelation w r h) (Ioi 0) := by
  have hcplx : IntegrableOn
      (fun h : ℝ => ((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h) (Ioi 0) := by
    have hpoint : ∀ h : ℝ, ((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h
        = ∑ k, autocorrCoeff w r k * Complex.exp (-(w k + (c : ℂ)) * (h : ℂ)) := by
      intro h
      unfold halfLineExpPacket
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.ofReal_exp]
      rw [show (Complex.exp ((-(c * h) : ℝ) : ℂ)
            * (autocorrCoeff w r k * Complex.exp (-(w k) * (h : ℂ))))
          = autocorrCoeff w r k
            * Complex.exp (((-(c * h) : ℝ) : ℂ) + -(w k) * (h : ℂ)) from by
        rw [Complex.exp_add]; ring]
      congr 2
      push_cast
      ring
    have hbase : IntegrableOn
        (fun h : ℝ => ∑ k, autocorrCoeff w r k * Complex.exp (-(w k + (c : ℂ)) * (h : ℂ)))
        (Ioi 0) :=
      integrable_finsetSum _ fun k _ =>
        (integrableOn_exp_neg_atom (hwc k)).const_mul (autocorrCoeff w r k)
    exact hbase.congr_fun (fun h _ => (hpoint h).symm) measurableSet_Ioi
  have heq : ∀ h : ℝ, Real.exp (-(c * h)) * packetAutocorrelation w r h
      = (1 / 2 : ℝ) * (((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h).re := by
    intro h
    rw [Complex.re_ofReal_mul]
    have hpa := packetAutocorrelation_eq hw r h
    linear_combination (Real.exp (-(c * h)) / 2) * hpa
  have hbase2 : IntegrableOn
      (fun h : ℝ => (1 / 2 : ℝ) * (((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h).re) (Ioi 0) :=
    (hcplx.re).const_mul (1 / 2 : ℝ)
  exact hbase2.congr_fun (fun h _ => (heq h).symm) measurableSet_Ioi

/-- **The autocorrelation Laplace transform.** -/
theorem autocorrLaplace_eq {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {c : ℝ}
    (hwc : ∀ j, 0 < (w j + (c : ℂ)).re) :
    2 * autocorrLaplace w r c = (∑ k, autocorrCoeff w r k / (w k + (c : ℂ))).re := by
  classical
  have hcplx : IntegrableOn
      (fun h : ℝ => ((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h) (Ioi 0) := by
    have hpoint : ∀ h : ℝ, ((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h
        = ∑ k, autocorrCoeff w r k * Complex.exp (-(w k + (c : ℂ)) * (h : ℂ)) := by
      intro h
      unfold halfLineExpPacket
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.ofReal_exp]
      rw [show (Complex.exp ((-(c * h) : ℝ) : ℂ)
            * (autocorrCoeff w r k * Complex.exp (-(w k) * (h : ℂ))))
          = autocorrCoeff w r k
            * Complex.exp (((-(c * h) : ℝ) : ℂ) + -(w k) * (h : ℂ)) from by
        rw [Complex.exp_add]; ring]
      congr 2
      push_cast
      ring
    have hbase : IntegrableOn
        (fun h : ℝ => ∑ k, autocorrCoeff w r k * Complex.exp (-(w k + (c : ℂ)) * (h : ℂ)))
        (Ioi 0) :=
      integrable_finsetSum _ fun k _ =>
        (integrableOn_exp_neg_atom (hwc k)).const_mul (autocorrCoeff w r k)
    exact hbase.congr_fun (fun h _ => (hpoint h).symm) measurableSet_Ioi
  have hpt : ∀ h : ℝ, 2 * (Real.exp (-(c * h)) * packetAutocorrelation w r h)
      = (((Real.exp (-(c * h)) : ℝ) : ℂ) * halfLineExpPacket w (autocorrCoeff w r) h).re := by
    intro h
    rw [Complex.re_ofReal_mul]
    have hpa := packetAutocorrelation_eq hw r h
    linear_combination Real.exp (-(c * h)) * hpa
  have hstep : 2 * autocorrLaplace w r c
      = ∫ h in Ioi (0 : ℝ), (((Real.exp (-(c * h)) : ℝ) : ℂ)
          * halfLineExpPacket w (autocorrCoeff w r) h).re := by
    rw [autocorrLaplace, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hre : (∫ h in Ioi (0 : ℝ), (((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h).re)
      = (∫ h in Ioi (0 : ℝ), ((Real.exp (-(c * h)) : ℝ) : ℂ)
        * halfLineExpPacket w (autocorrCoeff w r) h).re := integral_re hcplx
  rw [hstep, hre, integral_exp_neg_mul_halfLineExpPacket hwc]

/-- **The resolvent pairing is the autocorrelation Laplace transform.** -/
theorem packetResolventPairing_eq_autocorrLaplace {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {c : ℝ} (hwc : ∀ j, 0 < (w j + (c : ℂ)).re) :
    packetResolventPairing w r c = autocorrLaplace w r c := by
  classical
  have hcross := integral_im_mul_im_expPacket (w := w) (fun j => (r j : ℂ))
    (resolventCoeff w r c) hw
  have hpair : packetResolventPairing w r c
      = ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w (fun j => (r j : ℂ)) x).im
          * (halfLineExpPacket w (resolventCoeff w r c) x).im := rfl
  have hcne : ∀ k, w k + (c : ℂ) ≠ 0 := by
    intro k h
    have := hwc k
    rw [h] at this
    simp at this
  have hcollect : (∑ j, ∑ k, (starRingEnd ℂ) ((r j : ℂ)) * resolventCoeff w r c k
          / ((starRingEnd ℂ) (w j) + w k))
        - ∑ j, ∑ k, (r j : ℂ) * resolventCoeff w r c k / (w j + w k)
      = ∑ k, autocorrCoeff w r k / (w k + (c : ℂ)) := by
    rw [Finset.sum_comm (f := fun j k => (starRingEnd ℂ) ((r j : ℂ)) * resolventCoeff w r c k
      / ((starRingEnd ℂ) (w j) + w k))]
    rw [Finset.sum_comm (f := fun j k => (r j : ℂ) * resolventCoeff w r c k / (w j + w k))]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hterm : ∀ j : Fin n,
        (starRingEnd ℂ) ((r j : ℂ)) * resolventCoeff w r c k / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) * resolventCoeff w r c k / (w j + w k)
        = ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k) - (r j : ℂ) / (w j + w k))
          * ((r k : ℂ) / (w k + (c : ℂ))) := by
      intro j
      rw [Complex.conj_ofReal, resolventCoeff]
      ring
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j), ← Finset.sum_mul]
    unfold autocorrCoeff
    field_simp
  have hLap := autocorrLaplace_eq hw r hwc
  rw [← Complex.sub_re, hcollect] at hcross
  rw [hpair]
  linarith [hcross, hLap]

/-! ## The polar pair of resolvents -/

/-- The polar half of the infinite-aperture pairing, in real form. -/
def polarAutocorrCurrentReal (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), 2 * Real.cosh (h / 2) * packetAutocorrelation w r h

theorem polarAutocorrCurrent_eq_ofReal (w : Fin n → ℂ) (r : Fin n → ℝ) :
    polarAutocorrCurrent w r = ((polarAutocorrCurrentReal w r : ℝ) : ℂ) := by
  have hof : (∫ h in Ioi (0 : ℝ),
        ((2 * Real.cosh (h / 2) * packetAutocorrelation w r h : ℝ) : ℂ))
      = ((∫ h in Ioi (0 : ℝ), 2 * Real.cosh (h / 2) * packetAutocorrelation w r h : ℝ) : ℂ) :=
    integral_ofReal
  rw [polarAutocorrCurrent, polarAutocorrCurrentReal, ← hof]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  show autocorrTest w r h * (2 * (Real.cosh (h / 2) : ℂ))
    = ((2 * Real.cosh (h / 2) * packetAutocorrelation w r h : ℝ) : ℂ)
  rw [autocorrTest]
  push_cast
  ring

/-- **Equation `(9)` of the parent card in autocorrelation form.**  The two polar resolvent values
add to the `2 cosh(h/2)` current. -/
theorem autocorrLaplace_polar_pair {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    (hhalf : ∀ j, 1 / 2 < (w j).re) :
    autocorrLaplace w r (1 / 2) + autocorrLaplace w r (-(1 / 2))
      = polarAutocorrCurrentReal w r := by
  have hplus : ∀ j, 0 < (w j + ((1 / 2 : ℝ) : ℂ)).re := by
    intro j
    have := hw j
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hminus : ∀ j, 0 < (w j + ((-(1 / 2) : ℝ) : ℂ)).re := by
    intro j
    have := hhalf j
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hint1 := integrableOn_exp_neg_mul_packetAutocorrelation hw r hplus
  have hint2 := integrableOn_exp_neg_mul_packetAutocorrelation hw r hminus
  rw [autocorrLaplace, autocorrLaplace, ← MeasureTheory.integral_add hint1 hint2,
    polarAutocorrCurrentReal]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  show Real.exp (-((1 / 2 : ℝ) * h)) * packetAutocorrelation w r h
      + Real.exp (-((-(1 / 2) : ℝ) * h)) * packetAutocorrelation w r h
    = 2 * Real.cosh (h / 2) * packetAutocorrelation w r h
  rw [Real.cosh_eq, show -((1 / 2 : ℝ) * h) = -(h / 2) from by ring,
    show -((-(1 / 2) : ℝ) * h) = h / 2 from by ring]
  ring


end

end RHTower
