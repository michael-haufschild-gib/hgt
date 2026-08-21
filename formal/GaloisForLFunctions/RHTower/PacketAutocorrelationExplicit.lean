import GaloisForLFunctions.RHTower.PairedTranslationResolventCalculus

/-!
# The autocorrelation of a damped exponential packet is again a packet

For a finite real-coefficient packet `E(x) = ∑ⱼ rⱼ e^{-wⱼ x}` with `Re wⱼ > 0` and `y = Im E`, the
half-line autocorrelation

```text
C_y(h) = ∫_0^∞ y(x) y(x+h) dx
```

is `1/2` the real part of an explicit exponential packet in the lag variable, with coefficients

```text
q_k = r_k ∑ⱼ rⱼ ( 1/(conj wⱼ + w_k) - 1/(wⱼ + w_k) ).
```

Consequently `C_y` is smooth, its derivative is the packet with coefficients `-w_k q_k`, and both
decay like `e^{-α h}` for any lower bound `α` on the real parts.  This is exactly the input the
infinite-aperture Stieltjes passage needs.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Complex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Uniform exponential bound for a packet -/

theorem norm_halfLineExpPacket_le {w q : Fin n → ℂ} {α : ℝ} (hα : ∀ k, α ≤ (w k).re)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖halfLineExpPacket w q x‖ ≤ (∑ k, ‖q k‖) * Real.exp (-(α * x)) := by
  classical
  calc ‖halfLineExpPacket w q x‖
      ≤ ∑ k, ‖q k * Complex.exp (-(w k) * (x : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖q k‖ * Real.exp (-(α * x)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(w k) * (x : ℂ)).re = -((w k).re * x) := by
          simp [Complex.mul_re]
        rw [hre]
        have hmono : Real.exp (-((w k).re * x)) ≤ Real.exp (-(α * x)) := by
          rw [Real.exp_le_exp]
          have := mul_le_mul_of_nonneg_right (hα k) hx
          linarith
        exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
    _ = (∑ k, ‖q k‖) * Real.exp (-(α * x)) := by rw [Finset.sum_mul]

/-! ## The explicit autocorrelation packet -/

/-- The lag coefficients of the half-line autocorrelation. -/
def autocorrCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) (k : Fin n) : ℂ :=
  (r k : ℂ) * ∑ j, ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k) - (r j : ℂ) / (w j + w k))

/-- **The autocorrelation is half the real part of an exponential packet.** -/
theorem packetAutocorrelation_eq {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    (tau : ℝ) :
    2 * packetAutocorrelation w r tau
      = (halfLineExpPacket w (autocorrCoeff w r) tau).re := by
  classical
  have hcross := integral_im_mul_im_expPacket (w := w) (fun j => (r j : ℂ))
    (lagCoeff w r tau) hw
  have hpair : packetAutocorrelation w r tau
      = ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w (fun j => (r j : ℂ)) x).im
          * (halfLineExpPacket w (lagCoeff w r tau) x).im := rfl
  rw [hpair, hcross]
  have hcollect : (∑ j, ∑ k, (starRingEnd ℂ) ((r j : ℂ)) * lagCoeff w r tau k
          / ((starRingEnd ℂ) (w j) + w k))
        - ∑ j, ∑ k, (r j : ℂ) * lagCoeff w r tau k / (w j + w k)
      = halfLineExpPacket w (autocorrCoeff w r) tau := by
    rw [Finset.sum_comm (f := fun j k => (starRingEnd ℂ) ((r j : ℂ)) * lagCoeff w r tau k
      / ((starRingEnd ℂ) (w j) + w k))]
    rw [Finset.sum_comm (f := fun j k => (r j : ℂ) * lagCoeff w r tau k / (w j + w k))]
    rw [← Finset.sum_sub_distrib]
    unfold halfLineExpPacket
    refine Finset.sum_congr rfl fun k _ => ?_
    have hterm : ∀ j : Fin n,
        (starRingEnd ℂ) ((r j : ℂ)) * lagCoeff w r tau k / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) * lagCoeff w r tau k / (w j + w k)
        = ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k) - (r j : ℂ) / (w j + w k))
          * ((r k : ℂ) * Complex.exp (-(w k) * (tau : ℂ))) := by
      intro j
      rw [Complex.conj_ofReal, lagCoeff]
      ring
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j), ← Finset.sum_mul]
    unfold autocorrCoeff
    ring
  rw [← Complex.sub_re, hcollect]

/-- The derivative of the autocorrelation packet. -/
def packetAutocorrelationDeriv (w : Fin n → ℂ) (r : Fin n → ℝ) (tau : ℝ) : ℝ :=
  (1 / 2) * (halfLineExpPacket w (fun k => -(w k) * autocorrCoeff w r k) tau).re

theorem hasDerivAt_re_halfLineExpPacket (w q : Fin n → ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (halfLineExpPacket w q t).re)
      ((halfLineExpPacket w (fun k => -(w k) * q k) x).re) x := by
  classical
  have hderiv : HasDerivAt (fun t : ℝ => halfLineExpPacket w q t)
      (halfLineExpPacket w (fun k => -(w k) * q k) x) x := by
    unfold halfLineExpPacket
    refine HasDerivAt.fun_sum fun k _ => ?_
    have hb : HasDerivAt (fun t : ℝ => Complex.exp (-(w k) * (t : ℂ)))
        (Complex.exp (-(w k) * (x : ℂ)) * (-(w k))) x := by
      have h1 : HasDerivAt (fun t : ℝ => (-(w k)) * (t : ℂ)) (-(w k)) x := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(w k)))
      simpa using h1.cexp
    have hcm := hb.const_mul (q k)
    have hre : q k * (Complex.exp (-(w k) * (x : ℂ)) * (-(w k)))
        = -(w k) * q k * Complex.exp (-(w k) * (x : ℂ)) := by ring
    rwa [hre] at hcm
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hderiv)

/-- **The autocorrelation is differentiable, with the explicit packet derivative.** -/
theorem hasDerivAt_packetAutocorrelation {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) (tau : ℝ) :
    HasDerivAt (packetAutocorrelation w r) (packetAutocorrelationDeriv w r tau) tau := by
  have hfun : packetAutocorrelation w r
      = fun t : ℝ => (1 / 2 : ℝ) * (halfLineExpPacket w (autocorrCoeff w r) t).re := by
    funext t
    have := packetAutocorrelation_eq hw r t
    linarith
  rw [hfun, packetAutocorrelationDeriv]
  exact (hasDerivAt_re_halfLineExpPacket w (autocorrCoeff w r) tau).const_mul (1 / 2 : ℝ)

/-! ## Exponential decay -/

theorem abs_packetAutocorrelation_le {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) {tau : ℝ} (htau : 0 ≤ tau) :
    |packetAutocorrelation w r tau|
      ≤ (1 / 2) * (∑ k, ‖autocorrCoeff w r k‖) * Real.exp (-(α * tau)) := by
  have heq := packetAutocorrelation_eq hw r tau
  have hle : |(halfLineExpPacket w (autocorrCoeff w r) tau).re|
      ≤ (∑ k, ‖autocorrCoeff w r k‖) * Real.exp (-(α * tau)) :=
    le_trans (Complex.abs_re_le_norm _) (norm_halfLineExpPacket_le hα htau)
  have habs : |2 * packetAutocorrelation w r tau| = 2 * |packetAutocorrelation w r tau| := by
    rw [abs_mul]
    norm_num
  rw [heq] at habs
  linarith [hle, habs]

theorem abs_packetAutocorrelationDeriv_le {w : Fin n → ℂ} (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) {tau : ℝ} (htau : 0 ≤ tau) :
    |packetAutocorrelationDeriv w r tau|
      ≤ (1 / 2) * (∑ k, ‖-(w k) * autocorrCoeff w r k‖) * Real.exp (-(α * tau)) := by
  rw [packetAutocorrelationDeriv, abs_mul]
  have hle : |(halfLineExpPacket w (fun k => -(w k) * autocorrCoeff w r k) tau).re|
      ≤ (∑ k, ‖-(w k) * autocorrCoeff w r k‖) * Real.exp (-(α * tau)) :=
    le_trans (Complex.abs_re_le_norm _) (norm_halfLineExpPacket_le hα htau)
  have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

/-! ## The integral form of the autocorrelation derivative -/

/-- The derivative of the half-line profile `y' = Im E'`. -/
def packetProfileDeriv (w : Fin n → ℂ) (r : Fin n → ℝ) (x : ℝ) : ℝ :=
  (halfLineExpPacket w (fun j => -(w j) * (r j : ℂ)) x).im

theorem hasDerivAt_packetProfile (w : Fin n → ℂ) (r : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (packetProfile w r) (packetProfileDeriv w r x) x := by
  have hderiv : HasDerivAt (fun t : ℝ => halfLineExpPacket w (fun j => (r j : ℂ)) t)
      (halfLineExpPacket w (fun j => -(w j) * (r j : ℂ)) x) x := by
    unfold halfLineExpPacket
    refine HasDerivAt.fun_sum fun j _ => ?_
    have hb : HasDerivAt (fun t : ℝ => Complex.exp (-(w j) * (t : ℂ)))
        (Complex.exp (-(w j) * (x : ℂ)) * (-(w j))) x := by
      have h1 : HasDerivAt (fun t : ℝ => (-(w j)) * (t : ℂ)) (-(w j)) x := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(w j)))
      simpa using h1.cexp
    have hcm := hb.const_mul ((r j : ℂ))
    have hre : (r j : ℂ) * (Complex.exp (-(w j) * (x : ℂ)) * (-(w j)))
        = -(w j) * (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ)) := by ring
    rwa [hre] at hcm
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hderiv

/-- The shifted derivative coefficients. -/
def derivLagCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) (tau : ℝ) (k : Fin n) : ℂ :=
  -(w k) * (r k : ℂ) * Complex.exp (-(w k) * (tau : ℂ))

theorem expPacket_derivLagCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) (tau x : ℝ) :
    halfLineExpPacket w (derivLagCoeff w r tau) x = halfLineExpPacket w
      (fun j => -(w j) * (r j : ℂ)) (x + tau) := by
  unfold halfLineExpPacket derivLagCoeff
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Equation `(3)`.**  The autocorrelation derivative is the half-line pairing of the profile
with the shifted profile derivative. -/
theorem packetAutocorrelationDeriv_eq_integral {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) (tau : ℝ) :
    packetAutocorrelationDeriv w r tau
      = ∫ x in Ioi (0 : ℝ), packetProfile w r x * packetProfileDeriv w r (x + tau) := by
  classical
  have hcross := integral_im_mul_im_expPacket (w := w) (fun j => (r j : ℂ))
    (derivLagCoeff w r tau) hw
  have hpair : (∫ x in Ioi (0 : ℝ), packetProfile w r x * packetProfileDeriv w r (x + tau))
      = ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w (fun j => (r j : ℂ)) x).im
          * (halfLineExpPacket w (derivLagCoeff w r tau) x).im := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (nodePacket w r x).im * (halfLineExpPacket w (fun j => -(w j) * (r j : ℂ)) (x + tau)).im
      = (halfLineExpPacket w (fun j => (r j : ℂ)) x).im
        * (halfLineExpPacket w (derivLagCoeff w r tau) x).im
    rw [expPacket_derivLagCoeff]
    rfl
  have hcollect : (∑ j, ∑ k, (starRingEnd ℂ) ((r j : ℂ)) * derivLagCoeff w r tau k
          / ((starRingEnd ℂ) (w j) + w k))
        - ∑ j, ∑ k, (r j : ℂ) * derivLagCoeff w r tau k / (w j + w k)
      = halfLineExpPacket w (fun k => -(w k) * autocorrCoeff w r k) tau := by
    rw [Finset.sum_comm (f := fun j k => (starRingEnd ℂ) ((r j : ℂ)) * derivLagCoeff w r tau k
      / ((starRingEnd ℂ) (w j) + w k))]
    rw [Finset.sum_comm (f := fun j k => (r j : ℂ) * derivLagCoeff w r tau k / (w j + w k))]
    rw [← Finset.sum_sub_distrib]
    unfold halfLineExpPacket
    refine Finset.sum_congr rfl fun k _ => ?_
    have hterm : ∀ j : Fin n,
        (starRingEnd ℂ) ((r j : ℂ)) * derivLagCoeff w r tau k / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) * derivLagCoeff w r tau k / (w j + w k)
        = ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k) - (r j : ℂ) / (w j + w k))
          * (-(w k) * (r k : ℂ) * Complex.exp (-(w k) * (tau : ℂ))) := by
      intro j
      rw [Complex.conj_ofReal, derivLagCoeff]
      ring
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j), ← Finset.sum_mul]
    unfold autocorrCoeff
    ring
  rw [← Complex.sub_re, hcollect] at hcross
  rw [hpair, packetAutocorrelationDeriv]
  linarith [hcross]


end

end RHTower
