import GaloisForLFunctions.RHTower.PacketAutocorrelationExplicit

/-!
# The paired contact laws of the half-line autocorrelation

For a finite node packet `E(x) = ∑ⱼ rⱼ e^{-wⱼ x}` with `Re wⱼ > 0` and **real** coefficients
`rⱼ`, the half-line profile `y = Im E` vanishes at contact, and its autocorrelation
`C_y(h) = ∫_0^∞ y(x) y(x+h) dx` satisfies the exact contact laws

```text
y(0) = 0,      C_y'(0) = -y(0)^(2 : ℕ)/2 = 0,      C_y''(0) = -∫_0^∞ y'(x)^(2 : ℕ) dx.
```

Both derivative laws are pure Cauchy-kernel symmetry: the plain double sum
`∑ⱼₖ rⱼ r_k w_k/(wⱼ+w_k)` is half `(∑ⱼ rⱼ)^(2 : ℕ)` by swapping the indices, and the conjugate-twisted
double sum `∑ⱼₖ rⱼ r_k w_k/(conj wⱼ + w_k)` has the same real part by conjugating and swapping.
No estimate or limiting argument is involved.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Complex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Cauchy-kernel symmetry -/

theorem sum_sum_ofReal_mul (r : Fin n → ℝ) :
    (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ)) = (((∑ j, r j) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [← Finset.sum_mul_sum]
  push_cast
  ring

/-- The plain Cauchy double sum is half the squared coefficient mass. -/
theorem two_mul_sum_plain {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) :
    (2 : ℂ) * (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k))
      = (((∑ j, r j) ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  have hne : ∀ j k : Fin n, w j + w k ≠ 0 := fun j k => add_ne_zero_of_re_pos (hw j) (hw k)
  have hswap : (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k))
      = ∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w j) / (w j + w k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [add_comm (w y) (w x)]
    ring
  have hinner : ∀ j : Fin n,
      (∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k))
        + (∑ k, (r j : ℂ) * (r k : ℂ) * (w j) / (w j + w k))
        = ∑ k, (r j : ℂ) * (r k : ℂ) := by
    intro j
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h0 := hne j k
    field_simp
    try ring
  have htot : (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k))
      + (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w j) / (w j + w k))
      = (((∑ j, r j) ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib, ← sum_sum_ofReal_mul]
    exact Finset.sum_congr rfl fun j _ => hinner j
  linear_combination htot + hswap

/-- The conjugate-twisted Cauchy double sum has the same real part. -/
theorem add_conj_sum_twisted {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) :
    (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / ((starRingEnd ℂ) (w j) + w k))
      + (starRingEnd ℂ)
          (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / ((starRingEnd ℂ) (w j) + w k))
      = (((∑ j, r j) ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  have hne : ∀ j k : Fin n, (starRingEnd ℂ) (w j) + w k ≠ 0 := fun j k =>
    add_ne_zero_of_re_pos (by simpa using hw j) (hw k)
  have hconj : (starRingEnd ℂ)
      (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / ((starRingEnd ℂ) (w j) + w k))
      = ∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * ((starRingEnd ℂ) (w j)) /
          ((starRingEnd ℂ) (w j) + w k) := by
    rw [map_sum]
    rw [show (fun j => (starRingEnd ℂ) (∑ k, (r j : ℂ) * (r k : ℂ) * (w k) /
        ((starRingEnd ℂ) (w j) + w k)))
        = fun j => ∑ k, (r j : ℂ) * (r k : ℂ) * ((starRingEnd ℂ) (w k)) /
          (w j + (starRingEnd ℂ) (w k)) by
      funext j
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_div₀, map_mul, map_mul, map_add]
      simp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [add_comm (w y) ((starRingEnd ℂ) (w x))]
    ring
  rw [hconj]
  have hinner : ∀ j : Fin n,
      (∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / ((starRingEnd ℂ) (w j) + w k))
        + (∑ k, (r j : ℂ) * (r k : ℂ) * ((starRingEnd ℂ) (w j)) /
            ((starRingEnd ℂ) (w j) + w k))
        = ∑ k, (r j : ℂ) * (r k : ℂ) := by
    intro j
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h0 := hne j k
    field_simp
    try ring
  rw [← Finset.sum_add_distrib, ← sum_sum_ofReal_mul]
  exact Finset.sum_congr rfl fun j _ => hinner j

/-! ## Equation `(3)`: the paired source vanishes at contact -/

/-- **Equation `(3)`.**  A real-coefficient node packet has vanishing profile at contact. -/
theorem packetProfile_zero (w : Fin n → ℂ) (r : Fin n → ℝ) : packetProfile w r 0 = 0 := by
  unfold packetProfile nodePacket halfLineExpPacket
  simp [Complex.im_sum]

/-- The twisted and plain Cauchy double sums have equal real parts. -/
theorem re_sum_twisted_eq_re_sum_plain {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) :
    (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / ((starRingEnd ℂ) (w j) + w k)).re
      = (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k)).re := by
  have hA := two_mul_sum_plain hw r
  have hB := add_conj_sum_twisted hw r
  have hS1re : (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) /
        ((starRingEnd ℂ) (w j) + w k)).re
      + (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) /
        ((starRingEnd ℂ) (w j) + w k)).re = (∑ j, r j) ^ (2 : ℕ) := by
    have h := congrArg Complex.re hB
    rwa [Complex.add_re, Complex.conj_re, Complex.ofReal_re] at h
  have hS2re : 2 * (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k)).re
      = (∑ j, r j) ^ (2 : ℕ) := by
    have h := congrArg Complex.re hA
    rw [Complex.ofReal_re,
      show ((2 : ℂ) * ∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k)).re
        = 2 * (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k)).re by simp] at h
    exact h
  linarith

/-! ## Equation `(4)`: the contact derivative vanishes -/

theorem sum_neg_mul_autocorrCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) :
    (∑ k, -(w k) * autocorrCoeff w r k)
      = (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k))
        - ∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) / ((starRingEnd ℂ) (w j) + w k) := by
  classical
  have step1 : (∑ k, -(w k) * autocorrCoeff w r k)
      = ∑ k, ∑ j, ((r j : ℂ) * (r k : ℂ) * (w k) / (w j + w k)
          - (r j : ℂ) * (r k : ℂ) * (w k) / ((starRingEnd ℂ) (w j) + w k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold autocorrCoeff
    rw [show -(w k) * ((r k : ℂ) * ∑ j, ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) / (w j + w k)))
        = ∑ j, (-(w k) * (r k : ℂ)) * ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) / (w j + w k)) by
      rw [← Finset.mul_sum]
      ring]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [step1, Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]

/-- **Equation `(4)`.**  The paired autocorrelation has vanishing contact derivative:
`C_y'(0) = -y(0)^(2 : ℕ)/2 = 0`. -/
theorem packetAutocorrelationDeriv_zero {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) : packetAutocorrelationDeriv w r 0 = 0 := by
  classical
  unfold packetAutocorrelationDeriv halfLineExpPacket
  have hcoll : (∑ k, -(w k) * autocorrCoeff w r k * Complex.exp (-(w k) * ((0 : ℝ) : ℂ)))
      = ∑ k, -(w k) * autocorrCoeff w r k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  rw [hcoll, sum_neg_mul_autocorrCoeff, Complex.sub_re,
    re_sum_twisted_eq_re_sum_plain hw r]
  ring

/-! ## Equation `(5)`: the second contact derivative is the derivative energy -/

/-- The second transverse jet of the paired autocorrelation. -/
def packetAutocorrelationDeriv2 (w : Fin n → ℂ) (r : Fin n → ℝ) (tau : ℝ) : ℝ :=
  (1 / 2) * (halfLineExpPacket w
    (fun k => -(w k) * (-(w k) * autocorrCoeff w r k)) tau).re

theorem hasDerivAt_packetAutocorrelationDeriv (w : Fin n → ℂ) (r : Fin n → ℝ) (tau : ℝ) :
    HasDerivAt (packetAutocorrelationDeriv w r) (packetAutocorrelationDeriv2 w r tau) tau := by
  unfold packetAutocorrelationDeriv packetAutocorrelationDeriv2
  exact (hasDerivAt_re_halfLineExpPacket w (fun k => -(w k) * autocorrCoeff w r k)
    tau).const_mul (1 / 2 : ℝ)

theorem sum_sq_mul_autocorrCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) :
    (∑ k, -(w k) * (-(w k) * autocorrCoeff w r k))
      = (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / ((starRingEnd ℂ) (w j) + w k))
        - ∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / (w j + w k) := by
  classical
  have step1 : (∑ k, -(w k) * (-(w k) * autocorrCoeff w r k))
      = ∑ k, ∑ j, ((r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / (w j + w k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold autocorrCoeff
    rw [show -(w k) * (-(w k) * ((r k : ℂ) * ∑ j, ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) / (w j + w k))))
        = ∑ j, ((w k) ^ (2 : ℕ) * (r k : ℂ)) * ((r j : ℂ) / ((starRingEnd ℂ) (w j) + w k)
          - (r j : ℂ) / (w j + w k)) by
      rw [← Finset.mul_sum]
      ring]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [step1, Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]

/-- **Equation `(5)`.**  `C_y''(0) = -∫_0^∞ y'(x)^(2 : ℕ) dx`. -/
theorem packetAutocorrelationDeriv2_zero {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) :
    packetAutocorrelationDeriv2 w r 0
      = -∫ x in Ioi (0 : ℝ), (packetProfileDeriv w r x) ^ (2 : ℕ) := by
  classical
  have hne : ∀ j k : Fin n, w j + w k ≠ 0 := fun j k => add_ne_zero_of_re_pos (hw j) (hw k)
  have hcne : ∀ j k : Fin n, (starRingEnd ℂ) (w j) + w k ≠ 0 := fun j k =>
    add_ne_zero_of_re_pos (by simpa using hw j) (hw k)
  have hen := integral_im_sq_expPacket (w := w) (c := fun j => -(w j) * (r j : ℂ)) hw
  have hkey : (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / ((starRingEnd ℂ) (w j) + w k))
      + (∑ j, ∑ k, (starRingEnd ℂ) (-(w j) * (r j : ℂ)) * (-(w k) * (r k : ℂ)) /
          ((starRingEnd ℂ) (w j) + w k))
      = (∑ j, ∑ k, (r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / (w j + w k))
        + (∑ j, ∑ k, (-(w j) * (r j : ℂ)) * (-(w k) * (r k : ℂ)) / (w j + w k)) := by
    have hL : ∀ j k : Fin n,
        (r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / ((starRingEnd ℂ) (w j) + w k)
          + (starRingEnd ℂ) (-(w j) * (r j : ℂ)) * (-(w k) * (r k : ℂ)) /
              ((starRingEnd ℂ) (w j) + w k)
          = (r j : ℂ) * (r k : ℂ) * (w k) := by
      intro j k
      rw [map_mul, map_neg, Complex.conj_ofReal]
      have h0 := hcne j k
      field_simp
      try ring
    have hR : ∀ j k : Fin n,
        (r j : ℂ) * (r k : ℂ) * (w k) ^ (2 : ℕ) / (w j + w k)
          + (-(w j) * (r j : ℂ)) * (-(w k) * (r k : ℂ)) / (w j + w k)
          = (r j : ℂ) * (r k : ℂ) * (w k) := by
      intro j k
      have h0 := hne j k
      field_simp
      try ring
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hL j k, hR j k]
  have hre := congrArg Complex.re hkey
  rw [Complex.add_re, Complex.add_re] at hre
  have hprof : (fun x : ℝ => (packetProfileDeriv w r x) ^ (2 : ℕ))
      = fun x : ℝ => ((halfLineExpPacket w (fun j => -(w j) * (r j : ℂ)) x).im) ^ (2 : ℕ) := rfl
  unfold packetAutocorrelationDeriv2 halfLineExpPacket
  have hcoll : (∑ k, -(w k) * (-(w k) * autocorrCoeff w r k) *
      Complex.exp (-(w k) * ((0 : ℝ) : ℂ)))
      = ∑ k, -(w k) * (-(w k) * autocorrCoeff w r k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  rw [hcoll]
  have hsum := sum_sq_mul_autocorrCoeff w r
  rw [hsum, Complex.sub_re, hprof]
  linarith

/-! ## The contact laws in derivative form -/

/-- **Equation `(4)`, derivative form.**  `C_y'(0) = 0`. -/
theorem deriv_packetAutocorrelation_zero {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) : deriv (packetAutocorrelation w r) 0 = 0 := by
  rw [(hasDerivAt_packetAutocorrelation hw r 0).deriv, packetAutocorrelationDeriv_zero hw r]

/-- **Equation `(5)`, derivative form.**  `C_y''(0) = -∫_0^∞ y'(x)^(2 : ℕ) dx`. -/
theorem deriv_deriv_packetAutocorrelation_zero {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) :
    deriv (deriv (packetAutocorrelation w r)) 0
      = -∫ x in Ioi (0 : ℝ), (packetProfileDeriv w r x) ^ (2 : ℕ) := by
  have hfun : deriv (packetAutocorrelation w r) = packetAutocorrelationDeriv w r :=
    funext fun tau => (hasDerivAt_packetAutocorrelation hw r tau).deriv
  rw [hfun, (hasDerivAt_packetAutocorrelationDeriv w r 0).deriv,
    packetAutocorrelationDeriv2_zero hw r]

/-- The contact derivative of the paired autocorrelation is `O(h)` at the origin. -/
theorem packetAutocorrelationDeriv_isBigO {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) :
    packetAutocorrelationDeriv w r =O[nhds (0 : ℝ)] fun h : ℝ => h := by
  have h := (hasDerivAt_packetAutocorrelationDeriv w r 0).isBigO_sub
  simpa [packetAutocorrelationDeriv_zero hw r] using h

end

end RHTower
