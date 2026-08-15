import GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryScalarDressingRigidity

/-!
# Third-jet transverse activation at a Guinand--Weil prime-entry wall

The prime-entry first jet is a negative constant-boundary channel, and arbitrary scalar dressing
cannot make it visible after coefficient centering.  This file computes the next two actual
aperture jets of the same literal odd-source and weighted-cosine reporters.

The second jet remains a scalar multiple of the constant-boundary outer product and is again killed
by centering.  The third jet is different.  Its whole divided-difference matrix is the Loewner
matrix of a cubic-minus-linear source polynomial.  On every zero-sum coefficient packet `v`, its
quadratic form is exactly

```text
2 * pi^2 * q_k * (sum_i clock_i * v_i)^2,
q_k = 32 * criticalMellinAtomWeight(k) / log(k)^3.
```

For a genuine prime power `q_k>0`, so the third jet is positive semidefinite on the centered sector
and strictly positive exactly when the first clock moment is nonzero.  This is the first
source-derived transverse CCM channel at prime entry.  The complete `HasDerivAt` chain is proved;
the polynomial matrix is not a formal surrogate for an unverified derivative.
-/

open scoped BigOperators

namespace RHTower

open Matrix Filter

noncomputable section

/-! ## Horizon and reporter jet chains -/

/-- First aperture derivative of the moving horizon away from zero aperture. -/
def ccmGuinandWeilPrimeEntryHorizonJet1 (k : ℕ) (a : ℝ) : ℝ :=
  (Real.log k / 2) / a ^ 2

/-- Second aperture derivative of the moving horizon away from zero aperture. -/
def ccmGuinandWeilPrimeEntryHorizonJet2 (k : ℕ) (a : ℝ) : ℝ :=
  -2 * (Real.log k / 2) / a ^ 3

/-- Third aperture derivative of the moving horizon away from zero aperture. -/
def ccmGuinandWeilPrimeEntryHorizonJet3 (k : ℕ) (a : ℝ) : ℝ :=
  6 * (Real.log k / 2) / a ^ 4

theorem hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_jet1
    (k : ℕ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryHorizon k)
      (ccmGuinandWeilPrimeEntryHorizonJet1 k a) a := by
  have hquot := (hasDerivAt_const (x := a) (c := Real.log k / 2)).div
    (hasDerivAt_id (x := a)) ha
  have hraw := (hasDerivAt_const (x := a) (c := (1 : ℝ))).sub hquot
  have hraw' : HasDerivAt (fun x : ℝ => 1 - (Real.log k / 2) / x)
      ((Real.log k / 2) / a ^ 2) a := by
    apply hraw.congr_deriv
    simp only [id_eq, zero_mul, zero_sub]
    field_simp [ha]
  exact hraw'.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rw [ccmGuinandWeilPrimeEntryHorizon])

theorem hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet1
    (k : ℕ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryHorizonJet1 k)
      (ccmGuinandWeilPrimeEntryHorizonJet2 k a) a := by
  have hraw := (hasDerivAt_const (x := a) (c := Real.log k / 2)).div
    ((hasDerivAt_id (x := a)).pow 2) (pow_ne_zero 2 ha)
  have hraw' : HasDerivAt (fun x : ℝ => (Real.log k / 2) / x ^ 2)
      (-2 * (Real.log k / 2) / a ^ 3) a := by
    apply hraw.congr_deriv
    simp only [Pi.pow_apply, id_eq, zero_mul, zero_sub, Nat.cast_ofNat]
    field_simp [ha]
    ring
  exact hraw'.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rw [ccmGuinandWeilPrimeEntryHorizonJet1])

theorem hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet2
    (k : ℕ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryHorizonJet2 k)
      (ccmGuinandWeilPrimeEntryHorizonJet3 k a) a := by
  have hraw := (hasDerivAt_const (x := a) (c := -2 * (Real.log k / 2))).div
    ((hasDerivAt_id (x := a)).pow 3) (pow_ne_zero 3 ha)
  have hraw' : HasDerivAt (fun x : ℝ => -2 * (Real.log k / 2) / x ^ 3)
      (6 * (Real.log k / 2) / a ^ 4) a := by
    apply hraw.congr_deriv
    simp only [Pi.pow_apply, id_eq, zero_mul, zero_sub, Nat.cast_ofNat]
    field_simp [ha]
    ring
  exact hraw'.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rw [ccmGuinandWeilPrimeEntryHorizonJet2])

/-- First horizon jet of the odd reporter. -/
def ccmGuinandWeilPrimeEntryOddProfileJet1
    (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  -2 * (mode : ℝ) * criticalMellinAtomWeight k *
    Real.cos (2 * Real.pi * omega * (mode : ℝ))

/-- Second horizon jet of the odd reporter. -/
def ccmGuinandWeilPrimeEntryOddProfileJet2
    (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  4 * Real.pi * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k *
    Real.sin (2 * Real.pi * omega * (mode : ℝ))

/-- Third horizon jet of the odd reporter. -/
def ccmGuinandWeilPrimeEntryOddProfileJet3
    (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  8 * Real.pi ^ 2 * (mode : ℝ) ^ 3 * criticalMellinAtomWeight k *
    Real.cos (2 * Real.pi * omega * (mode : ℝ))

theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddProfile_jet1
    (k : ℕ) (mode : ℤ) (omega : ℝ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddProfile k mode)
      (ccmGuinandWeilPrimeEntryOddProfileJet1 k mode omega) omega := by
  have hphase : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) omega := by
    have hraw := ((hasDerivAt_id (x := omega)).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun x : ℝ => 2 * Real.pi * id x * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) omega :=
      hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by rfl)
  have hsin := (Real.hasDerivAt_sin
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have hscaled := (hsin.const_mul (-criticalMellinAtomWeight k)).div_const Real.pi
  have hscaled' : HasDerivAt
      (fun x : ℝ => -criticalMellinAtomWeight k *
        Real.sin (2 * Real.pi * x * (mode : ℝ)) / Real.pi)
      (ccmGuinandWeilPrimeEntryOddProfileJet1 k mode omega) omega := by
    apply hscaled.congr_deriv
    rw [ccmGuinandWeilPrimeEntryOddProfileJet1]
    field_simp [Real.pi_ne_zero]
  exact hscaled'.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rw [ccmGuinandWeilPrimeEntryOddProfile])

theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddProfileJet1
    (k : ℕ) (mode : ℤ) (omega : ℝ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddProfileJet1 k mode)
      (ccmGuinandWeilPrimeEntryOddProfileJet2 k mode omega) omega := by
  have hphase : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) omega := by
    have hraw := ((hasDerivAt_id (x := omega)).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun x : ℝ => 2 * Real.pi * id x * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) omega :=
      hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by rfl)
  have hcos := (Real.hasDerivAt_cos
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have hscaled := hcos.const_mul
    (-2 * (mode : ℝ) * criticalMellinAtomWeight k)
  have hscaled' : HasDerivAt
      (fun x : ℝ => -2 * (mode : ℝ) * criticalMellinAtomWeight k *
        Real.cos (2 * Real.pi * x * (mode : ℝ)))
      (ccmGuinandWeilPrimeEntryOddProfileJet2 k mode omega) omega := by
    apply hscaled.congr_deriv
    rw [ccmGuinandWeilPrimeEntryOddProfileJet2]
    ring
  exact hscaled'.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rw [ccmGuinandWeilPrimeEntryOddProfileJet1])

theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddProfileJet2
    (k : ℕ) (mode : ℤ) (omega : ℝ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddProfileJet2 k mode)
      (ccmGuinandWeilPrimeEntryOddProfileJet3 k mode omega) omega := by
  have hphase : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) omega := by
    have hraw := ((hasDerivAt_id (x := omega)).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun x : ℝ => 2 * Real.pi * id x * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) omega :=
      hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by rfl)
  have hsin := (Real.hasDerivAt_sin
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have hscaled := hsin.const_mul
    (4 * Real.pi * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k)
  have hscaled' : HasDerivAt
      (fun x : ℝ => 4 * Real.pi * (mode : ℝ) ^ 2 *
        criticalMellinAtomWeight k *
          Real.sin (2 * Real.pi * x * (mode : ℝ)))
      (ccmGuinandWeilPrimeEntryOddProfileJet3 k mode omega) omega := by
    apply hscaled.congr_deriv
    rw [ccmGuinandWeilPrimeEntryOddProfileJet3]
    ring
  exact hscaled'.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rw [ccmGuinandWeilPrimeEntryOddProfileJet2])

/-- First horizon jet of the weighted-cosine diagonal reporter. -/
def ccmGuinandWeilPrimeEntryDiagonalProfileJet1
    (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  -2 * criticalMellinAtomWeight k *
    (Real.cos (2 * Real.pi * omega * (mode : ℝ)) -
      (2 * Real.pi * (mode : ℝ)) * omega *
        Real.sin (2 * Real.pi * omega * (mode : ℝ)))

/-- Second horizon jet of the weighted-cosine diagonal reporter. -/
def ccmGuinandWeilPrimeEntryDiagonalProfileJet2
    (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  8 * Real.pi * (mode : ℝ) * criticalMellinAtomWeight k *
      Real.sin (2 * Real.pi * omega * (mode : ℝ)) +
    8 * Real.pi ^ 2 * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k * omega *
      Real.cos (2 * Real.pi * omega * (mode : ℝ))

/-- Third horizon jet of the weighted-cosine diagonal reporter. -/
def ccmGuinandWeilPrimeEntryDiagonalProfileJet3
    (k : ℕ) (mode : ℤ) (omega : ℝ) : ℝ :=
  24 * Real.pi ^ 2 * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k *
      Real.cos (2 * Real.pi * omega * (mode : ℝ)) -
    16 * Real.pi ^ 3 * (mode : ℝ) ^ 3 * criticalMellinAtomWeight k * omega *
      Real.sin (2 * Real.pi * omega * (mode : ℝ))

theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfile_jet1
    (k : ℕ) (mode : ℤ) (omega : ℝ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalProfile k mode)
      (ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode omega) omega := by
  have hphase : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) omega := by
    have hraw := ((hasDerivAt_id (x := omega)).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun x : ℝ => 2 * Real.pi * id x * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) omega :=
      hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by rfl)
  have hcos := (Real.hasDerivAt_cos
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have hprod := (hasDerivAt_id (x := omega)).mul hcos
  have hscaled := hprod.const_mul (-2 * criticalMellinAtomWeight k)
  have hscaled' : HasDerivAt
      (fun x : ℝ => -2 * criticalMellinAtomWeight k *
        (x * Real.cos (2 * Real.pi * x * (mode : ℝ))))
      (ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode omega) omega := by
    apply hscaled.congr_deriv
    rw [ccmGuinandWeilPrimeEntryDiagonalProfileJet1]
    simp only [id_eq, Function.comp_apply]
    ring
  exact hscaled'.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rw [ccmGuinandWeilPrimeEntryDiagonalProfile]
      ring)

theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfileJet1
    (k : ℕ) (mode : ℤ) (omega : ℝ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode)
      (ccmGuinandWeilPrimeEntryDiagonalProfileJet2 k mode omega) omega := by
  have hphase : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) omega := by
    have hraw := ((hasDerivAt_id (x := omega)).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun x : ℝ => 2 * Real.pi * id x * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) omega :=
      hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by rfl)
  have hsin := (Real.hasDerivAt_sin
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have hcos := (Real.hasDerivAt_cos
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have homegaSin := (hasDerivAt_id (x := omega)).mul hsin
  have hinside := hcos.sub
    (homegaSin.const_mul (2 * Real.pi * (mode : ℝ)))
  have hscaled := hinside.const_mul (-2 * criticalMellinAtomWeight k)
  have hfunc : HasDerivAt
      (fun x : ℝ => -2 * criticalMellinAtomWeight k *
        (Real.cos (2 * Real.pi * x * (mode : ℝ)) -
          (2 * Real.pi * (mode : ℝ)) * x *
            Real.sin (2 * Real.pi * x * (mode : ℝ))))
      (-2 * criticalMellinAtomWeight k *
        (-Real.sin (2 * Real.pi * omega * (mode : ℝ)) *
            (2 * Real.pi * (mode : ℝ)) -
          2 * Real.pi * (mode : ℝ) *
            (1 * Real.sin (2 * Real.pi * omega * (mode : ℝ)) +
              omega * (Real.cos (2 * Real.pi * omega * (mode : ℝ)) *
                (2 * Real.pi * (mode : ℝ)))))) omega :=
    hscaled.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by
        simp only [id_eq, Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
        ring)
  have htarget : HasDerivAt
      (fun x : ℝ => -2 * criticalMellinAtomWeight k *
        (Real.cos (2 * Real.pi * x * (mode : ℝ)) -
          (2 * Real.pi * (mode : ℝ)) * x *
            Real.sin (2 * Real.pi * x * (mode : ℝ))))
      (ccmGuinandWeilPrimeEntryDiagonalProfileJet2 k mode omega) omega := by
    apply hfunc.congr_deriv
    unfold ccmGuinandWeilPrimeEntryDiagonalProfileJet2
    ring
  exact htarget.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rfl)

theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfileJet2
    (k : ℕ) (mode : ℤ) (omega : ℝ) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalProfileJet2 k mode)
      (ccmGuinandWeilPrimeEntryDiagonalProfileJet3 k mode omega) omega := by
  have hphase : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x * (mode : ℝ))
      (2 * Real.pi * (mode : ℝ)) omega := by
    have hraw := ((hasDerivAt_id (x := omega)).const_mul
      (2 * Real.pi)).mul_const (mode : ℝ)
    have hraw' : HasDerivAt
        (fun x : ℝ => 2 * Real.pi * id x * (mode : ℝ))
        (2 * Real.pi * (mode : ℝ)) omega :=
      hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by rfl)
  have hsin := (Real.hasDerivAt_sin
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have hcos := (Real.hasDerivAt_cos
    (2 * Real.pi * omega * (mode : ℝ))).comp omega hphase
  have hterm1 := hsin.const_mul
    (8 * Real.pi * (mode : ℝ) * criticalMellinAtomWeight k)
  have hterm2 := ((hasDerivAt_id (x := omega)).mul hcos).const_mul
    (8 * Real.pi ^ 2 * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k)
  have hsum := hterm1.add hterm2
  have hfunc : HasDerivAt
      (fun x : ℝ =>
        8 * Real.pi * (mode : ℝ) * criticalMellinAtomWeight k *
            Real.sin (2 * Real.pi * x * (mode : ℝ)) +
          8 * Real.pi ^ 2 * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k * x *
            Real.cos (2 * Real.pi * x * (mode : ℝ)))
      (8 * Real.pi * (mode : ℝ) * criticalMellinAtomWeight k *
          (Real.cos (2 * Real.pi * omega * (mode : ℝ)) *
            (2 * Real.pi * (mode : ℝ))) +
        8 * Real.pi ^ 2 * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k *
          (1 * Real.cos (2 * Real.pi * omega * (mode : ℝ)) +
            omega * (-Real.sin (2 * Real.pi * omega * (mode : ℝ)) *
              (2 * Real.pi * (mode : ℝ))))) omega :=
    hsum.congr_of_eventuallyEq
      (Eventually.of_forall fun x => by
        simp only [id_eq, Function.comp_apply, Pi.add_apply, Pi.mul_apply]
        ring)
  have htarget : HasDerivAt
      (fun x : ℝ =>
        8 * Real.pi * (mode : ℝ) * criticalMellinAtomWeight k *
            Real.sin (2 * Real.pi * x * (mode : ℝ)) +
          8 * Real.pi ^ 2 * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k * x *
            Real.cos (2 * Real.pi * x * (mode : ℝ)))
      (ccmGuinandWeilPrimeEntryDiagonalProfileJet3 k mode omega) omega := by
    apply hfunc.congr_deriv
    unfold ccmGuinandWeilPrimeEntryDiagonalProfileJet3
    ring
  exact htarget.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      rfl)

/-! ## Aperture-chain pullback -/

private theorem hasDerivAt_compJet0
    {f0 f1 g0 g1 : ℝ → ℝ} {a : ℝ}
    (hf0 : HasDerivAt f0 (f1 (g0 a)) (g0 a))
    (hg0 : HasDerivAt g0 (g1 a) a) :
    HasDerivAt (fun x => f0 (g0 x)) (f1 (g0 a) * g1 a) a := by
  exact hf0.comp a hg0

private theorem hasDerivAt_compJet1
    {f1 f2 g0 g1 g2 : ℝ → ℝ} {a : ℝ}
    (hf1 : HasDerivAt f1 (f2 (g0 a)) (g0 a))
    (hg0 : HasDerivAt g0 (g1 a) a)
    (hg1 : HasDerivAt g1 (g2 a) a) :
    HasDerivAt (fun x => f1 (g0 x) * g1 x)
      (f2 (g0 a) * (g1 a) ^ 2 + f1 (g0 a) * g2 a) a := by
  have hraw := (hf1.comp a hg0).mul hg1
  exact hraw.congr_deriv (by
    simp only [Function.comp_apply]
    ring)

private theorem hasDerivAt_compJet2
    {f1 f2 f3 g0 g1 g2 g3 : ℝ → ℝ} {a : ℝ}
    (hf1 : HasDerivAt f1 (f2 (g0 a)) (g0 a))
    (hf2 : HasDerivAt f2 (f3 (g0 a)) (g0 a))
    (hg0 : HasDerivAt g0 (g1 a) a)
    (hg1 : HasDerivAt g1 (g2 a) a)
    (hg2 : HasDerivAt g2 (g3 a) a) :
    HasDerivAt
      (fun x => f2 (g0 x) * (g1 x) ^ 2 + f1 (g0 x) * g2 x)
      (f3 (g0 a) * (g1 a) ^ 3 +
        3 * f2 (g0 a) * g1 a * g2 a + f1 (g0 a) * g3 a) a := by
  have hterm1 := (hf2.comp a hg0).mul (hg1.pow 2)
  have hterm2 := (hf1.comp a hg0).mul hg2
  have hraw := hterm1.add hterm2
  exact hraw.congr_deriv (by
    simp only [Function.comp_apply, Pi.pow_apply]
    ring)

/-- First aperture jet of the pulled-back odd reporter. -/
def ccmGuinandWeilPrimeEntryOddGermJet1
    (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryOddProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
    ccmGuinandWeilPrimeEntryHorizonJet1 k a

/-- Second aperture jet of the pulled-back odd reporter. -/
def ccmGuinandWeilPrimeEntryOddGermJet2
    (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryOddProfileJet2 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      (ccmGuinandWeilPrimeEntryHorizonJet1 k a) ^ 2 +
    ccmGuinandWeilPrimeEntryOddProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      ccmGuinandWeilPrimeEntryHorizonJet2 k a

/-- Third aperture jet of the pulled-back odd reporter. -/
def ccmGuinandWeilPrimeEntryOddGermJet3
    (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryOddProfileJet3 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      (ccmGuinandWeilPrimeEntryHorizonJet1 k a) ^ 3 +
    3 * ccmGuinandWeilPrimeEntryOddProfileJet2 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      ccmGuinandWeilPrimeEntryHorizonJet1 k a *
      ccmGuinandWeilPrimeEntryHorizonJet2 k a +
    ccmGuinandWeilPrimeEntryOddProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      ccmGuinandWeilPrimeEntryHorizonJet3 k a

theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddGerm_jet1
    (k : ℕ) (mode : ℤ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddGerm k mode)
      (ccmGuinandWeilPrimeEntryOddGermJet1 k mode a) a := by
  have h := hasDerivAt_compJet0
    (hasDerivAt_ccmGuinandWeilPrimeEntryOddProfile_jet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_jet1 k ha)
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by rfl)

theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddGermJet1
    (k : ℕ) (mode : ℤ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddGermJet1 k mode)
      (ccmGuinandWeilPrimeEntryOddGermJet2 k mode a) a := by
  have h := hasDerivAt_compJet1
    (hasDerivAt_ccmGuinandWeilPrimeEntryOddProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_jet1 k ha)
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet1 k ha)
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by rfl)

theorem hasDerivAt_ccmGuinandWeilPrimeEntryOddGermJet2
    (k : ℕ) (mode : ℤ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryOddGermJet2 k mode)
      (ccmGuinandWeilPrimeEntryOddGermJet3 k mode a) a := by
  have h := hasDerivAt_compJet2
    (hasDerivAt_ccmGuinandWeilPrimeEntryOddProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryOddProfileJet2 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_jet1 k ha)
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet1 k ha)
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet2 k ha)
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by rfl)

/-- First aperture jet of the pulled-back diagonal reporter. -/
def ccmGuinandWeilPrimeEntryDiagonalGermJet1
    (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
    ccmGuinandWeilPrimeEntryHorizonJet1 k a

/-- Second aperture jet of the pulled-back diagonal reporter. -/
def ccmGuinandWeilPrimeEntryDiagonalGermJet2
    (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalProfileJet2 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      (ccmGuinandWeilPrimeEntryHorizonJet1 k a) ^ 2 +
    ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      ccmGuinandWeilPrimeEntryHorizonJet2 k a

/-- Third aperture jet of the pulled-back diagonal reporter. -/
def ccmGuinandWeilPrimeEntryDiagonalGermJet3
    (k : ℕ) (mode : ℤ) (a : ℝ) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalProfileJet3 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      (ccmGuinandWeilPrimeEntryHorizonJet1 k a) ^ 3 +
    3 * ccmGuinandWeilPrimeEntryDiagonalProfileJet2 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      ccmGuinandWeilPrimeEntryHorizonJet1 k a *
      ccmGuinandWeilPrimeEntryHorizonJet2 k a +
    ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a) *
      ccmGuinandWeilPrimeEntryHorizonJet3 k a

theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGerm_jet1
    (k : ℕ) (mode : ℤ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalGerm k mode)
      (ccmGuinandWeilPrimeEntryDiagonalGermJet1 k mode a) a := by
  have h := hasDerivAt_compJet0
    (hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfile_jet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_jet1 k ha)
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by rfl)

theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGermJet1
    (k : ℕ) (mode : ℤ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalGermJet1 k mode)
      (ccmGuinandWeilPrimeEntryDiagonalGermJet2 k mode a) a := by
  have h := hasDerivAt_compJet1
    (hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_jet1 k ha)
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet1 k ha)
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by rfl)

theorem hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGermJet2
    (k : ℕ) (mode : ℤ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (ccmGuinandWeilPrimeEntryDiagonalGermJet2 k mode)
      (ccmGuinandWeilPrimeEntryDiagonalGermJet3 k mode a) a := by
  have h := hasDerivAt_compJet2
    (hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalProfileJet2 k mode
      (ccmGuinandWeilPrimeEntryHorizon k a))
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizon_jet1 k ha)
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet1 k ha)
    (hasDerivAt_ccmGuinandWeilPrimeEntryHorizonJet2 k ha)
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by rfl)

/-! ## Exact entry-wall values -/

/-- Moving horizon has entry velocity `2 / log k`. -/
theorem ccmGuinandWeilPrimeEntryHorizonJet1_at_entry
    {k : ℕ} (hk : 1 < k) :
    ccmGuinandWeilPrimeEntryHorizonJet1 k
        (ccmGuinandWeilPrimeEntryAperture k) = 2 / Real.log k := by
  have hlog : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hk)).ne'
  unfold ccmGuinandWeilPrimeEntryHorizonJet1 ccmGuinandWeilPrimeEntryAperture
  field_simp [hlog]

theorem ccmGuinandWeilPrimeEntryHorizonJet2_at_entry
    {k : ℕ} (hk : 1 < k) :
    ccmGuinandWeilPrimeEntryHorizonJet2 k
        (ccmGuinandWeilPrimeEntryAperture k) = -8 / Real.log k ^ 2 := by
  have hlog : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hk)).ne'
  unfold ccmGuinandWeilPrimeEntryHorizonJet2 ccmGuinandWeilPrimeEntryAperture
  field_simp [hlog]
  ring

theorem ccmGuinandWeilPrimeEntryHorizonJet3_at_entry
    {k : ℕ} (hk : 1 < k) :
    ccmGuinandWeilPrimeEntryHorizonJet3 k
        (ccmGuinandWeilPrimeEntryAperture k) = 48 / Real.log k ^ 3 := by
  have hlog : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hk)).ne'
  unfold ccmGuinandWeilPrimeEntryHorizonJet3 ccmGuinandWeilPrimeEntryAperture
  field_simp [hlog]
  ring

@[simp] theorem ccmGuinandWeilPrimeEntryOddProfileJet1_zero
    (k : ℕ) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryOddProfileJet1 k mode 0 =
      -2 * (mode : ℝ) * criticalMellinAtomWeight k := by
  simp [ccmGuinandWeilPrimeEntryOddProfileJet1]

@[simp] theorem ccmGuinandWeilPrimeEntryOddProfileJet2_zero
    (k : ℕ) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryOddProfileJet2 k mode 0 = 0 := by
  simp [ccmGuinandWeilPrimeEntryOddProfileJet2]

@[simp] theorem ccmGuinandWeilPrimeEntryOddProfileJet3_zero
    (k : ℕ) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryOddProfileJet3 k mode 0 =
      8 * Real.pi ^ 2 * (mode : ℝ) ^ 3 * criticalMellinAtomWeight k := by
  simp [ccmGuinandWeilPrimeEntryOddProfileJet3]

@[simp] theorem ccmGuinandWeilPrimeEntryDiagonalProfileJet1_zero
    (k : ℕ) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryDiagonalProfileJet1 k mode 0 =
      -2 * criticalMellinAtomWeight k := by
  simp [ccmGuinandWeilPrimeEntryDiagonalProfileJet1]

@[simp] theorem ccmGuinandWeilPrimeEntryDiagonalProfileJet2_zero
    (k : ℕ) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryDiagonalProfileJet2 k mode 0 = 0 := by
  simp [ccmGuinandWeilPrimeEntryDiagonalProfileJet2]

@[simp] theorem ccmGuinandWeilPrimeEntryDiagonalProfileJet3_zero
    (k : ℕ) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryDiagonalProfileJet3 k mode 0 =
      24 * Real.pi ^ 2 * (mode : ℝ) ^ 2 * criticalMellinAtomWeight k := by
  simp [ccmGuinandWeilPrimeEntryDiagonalProfileJet3]

/-- Odd second aperture jet is linear in Fourier mode. -/
theorem ccmGuinandWeilPrimeEntryOddGermJet2_at_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryOddGermJet2 k mode
        (ccmGuinandWeilPrimeEntryAperture k) =
      16 * (mode : ℝ) * criticalMellinAtomWeight k / Real.log k ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryOddGermJet2,
    ccmGuinandWeilPrimeEntryHorizon_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet1_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet2_at_entry hk]
  simp
  ring

/-- Diagonal second aperture jet remains mode-independent. -/
theorem ccmGuinandWeilPrimeEntryDiagonalGermJet2_at_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryDiagonalGermJet2 k mode
        (ccmGuinandWeilPrimeEntryAperture k) =
      16 * criticalMellinAtomWeight k / Real.log k ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryDiagonalGermJet2,
    ccmGuinandWeilPrimeEntryHorizon_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet1_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet2_at_entry hk]
  simp
  ring

/-- Odd third aperture jet is cubic-minus-linear in Fourier mode. -/
theorem ccmGuinandWeilPrimeEntryOddGermJet3_at_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryOddGermJet3 k mode
        (ccmGuinandWeilPrimeEntryAperture k) =
      32 * (mode : ℝ) * criticalMellinAtomWeight k *
        (2 * Real.pi ^ 2 * (mode : ℝ) ^ 2 - 3) / Real.log k ^ 3 := by
  rw [ccmGuinandWeilPrimeEntryOddGermJet3,
    ccmGuinandWeilPrimeEntryHorizon_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet1_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet2_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet3_at_entry hk]
  simp
  ring

/-- Diagonal third aperture jet is the derivative of the cubic odd-source polynomial. -/
theorem ccmGuinandWeilPrimeEntryDiagonalGermJet3_at_entry
    {k : ℕ} (hk : 1 < k) (mode : ℤ) :
    ccmGuinandWeilPrimeEntryDiagonalGermJet3 k mode
        (ccmGuinandWeilPrimeEntryAperture k) =
      96 * criticalMellinAtomWeight k *
        (2 * Real.pi ^ 2 * (mode : ℝ) ^ 2 - 1) / Real.log k ^ 3 := by
  rw [ccmGuinandWeilPrimeEntryDiagonalGermJet3,
    ccmGuinandWeilPrimeEntryHorizon_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet1_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet2_at_entry hk,
    ccmGuinandWeilPrimeEntryHorizonJet3_at_entry hk]
  simp
  ring

/-! ## Cubic Loewner matrix and transverse positivity -/

/-- Positive third-jet scale at genuine prime powers. -/
def ccmGuinandWeilPrimeEntryThirdJetScale (k : ℕ) : ℝ :=
  32 * criticalMellinAtomWeight k / Real.log k ^ 3

def ccmGuinandWeilPrimeEntryCenteredSourceJet3
    (k N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryOddGermJet3 k
    (ccmPublishedCenteredMode N i) (ccmGuinandWeilPrimeEntryAperture k)

def ccmGuinandWeilPrimeEntryCenteredDiagonalJet3
    (k N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalGermJet3 k
    (ccmPublishedCenteredMode N i) (ccmGuinandWeilPrimeEntryAperture k)

/-- Whole centered divided-difference third jet at the entry wall. -/
def ccmGuinandWeilPrimeEntryCenteredMatrixJet3 (k N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet3 k N)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet3 k N)

theorem ccmGuinandWeilPrimeEntryCenteredSourceJet3_eq
    {k : ℕ} (hk : 1 < k) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmGuinandWeilPrimeEntryCenteredSourceJet3 k N i =
      ccmGuinandWeilPrimeEntryThirdJetScale k *
        ccmPublishedCenteredClock N i *
          (2 * Real.pi ^ 2 * ccmPublishedCenteredClock N i ^ 2 - 3) := by
  rw [ccmGuinandWeilPrimeEntryCenteredSourceJet3,
    ccmGuinandWeilPrimeEntryOddGermJet3_at_entry hk,
    ccmGuinandWeilPrimeEntryThirdJetScale, ccmPublishedCenteredClock]
  ring

theorem ccmGuinandWeilPrimeEntryCenteredDiagonalJet3_eq
    {k : ℕ} (hk : 1 < k) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmGuinandWeilPrimeEntryCenteredDiagonalJet3 k N i =
      3 * ccmGuinandWeilPrimeEntryThirdJetScale k *
        (2 * Real.pi ^ 2 * ccmPublishedCenteredClock N i ^ 2 - 1) := by
  rw [ccmGuinandWeilPrimeEntryCenteredDiagonalJet3,
    ccmGuinandWeilPrimeEntryDiagonalGermJet3_at_entry hk,
    ccmGuinandWeilPrimeEntryThirdJetScale, ccmPublishedCenteredClock]
  ring

/-- Exact cubic Loewner entry formula. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_apply
    {k : ℕ} (hk : 1 < k) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N i j =
      ccmGuinandWeilPrimeEntryThirdJetScale k *
        (2 * Real.pi ^ 2 *
          (ccmPublishedCenteredClock N i ^ 2 +
            ccmPublishedCenteredClock N i * ccmPublishedCenteredClock N j +
            ccmPublishedCenteredClock N j ^ 2) - 3) := by
  by_cases hij : i = j
  · subst j
    rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3,
      ccmDividedDifferenceMatrix, if_pos rfl,
      ccmGuinandWeilPrimeEntryCenteredDiagonalJet3_eq hk]
    ring
  · rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3,
      ccmDividedDifferenceMatrix, if_neg hij,
      ccmGuinandWeilPrimeEntryCenteredSourceJet3_eq hk,
      ccmGuinandWeilPrimeEntryCenteredSourceJet3_eq hk]
    have hclock : ccmPublishedCenteredClock N i -
        ccmPublishedCenteredClock N j ≠ 0 :=
      sub_ne_zero.mpr ((ccmPublishedCenteredClock_injective N).ne hij)
    field_simp [hclock]
    ring

/-- The cubic Loewner jet has a four-term outer-product decomposition. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_eq_outerProducts
    {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N =
      (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k) •
          Matrix.vecMulVec
            (fun i : Fin (2 * N + 1) => ccmPublishedCenteredClock N i ^ 2)
            ccmConstantBoundary +
        (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k) •
          Matrix.vecMulVec (ccmPublishedCenteredClock N)
            (ccmPublishedCenteredClock N) +
        (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k) •
          Matrix.vecMulVec ccmConstantBoundary
            (fun i : Fin (2 * N + 1) => ccmPublishedCenteredClock N i ^ 2) -
        (3 * ccmGuinandWeilPrimeEntryThirdJetScale k) •
          Matrix.vecMulVec ccmConstantBoundary ccmConstantBoundary := by
  ext i j
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_apply hk]
  simp [Matrix.vecMulVec_apply, ccmConstantBoundary]
  ring

/-- **Transverse third-jet square law.** On the zero-sum sector, all central terms vanish and only
the positive clock outer product survives. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_quadratic_of_sum_eq_zero
    {k : ℕ} (hk : 1 < k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    dotProduct v (ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N *ᵥ v) =
      2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k *
        (∑ i, ccmPublishedCenteredClock N i * v i) ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_eq_outerProducts hk]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [ccmConstantBoundary, one_mul]
  rw [hv]
  simp
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ x, v x *
        (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k *
          (ccmPublishedCenteredClock N x *
            ∑ i, ccmPublishedCenteredClock N i * v i))) =
        (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k) *
          (∑ i, ccmPublishedCenteredClock N i * v i) *
            (∑ x, v x * ccmPublishedCenteredClock N x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsecond :
      (∑ x, v x *
        (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k *
          ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x)) =
        (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k) *
          (∑ x, ccmPublishedCenteredClock N x ^ 2 * v x) *
            (∑ x, v x) := by
    calc
      (∑ x, v x *
          (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k *
            ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x)) =
          (∑ x, v x) *
            (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k *
              ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x) :=
        (Finset.sum_mul Finset.univ (fun x => v x)
          (2 * Real.pi ^ 2 * ccmGuinandWeilPrimeEntryThirdJetScale k *
            ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x)).symm
      _ = _ := by ring
  rw [hfirst, hsecond, hv]
  simp
  have hcomm : (∑ x, v x * ccmPublishedCenteredClock N x) =
      ∑ x, ccmPublishedCenteredClock N x * v x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hcomm]
  ring

theorem ccmGuinandWeilPrimeEntryThirdJetScale_pos
    {k : ℕ} (hk : IsPrimePow k) :
    0 < ccmGuinandWeilPrimeEntryThirdJetScale k := by
  rw [ccmGuinandWeilPrimeEntryThirdJetScale]
  exact div_pos (mul_pos (by norm_num) (criticalMellinAtomWeight_pos hk))
    (pow_pos (Real.log_pos (by exact_mod_cast hk.one_lt)) 3)

/-- A genuine prime-power third jet is positive semidefinite on the centered sector. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_quadratic_nonneg_of_sum_eq_zero
    {k : ℕ} (hk : IsPrimePow k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    0 ≤ dotProduct v
      (ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N *ᵥ v) := by
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_quadratic_of_sum_eq_zero
    hk.one_lt N v hv]
  have hscale := ccmGuinandWeilPrimeEntryThirdJetScale_pos hk
  positivity

/-- Centered third-jet positivity is strict exactly when the first clock moment is visible. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_quadratic_pos_of_sum_eq_zero
    {k : ℕ} (hk : IsPrimePow k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0)
    (hmoment : (∑ i, ccmPublishedCenteredClock N i * v i) ≠ 0) :
    0 < dotProduct v
      (ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N *ᵥ v) := by
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_quadratic_of_sum_eq_zero
    hk.one_lt N v hv]
  have hscale := ccmGuinandWeilPrimeEntryThirdJetScale_pos hk
  positivity

/-! ## Second-jet centrality -/

/-- Common second-jet entry scale. -/
def ccmGuinandWeilPrimeEntrySecondJetScale (k : ℕ) : ℝ :=
  16 * criticalMellinAtomWeight k / Real.log k ^ 2

def ccmGuinandWeilPrimeEntryCenteredSourceJet2
    (k N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryOddGermJet2 k
    (ccmPublishedCenteredMode N i) (ccmGuinandWeilPrimeEntryAperture k)

def ccmGuinandWeilPrimeEntryCenteredDiagonalJet2
    (k N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalGermJet2 k
    (ccmPublishedCenteredMode N i) (ccmGuinandWeilPrimeEntryAperture k)

/-- Whole centered divided-difference second jet at the entry wall. -/
def ccmGuinandWeilPrimeEntryCenteredMatrixJet2 (k N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet2 k N)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet2 k N)

theorem ccmGuinandWeilPrimeEntryCenteredSourceJet2_eq
    {k : ℕ} (hk : 1 < k) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmGuinandWeilPrimeEntryCenteredSourceJet2 k N i =
      ccmGuinandWeilPrimeEntrySecondJetScale k *
        ccmPublishedCenteredClock N i := by
  rw [ccmGuinandWeilPrimeEntryCenteredSourceJet2,
    ccmGuinandWeilPrimeEntryOddGermJet2_at_entry hk,
    ccmGuinandWeilPrimeEntrySecondJetScale, ccmPublishedCenteredClock]
  ring

theorem ccmGuinandWeilPrimeEntryCenteredDiagonalJet2_eq
    {k : ℕ} (hk : 1 < k) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmGuinandWeilPrimeEntryCenteredDiagonalJet2 k N i =
      ccmGuinandWeilPrimeEntrySecondJetScale k := by
  rw [ccmGuinandWeilPrimeEntryCenteredDiagonalJet2,
    ccmGuinandWeilPrimeEntryDiagonalGermJet2_at_entry hk,
    ccmGuinandWeilPrimeEntrySecondJetScale]

/-- Second jet still factors through the constant-boundary outer product. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet2_eq_rankOne
    {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet2 k N =
      ccmGuinandWeilPrimeEntrySecondJetScale k •
        Matrix.vecMulVec
          (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
          ccmConstantBoundary := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet2,
      ccmDividedDifferenceMatrix, if_pos rfl,
      ccmGuinandWeilPrimeEntryCenteredDiagonalJet2_eq hk]
    simp [Matrix.vecMulVec_apply, ccmConstantBoundary]
  · rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet2,
      ccmDividedDifferenceMatrix, if_neg hij,
      ccmGuinandWeilPrimeEntryCenteredSourceJet2_eq hk,
      ccmGuinandWeilPrimeEntryCenteredSourceJet2_eq hk]
    have hclock : ccmPublishedCenteredClock N i -
        ccmPublishedCenteredClock N j ≠ 0 :=
      sub_ne_zero.mpr ((ccmPublishedCenteredClock_injective N).ne hij)
    simp [Matrix.vecMulVec_apply, ccmConstantBoundary]
    field_simp [hclock]

/-- Canonical centering annihilates the complete second jet. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet2_centerCoefficients_eq_zero
    {k : ℕ} (hk : 1 < k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet2 k N *ᵥ
        ccmGuinandWeilCenterCoefficients N v = 0 := by
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet2_eq_rankOne hk]
  rw [Matrix.smul_mulVec]
  have hzero : Matrix.vecMulVec
      (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
      (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) *ᵥ
        ccmGuinandWeilCenterCoefficients N v = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
      ccmConstantBoundary, one_mul]
    rw [sum_ccmGuinandWeilCenterCoefficients]
    rfl
  rw [hzero, smul_zero]

/-! ## Whole-matrix derivative chain -/

private theorem hasDerivAt_ccmDividedDifferenceMatrix_apply
    {ι : Type*} [DecidableEq ι]
    (clock : ι → ℝ) (hclock : Function.Injective clock)
    (source sourceJet diagonal diagonalJet : ℝ → ι → ℝ)
    {a : ℝ} (i j : ι)
    (hsource : ∀ r, HasDerivAt (fun x => source x r) (sourceJet a r) a)
    (hdiagonal : ∀ r, HasDerivAt (fun x => diagonal x r) (diagonalJet a r) a) :
    HasDerivAt
      (fun x => ccmDividedDifferenceMatrix clock (source x) (diagonal x) i j)
      (ccmDividedDifferenceMatrix clock (sourceJet a) (diagonalJet a) i j) a := by
  by_cases hij : i = j
  · subst j
    simpa [ccmDividedDifferenceMatrix] using hdiagonal i
  · have hdenom : clock i - clock j ≠ 0 :=
      sub_ne_zero.mpr (hclock.ne hij)
    have hquot := ((hsource i).sub (hsource j)).div_const (clock i - clock j)
    simpa [ccmDividedDifferenceMatrix, hij] using hquot

def ccmGuinandWeilPrimeEntryCenteredSourceJet1Path
    (k N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryOddGermJet1 k (ccmPublishedCenteredMode N i) a

def ccmGuinandWeilPrimeEntryCenteredDiagonalJet1Path
    (k N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalGermJet1 k (ccmPublishedCenteredMode N i) a

def ccmGuinandWeilPrimeEntryCenteredSourceJet2Path
    (k N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryOddGermJet2 k (ccmPublishedCenteredMode N i) a

def ccmGuinandWeilPrimeEntryCenteredDiagonalJet2Path
    (k N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalGermJet2 k (ccmPublishedCenteredMode N i) a

def ccmGuinandWeilPrimeEntryCenteredSourceJet3Path
    (k N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryOddGermJet3 k (ccmPublishedCenteredMode N i) a

def ccmGuinandWeilPrimeEntryCenteredDiagonalJet3Path
    (k N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalGermJet3 k (ccmPublishedCenteredMode N i) a

/-- Whole divided-difference first-jet path before entry evaluation. -/
def ccmGuinandWeilPrimeEntryCenteredMatrixJet1Path
    (k N : ℕ) (a : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet1Path k N a)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet1Path k N a)

/-- Whole divided-difference second-jet path before entry evaluation. -/
def ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path
    (k N : ℕ) (a : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet2Path k N a)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet2Path k N a)

/-- Whole divided-difference third-jet path before entry evaluation. -/
def ccmGuinandWeilPrimeEntryCenteredMatrixJet3Path
    (k N : ℕ) (a : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet3Path k N a)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet3Path k N a)

theorem hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrix_jet1_apply
    (k N : ℕ) {a : ℝ} (ha : a ≠ 0)
    (i j : Fin (2 * N + 1)) :
    HasDerivAt (fun x => ccmGuinandWeilPrimeEntryCenteredMatrix k N x i j)
      (ccmGuinandWeilPrimeEntryCenteredMatrixJet1Path k N a i j) a := by
  apply hasDerivAt_ccmDividedDifferenceMatrix_apply
    (ccmPublishedCenteredClock N) (ccmPublishedCenteredClock_injective N)
    (fun x => ccmGuinandWeilPrimeEntryCenteredSource k N x)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet1Path k N)
    (fun x => ccmGuinandWeilPrimeEntryCenteredDiagonal k N x)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet1Path k N)
  · intro r
    exact hasDerivAt_ccmGuinandWeilPrimeEntryOddGerm_jet1 k
      (ccmPublishedCenteredMode N r) ha
  · intro r
    exact hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGerm_jet1 k
      (ccmPublishedCenteredMode N r) ha

theorem hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrixJet1Path_apply
    (k N : ℕ) {a : ℝ} (ha : a ≠ 0)
    (i j : Fin (2 * N + 1)) :
    HasDerivAt
      (fun x => ccmGuinandWeilPrimeEntryCenteredMatrixJet1Path k N x i j)
      (ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path k N a i j) a := by
  apply hasDerivAt_ccmDividedDifferenceMatrix_apply
    (ccmPublishedCenteredClock N) (ccmPublishedCenteredClock_injective N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet1Path k N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet2Path k N)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet1Path k N)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet2Path k N)
  · intro r
    exact hasDerivAt_ccmGuinandWeilPrimeEntryOddGermJet1 k
      (ccmPublishedCenteredMode N r) ha
  · intro r
    exact hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGermJet1 k
      (ccmPublishedCenteredMode N r) ha

theorem hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path_apply
    (k N : ℕ) {a : ℝ} (ha : a ≠ 0)
    (i j : Fin (2 * N + 1)) :
    HasDerivAt
      (fun x => ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path k N x i j)
      (ccmGuinandWeilPrimeEntryCenteredMatrixJet3Path k N a i j) a := by
  apply hasDerivAt_ccmDividedDifferenceMatrix_apply
    (ccmPublishedCenteredClock N) (ccmPublishedCenteredClock_injective N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet2Path k N)
    (ccmGuinandWeilPrimeEntryCenteredSourceJet3Path k N)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet2Path k N)
    (ccmGuinandWeilPrimeEntryCenteredDiagonalJet3Path k N)
  · intro r
    exact hasDerivAt_ccmGuinandWeilPrimeEntryOddGermJet2 k
      (ccmPublishedCenteredMode N r) ha
  · intro r
    exact hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGermJet2 k
      (ccmPublishedCenteredMode N r) ha

theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path_at_entry
    (k N : ℕ) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path k N
        (ccmGuinandWeilPrimeEntryAperture k) =
      ccmGuinandWeilPrimeEntryCenteredMatrixJet2 k N := by
  rfl

theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3Path_at_entry
    (k N : ℕ) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet3Path k N
        (ccmGuinandWeilPrimeEntryAperture k) =
      ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N := by
  rfl

/-- **Actual whole-matrix higher-jet chain.**  At every nontrivial entry wall, the source matrix,
first-jet path, and second-jet path differentiate successively to the displayed first, second, and
third jets. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrix_entry_higherJetChain
    {k : ℕ} (hk : 1 < k) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    HasDerivAt
        (fun x => ccmGuinandWeilPrimeEntryCenteredMatrix k N x i j)
        (ccmGuinandWeilPrimeEntryCenteredMatrixJet1Path k N
          (ccmGuinandWeilPrimeEntryAperture k) i j)
        (ccmGuinandWeilPrimeEntryAperture k) ∧
      HasDerivAt
        (fun x => ccmGuinandWeilPrimeEntryCenteredMatrixJet1Path k N x i j)
        (ccmGuinandWeilPrimeEntryCenteredMatrixJet2 k N i j)
        (ccmGuinandWeilPrimeEntryAperture k) ∧
      HasDerivAt
        (fun x => ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path k N x i j)
        (ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N i j)
        (ccmGuinandWeilPrimeEntryAperture k) := by
  have ha0 : ccmGuinandWeilPrimeEntryAperture k ≠ 0 := by
    rw [ccmGuinandWeilPrimeEntryAperture]
    have hkreal : (1 : ℝ) < k := by exact_mod_cast hk
    have := Real.log_pos hkreal
    positivity
  refine ⟨hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrix_jet1_apply
    k N ha0 i j, ?_, ?_⟩
  · simpa [ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path_at_entry] using
      hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrixJet1Path_apply
        k N ha0 i j
  · simpa [ccmGuinandWeilPrimeEntryCenteredMatrixJet3Path_at_entry] using
      hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrixJet2Path_apply
        k N ha0 i j

end


end RHTower
