import GaloisForLFunctions.RHTower.PrimeSquareFourierStrata

/-!
# The prime-square Möbius--Fourier complementary record law

The literal local factor of the Möbius function at a prime `p` lives on the finite clock
`ZMod (p ^ 2)`:

```
m_p x = 1   if p ∤ x,      m_p x = -1  if p ‖ x,      m_p x = 0   if p ^ 2 ∣ x.
```

This file proves, unconditionally, the local half of the card
`prime-square-mobius-fourier-complementary-record-law`:

* the three valuation strata `1_U`, `1_V`, `δ₀` are orthogonal with squared lengths
  `p² − p`, `p − 1`, `1` (`countInner_strataVec`);
* their unitary additive Fourier images, equation (7)
  (`primeSquareFourier_unitVec`, `primeSquareFourier_valOneVec'`);
* the producer--reporter compression matrix, equation (8) (`compression_*`);
* its spectrum `{1, −1/p}` with the explicit eigenvectors, equations (9)--(11)
  (`primeSquareFourier_fourierFixedVec`, `countInner_recordVec_fourier_recordVec`,
  `countInner_recordLeak_self`);
* Möbius parity as the complementary record, equations (14)--(18)
  (`primeSquareOccupationVec_eq_recordVec`, `primeSquareSourceInvolution_occupationVec`,
  `primeSquareMobiusVec_eq`, `primeRecordSigma_sq_add_tau_sq`);
* the hyperbolic form `σ_p = sech(log p / 2)`, `τ_p = tanh(log p / 2)`, equations (19)--(21)
  (`primeRecordSigma_eq_sech`, `primeRecordTau_eq_tanh`);
* the exact local Fourier spectrum and Plancherel mass, equations (22)--(26) and (38)
  (`primeSquareMobiusDFT_strata`, `countInner_mobiusDFT_self`,
  `primeSquare_zeroFrequency_factorization`, `primeSquare_zeroFrequency_share`);
* the deformed clock and the projective natural cone, equations (27)--(29)
  (`countInner_deformedLine`).

Everything is a finite identity on `ZMod (p ^ 2)`; no analytic input and no hypothesis beyond
`1 < p` (satisfied by every prime) is used.
-/

open Complex Finset

namespace RHTower

noncomputable section

variable {p : ℕ}

/-! ## Pointwise orthogonality of the three valuation strata -/

theorem unitIndicator_mul_valOneVec (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    unitIndicator p x * valOneVec p x = 0 := by
  simp only [valOneVec, mul_sub, unitIndicator_mul_multipleIndicator,
    unitIndicator_mul_deltaZero, sub_zero]

theorem valOneVec_mul_deltaZero (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    valOneVec p x * deltaZero p x = 0 := by
  simp only [valOneVec, sub_mul, sum_multipleIndicator_mul_deltaZero, deltaZero_sq, sub_self]

theorem sum_unitIndicator_mul_valOneVec (p : ℕ) [NeZero p] :
    ∑ x : ZMod (p ^ 2), unitIndicator p x * valOneVec p x = 0 := by
  simp [unitIndicator_mul_valOneVec]

theorem sum_valOneVec_mul_deltaZero (p : ℕ) [NeZero p] :
    ∑ x : ZMod (p ^ 2), valOneVec p x * deltaZero p x = 0 := by
  simp [valOneVec_mul_deltaZero]

/-- A general vector of the three-dimensional valuation-strata space. -/
def strataVec (p : ℕ) [NeZero p] (a b c : ℂ) : ZMod (p ^ 2) → ℂ :=
  fun x => a * unitIndicator p x + b * valOneVec p x + c * deltaZero p x

/-- **The exact Gram form of the valuation strata.**  The three strata are orthogonal with
squared lengths `p² - p`, `p - 1` and `1`. -/
theorem countInner_strataVec {p : ℕ} [NeZero p] (hp : 1 < p) (a b c a' b' c' : ℂ) :
    countInner p (strataVec p a b c) (strataVec p a' b' c')
      = (starRingEnd ℂ) a * a' * ((p : ℂ) ^ 2 - (p : ℂ))
        + (starRingEnd ℂ) b * b' * ((p : ℂ) - 1)
        + (starRingEnd ℂ) c * c' := by
  rw [countInner]
  have hterm : ∀ x : ZMod (p ^ 2),
      (starRingEnd ℂ) (strataVec p a b c x) * strataVec p a' b' c' x
        = (starRingEnd ℂ) a * a' * (unitIndicator p x * unitIndicator p x)
          + (starRingEnd ℂ) b * b' * (valOneVec p x * valOneVec p x)
          + (starRingEnd ℂ) c * c' * (deltaZero p x * deltaZero p x)
          + ((starRingEnd ℂ) a * b' + (starRingEnd ℂ) b * a')
              * (unitIndicator p x * valOneVec p x)
          + ((starRingEnd ℂ) a * c' + (starRingEnd ℂ) c * a')
              * (unitIndicator p x * deltaZero p x)
          + ((starRingEnd ℂ) b * c' + (starRingEnd ℂ) c * b')
              * (valOneVec p x * deltaZero p x) := by
    intro x
    simp only [strataVec, map_add, map_mul, conj_unitIndicator, conj_valOneVec, conj_deltaZero]
    ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_unitIndicator_sq hp, sum_valOneVec_sq hp, sum_deltaZero_sq,
    sum_unitIndicator_mul_valOneVec, sum_unitIndicator_mul_deltaZero,
    sum_valOneVec_mul_deltaZero]
  ring

/-! ## The Fourier images of the strata -/

/-- **Fourier image of the unit stratum in the strata basis.** -/
theorem primeSquareFourier_unitIndicator_strata {p : ℕ} [NeZero p] (hp : 1 < p) :
    primeSquareFourier p (unitIndicator p) = strataVec p 0 (-1) ((p : ℂ) - 1) := by
  funext k
  rw [primeSquareFourier_unitIndicator hp, strataVec]
  have hmv : multipleIndicator p k = valOneVec p k + deltaZero p k := by
    simp [valOneVec]
  rw [hmv]
  ring

/-- The strata resolution of the constant one. -/
theorem strata_resolution_one (p : ℕ) [NeZero p] (k : ZMod (p ^ 2)) :
    unitIndicator p k + valOneVec p k + deltaZero p k = 1 := by
  have := unitIndicator_add_multipleIndicator p k
  simp only [valOneVec]
  linear_combination this

theorem multipleIndicator_eq_strata (p : ℕ) [NeZero p] (k : ZMod (p ^ 2)) :
    multipleIndicator p k = valOneVec p k + deltaZero p k := by
  simp [valOneVec]

/-- **Fourier image of the valuation-one stratum in the strata basis.** -/
theorem primeSquareFourier_valOneVec_strata {p : ℕ} [NeZero p] (hp : 1 < p) :
    primeSquareFourier p (valOneVec p)
      = strataVec p (-(p : ℂ)⁻¹) (1 - (p : ℂ)⁻¹) (1 - (p : ℂ)⁻¹) := by
  funext k
  rw [primeSquareFourier_valOneVec hp, strataVec]
  linear_combination multipleIndicator_eq_strata p k + ((p : ℂ))⁻¹ * strata_resolution_one p k

/-- **Fourier image of the origin delta.** -/
theorem primeSquareFourier_deltaZero_strata (p : ℕ) [NeZero p] :
    primeSquareFourier p (deltaZero p)
      = strataVec p ((p : ℂ)⁻¹) ((p : ℂ)⁻¹) ((p : ℂ)⁻¹) := by
  funext k
  rw [primeSquareFourier, dft_deltaZero, strataVec]
  linear_combination (-((p : ℂ))⁻¹) * strata_resolution_one p k

/-- Linearity of the unitary prime-square Fourier transform on three summands. -/
theorem primeSquareFourier_linear3 (p : ℕ) [NeZero p] (a b c : ℂ)
    (f g h : ZMod (p ^ 2) → ℂ) :
    primeSquareFourier p (fun x => a * f x + b * g x + c * h x)
      = fun k => a * primeSquareFourier p f k + b * primeSquareFourier p g k
          + c * primeSquareFourier p h k := by
  funext k
  simp only [primeSquareFourier]
  have hsum : (fun x => a * f x + b * g x + c * h x) = a • f + b • g + c • h := by
    funext x; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum, map_add, map_add, map_smul, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The Fourier transform in strata coordinates.** -/
theorem primeSquareFourier_strataVec {p : ℕ} [NeZero p] (hp : 1 < p) (a b c : ℂ) :
    primeSquareFourier p (strataVec p a b c)
      = strataVec p (-b * (p : ℂ)⁻¹ + c * (p : ℂ)⁻¹)
          (-a + b * (1 - (p : ℂ)⁻¹) + c * (p : ℂ)⁻¹)
          (a * ((p : ℂ) - 1) + b * (1 - (p : ℂ)⁻¹) + c * (p : ℂ)⁻¹) := by
  have hform : strataVec p a b c
      = fun x => a * unitIndicator p x + b * valOneVec p x + c * deltaZero p x := rfl
  rw [hform, primeSquareFourier_linear3]
  funext k
  rw [primeSquareFourier_unitIndicator_strata hp, primeSquareFourier_valOneVec_strata hp,
    primeSquareFourier_deltaZero_strata p]
  simp only [strataVec]
  ring


/-! ## Real square-root toolkit for the prime-square strata -/

theorem conj_ofReal_inv (x : ℝ) : (starRingEnd ℂ) ((x : ℂ))⁻¹ = ((x : ℂ))⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

theorem ofReal_sqrt_ne_zero {x : ℝ} (hx : 0 < x) : ((Real.sqrt x : ℝ) : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.sqrt_pos.mpr hx)

theorem sqrt_prime_sq_sub_self {p : ℕ} (hp : 1 < p) :
    Real.sqrt ((p : ℝ) ^ 2 - (p : ℝ)) = Real.sqrt (p : ℝ) * Real.sqrt ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [show (p : ℝ) ^ 2 - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) by ring,
    Real.sqrt_mul (by linarith)]

theorem sqrt_prime_sq_sub_one {p : ℕ} (hp : 1 < p) :
    Real.sqrt ((p : ℝ) ^ 2 - 1) = Real.sqrt ((p : ℝ) - 1) * Real.sqrt ((p : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [show (p : ℝ) ^ 2 - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) by ring,
    Real.sqrt_mul (by linarith)]

theorem sqrt_prime_mul_sq_sub_one {p : ℕ} (hp : 1 < p) :
    Real.sqrt ((p : ℝ) * ((p : ℝ) ^ 2 - 1))
      = Real.sqrt (p : ℝ) * Real.sqrt ((p : ℝ) - 1) * Real.sqrt ((p : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [Real.sqrt_mul (by linarith), sqrt_prime_sq_sub_one hp, ← mul_assoc]

/-- The complete arithmetic of the three square roots `√p`, `√(p−1)`, `√(p+1)`. -/
theorem prime_sqrt_facts {p : ℕ} (hp : 1 < p) :
    ((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ) = (p : ℂ)
      ∧ ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ) = (p : ℂ) - 1
      ∧ ((Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ) = (p : ℂ) + 1
      ∧ ((Real.sqrt (p : ℝ) : ℝ) : ℂ) ≠ 0
      ∧ ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ) ≠ 0
      ∧ ((Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ) ≠ 0
      ∧ ((p : ℂ)) ≠ 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  have hV : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hW : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  refine ⟨?_, ?_, ?_, ofReal_sqrt_ne_zero hpp, ofReal_sqrt_ne_zero hV,
    ofReal_sqrt_ne_zero hW, ?_⟩
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpp.le]; push_cast; ring
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt hV.le]; push_cast; ring
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt hW.le]; push_cast; ring
  · exact Nat.cast_ne_zero.mpr (by omega)

/-! ## The orthonormal valuation basis -/

/-- Normalized unit-residue stratum `u_p = 1_U/√(p²−p)`. -/
def primeSquareUnitVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  strataVec p (((Real.sqrt ((p : ℝ) ^ 2 - (p : ℝ)) : ℝ) : ℂ)⁻¹) 0 0

/-- Normalized valuation-one stratum `v_p = 1_V/√(p−1)`. -/
def primeSquareValOneVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  strataVec p 0 (((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ)⁻¹) 0

/-- The origin stratum `w_p = δ₀`. -/
def primeSquareOriginVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ := strataVec p 0 0 1

section Basis

variable {p : ℕ} [NeZero p]

/-- `u_p` in the atomic square-root coordinates. -/
theorem primeSquareUnitVec_eq (hp : 1 < p) :
    primeSquareUnitVec p
      = strataVec p ((((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ))⁻¹)
          0 0 := by
  rw [primeSquareUnitVec, sqrt_prime_sq_sub_self hp, Complex.ofReal_mul]

theorem countInner_unitVec_self (hp : 1 < p) :
    countInner p (primeSquareUnitVec p) (primeSquareUnitVec p) = 1 := by
  obtain ⟨ha2, hb2, _, ha0, hb0, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareUnitVec_eq hp, countInner_strataVec hp]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal, map_zero, zero_mul, mul_zero, add_zero]
  rw [show ((p : ℂ)) ^ 2 - (p : ℂ)
      = (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ))
        * (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ)) by
    linear_combination (-((p : ℂ) - 1)) * ha2
      - (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ)) * hb2]
  field_simp

theorem countInner_valOneVec_self (hp : 1 < p) :
    countInner p (primeSquareValOneVec p) (primeSquareValOneVec p) = 1 := by
  obtain ⟨_, hb2, _, _, hb0, _, _⟩ := prime_sqrt_facts hp
  rw [primeSquareValOneVec, countInner_strataVec hp, conj_ofReal_inv]
  simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero]
  rw [← hb2]
  field_simp

theorem countInner_originVec_self (hp : 1 < p) :
    countInner p (primeSquareOriginVec p) (primeSquareOriginVec p) = 1 := by
  rw [primeSquareOriginVec, countInner_strataVec hp]
  simp

theorem countInner_unitVec_valOneVec (hp : 1 < p) :
    countInner p (primeSquareUnitVec p) (primeSquareValOneVec p) = 0 := by
  rw [primeSquareUnitVec, primeSquareValOneVec, countInner_strataVec hp]
  simp

theorem countInner_unitVec_originVec (hp : 1 < p) :
    countInner p (primeSquareUnitVec p) (primeSquareOriginVec p) = 0 := by
  rw [primeSquareUnitVec, primeSquareOriginVec, countInner_strataVec hp]
  simp

theorem countInner_valOneVec_originVec (hp : 1 < p) :
    countInner p (primeSquareValOneVec p) (primeSquareOriginVec p) = 0 := by
  rw [primeSquareValOneVec, primeSquareOriginVec, countInner_strataVec hp]
  simp

end Basis


/-! ## Equation (7): the Fourier images of the two strata -/

section FourierImages

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem prime_sq_sub_self_eq (hp : 1 < p) :
    ((p : ℂ)) ^ 2 - (p : ℂ)
      = (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ))
        * (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ)) := by
  obtain ⟨ha2, hb2, _, _, _, _, _⟩ := prime_sqrt_facts hp
  linear_combination (-((p : ℂ) - 1)) * ha2
    - (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ)) * hb2

/-- Fourier image of the normalized unit stratum, in strata coordinates. -/
theorem primeSquareFourier_unitVec_strata (hp : 1 < p) :
    primeSquareFourier p (primeSquareUnitVec p)
      = strataVec p 0
          (-((((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ))⁻¹))
          ((((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ))⁻¹
            * ((p : ℂ) - 1)) := by
  rw [primeSquareUnitVec_eq hp, primeSquareFourier_strataVec hp]
  funext k
  simp only [strataVec]
  ring

/-- Fourier image of the normalized valuation-one stratum, in strata coordinates. -/
theorem primeSquareFourier_valOneVec_strata' (hp : 1 < p) :
    primeSquareFourier p (primeSquareValOneVec p)
      = strataVec p (-(((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ)⁻¹ * (p : ℂ)⁻¹))
          (((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ)⁻¹ * (1 - (p : ℂ)⁻¹))
          (((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ)⁻¹ * (1 - (p : ℂ)⁻¹)) := by
  rw [primeSquareValOneVec, primeSquareFourier_strataVec hp]
  funext k
  simp only [strataVec]
  ring

/-- **Equation (7), first line.**  `ℱ u_p = √((p−1)/p)·w_p − p^(−1/2)·v_p`. -/
theorem primeSquareFourier_unitVec (hp : 1 < p) :
    primeSquareFourier p (primeSquareUnitVec p)
      = fun k => (((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ)⁻¹)
            * primeSquareOriginVec p k
          - ((Real.sqrt (p : ℝ) : ℝ) : ℂ)⁻¹ * primeSquareValOneVec p k := by
  obtain ⟨ha2, hb2, _, ha0, hb0, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourier_unitVec_strata hp]
  funext k
  simp only [strataVec, primeSquareOriginVec, primeSquareValOneVec]
  field_simp
  linear_combination (-(deltaZero p k)) * hb2

/-- **Equation (7), second line.**
`ℱ v_p = −p^(−1/2)·u_p + ((p−1)/p)·v_p + (√(p−1)/p)·w_p`. -/
theorem primeSquareFourier_valOneVec' (hp : 1 < p) :
    primeSquareFourier p (primeSquareValOneVec p)
      = fun k => -(((Real.sqrt (p : ℝ) : ℝ) : ℂ)⁻¹) * primeSquareUnitVec p k
          + (((p : ℂ) - 1) / (p : ℂ)) * primeSquareValOneVec p k
          + (((Real.sqrt ((p : ℝ) - 1) : ℝ) : ℂ) / (p : ℂ)) * primeSquareOriginVec p k := by
  obtain ⟨ha2, hb2, _, ha0, hb0, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourier_valOneVec_strata' hp]
  funext k
  simp only [strataVec, primeSquareOriginVec, primeSquareValOneVec, primeSquareUnitVec_eq hp]
  field_simp
  linear_combination (-(unitIndicator p k)) * ha2
    - (deltaZero p k * (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * ((Real.sqrt (p : ℝ) : ℝ) : ℂ))) * hb2

/-! ## Equation (8): the producer--reporter compression -/

/-- Compression entry `⟨u_p, ℱ u_p⟩ = 0`: the Fourier compression is transverse on the unit
stratum. -/
theorem compression_unit_unit (hp : 1 < p) :
    countInner p (primeSquareUnitVec p) (primeSquareFourier p (primeSquareUnitVec p)) = 0 := by
  rw [primeSquareFourier_unitVec_strata hp, primeSquareUnitVec_eq hp, countInner_strataVec hp]
  simp

/-- Compression entry `⟨v_p, ℱ u_p⟩ = −p^(−1/2)`. -/
theorem compression_valOne_unit (hp : 1 < p) :
    countInner p (primeSquareValOneVec p) (primeSquareFourier p (primeSquareUnitVec p))
      = -((Real.sqrt (p : ℝ) : ℝ) : ℂ)⁻¹ := by
  obtain ⟨ha2, hb2, _, ha0, hb0, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourier_unitVec_strata hp, primeSquareValOneVec, countInner_strataVec hp,
    conj_ofReal_inv]
  simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero]
  field_simp
  linear_combination hb2

/-- Compression entry `⟨u_p, ℱ v_p⟩ = −p^(−1/2)`. -/
theorem compression_unit_valOne (hp : 1 < p) :
    countInner p (primeSquareUnitVec p) (primeSquareFourier p (primeSquareValOneVec p))
      = -((Real.sqrt (p : ℝ) : ℝ) : ℂ)⁻¹ := by
  obtain ⟨ha2, hb2, _, ha0, hb0, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourier_valOneVec_strata' hp, primeSquareUnitVec_eq hp,
    countInner_strataVec hp]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal, map_zero, zero_mul, add_zero]
  rw [prime_sq_sub_self_eq hp]
  field_simp
  linear_combination -ha2

/-- Compression entry `⟨v_p, ℱ v_p⟩ = 1 − 1/p`. -/
theorem compression_valOne_valOne (hp : 1 < p) :
    countInner p (primeSquareValOneVec p) (primeSquareFourier p (primeSquareValOneVec p))
      = 1 - (p : ℂ)⁻¹ := by
  obtain ⟨ha2, hb2, _, ha0, hb0, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourier_valOneVec_strata' hp, primeSquareValOneVec, countInner_strataVec hp,
    conj_ofReal_inv]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  field_simp
  linear_combination (1 - (p : ℂ)) * hb2

end FourierImages


/-! ## Equations (9)--(11): the Fourier principal basis -/

section Principal

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem prime_norm_facts (hp : 1 < p) :
    ((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)
        = (p : ℂ) ^ 2 - 1
      ∧ ((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ) ≠ 0
      ∧ ((Real.sqrt ((p : ℝ) * ((p : ℝ) ^ 2 - 1)) : ℝ) : ℂ)
          * ((Real.sqrt ((p : ℝ) * ((p : ℝ) ^ 2 - 1)) : ℝ) : ℂ) = (p : ℂ) * ((p : ℂ) ^ 2 - 1)
      ∧ ((Real.sqrt ((p : ℝ) * ((p : ℝ) ^ 2 - 1)) : ℝ) : ℂ) ≠ 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hR : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hD : (0 : ℝ) < (p : ℝ) * ((p : ℝ) ^ 2 - 1) := by positivity
  refine ⟨?_, ofReal_sqrt_ne_zero hR, ?_, ofReal_sqrt_ne_zero hD⟩
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt hR.le]; push_cast; ring
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt hD.le]; push_cast; ring

/-- The Fourier-fixed continuation vector `c_p = (u_p − √p·v_p)/√(p+1)`. -/
def primeSquareFourierFixedVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  strataVec p (((Real.sqrt ((p : ℝ) * ((p : ℝ) ^ 2 - 1)) : ℝ) : ℂ)⁻¹)
    (-(p : ℂ) * ((Real.sqrt ((p : ℝ) * ((p : ℝ) ^ 2 - 1)) : ℝ) : ℂ)⁻¹) 0

/-- The Möbius record vector `t_p = (√p·u_p + v_p)/√(p+1)`. -/
def primeSquareRecordVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  strataVec p (((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹)
    (((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹) 0

/-- **Equation (10), continuation eigenvector.** -/
theorem primeSquareFourierFixedVec_eq (hp : 1 < p) :
    primeSquareFourierFixedVec p
      = fun x => ((Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ)⁻¹
          * (primeSquareUnitVec p x - ((Real.sqrt (p : ℝ) : ℝ) : ℂ) * primeSquareValOneVec p x) := by
  obtain ⟨ha2, hb2, hc2, ha0, hb0, hc0, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourierFixedVec, sqrt_prime_mul_sq_sub_one hp]
  funext x
  simp only [primeSquareUnitVec_eq hp, primeSquareValOneVec, strataVec]
  push_cast
  field_simp
  linear_combination (valOneVec p x) * ha2

/-- **Equation (10), record eigenvector.** -/
theorem primeSquareRecordVec_eq (hp : 1 < p) :
    primeSquareRecordVec p
      = fun x => ((Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ)⁻¹
          * (((Real.sqrt (p : ℝ) : ℝ) : ℂ) * primeSquareUnitVec p x + primeSquareValOneVec p x) := by
  obtain ⟨ha2, hb2, hc2, ha0, hb0, hc0, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareRecordVec, sqrt_prime_sq_sub_one hp]
  funext x
  simp only [primeSquareUnitVec_eq hp, primeSquareValOneVec, strataVec]
  push_cast
  field_simp
  ring

theorem countInner_fourierFixedVec_self (hp : 1 < p) :
    countInner p (primeSquareFourierFixedVec p) (primeSquareFourierFixedVec p) = 1 := by
  obtain ⟨_, _, hD2, hD0⟩ := prime_norm_facts hp
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourierFixedVec, countInner_strataVec hp]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_neg, Complex.conj_natCast,
    map_zero, zero_mul, add_zero, neg_mul, mul_neg, neg_neg]
  field_simp
  linear_combination -hD2

theorem countInner_recordVec_self (hp : 1 < p) :
    countInner p (primeSquareRecordVec p) (primeSquareRecordVec p) = 1 := by
  obtain ⟨hS2, hS0, _, _⟩ := prime_norm_facts hp
  rw [primeSquareRecordVec, countInner_strataVec hp, conj_ofReal_inv]
  simp only [map_zero, zero_mul, add_zero]
  field_simp
  linear_combination -hS2

theorem countInner_fourierFixedVec_recordVec (hp : 1 < p) :
    countInner p (primeSquareFourierFixedVec p) (primeSquareRecordVec p) = 0 := by
  obtain ⟨hS2, hS0, hD2, hD0⟩ := prime_norm_facts hp
  rw [primeSquareFourierFixedVec, primeSquareRecordVec, countInner_strataVec hp]
  simp only [map_inv₀, Complex.conj_ofReal, map_mul, map_neg, Complex.conj_natCast,
    map_zero, zero_mul, add_zero, neg_mul]
  field_simp
  ring

/-- **Equation (11), first line.**  `c_p` is an exact fixed vector of the additive Fourier
transform. -/
theorem primeSquareFourier_fourierFixedVec (hp : 1 < p) :
    primeSquareFourier p (primeSquareFourierFixedVec p) = primeSquareFourierFixedVec p := by
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourierFixedVec, primeSquareFourier_strataVec hp]
  funext k
  simp only [strataVec]
  field_simp
  ring

/-- The Fourier image of the record vector, in strata coordinates. -/
theorem primeSquareFourier_recordVec_strata (hp : 1 < p) :
    primeSquareFourier p (primeSquareRecordVec p)
      = strataVec p (-(((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ * (p : ℂ)⁻¹))
          (-(((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ * (p : ℂ)⁻¹))
          (((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ * ((p : ℂ) - (p : ℂ)⁻¹)) := by
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareRecordVec, primeSquareFourier_strataVec hp]
  funext k
  simp only [strataVec]
  field_simp
  ring

/-- **Equation (11), second line, transverse part.** -/
theorem countInner_fourierFixedVec_fourier_recordVec (hp : 1 < p) :
    countInner p (primeSquareFourierFixedVec p) (primeSquareFourier p (primeSquareRecordVec p))
      = 0 := by
  obtain ⟨hS2, hS0, hD2, hD0⟩ := prime_norm_facts hp
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourier_recordVec_strata hp, primeSquareFourierFixedVec,
    countInner_strataVec hp]
  simp only [map_inv₀, Complex.conj_ofReal, map_mul, map_neg, Complex.conj_natCast,
    map_zero, zero_mul, add_zero, neg_mul]
  field_simp
  ring

/-- **Equation (11), second line, diagonal part.**  The record vector is compressed to the
eigenvalue `−1/p`. -/
theorem countInner_recordVec_fourier_recordVec (hp : 1 < p) :
    countInner p (primeSquareRecordVec p) (primeSquareFourier p (primeSquareRecordVec p))
      = -(p : ℂ)⁻¹ := by
  obtain ⟨hS2, hS0, _, _⟩ := prime_norm_facts hp
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareFourier_recordVec_strata hp, primeSquareRecordVec, countInner_strataVec hp,
    conj_ofReal_inv]
  simp only [map_zero, zero_mul, add_zero]
  field_simp
  linear_combination hS2

/-- The transverse residual `(1 − P_E)ℱ t_p`. -/
def primeSquareRecordLeak (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  fun x => primeSquareFourier p (primeSquareRecordVec p) x
    + (p : ℂ)⁻¹ * primeSquareRecordVec p x

theorem primeSquareRecordLeak_strata (hp : 1 < p) :
    primeSquareRecordLeak p
      = strataVec p 0 0 (((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ * ((p : ℂ) - (p : ℂ)⁻¹)) := by
  funext x
  show primeSquareFourier p (primeSquareRecordVec p) x
      + (p : ℂ)⁻¹ * primeSquareRecordVec p x = _
  rw [primeSquareFourier_recordVec_strata hp]
  simp only [primeSquareRecordVec, strataVec]
  ring

/-- **Equation (11), third line.**  The Fourier image of the record vector leaks exactly
`1 − p^(−2)` of its unit mass out of the two-dimensional stratum plane. -/
theorem countInner_recordLeak_self (hp : 1 < p) :
    countInner p (primeSquareRecordLeak p) (primeSquareRecordLeak p)
      = 1 - (p : ℂ)⁻¹ * (p : ℂ)⁻¹ := by
  obtain ⟨hS2, hS0, _, _⟩ := prime_norm_facts hp
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareRecordLeak_strata hp, countInner_strataVec hp]
  simp only [map_zero, zero_mul, zero_add, map_mul, map_inv₀, Complex.conj_ofReal,
    map_sub, Complex.conj_natCast]
  field_simp
  linear_combination (1 - (p : ℂ) ^ 2) * hS2

end Principal


/-! ## Equations (14)--(21): Möbius parity as the complementary record -/

section Record

variable {p : ℕ} [NeZero p]

theorem unitIndicator_mul_self (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    unitIndicator p x * unitIndicator p x = unitIndicator p x := by
  rw [unitIndicator]
  by_cases h : (p : ℕ) ∣ x.val <;> simp [h]

theorem valOneVec_mul_self (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    valOneVec p x * valOneVec p x = valOneVec p x := by
  simp only [valOneVec]
  have h1 := multipleIndicator_sq p x
  have h2 := deltaZero_sq p x
  have h3 := sum_multipleIndicator_mul_deltaZero p x
  linear_combination h1 - 2 * h3 + h2

/-- The literal local Möbius factor `m_p` of equation (1). -/
def primeSquareLocalMobius (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ := strataVec p 1 (-1) 0

/-- The local squarefree occupation `|m_p|`. -/
def primeSquareLocalOccupation (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ := strataVec p 1 1 0

theorem primeSquareLocalMobius_of_not_dvd (x : ZMod (p ^ 2)) (hx : ¬ (p : ℕ) ∣ x.val) :
    primeSquareLocalMobius p x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  simp only [primeSquareLocalMobius, strataVec, unitIndicator, valOneVec, multipleIndicator,
    deltaZero, if_neg hx, if_neg hx0]
  ring

theorem primeSquareLocalMobius_of_dvd (x : ZMod (p ^ 2)) (hx : (p : ℕ) ∣ x.val) (hx0 : x ≠ 0) :
    primeSquareLocalMobius p x = -1 := by
  simp only [primeSquareLocalMobius, strataVec, unitIndicator, valOneVec, multipleIndicator,
    deltaZero, if_pos hx, if_neg hx0]
  ring

theorem primeSquareLocalMobius_zero : primeSquareLocalMobius p 0 = 0 := by
  simp only [primeSquareLocalMobius, strataVec, unitIndicator, valOneVec, multipleIndicator,
    deltaZero]
  simp

theorem countInner_localMobius_self (hp : 1 < p) :
    countInner p (primeSquareLocalMobius p) (primeSquareLocalMobius p) = (p : ℂ) ^ 2 - 1 := by
  rw [primeSquareLocalMobius, countInner_strataVec hp]
  simp only [map_one, map_neg, map_zero]
  ring

theorem countInner_localOccupation_self (hp : 1 < p) :
    countInner p (primeSquareLocalOccupation p) (primeSquareLocalOccupation p)
      = (p : ℂ) ^ 2 - 1 := by
  rw [primeSquareLocalOccupation, countInner_strataVec hp]
  simp only [map_one, map_zero]
  ring

/-- The normalized signed Möbius record `m̃_p`, equation (15). -/
def primeSquareMobiusVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  fun x => ((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ * primeSquareLocalMobius p x

/-- The normalized positive squarefree occupation `q_p`, equation (14). -/
def primeSquareOccupationVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  fun x => ((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ * primeSquareLocalOccupation p x

theorem primeSquareMobiusVec_strata :
    primeSquareMobiusVec p
      = strataVec p (((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹)
          (-(((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹)) 0 := by
  funext x
  simp only [primeSquareMobiusVec, primeSquareLocalMobius, strataVec]
  ring

/-- **Equation (14).**  The normalized squarefree occupation vector *is* the Fourier record
eigenvector `t_p`. -/
theorem primeSquareOccupationVec_eq_recordVec :
    primeSquareOccupationVec p = primeSquareRecordVec p := by
  funext x
  simp only [primeSquareOccupationVec, primeSquareLocalOccupation, primeSquareRecordVec,
    strataVec]
  ring

/-- The source involution: pointwise multiplication by the local Möbius sign. -/
def primeSquareSourceInvolution (p : ℕ) [NeZero p] (f : ZMod (p ^ 2) → ℂ) :
    ZMod (p ^ 2) → ℂ := fun x => primeSquareLocalMobius p x * f x

theorem primeSquareSourceInvolution_strataVec (a b c : ℂ) :
    primeSquareSourceInvolution p (strataVec p a b c) = strataVec p a (-b) 0 := by
  funext x
  show primeSquareLocalMobius p x * strataVec p a b c x = _
  simp only [primeSquareLocalMobius, strataVec]
  have h1 := unitIndicator_mul_self p x
  have h2 := valOneVec_mul_self p x
  have h3 := unitIndicator_mul_valOneVec p x
  have h4 := unitIndicator_mul_deltaZero p x
  have h5 := valOneVec_mul_deltaZero p x
  linear_combination a * h1 - b * h2 + (b - a) * h3 + c * h4 - c * h5

/-- **Equation (16).**  The source involution sends the occupation record to the signed
Möbius record. -/
theorem primeSquareSourceInvolution_occupationVec :
    primeSquareSourceInvolution p (primeSquareOccupationVec p) = primeSquareMobiusVec p := by
  rw [primeSquareMobiusVec_strata]
  have hocc : primeSquareOccupationVec p
      = strataVec p (((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹)
          (((Real.sqrt ((p : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹) 0 := by
    funext x
    simp only [primeSquareOccupationVec, primeSquareLocalOccupation, strataVec]
    ring
  rw [hocc, primeSquareSourceInvolution_strataVec]

/-- The critical fixed-source `p`-adic spherical moment `σ_p = 2√p/(p+1)`, equation (19). -/
def primeRecordSigma (p : ℕ) : ℝ := 2 * Real.sqrt (p : ℝ) / ((p : ℝ) + 1)

/-- The projective Möbius/Plücker overlap `τ_p = (p−1)/(p+1)`, equation (20). -/
def primeRecordTau (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) + 1)

theorem sqrt_prime_mul_record {p : ℕ} (hp : 1 < p) :
    Real.sqrt ((p : ℝ) * ((p : ℝ) ^ 2 - 1))
      = Real.sqrt (p : ℝ) * Real.sqrt ((p : ℝ) ^ 2 - 1) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  exact Real.sqrt_mul (by linarith) _

/-- **Equation (18), Pythagorean law.**  The two source amplitudes are complementary. -/
theorem primeRecordSigma_sq_add_tau_sq {p : ℕ} (hp : 1 < p) :
    primeRecordSigma p ^ 2 + primeRecordTau p ^ 2 = 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  have ha : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hpp.le
  have hne : ((p : ℝ) + 1) ≠ 0 := by linarith
  rw [primeRecordSigma, primeRecordTau]
  field_simp
  linear_combination 4 * ha

/-- **Equation (18).**  The signed Möbius record splits into the Fourier continuation mode and
the transverse record mode with the complementary amplitudes `σ_p`, `τ_p`. -/
theorem primeSquareMobiusVec_eq (hp : 1 < p) :
    primeSquareMobiusVec p
      = fun x => ((primeRecordSigma p : ℝ) : ℂ) * primeSquareFourierFixedVec p x
          + ((primeRecordTau p : ℝ) : ℂ) * primeSquareRecordVec p x := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨hS2, hS0, _, _⟩ := prime_norm_facts hp
  have ha0 : ((Real.sqrt (p : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_sqrt_ne_zero hpp
  have hpc : ((p : ℂ)) + 1 ≠ 0 := by
    have h1 : ((p : ℂ)) + 1 = ((p + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h1, ne_eq, Nat.cast_eq_zero]
    omega
  rw [primeSquareMobiusVec_strata, primeSquareFourierFixedVec, primeSquareRecordVec,
    sqrt_prime_mul_record hp, primeRecordSigma, primeRecordTau]
  funext x
  simp only [strataVec]
  push_cast
  field_simp
  ring

/-- **Equation (17), record column.** -/
theorem primeSquareSourceInvolution_recordVec (hp : 1 < p) :
    primeSquareSourceInvolution p (primeSquareRecordVec p)
      = fun x => ((primeRecordSigma p : ℝ) : ℂ) * primeSquareFourierFixedVec p x
          + ((primeRecordTau p : ℝ) : ℂ) * primeSquareRecordVec p x := by
  rw [← primeSquareMobiusVec_eq hp, ← primeSquareOccupationVec_eq_recordVec,
    primeSquareSourceInvolution_occupationVec]

/-- **Equation (17), continuation column.** -/
theorem primeSquareSourceInvolution_fourierFixedVec (hp : 1 < p) :
    primeSquareSourceInvolution p (primeSquareFourierFixedVec p)
      = fun x => -((primeRecordTau p : ℝ) : ℂ) * primeSquareFourierFixedVec p x
          + ((primeRecordSigma p : ℝ) : ℂ) * primeSquareRecordVec p x := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨hS2, hS0, _, _⟩ := prime_norm_facts hp
  obtain ⟨ha2, _, _, ha0, _, _, _⟩ := prime_sqrt_facts hp
  have hpc : ((p : ℂ)) + 1 ≠ 0 := by
    have h1 : ((p : ℂ)) + 1 = ((p + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h1, ne_eq, Nat.cast_eq_zero]
    omega
  rw [primeSquareFourierFixedVec, sqrt_prime_mul_record hp,
    primeSquareSourceInvolution_strataVec, primeSquareRecordVec,
    primeRecordSigma, primeRecordTau]
  funext x
  simp only [strataVec]
  push_cast
  field_simp
  linear_combination (-2 * unitIndicator p x - 2 * valOneVec p x) * ha2

/-! ### The hyperbolic form of the two amplitudes -/

theorem exp_half_log_eq_sqrt {p : ℕ} (hp : 1 < p) :
    Real.exp (Real.log (p : ℝ) / 2) = Real.sqrt (p : ℝ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpp]
  ring_nf

/-- **Equation (21), first amplitude.**  `σ_p = sech(log p / 2)`. -/
theorem primeRecordSigma_eq_sech {p : ℕ} (hp : 1 < p) :
    primeRecordSigma p = 1 / Real.cosh (Real.log (p : ℝ) / 2) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  have ha : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt hpp.le
  have ha0 : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpp)
  have hcosh : Real.cosh (Real.log (p : ℝ) / 2)
      = ((p : ℝ) + 1) / (2 * Real.sqrt (p : ℝ)) := by
    rw [Real.cosh_eq, Real.exp_neg, exp_half_log_eq_sqrt hp]
    field_simp
    linear_combination ha
  rw [primeRecordSigma, hcosh]
  have hne : ((p : ℝ) + 1) ≠ 0 := by linarith
  field_simp

/-- **Equation (21), second amplitude.**  `τ_p = tanh(log p / 2)`. -/
theorem primeRecordTau_eq_tanh {p : ℕ} (hp : 1 < p) :
    primeRecordTau p = Real.tanh (Real.log (p : ℝ) / 2) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  have ha : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt hpp.le
  have ha0 : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpp)
  have hne : ((p : ℝ) + 1) ≠ 0 := by linarith
  rw [primeRecordTau, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq,
    Real.exp_neg, exp_half_log_eq_sqrt hp]
  rw [div_eq_div_iff hne (by
    have : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpp
    have hsum : 0 < Real.sqrt (p : ℝ) + (Real.sqrt (p : ℝ))⁻¹ := by positivity
    intro hcon
    nlinarith [hsum])]
  field_simp
  linear_combination (-2 : ℝ) * ha

end Record


/-! ## Equations (22)--(26) and (38): the exact local Fourier spectrum -/

section Spectrum

variable {p : ℕ} [NeZero p]

/-- **Equation (24).** -/
theorem primeSquareLocalMobius_eq_sub :
    primeSquareLocalMobius p = fun x => 1 - 2 * multipleIndicator p x + deltaZero p x := by
  funext x
  simp only [primeSquareLocalMobius, strataVec]
  linear_combination strata_resolution_one p x + 2 * multipleIndicator_eq_strata p x

/-- The probability-normalized local Fourier transform, equation (22). -/
def primeSquareMobiusDFT (p : ℕ) [NeZero p] (a : ZMod (p ^ 2)) : ℂ :=
  ((p : ℂ) ^ 2)⁻¹ * ZMod.dft (primeSquareLocalMobius p) a

theorem primeSquareMobiusDFT_eq (a : ZMod (p ^ 2)) :
    primeSquareMobiusDFT p a
      = ((p : ℂ))⁻¹ * primeSquareFourier p (primeSquareLocalMobius p) a := by
  rw [primeSquareMobiusDFT, primeSquareFourier]
  ring

/-- **Equation (23).**  The complete local Fourier spectrum, in strata coordinates. -/
theorem primeSquareMobiusDFT_strata (hp : 1 < p) :
    primeSquareMobiusDFT p
      = strataVec p (((p : ℂ) ^ 2)⁻¹) (-(2 * (p : ℂ) - 1) * ((p : ℂ) ^ 2)⁻¹)
          (((p : ℂ) - 1) ^ 2 * ((p : ℂ) ^ 2)⁻¹) := by
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  funext a
  rw [primeSquareMobiusDFT_eq, primeSquareLocalMobius, primeSquareFourier_strataVec hp]
  simp only [strataVec]
  field_simp
  ring

theorem primeSquareMobiusDFT_zero (hp : 1 < p) :
    primeSquareMobiusDFT p 0 = ((p : ℂ) - 1) ^ 2 * ((p : ℂ) ^ 2)⁻¹ := by
  have h2 : valOneVec p 0 = 0 := by
    simp [valOneVec, multipleIndicator_zero, deltaZero]
  have h3 : deltaZero p 0 = 1 := by simp [deltaZero]
  rw [primeSquareMobiusDFT_strata hp]
  simp only [strataVec]
  rw [unitIndicator_zero, h2, h3]
  ring

theorem primeSquareMobiusDFT_of_dvd (hp : 1 < p) (a : ZMod (p ^ 2)) (ha : (p : ℕ) ∣ a.val)
    (ha0 : a ≠ 0) : primeSquareMobiusDFT p a = -(2 * (p : ℂ) - 1) * ((p : ℂ) ^ 2)⁻¹ := by
  rw [primeSquareMobiusDFT_strata hp]
  simp only [strataVec, unitIndicator, valOneVec, multipleIndicator, deltaZero,
    if_pos ha, if_neg ha0]
  ring

theorem primeSquareMobiusDFT_of_not_dvd (hp : 1 < p) (a : ZMod (p ^ 2))
    (ha : ¬ (p : ℕ) ∣ a.val) : primeSquareMobiusDFT p a = ((p : ℂ) ^ 2)⁻¹ := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (by simp)
  rw [primeSquareMobiusDFT_strata hp]
  simp only [strataVec, unitIndicator, valOneVec, multipleIndicator, deltaZero,
    if_neg ha, if_neg ha0]
  ring

/-- **Equation (25), Plancherel.**  The total local Fourier mass is exactly `1 − p^(−2)`. -/
theorem countInner_mobiusDFT_self (hp : 1 < p) :
    countInner p (primeSquareMobiusDFT p) (primeSquareMobiusDFT p) = 1 - ((p : ℂ) ^ 2)⁻¹ := by
  obtain ⟨_, _, _, _, _, _, hp0⟩ := prime_sqrt_facts hp
  rw [primeSquareMobiusDFT_strata hp, countInner_strataVec hp]
  simp only [map_inv₀, map_pow, Complex.conj_natCast, map_mul, map_neg, map_sub, map_one,
    map_ofNat]
  field_simp
  ring

/-- **Equation (26).**  The normalized zero-frequency survival probability factors exactly into
the safe squarefree Fourier mass and the squared projective Möbius record. -/
theorem primeSquare_zeroFrequency_factorization {p : ℕ} (hp : 1 < p) :
    ((((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 2) ^ 2) / (1 - ((p : ℝ) ^ 2)⁻¹)
      = (1 - ((p : ℝ) ^ 2)⁻¹) * primeRecordTau p ^ 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := by linarith
  have h1 : ((p : ℝ) + 1) ≠ 0 := by linarith
  have h4 : ((p : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by field_simp
  rw [primeRecordTau, h3]
  field_simp
  ring

/-- **Equation (38).**  The proportion of local Plancherel mass carried by the zero frequency. -/
theorem primeSquare_zeroFrequency_share {p : ℕ} (hp : 1 < p) :
    ((p : ℝ) - 1) ^ 3 / ((p : ℝ) ^ 2 * ((p : ℝ) + 1))
      = (1 - ((p : ℝ) ^ 2)⁻¹) * primeRecordTau p ^ 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := by linarith
  have h1 : ((p : ℝ) + 1) ≠ 0 := by linarith
  rw [primeRecordTau]
  field_simp
  ring

end Spectrum

/-! ## Equations (27)--(29): the deformed clock and the projective natural cone -/

section Deformed

variable {p : ℕ} [NeZero p]

/-- The deformed local Möbius clock `m_{p,c}` of equation (27). -/
def primeSquareDeformedMobius (p : ℕ) [NeZero p] (c : ℝ) : ZMod (p ^ 2) → ℂ :=
  strataVec p 1 (-(((p : ℝ) ^ c : ℝ) : ℂ)) 0

theorem countInner_deformedMobius (hp : 1 < p) (c d : ℝ) :
    countInner p (primeSquareDeformedMobius p c) (primeSquareDeformedMobius p d)
      = ((p : ℂ) - 1) * ((p : ℂ) + (((p : ℝ) ^ (c + d) : ℝ) : ℂ)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  rw [primeSquareDeformedMobius, primeSquareDeformedMobius, countInner_strataVec hp,
    Real.rpow_add hpp]
  simp only [map_one, map_neg, Complex.conj_ofReal, map_zero, one_mul, zero_mul, add_zero,
    neg_mul, Complex.ofReal_mul]
  ring

/-- The normalized deformed Möbius line of equation (28). -/
def primeSquareDeformedLine (p : ℕ) [NeZero p] (c : ℝ) : ZMod (p ^ 2) → ℂ :=
  fun x => ((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) : ℝ) : ℂ)⁻¹
    * primeSquareDeformedMobius p c x

/-- **Equation (29).**  The Gram matrix of the normalized deformed Möbius lines is exactly the
projective-prime Hellinger cone coefficient. -/
theorem countInner_deformedLine (hp : 1 < p) (c d : ℝ) :
    countInner p (primeSquareDeformedLine p c) (primeSquareDeformedLine p d)
      = ((((p : ℝ) + (p : ℝ) ^ (c + d))
          / Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (2 * d))) : ℝ) : ℂ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) := by linarith
  have hW : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hX : (0 : ℝ) < (p : ℝ) + (p : ℝ) ^ (2 * c) := by positivity
  have hY : (0 : ℝ) < (p : ℝ) + (p : ℝ) ^ (2 * d) := by positivity
  have hprod : Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c)))
      * Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * d)))
      = ((p : ℝ) - 1)
        * Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (2 * d))) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show ((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))
        * (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * d)))
        = ((p : ℝ) - 1) ^ 2
          * (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (2 * d))) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hW.le]
  have hXne : Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hYne : Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * d))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hXYne : Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (2 * d))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hWne : ((p : ℝ) - 1) ≠ 0 := ne_of_gt hW
  have hkey : countInner p (primeSquareDeformedLine p c) (primeSquareDeformedLine p d)
      = (((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) : ℝ) : ℂ)⁻¹
          * ((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * d))) : ℝ) : ℂ)⁻¹)
        * (((p : ℂ) - 1) * ((p : ℂ) + (((p : ℝ) ^ (c + d) : ℝ) : ℂ))) := by
    show countInner p
        (fun x => ((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) : ℝ) : ℂ)⁻¹
          * primeSquareDeformedMobius p c x)
        (fun x => ((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * d))) : ℝ) : ℂ)⁻¹
          * primeSquareDeformedMobius p d x) = _
    rw [countInner_smul_left, countInner_smul_right, countInner_deformedMobius hp,
      conj_ofReal_inv]
    ring
  rw [hkey]
  have hcast : ((p : ℂ)) - 1 = ((((p : ℝ) - 1 : ℝ)) : ℂ) := by push_cast; ring
  have hcast2 : ((p : ℂ)) + (((p : ℝ) ^ (c + d) : ℝ) : ℂ)
      = ((((p : ℝ) + (p : ℝ) ^ (c + d) : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, hcast2, ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [← mul_inv, hprod]
  field_simp

end Deformed


/-! ## Prime-facing capstone -/

/-- **The prime-square Möbius--Fourier complementary record law.**  For every prime `p` the
additive Fourier clock on `ZMod (p ^ 2)` has an exact continuation eigenvector `c_p` with
eigenvalue `1`; the normalized squarefree occupation vector is precisely the transverse record
eigenvector `t_p`, compressed to `−1/p` with leakage `1 − p^(−2)`; and the signed Möbius record
is the complementary combination `σ_p c_p + τ_p t_p` with `σ_p² + τ_p² = 1`. -/
theorem primeSquare_complementary_record_law {p : ℕ} [NeZero p] (hp : p.Prime) :
    primeSquareFourier p (primeSquareFourierFixedVec p) = primeSquareFourierFixedVec p
      ∧ countInner p (primeSquareFourierFixedVec p)
          (primeSquareFourier p (primeSquareRecordVec p)) = 0
      ∧ countInner p (primeSquareRecordVec p) (primeSquareFourier p (primeSquareRecordVec p))
          = -(p : ℂ)⁻¹
      ∧ countInner p (primeSquareRecordLeak p) (primeSquareRecordLeak p)
          = 1 - (p : ℂ)⁻¹ * (p : ℂ)⁻¹
      ∧ primeSquareOccupationVec p = primeSquareRecordVec p
      ∧ primeSquareSourceInvolution p (primeSquareOccupationVec p) = primeSquareMobiusVec p
      ∧ primeSquareMobiusVec p
          = (fun x => ((primeRecordSigma p : ℝ) : ℂ) * primeSquareFourierFixedVec p x
              + ((primeRecordTau p : ℝ) : ℂ) * primeSquareRecordVec p x)
      ∧ primeRecordSigma p ^ 2 + primeRecordTau p ^ 2 = 1
      ∧ primeRecordSigma p = 1 / Real.cosh (Real.log (p : ℝ) / 2)
      ∧ primeRecordTau p = Real.tanh (Real.log (p : ℝ) / 2)
      ∧ countInner p (primeSquareMobiusDFT p) (primeSquareMobiusDFT p)
          = 1 - ((p : ℂ) ^ 2)⁻¹ := by
  have h1 : 1 < p := hp.one_lt
  exact ⟨primeSquareFourier_fourierFixedVec h1,
    countInner_fourierFixedVec_fourier_recordVec h1,
    countInner_recordVec_fourier_recordVec h1,
    countInner_recordLeak_self h1,
    primeSquareOccupationVec_eq_recordVec,
    primeSquareSourceInvolution_occupationVec,
    primeSquareMobiusVec_eq h1,
    primeRecordSigma_sq_add_tau_sq h1,
    primeRecordSigma_eq_sech h1,
    primeRecordTau_eq_tanh h1,
    countInner_mobiusDFT_self h1⟩

end

end RHTower
