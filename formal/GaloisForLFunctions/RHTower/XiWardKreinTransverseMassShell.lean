import GaloisForLFunctions.HTGeometry.CarrierPickKernel
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardHerglotzTangent
import GaloisForLFunctions.RHTower.XiWardEndpointSourceIndex

/-!
# Ward-positive / Krein-indefinite mass shell

For one conjugate pole pair, evaluate its Pick diagonal at the canonical inward and outward
normal witnesses.  Before transverse renormalization the values are
`-8 / (3 * delta^(2 : ℕ))` and `2 / (3 * delta^(2 : ℕ))`.  Multiplication by the squared pole height produces
the rigid quanta `-8/3` and `2/3`, hence a four-to-one signed balance.

Specializing the pole to the upper spectral representative of a strict-right Xi zero gives a
single atomic law: the same off-line pair has a positive Ward tangent on every finite
right-half-plane packet and exact Ward mass `8*pi`, yet its transverse carrier has the nonzero
Krein quanta above.  Thus first-order Ward positivity and transverse Pick instability coexist;
the RH-bearing datum is their oriented coupling, not either positive marginal.

No RH premise, numerical estimate, or added axiom enters.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

def conjugatePairCarrierValue (t z : ℂ) : ℂ :=
  (t - z)⁻¹ + (star t - z)⁻¹

def conjugatePairPickDiagonal (t z : ℂ) : ℂ :=
  (conjugatePairCarrierValue t z - star (conjugatePairCarrierValue t z)) /
    (z - star z)

def conjugatePairInwardWitness (t : ℂ) : ℂ :=
  t - I * ((t.im / 2 : ℝ) : ℂ)

def conjugatePairOutwardWitness (t : ℂ) : ℂ :=
  t + I * ((t.im : ℝ) : ℂ)

theorem conjugatePairCarrierValue_inward_im
    (t : ℂ) (ht : t.im ≠ 0) :
    (conjugatePairCarrierValue t (conjugatePairInwardWitness t)).im =
      -4 / (3 * t.im) := by
  rw [conjugatePairCarrierValue, conjugatePairInwardWitness, Complex.add_im]
  have e1 : t - (t - I * ((t.im / 2 : ℝ) : ℂ)) =
      I * ((t.im / 2 : ℝ) : ℂ) := by ring
  have hsc : t - star t = ((2 * t.im : ℝ) : ℂ) * I := by
    rw [show star t = (starRingEnd ℂ) t from rfl, Complex.sub_conj]
  have e2 : star t - (t - I * ((t.im / 2 : ℝ) : ℂ)) =
      I * (((-3 * t.im / 2 : ℝ)) : ℂ) := by
    have hst : star t - t = -(((2 * t.im : ℝ) : ℂ) * I) := by
      rw [← hsc]
      ring
    rw [show star t - (t - I * ((t.im / 2 : ℝ) : ℂ)) =
      (star t - t) + I * ((t.im / 2 : ℝ) : ℂ) from by ring, hst]
    push_cast
    ring
  rw [e1, e2, imInv_I_mul _ (div_ne_zero ht (by norm_num)),
    imInv_I_mul _ (by intro h; apply ht; linarith)]
  field_simp
  ring

theorem conjugatePairCarrierValue_outward_im
    (t : ℂ) (ht : t.im ≠ 0) :
    (conjugatePairCarrierValue t (conjugatePairOutwardWitness t)).im =
      4 / (3 * t.im) := by
  rw [conjugatePairCarrierValue, conjugatePairOutwardWitness, Complex.add_im]
  have e1 : t - (t + I * ((t.im : ℝ) : ℂ)) =
      I * (((-t.im : ℝ)) : ℂ) := by
    push_cast
    ring
  have hsc : t - star t = ((2 * t.im : ℝ) : ℂ) * I := by
    rw [show star t = (starRingEnd ℂ) t from rfl, Complex.sub_conj]
  have e2 : star t - (t + I * ((t.im : ℝ) : ℂ)) =
      I * (((-3 * t.im : ℝ)) : ℂ) := by
    have hst : star t - t = -(((2 * t.im : ℝ) : ℂ) * I) := by
      rw [← hsc]
      ring
    rw [show star t - (t + I * ((t.im : ℝ) : ℂ)) =
      (star t - t) - I * ((t.im : ℝ) : ℂ) from by ring, hst]
    push_cast
    ring
  rw [e1, e2, imInv_I_mul _ (by exact neg_ne_zero.mpr ht),
    imInv_I_mul _ (by intro h; apply ht; linarith)]
  field_simp
  ring

theorem conjugatePairPickDiagonal_inward_re
    (t : ℂ) (ht : t.im ≠ 0) :
    (conjugatePairPickDiagonal t (conjugatePairInwardWitness t)).re =
      -8 / (3 * t.im ^ 2) := by
  have hzim : (conjugatePairInwardWitness t).im = t.im / 2 := by
    simp [conjugatePairInwardWitness, Complex.sub_im, Complex.mul_im]
    ring
  rw [conjugatePairPickDiagonal,
    pickDiag_re _ _ (hzim.symm ▸ div_ne_zero ht (by norm_num)),
    conjugatePairCarrierValue_inward_im t ht]
  simp only [conjugatePairInwardWitness]
  simp [Complex.sub_im, Complex.mul_im]
  field_simp
  ring

theorem conjugatePairPickDiagonal_outward_re
    (t : ℂ) (ht : t.im ≠ 0) :
    (conjugatePairPickDiagonal t (conjugatePairOutwardWitness t)).re =
      2 / (3 * t.im ^ 2) := by
  have hzim : (conjugatePairOutwardWitness t).im = 2 * t.im := by
    simp [conjugatePairOutwardWitness, Complex.add_im, Complex.mul_im]
    ring
  rw [conjugatePairPickDiagonal,
    pickDiag_re _ _ (hzim.symm ▸ mul_ne_zero (by norm_num) ht),
    conjugatePairCarrierValue_outward_im t ht]
  simp only [conjugatePairOutwardWitness]
  simp [Complex.add_im, Complex.mul_im]
  field_simp
  ring

theorem conjugatePairPickDiagonal_massShell
    (t : ℂ) (ht : t.im ≠ 0) :
    (conjugatePairPickDiagonal t (conjugatePairInwardWitness t)).re +
        4 * (conjugatePairPickDiagonal t (conjugatePairOutwardWitness t)).re = 0 := by
  rw [conjugatePairPickDiagonal_inward_re t ht,
    conjugatePairPickDiagonal_outward_re t ht]
  ring

theorem conjugatePairPickDiagonal_inward_quantum
    (t : ℂ) (ht : t.im ≠ 0) :
    t.im ^ 2 *
        (-(conjugatePairPickDiagonal t (conjugatePairInwardWitness t)).re) =
      8 / 3 := by
  rw [conjugatePairPickDiagonal_inward_re t ht]
  field_simp [ht]

theorem conjugatePairPickDiagonal_outward_quantum
    (t : ℂ) (ht : t.im ≠ 0) :
    t.im ^ 2 *
        (conjugatePairPickDiagonal t (conjugatePairOutwardWitness t)).re =
      2 / 3 := by
  rw [conjugatePairPickDiagonal_outward_re t ht]
  field_simp [ht]

end

end GaloisForLFunctions

namespace RHTower

open Complex GaloisForLFunctions MeasureTheory
open scoped ComplexOrder

noncomputable section

/-- Upper-half-plane spectral pole associated to a strict-right upper Xi copy. -/
def xiWardKreinUpperSpectralPole (q : XiRightUpperZeroCopy) : ℂ :=
  star (xiSpectralPoint q.1.1)

theorem xiWardKreinUpperSpectralPole_im_eq_transverse
    (q : XiRightUpperZeroCopy) :
    (xiWardKreinUpperSpectralPole q).im = (xiRightCenteredZero q.1).re := by
  rw [xiWardKreinUpperSpectralPole, xiRightCenteredZero]
  simp [Complex.mul_re]

theorem xiWardKreinUpperSpectralPole_im_pos
    (q : XiRightUpperZeroCopy) :
    0 < (xiWardKreinUpperSpectralPole q).im := by
  rw [xiWardKreinUpperSpectralPole_im_eq_transverse]
  exact xiRightCenteredZero_re_pos q.1

/-- Exact renormalized negative Pick quantum carried by an off-line Xi pair. -/
theorem xiWardKrein_inwardPickQuantum (q : XiRightUpperZeroCopy) :
    (xiRightCenteredZero q.1).re ^ 2 *
        (-(conjugatePairPickDiagonal (xiWardKreinUpperSpectralPole q)
          (conjugatePairInwardWitness (xiWardKreinUpperSpectralPole q))).re) =
      8 / 3 := by
  have ht := (xiWardKreinUpperSpectralPole_im_pos q).ne'
  simpa [xiWardKreinUpperSpectralPole_im_eq_transverse q] using
    conjugatePairPickDiagonal_inward_quantum
      (xiWardKreinUpperSpectralPole q) ht

/-- Exact renormalized positive Pick quantum paired with the negative channel. -/
theorem xiWardKrein_outwardPickQuantum (q : XiRightUpperZeroCopy) :
    (xiRightCenteredZero q.1).re ^ 2 *
        (conjugatePairPickDiagonal (xiWardKreinUpperSpectralPole q)
          (conjugatePairOutwardWitness (xiWardKreinUpperSpectralPole q))).re =
      2 / 3 := by
  have ht := (xiWardKreinUpperSpectralPole_im_pos q).ne'
  simpa [xiWardKreinUpperSpectralPole_im_eq_transverse q] using
    conjugatePairPickDiagonal_outward_quantum
      (xiWardKreinUpperSpectralPole q) ht

/-- An off-line Xi pair has a positive Ward tangent but a rigid transverse Krein mass shell. -/
theorem xiWardKrein_transverseAtomicLaw (q : XiRightUpperZeroCopy) :
    (∫⁻ t : ℝ, ENNReal.ofReal
        (2 * (xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      ENNReal.ofReal (8 * Real.pi)) ∧
    (xiRightCenteredZero q.1).re ^ 2 *
        (-(conjugatePairPickDiagonal (xiWardKreinUpperSpectralPole q)
          (conjugatePairInwardWitness (xiWardKreinUpperSpectralPole q))).re) =
      8 / 3 ∧
    (xiRightCenteredZero q.1).re ^ 2 *
        (conjugatePairPickDiagonal (xiWardKreinUpperSpectralPole q)
          (conjugatePairOutwardWitness (xiWardKreinUpperSpectralPole q))).re =
      2 / 3 ∧
    ∀ {n : ℕ} (w : Fin n → ℂ),
      (∀ i, 0 < (w i).re) →
      (xiWardSchwarzPairHerglotzPickMatrix w q).PosSemidef := by
  exact ⟨
    lintegral_infinitesimalDefect_xiAntiCausalWardSchwarzPair_eulerEdge q,
    xiWardKrein_inwardPickQuantum q,
    xiWardKrein_outwardPickQuantum q,
    fun w hw => xiWardSchwarzPairHerglotzPickMatrix_posSemidef hw q⟩

/-- Canonically summable coupling of endpoint source weight to the renormalized inward Pick
quantum. -/
def xiWardKreinWeightedTransverseAtom (q : XiRightUpperZeroCopy) : ℝ :=
  xiEndpointWardPairWeight q *
    ((xiRightCenteredZero q.1).re ^ 2 *
      (-(conjugatePairPickDiagonal (xiWardKreinUpperSpectralPole q)
        (conjugatePairInwardWitness (xiWardKreinUpperSpectralPole q))).re))

/-- The transverse atom contains no hidden gain: after canonical renormalization it is exactly
`8/3` times the endpoint Ward weight. -/
theorem xiWardKreinWeightedTransverseAtom_eq (q : XiRightUpperZeroCopy) :
    xiWardKreinWeightedTransverseAtom q =
      (8 / 3) * xiEndpointWardPairWeight q := by
  rw [xiWardKreinWeightedTransverseAtom, xiWardKrein_inwardPickQuantum]
  ring

theorem summable_xiWardKreinWeightedTransverseAtom :
    Summable xiWardKreinWeightedTransverseAtom := by
  rw [show xiWardKreinWeightedTransverseAtom =
      fun q => (8 / 3) * xiEndpointWardPairWeight q from
    funext xiWardKreinWeightedTransverseAtom_eq]
  exact summable_xiEndpointWardPairWeight.mul_left (8 / 3)

/-- Global source-weighted transverse Krein index. -/
def xiWardKreinWeightedTransverseIndex : ℝ :=
  ∑' q : XiRightUpperZeroCopy, xiWardKreinWeightedTransverseAtom q

/-- **Weighted-coupling no-go.** The globally summable transverse index is exactly the existing
endpoint-weighted Ward index divided by `3*pi`.  Canonical source weighting therefore restores
summability only by collapsing the new transverse quantum back to the old RH endpoint. -/
theorem xiWardKreinWeightedTransverseIndex_eq :
    xiWardKreinWeightedTransverseIndex =
      xiEndpointWeightedWardIndex / (3 * Real.pi) := by
  rw [xiWardKreinWeightedTransverseIndex,
    tsum_congr xiWardKreinWeightedTransverseAtom_eq,
    tsum_mul_left, xiEndpointWeightedWardIndex]
  field_simp [Real.pi_ne_zero]

theorem xiWardKreinWeightedTransverseIndex_eq_zero_iff_rh :
    xiWardKreinWeightedTransverseIndex = 0 ↔ RiemannHypothesis := by
  rw [xiWardKreinWeightedTransverseIndex_eq,
    div_eq_zero_iff, xiEndpointWeightedWardIndex_eq_zero_iff_rh,
    or_iff_left (mul_ne_zero (by norm_num) Real.pi_ne_zero)]

end

end RHTower
