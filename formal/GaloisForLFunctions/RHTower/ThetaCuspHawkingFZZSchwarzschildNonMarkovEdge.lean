import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildDressedLogIncidence
import GaloisForLFunctions.HTGeometry.NormalizedMomentQuantumVariance

/-!
# FZZ--Schwarzschild memory excludes canonical Markov completion

The exact protected FZZ long-string delay clock and the four-dimensional Schwarzschild
dressed-log response jet are the same positive moment sequence

`M_m = sum_{j >= 0} (j + 1)^(-m-2) = zeta(m+2)`.

This file tests the canonical long edge proposed for a three-shell Hawking completion against
that source-derived all-order clock.  At response depth `b`, the three moment features
`1, x, x^2` give

`K_01 = M_(b+1)`, `K_11 = K_02 = M_(b+2)`, `K_12 = M_(b+3)`.

Conditional independence through the middle feature would replace the actual remote edge by

`K_02^Markov = K_01 K_12 / K_11`.

The reciprocal-energy spectrum has infinitely many positive nodes and weights.  Its shifted
two-by-two Hankel determinant is therefore strictly positive at every depth:

`M_(b+1) M_(b+3) - M_(b+2)^2 > 0`.

Consequently the actual black-hole edge is always strictly smaller than its canonical Markov
completion.  The difference is an exact positive, nonzero remote-memory channel.  Through the
proved FZZ--Schwarzschild incidence, the same statement holds for the protected cigar delay.

**[POSITIVE SURVIVOR]** Canonical Schur/Cayley completion is not merely unselected by the known
dynamics: it is incompatible with the all-depth response clock actually supplied by these two
black-hole scattering calculations.  Any Hawking-native RH producer using this clock must retain
irreducible remote coupling rather than impose conditional independence.

**[SCOPE]** Response-jet depth is an observable-order coordinate, not a spatial shell or time
step.  This theorem does not identify the theta three-shell kernel with the moment kernel and does
not prove RH.  It closes the finite-memory canonical-completion branch and sharpens the remaining
physical weld to a theta-dependent, non-Markov influence functional.

The exact remote-memory defect is also identified below as a positive prefactor times the static
susceptibility, equivalently one quarter of the pure-state quantum Fisher fluctuation, of the
size-biased reciprocal-energy Bose state.  This is not yet the stochastic noise kernel of an
Einstein--Langevin or Teukolsky influence functional; deriving that dynamical incidence remains
open.

`[LITERATURE]` The FZZ reflection asymmetry is from Ashok--Troost, arXiv:1101.1059; the
Schwarzschild dressed logarithm is from Solon, arXiv:2606.19281.  Hankel positivity of zeta-value
sequences has related amplitude precedents, including Green--Wen, arXiv:1908.08426.  The exact
cross-black-hole non-Markov conclusion is `[NOVELTY UNVERIFIED]`.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- Bose spectral weight after shifting the observed response-jet order. -/
def gammaBoseShiftedWeight (a : ℝ) (shift j : ℕ) : ℝ :=
  gammaBoseWeight a j * gammaBoseNode a j ^ shift

theorem gammaBoseShiftedWeight_pos
    {a : ℝ} (ha : 0 < a) (shift j : ℕ) :
    0 < gammaBoseShiftedWeight a shift j := by
  exact mul_pos (gammaBoseWeight_pos ha j) (pow_pos (by
    simp only [gammaBoseNode]
    positivity) _)

theorem summable_gammaBoseShiftedWeight_mul_node_abs_pow
    {a : ℝ} (ha : 0 < a) (shift m : ℕ) :
    Summable (fun j : ℕ =>
      gammaBoseShiftedWeight a shift j * |gammaBoseNode a j| ^ m) := by
  apply (summable_gammaBoseWeight_mul_node_abs_pow ha (shift + m)).congr
  intro j
  have hx : |gammaBoseNode a j| = gammaBoseNode a j := by
    rw [abs_of_pos]
    simp only [gammaBoseNode]
    positivity
  simp only [gammaBoseShiftedWeight, hx, pow_add]
  ring

theorem gammaBoseShifted_infiniteSupport
    {a : ℝ} (ha : 0 < a) (shift : ℕ) (F : Finset ℝ) :
    ∃ j : ℕ, gammaBoseNode a j ∉ F ∧
      0 < gammaBoseShiftedWeight a shift j := by
  obtain ⟨j, hj, _⟩ := gammaBose_infiniteSupport ha F
  exact ⟨j, hj, gammaBoseShiftedWeight_pos ha shift j⟩

theorem gammaBoseShiftedMoment_eq
    (a : ℝ) (shift m : ℕ) :
    (∑' j : ℕ,
      gammaBoseShiftedWeight a shift j * gammaBoseNode a j ^ m) =
      gammaBoseMoment a (shift + m) := by
  rw [gammaBoseMoment]
  apply tsum_congr
  intro j
  simp only [gammaBoseShiftedWeight, pow_add]
  ring

/-- Strict all-depth memory law for the Bose response clock. -/
theorem gammaBoseMoment_strictLogConvex
    {a : ℝ} (ha : 0 < a) (shift : ℕ) :
    gammaBoseMoment a (shift + 1) ^ 2 <
      gammaBoseMoment a shift * gammaBoseMoment a (shift + 2) := by
  let w : ℕ → ℝ := gammaBoseShiftedWeight a shift
  let x : ℕ → ℝ := gammaBoseNode a
  have hdet := (discreteMomentHankel_posDef w x
    (fun j => (gammaBoseShiftedWeight_pos ha shift j).le)
    (summable_gammaBoseShiftedWeight_mul_node_abs_pow ha shift)
    (gammaBoseShifted_infiniteSupport ha shift) 2).det_pos
  simp only [momentHankelMatrix, Matrix.det_fin_two] at hdet
  norm_num [w, x] at hdet
  have h0 := gammaBoseShiftedMoment_eq a shift 0
  have h1 := gammaBoseShiftedMoment_eq a shift 1
  have h2 := gammaBoseShiftedMoment_eq a shift 2
  norm_num at h0 h1 h2
  rw [h0, h1, h2] at hdet
  nlinarith

theorem gammaBoseMoment_pos
    {a : ℝ} (ha : 0 < a) (m : ℕ) :
    0 < gammaBoseMoment a m := by
  let w : ℕ → ℝ := gammaBoseShiftedWeight a m
  let x : ℕ → ℝ := gammaBoseNode a
  have hdiag : 0 <
      (momentHankelMatrix (fun k => ∑' j, w j * x j ^ k) 1)
        (0 : Fin 1) (0 : Fin 1) :=
    (discreteMomentHankel_posDef w x
      (fun j => (gammaBoseShiftedWeight_pos ha m j).le)
      (summable_gammaBoseShiftedWeight_mul_node_abs_pow ha m)
      (gammaBoseShifted_infiniteSupport ha m) 1).diag_pos
  simp only [momentHankelMatrix] at hdiag
  norm_num [w, x] at hdiag
  have h0 := gammaBoseShiftedMoment_eq a m 0
  norm_num at h0
  rwa [h0] at hdiag

end

end HTGeometry

namespace RHTower

open HTGeometry
open Polynomial

noncomputable section

/-- Actual long edge of three consecutive response-jet shells. -/
def blackHoleFarZoneActualJetLongEdge (scaleLog : ℂ) (base : ℕ) : ℝ :=
  normalizedBlackHoleFarZoneJet scaleLog (base + 2)

/-- Conditional-independence/Markov completion of the same three response-jet shells. -/
def blackHoleFarZoneCanonicalJetLongEdge (scaleLog : ℂ) (base : ℕ) : ℝ :=
  normalizedBlackHoleFarZoneJet scaleLog (base + 1) *
      normalizedBlackHoleFarZoneJet scaleLog (base + 3) /
    normalizedBlackHoleFarZoneJet scaleLog (base + 2)

/-- Genuine Schwarzschild Bose memory lies strictly below the canonical Markov long edge at
every response depth. -/
theorem blackHoleFarZoneActualJetLongEdge_lt_canonical
    (scaleLog : ℂ) (base : ℕ) :
    blackHoleFarZoneActualJetLongEdge scaleLog base <
      blackHoleFarZoneCanonicalJetLongEdge scaleLog base := by
  have hstrict := gammaBoseMoment_strictLogConvex (a := 1) (by norm_num) (base + 1)
  have hpos : 0 < gammaBoseMoment 1 (base + 2) :=
    gammaBoseMoment_pos (by norm_num) _
  rw [blackHoleFarZoneActualJetLongEdge,
    blackHoleFarZoneCanonicalJetLongEdge]
  simp only [normalizedBlackHoleFarZoneJet_eq_gammaBoseMoment]
  rw [lt_div_iff₀ hpos]
  simpa [pow_two, Nat.add_assoc] using hstrict

/-- Exact positive non-Markov remote-shell correction. -/
theorem blackHoleFarZoneCanonical_sub_actual_pos
    (scaleLog : ℂ) (base : ℕ) :
    0 < blackHoleFarZoneCanonicalJetLongEdge scaleLog base -
      blackHoleFarZoneActualJetLongEdge scaleLog base :=
  sub_pos.mpr (blackHoleFarZoneActualJetLongEdge_lt_canonical scaleLog base)

/-- Same strict non-Markov law for the FZZ long-string delay clock, by exact 2D--4D incidence. -/
theorem fzzCigarNormalizedDelayMoment_actual_lt_canonical
    (base : ℕ) :
    fzzCigarNormalizedDelayMoment (base + 2) <
      fzzCigarNormalizedDelayMoment (base + 1) *
          fzzCigarNormalizedDelayMoment (base + 3) /
        fzzCigarNormalizedDelayMoment (base + 2) := by
  have h := blackHoleFarZoneActualJetLongEdge_lt_canonical 0 base
  rw [blackHoleFarZoneActualJetLongEdge,
    blackHoleFarZoneCanonicalJetLongEdge] at h
  simpa only [fzzCigarNormalizedDelayMoment_eq_blackHoleFarZoneJet 0] using h

/-! ## Exact fluctuation content of the forced remote edge -/

/-- Static reciprocal-energy susceptibility in the `(base + 1)`-st size-biased Bose state. -/
def blackHoleFarZoneBoseSpectralSusceptibility (base : ℕ) : ℝ :=
  momentNormalizedVariance
    (momentSizeBiasedSequence (gammaBoseMoment 1) (base + 1)) Polynomial.X

/-- The canonical-minus-actual edge is exactly the size-biased Bose susceptibility multiplied by
its source normalization.  Thus the forced non-Markov channel has a precise fluctuation content;
it is not an arbitrary completion parameter. -/
theorem blackHoleFarZoneCanonical_sub_actual_eq_spectralSusceptibility
    (scaleLog : ℂ) (base : ℕ) :
    blackHoleFarZoneCanonicalJetLongEdge scaleLog base -
        blackHoleFarZoneActualJetLongEdge scaleLog base =
      gammaBoseMoment 1 (base + 1) ^ 2 /
          gammaBoseMoment 1 (base + 2) *
        blackHoleFarZoneBoseSpectralSusceptibility base := by
  rw [blackHoleFarZoneActualJetLongEdge,
    blackHoleFarZoneCanonicalJetLongEdge]
  simp only [normalizedBlackHoleFarZoneJet_eq_gammaBoseMoment]
  rw [blackHoleFarZoneBoseSpectralSusceptibility,
    momentNormalizedVariance_X_sizeBiased]
  have h1 : gammaBoseMoment 1 (base + 1) ≠ 0 :=
    (gammaBoseMoment_pos (a := 1) (by norm_num) _).ne'
  have h2 : gammaBoseMoment 1 (base + 2) ≠ 0 :=
    (gammaBoseMoment_pos (a := 1) (by norm_num) _).ne'
  norm_num [Nat.add_assoc]
  field_simp [h1, h2]

/-- Pure-state quantum Fisher fluctuation of the same size-biased reciprocal-energy state. -/
def blackHoleFarZoneBoseSpectralQuantumFisher (base : ℕ) : ℝ :=
  let s := momentSizeBiasedSequence (gammaBoseMoment 1) (base + 1)
  pureStateQuantumFisherValue (s 0)
    (momentFunctional s Polynomial.X) (momentFunctional s (Polynomial.X ^ 2))

/-- Spectral quantum Fisher information is four times the Bose susceptibility. -/
theorem blackHoleFarZoneBoseSpectralQuantumFisher_eq_four_mul_susceptibility
    (base : ℕ) :
    blackHoleFarZoneBoseSpectralQuantumFisher base =
      4 * blackHoleFarZoneBoseSpectralSusceptibility base := by
  let s := momentSizeBiasedSequence (gammaBoseMoment 1) (base + 1)
  have h0 : s 0 ≠ 0 := by
    simpa [s, momentSizeBiasedSequence] using
      (gammaBoseMoment_pos (a := 1) (by norm_num) (base + 1)).ne'
  simpa [blackHoleFarZoneBoseSpectralQuantumFisher,
    blackHoleFarZoneBoseSpectralSusceptibility, s] using
    pureStateQuantumFisherValue_moment_eq_four_mul_normalizedVariance
      s h0 Polynomial.X

/-- Exact Fisher-information form of the non-Markov remote-edge defect. -/
theorem blackHoleFarZoneCanonical_sub_actual_eq_spectralQuantumFisher
    (scaleLog : ℂ) (base : ℕ) :
    blackHoleFarZoneCanonicalJetLongEdge scaleLog base -
        blackHoleFarZoneActualJetLongEdge scaleLog base =
      gammaBoseMoment 1 (base + 1) ^ 2 /
          (4 * gammaBoseMoment 1 (base + 2)) *
        blackHoleFarZoneBoseSpectralQuantumFisher base := by
  rw [blackHoleFarZoneBoseSpectralQuantumFisher_eq_four_mul_susceptibility,
    blackHoleFarZoneCanonical_sub_actual_eq_spectralSusceptibility]
  have h2 : gammaBoseMoment 1 (base + 2) ≠ 0 :=
    (gammaBoseMoment_pos (a := 1) (by norm_num) _).ne'
  field_simp [h2]

/-- Every size-biased Bose response shell has strictly positive static susceptibility. -/
theorem blackHoleFarZoneBoseSpectralSusceptibility_pos (base : ℕ) :
    0 < blackHoleFarZoneBoseSpectralSusceptibility base := by
  have hgap := blackHoleFarZoneCanonical_sub_actual_pos 0 base
  rw [blackHoleFarZoneCanonical_sub_actual_eq_spectralSusceptibility] at hgap
  have hprefactor : 0 <
      gammaBoseMoment 1 (base + 1) ^ 2 /
        gammaBoseMoment 1 (base + 2) := by
    exact div_pos (sq_pos_of_pos (gammaBoseMoment_pos (a := 1) (by norm_num) _))
      (gammaBoseMoment_pos (a := 1) (by norm_num) _)
  exact pos_of_mul_pos_right hgap hprefactor.le

end

end RHTower
