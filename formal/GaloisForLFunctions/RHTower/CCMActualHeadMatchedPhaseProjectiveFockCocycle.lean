import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseInfiniteFockKernel

/-!
# Projective Fock cocycle for the intact matched CCM source

The trace-free Fock carrier made the matched cosine and sine channels into logarithmic anchor
entries, but the intact oriented source was still read by an external signed linear combination.
This module internalizes that reporter.

An arithmetic atom is lifted to the three-dimensional feature `(w, C-w, S)`.  Its moving phase
probe is `(cos θ, cos θ, sin θ)`.  Their inner product is exactly `C cos θ + S sin θ`, because the
critical weight cancels inside the first two coordinates.  Pairing the atom with both the probe
and its negative in an exponential-inner-product Fock kernel makes the entire oriented source half
the logarithm of a positive entry ratio.

The kernel is one infinite PSD kernel on all arithmetic atoms and probes.  Multiplying its ratios
over a finite packet gives a projective holonomy whose logarithm is exactly twice the finite CCM
source symbol.  Thus every finite actual matched prime-polar block is the spectral integral of one
multiplicative positive-kernel cocycle, with no external weight term or target-fitted completion.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder RealInnerProductSpace

noncomputable section
namespace RHTower

abbrev CCMActualHeadMatchedPhaseProjectiveFockSpace := EuclideanSpace ℝ (Fin 3)

/-- Arithmetic feature retaining critical weight and the two trace-free Bloch coordinates. -/
def ccmActualHeadMatchedPhaseProjectiveAtomFeature (n : ℕ) (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveFockSpace :=
  WithLp.toLp 2 ![criticalMellinAtomWeight n,
    ccmActualHeadMatchedCosinePhaseProfile n xi - criticalMellinAtomWeight n,
    ccmActualHeadMatchedSinePhaseProfile n xi]

/-- Moving phase probe that cancels the split critical-weight coordinates in its pairing. -/
def ccmActualHeadMatchedPhaseRotatingProbe (n : ℕ) (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveFockSpace :=
  let theta := 2 * Real.pi * Real.log n * xi
  WithLp.toLp 2 ![Real.cos theta, Real.cos theta, Real.sin theta]

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveAtomFeature_apply_zero
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveAtomFeature n xi 0 =
      criticalMellinAtomWeight n := rfl

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveAtomFeature_apply_one
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveAtomFeature n xi 1 =
      ccmActualHeadMatchedCosinePhaseProfile n xi - criticalMellinAtomWeight n := rfl

@[simp] theorem ccmActualHeadMatchedPhaseProjectiveAtomFeature_apply_two
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveAtomFeature n xi 2 =
      ccmActualHeadMatchedSinePhaseProfile n xi := rfl

@[simp] theorem ccmActualHeadMatchedPhaseRotatingProbe_apply_zero
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseRotatingProbe n xi 0 =
      Real.cos (2 * Real.pi * Real.log n * xi) := rfl

@[simp] theorem ccmActualHeadMatchedPhaseRotatingProbe_apply_one
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseRotatingProbe n xi 1 =
      Real.cos (2 * Real.pi * Real.log n * xi) := rfl

@[simp] theorem ccmActualHeadMatchedPhaseRotatingProbe_apply_two
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseRotatingProbe n xi 2 =
      Real.sin (2 * Real.pi * Real.log n * xi) := rfl

/-- Arithmetic atoms and their positive/negative moving probes. -/
inductive CCMActualHeadMatchedPhaseProjectiveFockIndex (ι : Type*)
  | atom (i : ι)
  | positiveProbe (i : ι)
  | negativeProbe (i : ι)
  deriving DecidableEq, Fintype

namespace CCMActualHeadMatchedPhaseProjectiveFockIndex

def feature {ι : Type*} (n : ι → ℕ) (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveFockIndex ι →
      CCMActualHeadMatchedPhaseProjectiveFockSpace
  | atom i => ccmActualHeadMatchedPhaseProjectiveAtomFeature (n i) xi
  | positiveProbe i => ccmActualHeadMatchedPhaseRotatingProbe (n i) xi
  | negativeProbe i => -ccmActualHeadMatchedPhaseRotatingProbe (n i) xi

end CCMActualHeadMatchedPhaseProjectiveFockIndex

def ccmActualHeadMatchedPhaseProjectiveFockMatrix {ι : Type*}
    (n : ι → ℕ) (xi : ℝ) :
    Matrix (CCMActualHeadMatchedPhaseProjectiveFockIndex ι)
      (CCMActualHeadMatchedPhaseProjectiveFockIndex ι) ℝ :=
  GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix
    (CCMActualHeadMatchedPhaseProjectiveFockIndex.feature n xi) (1 / 2)

def ccmActualHeadMatchedPhaseProjectiveFockKernel {ι : Type*}
    (n : ι → ℕ) (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveFockIndex ι →
      CCMActualHeadMatchedPhaseProjectiveFockIndex ι → ℂ :=
  fun a b => (ccmActualHeadMatchedPhaseProjectiveFockMatrix n xi a b : ℂ)

/-- The atom/probe Fock carrier is one genuine infinite PSD kernel. -/
theorem ccmActualHeadMatchedPhaseProjectiveFockKernel_isPSDKernel
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
      (ccmActualHeadMatchedPhaseProjectiveFockKernel n xi) := by
  apply GaloisForLFunctions.HTGeometry.isPSDKernel_of_forall_posSemidef
  · intro a b
    have hs : ccmActualHeadMatchedPhaseProjectiveFockMatrix n xi a b =
        ccmActualHeadMatchedPhaseProjectiveFockMatrix n xi b a := by
      simp [ccmActualHeadMatchedPhaseProjectiveFockMatrix,
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
        real_inner_comm]
    simpa [ccmActualHeadMatchedPhaseProjectiveFockKernel] using
      congrArg (fun r : ℝ => (r : ℂ)) hs
  · intro m w
    let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun j k =>
      ccmActualHeadMatchedPhaseProjectiveFockMatrix n xi (w j) (w k)
    have hA : A.PosSemidef := by
      have h :=
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix_fin_posSemidef
          (fun j => CCMActualHeadMatchedPhaseProjectiveFockIndex.feature n xi (w j))
          (1 / 2) (by norm_num)
      convert h using 1
      ext j k
      simp [A, ccmActualHeadMatchedPhaseProjectiveFockMatrix,
        GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix]
    convert realMatrix_posSemidef_map_complex A hA using 1
    ext j k
    rfl

/-- Atom/probe pairing is the intact oriented source, including its critical weight. -/
theorem ccmActualHeadMatchedPhaseProjectiveAtom_inner_rotatingProbe
    (n : ℕ) (xi : ℝ) :
    inner ℝ (ccmActualHeadMatchedPhaseProjectiveAtomFeature n xi)
        (ccmActualHeadMatchedPhaseRotatingProbe n xi) =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re]
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [ccmActualHeadMatchedPhaseProjectiveAtomFeature_apply_zero,
    ccmActualHeadMatchedPhaseProjectiveAtomFeature_apply_one,
    ccmActualHeadMatchedPhaseProjectiveAtomFeature_apply_two,
    ccmActualHeadMatchedPhaseRotatingProbe_apply_zero,
    ccmActualHeadMatchedPhaseRotatingProbe_apply_one,
    ccmActualHeadMatchedPhaseRotatingProbe_apply_two, RCLike.inner_apply,
    starRingEnd_apply, star_trivial]
  ring

theorem ccmActualHeadMatchedPhaseProjectiveFockKernel_atom_positiveProbe_re
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    (ccmActualHeadMatchedPhaseProjectiveFockKernel n xi
      (.atom i) (.positiveProbe i)).re =
      Real.exp ((ccmActualHeadMatchedOrientedPhaseSymbol (n i) xi).re) := by
  change ccmActualHeadMatchedPhaseProjectiveFockMatrix n xi
      (.atom i) (.positiveProbe i) = _
  simp [ccmActualHeadMatchedPhaseProjectiveFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseProjectiveFockIndex.feature,
    ccmActualHeadMatchedPhaseProjectiveAtom_inner_rotatingProbe]

theorem ccmActualHeadMatchedPhaseProjectiveFockKernel_atom_negativeProbe_re
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    (ccmActualHeadMatchedPhaseProjectiveFockKernel n xi
      (.atom i) (.negativeProbe i)).re =
      Real.exp (-((ccmActualHeadMatchedOrientedPhaseSymbol (n i) xi).re)) := by
  change ccmActualHeadMatchedPhaseProjectiveFockMatrix n xi
      (.atom i) (.negativeProbe i) = _
  simp [ccmActualHeadMatchedPhaseProjectiveFockMatrix,
    GaloisForLFunctions.HilbertMetric.hilbertExponentialInnerMatrix,
    CCMActualHeadMatchedPhaseProjectiveFockIndex.feature,
    ccmActualHeadMatchedPhaseProjectiveAtom_inner_rotatingProbe]

/-- Projective positive/negative probe ratio for one arithmetic atom. -/
def ccmActualHeadMatchedPhaseProjectiveFockRatio {ι : Type*}
    (n : ι → ℕ) (xi : ℝ) (i : ι) : ℝ :=
  (ccmActualHeadMatchedPhaseProjectiveFockKernel n xi
      (.atom i) (.positiveProbe i)).re /
    (ccmActualHeadMatchedPhaseProjectiveFockKernel n xi
      (.atom i) (.negativeProbe i)).re

theorem ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    ccmActualHeadMatchedPhaseProjectiveFockRatio n xi i =
      Real.exp (2 * (ccmActualHeadMatchedOrientedPhaseSymbol (n i) xi).re) := by
  rw [ccmActualHeadMatchedPhaseProjectiveFockRatio,
    ccmActualHeadMatchedPhaseProjectiveFockKernel_atom_positiveProbe_re,
    ccmActualHeadMatchedPhaseProjectiveFockKernel_atom_negativeProbe_re,
    ← Real.exp_sub]
  congr 1
  ring

/-- Exact single-atom projective/Busemann reporter. -/
theorem half_log_ccmActualHeadMatchedPhaseProjectiveFockRatio
    {ι : Type*} (n : ι → ℕ) (xi : ℝ) (i : ι) :
    (1 / 2 : ℝ) * Real.log
      (ccmActualHeadMatchedPhaseProjectiveFockRatio n xi i) =
      (ccmActualHeadMatchedOrientedPhaseSymbol (n i) xi).re := by
  rw [ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp, Real.log_exp]
  ring

def ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel (xi : ℝ) :
    CCMActualHeadMatchedPhaseProjectiveFockIndex ℕ →
      CCMActualHeadMatchedPhaseProjectiveFockIndex ℕ → ℂ :=
  ccmActualHeadMatchedPhaseProjectiveFockKernel id xi

theorem ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel_isPSDKernel (xi : ℝ) :
    GaloisForLFunctions.HTGeometry.IsPSDKernel
      (ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel xi) := by
  exact ccmActualHeadMatchedPhaseProjectiveFockKernel_isPSDKernel id xi

def ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio (xi : ℝ) (n : ℕ) : ℝ :=
  ccmActualHeadMatchedPhaseProjectiveFockRatio id xi n

theorem ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_pos
    (xi : ℝ) (n : ℕ) :
    0 < ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio xi n := by
  rw [ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio,
    ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp]
  positivity

/-- Multiplicative holonomy accumulated over a finite arithmetic packet. -/
def ccmActualHeadMatchedPhaseProjectiveFockHolonomy
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∏ n ∈ F, ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio xi n

theorem ccmActualHeadMatchedPhaseProjectiveFockHolonomy_pos
    (F : Finset ℕ) (xi : ℝ) :
    0 < ccmActualHeadMatchedPhaseProjectiveFockHolonomy F xi := by
  apply Finset.prod_pos
  intro n hn
  exact ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_pos xi n

/-- Finite CCM source addition is exactly logarithm of multiplicative projective holonomy. -/
theorem log_ccmActualHeadMatchedPhaseProjectiveFockHolonomy
    (F : Finset ℕ) (xi : ℝ) :
    Real.log (ccmActualHeadMatchedPhaseProjectiveFockHolonomy F xi) =
      2 * (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  rw [ccmActualHeadMatchedPhaseProjectiveFockHolonomy,
    Real.log_prod (fun n hn =>
      (ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_pos xi n).ne')]
  simp_rw [ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio,
    ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp, Real.log_exp]
  unfold ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [id_eq]

theorem half_log_ccmActualHeadMatchedPhaseProjectiveFockHolonomy
    (F : Finset ℕ) (xi : ℝ) :
    (1 / 2 : ℝ) *
        Real.log (ccmActualHeadMatchedPhaseProjectiveFockHolonomy F xi) =
      (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re := by
  rw [log_ccmActualHeadMatchedPhaseProjectiveFockHolonomy]
  ring

/-- Actual finite matched block as spectral integral of one multiplicative projective cocycle. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_projectiveFockHolonomy
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ((1 / 2 : ℝ) *
          Real.log (ccmActualHeadMatchedPhaseProjectiveFockHolonomy F xi)) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol]
  congr 2
  funext xi
  rw [half_log_ccmActualHeadMatchedPhaseProjectiveFockHolonomy]

end RHTower
