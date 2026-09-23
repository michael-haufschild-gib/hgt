import GaloisForLFunctions.HTGeometry.FiniteGeometricCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureStrictDyadicLaw

/-!
# Cofinite Hilbert reconstruction for continuous Möbius dyadic innovations

At one prime, every dyadic innovation feature is a weighted geometric sequence in valuation
depth. The generic HTGeometry tail theorem therefore upgrades the existing first-`N` Vandermonde
sampler to exact reconstruction after every finite deletion of depth coordinates.

The resulting deletion-robust phase detects distinct nonzero mesh-scaled apertures. Adding the
positive-orientation chamber is exactly equivalent to strict positivity of the completed
all-prime innovation Gram.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Complex column weight of one prime's dyadic innovation depth feature. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight
    (h a : ℝ) (p : Nat.Primes) : ℂ :=
  ((xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) *
    (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ (2 : ℕ) : ℝ)

/-- Complex geometric node of one prime's dyadic innovation depth feature. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode
    (h a : ℝ) (p : Nat.Primes) : ℂ :=
  (xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ (2 : ℕ) : ℝ)

/-- Complexification of one prime's real dyadic innovation feature packet. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature
    {ι : Type*} (h : ℝ) (aperture : ι → ℝ) (p : Nat.Primes) :
    ι → ℕ → ℂ :=
  fun j e => xiMobiusPrimeContinuousApertureDyadicInnovationFeature
    h (aperture j) p e

/-- The complex dyadic depth family is literally a finite weighted geometric family. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature_eq_geometric
    {ι : Type*} (h : ℝ) (aperture : ι → ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature h aperture p =
      finiteWeightedGeometricFamily
        (fun j => xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight
          h (aperture j) p)
        (fun j => xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode
          h (aperture j) p) := by
  funext j e
  simp [xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight,
    xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode,
    finiteWeightedGeometricFamily,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature]

/-- Dyadic depth nodes never vanish, for any real mesh or aperture. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode_ne_zero
    (h a : ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode h a p ≠ 0 := by
  rw [xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode]
  exact Complex.ofReal_ne_zero.mpr (sq_pos_of_pos
    (xiMobiusContinuousApertureDiskNode_pos ((h / 2) * a) p)).ne'

/-- A dyadic depth column weight vanishes exactly on the mesh-scaled zero aperture. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight_ne_zero_iff
    (h a : ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight h a p ≠ 0 ↔
      h * a ≠ 0 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  have hq : q / (1 + q) ≠ 0 := by
    exact div_ne_zero (xiTransversePrimeApertureDiskNode_pos 1 p).ne'
      (by
        have hqpos := xiTransversePrimeApertureDiskNode_pos 1 p
        linarith)
  constructor
  · intro hweight hzero
    have hhalf : (h / 2) * a = 0 := by linarith
    apply hweight
    simp [xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight,
      hhalf, xiMobiusContinuousApertureDiskNode]
  · intro hha
    apply Complex.ofReal_ne_zero.mpr
    apply mul_ne_zero hq
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro hr
    apply hha
    have hhalf : (h / 2) * a = 0 := by
      apply xiMobiusContinuousApertureDiskNode_injective p
      simpa [r, xiMobiusContinuousApertureDiskNode] using hr.symm
    linarith

/-- Dyadic geometric nodes are distinct exactly when the mesh-scaled apertures are distinct. -/
theorem
    xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode_injective_iff_scaled_injective
    {ι : Type*} (h : ℝ) (aperture : ι → ℝ) (p : Nat.Primes) :
    Function.Injective (fun j =>
      xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode
        h (aperture j) p) ↔
      Function.Injective (fun j => h * aperture j) := by
  constructor
  · intro hnode i j hij
    apply hnode
    change
      xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode h (aperture i) p =
        xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode h (aperture j) p
    have hhalf :
        (h / 2) * aperture i = (h / 2) * aperture j := by
      change h * aperture i = h * aperture j at hij
      linarith
    simp only [xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode]
    rw [hhalf]
  · intro hscaled i j hij
    apply hscaled
    have hsquare :
        xiMobiusContinuousApertureDiskNode ((h / 2) * aperture i) p ^ (2 : ℕ) =
          xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p ^ (2 : ℕ) := by
      apply Complex.ofReal_injective
      simpa [xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode] using hij
    have hi := xiMobiusContinuousApertureDiskNode_pos
      ((h / 2) * aperture i) p
    have hj := xiMobiusContinuousApertureDiskNode_pos
      ((h / 2) * aperture j) p
    have hnode :
        xiMobiusContinuousApertureDiskNode ((h / 2) * aperture i) p =
          xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p := by
      nlinarith
    have hhalf := xiMobiusContinuousApertureDiskNode_injective p hnode
    change h * aperture i = h * aperture j
    linarith

/-- **Exact dyadic tail classification.** One prime's innovation depth columns remain independent
after every finite depth deletion exactly off the scaled collision and zero strata. -/
theorem
    tailCoefficientIndependent_xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ℝ) (aperture : ι → ℝ) (p : Nat.Primes) :
    TailCoefficientIndependent
        (xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature h aperture p) ↔
      Function.Injective (fun j => h * aperture j) ∧
        ∀ j, h * aperture j ≠ 0 := by
  rw [xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature_eq_geometric,
    tailCoefficientIndependent_finiteWeightedGeometricFamily_iff,
    xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode_injective_iff_scaled_injective]
  constructor
  · rintro ⟨hinjective, hweight, _hnode⟩
    exact ⟨hinjective, fun j =>
      (xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight_ne_zero_iff
        h (aperture j) p).mp (hweight j)⟩
  · rintro ⟨hinjective, hne⟩
    exact ⟨hinjective,
      fun j =>
        (xiMobiusPrimeContinuousApertureDyadicInnovationDepthWeight_ne_zero_iff
          h (aperture j) p).mpr (hne j),
      fun j => xiMobiusPrimeContinuousApertureDyadicInnovationDepthNode_ne_zero
        h (aperture j) p⟩

/-- Complete exact recovery from one prime's dyadic depth features after every finite deletion. -/
def XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ℝ) (aperture : ι → ℝ) (p : Nat.Primes) : Prop :=
  CofiniteEvaluationHilbertReconstruction
    (xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature h aperture p)

/-- **Deletion-robust dyadic recovery classification.** Cofinite exact Hilbert reconstruction at
one prime detects exactly distinct nonzero mesh-scaled apertures. -/
theorem
    xiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction_iff_scaled_injective_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ℝ) (aperture : ι → ℝ) (p : Nat.Primes) :
    XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        h aperture p ↔
      Function.Injective (fun j => h * aperture j) ∧
        ∀ j, h * aperture j ≠ 0 := by
  rw [XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction,
    cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent,
    tailCoefficientIndependent_xiMobiusPrimeContinuousApertureDyadicInnovationComplexFeature_iff]

/-- Cofinite dyadic-depth recovery is exactly canonical finite continuous-aperture recovery for
the mesh-scaled packet. -/
theorem
    xiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction_iff_scaledCanonicalReconstruction
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        h aperture p ↔
      XiMobiusPrimeContinuousApertureCanonicalReconstruction
        (fun j => h * aperture j) p := by
  rw [
    xiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction_iff_scaled_injective_ne_zero,
    xiMobiusPrimeContinuousApertureCanonicalReconstruction_iff_injective_ne_zero]

/-- **Cofinite-recovery/strict-innovation phase.** The completed all-prime dyadic innovation is
strict exactly when one prime supports deletion-robust depth recovery and all scaled apertures
have positive orientation. -/
theorem
    xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_primeCofiniteHilbertReconstruction_and_scaled_pos
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusContinuousApertureDyadicInnovationGram h aperture).PosDef ↔
      XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        h aperture p ∧
        ∀ j, 0 < h * aperture j := by
  rw [xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_scaled_injective_pos,
    xiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction_iff_scaled_injective_ne_zero]
  constructor
  · rintro ⟨hinjective, hpos⟩
    exact ⟨⟨hinjective, fun j => (hpos j).ne'⟩, hpos⟩
  · rintro ⟨⟨hinjective, _hne⟩, hpos⟩
    exact ⟨hinjective, hpos⟩

/-! ### Root-deleted integral aperture -/

/-- Cofinite dyadic-depth recovery after deleting one distinguished integral aperture. -/
def XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (p : Nat.Primes) : Prop :=
  XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
    2 (fun v : {v : Fin N // v ≠ root} => (shift v : ℝ)) p

/-- **Root-deleted dyadic recovery classification.** When the deleted aperture is labeled zero,
cofinite recovery from every tail of the remaining dyadic-depth features detects exactly
injectivity of the complete integral packet. The retained nonvanishing condition is discharged by
separation from the zero root. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      Function.Injective shift := by
  rw [
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction,
    xiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction_iff_scaled_injective_ne_zero]
  constructor
  · rintro ⟨hinjective, hnonzero⟩ x y hxy
    by_cases hx : x = root
    · subst x
      by_contra hy
      have hzero : (2 : ℝ) * (shift (⟨y, Ne.symm hy⟩ :
          {v : Fin N // v ≠ root}) : ℝ) = 0 := by
        norm_num
        exact_mod_cast hxy.symm.trans hroot
      exact hnonzero ⟨y, Ne.symm hy⟩ hzero
    · by_cases hy : y = root
      · subst y
        have hzero : (2 : ℝ) * (shift (⟨x, hx⟩ :
            {v : Fin N // v ≠ root}) : ℝ) = 0 := by
          norm_num
          exact_mod_cast hxy.trans hroot
        exact False.elim (hnonzero ⟨x, hx⟩ hzero)
      · have hsub :
            (⟨x, hx⟩ : {v : Fin N // v ≠ root}) =
              ⟨y, hy⟩ := by
          apply hinjective
          norm_num
          exact_mod_cast hxy
        exact congrArg Subtype.val hsub
  · intro hinjective
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hinjective
      have hcast : (shift x : ℝ) = shift y := by
        norm_num at hxy ⊢
        linarith
      exact_mod_cast hcast
    · intro v hv
      have hcast : (shift v : ℝ) = 0 := by
        norm_num at hv ⊢
        linarith
      have hzero : shift v = 0 := by
        exact_mod_cast hcast
      exact v.property (hinjective (hzero.trans hroot.symm))

end

end RHTower
