import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnSquarefreeFisherPhaseGaugeRiggingNoGo
import GaloisForLFunctions.RHTower.BesselBoundWitnesses

/-!
# Sharp Bessel-Hilbert stability wall for physical MSC overlap

For an arbitrary positive Hilbert geometry, require only that normalized
arithmetic modes reproduce the exact physical MSC source and literal overlap
columns. A finite Bessel bound forces both analysis columns into `ℓ²`; their
pointwise norm product is therefore in `ℓ¹`. Mode norms cancel exactly, and the
MSC product invariant identifies the result with squarefree-Möbius mass at
`Re rho`. Hence every stable realization lies in `Re rho > 1`.

The boundary is sharp. To the right of one, the balanced corpus weight gives an
explicit canonical `ℓ²` realization whose normalized modes are orthonormal.
Consequently, at every strict-right Xi zero any coefficient-faithful positive
Hilbert realization must violate every Bessel bound on a finite packet. This
kills all frame, Riesz-basis, bounded-synthesis, and Gram-Schur-stable
non-diagonal MSC completions; only singular non-Bessel geometry survives.
-/

open Complex Filter Set Topology
open scoped Topology InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact physical MSC source/overlap analysis columns in an arbitrary positive Hilbert geometry. -/
def IsMSCPhysicalOverlapHilbertRealization
    (rho : ℂ) (sigma : ℝ) (modes : ℕ → H) (source overlap : H) : Prop :=
  (∀ n, modes n ≠ 0) ∧
  (∀ n,
    inner ℂ (mscSignGaugeNormalizedMode modes n) source =
      star (RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (RHTower.mscPhysicalZeroCoordinate rho sigma) n) * (‖modes n‖ : ℂ)) ∧
  (∀ n,
    inner ℂ (mscSignGaugeNormalizedMode modes n) overlap =
      star (RHTower.infiniteMobiusSignedWeight sigma n) / (‖modes n‖ : ℂ))

/-- A stable realization is one whose normalized arithmetic modes have a finite Bessel bound. -/
def IsMSCPhysicalOverlapBesselHilbertRealization
    (rho : ℂ) (sigma : ℝ) (modes : ℕ → H) (source overlap : H) (B : ℝ) : Prop :=
  IsMSCPhysicalOverlapHilbertRealization rho sigma modes source overlap ∧
    GaloisForLFunctions.HasBesselBound (mscSignGaugeNormalizedMode modes) B

theorem summable_norm_inner_sq_of_hasBesselBound
    (u : ℕ → H) (B : ℝ) (hB : GaloisForLFunctions.HasBesselBound u B) (x : H) :
    Summable (fun n => ‖inner ℂ (u n) x‖ ^ 2) := by
  refine summable_of_sum_le (c := B * ‖x‖ ^ 2) (fun n => by positivity) fun s => ?_
  exact hB s x

/-- Bessel stability canonically produces the reciprocal diagonal MSC rigging. -/
theorem admitsMSCPhysicalOverlapDiagonalRigging_of_besselHilbertRealization
    (rho : ℂ) (sigma : ℝ)
    (modes : ℕ → H) (source overlap : H) (B : ℝ)
    (h : IsMSCPhysicalOverlapBesselHilbertRealization
      rho sigma modes source overlap B) :
    AdmitsMSCPhysicalOverlapDiagonalRigging rho sigma := by
  rcases h with ⟨⟨hne, hsource, hoverlap⟩, hB⟩
  have hs := summable_norm_inner_sq_of_hasBesselBound
    (mscSignGaugeNormalizedMode modes) B hB source
  have ho := summable_norm_inner_sq_of_hasBesselBound
    (mscSignGaugeNormalizedMode modes) B hB overlap
  refine ⟨fun n => ‖modes n‖ ^ 2,
    fun n => sq_pos_of_pos (norm_pos_iff.mpr (hne n)), ?_, ?_⟩
  · refine hs.congr (fun n => ?_)
    rw [hsource n, norm_mul, norm_star]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    ring
  · refine ho.congr (fun n => ?_)
    rw [hoverlap n, norm_div, norm_star]
    have hp : 0 < ‖modes n‖ := norm_pos_iff.mpr (hne n)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    field_simp [hp.ne']

theorem one_lt_re_of_besselHilbertRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (modes : ℕ → H) (source overlap : H) (B : ℝ)
    (h : IsMSCPhysicalOverlapBesselHilbertRealization
      rho sigma modes source overlap B) :
    1 < rho.re := by
  exact one_lt_re_of_admitsMSCPhysicalOverlapDiagonalRigging rho hsigma
    (admitsMSCPhysicalOverlapDiagonalRigging_of_besselHilbertRealization
      rho sigma modes source overlap B h)

/-- Sharp positive survivor: every exact strip realization has unbounded finite-packet analysis. -/
theorem exists_besselViolation_of_re_le_one
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : rho.re ≤ 1)
    (modes : ℕ → H) (source overlap : H)
    (h : IsMSCPhysicalOverlapHilbertRealization rho sigma modes source overlap)
    (B : ℝ) :
    ∃ s : Finset ℕ, ∃ x : H,
      B * ‖x‖ ^ 2 <
        ∑ n ∈ s, ‖inner ℂ (mscSignGaugeNormalizedMode modes n) x‖ ^ 2 := by
  have hnot : ¬ GaloisForLFunctions.HasBesselBound
      (mscSignGaugeNormalizedMode modes) B := by
    intro hB
    exact (not_lt_of_ge hrho)
      (one_lt_re_of_besselHilbertRealization rho hsigma modes source overlap B ⟨h, hB⟩)
  simp only [GaloisForLFunctions.HasBesselBound, not_forall] at hnot
  obtain ⟨s, x, hx⟩ := hnot
  exact ⟨s, x, lt_of_not_ge hx⟩

/-! ## Sharp canonical realization to the right of the wall -/

abbrev MSCPhysicalOverlapEllTwo := lp (fun _ : ℕ => ℂ) 2

def mscBesselCanonicalBasis (n : ℕ) : MSCPhysicalOverlapEllTwo :=
  lp.single 2 n 1

theorem norm_mscBesselCanonicalBasis (n : ℕ) :
    ‖mscBesselCanonicalBasis n‖ = 1 := by
  rw [mscBesselCanonicalBasis, lp.norm_single (by norm_num), norm_one]

theorem inner_mscBesselCanonicalBasis (n m : ℕ) :
    inner ℂ (mscBesselCanonicalBasis n) (mscBesselCanonicalBasis m) =
      if n = m then 1 else 0 := by
  by_cases h : n = m
  · subst m
    simp [mscBesselCanonicalBasis]
  · simp [mscBesselCanonicalBasis, lp.inner_single_left, h]

theorem orthonormal_mscBesselCanonicalBasis :
    Orthonormal ℂ mscBesselCanonicalBasis := by
  rw [orthonormal_iff_ite]
  exact inner_mscBesselCanonicalBasis

def mscBesselCanonicalMode (rho : ℂ) (sigma : ℝ) (n : ℕ) :
    MSCPhysicalOverlapEllTwo :=
  (Real.sqrt (mscBalancedDiagonalWeight rho sigma n) : ℂ) •
    mscBesselCanonicalBasis n

theorem norm_mscBesselCanonicalMode (rho : ℂ) (sigma : ℝ) (n : ℕ) :
    ‖mscBesselCanonicalMode rho sigma n‖ =
      Real.sqrt (mscBalancedDiagonalWeight rho sigma n) := by
  rw [mscBesselCanonicalMode, norm_smul, norm_mscBesselCanonicalBasis, mul_one]
  simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem mscBesselCanonicalMode_ne_zero (rho : ℂ) (sigma : ℝ) (n : ℕ) :
    mscBesselCanonicalMode rho sigma n ≠ 0 := by
  rw [← norm_pos_iff, norm_mscBesselCanonicalMode]
  exact Real.sqrt_pos.2 (mscBalancedDiagonalWeight_pos rho sigma n)

theorem mscSignGaugeNormalizedMode_mscBesselCanonicalMode
    (rho : ℂ) (sigma : ℝ) (n : ℕ) :
    mscSignGaugeNormalizedMode (mscBesselCanonicalMode rho sigma) n =
      mscBesselCanonicalBasis n := by
  have hsqrt : Real.sqrt (mscBalancedDiagonalWeight rho sigma n) ≠ 0 :=
    (Real.sqrt_pos.2 (mscBalancedDiagonalWeight_pos rho sigma n)).ne'
  rw [mscSignGaugeNormalizedMode, norm_mscBesselCanonicalMode,
    mscBesselCanonicalMode, smul_smul]
  have hsqrtC : (Real.sqrt (mscBalancedDiagonalWeight rho sigma n) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt
  rw [inv_mul_cancel₀ hsqrtC, one_smul]

def mscBesselCanonicalSourceCoeff (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℂ :=
  star (RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
    (RHTower.mscPhysicalZeroCoordinate rho sigma) n) *
      (Real.sqrt (mscBalancedDiagonalWeight rho sigma n) : ℂ)

def mscBesselCanonicalOverlapCoeff (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℂ :=
  star (RHTower.infiniteMobiusSignedWeight sigma n) /
    (Real.sqrt (mscBalancedDiagonalWeight rho sigma n) : ℂ)

theorem norm_sq_mscBesselCanonicalSourceCoeff
    (rho : ℂ) (sigma : ℝ) (n : ℕ) :
    ‖mscBesselCanonicalSourceCoeff rho sigma n‖ ^ 2 =
      mscBalancedDiagonalWeight rho sigma n *
        ‖RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
          (RHTower.mscPhysicalZeroCoordinate rho sigma) n‖ ^ 2 := by
  rw [mscBesselCanonicalSourceCoeff, norm_mul, norm_star,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (mscBalancedDiagonalWeight_pos rho sigma n).le]
  ring

theorem norm_sq_mscBesselCanonicalOverlapCoeff
    (rho : ℂ) (sigma : ℝ) (n : ℕ) :
    ‖mscBesselCanonicalOverlapCoeff rho sigma n‖ ^ 2 =
      (mscBalancedDiagonalWeight rho sigma n)⁻¹ *
        ‖RHTower.infiniteMobiusSignedWeight sigma n‖ ^ 2 := by
  have hw := mscBalancedDiagonalWeight_pos rho sigma n
  rw [mscBesselCanonicalOverlapCoeff, norm_div, norm_star,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hw.le]
  field_simp [hw.ne']

theorem summable_norm_sq_mscBesselCanonicalSourceCoeff
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) :
    Summable (fun n => ‖mscBesselCanonicalSourceCoeff rho sigma n‖ ^ 2) := by
  refine ((RHTower.summable_squarefreeMobiusMass hrho).div_const
    (RHTower.squarefreeMobiusTotal sigma)).congr (fun n => ?_)
  rw [norm_sq_mscBesselCanonicalSourceCoeff,
    mscBalancedDiagonalWeight_mul_physical_norm_sq rho hsigma n]

theorem summable_norm_sq_mscBesselCanonicalOverlapCoeff
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) :
    Summable (fun n => ‖mscBesselCanonicalOverlapCoeff rho sigma n‖ ^ 2) := by
  refine ((RHTower.summable_squarefreeMobiusMass hrho).div_const
    (RHTower.squarefreeMobiusTotal sigma)).congr (fun n => ?_)
  rw [norm_sq_mscBesselCanonicalOverlapCoeff,
    mscBalancedDiagonalWeight_inv_mul_base_norm_sq rho hsigma n]

private theorem memℓp_two_of_norm_sq_summable
    {f : ℕ → ℂ} (hf : Summable fun n => ‖f n‖ ^ 2) : Memℓp f 2 := by
  apply memℓp_gen
  refine hf.congr fun n => ?_
  rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) by simp,
    Real.rpow_natCast]

def mscBesselCanonicalSource
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) :
    MSCPhysicalOverlapEllTwo :=
  ⟨mscBesselCanonicalSourceCoeff rho sigma,
    memℓp_two_of_norm_sq_summable
      (summable_norm_sq_mscBesselCanonicalSourceCoeff rho hsigma hrho)⟩

def mscBesselCanonicalOverlap
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) :
    MSCPhysicalOverlapEllTwo :=
  ⟨mscBesselCanonicalOverlapCoeff rho sigma,
    memℓp_two_of_norm_sq_summable
      (summable_norm_sq_mscBesselCanonicalOverlapCoeff rho hsigma hrho)⟩

@[simp] theorem mscBesselCanonicalSource_apply
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) (n : ℕ) :
    mscBesselCanonicalSource rho hsigma hrho n =
      mscBesselCanonicalSourceCoeff rho sigma n := rfl

@[simp] theorem mscBesselCanonicalOverlap_apply
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) (n : ℕ) :
    mscBesselCanonicalOverlap rho hsigma hrho n =
      mscBesselCanonicalOverlapCoeff rho sigma n := rfl

theorem inner_mscBesselCanonicalBasis_left
    (n : ℕ) (x : MSCPhysicalOverlapEllTwo) :
    inner ℂ (mscBesselCanonicalBasis n) x = x n := by
  rw [mscBesselCanonicalBasis, lp.inner_single_left]
  simp

theorem isMSCPhysicalOverlapHilbertRealization_mscBesselCanonical
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) :
    IsMSCPhysicalOverlapHilbertRealization rho sigma
      (mscBesselCanonicalMode rho sigma)
      (mscBesselCanonicalSource rho hsigma hrho)
      (mscBesselCanonicalOverlap rho hsigma hrho) := by
  refine ⟨mscBesselCanonicalMode_ne_zero rho sigma, ?_, ?_⟩
  · intro n
    rw [mscSignGaugeNormalizedMode_mscBesselCanonicalMode,
      inner_mscBesselCanonicalBasis_left,
      mscBesselCanonicalSource_apply,
      mscBesselCanonicalSourceCoeff,
      norm_mscBesselCanonicalMode]
  · intro n
    rw [mscSignGaugeNormalizedMode_mscBesselCanonicalMode,
      inner_mscBesselCanonicalBasis_left,
      mscBesselCanonicalOverlap_apply,
      mscBesselCanonicalOverlapCoeff,
      norm_mscBesselCanonicalMode]

theorem hasBesselBound_mscBesselCanonicalMode_normalized
    (rho : ℂ) (sigma : ℝ) :
    GaloisForLFunctions.HasBesselBound
      (mscSignGaugeNormalizedMode (mscBesselCanonicalMode rho sigma)) 1 := by
  rw [show mscSignGaugeNormalizedMode (mscBesselCanonicalMode rho sigma) =
      mscBesselCanonicalBasis by
    funext n
    exact mscSignGaugeNormalizedMode_mscBesselCanonicalMode rho sigma n]
  exact GaloisForLFunctions.hasBesselBound_of_orthonormal
    orthonormal_mscBesselCanonicalBasis

theorem exists_mscPhysicalOverlapBesselHilbertRealization_of_one_lt_re
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 < rho.re) :
    ∃ (modes : ℕ → MSCPhysicalOverlapEllTwo)
        (source overlap : MSCPhysicalOverlapEllTwo) (B : ℝ),
      IsMSCPhysicalOverlapBesselHilbertRealization
        rho sigma modes source overlap B := by
  exact ⟨mscBesselCanonicalMode rho sigma,
    mscBesselCanonicalSource rho hsigma hrho,
    mscBesselCanonicalOverlap rho hsigma hrho, 1,
    isMSCPhysicalOverlapHilbertRealization_mscBesselCanonical rho hsigma hrho,
    hasBesselBound_mscBesselCanonicalMode_normalized rho sigma⟩

/-- Exact Bessel-Hilbert classification for the physical MSC source/overlap pair. -/
theorem exists_mscPhysicalOverlapBesselHilbertRealization_iff
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∃ (modes : ℕ → MSCPhysicalOverlapEllTwo)
        (source overlap : MSCPhysicalOverlapEllTwo) (B : ℝ),
      IsMSCPhysicalOverlapBesselHilbertRealization
        rho sigma modes source overlap B) ↔
      1 < rho.re := by
  constructor
  · rintro ⟨modes, source, overlap, B, h⟩
    exact one_lt_re_of_besselHilbertRealization
      rho hsigma modes source overlap B h
  · exact exists_mscPhysicalOverlapBesselHilbertRealization_of_one_lt_re
      rho hsigma

theorem not_exists_mscPhysicalOverlapBesselHilbertRealization_of_re_le_one
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : rho.re ≤ 1)
    (modes : ℕ → H) (source overlap : H) :
    ¬ ∃ B : ℝ, IsMSCPhysicalOverlapBesselHilbertRealization
      rho sigma modes source overlap B := by
  rintro ⟨B, h⟩
  exact (not_lt_of_ge hrho)
    (one_lt_re_of_besselHilbertRealization
      rho hsigma modes source overlap B h)

/-- At a strict-right Xi zero, the physical four-unit MSC germ coexists with a
universal stable-Hilbert no-go. Any exact positive Hilbert realization has
arbitrarily large finite-packet analysis amplification. -/
theorem strictRightXiZero_mscBesselHilbertStabilityWall
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : RHTower.xi rho = 0) {sigma : ℝ} (hsigma : 1 < sigma)
    (modes : ℕ → H) (source overlap : H) :
    (∃ k : ℕ, analyticOrderAt RHTower.xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        (∀ tau : ℝ, 1 < tau →
          AnalyticAt ℂ (RHTower.mscPhysicalRegularGerm rho g tau)
              (RHTower.mscPhysicalZeroCoordinate rho tau) ∧
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v /
                GaloisForLFunctions.squarefreeBoundaryOverlap
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v) =ᶠ[
              𝓝[≠] (RHTower.mscPhysicalZeroCoordinate rho tau)]
                fun v => 2 * ((k + 1 : ℕ) : ℂ) /
                  (v - RHTower.mscPhysicalZeroCoordinate rho tau) +
                    RHTower.mscPhysicalRegularGerm rho g tau v) ∧
          Tendsto
            (fun tau : ℝ =>
              Complex.normSq
                (RHTower.mscPhysicalRegularGerm rho g tau
                  (RHTower.mscPhysicalZeroCoordinate rho tau)))
            (nhdsWithin 1 (Set.Ioi 1)) (nhds 4)) ∧
      (¬ ∃ B : ℝ, IsMSCPhysicalOverlapBesselHilbertRealization
        rho sigma modes source overlap B) ∧
      (IsMSCPhysicalOverlapHilbertRealization
          rho sigma modes source overlap →
        ∀ B : ℝ, ∃ s : Finset ℕ, ∃ x : H,
          B * ‖x‖ ^ 2 <
            ∑ n ∈ s,
              ‖inner ℂ (mscSignGaugeNormalizedMode modes n) x‖ ^ 2) := by
  refine ⟨RHTower.exists_mscPhysicalRegularGerm_residueSplit_tendsto_four
      hhalf hone hzero,
    not_exists_mscPhysicalOverlapBesselHilbertRealization_of_re_le_one
      rho hsigma hone.le modes source overlap, ?_⟩
  intro h B
  exact exists_besselViolation_of_re_le_one
    rho hsigma hone.le modes source overlap h B

end RHTower.HedenmalmThetaSource
