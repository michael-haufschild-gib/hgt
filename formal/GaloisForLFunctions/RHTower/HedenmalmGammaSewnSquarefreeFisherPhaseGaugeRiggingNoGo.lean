import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherDiagonalRiggingNoGo
import GaloisForLFunctions.HTGeometry.OrthonormalNormalize

/-!
# Phase-gauge rigidity of physical MSC Hilbert realizations

A nominally non-diagonal positive Hilbert completion of the physical MSC source
cannot preserve independent coefficient gauges.  If every arithmetic mode has a
unitary sign gauge which negates that mode and fixes all others, then distinct
modes are orthogonal.  Normalizing them and applying Bessel to the physical
source and literal overlap vector produces the reciprocal diagonal weight

`w n = ‖mode n‖²`.

The existing exact diagonal-rigging classification therefore forces
`1 < rho.re`.  At every strict-right Xi zero this is impossible.  Thus the
non-diagonal MSC survivor must break independent coefficient-gauge unitarity or
leave the positive Hilbert category altogether; off-diagonal Gram entries alone
cannot evade the absolute-product wall.

The abstract sign-gauge orthogonality step is classical.  The new content is its
coefficient-faithful application to the exact physical MSC source/overlap pair
and the resulting reduction of every phase-gauge Hilbert realization to the
sharp squarefree-Mobius diagonal wall.
-/

open Complex Filter Set Topology
open scoped Topology

noncomputable section

namespace RHTower.HedenmalmThetaSource

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Unit normalization of an abstract arithmetic mode. -/
def mscSignGaugeNormalizedMode (modes : ℕ → H) (n : ℕ) : H :=
  ((‖modes n‖ : ℂ))⁻¹ • modes n

/-- A coefficient-faithful positive Hilbert realization of the physical MSC
source and its literal overlap covector, equipped with every independent mode
sign gauge.  No orthogonality, diagonal Gram law, basis completeness, or Riesz
bound is assumed. -/
def IsMSCPhysicalOverlapSignGaugeHilbertRealization
    (rho : ℂ) (sigma : ℝ) (modes : ℕ → H) (source overlap : H) : Prop :=
  (∀ n, modes n ≠ 0) ∧
  (∀ n, ∃ U : H ≃ₗᵢ[ℂ] H,
    U (modes n) = -modes n ∧
      ∀ m, m ≠ n → U (modes m) = modes m) ∧
  (∀ n,
    inner ℂ (mscSignGaugeNormalizedMode modes n) source =
      star (RHTower.infiniteMobiusCriticalComplexDampedSignedWeight sigma
        (RHTower.mscPhysicalZeroCoordinate rho sigma) n) * (‖modes n‖ : ℂ)) ∧
  (∀ n,
    inner ℂ (mscSignGaugeNormalizedMode modes n) overlap =
      star (RHTower.infiniteMobiusSignedWeight sigma n) / (‖modes n‖ : ℂ))

/-- Independent unitary sign gauges force all off-diagonal mode Gram entries to
vanish. -/
theorem pairwise_orthogonal_of_signGauge
    (modes : ℕ → H)
    (hgauge : ∀ n, ∃ U : H ≃ₗᵢ[ℂ] H,
      U (modes n) = -modes n ∧
        ∀ m, m ≠ n → U (modes m) = modes m) :
    ∀ i j, i ≠ j → inner ℂ (modes i) (modes j) = 0 := by
  intro i j hij
  obtain ⟨U, hi, hfix⟩ := hgauge i
  have hinner := U.inner_map_map (modes i) (modes j)
  rw [hi, hfix j hij.symm] at hinner
  simp only [inner_neg_left] at hinner
  have hadd : inner ℂ (modes i) (modes j) +
      inner ℂ (modes i) (modes j) = 0 :=
    eq_neg_iff_add_eq_zero.mp hinner.symm
  have htwo : (2 : ℂ) * inner ℂ (modes i) (modes j) = 0 := by
    simpa [two_mul] using hadd
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- **Phase-gauge collapse theorem.**  Any coefficient-faithful sign-gauge
Hilbert realization canonically supplies the reciprocal positive diagonal
rigging with weight `n ↦ ‖mode n‖²`. -/
theorem admitsMSCPhysicalOverlapDiagonalRigging_of_signGaugeHilbertRealization
    (rho : ℂ) (sigma : ℝ)
    (modes : ℕ → H) (source overlap : H)
    (h : IsMSCPhysicalOverlapSignGaugeHilbertRealization
      rho sigma modes source overlap) :
    AdmitsMSCPhysicalOverlapDiagonalRigging rho sigma := by
  rcases h with ⟨hne, hgauge, hsource, hoverlap⟩
  have horth := pairwise_orthogonal_of_signGauge modes hgauge
  have hon : Orthonormal ℂ (mscSignGaugeNormalizedMode modes) := by
    exact RHTower.orthonormal_normalize hne horth
  refine ⟨fun n => ‖modes n‖ ^ 2,
    fun n => sq_pos_of_pos (norm_pos_iff.mpr (hne n)), ?_, ?_⟩
  · have hs := hon.inner_products_summable source
    refine hs.congr (fun n => ?_)
    rw [hsource n, norm_mul, norm_star]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    ring
  · have hs := hon.inner_products_summable overlap
    refine hs.congr (fun n => ?_)
    rw [hoverlap n, norm_div, norm_star]
    have hp : 0 < ‖modes n‖ := norm_pos_iff.mpr (hne n)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    field_simp [hp.ne']

/-- Every phase-gauge Hilbert realization lies strictly right of the absolute
convergence wall. -/
theorem one_lt_re_of_signGaugeHilbertRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (modes : ℕ → H) (source overlap : H)
    (h : IsMSCPhysicalOverlapSignGaugeHilbertRealization
      rho sigma modes source overlap) :
    1 < rho.re := by
  exact one_lt_re_of_admitsMSCPhysicalOverlapDiagonalRigging rho hsigma
    (admitsMSCPhysicalOverlapDiagonalRigging_of_signGaugeHilbertRealization
      rho sigma modes source overlap h)

theorem not_isMSCPhysicalOverlapSignGaugeHilbertRealization_of_re_le_one
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : rho.re ≤ 1)
    (modes : ℕ → H) (source overlap : H) :
    ¬ IsMSCPhysicalOverlapSignGaugeHilbertRealization
      rho sigma modes source overlap := by
  intro h
  exact (not_lt_of_ge hrho)
    (one_lt_re_of_signGaugeHilbertRealization
      rho hsigma modes source overlap h)

/-- At an actual strict-right Xi zero, the physical residue-split MSC germ and
its four-unit regular energy coexist with no coefficient-faithful positive
Hilbert realization preserving every independent arithmetic-mode sign gauge. -/
theorem strictRightXiZero_mscPhysicalOverlapSignGaugeHilbertNoGo
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
      ¬ IsMSCPhysicalOverlapSignGaugeHilbertRealization
        rho sigma modes source overlap := by
  exact ⟨RHTower.exists_mscPhysicalRegularGerm_residueSplit_tendsto_four
      hhalf hone hzero,
    not_isMSCPhysicalOverlapSignGaugeHilbertRealization_of_re_le_one
      rho hsigma hone.le modes source overlap⟩

end RHTower.HedenmalmThetaSource
