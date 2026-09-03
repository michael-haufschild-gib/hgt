import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceCayleySeam
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRegionKappaOne

/-!
# Unconditional arithmetic half-germ continuation across high Euler bands

The classical de la Vallée Poussin zero-free region gives more than pointwise local passage across
`Re s = 1`.  In every sufficiently high horizontal band of height one, a fixed-width convex strip
crossing that line is zero-free.  The pole-cleared first-trace field therefore has an analytic
square root on the whole band, uniquely oriented to agree with the fixed prime-zeta half-germ on
the Euler-side overlap.

This is an unconditional continuation beyond the Dirichlet-series chamber, but its width shrinks
like `1 / log |Im s|`; it does not fill the target half-plane.
-/

open Complex Filter Set Topology

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-- Left edge used in a height-one zero-free band. -/
def firstTraceZeroFreeBandLeftEdge (Y : ℝ) : ℝ :=
  1 - (1 / 10000 : ℝ) / Real.log (Y + 1)

/-- Convex height-one band crossing the Euler line inside the classical zero-free region. -/
def firstTraceZeroFreeBand (Y : ℝ) : Set ℂ :=
  {s : ℂ | firstTraceZeroFreeBandLeftEdge Y < s.re ∧ Y < s.im ∧ s.im < Y + 1}

theorem firstTraceZeroFreeBand_eq_inter (Y : ℝ) :
    firstTraceZeroFreeBand Y =
      {s : ℂ | firstTraceZeroFreeBandLeftEdge Y < s.re} ∩
        ({s : ℂ | Y < s.im} ∩ {s : ℂ | s.im < Y + 1}) := by
  ext s
  simp [firstTraceZeroFreeBand]

theorem isOpen_firstTraceZeroFreeBand (Y : ℝ) :
    IsOpen (firstTraceZeroFreeBand Y) := by
  rw [firstTraceZeroFreeBand_eq_inter]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

theorem convex_firstTraceZeroFreeBand (Y : ℝ) :
    Convex ℝ (firstTraceZeroFreeBand Y) := by
  rw [firstTraceZeroFreeBand_eq_inter]
  exact (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))

/-- A canonical Euler-side point in every height-one band. -/
def firstTraceZeroFreeBandAnchor (Y : ℝ) : ℂ :=
  2 + ((Y + 1 / 2 : ℝ) : ℂ) * I

theorem firstTraceZeroFreeBandAnchor_mem {Y : ℝ} (hY : 3 ≤ Y) :
    firstTraceZeroFreeBandAnchor Y ∈ firstTraceZeroFreeBand Y := by
  have hlog : 0 < Real.log (Y + 1) := Real.log_pos (by linarith)
  have hedge : firstTraceZeroFreeBandLeftEdge Y < 2 := by
    dsimp [firstTraceZeroFreeBandLeftEdge]
    have : 0 < (1 / 10000 : ℝ) / Real.log (Y + 1) := div_pos (by norm_num) hlog
    linarith
  rw [firstTraceZeroFreeBand]
  constructor
  · simpa [firstTraceZeroFreeBandAnchor] using hedge
  · constructor <;> norm_num [firstTraceZeroFreeBandAnchor]

theorem firstTraceZeroFreeBandAnchor_mem_farHalf (Y : ℝ) :
    firstTraceZeroFreeBandAnchor Y ∈ farHalf := by
  rw [mem_farHalf]
  norm_num [firstTraceZeroFreeBandAnchor]

theorem firstTraceZeroFreeBand_subset_rightHalf {Y : ℝ} (hY : 3 ≤ Y) :
    firstTraceZeroFreeBand Y ⊆ rightHalf := by
  intro s hs
  have hY1pos : 0 < Y + 1 := by linarith
  have h2Y : (2 : ℝ) ≤ Y + 1 := by linarith
  have hlogmono : Real.log 2 ≤ Real.log (Y + 1) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hY1pos h2Y
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog : (1 / 2 : ℝ) < Real.log (Y + 1) := hlog2.trans_le hlogmono
  have hquot : (1 / 10000 : ℝ) / Real.log (Y + 1) < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith : 0 < Real.log (Y + 1))]
    nlinarith
  rw [mem_rightHalf]
  rw [firstTraceZeroFreeBand] at hs
  dsimp [firstTraceZeroFreeBandLeftEdge] at hs
  linarith

theorem poleClearedFirstTraceExponentialContinuation_ne_zero_on_band
    {T Y : ℝ} (hT : 3 ≤ T)
    (hzf : ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hY : T ≤ Y) {s : ℂ} (hs : s ∈ firstTraceZeroFreeBand Y) :
    poleClearedFirstTraceExponentialContinuation s ≠ 0 := by
  have hY3 : 3 ≤ Y := hT.trans hY
  have hsright := firstTraceZeroFreeBand_subset_rightHalf hY3 hs
  by_cases hre : 1 ≤ s.re
  · exact poleClearedFirstTraceExponentialContinuation_ne_zero_of_one_le_re hre
  · have hrelt : s.re < 1 := lt_of_not_ge hre
    have himY : Y < s.im := hs.2.1
    have himpos : 0 < s.im := by linarith
    have habsim : |s.im| = s.im := abs_of_pos himpos
    have hheight : T ≤ |s.im| := by rw [habsim]; linarith
    have hlogim : 0 < Real.log |s.im| := Real.log_pos (by rw [habsim]; linarith)
    have hlogY : 0 < Real.log (Y + 1) := Real.log_pos (by linarith)
    have hloglt : Real.log |s.im| < Real.log (Y + 1) := by
      apply Real.log_lt_log
      · rw [habsim]
        linarith
      · rw [habsim]
        exact hs.2.2
    have hdiv : (1 / 10000 : ℝ) / Real.log (Y + 1) <
        (1 / 10000 : ℝ) / Real.log |s.im| :=
      div_lt_div_of_pos_left (by norm_num) hlogim hloglt
    have hwidth : 1 - 1 / 10000 / Real.log |s.im| < s.re := by
      rw [firstTraceZeroFreeBand] at hs
      dsimp [firstTraceZeroFreeBandLeftEdge] at hs
      linarith [hs.1]
    have hzeta : riemannZeta s ≠ 0 := by
      have hz := hzf s.re s.im hheight (le_of_lt hrelt) hwidth
      simpa [Complex.ext_iff] using hz
    have hxi : xi s ≠ 0 := by
      intro hxi
      have hspos : 0 < s.re := by linarith [mem_rightHalf.mp hsright]
      have hs1 : s ≠ 1 := by
        intro h
        subst s
        norm_num at himpos
      rw [xi_eq_zero_iff hspos hs1] at hxi
      exact hzeta hxi
    exact poleClearedFirstTraceExponentialContinuation_ne_zero_of_xi_ne_zero hsright hxi

/-- Above one absolute threshold, every height-one band has an analytic square root of the
pole-cleared field which agrees with the fixed arithmetic Euler half-germ on the overlap. -/
theorem exists_poleClearedFirstTrace_zeroFreeBand_arithmetic_extensions :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g (firstTraceZeroFreeBand Y) ∧
          (∀ s ∈ firstTraceZeroFreeBand Y,
            g s ^ 2 = poleClearedFirstTraceExponentialContinuation s) ∧
          EqOn g poleClearedPrimeZetaHalfEulerGerm
            (firstTraceZeroFreeBand Y ∩ farHalf) := by
  obtain ⟨T, hT, hzf⟩ := Sieve.exists_zero_free_region_explicit
  refine ⟨T, hT, fun Y hY => ?_⟩
  have hY3 : 3 ≤ Y := hT.trans hY
  have hbandOpen := isOpen_firstTraceZeroFreeBand Y
  have hbandConvex := convex_firstTraceZeroFreeBand Y
  have hanchorBand := firstTraceZeroFreeBandAnchor_mem hY3
  have hbandRight := firstTraceZeroFreeBand_subset_rightHalf hY3
  obtain ⟨g, hg, hgsq⟩ := Bottcher.exists_analyticOnNhd_pow_eq
    (isSimplyConnected_of_convex hbandConvex ⟨_, hanchorBand⟩) hbandOpen
    (analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf.mono hbandRight)
    (fun s hs => poleClearedFirstTraceExponentialContinuation_ne_zero_on_band
      hT hzf hY hs) (N := 2) (by norm_num)
  have hanchorFar := firstTraceZeroFreeBandAnchor_mem_farHalf Y
  have hsquares :
      g (firstTraceZeroFreeBandAnchor Y) ^ 2 =
        poleClearedPrimeZetaHalfEulerGerm (firstTraceZeroFreeBandAnchor Y) ^ 2 := by
    rw [hgsq _ hanchorBand, poleClearedPrimeZetaHalfEulerGerm_sq hanchorFar]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hmatch | hmatch
  · refine ⟨g, hg, hgsq, ?_⟩
    exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
      (hbandConvex.inter convex_farHalf).isPreconnected
      (hg.continuousOn.mono inter_subset_left)
      (analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn.mono
        inter_subset_right)
      (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
      (fun s hs => by rw [hgsq s hs.1, poleClearedPrimeZetaHalfEulerGerm_sq hs.2])
      ⟨hanchorBand, hanchorFar⟩ hmatch
  · refine ⟨fun s => -g s, hg.neg, ?_, ?_⟩
    · intro s hs
      rw [neg_sq, hgsq s hs]
    · have hanchor : -g (firstTraceZeroFreeBandAnchor Y) =
          poleClearedPrimeZetaHalfEulerGerm (firstTraceZeroFreeBandAnchor Y) := by
        rw [hmatch]
        ring
      exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
        (hbandConvex.inter convex_farHalf).isPreconnected
        ((hg.neg).continuousOn.mono inter_subset_left)
        (analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn.mono
          inter_subset_right)
        (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
        (fun s hs => by rw [neg_sq, hgsq s hs.1,
          poleClearedPrimeZetaHalfEulerGerm_sq hs.2])
        ⟨hanchorBand, hanchorFar⟩ hanchor

end

end RHTower
