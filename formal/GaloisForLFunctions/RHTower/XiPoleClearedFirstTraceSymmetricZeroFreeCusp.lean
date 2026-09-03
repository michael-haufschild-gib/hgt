import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceZeroFreeCusp

/-!
# A symmetric two-ended zero-free cusp for the arithmetic half-germ

The classical zero-free cusp has a lower-half-plane reflection.  Both cusps meet the Euler
half-plane, which supplies a common arithmetic normalization.  Two-chart gluing therefore gives
one analytic square root on the Euler chamber together with both high-imaginary cusps.

The resulting domain is connected and invariant under complex conjugation, but its two cusp
boundaries still retreat to `Re s = 1`.  This is an unconditional enlargement of the arithmetic
continuation domain, not a square root on the full strict right half-plane.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Lower zero-free cusp, defined as the conjugate reflection of the upper cusp. -/
def firstTraceZeroFreeLowerCusp (T : ℝ) : Set ℂ :=
  {s : ℂ | (starRingEnd ℂ) s ∈ firstTraceZeroFreeCusp T}

/-- Euler chamber joined to both classical zero-free cusps. -/
def firstTraceSymmetricZeroFreeCusp (T : ℝ) : Set ℂ :=
  (firstTraceZeroFreeCusp T ∪ farHalf) ∪ firstTraceZeroFreeLowerCusp T

theorem firstTraceZeroFreeLowerCusp_eq {T : ℝ} :
    firstTraceZeroFreeLowerCusp T =
      {s : ℂ | s.im < -T ∧ firstTraceZeroFreeCuspBoundary T (-s.im) < s.re} := by
  ext s
  simp only [firstTraceZeroFreeLowerCusp, firstTraceZeroFreeCusp, mem_setOf_eq,
    Complex.conj_im, Complex.conj_re]
  constructor
  · rintro ⟨him, hre⟩
    exact ⟨by linarith, hre⟩
  · rintro ⟨him, hre⟩
    exact ⟨by linarith, hre⟩

theorem isOpen_firstTraceZeroFreeLowerCusp {T : ℝ} (hT : 4 ≤ T) :
    IsOpen (firstTraceZeroFreeLowerCusp T) := by
  change IsOpen ((starRingEnd ℂ) ⁻¹' firstTraceZeroFreeCusp T)
  exact (isOpen_firstTraceZeroFreeCusp hT).preimage Complex.continuous_conj

theorem isSimplyConnected_firstTraceZeroFreeLowerCusp {T : ℝ} (hT : 4 ≤ T) :
    IsSimplyConnected (firstTraceZeroFreeLowerCusp T) := by
  have himage :
      (starRingEnd ℂ) '' firstTraceZeroFreeCusp T = firstTraceZeroFreeLowerCusp T := by
    ext s
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [firstTraceZeroFreeLowerCusp] using hz
    · intro hs
      refine ⟨(starRingEnd ℂ) s, ?_, by simp⟩
      simpa [firstTraceZeroFreeLowerCusp] using hs
  rw [← himage]
  change IsSimplyConnected
    (Complex.conjCLE.toHomeomorph '' firstTraceZeroFreeCusp T)
  rw [Complex.conjCLE.toHomeomorph.isEmbedding.isSimplyConnected_image]
  exact isSimplyConnected_firstTraceZeroFreeCusp hT

theorem firstTraceZeroFreeLowerCusp_subset_rightHalf {T : ℝ} (hT : 4 ≤ T) :
    firstTraceZeroFreeLowerCusp T ⊆ rightHalf := by
  intro s hs
  have hu : (starRingEnd ℂ) s ∈ firstTraceZeroFreeCusp T := hs
  have hr := firstTraceZeroFreeCusp_subset_rightHalf hT hu
  rw [mem_rightHalf] at hr ⊢
  simpa using hr

theorem firstTraceZeroFreeLowerCusp_inter_farHalf_eq {T : ℝ} (hT : 4 ≤ T) :
    firstTraceZeroFreeLowerCusp T ∩ farHalf = {s : ℂ | s.im < -T ∧ 1 < s.re} := by
  ext s
  constructor
  · rintro ⟨hs, hfar⟩
    have hconjFar : (starRingEnd ℂ) s ∈ farHalf := by
      rw [mem_farHalf] at hfar ⊢
      simpa using hfar
    have hboth : (starRingEnd ℂ) s ∈ firstTraceZeroFreeCusp T ∩ farHalf :=
      ⟨hs, hconjFar⟩
    rw [firstTraceZeroFreeCusp_inter_farHalf_eq hT] at hboth
    have himc : ((starRingEnd ℂ) s).im = -s.im := by simp
    exact ⟨by linarith [hboth.1], by simpa using hboth.2⟩
  · rintro ⟨him, hre⟩
    have hconjBoth :
        (starRingEnd ℂ) s ∈ firstTraceZeroFreeCusp T ∩ farHalf := by
      rw [firstTraceZeroFreeCusp_inter_farHalf_eq hT]
      have himc : ((starRingEnd ℂ) s).im = -s.im := by simp
      exact ⟨by linarith [him], by simpa using hre⟩
    exact ⟨hconjBoth.1, by rw [mem_farHalf]; exact hre⟩

theorem convex_firstTraceZeroFreeLowerCusp_inter_farHalf {T : ℝ} (hT : 4 ≤ T) :
    Convex ℝ (firstTraceZeroFreeLowerCusp T ∩ farHalf) := by
  rw [firstTraceZeroFreeLowerCusp_inter_farHalf_eq hT]
  exact (convex_halfSpace_im_lt (-T)).inter (convex_halfSpace_re_gt 1)

theorem firstTraceZeroFreeCusp_disjoint_lowerCusp {T : ℝ} (hT : 0 ≤ T) :
    Disjoint (firstTraceZeroFreeCusp T) (firstTraceZeroFreeLowerCusp T) := by
  rw [Set.disjoint_left]
  intro s hu hl
  have himUpper : T < s.im := hu.1
  have hlc : s.im < -T := by
    rw [firstTraceZeroFreeLowerCusp_eq] at hl
    exact hl.1
  linarith

theorem firstTraceZeroFreeCusp_mono_height {T T' : ℝ} (hTT' : T ≤ T') :
    firstTraceZeroFreeCusp T' ⊆ firstTraceZeroFreeCusp T := by
  intro s hs
  have himT : T < s.im := hTT'.trans_lt hs.1
  have hmax : max T s.im = s.im := max_eq_right (le_of_lt himT)
  have hmax' : max T' s.im = s.im := max_eq_right (le_of_lt hs.1)
  refine ⟨himT, ?_⟩
  simpa [firstTraceZeroFreeCuspBoundary, hmax, hmax'] using hs.2

theorem poleClearedFirstTraceExponentialContinuation_ne_zero_on_lowerCusp
    {T₀ T : ℝ} (_hT₀ : 3 ≤ T₀)
    (hzf : ∀ β γ : ℝ, T₀ ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hT₀T : T₀ ≤ T) (hT : 4 ≤ T) {s : ℂ}
    (hs : s ∈ firstTraceZeroFreeLowerCusp T) :
    poleClearedFirstTraceExponentialContinuation s ≠ 0 := by
  have hsright := firstTraceZeroFreeLowerCusp_subset_rightHalf hT hs
  by_cases hre : 1 ≤ s.re
  · exact poleClearedFirstTraceExponentialContinuation_ne_zero_of_one_le_re hre
  · have hrelt : s.re < 1 := lt_of_not_ge hre
    have hcoord :
        s.im < -T ∧ firstTraceZeroFreeCuspBoundary T (-s.im) < s.re := by
      simpa [firstTraceZeroFreeLowerCusp_eq] using hs
    have himneg : s.im < 0 := by linarith [hcoord.1, hT]
    have habsim : |s.im| = -s.im := abs_of_neg himneg
    have hheight : T₀ ≤ |s.im| := by rw [habsim]; linarith [hcoord.1]
    have hmax : max T (-s.im) = -s.im := max_eq_right (by linarith [hcoord.1])
    have hwidth : 1 - 1 / 10000 / Real.log |s.im| < s.re := by
      rw [habsim]
      simpa [firstTraceZeroFreeCuspBoundary, hmax] using hcoord.2
    have hzeta : riemannZeta s ≠ 0 := by
      have hz := hzf s.re s.im hheight (le_of_lt hrelt) hwidth
      simpa [Complex.ext_iff] using hz
    have hxi : xi s ≠ 0 := by
      intro hxi
      have hspos : 0 < s.re := by linarith [mem_rightHalf.mp hsright]
      have hs1 : s ≠ 1 := by
        intro h
        subst s
        norm_num at himneg
      rw [xi_eq_zero_iff hspos hs1] at hxi
      exact hzeta hxi
    exact poleClearedFirstTraceExponentialContinuation_ne_zero_of_xi_ne_zero hsright hxi

/-- A lower-cusp root with the unique arithmetic orientation on its Euler overlap. -/
theorem exists_poleClearedFirstTrace_lowerCusp_arithmetic_extension_of_zeroFree
    {T₀ T : ℝ} (hT₀ : 3 ≤ T₀)
    (hzf : ∀ β γ : ℝ, T₀ ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hT₀T : T₀ ≤ T) (hT : 4 ≤ T) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (firstTraceZeroFreeLowerCusp T) ∧
        (∀ s ∈ firstTraceZeroFreeLowerCusp T,
          g s ^ 2 = poleClearedFirstTraceExponentialContinuation s) ∧
        EqOn g poleClearedPrimeZetaHalfEulerGerm
          (firstTraceZeroFreeLowerCusp T ∩ farHalf) := by
  have hlowerOpen := isOpen_firstTraceZeroFreeLowerCusp hT
  have hlowerSimply := isSimplyConnected_firstTraceZeroFreeLowerCusp hT
  have hlowerRight := firstTraceZeroFreeLowerCusp_subset_rightHalf hT
  obtain ⟨g, hg, hgsq⟩ := Bottcher.exists_analyticOnNhd_pow_eq hlowerSimply hlowerOpen
    (analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf.mono hlowerRight)
    (fun s hs => poleClearedFirstTraceExponentialContinuation_ne_zero_on_lowerCusp
      hT₀ hzf hT₀T hT hs) (N := 2) (by norm_num)
  let a : ℂ := 2 - ((T + 1 : ℝ) : ℂ) * I
  have haLower : a ∈ firstTraceZeroFreeLowerCusp T := by
    rw [firstTraceZeroFreeLowerCusp_eq]
    have him : a.im < -T := by norm_num [a]
    have hmax : max T (-a.im) = -a.im := max_eq_right (by linarith [him])
    have hlogpos : 0 < Real.log (-a.im) := Real.log_pos (by norm_num [a]; linarith)
    have hedge : firstTraceZeroFreeCuspBoundary T (-a.im) < 1 := by
      dsimp [firstTraceZeroFreeCuspBoundary]
      rw [hmax]
      have : 0 < (1 / 10000 : ℝ) / Real.log (-a.im) := div_pos (by norm_num) hlogpos
      linarith
    exact ⟨him, hedge.trans (by norm_num [a])⟩
  have haFar : a ∈ farHalf := by rw [mem_farHalf]; norm_num [a]
  have hsquares : g a ^ 2 = poleClearedPrimeZetaHalfEulerGerm a ^ 2 := by
    rw [hgsq a haLower, poleClearedPrimeZetaHalfEulerGerm_sq haFar]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hmatch | hmatch
  · refine ⟨g, hg, hgsq, ?_⟩
    exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
      (convex_firstTraceZeroFreeLowerCusp_inter_farHalf hT).isPreconnected
      (hg.continuousOn.mono inter_subset_left)
      (analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn.mono
        inter_subset_right)
      (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
      (fun s hs => by rw [hgsq s hs.1, poleClearedPrimeZetaHalfEulerGerm_sq hs.2])
      ⟨haLower, haFar⟩ hmatch
  · refine ⟨fun s => -g s, hg.neg, ?_, ?_⟩
    · intro s hs
      rw [neg_sq, hgsq s hs]
    · have hanchor : -g a = poleClearedPrimeZetaHalfEulerGerm a := by
        rw [hmatch]
        ring
      exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
        (convex_firstTraceZeroFreeLowerCusp_inter_farHalf hT).isPreconnected
        ((hg.neg).continuousOn.mono inter_subset_left)
        (analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn.mono
          inter_subset_right)
        (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
        (fun s hs => by rw [neg_sq, hgsq s hs.1,
          poleClearedPrimeZetaHalfEulerGerm_sq hs.2])
        ⟨haLower, haFar⟩ hanchor

/-- One unconditional arithmetic square root on the connected, conjugation-symmetric union of the
Euler half-plane and the upper and lower classical zero-free cusps. -/
theorem exists_poleClearedFirstTrace_symmetricZeroFreeCusp_arithmetic_extension :
    ∃ T : ℝ, 4 ≤ T ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (firstTraceSymmetricZeroFreeCusp T) ∧
        (∀ s ∈ firstTraceSymmetricZeroFreeCusp T,
          g s ^ 2 = poleClearedFirstTraceExponentialContinuation s) ∧
        EqOn g poleClearedPrimeZetaHalfEulerGerm farHalf := by
  obtain ⟨TU, hTU, gU, hgU, hgUsq, hgUEuler⟩ :=
    exists_poleClearedFirstTrace_zeroFreeCusp_arithmetic_extension
  obtain ⟨T₀, hT₀, hzf⟩ := Sieve.exists_zero_free_region_explicit
  let T : ℝ := max TU T₀
  have hTUT : TU ≤ T := le_max_left _ _
  have hT₀T : T₀ ≤ T := le_max_right _ _
  have hT : 4 ≤ T := hTU.trans hTUT
  have hupperSub : firstTraceZeroFreeCusp T ⊆ firstTraceZeroFreeCusp TU :=
    firstTraceZeroFreeCusp_mono_height hTUT
  have hgU' : AnalyticOnNhd ℂ gU (firstTraceZeroFreeCusp T) := hgU.mono hupperSub
  have hgUsq' : ∀ s ∈ firstTraceZeroFreeCusp T,
      gU s ^ 2 = poleClearedFirstTraceExponentialContinuation s :=
    fun s hs => hgUsq s (hupperSub hs)
  have hgUEuler' : EqOn gU poleClearedPrimeZetaHalfEulerGerm
      (firstTraceZeroFreeCusp T ∩ farHalf) := by
    intro s hs
    exact hgUEuler ⟨hupperSub hs.1, hs.2⟩
  obtain ⟨gL, hgL, hgLsq, hgLEuler⟩ :=
    exists_poleClearedFirstTrace_lowerCusp_arithmetic_extension_of_zeroFree
      hT₀ hzf hT₀T hT
  obtain ⟨gUF, hgUF, hgUFUpper, hgUFFar⟩ := Bottcher.analyticOnNhd_glue_twoChart
    (isOpen_firstTraceZeroFreeCusp hT) isOpen_farHalf hgU'
    analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf hgUEuler'
  have hUFLAgree : EqOn gUF gL
      ((firstTraceZeroFreeCusp T ∪ farHalf) ∩ firstTraceZeroFreeLowerCusp T) := by
    intro s hs
    have hnotUpper : s ∉ firstTraceZeroFreeCusp T := by
      intro hu
      exact Set.disjoint_left.mp (firstTraceZeroFreeCusp_disjoint_lowerCusp (by linarith [hT]))
        hu hs.2
    have hfar : s ∈ farHalf := hs.1.resolve_left hnotUpper
    rw [hgUFFar hfar]
    exact (hgLEuler ⟨hs.2, hfar⟩).symm
  obtain ⟨g, hg, hgUFg, hgLg⟩ := Bottcher.analyticOnNhd_glue_twoChart
    ((isOpen_firstTraceZeroFreeCusp hT).union isOpen_farHalf)
    (isOpen_firstTraceZeroFreeLowerCusp hT) hgUF hgL hUFLAgree
  refine ⟨T, hT, g, ?_, ?_, ?_⟩
  · simpa [firstTraceSymmetricZeroFreeCusp] using hg
  · intro s hs
    rw [firstTraceSymmetricZeroFreeCusp] at hs
    rcases hs with hsUF | hsL
    · rw [hgUFg hsUF]
      rcases hsUF with hsU | hsFar
      · rw [hgUFUpper hsU]
        exact hgUsq' s hsU
      · rw [hgUFFar hsFar]
        exact poleClearedPrimeZetaHalfEulerGerm_sq hsFar
    · rw [hgLg hsL]
      exact hgLsq s hsL
  · intro s hs
    have hsUF : s ∈ firstTraceZeroFreeCusp T ∪ farHalf := Or.inr hs
    rw [hgUFg hsUF, hgUFFar hs]

end

end RHTower
