import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceZeroFreeBand

/-!
# One coherent arithmetic half-germ on a classical zero-free cusp

The height-one band roots can be glued conceptually because they all carry the same Euler
normalization.  This file constructs the stronger object directly.  A real-coordinate shear
identifies the classical de la Vallee Poussin cusp with a convex quadrant, proving simple
connectedness.  Zero-freeness then supplies one analytic square root on the whole upper cusp,
oriented to the fixed prime-zeta half-germ.

The cusp retreats to `Re s = 1` at infinity.  It is an unconditional source-faithful continuation,
not a root on any fixed strip `Re s > sigma` with `sigma < 1`.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Globally continuous version of the classical cusp boundary. The `max` only protects the
logarithm away from the cusp itself. -/
def firstTraceZeroFreeCuspBoundary (T y : ℝ) : ℝ :=
  1 - (1 / 10000 : ℝ) / Real.log (max T y)

/-- Upper classical zero-free cusp. -/
def firstTraceZeroFreeCusp (T : ℝ) : Set ℂ :=
  {s : ℂ | T < s.im ∧ firstTraceZeroFreeCuspBoundary T s.im < s.re}

private theorem continuous_firstTraceZeroFreeCuspBoundary {T : ℝ} (hT : 4 ≤ T) :
    Continuous (firstTraceZeroFreeCuspBoundary T) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hmaxpos : 0 < max T y := lt_of_lt_of_le (by linarith) (le_max_left T y)
  have hmaxcont : ContinuousAt (fun x : ℝ => max T x) y :=
    continuousAt_const.max continuousAt_id
  have hlogcont : ContinuousAt (fun x : ℝ => Real.log (max T x)) y :=
    (Real.continuousAt_log hmaxpos.ne').comp hmaxcont
  have hmaxone : 1 < max T y := lt_of_lt_of_le (by linarith) (le_max_left T y)
  have hlogpos : 0 < Real.log (max T y) := Real.log_pos hmaxone
  exact continuousAt_const.sub (continuousAt_const.div hlogcont hlogpos.ne')

/-- Real shear taking the positive upper quadrant to the zero-free cusp. -/
noncomputable def firstTraceZeroFreeCuspShear (T : ℝ) (hT : 4 ≤ T) : ℂ ≃ₜ ℂ where
  toFun z := z + (firstTraceZeroFreeCuspBoundary T z.im : ℂ)
  invFun z := z - (firstTraceZeroFreeCuspBoundary T z.im : ℂ)
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv z := by
    apply Complex.ext <;> simp
  continuous_toFun := by
    exact continuous_id.add (Complex.continuous_ofReal.comp
      ((continuous_firstTraceZeroFreeCuspBoundary hT).comp Complex.continuous_im))
  continuous_invFun := by
    exact continuous_id.sub (Complex.continuous_ofReal.comp
      ((continuous_firstTraceZeroFreeCuspBoundary hT).comp Complex.continuous_im))

@[simp] theorem firstTraceZeroFreeCuspShear_re {T : ℝ} (hT : 4 ≤ T) (z : ℂ) :
    (firstTraceZeroFreeCuspShear T hT z).re =
      z.re + firstTraceZeroFreeCuspBoundary T z.im := by
  simp [firstTraceZeroFreeCuspShear]

@[simp] theorem firstTraceZeroFreeCuspShear_im {T : ℝ} (hT : 4 ≤ T) (z : ℂ) :
    (firstTraceZeroFreeCuspShear T hT z).im = z.im := by
  simp [firstTraceZeroFreeCuspShear]

@[simp] theorem firstTraceZeroFreeCuspShear_symm_re {T : ℝ} (hT : 4 ≤ T) (z : ℂ) :
    ((firstTraceZeroFreeCuspShear T hT).symm z).re =
      z.re - firstTraceZeroFreeCuspBoundary T z.im := by
  simp [firstTraceZeroFreeCuspShear]

@[simp] theorem firstTraceZeroFreeCuspShear_symm_im {T : ℝ} (hT : 4 ≤ T) (z : ℂ) :
    ((firstTraceZeroFreeCuspShear T hT).symm z).im = z.im := by
  simp [firstTraceZeroFreeCuspShear]

theorem isOpen_firstTraceZeroFreeCusp {T : ℝ} (hT : 4 ≤ T) :
    IsOpen (firstTraceZeroFreeCusp T) := by
  let Q : Set ℂ := {z : ℂ | 0 < z.re ∧ T < z.im}
  have hQopen : IsOpen Q :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have himage : firstTraceZeroFreeCuspShear T hT '' Q = firstTraceZeroFreeCusp T := by
    ext s
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [firstTraceZeroFreeCusp]
      constructor
      · simpa using hz.2
      · rw [firstTraceZeroFreeCuspShear_re, firstTraceZeroFreeCuspShear_im]
        linarith [hz.1]
    · intro hs
      refine ⟨(firstTraceZeroFreeCuspShear T hT).symm s, ?_,
        (firstTraceZeroFreeCuspShear T hT).apply_symm_apply s⟩
      rw [firstTraceZeroFreeCusp] at hs
      exact ⟨by simp only [firstTraceZeroFreeCuspShear_symm_re]; linarith [hs.2],
        by simpa using hs.1⟩
  rw [← himage]
  exact (firstTraceZeroFreeCuspShear T hT).isOpenMap Q hQopen

theorem isSimplyConnected_firstTraceZeroFreeCusp {T : ℝ} (hT : 4 ≤ T) :
    IsSimplyConnected (firstTraceZeroFreeCusp T) := by
  let Q : Set ℂ := {z : ℂ | 0 < z.re ∧ T < z.im}
  let F : Q → ℂ := fun z => firstTraceZeroFreeCuspShear T hT z
  have hemb : IsEmbedding F :=
    (firstTraceZeroFreeCuspShear T hT).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal
  have himage : F '' univ = firstTraceZeroFreeCusp T := by
    ext s
    constructor
    · rintro ⟨⟨z, hz⟩, -, rfl⟩
      rw [firstTraceZeroFreeCusp]
      constructor
      · simpa [F] using hz.2
      · simp only [F, firstTraceZeroFreeCuspShear_re,
          firstTraceZeroFreeCuspShear_im]
        linarith [hz.1]
    · intro hs
      refine ⟨⟨(firstTraceZeroFreeCuspShear T hT).symm s, ?_⟩, mem_univ _, ?_⟩
      · rw [firstTraceZeroFreeCusp] at hs
        exact ⟨by simp only [firstTraceZeroFreeCuspShear_symm_re]; linarith [hs.2],
          by simpa using hs.1⟩
      · exact (firstTraceZeroFreeCuspShear T hT).apply_symm_apply s
  rw [← himage, hemb.isSimplyConnected_image]
  have hQconvex : Convex ℝ Q :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt T)
  have hQne : Q.Nonempty := by
    refine ⟨1 + ((T + 1 : ℝ) : ℂ) * I, ?_⟩
    constructor <;> norm_num
  haveI : ContractibleSpace Q := hQconvex.contractibleSpace hQne
  haveI : SimplyConnectedSpace Q := SimplyConnectedSpace.ofContractible Q
  exact ((Homeomorph.Set.univ Q).toHomotopyEquiv).simplyConnectedSpace_iff.mpr ‹_›

theorem firstTraceZeroFreeCusp_subset_rightHalf {T : ℝ} (hT : 4 ≤ T) :
    firstTraceZeroFreeCusp T ⊆ rightHalf := by
  intro s hs
  have himT : T < s.im := hs.1
  have hmax : max T s.im = s.im := max_eq_right (le_of_lt himT)
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have hlogeq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlogeq]
    linarith [Real.log_two_gt_d9]
  have himpos : 0 < s.im := by linarith [himT]
  have h4im : (4 : ℝ) ≤ s.im := by linarith [himT]
  have hlogmono : Real.log 4 ≤ Real.log s.im :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) himpos h4im
  have hlog : 1 < Real.log s.im := hlog4.trans_le hlogmono
  have hquot : (1 / 10000 : ℝ) / Real.log s.im < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith : 0 < Real.log s.im)]
    nlinarith
  rw [mem_rightHalf]
  rw [firstTraceZeroFreeCusp] at hs
  dsimp [firstTraceZeroFreeCuspBoundary] at hs
  rw [hmax] at hs
  linarith

theorem firstTraceZeroFreeCusp_inter_farHalf_eq {T : ℝ} (hT : 4 ≤ T) :
    firstTraceZeroFreeCusp T ∩ farHalf = {s : ℂ | T < s.im ∧ 1 < s.re} := by
  ext s
  constructor
  · rintro ⟨hs, hfar⟩
    exact ⟨hs.1, mem_farHalf.mp hfar⟩
  · rintro ⟨him, hre⟩
    have hmax : max T s.im = s.im := max_eq_right (le_of_lt him)
    have hlogpos : 0 < Real.log s.im := Real.log_pos (by linarith)
    have hedge : firstTraceZeroFreeCuspBoundary T s.im < 1 := by
      dsimp [firstTraceZeroFreeCuspBoundary]
      rw [hmax]
      have : 0 < (1 / 10000 : ℝ) / Real.log s.im := div_pos (by norm_num) hlogpos
      linarith
    exact ⟨⟨him, hedge.trans hre⟩, mem_farHalf.mpr hre⟩

theorem convex_firstTraceZeroFreeCusp_inter_farHalf {T : ℝ} (hT : 4 ≤ T) :
    Convex ℝ (firstTraceZeroFreeCusp T ∩ farHalf) := by
  rw [firstTraceZeroFreeCusp_inter_farHalf_eq hT]
  exact (convex_halfSpace_im_gt T).inter (convex_halfSpace_re_gt 1)

theorem poleClearedFirstTraceExponentialContinuation_ne_zero_on_cusp
    {T₀ T : ℝ} (_hT₀ : 3 ≤ T₀)
    (hzf : ∀ β γ : ℝ, T₀ ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hT₀T : T₀ ≤ T) (hT : 4 ≤ T) {s : ℂ} (hs : s ∈ firstTraceZeroFreeCusp T) :
    poleClearedFirstTraceExponentialContinuation s ≠ 0 := by
  have hsright := firstTraceZeroFreeCusp_subset_rightHalf hT hs
  by_cases hre : 1 ≤ s.re
  · exact poleClearedFirstTraceExponentialContinuation_ne_zero_of_one_le_re hre
  · have hrelt : s.re < 1 := lt_of_not_ge hre
    have himpos : 0 < s.im := by linarith [hs.1]
    have habsim : |s.im| = s.im := abs_of_pos himpos
    have hheight : T₀ ≤ |s.im| := by rw [habsim]; linarith [hs.1]
    have hmax : max T s.im = s.im := max_eq_right (le_of_lt hs.1)
    have hwidth : 1 - 1 / 10000 / Real.log |s.im| < s.re := by
      rw [habsim]
      simpa [firstTraceZeroFreeCuspBoundary, hmax] using hs.2
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

/-- One unconditional analytic continuation of the fixed arithmetic half-germ on the entire
classical upper zero-free cusp. -/
theorem exists_poleClearedFirstTrace_zeroFreeCusp_arithmetic_extension :
    ∃ T : ℝ, 4 ≤ T ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (firstTraceZeroFreeCusp T) ∧
        (∀ s ∈ firstTraceZeroFreeCusp T,
          g s ^ 2 = poleClearedFirstTraceExponentialContinuation s) ∧
        EqOn g poleClearedPrimeZetaHalfEulerGerm
          (firstTraceZeroFreeCusp T ∩ farHalf) := by
  obtain ⟨T₀, hT₀, hzf⟩ := Sieve.exists_zero_free_region_explicit
  let T : ℝ := max T₀ 4
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hT : 4 ≤ T := le_max_right _ _
  have hcuspOpen := isOpen_firstTraceZeroFreeCusp hT
  have hcuspSimply := isSimplyConnected_firstTraceZeroFreeCusp hT
  have hcuspRight := firstTraceZeroFreeCusp_subset_rightHalf hT
  obtain ⟨g, hg, hgsq⟩ := Bottcher.exists_analyticOnNhd_pow_eq hcuspSimply hcuspOpen
    (analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf.mono hcuspRight)
    (fun s hs => poleClearedFirstTraceExponentialContinuation_ne_zero_on_cusp
      hT₀ hzf hT₀T hT hs) (N := 2) (by norm_num)
  let a : ℂ := 2 + ((T + 1 : ℝ) : ℂ) * I
  have haCusp : a ∈ firstTraceZeroFreeCusp T := by
    have him : T < a.im := by norm_num [a]
    have hmax : max T a.im = a.im := max_eq_right (le_of_lt him)
    have hlogpos : 0 < Real.log a.im := Real.log_pos (by norm_num [a]; linarith)
    have hedge : firstTraceZeroFreeCuspBoundary T a.im < 1 := by
      dsimp [firstTraceZeroFreeCuspBoundary]
      rw [hmax]
      have : 0 < (1 / 10000 : ℝ) / Real.log a.im := div_pos (by norm_num) hlogpos
      linarith
    refine ⟨him, ?_⟩
    exact hedge.trans (by norm_num [a])
  have haFar : a ∈ farHalf := by
    rw [mem_farHalf]
    norm_num [a]
  have hsquares : g a ^ 2 = poleClearedPrimeZetaHalfEulerGerm a ^ 2 := by
    rw [hgsq a haCusp, poleClearedPrimeZetaHalfEulerGerm_sq haFar]
  refine ⟨T, hT, ?_⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hmatch | hmatch
  · refine ⟨g, hg, hgsq, ?_⟩
    exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
      (convex_firstTraceZeroFreeCusp_inter_farHalf hT).isPreconnected
      (hg.continuousOn.mono inter_subset_left)
      (analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn.mono
        inter_subset_right)
      (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
      (fun s hs => by rw [hgsq s hs.1, poleClearedPrimeZetaHalfEulerGerm_sq hs.2])
      ⟨haCusp, haFar⟩ hmatch
  · refine ⟨fun s => -g s, hg.neg, ?_, ?_⟩
    · intro s hs
      rw [neg_sq, hgsq s hs]
    · have hanchor : -g a = poleClearedPrimeZetaHalfEulerGerm a := by
        rw [hmatch]
        ring
      exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
        (convex_firstTraceZeroFreeCusp_inter_farHalf hT).isPreconnected
        ((hg.neg).continuousOn.mono inter_subset_left)
        (analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn.mono
          inter_subset_right)
        (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
        (fun s hs => by rw [neg_sq, hgsq s hs.1,
          poleClearedPrimeZetaHalfEulerGerm_sq hs.2])
        ⟨haCusp, haFar⟩ hanchor

end

end RHTower
