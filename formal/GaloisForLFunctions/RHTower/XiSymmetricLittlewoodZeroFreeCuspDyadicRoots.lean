import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceSymmetricZeroFreeCusp
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegionNine
import GaloisForLFunctions.RHTower.GermExtension

/-!
# Actual Xi dyadic roots on a symmetric Littlewood zero-free cusp

The repository's unconditional Littlewood region is wider than the classical
`1 / log |t|` cusp by a factor `log log |t|`.  After clamping its left boundary at
`Re s = 1/2`, a real shear proves each high cusp simply connected.  Hence every chosen
Euler-side `2^k`-th root of the actual completed `xi` extends across both cusps.  A
root-of-unity normalization on each convex Euler overlap and two-chart gluing produce one
root on the conjugation-symmetric union, with one fixed positive Littlewood constant for
all dyadic levels.

This is an unconditional enlargement of the actual-root domain.  Its boundary still tends
to `Re s = 1`, so it does not supply roots on all of `rightHalf` and does not prove RH.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

def littlewoodZeroFreeCuspBoundary (c y : ℝ) : ℝ :=
  max (1 / 2 : ℝ)
    (1 - c * Real.log (Real.log (max 9 y)) / Real.log (max 9 y))

def littlewoodZeroFreeCusp (c : ℝ) : Set ℂ :=
  {s : ℂ | 9 < s.im ∧ littlewoodZeroFreeCuspBoundary c s.im < s.re}

def littlewoodZeroFreeLowerCusp (c : ℝ) : Set ℂ :=
  {s : ℂ | (starRingEnd ℂ) s ∈ littlewoodZeroFreeCusp c}

def littlewoodSymmetricZeroFreeCusp (c : ℝ) : Set ℂ :=
  (littlewoodZeroFreeCusp c ∪ farHalf) ∪ littlewoodZeroFreeLowerCusp c

/-- Explicit height after which the Littlewood width dominates the classical `1 / log` width. -/
def littlewoodClassicalDominanceHeight (c : ℝ) : ℝ :=
  max 9 (Real.exp (Real.exp (1 / (10000 * c) + 1)))

theorem nine_le_littlewoodClassicalDominanceHeight (c : ℝ) :
    9 ≤ littlewoodClassicalDominanceHeight c :=
  le_max_left _ _

private theorem continuous_littlewoodZeroFreeCuspBoundary (c : ℝ) :
    Continuous (littlewoodZeroFreeCuspBoundary c) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hmaxpos : 0 < max (9 : ℝ) y :=
    lt_of_lt_of_le (by norm_num) (le_max_left 9 y)
  have hmaxone : 1 < max (9 : ℝ) y :=
    lt_of_lt_of_le (by norm_num) (le_max_left 9 y)
  have hmaxcont : ContinuousAt (fun x : ℝ => max 9 x) y :=
    continuousAt_const.max continuousAt_id
  have hlogcont : ContinuousAt (fun x : ℝ => Real.log (max 9 x)) y :=
    (Real.continuousAt_log hmaxpos.ne').comp hmaxcont
  have hlogpos : 0 < Real.log (max 9 y) := Real.log_pos hmaxone
  have hloglogcont :
      ContinuousAt (fun x : ℝ => Real.log (Real.log (max 9 x))) y :=
    hlogcont.log hlogpos.ne'
  exact continuousAt_const.max
    (continuousAt_const.sub
      ((continuousAt_const.mul hloglogcont).div hlogcont hlogpos.ne'))

noncomputable def littlewoodZeroFreeCuspShear (c : ℝ) : ℂ ≃ₜ ℂ where
  toFun z := z + (littlewoodZeroFreeCuspBoundary c z.im : ℂ)
  invFun z := z - (littlewoodZeroFreeCuspBoundary c z.im : ℂ)
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp
  continuous_toFun := by
    exact continuous_id.add (Complex.continuous_ofReal.comp
      ((continuous_littlewoodZeroFreeCuspBoundary c).comp Complex.continuous_im))
  continuous_invFun := by
    exact continuous_id.sub (Complex.continuous_ofReal.comp
      ((continuous_littlewoodZeroFreeCuspBoundary c).comp Complex.continuous_im))

@[simp] theorem littlewoodZeroFreeCuspShear_re (c : ℝ) (z : ℂ) :
    (littlewoodZeroFreeCuspShear c z).re =
      z.re + littlewoodZeroFreeCuspBoundary c z.im := by
  simp [littlewoodZeroFreeCuspShear]

@[simp] theorem littlewoodZeroFreeCuspShear_im (c : ℝ) (z : ℂ) :
    (littlewoodZeroFreeCuspShear c z).im = z.im := by
  simp [littlewoodZeroFreeCuspShear]

@[simp] theorem littlewoodZeroFreeCuspShear_symm_re (c : ℝ) (z : ℂ) :
    ((littlewoodZeroFreeCuspShear c).symm z).re =
      z.re - littlewoodZeroFreeCuspBoundary c z.im := by
  simp [littlewoodZeroFreeCuspShear]

@[simp] theorem littlewoodZeroFreeCuspShear_symm_im (c : ℝ) (z : ℂ) :
    ((littlewoodZeroFreeCuspShear c).symm z).im = z.im := by
  simp [littlewoodZeroFreeCuspShear]

theorem isOpen_littlewoodZeroFreeCusp (c : ℝ) :
    IsOpen (littlewoodZeroFreeCusp c) := by
  let Q : Set ℂ := {z : ℂ | 0 < z.re ∧ 9 < z.im}
  have hQopen : IsOpen Q :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have himage : littlewoodZeroFreeCuspShear c '' Q = littlewoodZeroFreeCusp c := by
    ext s
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [littlewoodZeroFreeCusp]
      constructor
      · simpa using hz.2
      · rw [littlewoodZeroFreeCuspShear_re, littlewoodZeroFreeCuspShear_im]
        linarith [hz.1]
    · intro hs
      refine ⟨(littlewoodZeroFreeCuspShear c).symm s, ?_,
        (littlewoodZeroFreeCuspShear c).apply_symm_apply s⟩
      rw [littlewoodZeroFreeCusp] at hs
      exact ⟨by simp only [littlewoodZeroFreeCuspShear_symm_re]; linarith [hs.2],
        by simpa using hs.1⟩
  rw [← himage]
  exact (littlewoodZeroFreeCuspShear c).isOpenMap Q hQopen

theorem isSimplyConnected_littlewoodZeroFreeCusp (c : ℝ) :
    IsSimplyConnected (littlewoodZeroFreeCusp c) := by
  let Q : Set ℂ := {z : ℂ | 0 < z.re ∧ 9 < z.im}
  let F : Q → ℂ := fun z => littlewoodZeroFreeCuspShear c z
  have hemb : IsEmbedding F :=
    (littlewoodZeroFreeCuspShear c).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have himage : F '' univ = littlewoodZeroFreeCusp c := by
    ext s
    constructor
    · rintro ⟨⟨z, hz⟩, -, rfl⟩
      rw [littlewoodZeroFreeCusp]
      constructor
      · simpa [F] using hz.2
      · simp only [F, littlewoodZeroFreeCuspShear_re,
          littlewoodZeroFreeCuspShear_im]
        linarith [hz.1]
    · intro hs
      refine ⟨⟨(littlewoodZeroFreeCuspShear c).symm s, ?_⟩, mem_univ _, ?_⟩
      · rw [littlewoodZeroFreeCusp] at hs
        exact ⟨by simp only [littlewoodZeroFreeCuspShear_symm_re]; linarith [hs.2],
          by simpa using hs.1⟩
      · exact (littlewoodZeroFreeCuspShear c).apply_symm_apply s
  rw [← himage, hemb.isSimplyConnected_image]
  have hQconvex : Convex ℝ Q :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 9)
  have hQne : Q.Nonempty := by
    refine ⟨1 + (10 : ℂ) * I, ?_⟩
    constructor <;> norm_num
  haveI : ContractibleSpace Q := hQconvex.contractibleSpace hQne
  haveI : SimplyConnectedSpace Q := SimplyConnectedSpace.ofContractible Q
  exact ((Homeomorph.Set.univ Q).toHomotopyEquiv).simplyConnectedSpace_iff.mpr ‹_›

theorem littlewoodZeroFreeCusp_subset_rightHalf (c : ℝ) :
    littlewoodZeroFreeCusp c ⊆ rightHalf := by
  intro s hs
  rw [mem_rightHalf]
  exact lt_of_le_of_lt (le_max_left _ _) hs.2

theorem littlewoodZeroFreeLowerCusp_eq (c : ℝ) :
    littlewoodZeroFreeLowerCusp c =
      {s : ℂ | s.im < -9 ∧ littlewoodZeroFreeCuspBoundary c (-s.im) < s.re} := by
  ext s
  simp only [littlewoodZeroFreeLowerCusp, littlewoodZeroFreeCusp, mem_setOf_eq,
    Complex.conj_im, Complex.conj_re]
  constructor
  · rintro ⟨him, hre⟩
    exact ⟨by linarith, hre⟩
  · rintro ⟨him, hre⟩
    exact ⟨by linarith, hre⟩

theorem isOpen_littlewoodZeroFreeLowerCusp (c : ℝ) :
    IsOpen (littlewoodZeroFreeLowerCusp c) := by
  change IsOpen ((starRingEnd ℂ) ⁻¹' littlewoodZeroFreeCusp c)
  exact (isOpen_littlewoodZeroFreeCusp c).preimage Complex.continuous_conj

theorem isSimplyConnected_littlewoodZeroFreeLowerCusp (c : ℝ) :
    IsSimplyConnected (littlewoodZeroFreeLowerCusp c) := by
  have himage :
      (starRingEnd ℂ) '' littlewoodZeroFreeCusp c = littlewoodZeroFreeLowerCusp c := by
    ext s
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [littlewoodZeroFreeLowerCusp] using hz
    · intro hs
      refine ⟨(starRingEnd ℂ) s, ?_, by simp⟩
      simpa [littlewoodZeroFreeLowerCusp] using hs
  rw [← himage]
  change IsSimplyConnected (Complex.conjCLE.toHomeomorph '' littlewoodZeroFreeCusp c)
  rw [Complex.conjCLE.toHomeomorph.isEmbedding.isSimplyConnected_image]
  exact isSimplyConnected_littlewoodZeroFreeCusp c

theorem littlewoodZeroFreeLowerCusp_subset_rightHalf (c : ℝ) :
    littlewoodZeroFreeLowerCusp c ⊆ rightHalf := by
  intro s hs
  have hu : (starRingEnd ℂ) s ∈ littlewoodZeroFreeCusp c := hs
  have hr := littlewoodZeroFreeCusp_subset_rightHalf c hu
  rw [mem_rightHalf] at hr ⊢
  simpa using hr

theorem littlewoodZeroFreeCuspBoundary_lt_one {c y : ℝ} (hc : 0 < c) (hy : 9 < y) :
    littlewoodZeroFreeCuspBoundary c y < 1 := by
  have hmax : max (9 : ℝ) y = y := max_eq_right (le_of_lt hy)
  have hlog9 : (2 : ℝ) < Real.log 9 := by
    have h8 : Real.log (8 : ℝ) ≤ Real.log 9 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h8eq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h8eq] at h8
    linarith [Real.log_two_gt_d9]
  have hlogy : 1 < Real.log y := by
    have hmono : Real.log 9 ≤ Real.log y :=
      Real.log_le_log (by norm_num) (le_of_lt hy)
    linarith
  have hlogpos : 0 < Real.log y := by linarith
  have hloglogpos : 0 < Real.log (Real.log y) := Real.log_pos hlogy
  have hwidth : 0 < c * Real.log (Real.log y) / Real.log y :=
    div_pos (mul_pos hc hloglogpos) hlogpos
  rw [littlewoodZeroFreeCuspBoundary, hmax]
  exact max_lt (by norm_num) (by linarith)

theorem littlewoodZeroFreeCuspBoundary_lt_firstTraceZeroFreeCuspBoundary
    {c y : ℝ} (hc : 0 < c) (hy : littlewoodClassicalDominanceHeight c < y) :
    littlewoodZeroFreeCuspBoundary c y <
      firstTraceZeroFreeCuspBoundary (littlewoodClassicalDominanceHeight c) y := by
  let A : ℝ := 1 / (10000 * c) + 1
  have hExp : Real.exp (Real.exp A) ≤ littlewoodClassicalDominanceHeight c := by
    exact le_max_right _ _
  have hExpY : Real.exp (Real.exp A) < y := hExp.trans_lt hy
  have hypos : 0 < y := lt_trans (Real.exp_pos _) hExpY
  have hlogLower : Real.exp A < Real.log y := by
    have h := Real.strictMonoOn_log (Real.exp_pos _) hypos hExpY
    simpa using h
  have hlogpos : 0 < Real.log y := lt_trans (Real.exp_pos _) hlogLower
  have hloglogLower : A < Real.log (Real.log y) := by
    have h := Real.strictMonoOn_log (Real.exp_pos _) hlogpos hlogLower
    simpa [A] using h
  have hnum : (1 / 10000 : ℝ) < c * Real.log (Real.log y) := by
    have hmul := mul_lt_mul_of_pos_left hloglogLower hc
    have heq : c * A = (1 / 10000 : ℝ) + c := by
      dsimp [A]
      field_simp [ne_of_gt hc]
    rw [heq] at hmul
    linarith
  have hfrac : (1 / 10000 : ℝ) / Real.log y <
      c * Real.log (Real.log y) / Real.log y :=
    div_lt_div_of_pos_right hnum hlogpos
  have hraw :
      1 - c * Real.log (Real.log y) / Real.log y <
        1 - (1 / 10000 : ℝ) / Real.log y := by
    linarith
  have hlog9 : (2 : ℝ) < Real.log 9 := by
    have h8 : Real.log (8 : ℝ) ≤ Real.log 9 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h8eq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h8eq] at h8
    linarith [Real.log_two_gt_d9]
  have h9y : (9 : ℝ) < y :=
    (nine_le_littlewoodClassicalDominanceHeight c).trans_lt hy
  have hlogy : 2 < Real.log y := by
    have hmono : Real.log 9 ≤ Real.log y :=
      Real.log_le_log (by norm_num) (le_of_lt h9y)
    linarith
  have holdWidth : (1 / 10000 : ℝ) / Real.log y < 1 / 2 := by
    rw [div_lt_iff₀ hlogpos]
    nlinarith
  have hhalf : (1 / 2 : ℝ) < 1 - (1 / 10000 : ℝ) / Real.log y := by
    linarith
  have hmax9 : max (9 : ℝ) y = y := max_eq_right (le_of_lt h9y)
  have hmaxT : max (littlewoodClassicalDominanceHeight c) y = y :=
    max_eq_right (le_of_lt hy)
  rw [littlewoodZeroFreeCuspBoundary, firstTraceZeroFreeCuspBoundary, hmax9, hmaxT]
  exact max_lt hhalf hraw

/-- Above an explicit height, the classical cusp is properly contained in the Littlewood cusp. -/
theorem firstTraceZeroFreeCusp_strictlyContainedIn_littlewoodZeroFreeCusp
    {c : ℝ} (hc : 0 < c) :
    firstTraceZeroFreeCusp (littlewoodClassicalDominanceHeight c) ⊆
        littlewoodZeroFreeCusp c ∧
      ∃ s : ℂ, s ∈ littlewoodZeroFreeCusp c ∧
        s ∉ firstTraceZeroFreeCusp (littlewoodClassicalDominanceHeight c) := by
  constructor
  · intro s hs
    exact ⟨(nine_le_littlewoodClassicalDominanceHeight c).trans_lt hs.1,
      (littlewoodZeroFreeCuspBoundary_lt_firstTraceZeroFreeCuspBoundary hc hs.1).trans
        hs.2⟩
  · let y : ℝ := littlewoodClassicalDominanceHeight c + 1
    let bL : ℝ := littlewoodZeroFreeCuspBoundary c y
    let bC : ℝ := firstTraceZeroFreeCuspBoundary
      (littlewoodClassicalDominanceHeight c) y
    let s : ℂ := (((bL + bC) / 2 : ℝ) : ℂ) + (y : ℂ) * I
    have hy : littlewoodClassicalDominanceHeight c < y := by
      dsimp [y]
      linarith
    have hb : bL < bC := by
      exact littlewoodZeroFreeCuspBoundary_lt_firstTraceZeroFreeCuspBoundary hc hy
    have hsim : s.im = y := by simp [s]
    have hsre : s.re = (bL + bC) / 2 := by simp [s]
    refine ⟨s, ?_, ?_⟩
    · constructor
      · rw [hsim]
        exact (nine_le_littlewoodClassicalDominanceHeight c).trans_lt hy
      · rw [hsim, hsre]
        change bL < (bL + bC) / 2
        linarith
    · intro hs
      have hre := hs.2
      rw [hsim, hsre] at hre
      change bC < (bL + bC) / 2 at hre
      linarith

theorem littlewoodZeroFreeCusp_inter_farHalf_eq {c : ℝ} (hc : 0 < c) :
    littlewoodZeroFreeCusp c ∩ farHalf = {s : ℂ | 9 < s.im ∧ 1 < s.re} := by
  ext s
  constructor
  · rintro ⟨hs, hfar⟩
    exact ⟨hs.1, mem_farHalf.mp hfar⟩
  · rintro ⟨him, hre⟩
    exact ⟨⟨him, (littlewoodZeroFreeCuspBoundary_lt_one hc him).trans hre⟩,
      mem_farHalf.mpr hre⟩

theorem convex_littlewoodZeroFreeCusp_inter_farHalf {c : ℝ} (hc : 0 < c) :
    Convex ℝ (littlewoodZeroFreeCusp c ∩ farHalf) := by
  rw [littlewoodZeroFreeCusp_inter_farHalf_eq hc]
  exact (convex_halfSpace_im_gt 9).inter (convex_halfSpace_re_gt 1)

theorem littlewoodZeroFreeLowerCusp_inter_farHalf_eq {c : ℝ} (hc : 0 < c) :
    littlewoodZeroFreeLowerCusp c ∩ farHalf = {s : ℂ | s.im < -9 ∧ 1 < s.re} := by
  ext s
  constructor
  · rintro ⟨hs, hfar⟩
    rw [littlewoodZeroFreeLowerCusp_eq] at hs
    exact ⟨hs.1, mem_farHalf.mp hfar⟩
  · rintro ⟨him, hre⟩
    rw [littlewoodZeroFreeLowerCusp_eq]
    exact ⟨⟨him, (littlewoodZeroFreeCuspBoundary_lt_one hc (by linarith)).trans hre⟩,
      mem_farHalf.mpr hre⟩

theorem convex_littlewoodZeroFreeLowerCusp_inter_farHalf {c : ℝ} (hc : 0 < c) :
    Convex ℝ (littlewoodZeroFreeLowerCusp c ∩ farHalf) := by
  rw [littlewoodZeroFreeLowerCusp_inter_farHalf_eq hc]
  exact (convex_halfSpace_im_lt (-9)).inter (convex_halfSpace_re_gt 1)

theorem littlewoodZeroFreeCusp_disjoint_lowerCusp (c : ℝ) :
    Disjoint (littlewoodZeroFreeCusp c) (littlewoodZeroFreeLowerCusp c) := by
  rw [Set.disjoint_left]
  intro s hu hl
  rw [littlewoodZeroFreeLowerCusp_eq] at hl
  linarith [hu.1, hl.1]

theorem isOpen_littlewoodSymmetricZeroFreeCusp (c : ℝ) :
    IsOpen (littlewoodSymmetricZeroFreeCusp c) := by
  simpa [littlewoodSymmetricZeroFreeCusp] using
    ((isOpen_littlewoodZeroFreeCusp c).union isOpen_farHalf).union
      (isOpen_littlewoodZeroFreeLowerCusp c)

theorem isPreconnected_littlewoodSymmetricZeroFreeCusp {c : ℝ} (hc : 0 < c) :
    IsPreconnected (littlewoodSymmetricZeroFreeCusp c) := by
  let aU : ℂ := 2 + (10 : ℂ) * I
  have haU : aU ∈ littlewoodZeroFreeCusp c := by
    exact ⟨by norm_num [aU],
      (littlewoodZeroFreeCuspBoundary_lt_one hc (by norm_num [aU])).trans
        (by norm_num [aU])⟩
  have haUFar : aU ∈ farHalf := by rw [mem_farHalf]; norm_num [aU]
  have hUF : IsPreconnected (littlewoodZeroFreeCusp c ∪ farHalf) :=
    IsPreconnected.union aU haU haUFar
      (isSimplyConnected_littlewoodZeroFreeCusp c).isPathConnected.isConnected.isPreconnected
      convex_farHalf.isPreconnected
  let aL : ℂ := 2 - (10 : ℂ) * I
  have haL : aL ∈ littlewoodZeroFreeLowerCusp c := by
    rw [littlewoodZeroFreeLowerCusp_eq]
    exact ⟨by norm_num [aL],
      (littlewoodZeroFreeCuspBoundary_lt_one hc (by norm_num [aL])).trans
        (by norm_num [aL])⟩
  have haLFar : aL ∈ farHalf := by rw [mem_farHalf]; norm_num [aL]
  rw [littlewoodSymmetricZeroFreeCusp]
  exact IsPreconnected.union aL (Or.inr haLFar) haL hUF
    (isSimplyConnected_littlewoodZeroFreeLowerCusp c).isPathConnected.isConnected.isPreconnected

theorem xi_ne_zero_on_littlewoodZeroFreeCusp_of_zeroFree
    {c : ℝ}
    (hzf : ∀ β t : ℝ, 9 ≤ |t| → β ≤ 1 →
      1 - c * Real.log (Real.log |t|) / Real.log |t| < β →
        riemannZeta ((β : ℂ) + (t : ℂ) * I) ≠ 0)
    {s : ℂ} (hs : s ∈ littlewoodZeroFreeCusp c) : xi s ≠ 0 := by
  have hsright := littlewoodZeroFreeCusp_subset_rightHalf c hs
  by_cases hre : 1 ≤ s.re
  · exact xi_ne_zero_of_one_le_re hre
  · have hrelt : s.re < 1 := lt_of_not_ge hre
    have himpos : 0 < s.im := by linarith [hs.1]
    have habsim : |s.im| = s.im := abs_of_pos himpos
    have hheight : 9 ≤ |s.im| := by rw [habsim]; linarith [hs.1]
    have hmax : max (9 : ℝ) s.im = s.im := max_eq_right (le_of_lt hs.1)
    have hwidth :
        1 - c * Real.log (Real.log |s.im|) / Real.log |s.im| < s.re := by
      rw [habsim]
      exact lt_of_le_of_lt (by
        simp only [littlewoodZeroFreeCuspBoundary, hmax]
        exact le_max_right _ _) hs.2
    have hzeta : riemannZeta s ≠ 0 := by
      have hz := hzf s.re s.im hheight (le_of_lt hrelt) hwidth
      simpa [Complex.ext_iff] using hz
    intro hxi
    have hspos : 0 < s.re := by linarith [mem_rightHalf.mp hsright]
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      norm_num at himpos
    rw [xi_eq_zero_iff hspos hs1] at hxi
    exact hzeta hxi

theorem xi_ne_zero_on_littlewoodZeroFreeLowerCusp_of_zeroFree
    {c : ℝ}
    (hzf : ∀ β t : ℝ, 9 ≤ |t| → β ≤ 1 →
      1 - c * Real.log (Real.log |t|) / Real.log |t| < β →
        riemannZeta ((β : ℂ) + (t : ℂ) * I) ≠ 0)
    {s : ℂ} (hs : s ∈ littlewoodZeroFreeLowerCusp c) : xi s ≠ 0 := by
  have hsright := littlewoodZeroFreeLowerCusp_subset_rightHalf c hs
  by_cases hre : 1 ≤ s.re
  · exact xi_ne_zero_of_one_le_re hre
  · have hrelt : s.re < 1 := lt_of_not_ge hre
    rw [littlewoodZeroFreeLowerCusp_eq] at hs
    have himneg : s.im < 0 := by linarith [hs.1]
    have habsim : |s.im| = -s.im := abs_of_neg himneg
    have hheight : 9 ≤ |s.im| := by rw [habsim]; linarith [hs.1]
    have hmax : max (9 : ℝ) (-s.im) = -s.im := max_eq_right (by linarith [hs.1])
    have hwidth :
        1 - c * Real.log (Real.log |s.im|) / Real.log |s.im| < s.re := by
      rw [habsim]
      exact lt_of_le_of_lt (by
        simp only [littlewoodZeroFreeCuspBoundary, hmax]
        exact le_max_right _ _) hs.2
    have hzeta : riemannZeta s ≠ 0 := by
      have hz := hzf s.re s.im hheight (le_of_lt hrelt) hwidth
      simpa [Complex.ext_iff] using hz
    intro hxi
    have hspos : 0 < s.re := by linarith [mem_rightHalf.mp hsright]
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      norm_num at himneg
    rw [xi_eq_zero_iff hspos hs1] at hxi
    exact hzeta hxi

theorem exists_xi_littlewoodZeroFreeCusp_extension_of_farHalf_root
    {c : ℝ} (hc : 0 < c)
    (hzf : ∀ β t : ℝ, 9 ≤ |t| → β ≤ 1 →
      1 - c * Real.log (Real.log |t|) / Real.log |t| < β →
        riemannZeta ((β : ℂ) + (t : ℂ) * I) ≠ 0)
    (k : ℕ) (g₁ : ℂ → ℂ) (hg₁ : AnalyticOnNhd ℂ g₁ farHalf)
    (hg₁pow : ∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (littlewoodZeroFreeCusp c) ∧
        (∀ s ∈ littlewoodZeroFreeCusp c, g s ^ 2 ^ k = xi s) ∧
        EqOn g g₁ (littlewoodZeroFreeCusp c ∩ farHalf) := by
  obtain ⟨g, hg, hgpow⟩ := Bottcher.exists_analyticOnNhd_pow_eq
    (isSimplyConnected_littlewoodZeroFreeCusp c)
    (isOpen_littlewoodZeroFreeCusp c)
    ((xi_analyticOnNhd rightHalf).mono (littlewoodZeroFreeCusp_subset_rightHalf c))
    (fun s hs => xi_ne_zero_on_littlewoodZeroFreeCusp_of_zeroFree hzf hs)
    Nat.one_le_two_pow
  let a : ℂ := 2 + (10 : ℂ) * I
  have haCusp : a ∈ littlewoodZeroFreeCusp c := by
    exact ⟨by norm_num [a],
      (littlewoodZeroFreeCuspBoundary_lt_one hc (by norm_num [a])).trans
        (by norm_num [a])⟩
  have haFar : a ∈ farHalf := by rw [mem_farHalf]; norm_num [a]
  have hxia : xi a ≠ 0 := xi_ne_zero_of_one_lt_re (mem_farHalf.mp haFar)
  have hga : g a ≠ 0 := by
    intro hzero
    have hpow := hgpow a haCusp
    rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
    exact hxia hpow.symm
  let omega : ℂ := g₁ a / g a
  have homegaPow : omega ^ 2 ^ k = 1 := by
    change (g₁ a / g a) ^ 2 ^ k = 1
    rw [div_pow, hg₁pow a haFar, hgpow a haCusp, div_self hxia]
  have hroot : ∀ s ∈ littlewoodZeroFreeCusp c,
      (omega * g s) ^ 2 ^ k = xi s := by
    intro s hs
    rw [mul_pow, homegaPow, one_mul, hgpow s hs]
  have hmatch : omega * g a = g₁ a := by
    change (g₁ a / g a) * g a = g₁ a
    rw [div_mul_cancel₀ _ hga]
  have hscaledAn : AnalyticOnNhd ℂ (fun s => omega * g s)
      (littlewoodZeroFreeCusp c) := fun s hs => analyticAt_const.mul (hg s hs)
  refine ⟨fun s => omega * g s, hscaledAn, hroot, ?_⟩
  exact Bottcher.eqOn_of_pow_eq_of_isPreconnected Nat.one_le_two_pow
    (convex_littlewoodZeroFreeCusp_inter_farHalf hc).isPreconnected
    (hscaledAn.continuousOn.mono inter_subset_left)
    (hg₁.continuousOn.mono inter_subset_right)
    (fun s hs => by
      intro hzero
      have hpow := hg₁pow s hs.2
      rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
      exact (xi_ne_zero_of_one_lt_re (mem_farHalf.mp hs.2)) hpow.symm)
    (fun s hs => by rw [hroot s hs.1, hg₁pow s hs.2])
    ⟨haCusp, haFar⟩ hmatch

theorem exists_xi_littlewoodZeroFreeLowerCusp_extension_of_farHalf_root
    {c : ℝ} (hc : 0 < c)
    (hzf : ∀ β t : ℝ, 9 ≤ |t| → β ≤ 1 →
      1 - c * Real.log (Real.log |t|) / Real.log |t| < β →
        riemannZeta ((β : ℂ) + (t : ℂ) * I) ≠ 0)
    (k : ℕ) (g₁ : ℂ → ℂ) (hg₁ : AnalyticOnNhd ℂ g₁ farHalf)
    (hg₁pow : ∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (littlewoodZeroFreeLowerCusp c) ∧
        (∀ s ∈ littlewoodZeroFreeLowerCusp c, g s ^ 2 ^ k = xi s) ∧
        EqOn g g₁ (littlewoodZeroFreeLowerCusp c ∩ farHalf) := by
  obtain ⟨g, hg, hgpow⟩ := Bottcher.exists_analyticOnNhd_pow_eq
    (isSimplyConnected_littlewoodZeroFreeLowerCusp c)
    (isOpen_littlewoodZeroFreeLowerCusp c)
    ((xi_analyticOnNhd rightHalf).mono (littlewoodZeroFreeLowerCusp_subset_rightHalf c))
    (fun s hs => xi_ne_zero_on_littlewoodZeroFreeLowerCusp_of_zeroFree hzf hs)
    Nat.one_le_two_pow
  let a : ℂ := 2 - (10 : ℂ) * I
  have haCusp : a ∈ littlewoodZeroFreeLowerCusp c := by
    rw [littlewoodZeroFreeLowerCusp_eq]
    exact ⟨by norm_num [a],
      (littlewoodZeroFreeCuspBoundary_lt_one hc (by norm_num [a])).trans
        (by norm_num [a])⟩
  have haFar : a ∈ farHalf := by rw [mem_farHalf]; norm_num [a]
  have hxia : xi a ≠ 0 := xi_ne_zero_of_one_lt_re (mem_farHalf.mp haFar)
  have hga : g a ≠ 0 := by
    intro hzero
    have hpow := hgpow a haCusp
    rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
    exact hxia hpow.symm
  let omega : ℂ := g₁ a / g a
  have homegaPow : omega ^ 2 ^ k = 1 := by
    change (g₁ a / g a) ^ 2 ^ k = 1
    rw [div_pow, hg₁pow a haFar, hgpow a haCusp, div_self hxia]
  have hroot : ∀ s ∈ littlewoodZeroFreeLowerCusp c,
      (omega * g s) ^ 2 ^ k = xi s := by
    intro s hs
    rw [mul_pow, homegaPow, one_mul, hgpow s hs]
  have hmatch : omega * g a = g₁ a := by
    change (g₁ a / g a) * g a = g₁ a
    rw [div_mul_cancel₀ _ hga]
  have hscaledAn : AnalyticOnNhd ℂ (fun s => omega * g s)
      (littlewoodZeroFreeLowerCusp c) := fun s hs => analyticAt_const.mul (hg s hs)
  refine ⟨fun s => omega * g s, hscaledAn, hroot, ?_⟩
  exact Bottcher.eqOn_of_pow_eq_of_isPreconnected Nat.one_le_two_pow
    (convex_littlewoodZeroFreeLowerCusp_inter_farHalf hc).isPreconnected
    (hscaledAn.continuousOn.mono inter_subset_left)
    (hg₁.continuousOn.mono inter_subset_right)
    (fun s hs => by
      intro hzero
      have hpow := hg₁pow s hs.2
      rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
      exact (xi_ne_zero_of_one_lt_re (mem_farHalf.mp hs.2)) hpow.symm)
    (fun s hs => by rw [hroot s hs.1, hg₁pow s hs.2])
    ⟨haCusp, haFar⟩ hmatch

theorem exists_xi_littlewoodSymmetricZeroFreeCusp_extension_of_farHalf_root_all_levels :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (g₁ : ℂ → ℂ),
      AnalyticOnNhd ℂ g₁ farHalf →
      (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
      ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g (littlewoodSymmetricZeroFreeCusp c) ∧
          (∀ s ∈ littlewoodSymmetricZeroFreeCusp c, g s ^ 2 ^ k = xi s) ∧
          EqOn g g₁ farHalf := by
  obtain ⟨c, hc, hzf⟩ := Sieve.exists_littlewood_zero_free_region_from_nine
  refine ⟨c, hc, fun k g₁ hg₁ hg₁pow => ?_⟩
  obtain ⟨gU, hgU, hgUpow, hgUFar⟩ :=
    exists_xi_littlewoodZeroFreeCusp_extension_of_farHalf_root
      hc hzf k g₁ hg₁ hg₁pow
  obtain ⟨gL, hgL, hgLpow, hgLFar⟩ :=
    exists_xi_littlewoodZeroFreeLowerCusp_extension_of_farHalf_root
      hc hzf k g₁ hg₁ hg₁pow
  obtain ⟨gUF, hgUF, hgUFUpper, hgUFFar⟩ := Bottcher.analyticOnNhd_glue_twoChart
    (isOpen_littlewoodZeroFreeCusp c) isOpen_farHalf hgU hg₁ hgUFar
  have hUFLAgree : EqOn gUF gL
      ((littlewoodZeroFreeCusp c ∪ farHalf) ∩ littlewoodZeroFreeLowerCusp c) := by
    intro s hs
    have hnotUpper : s ∉ littlewoodZeroFreeCusp c := by
      intro hu
      exact Set.disjoint_left.mp (littlewoodZeroFreeCusp_disjoint_lowerCusp c) hu hs.2
    have hfar : s ∈ farHalf := hs.1.resolve_left hnotUpper
    rw [hgUFFar hfar]
    exact (hgLFar ⟨hs.2, hfar⟩).symm
  obtain ⟨g, hg, hgUFg, hgLg⟩ := Bottcher.analyticOnNhd_glue_twoChart
    ((isOpen_littlewoodZeroFreeCusp c).union isOpen_farHalf)
    (isOpen_littlewoodZeroFreeLowerCusp c) hgUF hgL hUFLAgree
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [littlewoodSymmetricZeroFreeCusp] using hg
  · intro s hs
    rw [littlewoodSymmetricZeroFreeCusp] at hs
    rcases hs with hsUF | hsL
    · rw [hgUFg hsUF]
      rcases hsUF with hsU | hsFar
      · rw [hgUFUpper hsU]
        exact hgUpow s hsU
      · rw [hgUFFar hsFar]
        exact hg₁pow s hsFar
    · rw [hgLg hsL]
      exact hgLpow s hsL
  · intro s hs
    have hsUF : s ∈ littlewoodZeroFreeCusp c ∪ farHalf := Or.inr hs
    rw [hgUFg hsUF, hgUFFar hs]

theorem exists_xi_littlewoodSymmetricZeroFreeCusp_arithmetic_extensions_all_levels :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ g₁ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g₁ farHalf ∧
        (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) ∧
        AnalyticOnNhd ℂ g (littlewoodSymmetricZeroFreeCusp c) ∧
        (∀ s ∈ littlewoodSymmetricZeroFreeCusp c, g s ^ 2 ^ k = xi s) ∧
        EqOn g g₁ farHalf := by
  obtain ⟨c, hc, hext⟩ :=
    exists_xi_littlewoodSymmetricZeroFreeCusp_extension_of_farHalf_root_all_levels
  refine ⟨c, hc, fun k => ?_⟩
  obtain ⟨g₁, hg₁, hg₁pow⟩ := exists_farHalf_root k
  obtain ⟨g, hg, hgpow, heq⟩ := hext k g₁ hg₁ hg₁pow
  exact ⟨g₁, g, hg₁, hg₁pow, hg, hgpow, heq⟩

end

end RHTower
