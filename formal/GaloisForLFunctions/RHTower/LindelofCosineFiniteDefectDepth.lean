import GaloisForLFunctions.RHTower.LindelofQuasiRHCosineThreshold
import GaloisForLFunctions.RHTower.XiCosineShiftDeepZeroBudget

/-!
# Finite defects of the cosine family read the essential depth of the zeros

For `h > 0` let `A^h = cos(hD)Ξ = (Ξ(z+ih) + Ξ(z−ih))/2`.  A zero `ρ = β + iγ` of `ξ` has spectral
point `γ + i(½ − β)`; it is `h`-deep when `½ − β > h` (`deepCopies h`).

**Theorem** (`eventually_im_le_of_cosShiftXi_finite_nonreal_of_sparse`).  If the off-line zeros are
sparse in Backlund's sense and `A^h` has only finitely many non-real zeros, then for every `ε > 0`
only finitely many zero copies are `(h + ε)`-deep.

The cluster law `exists_zero_cosShiftXi_of_sparseCluster` places a non-real zero of `A^h` within
`ε/3` of `ζ₀ − ih` for every `(h + ε)`-deep zero `ζ₀` of large height; finitely many non-real zeros
have bounded real part, so deep zeros of large height cannot exist.  Reflection `z ↦ −z̄` moves
deep zeros of large negative ordinate to large positive ordinate.

**Corollary** (`cosShiftXi_finite_nonreal_iff_zerosApproachLine`).  Under the Lindelöf hypothesis,
`A^h` has finitely many non-real zeros for every `h > 0` if and only if the zeros of `ξ` approach
the critical line: for every `h > 0` only finitely many zeros satisfy `β < ½ − h`.  The direction
from the zeros to the cosine family is unconditional (`finite_nonreal_zeros_cosShiftXi`).

Zeros approaching the line are sparse off the line, so by Backlund's theorem they imply LH
(`lindelofCriticalLine_of_zerosApproachLine`), and they imply a zero-free half-plane
(`quasiRH_of_zerosApproachLine`).  Hence, unconditionally
(`zerosApproachLine_iff_lindelof_and_cosShiftXi_finite_nonreal`):

  zeros approach the line  ⟺  LH  ∧  `A^h` has finitely many non-real zeros for every `h > 0`.

The heat deformation `H_t` has finitely many non-real zeros for every `t > 0` unconditionally
(Ki–Kim–Lee), so the heat flow forgets the essential depth of the zeros.  The cosine flow retains
it exactly: under LH its finite-defect threshold
`inf {h > 0 : A^h has finitely many non-real zeros}` equals the essential depth
`inf {h > 0 : only finitely many zeros are h-deep}` (`cosShiftXi_finiteDefect_threshold_iff`).
-/

open Complex

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget

noncomputable section

/-- The zeros of `ξ` approach the critical line: for every `h > 0` only finitely many zero copies
satisfy `β < ½ − h`. -/
def ZerosApproachLine : Prop := ∀ h : ℝ, 0 < h → (deepCopies h).Finite

/-- **Finitely many non-real cosine zeros bound the depth at large height.** -/
theorem eventually_im_le_of_cosShiftXi_finite_nonreal_of_sparse (hsp : OffLineSparse) {h : ℝ}
    (hh : 0 < h) (hfin : {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ q : XiZeroCopy, T ≤ (xiSpectralPoint q).re → (xiSpectralPoint q).im ≤ h + ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨L, c, T₀, hL, hc, hmain⟩ := exists_zero_cosShiftXi_of_sparseCluster hh hε3 hε3
  obtain ⟨T, hT⟩ := hsp (ε / 3) L c hε3 hL hc
  obtain ⟨M, hM⟩ := (hfin.image Complex.re).bddAbove
  refine ⟨max (max T₀ T) (M + ε), fun q₀ hq₀ => ?_⟩
  have hq₀T₀ : T₀ ≤ (xiSpectralPoint q₀).re := (le_max_left _ _).trans ((le_max_left _ _).trans hq₀)
  have hq₀T : T ≤ (xiSpectralPoint q₀).re := (le_max_right _ _).trans ((le_max_left _ _).trans hq₀)
  have hq₀M : M + ε ≤ (xiSpectralPoint q₀).re := (le_max_right _ _).trans hq₀
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨z, hzd, hz, hz0⟩ := hmain q₀ (ε / 3) hε3.le (by linarith) hq₀T₀ (hT _ hq₀T)
  have hzre : (xiSpectralPoint q₀).re - ε / 3 ≤ z.re := by
    have h1 := Complex.abs_re_le_norm (z - (xiSpectralPoint q₀ - h * I))
    have h2 : (z - (xiSpectralPoint q₀ - h * I)).re = z.re - (xiSpectralPoint q₀).re := by simp
    rw [h2] at h1
    linarith [(abs_le.mp (h1.trans hzd)).1]
  have hzM : z.re ≤ M := hM ⟨z, ⟨hz0, by linarith⟩, rfl⟩
  linarith

/-- **Finitely many non-real cosine zeros give finitely many deeper zeros** (under sparsity). -/
theorem deepCopies_finite_of_cosShiftXi_finite_nonreal_of_sparse (hsp : OffLineSparse) {h : ℝ}
    (hh : 0 < h) (hfin : {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite) {ε : ℝ} (hε : 0 < ε) :
    (deepCopies (h + ε)).Finite := by
  obtain ⟨T, hT⟩ := eventually_im_le_of_cosShiftXi_finite_nonreal_of_sparse hsp hh hfin hε
  refine (xiZeroBall (⌈|T| + 1⌉₊)).finite_toSet.subset fun q hq => ?_
  have hq' : h + ε < (xiSpectralPoint q).im := hq
  simp only [Finset.mem_coe, mem_xiZeroBall]
  set z := xiSpectralPoint q with hz
  -- deep copies have ordinate of absolute value below `T`
  have hre : |z.re| < T := by
    rw [abs_lt]
    constructor
    · by_contra hneg
      rw [not_lt] at hneg
      have hboth := xiSpectralPoint_lineConj_symm (xiZeroCopyReflectEquiv.symm q)
      rw [xiSpectralPoint_reflect_symm] at hboth
      have h1 := hT (xiZeroCopyLineConjEquiv.symm (xiZeroCopyReflectEquiv.symm q))
        (by rw [hboth]; simp only [Complex.conj_re, Complex.neg_re]; linarith)
      rw [hboth] at h1
      simp only [Complex.conj_im, Complex.neg_im, neg_neg] at h1
      linarith
    · by_contra hpos
      rw [not_lt] at hpos
      have := hT q hpos
      linarith
  have h1 := Complex.norm_le_abs_re_add_abs_im z
  have h2 := abs_spectral_im_lt_half q
  have h3 : |T| + 1 ≤ (⌈|T| + 1⌉₊ : ℝ) := Nat.le_ceil _
  have h4 : T ≤ |T| := le_abs_self T
  rw [← hz] at h2
  linarith

/-- **Cosine finite defects follow from finitely many deep zeros** (unconditional). -/
theorem cosShiftXi_finite_nonreal_of_deepCopies_finite {h : ℝ} (hS : (deepCopies h).Finite) :
    {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite :=
  (finite_nonreal_zeros_cosShiftXi hS).1

/-- **Zeros approaching the line make every cosine level eventually real** (unconditional). -/
theorem cosShiftXi_finite_nonreal_of_zerosApproachLine (hZ : ZerosApproachLine) {h : ℝ}
    (hh : 0 < h) : {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite :=
  cosShiftXi_finite_nonreal_of_deepCopies_finite (hZ h hh)

/-- **The cosine analogue of Ki–Kim–Lee is equivalent, under LH, to zeros approaching the line.** -/
theorem cosShiftXi_finite_nonreal_iff_zerosApproachLine (hLH : LindelofCriticalLine) :
    (∀ h : ℝ, 0 < h → {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite) ↔ ZerosApproachLine := by
  refine ⟨fun hfin h hh => ?_, fun hZ h hh => cosShiftXi_finite_nonreal_of_zerosApproachLine hZ hh⟩
  have h2 : 0 < h / 2 := by positivity
  have := deepCopies_finite_of_cosShiftXi_finite_nonreal_of_sparse
    (offLineSparse_of_lindelofCriticalLine hLH) h2 (hfin _ h2) h2
  rwa [add_halves] at this

/-- **Under LH the finite-defect threshold of the cosine family is the essential depth.** For
`h₀ ≥ 0`, every level `h > h₀` has finitely many non-real zeros iff every depth `h > h₀` has
finitely many deep zeros. -/
theorem cosShiftXi_finiteDefect_threshold_iff (hLH : LindelofCriticalLine) {h₀ : ℝ}
    (hh₀ : 0 ≤ h₀) :
    (∀ h : ℝ, h₀ < h → {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite) ↔
      ∀ h : ℝ, h₀ < h → (deepCopies h).Finite := by
  refine ⟨fun hfin h hh => ?_, fun hS h hh => cosShiftXi_finite_nonreal_of_deepCopies_finite
    (hS h hh)⟩
  set h' := (h₀ + h) / 2 with hh'
  have hh'0 : 0 < h' := by rw [hh']; linarith
  have hh'h : h₀ < h' := by rw [hh']; linarith
  have hε : 0 < h - h' := by rw [hh']; linarith
  have := deepCopies_finite_of_cosShiftXi_finite_nonreal_of_sparse
    (offLineSparse_of_lindelofCriticalLine hLH) hh'0 (hfin h' hh'h) hε
  rwa [add_sub_cancel] at this

/-- Zeros approaching the line leave only finitely many copies with `|β − ½| > η`. -/
theorem finite_abs_im_gt_of_zerosApproachLine (hZ : ZerosApproachLine) {η : ℝ} (hη : 0 < η) :
    {q : XiZeroCopy | η < |(xiSpectralPoint q).im|}.Finite := by
  refine ((hZ η hη).union ((hZ η hη).preimage
    (xiZeroCopyReflectEquiv.symm.injective.injOn))).subset fun q hq => ?_
  have hq' : η < |(xiSpectralPoint q).im| := hq
  rcases lt_abs.mp hq' with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    show η < (xiSpectralPoint (xiZeroCopyReflectEquiv.symm q)).im
    rw [xiSpectralPoint_reflect_symm, Complex.neg_im]
    exact h1

/-- **Zeros approaching the line are sparse off the line.** -/
theorem offLineSparse_of_zerosApproachLine (hZ : ZerosApproachLine) : OffLineSparse := by
  intro η L c hη hL hc
  obtain ⟨M, hM⟩ := ((finite_abs_im_gt_of_zerosApproachLine hZ hη).image
    fun q => (xiSpectralPoint q).re).bddAbove
  refine ⟨max 1 (M + L + 1), fun t ht G hG => ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htM : M + L + 1 ≤ t := (le_max_right _ _).trans ht
  have hG0 : G = ∅ := Finset.eq_empty_of_forall_notMem fun q hq => by
    obtain ⟨h1, h2⟩ := hG q hq
    have hre : (xiSpectralPoint q).re ≤ M := hM ⟨q, h2, rfl⟩
    have := (abs_le.mp h1).1
    linarith
  rw [hG0, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg hc.le (Real.log_nonneg ht1)

/-- **Zeros approaching the line imply the Lindelöf hypothesis** (Backlund). -/
theorem lindelofCriticalLine_of_zerosApproachLine (hZ : ZerosApproachLine) :
    LindelofCriticalLine :=
  offLineSparse_iff_lindelofCriticalLine.mp (offLineSparse_of_zerosApproachLine hZ)

/-- **Zeros approaching the line imply a zero-free half-plane** `Re s > ½ + α`, `α < ½`. -/
theorem quasiRH_of_zerosApproachLine (hZ : ZerosApproachLine) :
    ∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α := by
  obtain ⟨M, hM⟩ := ((finite_abs_im_gt_of_zerosApproachLine hZ (by norm_num : (0 : ℝ) < 1 / 4)).image
    fun q => |(xiSpectralPoint q).re|).bddAbove
  obtain ⟨Δ, hΔ1, hΔ⟩ := exists_spectral_im_bound_of_re_le M
  refine ⟨max Δ (1 / 4), max_lt hΔ1 (by norm_num), halfPlaneBound_of_abs_spectral_im_le
    fun q => ?_⟩
  by_cases hq : 1 / 4 < |(xiSpectralPoint q).im|
  · exact (hΔ q (hM ⟨q, hq, rfl⟩)).trans (le_max_left _ _)
  · exact (not_lt.mp hq).trans (le_max_right _ _)

/-- **Zeros approach the critical line iff LH holds and every cosine level is eventually real.**
Unconditional: the forward direction is Backlund's theorem plus the deep-zero budget, the converse
is the localized cluster law. -/
theorem zerosApproachLine_iff_lindelof_and_cosShiftXi_finite_nonreal :
    ZerosApproachLine ↔ LindelofCriticalLine ∧
      ∀ h : ℝ, 0 < h → {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite :=
  ⟨fun hZ => ⟨lindelofCriticalLine_of_zerosApproachLine hZ,
      fun _ hh => cosShiftXi_finite_nonreal_of_zerosApproachLine hZ hh⟩,
    fun ⟨hLH, hfin⟩ => (cosShiftXi_finite_nonreal_iff_zerosApproachLine hLH).mp hfin⟩

end

end RHTower.BacklundConverse
