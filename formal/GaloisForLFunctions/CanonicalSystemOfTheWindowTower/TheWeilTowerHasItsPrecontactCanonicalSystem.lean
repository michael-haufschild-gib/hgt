import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheEndpointTracesLieInTheHermiteBiehlerSpan
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelHasItsPolarizedEndpointSlope
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The actual precontact Weil chain has a canonical system

The endpoint trace span and polarized aperture derivative determine the
normalized Hermite–Biehler equation. Its real drift has an integrable
primitive. A reciprocal diagonal gauge yields a nonnegative locally
integrable Hamiltonian and absolutely continuous entire coordinates.

The canonical equations, Christoffel–Darboux identity and Hamiltonian
density all refer to the literal Weil reproducing kernel. The determinant
is retained as an exact trace formula; no normalization to one is assumed.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

private def anchorMass (a : PrecontactAperture) : ℝ :=
  (‖evalVectorLeftTrace a I‖^2+‖evalVectorRightTrace a I‖^2)/(2*‖evalVector a I‖^2)

private def anchorDrift (a : PrecontactAperture) : ℝ :=
  (evalVectorLeftTrace a I).re*(evalVectorRightTrace a I).re/‖evalVector a I‖^2

private theorem leftAnchor_coe (a : PrecontactAperture) :
    ((evalVectorLeftTrace a I).re : ℂ) = evalVectorLeftTrace a I := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, evalVectorLeftTrace_I_im]

private theorem rightAnchor_coe (a : PrecontactAperture) :
    ((evalVectorRightTrace a I).re : ℂ) = evalVectorRightTrace a I := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, evalVectorRightTrace_I_im]

private theorem anchorNorm_pos (a : PrecontactAperture) : 0 < ‖evalVector a I‖^2 :=
  sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero a I))

private theorem leftAnchor_conj (a : PrecontactAperture) :
    (starRingEnd ℂ) (evalVectorLeftTrace a I) = evalVectorLeftTrace a I := by
  calc
    _ = (starRingEnd ℂ) ((evalVectorLeftTrace a I).re : ℂ) :=
      (congrArg (starRingEnd ℂ) (leftAnchor_coe a)).symm
    _ = ((evalVectorLeftTrace a I).re : ℂ) := Complex.conj_ofReal _
    _ = _ := leftAnchor_coe a

private theorem rightAnchor_conj (a : PrecontactAperture) :
    (starRingEnd ℂ) (evalVectorRightTrace a I) = evalVectorRightTrace a I := by
  calc
    _ = (starRingEnd ℂ) ((evalVectorRightTrace a I).re : ℂ) :=
      (congrArg (starRingEnd ℂ) (rightAnchor_coe a)).symm
    _ = ((evalVectorRightTrace a I).re : ℂ) := Complex.conj_ofReal _
    _ = _ := rightAnchor_coe a

private theorem anchorNorms (a : PrecontactAperture) :
    ‖evalVectorLeftTrace a I‖^2 = (evalVectorLeftTrace a I).re^2 ∧
    ‖evalVectorRightTrace a I‖^2 = (evalVectorRightTrace a I).re^2 := by
  constructor
  · rw [Complex.sq_norm, Complex.normSq_apply, evalVectorLeftTrace_I_im]
    ring
  · rw [Complex.sq_norm, Complex.normSq_apply, evalVectorRightTrace_I_im]
    ring

private theorem anchor_plus (a : PrecontactAperture) :
    anchorMass a+anchorDrift a =
      ((evalVectorLeftTrace a I).re+(evalVectorRightTrace a I).re)^2/(2*‖evalVector a I‖^2) := by
  rw [anchorMass, anchorDrift, (anchorNorms a).1, (anchorNorms a).2]
  field_simp [(anchorNorm_pos a).ne']
  ring

private theorem anchor_minus (a : PrecontactAperture) :
    anchorMass a-anchorDrift a =
      ((evalVectorLeftTrace a I).re-(evalVectorRightTrace a I).re)^2/(2*‖evalVector a I‖^2) := by
  rw [anchorMass, anchorDrift, (anchorNorms a).1, (anchorNorms a).2]
  field_simp [(anchorNorm_pos a).ne']
  ring

private theorem anchor_positive (a : PrecontactAperture) :
    0 ≤ anchorMass a+anchorDrift a ∧ 0 ≤ anchorMass a-anchorDrift a := by
  rw [anchor_plus, anchor_minus]
  exact ⟨div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (anchorNorm_pos a).le),
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (anchorNorm_pos a).le)⟩

private theorem anchorFlux (a : PrecontactAperture) (z : ℂ) :
    2*I*(‖evalVector a I‖ : ℂ)^2 *
      ((starRingEnd ℂ) (evalVectorLeftTrace a z)*evalVectorLeftTrace a I+
       (starRingEnd ℂ) (evalVectorRightTrace a z)*evalVectorRightTrace a I) =
      hermiteBiehler a z*(evalVectorLeftTrace a I ^ 2+evalVectorRightTrace a I ^ 2)-
        2*evalVectorLeftTrace a I*evalVectorRightTrace a I*
          (starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z)) := by
  have hl := congrArg (starRingEnd ℂ) (evalVectorLeftTrace_hermiteBiehler_span a z)
  have hr := congrArg (starRingEnd ℂ) (evalVectorRightTrace_hermiteBiehler_span a z)
  have hln : evalVectorLeftTrace a (-I) = evalVectorRightTrace a I :=
    (evalVectorRightTrace_eq_leftTrace_neg a I).symm
  have hrn : evalVectorRightTrace a (-I) = evalVectorLeftTrace a I := by
    rw [evalVectorRightTrace_eq_leftTrace_neg, neg_neg]
  rw [hln] at hl
  rw [hrn] at hr
  simp only [map_mul, map_pow, map_sub, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, starRingEnd_self_apply] at hl hr
  rw [leftAnchor_conj, rightAnchor_conj] at hl hr
  linear_combination -(evalVectorLeftTrace a I)*hl-(evalVectorRightTrace a I)*hr

private theorem anchorCross (a : PrecontactAperture) :
    ((starRingEnd ℂ) (evalVectorLeftTrace a (-I))*evalVectorLeftTrace a I+
      (starRingEnd ℂ) (evalVectorRightTrace a (-I))*evalVectorRightTrace a I).re =
      2*(evalVectorLeftTrace a I).re*(evalVectorRightTrace a I).re := by
  rw [← evalVectorRightTrace_eq_leftTrace_neg a I,
    evalVectorRightTrace_eq_leftTrace_neg a (-I), neg_neg,
    leftAnchor_conj, rightAnchor_conj, Complex.add_re, Complex.mul_re, Complex.mul_re,
    evalVectorLeftTrace_I_im, evalVectorRightTrace_I_im]
  ring

private theorem anchorFlux_equation (a : PrecontactAperture) (z : ℂ) :
    (z+I)*((starRingEnd ℂ) (evalVectorLeftTrace a z)*evalVectorLeftTrace a I+
      (starRingEnd ℂ) (evalVectorRightTrace a z)*evalVectorRightTrace a I) =
    (1-I*z)*((anchorMass a : ℂ)*hermiteBiehler a z-
      (anchorDrift a : ℂ)*(starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z))) := by
  have h := anchorFlux a z
  have hn : (‖evalVector a I‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero a I))
  have hden : 2*I*(‖evalVector a I‖ : ℂ)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (pow_ne_zero 2 hn)
  have hd : (starRingEnd ℂ) (evalVectorLeftTrace a z)*evalVectorLeftTrace a I+
      (starRingEnd ℂ) (evalVectorRightTrace a z)*evalVectorRightTrace a I =
      (hermiteBiehler a z*(evalVectorLeftTrace a I ^ 2+evalVectorRightTrace a I ^ 2)-
        2*evalVectorLeftTrace a I*evalVectorRightTrace a I*
          (starRingEnd ℂ) (hermiteBiehler a ((starRingEnd ℂ) z)))/
        (2*I*(‖evalVector a I‖ : ℂ)^2) := by
    apply (eq_div_iff hden).mpr
    linear_combination h
  rw [hd, anchorMass, anchorDrift, (anchorNorms a).1, (anchorNorms a).2]
  push_cast
  rw [leftAnchor_coe, rightAnchor_coe]
  field_simp [hn, Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

/-- The diagonal endpoint density divided by twice the positive anchor kernel. -/
def precontactCanonicalMass (a : ℝ) : ℝ :=
  (precontactKernelEndpointDensity I I a).re/(2*diagonalEvalGram I a)

/-- The real cross-anchor endpoint density in the same normalization. -/
def precontactCanonicalDrift (a : ℝ) : ℝ :=
  (precontactKernelEndpointDensity I (-I) a).re/(2*diagonalEvalGram I a)

/-- The actual anchored Hermite–Biehler function divided by the norm of its evaluation vector. -/
def normalizedHermiteBiehler (z : ℂ) (a : ℝ) : ℂ :=
  (z+I)*precontactKernel I z a/(Real.sqrt (diagonalEvalGram I a) : ℂ)

/-- The normalized Schwarz reflection, written through the opposite kernel anchor. -/
def normalizedHermiteBiehlerSharp (z : ℂ) (a : ℝ) : ℂ :=
  (z-I)*precontactKernel (-I) z a/(Real.sqrt (diagonalEvalGram I a) : ℂ)

private theorem diagonal_norm {a : ℝ} (ha : a ∈ precontactSet) :
    diagonalEvalGram I a = ‖evalVector (toPrecontact ha) I‖^2 :=
  diagonalEvalGram_eq_norm I (toPrecontact ha)

private theorem diagonal_pos {a : ℝ} (ha : a ∈ precontactSet) :
    0 < diagonalEvalGram I a := by
  rw [diagonal_norm ha]
  exact anchorNorm_pos _

private theorem diagonal_sqrt {a : ℝ} (ha : a ∈ precontactSet) :
    Real.sqrt (diagonalEvalGram I a) = ‖evalVector (toPrecontact ha) I‖ := by
  rw [diagonal_norm ha, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

private theorem precontactMass_eq {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalMass a = anchorMass (toPrecontact ha) := by
  rw [precontactCanonicalMass, precontactKernelEndpointDensity_diagonal_re,
    diagonalEndpointEnergy, dif_pos ha, diagonal_norm ha]
  rfl

private theorem precontactDrift_eq {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalDrift a = anchorDrift (toPrecontact ha) := by
  rw [precontactCanonicalDrift, precontactKernelEndpointDensity, dif_pos ha,
    diagonal_norm ha]
  change ((starRingEnd ℂ) (evalVectorLeftTrace (toPrecontact ha) (-I))*evalVectorLeftTrace (toPrecontact ha) I+
    (starRingEnd ℂ) (evalVectorRightTrace (toPrecontact ha) (-I))*evalVectorRightTrace (toPrecontact ha) I).re /
      (2*‖evalVector (toPrecontact ha) I‖^2) = _
  rw [anchorCross, anchorDrift]
  ring

private theorem precontactMass_positive {a : ℝ} (ha : a ∈ precontactSet) :
    0 ≤ precontactCanonicalMass a+precontactCanonicalDrift a ∧ 0 ≤ precontactCanonicalMass a-precontactCanonicalDrift a := by
  rw [precontactMass_eq ha, precontactDrift_eq ha]
  exact anchor_positive _

private theorem normalizedHB_eq {a : ℝ} (ha : a ∈ precontactSet) (z : ℂ) :
    normalizedHermiteBiehler z a = hermiteBiehler (toPrecontact ha) z /
      (‖evalVector (toPrecontact ha) I‖ : ℂ) := by
  rw [normalizedHermiteBiehler, precontactKernel, dif_pos ha, diagonal_sqrt ha]
  rfl

private theorem normalizedHBSharp_eq {a : ℝ} (ha : a ∈ precontactSet) (z : ℂ) :
    normalizedHermiteBiehlerSharp z a = (starRingEnd ℂ) (hermiteBiehler (toPrecontact ha) ((starRingEnd ℂ) z)) /
      (‖evalVector (toPrecontact ha) I‖ : ℂ) := by
  rw [normalizedHermiteBiehlerSharp, precontactKernel, dif_pos ha, diagonal_sqrt ha,
    hermiteBiehler_sharp]

/-- The opposite-anchor formula is exactly Schwarz reflection. -/
theorem normalizedHermiteBiehlerSharp_eq_conj (z : ℂ) (a : ℝ) :
    normalizedHermiteBiehlerSharp z a = (starRingEnd ℂ) (normalizedHermiteBiehler ((starRingEnd ℂ) z) a) := by
  by_cases ha : a ∈ precontactSet
  · rw [normalizedHBSharp_eq ha, normalizedHB_eq ha, map_div₀, Complex.conj_ofReal]
  · simp only [normalizedHermiteBiehlerSharp, normalizedHermiteBiehler, precontactKernel, dif_neg ha,
      mul_zero, zero_div, map_zero]

/-- The actual normalized Hermite–Biehler function satisfies its aperture equation from the right. -/
theorem hasDerivWithinAt_normalizedHermiteBiehler_right (z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    HasDerivWithinAt (normalizedHermiteBiehler z)
      (-I*z*(precontactCanonicalMass a : ℂ)*normalizedHermiteBiehler z a+
        (I*z-1)*(precontactCanonicalDrift a : ℂ)*normalizedHermiteBiehlerSharp z a) (Ioi a) a := by
  have hq := ((hasDerivWithinAt_diagonalEvalGram_right I ha).sqrt (diagonal_pos ha).ne').ofReal_comp
  have hn : (Real.sqrt (diagonalEvalGram I a) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (diagonal_pos ha)).ne'
  have h := ((hasDerivWithinAt_precontactKernel_right I z ha).const_mul (z+I)).div hq hn
  change HasDerivWithinAt (normalizedHermiteBiehler z) _ (Ioi a) a at h
  convert h using 1
  rw [precontactMass_eq ha, precontactDrift_eq ha, normalizedHB_eq ha,
    normalizedHBSharp_eq ha, precontactKernelEndpointDensity, dif_pos ha,
    precontactKernel, dif_pos ha, diagonalEndpointEnergy, dif_pos ha, diagonal_sqrt ha]
  change _ = ((z+I)*
    ((starRingEnd ℂ) (evalVectorLeftTrace (toPrecontact ha) z)*evalVectorLeftTrace (toPrecontact ha) I+
     (starRingEnd ℂ) (evalVectorRightTrace (toPrecontact ha) z)*evalVectorRightTrace (toPrecontact ha) I)*
       (‖evalVector (toPrecontact ha) I‖ : ℂ)-
     (z+I)*kernel (toPrecontact ha) I z*
       (((‖evalVectorLeftTrace (toPrecontact ha) I‖^2+
          ‖evalVectorRightTrace (toPrecontact ha) I‖^2)/
           (2*‖evalVector (toPrecontact ha) I‖) : ℝ) : ℂ))/
         (‖evalVector (toPrecontact ha) I‖ : ℂ)^2
  rw [anchorFlux_equation, ← hermiteBiehler]
  unfold anchorMass
  push_cast
  have hN : (‖evalVector (toPrecontact ha) I‖ : ℂ) ≠ 0 := by
    simpa only [diagonal_sqrt ha] using hn
  field_simp [hN]
  ring

private theorem reciprocal_diagonal_continuous {a b : ℝ} (hab : a ≤ b)
    (hs : Icc a b ⊆ precontactSet) :
    ContinuousOn (fun x => (2*diagonalEvalGram I x)⁻¹) (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact (continuousOn_const.mul
    (fun x hx => (continuousAt_diagonalEvalGram I (hs hx)).continuousWithinAt)).inv₀
      (fun x hx => mul_ne_zero (by norm_num) (diagonal_pos (hs hx)).ne')

/-- The actual diagonal coefficient is locally integrable before contact. -/
theorem intervalIntegrable_precontactCanonicalMass {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable precontactCanonicalMass volume a b := by
  have hi := intervalIntegrable_precontactKernelEndpointDensity I I hab hs
  have hir : IntervalIntegrable (fun x => (precontactKernelEndpointDensity I I x).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hi.1, Complex.reCLM.integrable_comp hi.2⟩
  unfold precontactCanonicalMass
  simpa only [div_eq_mul_inv, smul_eq_mul] using
    hir.smul_continuousOn (reciprocal_diagonal_continuous hab hs)

/-- Polarized kernel integrability makes the actual drift locally integrable. -/
theorem intervalIntegrable_precontactCanonicalDrift {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable precontactCanonicalDrift volume a b := by
  have hi := intervalIntegrable_precontactKernelEndpointDensity I (-I) hab hs
  have hir : IntervalIntegrable (fun x => (precontactKernelEndpointDensity I (-I) x).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hi.1, Complex.reCLM.integrable_comp hi.2⟩
  unfold precontactCanonicalDrift
  simpa only [div_eq_mul_inv, smul_eq_mul] using
    hir.smul_continuousOn (reciprocal_diagonal_continuous hab hs)

/-- The same aperture equation holds for the ordinary derivative almost everywhere. -/
theorem ae_hasDerivAt_normalizedHermiteBiehler (z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    ∀ᵐ x : ℝ, x ∈ Ioo a b → HasDerivAt (normalizedHermiteBiehler z)
      (-I*z*(precontactCanonicalMass x : ℂ)*normalizedHermiteBiehler z x+
        (I*z-1)*(precontactCanonicalDrift x : ℂ)*normalizedHermiteBiehlerSharp z x) x := by
  filter_upwards [ae_hasDerivAt_precontactKernel I z hab hs,
    ae_hasDerivAt_precontactKernel I I hab hs] with x hx hq hxI
  have hp := hs ⟨hxI.1.le,hxI.2.le⟩
  have hqr : HasDerivAt (diagonalEvalGram I) (precontactKernelEndpointDensity I I x).re x := by
    have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hq hxI)
    simpa only [Function.comp_def, Complex.reCLM_apply, precontactKernel_diagonal_re] using hd
  have hsq := (hqr.sqrt (diagonal_pos hp).ne').ofReal_comp
  have hn : (Real.sqrt (diagonalEvalGram I x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (diagonal_pos hp)).ne'
  have hf := (((hx hxI).const_mul (z+I)).div hsq hn).differentiableAt
  change DifferentiableAt ℝ (normalizedHermiteBiehler z) x at hf
  have he := (hf.derivWithin (uniqueDiffWithinAt_Ioi x)).symm.trans
    ((hasDerivWithinAt_normalizedHermiteBiehler_right z hp).derivWithin (uniqueDiffWithinAt_Ioi x))
  simpa only [he] using hf.hasDerivAt

private theorem ac_comp_lipschitz {f g : ℝ → ℝ} {a b c d : ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g (Icc c d))
    (hm : MapsTo f (uIcc a b) (Icc c d)) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  have hK : 0 < (K : ℝ)+1 := add_pos_of_nonneg_of_pos K.coe_nonneg zero_lt_one
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hf (ε/((K : ℝ)+1)) (div_pos hε hK)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  calc
    (∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))) ≤
        (K : ℝ)*(∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => hg.dist_le_mul
        _ (hm (hE.1 i hi).1) _ (hm (hE.1 i hi).2)
    _ ≤ ((K : ℝ)+1)*(∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Finset.sum_nonneg fun _ _ => dist_nonneg)
    _ < ((K : ℝ)+1)*(ε/((K : ℝ)+1)) := mul_lt_mul_of_pos_left (hb E hE hlen) hK
    _ = ε := by field_simp [hK.ne']

private theorem ac_comp_contDiff {f g : ℝ → ℝ} {a b c d : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : ContDiffOn ℝ 1 g (Icc c d))
    (hm : MapsTo f (uIcc a b) (Icc c d)) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  obtain ⟨K, hK⟩ := hg.exists_lipschitzOnWith (by norm_num) (convex_Icc c d) isCompact_Icc
  exact ac_comp_lipschitz hf hK hm

private theorem inverseNorm_ac {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (fun x => (Real.sqrt (diagonalEvalGram I x))⁻¹) a b := by
  have ha := hs ⟨le_rfl,hab⟩
  have hb := hs ⟨hab,le_rfl⟩
  have hlo := diagonal_pos ha
  have hg : ContDiffOn ℝ 1 (fun t : ℝ => (Real.sqrt t)⁻¹)
      (Icc (diagonalEvalGram I a) (diagonalEvalGram I b)) := by
    have hi : ContDiffOn ℝ 1 (fun t : ℝ => t)
        (Icc (diagonalEvalGram I a) (diagonalEvalGram I b)) := contDiffOn_id
    exact (hi.sqrt (fun t ht => (hlo.trans_le ht.1).ne')).inv
      (fun t ht => (Real.sqrt_pos.mpr (hlo.trans_le ht.1)).ne')
  have hm : MapsTo (diagonalEvalGram I) (uIcc a b)
      (Icc (diagonalEvalGram I a) (diagonalEvalGram I b)) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ⟨monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => I) ha (hs hx) hx.1,
      monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => I) (hs hx) hb hx.2⟩
  exact ac_comp_contDiff (f := diagonalEvalGram I) (g := fun t : ℝ => (Real.sqrt t)⁻¹)
    (absolutelyContinuousOnInterval_diagonalEvalGram I hab hs) hg hm

/-- Positive compact anchor bounds preserve absolute continuity under normalization. -/
theorem absolutelyContinuousOnInterval_normalizedHermiteBiehler (z : ℂ) {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (normalizedHermiteBiehler z) a b := by
  have h := (inverseNorm_ac hab hs).smul
    ((absolutelyContinuousOnInterval_precontactKernel I z hab hs).const_smul (z+I))
  have he : normalizedHermiteBiehler z =
      (fun x => (Real.sqrt (diagonalEvalGram I x))⁻¹) •
        (fun x => (z+I) • precontactKernel I z x) := by
    funext x
    change (z+I)*precontactKernel I z x/(Real.sqrt (diagonalEvalGram I x) : ℂ) =
      (Real.sqrt (diagonalEvalGram I x))⁻¹ • ((z+I) • precontactKernel I z x)
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
    ring
  rw [he]
  exact h

/-- The normalized opposite-anchor coordinate is locally absolutely continuous. -/
theorem absolutelyContinuousOnInterval_normalizedHermiteBiehlerSharp (z : ℂ) {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (normalizedHermiteBiehlerSharp z) a b := by
  have h := (inverseNorm_ac hab hs).smul
    ((absolutelyContinuousOnInterval_precontactKernel (-I) z hab hs).const_smul (z-I))
  have he : normalizedHermiteBiehlerSharp z =
      (fun x => (Real.sqrt (diagonalEvalGram I x))⁻¹) •
        (fun x => (z-I) • precontactKernel (-I) z x) := by
    funext x
    change (z-I)*precontactKernel (-I) z x/(Real.sqrt (diagonalEvalGram I x) : ℂ) =
      (Real.sqrt (diagonalEvalGram I x))⁻¹ • ((z-I) • precontactKernel (-I) z x)
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
    ring
  rw [he]
  exact h

/-- The real entire imaginary component of the normalized Hermite–Biehler pair. -/
def normalizedCanonicalA (z : ℂ) (a : ℝ) : ℂ :=
  (normalizedHermiteBiehler z a-normalizedHermiteBiehlerSharp z a)/(2*I)

/-- The real entire real component of the normalized Hermite–Biehler pair. -/
def normalizedCanonicalB (z : ℂ) (a : ℝ) : ℂ :=
  (normalizedHermiteBiehler z a+normalizedHermiteBiehlerSharp z a)/2

/-- The primitive of the actual cross-anchor drift from a fixed aperture. -/
def precontactCanonicalGauge (base a : ℝ) : ℝ := ∫ x in base..a, precontactCanonicalDrift x

/-- The first canonical coordinate after removing the spectral-parameter-free drift. -/
def canonicalSolutionA (base : ℝ) (z : ℂ) (a : ℝ) : ℂ :=
  (Real.exp (-precontactCanonicalGauge base a) : ℂ)*normalizedCanonicalA z a

/-- The second canonical coordinate with the reciprocal diagonal gauge. -/
def canonicalSolutionB (base : ℝ) (z : ℂ) (a : ℝ) : ℂ :=
  (Real.exp (precontactCanonicalGauge base a) : ℂ)*normalizedCanonicalB z a

/-- The first diagonal Hamiltonian entry, defined from the actual endpoint traces. -/
def canonicalHamiltonianOne (base a : ℝ) : ℝ :=
  (precontactCanonicalMass a+precontactCanonicalDrift a)*Real.exp (2*precontactCanonicalGauge base a)

/-- The second diagonal Hamiltonian entry in the reciprocal gauge. -/
def canonicalHamiltonianTwo (base a : ℝ) : ℝ :=
  (precontactCanonicalMass a-precontactCanonicalDrift a)*Real.exp (-2*precontactCanonicalGauge base a)

/-- Both actual Hamiltonian entries are nonnegative squares times positive gauge factors. -/
theorem canonicalHamiltonian_nonneg (base : ℝ) {a : ℝ} (ha : a ∈ precontactSet) :
    0 ≤ canonicalHamiltonianOne base a ∧ 0 ≤ canonicalHamiltonianTwo base a := by
  exact ⟨mul_nonneg (precontactMass_positive ha).1 (Real.exp_pos _).le,
    mul_nonneg (precontactMass_positive ha).2 (Real.exp_pos _).le⟩

private theorem canonicalA_ac (z : ℂ) {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (normalizedCanonicalA z) a b := by
  have h := ((absolutelyContinuousOnInterval_normalizedHermiteBiehler z hab hs).sub (absolutelyContinuousOnInterval_normalizedHermiteBiehlerSharp z hab hs)).const_smul
    ((2*I)⁻¹ : ℂ)
  have he : normalizedCanonicalA z = (fun x => ((2*I)⁻¹ : ℂ) • (normalizedHermiteBiehler z - normalizedHermiteBiehlerSharp z) x) := by
    funext x
    simp only [normalizedCanonicalA, smul_eq_mul, Pi.sub_apply]
    ring
  rw [he]
  exact h

private theorem canonicalB_ac (z : ℂ) {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (normalizedCanonicalB z) a b := by
  have h := ((absolutelyContinuousOnInterval_normalizedHermiteBiehler z hab hs).add (absolutelyContinuousOnInterval_normalizedHermiteBiehlerSharp z hab hs)).const_smul
    (1/2 : ℂ)
  have he : normalizedCanonicalB z = (fun x => (1/2 : ℂ) • (normalizedHermiteBiehler z + normalizedHermiteBiehlerSharp z) x) := by
    funext x
    simp only [normalizedCanonicalB, smul_eq_mul, Pi.add_apply]
    ring
  rw [he]
  exact h

private theorem normalizedSharp_ae_equation (z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    ∀ᵐ x : ℝ, x ∈ Ioo a b → HasDerivAt (normalizedHermiteBiehlerSharp z)
      (I*z*(precontactCanonicalMass x : ℂ)*normalizedHermiteBiehlerSharp z x+
        (-I*z-1)*(precontactCanonicalDrift x : ℂ)*normalizedHermiteBiehler z x) x := by
  filter_upwards [ae_hasDerivAt_normalizedHermiteBiehler ((starRingEnd ℂ) z) hab hs] with x hx hxI
  have h := (hx hxI).star
  change HasDerivAt (fun t => (starRingEnd ℂ) (normalizedHermiteBiehler ((starRingEnd ℂ) z) t))
    ((starRingEnd ℂ) _) x at h
  have hf : (fun t => (starRingEnd ℂ) (normalizedHermiteBiehler ((starRingEnd ℂ) z) t)) =
      normalizedHermiteBiehlerSharp z := funext fun t => (normalizedHermiteBiehlerSharp_eq_conj z t).symm
  rw [hf] at h
  have hss : (starRingEnd ℂ) (normalizedHermiteBiehlerSharp ((starRingEnd ℂ) z) x) = normalizedHermiteBiehler z x := by
    rw [normalizedHermiteBiehlerSharp_eq_conj, starRingEnd_self_apply, starRingEnd_self_apply]
  simpa only [map_add, map_mul, map_sub, map_neg, map_one, Complex.conj_I,
    Complex.conj_ofReal, starRingEnd_self_apply, neg_neg, ← normalizedHermiteBiehlerSharp_eq_conj, hss] using h

private theorem pair_ae_equations (z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    ∀ᵐ x : ℝ, x ∈ Ioo a b →
      HasDerivAt (normalizedCanonicalA z)
        ((precontactCanonicalDrift x : ℂ)*normalizedCanonicalA z x-z*((precontactCanonicalMass x-precontactCanonicalDrift x : ℝ) : ℂ)*normalizedCanonicalB z x) x ∧
      HasDerivAt (normalizedCanonicalB z)
        (-(precontactCanonicalDrift x : ℂ)*normalizedCanonicalB z x+z*((precontactCanonicalMass x+precontactCanonicalDrift x : ℝ) : ℂ)*normalizedCanonicalA z x) x := by
  filter_upwards [ae_hasDerivAt_normalizedHermiteBiehler z hab hs, normalizedSharp_ae_equation z hab hs]
    with x hx hy hxI
  constructor
  · have h := ((hx hxI).sub (hy hxI)).div_const (2*I)
    change HasDerivAt (normalizedCanonicalA z) _ x at h
    convert h using 1
    simp only [normalizedCanonicalA, normalizedCanonicalB, Complex.ofReal_sub]
    field_simp [Complex.I_ne_zero]
    ring
  · have h := ((hx hxI).add (hy hxI)).div_const 2
    change HasDerivAt (normalizedCanonicalB z) _ x at h
    convert h using 1
    simp only [normalizedCanonicalA, normalizedCanonicalB, Complex.ofReal_add]
    field_simp [Complex.I_ne_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring

private theorem exp_ac {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨M,hM⟩ := hf.exists_bound
  apply ac_comp_contDiff (c := -M) (d := M) hf Real.contDiff_exp.contDiffOn
  intro x hx
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hM x hx)

private theorem gauge_ac {base a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet)
    (hbase : base ∈ Icc a b) :
    AbsolutelyContinuousOnInterval (precontactCanonicalGauge base) a b := by
  exact (intervalIntegrable_precontactCanonicalDrift hab hs).absolutelyContinuousOnInterval_intervalIntegral
    (by simpa only [uIcc_of_le hab] using hbase)

/-- The first canonical coordinate is absolutely continuous on compact precontact intervals containing its base. -/
theorem absolutelyContinuousOnInterval_canonicalSolutionA (z : ℂ) {base a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet)
    (hbase : base ∈ Icc a b) :
    AbsolutelyContinuousOnInterval (canonicalSolutionA base z) a b := by
  have h := (exp_ac (gauge_ac hab hs hbase).neg).smul (canonicalA_ac z hab hs)
  have he : canonicalSolutionA base z = (fun x => Real.exp (-precontactCanonicalGauge base x)) • normalizedCanonicalA z := by
    funext x
    rfl
  rw [he]
  exact h

/-- The second canonical coordinate has the same local absolute continuity. -/
theorem absolutelyContinuousOnInterval_canonicalSolutionB (z : ℂ) {base a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet)
    (hbase : base ∈ Icc a b) :
    AbsolutelyContinuousOnInterval (canonicalSolutionB base z) a b := by
  have h := (exp_ac (gauge_ac hab hs hbase)).smul (canonicalB_ac z hab hs)
  have he : canonicalSolutionB base z = (fun x => Real.exp (precontactCanonicalGauge base x)) • normalizedCanonicalB z := by
    funext x
    rfl
  rw [he]
  exact h

/-- Both actual Hamiltonian entries are integrable on compact precontact intervals containing the base. -/
theorem intervalIntegrable_canonicalHamiltonian {base a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet)
    (hbase : base ∈ Icc a b) :
    IntervalIntegrable (canonicalHamiltonianOne base) volume a b ∧
      IntervalIntegrable (canonicalHamiltonianTwo base) volume a b := by
  have hc := (gauge_ac hab hs hbase).continuousOn
  constructor
  · unfold canonicalHamiltonianOne
    simpa only [smul_eq_mul, Function.comp_def, Pi.mul_apply] using
      ((intervalIntegrable_precontactCanonicalMass hab hs).add (intervalIntegrable_precontactCanonicalDrift hab hs)).smul_continuousOn
        (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hc))
  · unfold canonicalHamiltonianTwo
    simpa only [smul_eq_mul, Function.comp_def, Pi.mul_apply] using
      ((intervalIntegrable_precontactCanonicalMass hab hs).sub (intervalIntegrable_precontactCanonicalDrift hab hs)).smul_continuousOn
        (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hc))

/-- The actual Weil chain satisfies A′ = −z h₂ B and B′ = z h₁ A almost everywhere. -/
theorem ae_canonicalSystem_equations (z : ℂ) {base a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) (hbase : base ∈ Icc a b) :
    ∀ᵐ x : ℝ, x ∈ Ioo a b →
      HasDerivAt (canonicalSolutionA base z) (-z*(canonicalHamiltonianTwo base x : ℂ)*canonicalSolutionB base z x) x ∧
      HasDerivAt (canonicalSolutionB base z) (z*(canonicalHamiltonianOne base x : ℂ)*canonicalSolutionA base z x) x := by
  filter_upwards [pair_ae_equations z hab hs,
    (intervalIntegrable_precontactCanonicalDrift hab hs).ae_hasDerivAt_integral] with x hx hθ hxI
  have hxi : x ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ⟨hxI.1.le,hxI.2.le⟩
  have hbi : base ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hbase
  have hd : HasDerivAt (precontactCanonicalGauge base) (precontactCanonicalDrift x) x := hθ hxi base hbi
  constructor
  · have h := (hd.neg.exp.ofReal_comp).mul (hx hxI).1
    change HasDerivAt (canonicalSolutionA base z) _ x at h
    convert h using 1
    have he : (Real.exp (-2*precontactCanonicalGauge base x) : ℂ)*
        (Real.exp (precontactCanonicalGauge base x) : ℂ) = (Real.exp (-precontactCanonicalGauge base x) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    simp only [canonicalHamiltonianTwo, canonicalSolutionB, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_sub]
    linear_combination -z*((precontactCanonicalMass x : ℂ)-(precontactCanonicalDrift x : ℂ))*normalizedCanonicalB z x*he
  · have h := (hd.exp.ofReal_comp).mul (hx hxI).2
    change HasDerivAt (canonicalSolutionB base z) _ x at h
    convert h using 1
    have he : (Real.exp (2*precontactCanonicalGauge base x) : ℂ)*
        (Real.exp (-precontactCanonicalGauge base x) : ℂ) = (Real.exp (precontactCanonicalGauge base x) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    simp only [canonicalHamiltonianOne, canonicalSolutionA, Complex.ofReal_mul, Complex.ofReal_add]
    linear_combination z*((precontactCanonicalMass x : ℂ)+(precontactCanonicalDrift x : ℂ))*normalizedCanonicalA z x*he

private theorem normalized_cd (w z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    normalizedHermiteBiehler z a*(starRingEnd ℂ) (normalizedHermiteBiehler w a)-
      normalizedHermiteBiehlerSharp z a*(starRingEnd ℂ) (normalizedHermiteBiehlerSharp w a) =
      2*I*((starRingEnd ℂ) w-z)*precontactKernel w z a := by
  have h := kernel_christoffelDarboux (toPrecontact ha) w z
  have hN : (‖evalVector (toPrecontact ha) I‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero _ _))
  rw [normalizedHB_eq ha, normalizedHB_eq ha, normalizedHBSharp_eq ha,
    normalizedHBSharp_eq ha, precontactKernel, dif_pos ha]
  simp only [map_div₀, Complex.conj_ofReal, starRingEnd_self_apply]
  field_simp [hN]
  linear_combination h

private theorem pair_cd (w z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    ((starRingEnd ℂ) w-z)*precontactKernel w z a =
      normalizedCanonicalA z a*(starRingEnd ℂ) (normalizedCanonicalB w a)-
        normalizedCanonicalB z a*(starRingEnd ℂ) (normalizedCanonicalA w a) := by
  have h := normalized_cd w z ha
  have he : 2*I*(normalizedCanonicalA z a*(starRingEnd ℂ) (normalizedCanonicalB w a)-
      normalizedCanonicalB z a*(starRingEnd ℂ) (normalizedCanonicalA w a)) =
      normalizedHermiteBiehler z a*(starRingEnd ℂ) (normalizedHermiteBiehler w a)-
        normalizedHermiteBiehlerSharp z a*(starRingEnd ℂ) (normalizedHermiteBiehlerSharp w a) := by
    simp only [normalizedCanonicalA, normalizedCanonicalB, map_div₀, map_mul, map_sub, map_add,
      map_ofNat, Complex.conj_I]
    field_simp [Complex.I_ne_zero]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero)
  linear_combination -h-he

/-- The canonical coordinates reconstruct the literal polarized Weil kernel, including coincident parameters. -/
theorem canonicalSystem_christoffelDarboux (base : ℝ) (w z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    ((starRingEnd ℂ) w-z)*precontactKernel w z a =
      canonicalSolutionA base z a*(starRingEnd ℂ) (canonicalSolutionB base w a)-
        canonicalSolutionB base z a*(starRingEnd ℂ) (canonicalSolutionA base w a) := by
  rw [pair_cd w z ha]
  have he : (Real.exp (-precontactCanonicalGauge base a) : ℂ)*
      (Real.exp (precontactCanonicalGauge base a) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  simp only [canonicalSolutionA, canonicalSolutionB, map_mul, Complex.conj_ofReal]
  linear_combination -(normalizedCanonicalA z a*(starRingEnd ℂ) (normalizedCanonicalB w a)-
    normalizedCanonicalB z a*(starRingEnd ℂ) (normalizedCanonicalA w a))*he

/-- The actual left endpoint trace is the explicit real-anchor readout of the normalized entire pair. -/
theorem evalVectorLeftTrace_canonical_readout (z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    evalVectorLeftTrace (toPrecontact ha) z =
      (((evalVectorLeftTrace (toPrecontact ha) I).re+(evalVectorRightTrace (toPrecontact ha) I).re)/
        (2*‖evalVector (toPrecontact ha) I‖) : ℝ) * (starRingEnd ℂ) (normalizedCanonicalA z a)+
      I*((((evalVectorLeftTrace (toPrecontact ha) I).re-(evalVectorRightTrace (toPrecontact ha) I).re)/
        (2*‖evalVector (toPrecontact ha) I‖) : ℝ) : ℂ) * (starRingEnd ℂ) (normalizedCanonicalB z a) := by
  have hn : (‖evalVector (toPrecontact ha) I‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero _ _))
  have hden : 2*I*(‖evalVector (toPrecontact ha) I‖ : ℂ)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (pow_ne_zero 2 hn)
  have ht := evalVectorLeftTrace_hermiteBiehler_span (toPrecontact ha) z
  rw [← evalVectorRightTrace_eq_leftTrace_neg (toPrecontact ha) I] at ht
  have hτ : evalVectorLeftTrace (toPrecontact ha) z =
      (hermiteBiehler (toPrecontact ha) ((starRingEnd ℂ) z)*evalVectorRightTrace (toPrecontact ha) I-
       (starRingEnd ℂ) (hermiteBiehler (toPrecontact ha) z)*evalVectorLeftTrace (toPrecontact ha) I)/
       (2*I*(‖evalVector (toPrecontact ha) I‖ : ℂ)^2) := by
    apply (eq_div_iff hden).mpr
    linear_combination ht
  rw [hτ, normalizedCanonicalA, normalizedCanonicalB, normalizedHB_eq ha, normalizedHBSharp_eq ha]
  simp only [map_div₀, map_sub, map_add, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, starRingEnd_self_apply]
  push_cast
  rw [leftAnchor_coe, rightAnchor_coe]
  field_simp [hn, Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The right endpoint has the same first readout and opposite second readout. -/
theorem evalVectorRightTrace_canonical_readout (z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    evalVectorRightTrace (toPrecontact ha) z =
      (((evalVectorLeftTrace (toPrecontact ha) I).re+(evalVectorRightTrace (toPrecontact ha) I).re)/
        (2*‖evalVector (toPrecontact ha) I‖) : ℝ) * (starRingEnd ℂ) (normalizedCanonicalA z a)-
      I*((((evalVectorLeftTrace (toPrecontact ha) I).re-(evalVectorRightTrace (toPrecontact ha) I).re)/
        (2*‖evalVector (toPrecontact ha) I‖) : ℝ) : ℂ) * (starRingEnd ℂ) (normalizedCanonicalB z a) := by
  have hn : (‖evalVector (toPrecontact ha) I‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero _ _))
  have hden : 2*I*(‖evalVector (toPrecontact ha) I‖ : ℂ)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (pow_ne_zero 2 hn)
  have ht := evalVectorRightTrace_hermiteBiehler_span (toPrecontact ha) z
  rw [evalVectorRightTrace_eq_leftTrace_neg (toPrecontact ha) (-I), neg_neg] at ht
  have hτ : evalVectorRightTrace (toPrecontact ha) z =
      (hermiteBiehler (toPrecontact ha) ((starRingEnd ℂ) z)*evalVectorLeftTrace (toPrecontact ha) I-
       (starRingEnd ℂ) (hermiteBiehler (toPrecontact ha) z)*evalVectorRightTrace (toPrecontact ha) I)/
       (2*I*(‖evalVector (toPrecontact ha) I‖ : ℂ)^2) := by
    apply (eq_div_iff hden).mpr
    linear_combination ht
  rw [hτ, normalizedCanonicalA, normalizedCanonicalB, normalizedHB_eq ha, normalizedHBSharp_eq ha]
  simp only [map_div₀, map_sub, map_add, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, starRingEnd_self_apply]
  push_cast
  rw [leftAnchor_coe, rightAnchor_coe]
  field_simp [hn, Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem pair_trace_polarization (α β : ℝ) (A B C D : ℂ) :
    (starRingEnd ℂ) ((α : ℂ)*(starRingEnd ℂ) A+I*(β : ℂ)*(starRingEnd ℂ) B)*
        ((α : ℂ)*(starRingEnd ℂ) C+I*(β : ℂ)*(starRingEnd ℂ) D)+
      (starRingEnd ℂ) ((α : ℂ)*(starRingEnd ℂ) A-I*(β : ℂ)*(starRingEnd ℂ) B)*
        ((α : ℂ)*(starRingEnd ℂ) C-I*(β : ℂ)*(starRingEnd ℂ) D) =
      2*(α : ℂ)^2*A*(starRingEnd ℂ) C+2*(β : ℂ)^2*B*(starRingEnd ℂ) D := by
  simp only [map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal,
    starRingEnd_self_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem pair_density (w z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    precontactKernelEndpointDensity w z a =
      ((precontactCanonicalMass a+precontactCanonicalDrift a : ℝ) : ℂ)*normalizedCanonicalA z a*(starRingEnd ℂ) (normalizedCanonicalA w a)+
      ((precontactCanonicalMass a-precontactCanonicalDrift a : ℝ) : ℂ)*normalizedCanonicalB z a*(starRingEnd ℂ) (normalizedCanonicalB w a) := by
  rw [precontactKernelEndpointDensity, dif_pos ha]
  change (starRingEnd ℂ) (evalVectorLeftTrace (toPrecontact ha) z)*evalVectorLeftTrace (toPrecontact ha) w+
    (starRingEnd ℂ) (evalVectorRightTrace (toPrecontact ha) z)*evalVectorRightTrace (toPrecontact ha) w = _
  rw [evalVectorLeftTrace_canonical_readout z ha, evalVectorLeftTrace_canonical_readout w ha,
    evalVectorRightTrace_canonical_readout z ha, evalVectorRightTrace_canonical_readout w ha, pair_trace_polarization,
    precontactMass_eq ha, precontactDrift_eq ha, anchor_plus, anchor_minus]
  push_cast
  have hn : (‖evalVector (toPrecontact ha) I‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero _ _))
  field_simp [hn]

/-- The Hamiltonian quadratic kernel is exactly the two-trace density of the literal Weil kernel. -/
theorem precontactKernelEndpointDensity_eq_canonicalHamiltonian (base : ℝ) (w z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    precontactKernelEndpointDensity w z a =
      (canonicalHamiltonianOne base a : ℂ)*canonicalSolutionA base z a*(starRingEnd ℂ) (canonicalSolutionA base w a)+
      (canonicalHamiltonianTwo base a : ℂ)*canonicalSolutionB base z a*(starRingEnd ℂ) (canonicalSolutionB base w a) := by
  rw [pair_density w z ha]
  have he₁ : (Real.exp (2*precontactCanonicalGauge base a) : ℂ)*
      (Real.exp (-precontactCanonicalGauge base a) : ℂ)^2 = 1 := by
    rw [pow_two, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    convert (Complex.ofReal_one : ((1 : ℝ) : ℂ) = 1) using 1
    congr 1
    convert Real.exp_zero using 1
    congr 1
    ring
  have he₂ : (Real.exp (-2*precontactCanonicalGauge base a) : ℂ)*
      (Real.exp (precontactCanonicalGauge base a) : ℂ)^2 = 1 := by
    rw [pow_two, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    convert (Complex.ofReal_one : ((1 : ℝ) : ℂ) = 1) using 1
    congr 1
    convert Real.exp_zero using 1
    congr 1
    ring
  simp only [canonicalHamiltonianOne, canonicalHamiltonianTwo, canonicalSolutionA, canonicalSolutionB, map_mul,
    Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub]
  linear_combination
    -((precontactCanonicalMass a : ℂ)+(precontactCanonicalDrift a : ℂ))*normalizedCanonicalA z a*(starRingEnd ℂ) (normalizedCanonicalA w a)*he₁-
    ((precontactCanonicalMass a : ℂ)-(precontactCanonicalDrift a : ℂ))*normalizedCanonicalB z a*(starRingEnd ℂ) (normalizedCanonicalB w a)*he₂

private theorem normalizedHB_I {a : ℝ} (ha : a ∈ precontactSet) :
    normalizedHermiteBiehler I a = 2*I*(‖evalVector (toPrecontact ha) I‖ : ℂ) := by
  have hq : precontactKernel I I a = (‖evalVector (toPrecontact ha) I‖ : ℂ)^2 := by
    rw [precontactKernel, dif_pos ha]
    exact evalVector_self _ _
  have hn : (‖evalVector (toPrecontact ha) I‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero _ _))
  rw [normalizedHermiteBiehler, hq, diagonal_sqrt ha]
  field_simp [hn]
  ring

private theorem normalizedHBSharp_I (a : ℝ) : normalizedHermiteBiehlerSharp I a = 0 := by
  simp only [normalizedHermiteBiehlerSharp, sub_self, zero_mul, zero_div]

/-- The gauge is the identity at its base, fixing both canonical anchor values. -/
theorem canonicalSystem_base_anchor {base : ℝ} (hbase : base ∈ precontactSet) :
    canonicalSolutionA base I base = (‖evalVector (toPrecontact hbase) I‖ : ℂ) ∧
      canonicalSolutionB base I base = I*(‖evalVector (toPrecontact hbase) I‖ : ℂ) := by
  simp only [canonicalSolutionA, canonicalSolutionB, precontactCanonicalGauge, intervalIntegral.integral_same,
    neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul, normalizedCanonicalA, normalizedCanonicalB,
    normalizedHB_I hbase, normalizedHBSharp_I, add_zero, sub_zero]
  constructor
  · field_simp [Complex.I_ne_zero]
  · ring

private theorem normalized_differentiable {a : ℝ} (ha : a ∈ precontactSet) :
    Differentiable ℂ (fun z => normalizedHermiteBiehler z a) := by
  have he : (fun z => normalizedHermiteBiehler z a) =
      fun z => hermiteBiehler (toPrecontact ha) z/(‖evalVector (toPrecontact ha) I‖ : ℂ) :=
    funext (normalizedHB_eq ha)
  rw [he]
  exact (differentiable_hermiteBiehler _).div_const _

private theorem normalizedSharp_differentiable {a : ℝ} (ha : a ∈ precontactSet) :
    Differentiable ℂ (fun z => normalizedHermiteBiehlerSharp z a) := by
  have he : (fun z => normalizedHermiteBiehlerSharp z a) =
      fun z => (z-I)*kernel (toPrecontact ha) (-I) z/(‖evalVector (toPrecontact ha) I‖ : ℂ) := by
    funext z
    rw [normalizedHBSharp_eq ha, hermiteBiehler_sharp]
  rw [he]
  exact ((differentiable_id.sub_const I).mul (differentiable_fourier _ (evalVector _ (-I)))).div_const _

/-- Both canonical coordinates are entire in the spectral parameter at each precontact aperture. -/
theorem differentiable_canonicalSolution (base : ℝ) {a : ℝ} (ha : a ∈ precontactSet) :
    Differentiable ℂ (fun z => canonicalSolutionA base z a) ∧
      Differentiable ℂ (fun z => canonicalSolutionB base z a) := by
  exact ⟨(((normalized_differentiable ha).sub (normalizedSharp_differentiable ha)).div_const
    (2*I)).const_mul _,
    (((normalized_differentiable ha).add (normalizedSharp_differentiable ha)).div_const
    2).const_mul _⟩

/-- The actual Hamiltonian determinant is the square of the normalized difference of the two anchor energies. -/
theorem canonicalHamiltonian_determinant {base a : ℝ} (ha : a ∈ precontactSet) :
    canonicalHamiltonianOne base a*canonicalHamiltonianTwo base a =
      ((‖evalVectorLeftTrace (toPrecontact ha) I‖^2-
        ‖evalVectorRightTrace (toPrecontact ha) I‖^2)/(2*diagonalEvalGram I a))^2 := by
  have he : Real.exp (2*precontactCanonicalGauge base a)*Real.exp (-2*precontactCanonicalGauge base a) = 1 := by
    rw [← Real.exp_add]
    rw [show 2*precontactCanonicalGauge base a + -2*precontactCanonicalGauge base a = 0 by ring,
      Real.exp_zero]
  have hg : canonicalHamiltonianOne base a*canonicalHamiltonianTwo base a =
      (precontactCanonicalMass a)^2-(precontactCanonicalDrift a)^2 := by
    unfold canonicalHamiltonianOne canonicalHamiltonianTwo
    linear_combination (precontactCanonicalMass a+precontactCanonicalDrift a)*(precontactCanonicalMass a-precontactCanonicalDrift a)*he
  rw [hg, precontactMass_eq ha, precontactDrift_eq ha, diagonal_norm ha,
    anchorMass, anchorDrift, (anchorNorms (toPrecontact ha)).1, (anchorNorms (toPrecontact ha)).2]
  field_simp [(anchorNorm_pos (toPrecontact ha)).ne']
  ring

#print axioms hasDerivWithinAt_normalizedHermiteBiehler_right
#print axioms intervalIntegrable_precontactCanonicalMass
#print axioms intervalIntegrable_precontactCanonicalDrift
#print axioms canonicalHamiltonian_nonneg
#print axioms absolutelyContinuousOnInterval_canonicalSolutionA
#print axioms absolutelyContinuousOnInterval_canonicalSolutionB
#print axioms intervalIntegrable_canonicalHamiltonian
#print axioms ae_canonicalSystem_equations
#print axioms canonicalSystem_christoffelDarboux
#print axioms precontactKernelEndpointDensity_eq_canonicalHamiltonian
#print axioms canonicalSystem_base_anchor
#print axioms differentiable_canonicalSolution
#print axioms canonicalHamiltonian_determinant
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
