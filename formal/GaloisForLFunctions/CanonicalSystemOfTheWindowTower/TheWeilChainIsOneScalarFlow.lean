import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.AHyperbolicFlowIsRestoring
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilHamiltonianHasDeterminantOne
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelDivergesAtContact

/-!
# The Weil chain is one scalar flow up to contact

Write `K = K_a(i,i)`, `u = τ_L(a,i)`, `v = τ_R(a,i)`. The anchor traces are real and `u² − v² = 2K`,
so `r = v/u` lies in `(−1,1)`. In the variable `L = artanh r`:

* mass `m = (1+r²)/(1−r²) = cosh 2L` and drift `2r/(1−r²) = sinh 2L`, and `(log K)′ = 2m`;
* the Hamiltonian is `H₁ = e^{2Ψ}`, `H₂ = e^{−2Ψ}` with `Ψ = L + θ`, `θ′ = sinh 2L`;
* with `q = Ψ′`: `r′ = (1−r²)q − 2r`, and in integrated form
  `L(y) − L(x) = Ψ(y) − Ψ(x) − ∫_x^y sinh 2L`, valid with no regularity of `r`.

The anchor dominates every other spectral parameter: the energy of the normalized
Hermite–Biehler pair at `z` grows at most as `K^{2|z|+1}`. So a bounded anchor kernel keeps every
kernel bounded (limit-circle transfer), and at finite contact `K(i,i)` itself diverges, which is
`∫ dx/(1−r²) = ∞`. The flow `L′ = q − sinh 2L` is restoring, so `q ∈ L¹` up to contact excludes
contact.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open _root_.RHTower
open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open SquareRootThreshold WindowVisibilityLaw Zeta23

/-- The anchor reflection `r(a) = τ_R(a,i)/τ_L(a,i)`, extended by zero outside precontact. -/
def anchorReflection (a : ℝ) : ℝ :=
  open Classical in
  if h : a ∈ precontactSet then
    (evalVectorRightTrace (toPrecontact h) I).re / (evalVectorLeftTrace (toPrecontact h) I).re
  else 0

/-- The anchor mass ratio `m = (1+r²)/(1−r²)`. -/
def anchorMassRatio (a : ℝ) : ℝ :=
  (1 + anchorReflection a ^ 2) / (1 - anchorReflection a ^ 2)

/-- The canonical potential `Ψ`, defined by `H₁ = e^{2Ψ}`. -/
def canonicalPotential (base a : ℝ) : ℝ := Real.log (canonicalHamiltonianOne base a) / 2

private theorem anchorKernel_pos {a : ℝ} (ha : a ∈ precontactSet) :
    0 < diagonalEvalGram I a := by
  have h : diagonalEvalGram I a = ‖evalVector (toPrecontact ha) I‖ ^ 2 :=
    diagonalEvalGram_eq_norm I (toPrecontact ha)
  rw [h]
  exact sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero _ _))

private theorem anchor_trace_identity {a : ℝ} (ha : a ∈ precontactSet) :
    (evalVectorLeftTrace (toPrecontact ha) I).re ^ 2 -
      (evalVectorRightTrace (toPrecontact ha) I).re ^ 2 = 2 * diagonalEvalGram I a := by
  have h := evalVector_anchorTrace_energy_difference (toPrecontact ha)
  have hq : diagonalEvalGram I a = ‖evalVector (toPrecontact ha) I‖ ^ 2 :=
    diagonalEvalGram_eq_norm I (toPrecontact ha)
  rw [hq, ← h, Complex.sq_norm, Complex.normSq_apply, evalVectorLeftTrace_I_im, Complex.sq_norm,
    Complex.normSq_apply, evalVectorRightTrace_I_im]
  ring

private theorem anchorReflection_eq {a : ℝ} (ha : a ∈ precontactSet) :
    anchorReflection a =
      (evalVectorRightTrace (toPrecontact ha) I).re / (evalVectorLeftTrace (toPrecontact ha) I).re := by
  rw [anchorReflection, dif_pos ha]

/-- The anchor reflection lies strictly inside `(−1,1)` before contact. -/
theorem anchorReflection_mem {a : ℝ} (ha : a ∈ precontactSet) :
    anchorReflection a ∈ Ioo (-1 : ℝ) 1 := by
  rw [anchorReflection_eq ha]
  exact (traceReflection_algebra (anchorKernel_pos ha) (anchor_trace_identity ha)).2.1

private theorem one_sub_sq_pos {a : ℝ} (ha : a ∈ precontactSet) :
    0 < 1 - anchorReflection a ^ 2 := by
  have h := anchorReflection_mem ha
  nlinarith only [h.1, h.2]

private theorem endpointEnergy_anchor (a : PrecontactAperture) :
    evalEndpointEnergy a I =
      (evalVectorLeftTrace a I).re ^ 2 + (evalVectorRightTrace a I).re ^ 2 := by
  change ‖evalVectorLeftTrace a I‖ ^ 2 + ‖evalVectorRightTrace a I‖ ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_apply, evalVectorLeftTrace_I_im, Complex.sq_norm,
    Complex.normSq_apply, evalVectorRightTrace_I_im]
  ring

/-- The diagonal coefficient of the canonical system is the mass ratio of `r`. -/
theorem precontactCanonicalMass_eq_anchorMassRatio {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalMass a = anchorMassRatio a := by
  rw [precontactCanonicalMass, precontactKernelEndpointDensity_diagonal_re,
    diagonalEndpointEnergy, dif_pos ha, endpointEnergy_anchor, anchorMassRatio,
    anchorReflection_eq ha]
  exact (traceReflection_algebra (anchorKernel_pos ha) (anchor_trace_identity ha)).2.2.1

private theorem drift_eq_traces {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalDrift a =
      (evalVectorLeftTrace (toPrecontact ha) I).re * (evalVectorRightTrace (toPrecontact ha) I).re /
        diagonalEvalGram I a := by
  let A := toPrecontact ha
  have hd : (precontactKernelEndpointDensity I (-I) a).re =
      2 * ((evalVectorLeftTrace A I).re * (evalVectorRightTrace A I).re) := by
    rw [precontactKernelEndpointDensity, dif_pos ha]
    change ((starRingEnd ℂ) (evalVectorLeftTrace A (-I)) * evalVectorLeftTrace A I +
      (starRingEnd ℂ) (evalVectorRightTrace A (-I)) * evalVectorRightTrace A I).re = _
    rw [← evalVectorRightTrace_eq_leftTrace_neg A I, evalVectorRightTrace_eq_leftTrace_neg A (-I),
      neg_neg, Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_re,
      Complex.conj_im, Complex.conj_im, evalVectorLeftTrace_I_im, evalVectorRightTrace_I_im]
    ring
  have hK := (anchorKernel_pos ha).ne'
  rw [precontactCanonicalDrift, hd]
  field_simp
  rfl

/-- The drift of the canonical system is `2r/(1−r²)`. -/
theorem precontactCanonicalDrift_eq {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalDrift a = 2 * anchorReflection a / (1 - anchorReflection a ^ 2) := by
  rw [drift_eq_traces ha, anchorReflection_eq ha]
  exact (traceReflection_algebra (anchorKernel_pos ha) (anchor_trace_identity ha)).2.2.2.1

/-- The mass is `cosh 2L`. -/
theorem anchorMassRatio_eq_cosh {a : ℝ} (ha : a ∈ precontactSet) :
    anchorMassRatio a = Real.cosh (2 * Real.artanh (anchorReflection a)) :=
  (cosh_two_mul_artanh (anchorReflection_mem ha)).symm

/-- The drift is `sinh 2L`. -/
theorem precontactCanonicalDrift_eq_sinh {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalDrift a = Real.sinh (2 * Real.artanh (anchorReflection a)) := by
  rw [precontactCanonicalDrift_eq ha, sinh_two_mul_artanh (anchorReflection_mem ha)]

private theorem mass_add_drift {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalMass a + precontactCanonicalDrift a =
      Real.exp (2 * Real.artanh (anchorReflection a)) := by
  rw [precontactCanonicalMass_eq_anchorMassRatio ha, anchorMassRatio_eq_cosh ha,
    precontactCanonicalDrift_eq_sinh ha, Real.cosh_add_sinh]

private theorem mass_sub_drift {a : ℝ} (ha : a ∈ precontactSet) :
    precontactCanonicalMass a - precontactCanonicalDrift a =
      Real.exp (-(2 * Real.artanh (anchorReflection a))) := by
  rw [precontactCanonicalMass_eq_anchorMassRatio ha, anchorMassRatio_eq_cosh ha,
    precontactCanonicalDrift_eq_sinh ha, Real.cosh_sub_sinh]

private theorem abs_drift_le_mass {a : ℝ} (ha : a ∈ precontactSet) :
    |precontactCanonicalDrift a| ≤ precontactCanonicalMass a := by
  have h1 := mass_add_drift ha
  have h2 := mass_sub_drift ha
  have h1' := Real.exp_pos (2 * Real.artanh (anchorReflection a))
  have h2' := Real.exp_pos (-(2 * Real.artanh (anchorReflection a)))
  exact abs_le.mpr ⟨by linarith only [h1, h1'], by linarith only [h2, h2']⟩

/-- `1/(1−r²)` is half of `m + 1`. -/
theorem one_div_one_sub_sq_eq {a : ℝ} (ha : a ∈ precontactSet) :
    1 / (1 - anchorReflection a ^ 2) = (anchorMassRatio a + 1) / 2 := by
  have h := (one_sub_sq_pos ha).ne'
  rw [anchorMassRatio]
  field_simp
  ring

/-- **The first flow equation**, from the right at every precontact aperture:
`(log K)′ = 2(1+r²)/(1−r²)`. -/
theorem hasDerivWithinAt_log_anchorKernel_right {a : ℝ} (ha : a ∈ precontactSet) :
    HasDerivWithinAt (fun x => Real.log (diagonalEvalGram I x)) (2 * anchorMassRatio a)
      (Ioi a) a := by
  have h := (hasDerivWithinAt_diagonalEvalGram_right I ha).log (anchorKernel_pos ha).ne'
  refine h.congr_deriv ?_
  have hm := precontactCanonicalMass_eq_anchorMassRatio ha
  rw [precontactCanonicalMass, precontactKernelEndpointDensity_diagonal_re] at hm
  have hK := (anchorKernel_pos ha).ne'
  rw [← hm]
  field_simp

private theorem subset_of_mem_Icc {l h x y : ℝ} (hx : x ∈ Icc l h) (hy : y ∈ Icc l h) :
    uIcc x y ⊆ uIcc l h := by
  rw [uIcc_of_le (hx.1.trans hx.2)]
  exact uIcc_subset_Icc hx hy

/-- The mass ratio is locally integrable, and its integral is the logarithmic kernel gain. -/
theorem integral_two_mul_anchorMassRatio {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable anchorMassRatio volume a b ∧
      (∫ x in a..b, 2 * anchorMassRatio x) =
        Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a) := by
  have he : precontactCanonicalMass =ᵐ[volume.restrict (uIoc a b)] anchorMassRatio := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le hab] at hx
    exact precontactCanonicalMass_eq_anchorMassRatio (hs ⟨hx.1.le, hx.2⟩)
  have hi := (intervalIntegrable_precontactCanonicalMass hab hs).congr_ae he
  refine ⟨hi, ?_⟩
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
  · exact fun x hx => ((continuousAt_diagonalEvalGram I (hs hx)).log
      (anchorKernel_pos (hs hx)).ne').continuousWithinAt
  · exact fun x hx => hasDerivWithinAt_log_anchorKernel_right (hs ⟨hx.1.le, hx.2.le⟩)
  · exact hi.const_mul 2

/-- The first Hamiltonian entry in the hyperbolic variable. -/
theorem canonicalHamiltonianOne_eq (base : ℝ) {a : ℝ} (ha : a ∈ precontactSet) :
    canonicalHamiltonianOne base a =
      Real.exp (2 * (Real.artanh (anchorReflection a) + precontactCanonicalGauge base a)) := by
  rw [canonicalHamiltonianOne, mass_add_drift ha, ← Real.exp_add]
  congr 1
  ring

/-- `Ψ = L + θ`. -/
theorem canonicalPotential_eq (base : ℝ) {a : ℝ} (ha : a ∈ precontactSet) :
    canonicalPotential base a =
      Real.artanh (anchorReflection a) + precontactCanonicalGauge base a := by
  rw [canonicalPotential, canonicalHamiltonianOne_eq base ha, Real.log_exp]
  ring

/-- **The Hamiltonian is one scalar:** `H₁ = e^{2Ψ}`, `H₂ = e^{−2Ψ}`. -/
theorem canonicalHamiltonian_eq_exp (base : ℝ) {a : ℝ} (ha : a ∈ precontactSet) :
    canonicalHamiltonianOne base a = Real.exp (2 * canonicalPotential base a) ∧
      canonicalHamiltonianTwo base a = Real.exp (-(2 * canonicalPotential base a)) := by
  constructor
  · rw [canonicalPotential_eq base ha, canonicalHamiltonianOne_eq base ha]
  · rw [canonicalHamiltonianTwo, mass_sub_drift ha, canonicalPotential_eq base ha, ← Real.exp_add]
    congr 1
    ring

private theorem driftIntegrable {l h x y : ℝ} (hs : Icc l h ⊆ precontactSet) (hx : x ∈ Icc l h)
    (hy : y ∈ Icc l h) : IntervalIntegrable precontactCanonicalDrift volume x y :=
  (intervalIntegrable_precontactCanonicalDrift (hx.1.trans hx.2) hs).mono_set
    (subset_of_mem_Icc hx hy)

/-- **The integrated Riccati equation**, with no regularity assumed on `r`:
`L(y) − L(x) = Ψ(y) − Ψ(x) − ∫_x^y 2r/(1−r²)`. -/
theorem artanh_anchorReflection_sub {l h base x y : ℝ} (hs : Icc l h ⊆ precontactSet)
    (hb : base ∈ Icc l h) (hx : x ∈ Icc l h) (hy : y ∈ Icc l h) :
    Real.artanh (anchorReflection y) - Real.artanh (anchorReflection x) =
      canonicalPotential base y - canonicalPotential base x -
        ∫ t in x..y, precontactCanonicalDrift t := by
  rw [canonicalPotential_eq base (hs hy), canonicalPotential_eq base (hs hx)]
  have h1 := intervalIntegral.integral_interval_sub_left (driftIntegrable hs hb hy)
    (driftIntegrable hs hb hx)
  have h2 : precontactCanonicalGauge base y - precontactCanonicalGauge base x =
      ∫ t in x..y, precontactCanonicalDrift t := h1
  linarith only [h2]

/-- **The second flow equation** `r′ = (1−r²)q − 2r`, at almost every aperture: wherever `Ψ` has a
derivative `q`, the reflection has this derivative, and conversely. -/
theorem ae_anchorReflection_riccati {base a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet)
    (hbase : base ∈ Icc a b) :
    ∀ᵐ x : ℝ, x ∈ Ioo a b →
      (∀ q, HasDerivAt (canonicalPotential base) q x →
        HasDerivAt anchorReflection ((1 - anchorReflection x ^ 2) * q - 2 * anchorReflection x) x) ∧
      (∀ ρ, HasDerivAt anchorReflection ρ x →
        HasDerivAt (canonicalPotential base)
          ((ρ + 2 * anchorReflection x) / (1 - anchorReflection x ^ 2)) x) := by
  filter_upwards [(intervalIntegrable_precontactCanonicalDrift hab hs).ae_hasDerivAt_integral]
    with x hθ hxI
  have hxi : x ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ⟨hxI.1.le, hxI.2.le⟩
  have hbi : base ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hbase
  have hd : HasDerivAt (precontactCanonicalGauge base) (precontactCanonicalDrift x) x :=
    hθ hxi base hbi
  have hxp : x ∈ precontactSet := hs ⟨hxI.1.le, hxI.2.le⟩
  have hne := (one_sub_sq_pos hxp).ne'
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ precontactSet := by
    filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
    exact hs ⟨hy.1.le, hy.2.le⟩
  constructor
  · intro q hq
    have ht := (hasDerivAt_tanh (canonicalPotential base x - precontactCanonicalGauge base x)).comp
      x (hq.sub hd)
    have hval : Real.tanh (canonicalPotential base x - precontactCanonicalGauge base x) =
        anchorReflection x := by
      rw [canonicalPotential_eq base hxp, add_sub_cancel_right,
        Real.tanh_artanh (anchorReflection_mem hxp)]
    rw [hval] at ht
    have heq : anchorReflection =ᶠ[𝓝 x] Real.tanh ∘ (canonicalPotential base -
        precontactCanonicalGauge base) := by
      filter_upwards [hnear] with y hy
      simp only [Function.comp_apply, Pi.sub_apply]
      rw [canonicalPotential_eq base hy, add_sub_cancel_right,
        Real.tanh_artanh (anchorReflection_mem hy)]
    refine (ht.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [precontactCanonicalDrift_eq hxp]
    field_simp
  · intro ρ hρ
    have ha := (hasDerivAt_artanh (anchorReflection_mem hxp)).comp x hρ
    have hsum := ha.add hd
    have heq : canonicalPotential base =ᶠ[𝓝 x] (Real.artanh ∘ anchorReflection) +
        precontactCanonicalGauge base := by
      filter_upwards [hnear] with y hy
      simp only [Pi.add_apply, Function.comp_apply]
      exact canonicalPotential_eq base hy
    refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [precontactCanonicalDrift_eq hxp]
    field_simp

/-! ### The restoring bound -/

/-- If `Ψ` has an integrable derivative `q` on a compact precontact interval, then `L = artanh r`
grows by at most `∫|q|`, because the drift `sinh 2L` restores `L` towards zero. -/
theorem abs_artanh_anchorReflection_le {l h base a b : ℝ} (hs : Icc l h ⊆ precontactSet)
    (hb : base ∈ Icc l h) (ha : a ∈ Icc l h) (hbb : b ∈ Icc l h) (hab : a ≤ b) {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume a b)
    (hΨ : ∀ x ∈ Icc a b, canonicalPotential base x - canonicalPotential base a = ∫ t in a..x, q t) :
    |Real.artanh (anchorReflection b)| ≤
      |Real.artanh (anchorReflection a)| + ∫ t in a..b, |q t| := by
  have hsub : Icc a b ⊆ Icc l h := Icc_subset_Icc ha.1 hbb.2
  have hs' : Icc a b ⊆ precontactSet := hsub.trans hs
  have hdrift : IntervalIntegrable precontactCanonicalDrift volume a b :=
    intervalIntegrable_precontactCanonicalDrift hab hs'
  have hprim : ∀ x ∈ Icc a b, Real.artanh (anchorReflection x) =
      Real.artanh (anchorReflection a) + ((∫ t in a..x, q t) -
        ∫ t in a..x, precontactCanonicalDrift t) := by
    intro x hx
    have he := artanh_anchorReflection_sub hs hb ha (hsub hx)
    rw [← hΨ x hx] at *
    linarith only [he]
  have hc : ContinuousOn (fun x => Real.artanh (anchorReflection x)) (Icc a b) := by
    have h1 := (hq.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) left_mem_uIcc).continuousOn
    have h2 := (hdrift.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) left_mem_uIcc).continuousOn
    rw [uIcc_of_le hab] at h1 h2
    exact (continuousOn_const.add (h1.sub h2)).congr hprim
  apply abs_le_of_restoring hab hc hq hdrift
  · intro x hx y hy hxy
    have he := artanh_anchorReflection_sub hs hb (hsub hx) (hsub hy)
    have hsubxy : uIcc x y ⊆ uIcc a b := subset_of_mem_Icc hx hy
    rw [intervalIntegral.integral_sub (hq.mono_set hsubxy) (hdrift.mono_set hsubxy)]
    have h1 := hΨ x hx
    have h2 := hΨ y hy
    have h3 := intervalIntegral.integral_interval_sub_left
      (hq.mono_set (subset_of_mem_Icc (left_mem_Icc.mpr hab) hy))
      (hq.mono_set (subset_of_mem_Icc (left_mem_Icc.mpr hab) hx))
    linarith only [he, h1, h2, h3]
  · intro x hx hL
    rw [precontactCanonicalDrift_eq_sinh (hs' hx)]
    exact Real.sinh_nonneg_iff.mpr (by linarith only [hL])
  · intro x hx hL
    rw [precontactCanonicalDrift_eq_sinh (hs' hx)]
    exact Real.sinh_nonpos_iff.mpr (by linarith only [hL])

/-! ### Limit-circle transfer -/

/-- The energy of the normalized Hermite–Biehler pair at `z`. -/
def anchorPairEnergy (z : ℂ) (a : ℝ) : ℝ :=
  ‖normalizedHermiteBiehler z a‖ ^ 2 + ‖normalizedHermiteBiehler ((starRingEnd ℂ) z) a‖ ^ 2

private theorem norm_sharp_eq (z : ℂ) (a : ℝ) :
    ‖normalizedHermiteBiehlerSharp z a‖ = ‖normalizedHermiteBiehler ((starRingEnd ℂ) z) a‖ := by
  rw [normalizedHermiteBiehlerSharp_eq_conj, Complex.norm_conj]

/-- The aperture equation bounds the slope of a squared normalized Hermite–Biehler value. -/
private theorem slope_bound (z : ℂ) {x : ℝ} (hx : x ∈ precontactSet) :
    2 * ((starRingEnd ℂ) (normalizedHermiteBiehler z x) *
      (-I * z * (precontactCanonicalMass x : ℂ) * normalizedHermiteBiehler z x +
        (I * z - 1) * (precontactCanonicalDrift x : ℂ) * normalizedHermiteBiehlerSharp z x)).re ≤
      2 * ‖normalizedHermiteBiehler z x‖ * (‖z‖ * precontactCanonicalMass x *
          ‖normalizedHermiteBiehler z x‖ + (‖z‖ + 1) * precontactCanonicalMass x *
          ‖normalizedHermiteBiehler ((starRingEnd ℂ) z) x‖) := by
  set e := normalizedHermiteBiehler z x
  set f := normalizedHermiteBiehlerSharp z x
  have hf : ‖f‖ = ‖normalizedHermiteBiehler ((starRingEnd ℂ) z) x‖ := norm_sharp_eq z x
  rw [← hf]
  have hs := abs_drift_le_mass hx
  have hp : 0 ≤ precontactCanonicalMass x := (abs_nonneg _).trans hs
  have hre := Complex.re_le_norm ((starRingEnd ℂ) e *
    (-I * z * (precontactCanonicalMass x : ℂ) * e +
      (I * z - 1) * (precontactCanonicalDrift x : ℂ) * f))
  rw [norm_mul, Complex.norm_conj] at hre
  have h1 : ‖-I * z * (precontactCanonicalMass x : ℂ) * e‖ =
      ‖z‖ * precontactCanonicalMass x * ‖e‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hp]
  have h2 : ‖(I * z - 1) * (precontactCanonicalDrift x : ℂ) * f‖ ≤
      (‖z‖ + 1) * precontactCanonicalMass x * ‖f‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hz : ‖I * z - 1‖ ≤ ‖z‖ + 1 := by
      calc
        _ ≤ ‖I * z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, Complex.norm_I, one_mul, norm_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hz hs (abs_nonneg _) (by positivity)) (norm_nonneg _)
  have h3 := (norm_add_le (-I * z * (precontactCanonicalMass x : ℂ) * e)
    ((I * z - 1) * (precontactCanonicalDrift x : ℂ) * f)).trans (add_le_add h1.le h2)
  have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg e)
  linarith only [hre, h4]

private theorem anchorPairEnergy_ac (z : ℂ) {a b : ℝ} (hab : a ≤ b)
    (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (anchorPairEnergy z) a b := by
  have h := (absolutelyContinuousOnInterval_norm_sq
    (absolutelyContinuousOnInterval_normalizedHermiteBiehler z hab hs)).add
    (absolutelyContinuousOnInterval_norm_sq
      (absolutelyContinuousOnInterval_normalizedHermiteBiehler ((starRingEnd ℂ) z) hab hs))
  exact h

/-- **Anchor domination in the exponential form.** The pair energy grows no faster than the
`(2|z|+1)`-th power of the anchor kernel. -/
theorem anchorPairEnergy_mul_exp_le (z : ℂ) {a b : ℝ} (hab : a ≤ b)
    (hs : Icc a b ⊆ precontactSet) :
    anchorPairEnergy z b ≤ anchorPairEnergy z a *
      Real.exp ((2 * ‖z‖ + 1) * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a))) := by
  obtain ⟨hmi, hmint⟩ := integral_two_mul_anchorMassRatio hab hs
  let κ : ℝ := 2 * ‖z‖ + 1
  let g : ℝ → ℝ := fun x => κ * ∫ t in a..x, 2 * anchorMassRatio t
  have hgac : AbsolutelyContinuousOnInterval g a b :=
    (((hmi.const_mul 2).absolutelyContinuousOnInterval_intervalIntegral
      (c := a) left_mem_uIcc)).const_mul κ
  have hmain := mul_exp_neg_le_of_ae_deriv_le hab (anchorPairEnergy_ac z hab hs) hgac (by
    filter_upwards [ae_hasDerivAt_normalizedHermiteBiehler z hab hs,
      ae_hasDerivAt_normalizedHermiteBiehler ((starRingEnd ℂ) z) hab hs,
      (hmi.const_mul 2).ae_hasDerivAt_integral] with x he hf hd hxI
    have hxi : x ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ⟨hxI.1.le, hxI.2.le⟩
    have hxp : x ∈ precontactSet := hs ⟨hxI.1.le, hxI.2.le⟩
    refine ⟨_, κ * (2 * anchorMassRatio x),
      (hasDerivAt_norm_sq (he hxI)).add (hasDerivAt_norm_sq (hf hxI)),
      (hd hxi a left_mem_uIcc).const_mul κ, ?_⟩
    have hb1 := slope_bound z hxp
    have hb2 := slope_bound ((starRingEnd ℂ) z) hxp
    rw [Complex.norm_conj, Complex.conj_conj] at hb2
    rw [← precontactCanonicalMass_eq_anchorMassRatio hxp]
    have hp : 0 ≤ precontactCanonicalMass x := (abs_nonneg _).trans (abs_drift_le_mass hxp)
    set A := ‖normalizedHermiteBiehler z x‖
    set B := ‖normalizedHermiteBiehler ((starRingEnd ℂ) z) x‖
    set p := precontactCanonicalMass x
    have hAB : p * (2 * A * B) ≤ p * (A ^ 2 + B ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (A - B)]) hp
    have hn : anchorPairEnergy z x = A ^ 2 + B ^ 2 := rfl
    rw [hn]
    dsimp only [κ]
    have hz : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith only [hb1, hb2, hAB, mul_nonneg hz (mul_nonneg hp (sq_nonneg (A - B)))])
  have hg0 : g a = 0 := by simp only [g, intervalIntegral.integral_same, mul_zero]
  have hgb : g b = κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a)) := by
    simp only [g, hmint]
  rw [hg0, hgb, neg_zero, Real.exp_zero, mul_one] at hmain
  have hexp := Real.exp_pos (κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a)))
  have hinv : Real.exp (-(κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a)))) *
      Real.exp (κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a))) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    anchorPairEnergy z b = anchorPairEnergy z b *
        (Real.exp (-(κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a)))) *
          Real.exp (κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a)))) := by
      rw [hinv, mul_one]
    _ = (anchorPairEnergy z b *
        Real.exp (-(κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a))))) *
          Real.exp (κ * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a))) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmain hexp.le

/-- The two-trace energy at `z` is at most the mass times the pair energy. -/
private theorem diagonalEndpointEnergy_le (z : ℂ) {x : ℝ} (hx : x ∈ precontactSet) :
    diagonalEndpointEnergy z x ≤ anchorMassRatio x * anchorPairEnergy z x := by
  have hd := precontactKernelEndpointDensity_eq_canonicalHamiltonian x z z hx
  have hg : precontactCanonicalGauge x x = 0 := intervalIntegral.integral_same
  have hH1 : canonicalHamiltonianOne x x = precontactCanonicalMass x + precontactCanonicalDrift x := by
    rw [canonicalHamiltonianOne, hg, mul_zero, Real.exp_zero, mul_one]
  have hH2 : canonicalHamiltonianTwo x x = precontactCanonicalMass x - precontactCanonicalDrift x := by
    rw [canonicalHamiltonianTwo, hg, mul_zero, Real.exp_zero, mul_one]
  have hA : canonicalSolutionA x z x = normalizedCanonicalA z x := by
    rw [canonicalSolutionA, hg, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
  have hB : canonicalSolutionB x z x = normalizedCanonicalB z x := by
    rw [canonicalSolutionB, hg, Real.exp_zero, Complex.ofReal_one, one_mul]
  rw [hH1, hH2, hA, hB] at hd
  have hre := congrArg Complex.re hd
  rw [precontactKernelEndpointDensity_diagonal_re] at hre
  have hconj (c : ℝ) (w : ℂ) : (((c : ℝ) : ℂ) * w * (starRingEnd ℂ) w).re = c * ‖w‖ ^ 2 := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [Complex.add_re, hconj, hconj] at hre
  set e := normalizedHermiteBiehler z x
  set f := normalizedHermiteBiehlerSharp z x
  have hAn : ‖normalizedCanonicalA z x‖ ^ 2 = ‖e - f‖ ^ 2 / 4 := by
    rw [normalizedCanonicalA, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      div_pow]
    norm_num
    rfl
  have hBn : ‖normalizedCanonicalB z x‖ ^ 2 = ‖e + f‖ ^ 2 / 4 := by
    rw [normalizedCanonicalB, norm_div, Complex.norm_ofNat, div_pow]
    norm_num
    rfl
  have hpar : ‖e + f‖ ^ 2 + ‖e - f‖ ^ 2 = 2 * (‖e‖ ^ 2 + ‖f‖ ^ 2) := by
    have h := parallelogram_law_with_norm ℝ e f
    nlinarith only [h]
  have hn : anchorPairEnergy z x = ‖e‖ ^ 2 + ‖f‖ ^ 2 := by
    simp only [anchorPairEnergy, e, f, norm_sharp_eq]
  rw [hre, hAn, hBn, hn, ← precontactCanonicalMass_eq_anchorMassRatio hx]
  have hs := abs_le.mp (abs_drift_le_mass hx)
  have h1 := sq_nonneg ‖e - f‖
  have h2 := sq_nonneg ‖e + f‖
  nlinarith only [hs.1, hs.2, h1, h2, hpar]

private theorem anchorPairEnergy_nonneg (z : ℂ) (a : ℝ) : 0 ≤ anchorPairEnergy z a :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem anchorMassRatio_nonneg {x : ℝ} (hx : x ∈ precontactSet) : 0 ≤ anchorMassRatio x := by
  rw [← precontactCanonicalMass_eq_anchorMassRatio hx]
  exact (abs_nonneg _).trans (abs_drift_le_mass hx)

/-- **The limit-circle transfer, quantitatively.** The kernel at `z` is controlled by the anchor
kernel alone, with exponent `2|z|+1`. -/
theorem diagonalEvalGram_le_of_anchor (z : ℂ) {a b : ℝ} (hab : a ≤ b)
    (hs : Icc a b ⊆ precontactSet) :
    diagonalEvalGram z b ≤ diagonalEvalGram z a + anchorPairEnergy z a *
      Real.exp ((2 * ‖z‖ + 1) * (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a))) *
        ((Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a)) / 2) := by
  obtain ⟨hDi, hD⟩ := integral_diagonalEndpointEnergy_eq_sub z hab hs
  obtain ⟨hmi, hm⟩ := integral_two_mul_anchorMassRatio hab hs
  set Δ := Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a) with hΔ
  set C := anchorPairEnergy z a * Real.exp ((2 * ‖z‖ + 1) * Δ) with hC
  have hmono {x : ℝ} (hx : x ∈ Icc a b) : Real.log (diagonalEvalGram I x) ≤ Real.log (diagonalEvalGram I b) :=
    Real.log_le_log (anchorKernel_pos (hs hx))
      (monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => I) (hs hx)
        (hs (right_mem_Icc.mpr hab)) hx.2)
  have hle : ∀ x ∈ Icc a b, diagonalEndpointEnergy z x ≤ anchorMassRatio x * C := by
    intro x hx
    refine (diagonalEndpointEnergy_le z (hs hx)).trans
      (mul_le_mul_of_nonneg_left ?_ (anchorMassRatio_nonneg (hs hx)))
    have hsub : Icc a x ⊆ precontactSet := (Icc_subset_Icc le_rfl hx.2).trans hs
    refine (anchorPairEnergy_mul_exp_le z hx.1 hsub).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ?_ (by positivity))) (anchorPairEnergy_nonneg z a))
    linarith only [hmono hx]
  have hint : (∫ x in a..b, diagonalEndpointEnergy z x) ≤ ∫ x in a..b, anchorMassRatio x * C :=
    intervalIntegral.integral_mono_on hab hDi (hmi.mul_const C) hle
  rw [hD, intervalIntegral.integral_mul_const] at hint
  have hm' : (∫ x in a..b, anchorMassRatio x) = Δ / 2 := by
    have h2 : (∫ x in a..b, 2 * anchorMassRatio x) = 2 * ∫ x in a..b, anchorMassRatio x :=
      intervalIntegral.integral_const_mul _ _
    linarith only [h2, hm]
  rw [hm'] at hint
  rw [hC] at hint ⊢
  linarith only [hint]

private theorem Icc_subset_precontact {a b : PrecontactAperture} :
    Icc a.1.1 b.1.1 ⊆ precontactSet := fun x hx =>
  ⟨a.1.2.trans_le hx.1, (EReal.coe_le_coe_iff.mpr hx.2).trans_lt b.2⟩

private theorem diagonal_eq (z : ℂ) (a : PrecontactAperture) :
    ‖evalVector a z‖ ^ 2 = diagonalEvalGram z a.1.1 :=
  (diagonalEvalGram_eq_norm z a).symm

/-- A bounded anchor kernel keeps the kernel bounded at every spectral parameter. -/
theorem kernel_bounded_of_anchorKernel_bounded (a : PrecontactAperture) (z : ℂ) {M : ℝ}
    (hM : ∀ b : PrecontactAperture, a.1.1 ≤ b.1.1 → ‖evalVector b I‖ ^ 2 ≤ M) :
    ∃ C : ℝ, ∀ b : PrecontactAperture, a.1.1 ≤ b.1.1 → ‖evalVector b z‖ ^ 2 ≤ C := by
  have hKa := anchorKernel_pos (show a.1.1 ∈ precontactSet from ⟨a.1.2, a.2⟩)
  set Δ := Real.log M - Real.log (diagonalEvalGram I a.1.1) with hΔ
  refine ⟨diagonalEvalGram z a.1.1 + anchorPairEnergy z a.1.1 *
    Real.exp ((2 * ‖z‖ + 1) * Δ) * (Δ / 2), fun b hab => ?_⟩
  have hKb := anchorKernel_pos (show b.1.1 ∈ precontactSet from ⟨b.1.2, b.2⟩)
  have hbM : diagonalEvalGram I b.1.1 ≤ M := by
    rw [← diagonal_eq]
    exact hM b hab
  have hlog : Real.log (diagonalEvalGram I b.1.1) ≤ Real.log M := Real.log_le_log hKb hbM
  have hlow : Real.log (diagonalEvalGram I a.1.1) ≤ Real.log (diagonalEvalGram I b.1.1) :=
    Real.log_le_log hKa (monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => I)
      ⟨a.1.2, a.2⟩ ⟨b.1.2, b.2⟩ hab)
  rw [diagonal_eq]
  refine (diagonalEvalGram_le_of_anchor z hab Icc_subset_precontact).trans ?_
  refine add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by positivity)))
    (anchorPairEnergy_nonneg z _)) (by linarith only [hlog]) (by linarith only [hlow])
    (mul_nonneg (anchorPairEnergy_nonneg z _) (Real.exp_pos _).le))

/-- **Finite contact is the blow-up of the anchor kernel.** Off RH the kernel at `z = i` itself
tends to infinity at contact. -/
theorem riemannHypothesis_or_anchorKernel_tends_to_top :
    RiemannHypothesis ∨ ∃ a : SuzukiPositiveAperture,
      (a.1 : EReal) = onsetAperture zetaZeroConfig ∧
      ccmRestrictedWeilGroundEnergy a = 0 ∧
      ∀ C : ℝ, ∃ b₀ : PrecontactAperture, ∀ b : PrecontactAperture,
        b₀.1.1 ≤ b.1.1 → C < ‖evalVector b I‖ ^ 2 := by
  rcases riemannHypothesis_or_kernel_tends_to_top_at_contact with hRH | ⟨a, ha, hg, z, hz⟩
  · exact Or.inl hRH
  refine Or.inr ⟨a, ha, hg, fun C => ?_⟩
  by_contra! hC
  have hbdd : ∀ b : PrecontactAperture, ‖evalVector b I‖ ^ 2 ≤ C := fun b => by
    obtain ⟨b', hbb', hb'⟩ := hC b
    exact (norm_evalVector_sq_mono hbb' I).trans hb'
  obtain ⟨a₀, -⟩ := hz 0
  obtain ⟨C', hC'⟩ := kernel_bounded_of_anchorKernel_bounded a₀ z (fun b _ => hbdd b)
  obtain ⟨b₀, hb₀⟩ := hz C'
  rcases le_total a₀.1.1 b₀.1.1 with h | h
  · exact absurd (hC' b₀ h) (not_le.mpr (hb₀ b₀ le_rfl))
  · exact absurd (hC' a₀ le_rfl) (not_le.mpr (hb₀ a₀ h))

private theorem one_div_integrable {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable (fun x => 1 / (1 - anchorReflection x ^ 2)) volume a b ∧
      (∫ x in a..b, 1 / (1 - anchorReflection x ^ 2)) =
        (Real.log (diagonalEvalGram I b) - Real.log (diagonalEvalGram I a)) / 4 + (b - a) / 2 := by
  obtain ⟨hmi, hm⟩ := integral_two_mul_anchorMassRatio hab hs
  have hi : IntervalIntegrable (fun x => (anchorMassRatio x + 1) / 2) volume a b :=
    (hmi.add intervalIntegrable_const).div_const 2
  have he : (fun x => (anchorMassRatio x + 1) / 2) =ᵐ[volume.restrict (uIoc a b)]
      fun x => 1 / (1 - anchorReflection x ^ 2) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le hab] at hx
    exact (one_div_one_sub_sq_eq (hs ⟨hx.1.le, hx.2⟩)).symm
  refine ⟨hi.congr_ae he, ?_⟩
  rw [← intervalIntegral.integral_congr_ae (μ := volume) (f := fun x => (anchorMassRatio x + 1) / 2)
    (g := fun x => 1 / (1 - anchorReflection x ^ 2)) (by
      rw [uIoc_of_le hab] at he
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at he
      filter_upwards [he] with x hx hxI
      exact hx (by rwa [uIoc_of_le hab] at hxI))]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hmi intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have h2 : (∫ x in a..b, 2 * anchorMassRatio x) = 2 * ∫ x in a..b, anchorMassRatio x :=
    intervalIntegral.integral_const_mul _ _
  rw [hm] at h2
  linarith only [h2]

/-- **Contact is `∫ dx/(1−r²) = ∞`.** Off RH the integral is unbounded from every precontact base. -/
theorem riemannHypothesis_or_integral_reflection_unbounded :
    RiemannHypothesis ∨ ∃ a : SuzukiPositiveAperture,
      (a.1 : EReal) = onsetAperture zetaZeroConfig ∧
      ∀ (base : PrecontactAperture) (C : ℝ), ∃ b : PrecontactAperture, base.1.1 ≤ b.1.1 ∧
        C < ∫ x in base.1.1..b.1.1, 1 / (1 - anchorReflection x ^ 2) := by
  rcases riemannHypothesis_or_anchorKernel_tends_to_top with hRH | ⟨a, ha, -, hK⟩
  · exact Or.inl hRH
  refine Or.inr ⟨a, ha, fun base C => ?_⟩
  have hbp : base.1.1 ∈ precontactSet := ⟨base.1.2, base.2⟩
  have hKb := anchorKernel_pos hbp
  obtain ⟨b₀, hb₀⟩ := hK (Real.exp (4 * C + Real.log (diagonalEvalGram I base.1.1)))
  obtain ⟨b, hbase, hb⟩ : ∃ b : PrecontactAperture, base.1.1 ≤ b.1.1 ∧
      Real.exp (4 * C + Real.log (diagonalEvalGram I base.1.1)) < ‖evalVector b I‖ ^ 2 := by
    rcases le_total base.1.1 b₀.1.1 with h | h
    · exact ⟨b₀, h, hb₀ b₀ le_rfl⟩
    · exact ⟨base, le_rfl, hb₀ base h⟩
  refine ⟨b, hbase, ?_⟩
  rw [(one_div_integrable hbase Icc_subset_precontact).2]
  rw [diagonal_eq] at hb
  have hlog : 4 * C + Real.log (diagonalEvalGram I base.1.1) < Real.log (diagonalEvalGram I b.1.1) :=
    (Real.lt_log_iff_exp_lt (anchorKernel_pos ⟨b.1.2, b.2⟩)).mpr hb
  have hab' : 0 ≤ b.1.1 - base.1.1 := sub_nonneg.mpr hbase
  linarith only [hlog, hab']

/-- **The exact criterion for a real aperture to be strictly precontact**: the integral of
`1/(1−r²)` stays bounded below it. -/
theorem lt_onsetAperture_iff_integral_reflection_bounded {base : PrecontactAperture} {c : ℝ}
    (hbc : base.1.1 < c) (hc : (c : EReal) ≤ onsetAperture zetaZeroConfig) :
    (c : EReal) < onsetAperture zetaZeroConfig ↔
      ∃ C : ℝ, ∀ b : PrecontactAperture, base.1.1 ≤ b.1.1 → b.1.1 < c →
        ∫ x in base.1.1..b.1.1, 1 / (1 - anchorReflection x ^ 2) ≤ C := by
  constructor
  · intro hlt
    let C' : PrecontactAperture := ⟨⟨c, base.1.2.trans hbc⟩, hlt⟩
    obtain ⟨hi, -⟩ := one_div_integrable (a := base.1.1) (b := c) hbc.le
      (Icc_subset_precontact (a := base) (b := C'))
    refine ⟨∫ x in base.1.1..c, 1 / (1 - anchorReflection x ^ 2), fun b hb hbc' => ?_⟩
    refine intervalIntegral.integral_mono_interval le_rfl hb hbc'.le ?_ hi
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    have hxp : x ∈ precontactSet := Icc_subset_precontact (a := base) (b := C') ⟨hx.1.le, hx.2⟩
    exact (one_div_pos.mpr (one_sub_sq_pos hxp)).le
  · rintro ⟨C, hC⟩
    by_contra hne
    have heq : (c : EReal) = onsetAperture zetaZeroConfig := le_antisymm hc (not_lt.mp hne)
    rcases riemannHypothesis_or_integral_reflection_unbounded with hRH | ⟨a, ha, hu⟩
    · rw [riemannHypothesis_iff_onsetAperture_zeta_eq_top.mp hRH] at heq
      exact EReal.coe_ne_top _ heq
    · obtain ⟨b, hb, hlt⟩ := hu base C
      have hbc' : b.1.1 < c := EReal.coe_lt_coe_iff.mp (b.2.trans_eq heq.symm)
      exact absurd (hC b hb hbc') (not_le.mpr hlt)

/-- **An integrable `q` up to contact excludes contact.** If every finite contact aperture admits a
base and an integrable `q` with `Ψ(x) − Ψ(base) = ∫ q` below contact, then RH holds. -/
theorem riemannHypothesis_of_contact_potential_integrable
    (h : ∀ c : ℝ, (c : EReal) = onsetAperture zetaZeroConfig →
      ∃ (base : PrecontactAperture) (q : ℝ → ℝ), base.1.1 < c ∧
        IntervalIntegrable q volume base.1.1 c ∧
        ∀ x ∈ Ico base.1.1 c, canonicalPotential base.1.1 x -
          canonicalPotential base.1.1 base.1.1 = ∫ t in base.1.1..x, q t) :
    RiemannHypothesis := by
  rcases riemannHypothesis_or_anchorKernel_tends_to_top with hRH | ⟨a, ha, -, hK⟩
  · exact hRH
  exfalso
  obtain ⟨base, q, hbc, hq, hΨ⟩ := h a.1 ha
  have hbp : base.1.1 ∈ precontactSet := ⟨base.1.2, base.2⟩
  set Λ := |Real.artanh (anchorReflection base.1.1)| + ∫ t in base.1.1..a.1, |q t| with hΛ
  have hxpre {x : ℝ} (hx : x ∈ Ico base.1.1 a.1) : Icc base.1.1 x ⊆ precontactSet := fun y hy =>
    ⟨base.1.2.trans_le hy.1, by
      rw [← ha]
      exact EReal.coe_lt_coe_iff.mpr (hy.2.trans_lt hx.2)⟩
  have hmass : ∀ {x : ℝ}, x ∈ Ico base.1.1 a.1 → anchorMassRatio x ≤ Real.cosh (2 * Λ) := by
    intro x hx
    have hs := hxpre hx
    have hsub : uIcc base.1.1 x ⊆ uIcc base.1.1 a.1 := by
      rw [uIcc_of_le hx.1, uIcc_of_le hbc.le]
      exact Icc_subset_Icc le_rfl hx.2.le
    have hb := abs_artanh_anchorReflection_le (l := base.1.1) (h := x) (base := base.1.1)
      (a := base.1.1) (b := x) hs (left_mem_Icc.mpr hx.1) (left_mem_Icc.mpr hx.1)
      (right_mem_Icc.mpr hx.1) hx.1 (hq.mono_set hsub)
      (fun y hy => hΨ y ⟨hy.1, hy.2.trans_lt hx.2⟩)
    have hmono : ∫ t in base.1.1..x, |q t| ≤ ∫ t in base.1.1..a.1, |q t| :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2.le
        (Eventually.of_forall fun _ => abs_nonneg _) hq.abs
    have hxp : x ∈ precontactSet := hs (right_mem_Icc.mpr hx.1)
    rw [anchorMassRatio_eq_cosh hxp, Real.cosh_le_cosh, abs_mul, abs_mul, abs_two]
    have hΛnn : 0 ≤ Λ := add_nonneg (abs_nonneg _)
      (intervalIntegral.integral_nonneg hbc.le fun _ _ => abs_nonneg _)
    rw [abs_of_nonneg hΛnn]
    linarith only [hb, hmono]
  have hbound : ∀ {x : ℝ}, x ∈ Ico base.1.1 a.1 → Real.log (diagonalEvalGram I x) ≤
      Real.log (diagonalEvalGram I base.1.1) + 2 * Real.cosh (2 * Λ) * (a.1 - base.1.1) := by
    intro x hx
    have hs := hxpre hx
    obtain ⟨hi, he⟩ := integral_two_mul_anchorMassRatio hx.1 hs
    have hle : ∫ t in base.1.1..x, 2 * anchorMassRatio t ≤ ∫ _ in base.1.1..x, 2 * Real.cosh (2 * Λ) :=
      intervalIntegral.integral_mono_on hx.1 (hi.const_mul 2) intervalIntegrable_const fun t ht =>
        mul_le_mul_of_nonneg_left (hmass ⟨ht.1, ht.2.trans_lt hx.2⟩) (by norm_num)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    have hc := (Real.cosh_pos (2 * Λ)).le
    have hdx : x - base.1.1 ≤ a.1 - base.1.1 := sub_le_sub_right hx.2.le _
    nlinarith only [he, hle, hc, hdx]
  obtain ⟨b₀, hb₀⟩ := hK (Real.exp (Real.log (diagonalEvalGram I base.1.1) +
    2 * Real.cosh (2 * Λ) * (a.1 - base.1.1)))
  obtain ⟨b, hbase, hb⟩ : ∃ b : PrecontactAperture, base.1.1 ≤ b.1.1 ∧
      Real.exp (Real.log (diagonalEvalGram I base.1.1) +
        2 * Real.cosh (2 * Λ) * (a.1 - base.1.1)) < ‖evalVector b I‖ ^ 2 := by
    rcases le_total base.1.1 b₀.1.1 with h | h
    · exact ⟨b₀, h, hb₀ b₀ le_rfl⟩
    · exact ⟨base, le_rfl, hb₀ base h⟩
  have hba : b.1.1 < a.1 := EReal.coe_lt_coe_iff.mp (b.2.trans_eq ha.symm)
  rw [diagonal_eq] at hb
  have hlog := (Real.lt_log_iff_exp_lt (anchorKernel_pos ⟨b.1.2, b.2⟩)).mpr hb
  exact absurd (hbound ⟨hbase, hba⟩) (not_le.mpr hlog)


end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
