import GaloisForLFunctions.RHTower.ConstitutiveDaggerConfluence

/-!
# Canonical repair-pair positive-dark-history no-go

The pre-divisor source repair has exactly two normal presentations.  Their natural scalar
orientation values are opposite.  Hence a positive finite probability history supported on this
literal pair cannot become norm-dark off the critical line: positivity removes one orientation,
and unit mass then retains the other one unchanged.

This classifies the elementary two-atom candidate for Route RHist.  A viable positive dark-history
producer must add a source-visible vector channel; changing weights or taking a fixed reflection
mixture of these two scalar source values cannot supply it.
-/

open Filter Topology

namespace RHTower

noncomputable section

open ConstitutiveCriticalCompletionMechanics

/-- The two literal source orientations of one canonical conservative repair. -/
def canonicalRepairPairAmplitude (N clock : ℕ) (s : ℂ) : Bool → ℝ
  | true => actualRepairOrientationPotential N clock s (left (N + 1))
  | false => actualRepairOrientationPotential N clock s (right (N + 1))

/-- The two canonical source amplitudes are exact opposites. -/
theorem canonicalRepairPairAmplitude_false_eq_neg_true
    (N clock : ℕ) (s : ℂ) :
    canonicalRepairPairAmplitude N clock s false =
      -canonicalRepairPairAmplitude N clock s true := by
  simp only [canonicalRepairPairAmplitude]
  rw [actualRepairOrientationPotential_left,
    actualRepairOrientationPotential_right]
  ring

/-- A positive finite probability history on the literal repair pair whose scalar barycentres
become norm-dark. -/
def CanonicalRepairPairPositiveDarkHistory (N clock : ℕ) (s : ℂ) : Prop :=
  ∃ F : ℕ → Finset Bool, ∃ mu : ℕ → Bool → ℝ,
    (∀ n i, i ∈ F n → 0 ≤ mu n i) ∧
    (∀ n i, i ∈ F n → 0 ≤ canonicalRepairPairAmplitude N clock s i) ∧
    (∀ n, ∑ i ∈ F n, mu n i = 1) ∧
    Tendsto (fun n => ‖∑ i ∈ F n,
      mu n i * canonicalRepairPairAmplitude N clock s i‖) atTop (nhds 0)

/-- Positivity and darkness already force the active canonical repair amplitude to vanish. -/
lemma canonicalRepairPairPositiveDarkHistory_forces_amplitude_zero
    {N clock : ℕ} {s : ℂ}
    {F : ℕ → Finset Bool} {mu : ℕ → Bool → ℝ}
    (_hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i)
    (hpositive : ∀ n i, i ∈ F n → 0 ≤ canonicalRepairPairAmplitude N clock s i)
    (hmass : ∀ n, ∑ i ∈ F n, mu n i = 1)
    (hdark : Tendsto (fun n => ‖∑ i ∈ F n,
      mu n i * canonicalRepairPairAmplitude N clock s i‖) atTop (nhds 0)) :
    canonicalRepairPairAmplitude N clock s true = 0 := by
  let x := canonicalRepairPairAmplitude N clock s true
  have hneg : canonicalRepairPairAmplitude N clock s false = -x := by
    simpa [x] using canonicalRepairPairAmplitude_false_eq_neg_true N clock s
  by_cases hx : x = 0
  · exact hx
  have hx' : 0 ≠ x := by
    intro h
    exact hx h.symm
  have hxsign : 0 < x ∨ x < 0 := lt_or_gt_of_ne hx'
  rcases hxsign with hxpos | hxneg
  · have hfalse : ∀ n, false ∉ F n := by
      intro n hf
      have h := hpositive n false hf
      rw [hneg] at h
      linarith
    have htrue : ∀ n, true ∈ F n := by
      intro n
      by_contra hnot
      have hempty : F n = ∅ := by
        ext b
        cases b
        · simp [hfalse n]
        · simp [hnot]
      have := hmass n
      rw [hempty] at this
      norm_num at this
    have hF : ∀ n, F n = {true} := by
      intro n
      ext b
      cases b <;> simp [hfalse n, htrue n]
    have hmean : ∀ n, ∑ i ∈ F n,
        mu n i * canonicalRepairPairAmplitude N clock s i = x := by
      intro n
      have hm : mu n true = 1 := by
        simpa [hF n] using hmass n
      rw [hF n]
      simp [x, hm]
    have hlimit : Tendsto (fun _ : ℕ => ‖x‖) atTop (nhds 0) := by
      apply hdark.congr'
      filter_upwards [] with n
      rw [hmean n]
    have : ‖x‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hlimit
    exact norm_eq_zero.mp this
  · have htrue : ∀ n, true ∉ F n := by
      intro n ht
      have h := hpositive n true ht
      change 0 ≤ x at h
      linarith
    have hfalse : ∀ n, false ∈ F n := by
      intro n
      by_contra hnot
      have hempty : F n = ∅ := by
        ext b
        cases b
        · simp [hnot]
        · simp [htrue n]
      have := hmass n
      rw [hempty] at this
      norm_num at this
    have hF : ∀ n, F n = {false} := by
      intro n
      ext b
      cases b <;> simp [hfalse n, htrue n]
    have hmean : ∀ n, ∑ i ∈ F n,
        mu n i * canonicalRepairPairAmplitude N clock s i = -x := by
      intro n
      have hm : mu n false = 1 := by
        simpa [hF n] using hmass n
      rw [hF n]
      simp [hneg, hm]
    have hlimit : Tendsto (fun _ : ℕ => ‖-x‖) atTop (nhds 0) := by
      apply hdark.congr'
      filter_upwards [] with n
      rw [hmean n]
    have : ‖-x‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hlimit
    exact neg_eq_zero.mp (norm_eq_zero.mp this)

/-- **Canonical-pair classification.** The literal two-repair scalar source admits a positive
norm-dark finite history exactly on the critical line. -/
theorem canonicalRepairPairPositiveDarkHistory_iff_re_eq_half
    {N clock : ℕ} (hclock : 2 ≤ clock) (s : ℂ) :
    CanonicalRepairPairPositiveDarkHistory N clock s ↔ s.re = 1 / 2 := by
  constructor
  · rintro ⟨F, mu, hmu, hpositive, hmass, hdark⟩
    have hleft : canonicalRepairPairAmplitude N clock s true = 0 :=
      canonicalRepairPairPositiveDarkHistory_forces_amplitude_zero hmu hpositive hmass hdark
    have hright : canonicalRepairPairAmplitude N clock s false = 0 := by
      rw [canonicalRepairPairAmplitude_false_eq_neg_true, hleft]
      norm_num
    apply (actualRepairProofErasureConsistent_iff_re_eq_half hclock s).1
    apply (repairProofErasureConsistent_iff_repair_eq N _).2
    change canonicalRepairPairAmplitude N clock s true =
      canonicalRepairPairAmplitude N clock s false
    rw [hleft, hright]
  · intro hs
    have hleft : actualRepairOrientationPotential N clock s (left (N + 1)) = 0 := by
      rw [actualRepairOrientationPotential_left,
        logarithm_deningerHalfDensityMateGain, hs]
      norm_num
    have hright : actualRepairOrientationPotential N clock s (right (N + 1)) = 0 := by
      rw [actualRepairOrientationPotential_right,
        logarithm_deningerHalfDensityMateGain, hs]
      norm_num
    refine ⟨(fun _ => {true}), (fun _ i => if i then 1 else 0), ?_, ?_, ?_, ?_⟩
    · intro n i hi
      have : i = true := by simpa using hi
      subst i
      norm_num
    · intro n i hi
      cases i <;> simp [canonicalRepairPairAmplitude, hleft, hright]
    · intro n
      simp
    · simp [canonicalRepairPairAmplitude, hleft, hright]

end

end RHTower
