import GaloisForLFunctions.HTGeometry.CanonicalConstraintOrientationLimit
import GaloisForLFunctions.HTGeometry.UniversalPrimeKreinHamming

/-!
# Analytic realization of the complete prime orientation limit

Every Boolean sign sequence on the prime-log support defines an absolutely and normally convergent
signed Cauchy carrier.  It extends the finite prime-residue chambers exactly, retains a nonzero
simple pole at every prime logarithm, and is Herglotz precisely at the all-positive sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped BigOperators

noncomputable section

/-- The signed Cauchy mass attached to a point of the prime-labelled Cantor cube.  Its negative is
the ordinary meromorphic residue in the local coordinate `z - primeLogSupport p`. -/
def universalPrimeOrientationWeight
    (ε : Nat.Primes → Bool) (p : Nat.Primes) : ℝ :=
  if ε p = true then -universalPrimeWeight p else universalPrimeWeight p

theorem norm_universalPrimeOrientationWeight
    (ε : Nat.Primes → Bool) (p : Nat.Primes) :
    ‖(universalPrimeOrientationWeight ε p : ℂ)‖ = ‖(universalPrimeWeight p : ℂ)‖ := by
  simp only [universalPrimeOrientationWeight]
  split_ifs <;> simp

theorem summable_norm_universalPrimeWeight :
    Summable fun p : Nat.Primes => ‖(universalPrimeWeight p : ℂ)‖ := by
  simpa only [universalPrimeWeight] using
    summable_norm_primeDyadicWeight (fun q => universalFacetOrbitGauge q)
      ‖universalFacetOrbitGauge‖
      (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
        (universalFacetOrbitGauge.norm_coe_le_norm q))

theorem summable_norm_universalPrimeOrientationWeight (ε : Nat.Primes → Bool) :
    Summable fun p : Nat.Primes => ‖(universalPrimeOrientationWeight ε p : ℂ)‖ :=
  summable_norm_universalPrimeWeight.congr fun p =>
    (norm_universalPrimeOrientationWeight ε p).symm

/-- The canonical signed prime-log Cauchy carrier for an arbitrary orientation sequence. -/
def universalPrimeOrientationLimit (ε : Nat.Primes → Bool) (z : ℂ) : ℂ :=
  discreteHerglotz primeLogSupport (universalPrimeOrientationWeight ε) z

theorem universalPrimeOrientationLimit_empty (z : ℂ) :
    universalPrimeOrientationLimit (fun _ => false) z =
      primeLogHerglotz (fun q => universalFacetOrbitGauge q) z := by
  apply tsum_congr
  intro p
  simp [universalPrimeOrientationWeight, universalPrimeWeight]

theorem summable_universalPrimeOrientationTerm
    (ε : Nat.Primes → Bool) (z : ℂ) :
    Summable fun p => (universalPrimeOrientationWeight ε p : ℂ) *
      ((primeLogSupport p : ℂ) - z)⁻¹ := by
  rw [← summable_norm_iff]
  have hpos := (summable_primeLogHerglotz_term
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) z).norm
  exact hpos.congr fun p => by
    rw [norm_mul, norm_mul, norm_universalPrimeOrientationWeight ε]
    rfl

/-- Every infinite orientation gives a holomorphic carrier on the upper half-plane. -/
theorem differentiableOn_universalPrimeOrientationLimit_upperHalfPlane
    (ε : Nat.Primes → Bool) :
    DifferentiableOn ℂ (universalPrimeOrientationLimit ε) upperHalfPlane :=
  differentiableOn_discreteHerglotz_upperHalfPlane _ _
    (summable_norm_universalPrimeOrientationWeight ε)

/-- Signed prime-log carriers converge normally away from any selected subfamily of poles. -/
theorem summableLocallyUniformlyOn_universalPrimeOrientation_on_off_poles
    (ε : Nat.Primes → Bool) (S : Set Nat.Primes) :
    SummableLocallyUniformlyOn
      (fun p : S => fun z => (universalPrimeOrientationWeight ε p : ℂ) *
        ((primeLogSupport p : ℂ) - z)⁻¹) (primeLogPoleSetOn S)ᶜ := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_compl_primeLogPoleSetOn S)
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  refine ⟨fun p : S => ‖(universalPrimeWeight p : ℂ)‖,
    summable_norm_universalPrimeWeight.subtype S, ?_⟩
  have hfinite := finite_primeLogSupport_le_on S (R + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with p hp
  intro z hz
  have hpLarge : R + 1 < primeLogSupport p := by
    simpa using lt_of_not_ge hp
  have hzNorm : ‖z‖ ≤ R := hR z hz
  have hpNorm : ‖(primeLogSupport p : ℂ)‖ = primeLogSupport p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeLogSupport_pos p)]
  have hden : 1 ≤ ‖(primeLogSupport p : ℂ) - z‖ := by
    calc
      (1 : ℝ) ≤ primeLogSupport p - R := by linarith
      _ ≤ ‖(primeLogSupport p : ℂ)‖ - ‖z‖ := by rw [hpNorm]; linarith
      _ ≤ ‖(primeLogSupport p : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_mul, norm_inv, norm_universalPrimeOrientationWeight ε]
  have hinv : ‖(primeLogSupport p : ℂ) - z‖⁻¹ ≤ (1 : ℝ) :=
    (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
  simpa using
    (mul_le_mul_of_nonneg_left hinv (norm_nonneg (universalPrimeWeight p : ℂ)))

/-- Delete one atom from an arbitrary infinite orientation. -/
def universalPrimeOrientationRegular
    (ε : Nat.Primes → Bool) (p : Nat.Primes) (z : ℂ) : ℂ :=
  ∑' q : {q : Nat.Primes // q ∉ ({p} : Finset Nat.Primes)},
    (universalPrimeOrientationWeight ε q : ℂ) *
      ((primeLogSupport q : ℂ) - z)⁻¹

theorem differentiableAt_universalPrimeOrientationRegular
    (ε : Nat.Primes → Bool) (p : Nat.Primes) :
    DifferentiableAt ℂ (universalPrimeOrientationRegular ε p)
      (primeLogSupport p : ℂ) := by
  let S : Set Nat.Primes := {q | q ∉ ({p} : Finset Nat.Primes)}
  have hsum := summableLocallyUniformlyOn_universalPrimeOrientation_on_off_poles ε S
  have hdiff : DifferentiableOn ℂ (universalPrimeOrientationRegular ε p)
      (primeLogPoleSetOn S)ᶜ := by
    apply SummableLocallyUniformlyOn.differentiableOn
      (isOpen_compl_primeLogPoleSetOn S) hsum
    intro q z hz
    have hne : (primeLogSupport q : ℂ) - z ≠ 0 := by
      intro h
      apply hz
      exact ⟨q, sub_eq_zero.mp h⟩
    exact (((differentiableAt_const (c := (primeLogSupport q : ℂ))).sub
      differentiableAt_id).inv hne).const_mul _
  exact (hdiff _ (primeLogCenter_notMem_otherPoleSet p)).differentiableAt
    ((isOpen_compl_primeLogPoleSetOn S).mem_nhds
      (primeLogCenter_notMem_otherPoleSet p))

/-- Exact polar splitting for every point of the infinite orientation cube. -/
theorem universalPrimeOrientationLimit_add_polar_eq_regular
    (ε : Nat.Primes → Bool) (p : Nat.Primes) (z : ℂ) :
    universalPrimeOrientationLimit ε z +
        (universalPrimeOrientationWeight ε p : ℂ) *
          (z - (primeLogSupport p : ℂ))⁻¹ =
      universalPrimeOrientationRegular ε p z := by
  let f : Nat.Primes → ℂ := fun q => (universalPrimeOrientationWeight ε q : ℂ) *
    ((primeLogSupport q : ℂ) - z)⁻¹
  have hsum : Summable f := summable_universalPrimeOrientationTerm ε z
  have hsplit := hsum.sum_add_tsum_subtype_compl {p}
  have heq : f p + universalPrimeOrientationRegular ε p z =
      universalPrimeOrientationLimit ε z := by
    simpa [f, universalPrimeOrientationRegular, universalPrimeOrientationLimit,
      discreteHerglotz] using hsplit
  rw [← heq]
  have hinv : ((primeLogSupport p : ℂ) - z)⁻¹ =
      -(z - (primeLogSupport p : ℂ))⁻¹ := by
    rw [← inv_neg, neg_sub]
  simp only [f, hinv]
  ring

/-- The Boolean coordinate is exactly the sign of a nonzero simple-pole residue. -/
theorem hasSimplePoleAt_universalPrimeOrientationLimit
    (ε : Nat.Primes → Bool) (p : Nat.Primes) :
    HasSimplePoleAt (universalPrimeOrientationLimit ε) (primeLogSupport p : ℂ)
      (-(universalPrimeOrientationWeight ε p : ℂ)) := by
  constructor
  · have hw : universalPrimeOrientationWeight ε p ≠ 0 := by
      by_cases hp : ε p = true
      · simp [universalPrimeOrientationWeight, hp, universalPrimeWeight_pos p |>.ne']
      · simp [universalPrimeOrientationWeight, hp, universalPrimeWeight_pos p |>.ne']
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hw)
  · have hregular :=
      (differentiableAt_universalPrimeOrientationRegular ε p).continuousAt
    convert hregular using 1
    funext z
    simpa using universalPrimeOrientationLimit_add_polar_eq_regular ε p z

theorem universalPrimeOrientationLimit_eq_regular_sub_atom
    {ε : Nat.Primes → Bool} {p : Nat.Primes} (hpε : ε p = true) (z : ℂ) :
    universalPrimeOrientationLimit ε z =
      universalPrimeOrientationRegular ε p z -
        (universalPrimeWeight p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹ := by
  let f : Nat.Primes → ℂ := fun q => (universalPrimeOrientationWeight ε q : ℂ) *
    ((primeLogSupport q : ℂ) - z)⁻¹
  have hsum : Summable f := summable_universalPrimeOrientationTerm ε z
  have hsplit := hsum.sum_add_tsum_subtype_compl {p}
  have heq : f p + universalPrimeOrientationRegular ε p z =
      universalPrimeOrientationLimit ε z := by
    simpa [f, universalPrimeOrientationRegular, universalPrimeOrientationLimit,
      discreteHerglotz] using hsplit
  rw [← heq]
  simp only [f, universalPrimeOrientationWeight, if_pos hpε]
  push_cast
  ring

theorem universalPrimeOrientationLimit_not_nonneg_of_nonempty
    (ε : Nat.Primes → Bool) (hε : ∃ p, ε p = true) :
    ¬ ∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientationLimit ε z).im := by
  obtain ⟨p, hpε⟩ := hε
  obtain ⟨z, hz, hneg⟩ := exists_upper_im_neg_of_continuous_sub_weightedAtom
    (primeLogSupport p) (universalPrimeWeight p) (universalPrimeWeight_pos p)
    (universalPrimeOrientationRegular ε p)
    (differentiableAt_universalPrimeOrientationRegular ε p).continuousAt
  intro hnonneg
  have h := hnonneg z hz
  rw [universalPrimeOrientationLimit_eq_regular_sub_atom hpε z] at h
  exact (not_lt_of_ge h) hneg

/-- The all-positive sequence is the unique Herglotz point of the entire Cantor orientation
cube, including orientations with infinitely many negative residues. -/
theorem universalPrimeOrientationLimit_nonneg_iff_allPositive (ε : Nat.Primes → Bool) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientationLimit ε z).im) ↔
      ε = fun _ => false := by
  constructor
  · intro h
    apply funext
    intro p
    apply Bool.eq_false_of_not_eq_true
    intro hp
    exact universalPrimeOrientationLimit_not_nonneg_of_nonempty ε ⟨p, hp⟩ h
  · rintro rfl z hz
    rw [universalPrimeOrientationLimit_empty]
    exact universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz

/-- The canonical infinite carrier restricts to the previously constructed finite chambers. -/
theorem universalPrimeOrientationLimit_coe_finset
    (J : Finset Nat.Primes) (z : ℂ) :
    universalPrimeOrientationLimit (fun p => decide (p ∈ J)) z =
      universalPrimeOrientedHerglotz J z := by
  classical
  let f : Nat.Primes → ℂ := fun p => (universalPrimeWeight p : ℂ) *
    ((primeLogSupport p : ℂ) - z)⁻¹
  let c : Nat.Primes → ℂ := fun p =>
    if p ∈ J then -2 * (universalPrimeWeight p : ℂ) *
      ((primeLogSupport p : ℂ) - z)⁻¹ else 0
  have hf : Summable f := by
    simpa [f, universalPrimeWeight] using summable_primeLogHerglotz_term
      (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
      (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
        (universalFacetOrbitGauge.norm_coe_le_norm q)) z
  have hc : Summable c := summable_of_ne_finset_zero (s := J) (by
    intro p hp
    simp [c, hp])
  calc
    universalPrimeOrientationLimit (fun p => decide (p ∈ J)) z =
        ∑' p, (f p + c p) := by
          apply tsum_congr
          intro p
          by_cases hp : p ∈ J
          · simp [universalPrimeOrientationWeight, f, c, hp]
            ring
          · simp [universalPrimeOrientationWeight, f, c, hp]
    _ = (∑' p, f p) + ∑' p, c p := hf.tsum_add hc
    _ = (∑' p, f p) + ∑ p ∈ J, c p := by
      have hctsum : ∑' p, c p = ∑ p ∈ J, c p :=
        tsum_eq_sum (s := J) (by intro p hp; simp [c, hp])
      rw [hctsum]
    _ = universalPrimeOrientedHerglotz J z := by
      have hcfin : ∑ p ∈ J, c p = -2 * ∑ p ∈ J, f p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        simp [c, f, hp]
        ring
      rw [hcfin]
      simp only [f, universalPrimeOrientedHerglotz, primeLogHerglotz,
        discreteHerglotz, universalPrimeWeight]
      ring

/-- The finite part of the complete orientation carrier is Herglotz exactly when its independent
dephasing master energy against the all-positive chamber vanishes. -/
theorem universalPrimeOrientationLimit_coe_finset_nonneg_iff_dephasingMasterEnergy_eq_zero
    (J : Finset Nat.Primes) :
    (∀ z : ℂ, 0 < z.im →
        0 ≤ (universalPrimeOrientationLimit (fun p => decide (p ∈ J)) z).im) ↔
      primeChamberDephasingMasterEnergy J ∅ = 0 := by
  simpa only [universalPrimeOrientationLimit_coe_finset] using
    universalPrimeOrientedHerglotz_nonneg_iff_dephasingMasterEnergy_eq_zero J

/-- The analytic pointing on the canonical constraint--orientation limit depends only on its
orientation coordinate and selects exactly the all-positive global thread. -/
theorem canonicalConstraintOrientationLimit_primeCarrier_nonneg_iff_allPositive
    (X : CanonicalConstraintOrientationLimit ℕ Nat.Primes) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientationLimit X.2 z).im) ↔
      X.2 = fun _ => false :=
  universalPrimeOrientationLimit_nonneg_iff_allPositive X.2

end
end GaloisForLFunctions.HTGeometry
