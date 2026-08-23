import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.RHTower.MertensCoronaShiftConormal
import GaloisForLFunctions.HTGeometry.ScalarLinearPMapVerticalFibre

/-!
# Singular corona--residue incidence trilemma

Exact prime-shift, quotient-incidence, residue-translation, finite-gauge, and
Marcinkiewicz graph-closure laws.
-/

open Complex Filter Topology
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Diagonal multiplication by a normalized prime-shift character. -/
def primeShiftMultiplier (z : ℂ) (b : ℕ → ℂ) : ℕ → ℂ :=
  fun n => primeShiftCharacter z n * b n

theorem primeShiftMultiplier_prime (z : ℂ) (b : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    absField (primeShiftMultiplier z b) p =
      primeUnitTranslation (z.re - 1 / 2) (absField b) p := by
  rw [absField, primeShiftMultiplier, norm_mul, primeShiftCharacter, if_pos hp,
    Complex.norm_natCast_cpow_of_pos hp.pos, primeUnitTranslation]
  congr 1
  congr 1
  simp

theorem primeLogMass_congr_primes {b c : ℕ → ℝ}
    (h : ∀ p : ℕ, p.Prime → b p = c p) (X : ℕ) :
    primeLogMass b X = primeLogMass c X := by
  unfold primeLogMass
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [h p hp.2]

theorem memVanishingTailLayer_congr_primes {b c : ℕ → ℝ}
    (h : ∀ p : ℕ, p.Prime → b p = c p)
    (hb : MemVanishingTailLayer b) : MemVanishingTailLayer c := by
  intro ε hε
  obtain ⟨P, hP⟩ := hb ε hε
  refine ⟨P, fun X hX => ?_⟩
  have htail : ∀ p : ℕ, p.Prime →
      primeCoefficientTail b P p = primeCoefficientTail c P p := by
    intro p hp
    by_cases hPp : P < p <;> simp [primeCoefficientTail, hPp, h p hp]
  rw [marcinkiewiczLogQuotient,
    ← primeLogMass_congr_primes htail]
  exact hP X hX

/-- Every strict right-strip shift sends the full complex logarithmic Marcinkiewicz layer into
the vanishing-tail layer. -/
theorem memVanishingTailLayer_absField_primeShiftMultiplier
    {z : ℂ} (hz : 1 / 2 < z.re) {b : ℕ → ℂ}
    (hb : MemMarcinkiewiczLogLayer (absField b)) :
    MemVanishingTailLayer (absField (primeShiftMultiplier z b)) := by
  have htrans := memVanishingTailLayer_primeUnitTranslation
    (h := z.re - 1 / 2) (sub_pos.mpr hz) hb
  exact memVanishingTailLayer_congr_primes
    (fun p hp => (primeShiftMultiplier_prime z b hp).symm) htrans

/-- Explicit Marcinkiewicz seminorm bound for the shift multiplier. -/
theorem marcinkiewiczLogQuotient_primeShiftMultiplier_le
    {z : ℂ} (hz : 1 / 2 < z.re) (b : ℕ → ℂ) {X : ℕ} (hX : 2 ≤ X) :
    marcinkiewiczLogQuotient (absField (primeShiftMultiplier z b)) X ≤
      (2 : ℝ) ^ (-(z.re - 1 / 2)) * marcinkiewiczLogQuotient (absField b) X := by
  have heps : 0 < z.re - 1 / 2 := sub_pos.mpr hz
  have hmass : primeLogMass (absField (primeShiftMultiplier z b)) X ≤
      (2 : ℝ) ^ (-(z.re - 1 / 2)) * primeLogMass (absField b) X := by
    unfold primeLogMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [primeShiftMultiplier_prime z b hp.2, primeUnitTranslation]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hpow : (p : ℝ) ^ (-(z.re - 1 / 2)) ≤
        (2 : ℝ) ^ (-(z.re - 1 / 2)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_neg (show (0 : ℝ) ≤ 2 by positivity)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hp.2.two_le) heps.le)
    have hw : 0 ≤ Real.log p / p * absField b p :=
      mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
        (absField_nonneg b p)
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp0 _),
      abs_of_nonneg (absField_nonneg b p)]
    calc
      Real.log p / (p : ℝ) * ((p : ℝ) ^ (-(z.re - 1 / 2)) * absField b p) =
          (p : ℝ) ^ (-(z.re - 1 / 2)) *
            (Real.log p / (p : ℝ) * absField b p) := by ring
      _ ≤ (2 : ℝ) ^ (-(z.re - 1 / 2)) *
            (Real.log p / (p : ℝ) * absField b p) :=
        mul_le_mul_of_nonneg_right hpow hw
  unfold marcinkiewiczLogQuotient
  rw [div_le_iff₀ (log_cutoff_pos hX)]
  calc
    primeLogMass (absField (primeShiftMultiplier z b)) X ≤
        (2 : ℝ) ^ (-(z.re - 1 / 2)) * primeLogMass (absField b) X := hmass
    _ = ((2 : ℝ) ^ (-(z.re - 1 / 2)) *
        (primeLogMass (absField b) X / Real.log X)) * Real.log X := by
      field_simp [ne_of_gt (log_cutoff_pos hX)]

/-- Any quotient-linear incidence annihilating `M₀` vanishes after every strict right shift. -/
theorem quotientIncidence_primeShiftMultiplier_eq_zero
    (Lambda : (ℕ → ℂ) →ₗ[ℂ] ℂ)
    (hLambda : ∀ y : ℕ → ℂ,
      MemVanishingTailLayer (absField y) → Lambda y = 0)
    {z : ℂ} (hz : 1 / 2 < z.re) {b : ℕ → ℂ}
    (hb : MemMarcinkiewiczLogLayer (absField b)) :
    Lambda (primeShiftMultiplier z b) = 0 :=
  hLambda _ (memVanishingTailLayer_absField_primeShiftMultiplier hz hb)

theorem primeShiftMultiplier_primeShiftCharacter (z w : ℂ) :
    primeShiftMultiplier z (primeShiftCharacter w) =
      primeShiftCharacter (z + w - 1 / 2) := by
  funext n
  by_cases hn : n.Prime
  · simp only [primeShiftMultiplier, primeShiftCharacter, if_pos hn]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hn.pos.ne')]
    congr 1
    ring
  · simp [primeShiftMultiplier, primeShiftCharacter, hn]

theorem primeShiftMultiplier_character_mem_residueDomain
    {z w : ℂ} (hzw : z + w - 1 / 2 ∈ RightStrip) :
    primeShiftMultiplier z (primeShiftCharacter w) ∈ residueDomain := by
  rw [primeShiftMultiplier_primeShiftCharacter]
  exact primeShiftCharacter_mem_residueDomain ⟨z + w - 1 / 2, hzw⟩

theorem residueFunctional_primeShiftMultiplier_character
    {z w : ℂ} (hzw : z + w - 1 / 2 ∈ RightStrip) :
    residueFunctional
        ⟨primeShiftMultiplier z (primeShiftCharacter w),
          primeShiftMultiplier_character_mem_residueDomain hzw⟩ =
      primeShiftResidue (z + w - 1 / 2) := by
  let r := z + w - 1 / 2
  let hr : r ∈ RightStrip := hzw
  have hmem : primeShiftCharacter r ∈ residueDomain :=
    primeShiftCharacter_mem_residueDomain ⟨r, hr⟩
  have hval := residueFunctional_primeShiftCharacter ⟨r, hr⟩ hmem
  have heq :
      (⟨primeShiftMultiplier z (primeShiftCharacter w),
          primeShiftMultiplier_character_mem_residueDomain hzw⟩ : residueDomain) =
        ⟨primeShiftCharacter r, hmem⟩ := by
    apply Subtype.ext
    exact primeShiftMultiplier_primeShiftCharacter z w
  rw [heq]
  exact hval

theorem finite_support_primeShiftMultiplier {z : ℂ} {f : ℕ → ℂ}
    (hf : (Function.support f).Finite) :
    (Function.support (primeShiftMultiplier z f)).Finite := by
  exact hf.subset fun n hn => by
    simp only [Function.mem_support, primeShiftMultiplier] at hn ⊢
    intro hfn
    exact hn (by rw [hfn, mul_zero])

/-- Finite Euler corrections do not alter the canonical shifted residue incidence. -/
theorem residueFunctional_primeShiftMultiplier_unit_add_finite
    {z : ℂ} (hz : z ∈ RightStrip) {f : ℕ → ℂ}
    (hf : (Function.support f).Finite) :
    ∃ hmem : primeShiftMultiplier z (fun n => 1 + f n) ∈ residueDomain,
      residueFunctional ⟨primeShiftMultiplier z (fun n => 1 + f n), hmem⟩ =
        primeShiftResidue z := by
  have hzmem : primeShiftCharacter z ∈ residueDomain :=
    primeShiftCharacter_mem_residueDomain ⟨z, hz⟩
  have hfin := finite_support_primeShiftMultiplier (z := z) hf
  have hfinmem : primeShiftMultiplier z f ∈ residueDomain :=
    finiteSupportSpace_le_residueDomain hfin
  have heq : primeShiftMultiplier z (fun n => 1 + f n) =
      primeShiftCharacter z + primeShiftMultiplier z f := by
    funext n
    simp [primeShiftMultiplier]
    ring
  have hmem : primeShiftMultiplier z (fun n => 1 + f n) ∈ residueDomain := by
    rw [heq]
    exact Submodule.add_mem _ hzmem hfinmem
  refine ⟨hmem, ?_⟩
  have hsub :
      (⟨primeShiftMultiplier z (fun n => 1 + f n), hmem⟩ : residueDomain) =
        ⟨primeShiftCharacter z, hzmem⟩ + ⟨primeShiftMultiplier z f, hfinmem⟩ :=
    Subtype.ext heq
  rw [hsub, map_add,
    residueFunctional_primeShiftCharacter ⟨z, hz⟩ hzmem,
    residueFunctional_eq_zero_of_finiteSupport _ hfin, add_zero]

theorem marcinkiewiczLogQuotient_absField_add_le
    (b c : ℕ → ℂ) {X : ℕ} (hX : 2 ≤ X) :
    marcinkiewiczLogQuotient (absField (b + c)) X ≤
      marcinkiewiczLogQuotient (absField b) X +
        marcinkiewiczLogQuotient (absField c) X := by
  have hmass : primeLogMass (absField (b + c)) X ≤
      primeLogMass (absField b) X + primeLogMass (absField c) X := by
    unfold primeLogMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    have hw : 0 ≤ Real.log n / (n : ℝ) :=
      div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
    have hnorm : absField (b + c) n ≤ absField b n + absField c n := by
      simpa [absField] using norm_add_le (b n) (c n)
    simpa [absField, mul_add] using mul_le_mul_of_nonneg_left hnorm hw
  unfold marcinkiewiczLogQuotient
  rw [div_le_iff₀ (log_cutoff_pos hX)]
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (log_cutoff_pos hX)),
    div_mul_cancel₀ _ (ne_of_gt (log_cutoff_pos hX))]
  exact hmass

theorem marcinkiewiczSmall_add {b c : ℕ → ℂ} {ε δ : ℝ}
    (hb : MarcinkiewiczSmall b ε) (hc : MarcinkiewiczSmall c δ) :
    MarcinkiewiczSmall (b + c) (ε + δ) := by
  intro X hX
  exact le_trans (marcinkiewiczLogQuotient_absField_add_le b c hX)
    (add_le_add (hb X hX) (hc X hX))

theorem tendstoMarcinkiewiczZero_add {b c : ℕ → (ℕ → ℂ)}
    (hb : TendstoMarcinkiewiczZero b) (hc : TendstoMarcinkiewiczZero c) :
    TendstoMarcinkiewiczZero (fun n => b n + c n) := by
  intro ε hε
  obtain ⟨Nb, hNb⟩ := hb (ε / 2) (by linarith)
  obtain ⟨Nc, hNc⟩ := hc (ε / 2) (by linarith)
  refine ⟨max Nb Nc, fun n hn => ?_⟩
  have hb' := hNb n (le_trans (le_max_left _ _) hn)
  have hc' := hNc n (le_trans (le_max_right _ _) hn)
  have hsum := marcinkiewiczSmall_add hb' hc'
  simpa only [show ε / 2 + ε / 2 = ε by ring] using hsum

theorem marcinkiewiczLogQuotient_absField_smul
    (a : ℂ) (b : ℕ → ℂ) (X : ℕ) :
    marcinkiewiczLogQuotient (absField (a • b)) X =
      ‖a‖ * marcinkiewiczLogQuotient (absField b) X := by
  have hmass : primeLogMass (absField (a • b)) X =
      ‖a‖ * primeLogMass (absField b) X := by
    unfold primeLogMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp [absField]
    ring
  unfold marcinkiewiczLogQuotient
  rw [hmass]
  ring

theorem tendstoMarcinkiewiczZero_smul (a : ℂ) {b : ℕ → (ℕ → ℂ)}
    (hb : TendstoMarcinkiewiczZero b) :
    TendstoMarcinkiewiczZero (fun n => a • b n) := by
  by_cases ha : a = 0
  · subst a
    intro ε hε
    refine ⟨0, fun n _ X hX => ?_⟩
    simp [marcinkiewiczLogQuotient, primeLogMass, absField, hε.le]
  · have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
    intro ε hε
    obtain ⟨N, hN⟩ := hb (ε / ‖a‖) (div_pos hε hnorm)
    refine ⟨N, fun n hn X hX => ?_⟩
    rw [marcinkiewiczLogQuotient_absField_smul]
    have hsmall := hN n hn X hX
    exact le_trans (mul_le_mul_of_nonneg_left hsmall (norm_nonneg a))
      (by field_simp [ne_of_gt hnorm]; norm_num)

theorem tendstoMarcinkiewiczZero_zero :
    TendstoMarcinkiewiczZero (fun _ : ℕ => (0 : ℕ → ℂ)) := by
  intro ε hε
  refine ⟨0, fun n _ X hX => ?_⟩
  simp [marcinkiewiczLogQuotient, primeLogMass, absField, hε.le]

/-- Scalar vertical fibre for the actual Marcinkiewicz-null sequential graph topology. -/
def marcinkiewiczVerticalFibre
    (D : Submodule ℂ (ℕ → ℂ)) (L : D →ₗ[ℂ] ℂ) : Submodule ℂ ℂ where
  carrier := {v | ∃ y : ℕ → D,
    TendstoMarcinkiewiczZero (fun n => (y n : ℕ → ℂ)) ∧
      Tendsto (fun n => L (y n)) atTop (nhds v)}
  zero_mem' := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · simpa using tendstoMarcinkiewiczZero_zero
    · simp
  add_mem' := by
    rintro v w ⟨y, hy0, hyv⟩ ⟨u, hu0, huw⟩
    refine ⟨fun n => y n + u n, ?_, ?_⟩
    · exact tendstoMarcinkiewiczZero_add hy0 hu0
    · simpa using hyv.add huw
  smul_mem' := by
    rintro a v ⟨y, hy0, hyv⟩
    refine ⟨fun n => a • y n, ?_, ?_⟩
    · exact tendstoMarcinkiewiczZero_smul a hy0
    · simpa using (tendsto_const_nhds.smul hyv :
        Tendsto (fun n : ℕ => a • L (y n)) atTop (nhds (a • v)))

theorem isClosableMarcinkiewicz_iff_verticalFibre_eq_bot
    (D : Submodule ℂ (ℕ → ℂ)) (L : D →ₗ[ℂ] ℂ) :
    IsClosableMarcinkiewicz D L ↔ marcinkiewiczVerticalFibre D L = ⊥ := by
  constructor
  · intro hclos
    apply le_antisymm
    · intro v hv
      obtain ⟨y, hy0, hyv⟩ := hv
      change v = 0
      exact hclos y v hy0 hyv
    · exact bot_le
  · intro hbot y v hy0 hyv
    have hv : v ∈ marcinkiewiczVerticalFibre D L := ⟨y, hy0, hyv⟩
    rw [hbot] at hv
    simpa using hv

theorem marcinkiewiczVerticalFibre_eq_bot_or_top
    (D : Submodule ℂ (ℕ → ℂ)) (L : D →ₗ[ℂ] ℂ) :
    marcinkiewiczVerticalFibre D L = ⊥ ∨ marcinkiewiczVerticalFibre D L = ⊤ := by
  by_cases hbot : marcinkiewiczVerticalFibre D L = ⊥
  · exact Or.inl hbot
  · right
    rw [eq_top_iff]
    intro c _
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hsmul := (marcinkiewiczVerticalFibre D L).smul_mem (c / v) hv
    simpa [smul_eq_mul, div_mul_cancel₀ c hv0] using hsmul

theorem marcinkiewiczVerticalFibre_eq_top_iff_not_isClosable
    (D : Submodule ℂ (ℕ → ℂ)) (L : D →ₗ[ℂ] ℂ) :
    marcinkiewiczVerticalFibre D L = ⊤ ↔ ¬ IsClosableMarcinkiewicz D L := by
  rw [isClosableMarcinkiewicz_iff_verticalFibre_eq_bot]
  constructor
  · intro htop hbot
    rw [hbot] at htop
    exact bot_ne_top htop
  · intro hnot
    rcases marcinkiewiczVerticalFibre_eq_bot_or_top D L with hbot | htop
    · exact absurd hbot hnot
    · exact htop

theorem riemannHypothesis_iff_residueVerticalFibre_eq_bot :
    RiemannHypothesis ↔ marcinkiewiczVerticalFibre residueDomain residueFunctional = ⊥ := by
  rw [riemannHypothesis_iff_residueFunctional_isClosable,
    isClosableMarcinkiewicz_iff_verticalFibre_eq_bot]

theorem not_riemannHypothesis_iff_residueVerticalFibre_eq_top :
    ¬ RiemannHypothesis ↔ marcinkiewiczVerticalFibre residueDomain residueFunctional = ⊤ := by
  rw [riemannHypothesis_iff_residueFunctional_isClosable]
  exact (marcinkiewiczVerticalFibre_eq_top_iff_not_isClosable
    residueDomain residueFunctional).symm

theorem riemannHypothesis_or_residueVerticalFibre_eq_top :
    RiemannHypothesis ∨ marcinkiewiczVerticalFibre residueDomain residueFunctional = ⊤ := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr (not_riemannHypothesis_iff_residueVerticalFibre_eq_top.mp hRH)

/-- Shift parameters whose input and translated output both lie in the pole-excised right strip. -/
abbrev ShiftedStripPoint (z : ℂ) :=
  {w : ℂ // w ∈ RightStrip ∧ z + w - 1 / 2 ∈ RightStrip}

noncomputable def shiftedStripCharacterField (z : ℂ) :
    (ShiftedStripPoint z →₀ ℂ) →ₗ[ℂ] (ℕ → ℂ) :=
  Finsupp.linearCombination ℂ fun w : ShiftedStripPoint z => primeShiftCharacter (w : ℂ)

noncomputable def shiftedStripResidueValue (z : ℂ) :
    (ShiftedStripPoint z →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun w : ShiftedStripPoint z =>
    primeShiftResidue (z + (w : ℂ) - 1 / 2)

noncomputable def shiftedCoronaDomainMap (z : ℂ) :
    ((ℕ →₀ ℂ) × (ShiftedStripPoint z →₀ ℂ)) →ₗ[ℂ] (ℕ → ℂ) :=
  Finsupp.lcoeFun.comp
      (LinearMap.fst ℂ (ℕ →₀ ℂ) (ShiftedStripPoint z →₀ ℂ)) +
    (shiftedStripCharacterField z).comp
      (LinearMap.snd ℂ (ℕ →₀ ℂ) (ShiftedStripPoint z →₀ ℂ))

theorem shiftedCoronaDomainMap_apply (z : ℂ)
    (fu : (ℕ →₀ ℂ) × (ShiftedStripPoint z →₀ ℂ)) :
    shiftedCoronaDomainMap z fu =
      (fun n => fu.1 n) + shiftedStripCharacterField z fu.2 := rfl

theorem shiftedStripResidueValue_apply (z : ℂ) (u : ShiftedStripPoint z →₀ ℂ) :
    shiftedStripResidueValue z u =
      ∑ w ∈ u.support, u w * primeShiftResidue (z + (w : ℂ) - 1 / 2) := by
  rw [shiftedStripResidueValue, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

/-- Closability of the fixed-`z` pulled-back residue graph in the Marcinkiewicz topology. -/
def IsClosableShiftedCorona (z : ℂ) : Prop :=
  ∀ (y : ℕ → ((ℕ →₀ ℂ) × (ShiftedStripPoint z →₀ ℂ))) (v : ℂ),
    TendstoMarcinkiewiczZero (fun n => shiftedCoronaDomainMap z (y n)) →
      Tendsto (fun n => shiftedStripResidueValue z (y n).2) atTop (nhds v) → v = 0

theorem isClosableShiftedCorona_iff_residues_eq_zero (z : ℂ) :
    IsClosableShiftedCorona z ↔
      ∀ w : ShiftedStripPoint z,
        primeShiftResidue (z + (w : ℂ) - 1 / 2) = 0 := by
  constructor
  · intro hclos w
    let y : ℕ → ((ℕ →₀ ℂ) × (ShiftedStripPoint z →₀ ℂ)) := fun n =>
      (-Finsupp.ofSupportFinite (primeFieldHead (primeShiftCharacter (w : ℂ)) n)
          (finite_support_primeFieldHead _ n), Finsupp.single w 1)
    have hmap : ∀ n, shiftedCoronaDomainMap z (y n) =
        primeFieldTail (primeShiftCharacter (w : ℂ)) n := by
      intro n
      rw [shiftedCoronaDomainMap_apply]
      ext p
      simp [y, shiftedStripCharacterField, Finsupp.linearCombination_single,
        Finsupp.ofSupportFinite_coe]
      calc
        -primeFieldHead (primeShiftCharacter (w : ℂ)) n p +
            primeShiftCharacter (w : ℂ) p =
          primeShiftCharacter (w : ℂ) p -
            primeFieldHead (primeShiftCharacter (w : ℂ)) n p := by ring
        _ = primeFieldTail (primeShiftCharacter (w : ℂ)) n p :=
          congrFun (sub_primeFieldHead (primeShiftCharacter (w : ℂ)) n) p
    have hnull : TendstoMarcinkiewiczZero
        (fun n => shiftedCoronaDomainMap z (y n)) := by
      simp_rw [hmap]
      exact tendstoMarcinkiewiczZero_tail
        (memVanishingTailLayer_of_memCriticalSummableLayer
          (memCriticalSummableLayer_absField_primeShiftCharacter w.2.1.1))
    have hvalue : ∀ n, shiftedStripResidueValue z (y n).2 =
        primeShiftResidue (z + (w : ℂ) - 1 / 2) := by
      intro n
      simp [y, shiftedStripResidueValue, Finsupp.linearCombination_single]
    apply hclos y _ hnull
    simpa only [hvalue] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => primeShiftResidue (z + (w : ℂ) - 1 / 2)) atTop
        (nhds (primeShiftResidue (z + (w : ℂ) - 1 / 2))))
  · intro hzero y v _ hval
    have hv0 : ∀ n, shiftedStripResidueValue z (y n).2 = 0 := by
      intro n
      rw [shiftedStripResidueValue_apply]
      exact Finset.sum_eq_zero fun w _ => by rw [hzero w, mul_zero]
    simp only [hv0] at hval
    exact tendsto_nhds_unique hval tendsto_const_nhds

/-- The fixed-shift pulled-back graph is closable exactly on the corresponding zero-free
right-strip region above `Re z`. -/
theorem isClosableShiftedCorona_iff_zeroFree_above
    {z : ℂ} (hz : z ∈ RightStrip) :
    IsClosableShiftedCorona z ↔
      ∀ ρ : ℂ, ρ ∈ RightStrip → z.re < ρ.re → riemannZeta ρ ≠ 0 := by
  rw [isClosableShiftedCorona_iff_residues_eq_zero]
  constructor
  · intro hres ρ hρ hzρ
    let w : ℂ := ρ - z + 1 / 2
    have hw : w ∈ RightStrip := by
      constructor
      · dsimp [w]
        simp
        linarith
      · dsimp [w]
        simp
        linarith [hρ.2, hz.1]
    have hzw : z + w - 1 / 2 ∈ RightStrip := by
      have heq : z + w - 1 / 2 = ρ := by
        dsimp [w]
        ring
      rwa [heq]
    have hzero := hres ⟨w, hw, hzw⟩
    have hρ1 : ρ ≠ 1 := by
      intro h
      rw [h] at hρ
      norm_num [RightStrip] at hρ
    apply (primeShiftResidue_eq_zero_iff hρ1).mp
    have heq : z + w - 1 / 2 = ρ := by
      dsimp [w]
      ring
    rwa [heq] at hzero
  · intro hzero w
    have hr : z + (w : ℂ) - 1 / 2 ∈ RightStrip := w.2.2
    have hzlt : z.re < (z + (w : ℂ) - 1 / 2).re := by
      have hw := w.2.1.1
      simp at hw ⊢
      linarith
    have hne := hzero _ hr hzlt
    have hr1 : z + (w : ℂ) - 1 / 2 ≠ 1 := by
      intro h
      rw [h] at hr
      norm_num [RightStrip] at hr
    exact (primeShiftResidue_eq_zero_iff hr1).mpr hne

/-- Closed, unconditional package of the singular corona--residue trilemma. -/
theorem singularCoronaResidueIncidenceTrilemma :
    (∀ (z : ℂ), 1 / 2 < z.re → ∀ (b : ℕ → ℂ),
      MemMarcinkiewiczLogLayer (absField b) →
        MemVanishingTailLayer (absField (primeShiftMultiplier z b))) ∧
    (∀ (Lambda : (ℕ → ℂ) →ₗ[ℂ] ℂ),
      (∀ y : ℕ → ℂ, MemVanishingTailLayer (absField y) → Lambda y = 0) →
      ∀ (z : ℂ), 1 / 2 < z.re → ∀ (b : ℕ → ℂ),
        MemMarcinkiewiczLogLayer (absField b) → Lambda (primeShiftMultiplier z b) = 0) ∧
    (∀ (z w : ℂ) (hzw : z + w - 1 / 2 ∈ RightStrip),
      residueFunctional
          ⟨primeShiftMultiplier z (primeShiftCharacter w),
            primeShiftMultiplier_character_mem_residueDomain hzw⟩ =
        primeShiftResidue (z + w - 1 / 2)) ∧
    (∀ (z : ℂ), z ∈ RightStrip → ∀ (f : ℕ → ℂ),
      (Function.support f).Finite →
        ∃ hmem : primeShiftMultiplier z (fun n => 1 + f n) ∈ residueDomain,
          residueFunctional ⟨primeShiftMultiplier z (fun n => 1 + f n), hmem⟩ =
            primeShiftResidue z) ∧
    (RiemannHypothesis ↔
      marcinkiewiczVerticalFibre residueDomain residueFunctional = ⊥) ∧
    (¬ RiemannHypothesis ↔
      marcinkiewiczVerticalFibre residueDomain residueFunctional = ⊤) ∧
    (∀ (z : ℂ), z ∈ RightStrip →
      (IsClosableShiftedCorona z ↔
        ∀ ρ : ℂ, ρ ∈ RightStrip → z.re < ρ.re → riemannZeta ρ ≠ 0)) := by
  exact ⟨fun z hz b hb => memVanishingTailLayer_absField_primeShiftMultiplier hz hb,
    fun Lambda hLambda z hz b hb =>
      quotientIncidence_primeShiftMultiplier_eq_zero Lambda hLambda hz hb,
    fun z w hzw => residueFunctional_primeShiftMultiplier_character hzw,
    fun z hz f hf => residueFunctional_primeShiftMultiplier_unit_add_finite hz hf,
    riemannHypothesis_iff_residueVerticalFibre_eq_bot,
    not_riemannHypothesis_iff_residueVerticalFibre_eq_top,
    fun z hz => isClosableShiftedCorona_iff_zeroFree_above hz⟩

end RHTower
