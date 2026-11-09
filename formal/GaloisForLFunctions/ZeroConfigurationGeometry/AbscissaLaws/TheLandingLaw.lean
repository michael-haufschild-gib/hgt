import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheLinearAbscissaLawAndItsHierarchy

/-!
# The landing law of a zero configuration

For a zero configuration `Z` (`ZeroConfig`) the **landing law** says that a configuration whose
zeros approach the line (ZAL) has only finitely many zeros off it:

`LandingLaw Z : ApproachesLine Z → (rightOf Z 0).Finite`.

* **Tail law.** `LandingLaw` is a property of the zeros above any height (`landingLaw_isAsymptotic`)
  and no verification up to a fixed height decides it (`not_isLocalBelow_landingLaw`). Equivalently
  (`landingLaw_tfae`) the critical line holds above some height as soon as the zeros approach it.
* **Three atoms.** With the finite-stratum law `B13 = AbscissaLawAt Z 0` and the asymptotic
  Deuring–Heilbronn law `DH = (¬ AbscissaLaw Z → ApproachesLine Z)`:
  `LinearAbscissaLaw Z ↔ B13 ∧ LandingLaw Z`, `AbscissaLaw Z ↔ B13 ∧ LandingLaw Z ∧ DH`,
  `Pure Z ↔ ApproachesLine Z ∧ B13 ∧ LandingLaw Z`, and the extreme Deuring–Heilbronn law
  `¬ AbscissaLaw Z → (rightOf Z 0).Finite` is `LandingLaw Z ∧ DH`.
* **Disjoint defects.** No two of `B13`, `LandingLaw`, `DH` fail together
  (`landing_atoms_pairwise`), so a failure of the abscissa law lies in exactly one of three sectors
  (`not_abscissaLaw_iff_sector`).
* **Calibration.** The landing law implies neither quasi-RH nor ZAL nor `B13`
  (`exists_landingLaw_not_quasiRH`, `exists_landingLaw_not_abscissaLawAt_zero`).
-/

open Complex Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

open ArithmeticCastelnuovoSeveri

section General

variable (Z : ZeroConfig)

/-- **The landing law**: zeros that approach the critical line land on it, up to finitely many. -/
def LandingLaw : Prop := ApproachesLine Z → (rightOf Z 0).Finite

/-- Finitely many zeros right of the line approach it. -/
theorem approachesLine_of_rightOf_zero_finite (h : (rightOf Z 0).Finite) : ApproachesLine Z :=
  fun _ hh => h.subset fun _ ⟨hz, hre⟩ => ⟨hz, by linarith⟩

/-- Reflection `ρ ↦ 1 − ρ̄` keeps the ordinate. -/
theorem im_reflect (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

/-- **Finitely many zeros right of the line ⇔ the line holds above some height.** -/
theorem rightOf_zero_finite_iff_onLine_above :
    (rightOf Z 0).Finite ↔ ∃ T₀ : ℝ, ∀ ρ ∈ Z.carrier, T₀ < |ρ.im| → ρ.re = 1 / 2 := by
  constructor
  · intro hfin
    obtain ⟨M, hM⟩ := (hfin.image fun ρ : ℂ => |ρ.im|).bddAbove
    refine ⟨M, fun ρ hρ hlt => ?_⟩
    have hnot : ∀ z ∈ rightOf Z 0, ¬ M < |z.im| := fun z hz h =>
      absurd (hM ⟨z, hz, rfl⟩) (not_le.mpr h)
    rcases lt_trichotomy ρ.re (1 / 2) with hre | hre | hre
    · refine absurd hlt (by
        simpa [im_reflect] using hnot (reflect ρ) ⟨Z.reflect_mem ρ hρ, by
          rw [re_reflect]; linarith⟩)
    · exact hre
    · exact absurd hlt (hnot ρ ⟨hρ, by linarith⟩)
  · rintro ⟨T₀, hT₀⟩
    refine (finite_of_abs_im_le Z T₀).subset fun ρ ⟨hρ, hre⟩ => ⟨hρ, ?_⟩
    by_contra hlt
    have := hT₀ ρ hρ (not_le.mp hlt)
    linarith

/-- **Equivalent forms of the landing law.** -/
theorem landingLaw_tfae :
    [LandingLaw Z,
      asymptoticAbscissa Z = 1 / 2 → (rightOf Z 0).Finite,
      ApproachesLine Z ↔ (rightOf Z 0).Finite,
      ¬ ApproachesLine Z ∨ (rightOf Z 0).Finite,
      ApproachesLine Z → ∃ T₀ : ℝ, ∀ ρ ∈ Z.carrier, T₀ < |ρ.im| → ρ.re = 1 / 2].TFAE := by
  tfae_have 1 ↔ 2 := by rw [LandingLaw, approachesLine_iff_asymptoticAbscissa_eq_half]
  tfae_have 1 ↔ 3 :=
    ⟨fun h => ⟨h, approachesLine_of_rightOf_zero_finite Z⟩, fun h => h.mp⟩
  tfae_have 1 ↔ 4 := imp_iff_not_or
  tfae_have 1 ↔ 5 := by rw [LandingLaw, rightOf_zero_finite_iff_onLine_above]
  tfae_finish

/-- Purity empties the right half-strip. -/
theorem rightOf_zero_finite_of_pure (hP : Pure Z) : (rightOf Z 0).Finite :=
  finite_empty.subset fun ρ ⟨hρ, hre⟩ => by have := hP ρ hρ; linarith

/-- The finite-stratum law turns finitely many right zeros into purity. -/
theorem pure_of_abscissaLawAt_zero (hB : AbscissaLawAt Z 0) (hfin : (rightOf Z 0).Finite) :
    Pure Z :=
  (pure_iff_forall_re_le Z).mpr fun ρ hρ => by simpa using hB hfin ρ hρ

/-! ### The three atoms -/

/-- **Existential linear AAL is the finite stratum plus landing.** -/
theorem linearAbscissaLaw_iff_abscissaLawAt_zero_and_landingLaw :
    LinearAbscissaLaw Z ↔ AbscissaLawAt Z 0 ∧ LandingLaw Z := by
  have hlin : LinearAbscissaLaw Z ↔ (ApproachesLine Z → Pure Z) :=
    (linearAbscissaLaw_tfae Z).out 0 4
  refine hlin.trans ⟨fun h => ⟨fun hfin ρ hρ => ?_, fun hA => rightOf_zero_finite_of_pure Z (h hA)⟩,
    fun ⟨hB, hL⟩ hA => pure_of_abscissaLawAt_zero Z hB (hL hA)⟩
  have := h (approachesLine_of_rightOf_zero_finite Z hfin) ρ hρ
  linarith

/-- **Extreme Deuring–Heilbronn is landing plus asymptotic Deuring–Heilbronn.** -/
theorem extremeDH_iff_landingLaw_and_DH :
    (¬ AbscissaLaw Z → (rightOf Z 0).Finite) ↔
      LandingLaw Z ∧ (¬ AbscissaLaw Z → ApproachesLine Z) := by
  refine ⟨fun h => ⟨fun hA => ?_, fun hn => approachesLine_of_rightOf_zero_finite Z (h hn)⟩,
    fun ⟨hL, hD⟩ hn => hL (hD hn)⟩
  by_cases hAAL : AbscissaLaw Z
  · exact rightOf_zero_finite_of_pure Z
      ((pure_iff_approachesLine_and_abscissaLaw Z).mpr ⟨hA, hAAL⟩)
  · exact h hAAL

/-- **AAL is three atoms**: the finite stratum, landing, and asymptotic Deuring–Heilbronn. -/
theorem abscissaLaw_iff_three_atoms :
    AbscissaLaw Z ↔
      AbscissaLawAt Z 0 ∧ LandingLaw Z ∧ (¬ AbscissaLaw Z → ApproachesLine Z) := by
  refine ⟨fun h => ⟨h 0 le_rfl, fun hA => rightOf_zero_finite_of_pure Z
      ((pure_iff_approachesLine_and_abscissaLaw Z).mpr ⟨hA, h⟩), fun hn => absurd h hn⟩, ?_⟩
  rintro ⟨hB, hL, hD⟩
  by_contra hn
  have hA := hD hn
  exact hn ((pure_iff_approachesLine_and_abscissaLaw Z).mp
    (pure_of_abscissaLawAt_zero Z hB (hL hA))).2

/-- **Purity is ZAL, the finite stratum, and landing.** -/
theorem pure_iff_approachesLine_and_abscissaLawAt_zero_and_landingLaw :
    Pure Z ↔ ApproachesLine Z ∧ AbscissaLawAt Z 0 ∧ LandingLaw Z := by
  refine ⟨fun h => ?_, fun ⟨hA, hB, hL⟩ => pure_of_abscissaLawAt_zero Z hB (hL hA)⟩
  obtain ⟨hA, hAAL⟩ := (pure_iff_approachesLine_and_abscissaLaw Z).mp h
  exact ⟨hA, hAAL 0 le_rfl, fun _ => rightOf_zero_finite_of_pure Z h⟩

/-- **The three atoms never fail in pairs.** -/
theorem landing_atoms_pairwise :
    (AbscissaLawAt Z 0 ∨ LandingLaw Z) ∧
      (AbscissaLawAt Z 0 ∨ (¬ AbscissaLaw Z → ApproachesLine Z)) ∧
      (LandingLaw Z ∨ (¬ AbscissaLaw Z → ApproachesLine Z)) := by
  by_cases hfin : (rightOf Z 0).Finite
  · have hA := approachesLine_of_rightOf_zero_finite Z hfin
    exact ⟨Or.inr fun _ => hfin, Or.inr fun _ => hA, Or.inr fun _ => hA⟩
  · have hB : AbscissaLawAt Z 0 := fun h => absurd h hfin
    refine ⟨Or.inl hB, Or.inl hB, ?_⟩
    by_cases hA : ApproachesLine Z
    · exact Or.inr fun _ => hA
    · exact Or.inl fun h => absurd h hA

/-- **Disjoint defect trichotomy.** A failure of the abscissa law fails exactly one atom. -/
theorem not_abscissaLaw_iff_sector :
    ¬ AbscissaLaw Z ↔
      (¬ AbscissaLawAt Z 0 ∧ LandingLaw Z ∧ (¬ AbscissaLaw Z → ApproachesLine Z)) ∨
      (AbscissaLawAt Z 0 ∧ ¬ LandingLaw Z ∧ (¬ AbscissaLaw Z → ApproachesLine Z)) ∨
      (AbscissaLawAt Z 0 ∧ LandingLaw Z ∧ ¬ (¬ AbscissaLaw Z → ApproachesLine Z)) := by
  have key := abscissaLaw_iff_three_atoms Z
  obtain ⟨h12, h13, h23⟩ := landing_atoms_pairwise Z
  revert key h12 h13 h23
  generalize AbscissaLaw Z = A
  generalize AbscissaLawAt Z 0 = B
  generalize LandingLaw Z = L
  generalize ApproachesLine Z = Q
  tauto

end General

/-! ### Tail character -/

/-- Finitely many zeros right of `½ + h` is a property of the zeros above any height. -/
theorem rightOf_finite_congr {Z Z' : ZeroConfig} {T : ℝ}
    (hT : ∀ z : ℂ, T < |z.im| → (z ∈ Z.carrier ↔ z ∈ Z'.carrier)) (h : ℝ) :
    (rightOf Z h).Finite → (rightOf Z' h).Finite := fun hfin =>
  (hfin.union (finite_of_abs_im_le Z' T)).subset fun z ⟨hz, hre⟩ => by
    by_cases hzT : T < |z.im|
    · exact Or.inl ⟨(hT z hzT).mpr hz, hre⟩
    · exact Or.inr ⟨hz, not_lt.mp hzT⟩

/-- **The landing law is a tail law.** -/
theorem landingLaw_isAsymptotic : IsAsymptotic LandingLaw := by
  rintro Z Z' ⟨T, hT⟩
  have h₁ := approachesLine_isAsymptotic Z Z' ⟨T, hT⟩
  have h₂ : (rightOf Z 0).Finite ↔ (rightOf Z' 0).Finite :=
    ⟨rightOf_finite_congr (fun z hz => (hT z hz).1) 0,
      rightOf_finite_congr (fun z hz => ((hT z hz).1).symm) 0⟩
  exact imp_congr h₁ h₂

/-- The zeros of `Z` strictly above the height `T`. -/
def restrictAbove (Z : ZeroConfig) (T : ℝ) : ZeroConfig where
  carrier := {z ∈ Z.carrier | T < |z.im|}
  mult := Z.mult
  one_le_mult z hz := Z.one_le_mult z hz.1
  strip z hz := Z.strip z hz.1
  reflect_mem z hz := ⟨Z.reflect_mem z hz.1, by rw [im_reflect]; exact hz.2⟩
  mult_reflect z hz := Z.mult_reflect z hz.1
  finite_window T₁ T₂ := (Z.finite_window T₁ T₂).subset fun _ ⟨hz, hw⟩ => ⟨hz.1, hw⟩

/-- The empty configuration. -/
def emptyConfig : ZeroConfig where
  carrier := ∅
  mult _ := 1
  one_le_mult _ h := h.elim
  strip _ h := h.elim
  reflect_mem _ h := h.elim
  mult_reflect _ h := h.elim
  finite_window _ _ := finite_empty.subset inter_subset_left

/-- `harmonicConfig` approaches the line with infinitely many zeros off it. -/
theorem not_landingLaw_harmonicConfig : ¬ LandingLaw harmonicConfig := fun hL =>
  harmonicConfig_separates_linearAbscissaLaw_from_finiteStratum.1
    (hL harmonicConfig_separates_linearAbscissaLaw_from_finiteStratum.2.2.1)

/-- **No verification up to a fixed height decides the landing law.** -/
theorem not_isLocalBelow_landingLaw (T₀ : ℝ) : ¬ IsLocalBelow T₀ LandingLaw := by
  intro hloc
  set Z := restrictAbove harmonicConfig (max T₀ 0)
  have hbelow : ∀ z : ℂ, |z.im| ≤ T₀ →
      (z ∈ emptyConfig.carrier ↔ z ∈ Z.carrier) ∧
        (z ∈ emptyConfig.carrier → emptyConfig.mult z = Z.mult z) := fun z hz =>
    ⟨⟨fun h => h.elim, fun h => absurd (h.2.trans_le hz) (not_lt.mpr (le_max_left _ _))⟩,
      fun h => h.elim⟩
  have hempty : LandingLaw emptyConfig := fun _ => finite_empty.subset fun _ h => h.1
  have habove : LandingLaw Z ↔ LandingLaw harmonicConfig :=
    landingLaw_isAsymptotic Z harmonicConfig ⟨max T₀ 0, fun z hz =>
      ⟨⟨fun h => h.1, fun h => ⟨h, hz⟩⟩, fun _ => rfl⟩⟩
  exact not_landingLaw_harmonicConfig (habove.mp ((hloc _ _ hbelow).mp hempty))

/-! ### Calibration: landing implies none of quasi-RH, ZAL, the finite stratum -/

/-- The configuration `½ ± (½ − 1/(n + 2)) + i(n + 1)`: zeros accumulate at `Re s = 1`. -/
def edgeConfig : ZeroConfig :=
  seqPairConfig (fun n : ℕ => 1 / 2 - 1 / ((n : ℝ) + 2))
    (fun n => by
      have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
      linarith)
    (fun n => by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith)

/-- **Landing holds without quasi-RH and without ZAL.** -/
theorem exists_landingLaw_not_quasiRH :
    ∃ Z : ZeroConfig, LandingLaw Z ∧ ¬ ApproachesLine Z ∧ ¬ zeroAbscissa Z < 1 := by
  have hre : ∀ n : ℕ, (seqUpper (fun n : ℕ => 1 / 2 - 1 / ((n : ℝ) + 2)) n).re =
      1 - 1 / ((n : ℝ) + 2) := fun n => by
    simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    ring
  have hinj : Function.Injective (seqUpper fun n : ℕ => 1 / 2 - 1 / ((n : ℝ) + 2)) := by
    intro m n hmn
    have him := congrArg Complex.im hmn
    simp only [seqUpper, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add] at him
    exact Nat.cast_injective (by linarith : (m : ℝ) = n)
  have hnotA : ¬ ApproachesLine edgeConfig := by
    intro hA
    refine (infinite_range_of_injective (hinj.comp (add_left_injective 3))).mono ?_
      (hA (1 / 4) (by norm_num))
    rintro _ ⟨n, rfl⟩
    refine ⟨Or.inl ⟨n + 3, rfl⟩, ?_⟩
    rw [Function.comp_apply, hre]
    have : 1 / (((n + 3 : ℕ) : ℝ) + 2) ≤ 1 / 5 :=
      one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  refine ⟨edgeConfig, fun hA => absurd hA hnotA, hnotA, fun hlt => ?_⟩
  -- a zero `1 − 1/(n + 2)` lies beyond any abscissa below `1`
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - zeroAbscissa edgeConfig))
  have hpos : 0 < 1 - zeroAbscissa edgeConfig := by linarith
  have hle := re_le_zeroAbscissa edgeConfig (ρ := seqUpper _ n) (Or.inl ⟨n, rfl⟩)
  rw [hre] at hle
  have h1 : 1 / ((n : ℝ) + 2) < 1 - zeroAbscissa edgeConfig := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hpos] at hn
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

/-- **Landing holds without the finite stratum**: one reflection pair. -/
theorem exists_landingLaw_not_abscissaLawAt_zero :
    ∃ Z : ZeroConfig, LandingLaw Z ∧ ¬ AbscissaLawAt Z 0 ∧ ¬ AbscissaLaw Z := by
  obtain ⟨_, hB⟩ := pairConfig_not_abscissaLaw (ρ := (3 / 4 : ℂ)) (by norm_num) (by norm_num)
  refine ⟨_, fun _ => ((finite_singleton _).insert _).subset fun _ hz => hz.1, hB,
    fun hA => hB (hA 0 le_rfl)⟩

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
