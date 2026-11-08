import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawIsNotAsymptotic
import GaloisForLFunctions.ZeroConfigurationGeometry.SymmetricShiftsPreserveTheAsymptoticAbscissaLaw
import GaloisForLFunctions.ZeroConfigurationGeometry.TheOneOffsAreFiniteOscillationsOfThePrimeError
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.BezoutValuationIncidence.TheCentredPrimeBandForcesAZeroFreeStrip

/-!
# The linear abscissa law: quantifier collapse, strict hierarchy, shift non-invariance, heat equivalence, and the finite-rank Chebyshev exponent

For a reflection-symmetric, ordinate-locally-finite strip configuration `Z` (`ZeroConfig`), let
`Θ(Z)` (`zeroAbscissa`) be the global zero abscissa `sup ({½} ∪ Re(Z))` and `Θ_∞(Z)`
(`asymptoticAbscissa`) be the asymptotic zero abscissa `inf {σ ≥ ½ : (rightOf Z (σ − ½)).Finite}`.

* **Equivalence at fixed slope and quantifier collapse.** For `C ≥ 0`, the linear abscissa bound
  `Θ(Z) − ½ ≤ C (Θ_∞(Z) − ½)` (`LinearAbscissaLawAt Z C`) is equivalent to the eventual-to-global
  implication `∀ h ≥ 0, (rightOf Z h).Finite → ∀ ρ ∈ Z, Re ρ ≤ ½ + C h`
  (`LinearEventualToGlobalAt Z C`). Existentially (`LinearAbscissaLaw Z := ∃ C, LinearAbscissaLawAt Z C`),
  the constant disappears: off `ApproachesLine Z` (`Θ_∞ > ½`) the bound holds unconditionally at
  `C = (Θ − ½)/(Θ_∞ − ½)`, while on `ApproachesLine Z` (`Θ_∞ = ½`) any real `C` forces `Θ = ½`.
  Thus `LinearAbscissaLaw Z ↔ (ApproachesLine Z → Pure Z) ↔ (ApproachesLine Z → AbscissaLaw Z)`,
  `Pure Z ↔ ApproachesLine Z ∧ LinearAbscissaLawAt Z C` for every `C : ℝ`, and
  `AbscissaLaw Z ↔ ∀ C > 1, LinearAbscissaLawAt Z C`.
* **Strict hierarchy and scale-separation impossibility.** Explicit strip configurations separate
  every adjacent level:
  `Pure ⊊ AbscissaLaw ⊊ LinearAbscissaLawAt C₁ ⊊ LinearAbscissaLawAt C₂ ⊊ LinearAbscissaLaw ⊊ AbscissaLawAt · 0`
  for `1 < C₁ < C₂`. In particular `harmonicConfig` has infinitely many off-line zeros (so the
  finite-stratum law `AbscissaLawAt · 0` holds vacuously), satisfies `ApproachesLine`, and violates
  `LinearAbscissaLaw`. Neither asymptotic properties (`IsAsymptotic`) nor bounded-height properties
  (`IsLocalBelow`) can decide `LinearAbscissaLaw`, nor `LinearAbscissaLawAt · C` on configurations
  with infinitely many off-line zeros.
* **Specialization to `ζ` and failure of symmetric-shift invariance.** On `zetaZeroConfig`,
  `zeroAbscissa = zetaZeroAbscissa` and `asymptoticAbscissa = zetaAsymptoticAbscissa`. Existential
  linear AAL for `ζ` (`ZetaLinearAbscissaLaw`) is unconditionally equivalent to
  `ZerosApproachLine → RiemannHypothesis` (strictly above the finite-stratum implication
  `FiniteOffLine → RiemannHypothesis`). Unlike `AsymptoticAbscissaLaw`, linear AAL is not invariant
  under symmetric shifts: for every `a > 0`, `ξ(s + a)ξ(s − a)` satisfies the linear
  eventual-to-global law unconditionally with `C = 1 + 1/(2a)`, whereas a uniform constant `C` over
  all `a > 0` recovers `ZetaLinearAbscissaLawAt C`.
* **De Bruijn–Newman heat equivalence.** Every positive heat time `riemannHeat t` (`t > 0`) has
  vanishing asymptotic off-axis depth; hence linear AAL along `t → 0⁺`, even with an arbitrary
  `t`-dependent constant `C(t)`, is unconditionally equivalent to `RiemannHypothesis`.
* **Finite-rank Chebyshev error exponent.** Subtracting a finite complex exponential sum
  `Σ_{z ∈ S} d(z) x^z` from `ψ(x) − x` lowers its polynomial growth exponent `≥ ½` down to `Θ_∞`
  and never below: `zetaAsymptoticAbscissa` equals the infimum of exponents `σ ≥ ½` of `ψ(x) − x`
  modulo finite exponential sums, and `ZetaLinearAbscissaLawAt C` (`C ≥ 1`) is equivalent to
  finite-rank Chebyshev self-improvement with factor `C`.
-/

open Complex Filter Topology MeasureTheory Set Asymptotics
open scoped ComplexConjugate
open ArithmeticFunction (vonMangoldt)
open RHTower

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open ArithmeticCastelnuovoSeveri

namespace ConfigAbscissa

/-! ### Abscissa invariants and the linear abscissa law on `ZeroConfig` -/

section General

variable (Z : ZeroConfig)

/-- The set of real parts `≥ ½` above which `Z` has only finitely many zeros. -/
def asymptoticAbscissaSet : Set ℝ :=
  {σ : ℝ | 1 / 2 ≤ σ ∧ (rightOf Z (σ - 1 / 2)).Finite}

/-- Global zero abscissa `Θ(Z) = sup ({½} ∪ Re(Z))`. -/
def zeroAbscissa : ℝ :=
  sSup (insert (1 / 2 : ℝ) (Complex.re '' Z.carrier))

/-- Asymptotic zero abscissa `Θ_∞(Z) = inf {σ ≥ ½ : (rightOf Z (σ − ½)).Finite}`. -/
def asymptoticAbscissa : ℝ :=
  sInf (asymptoticAbscissaSet Z)

/-- **Linear abscissa law at slope `C`**: `Θ(Z) − ½ ≤ C (Θ_∞(Z) − ½)`. -/
def LinearAbscissaLawAt (C : ℝ) : Prop :=
  zeroAbscissa Z - 1 / 2 ≤ C * (asymptoticAbscissa Z - 1 / 2)

/-- **Eventual-to-global linear law at slope `C`**: finitely many zeros right of `½ + h` force all
zeros left of `½ + C h`, for every `h ≥ 0`. -/
def LinearEventualToGlobalAt (C : ℝ) : Prop :=
  ∀ h : ℝ, 0 ≤ h → (rightOf Z h).Finite → ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + C * h

/-- **Existential linear abscissa law**: `∃ C, Θ(Z) − ½ ≤ C (Θ_∞(Z) − ½)`. -/
def LinearAbscissaLaw : Prop :=
  ∃ C : ℝ, LinearAbscissaLawAt Z C

theorem bddAbove_re_insert : BddAbove (insert (1 / 2 : ℝ) (Complex.re '' Z.carrier)) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨z, hz, rfl⟩)
  · norm_num
  · exact (Z.strip z hz).2

theorem half_le_zeroAbscissa : (1 / 2 : ℝ) ≤ zeroAbscissa Z :=
  le_csSup (bddAbove_re_insert Z) (mem_insert _ _)

theorem re_le_zeroAbscissa {ρ : ℂ} (hρ : ρ ∈ Z.carrier) : ρ.re ≤ zeroAbscissa Z :=
  le_csSup (bddAbove_re_insert Z) (mem_insert_of_mem _ ⟨ρ, hρ, rfl⟩)

theorem zeroAbscissa_le_iff {σ : ℝ} :
    zeroAbscissa Z ≤ σ ↔ 1 / 2 ≤ σ ∧ ∀ ρ ∈ Z.carrier, ρ.re ≤ σ := by
  constructor
  · intro h
    exact ⟨(half_le_zeroAbscissa Z).trans h, fun ρ hρ => (re_le_zeroAbscissa Z hρ).trans h⟩
  · rintro ⟨h12, hall⟩
    refine csSup_le (insert_nonempty _ _) ?_
    rintro x (rfl | ⟨ρ, hρ, rfl⟩)
    · exact h12
    · exact hall ρ hρ

theorem zeroAbscissa_le_one : zeroAbscissa Z ≤ 1 :=
  (zeroAbscissa_le_iff Z).mpr ⟨by norm_num, fun ρ hρ => (Z.strip ρ hρ).2⟩

theorem one_mem_asymptoticAbscissaSet : (1 : ℝ) ∈ asymptoticAbscissaSet Z := by
  refine ⟨by norm_num, finite_empty.subset fun ρ ⟨hρ, hlt⟩ => ?_⟩
  have := (Z.strip ρ hρ).2
  linarith

theorem asymptoticAbscissaSet_nonempty : (asymptoticAbscissaSet Z).Nonempty :=
  ⟨1, one_mem_asymptoticAbscissaSet Z⟩

theorem bddBelow_asymptoticAbscissaSet : BddBelow (asymptoticAbscissaSet Z) :=
  ⟨1 / 2, fun _ h => h.1⟩

theorem zeroAbscissa_mem_asymptoticAbscissaSet : zeroAbscissa Z ∈ asymptoticAbscissaSet Z := by
  refine ⟨half_le_zeroAbscissa Z, finite_empty.subset fun ρ ⟨hρ, hlt⟩ => ?_⟩
  have := re_le_zeroAbscissa Z hρ
  linarith

theorem half_le_asymptoticAbscissa : (1 / 2 : ℝ) ≤ asymptoticAbscissa Z :=
  le_csInf (asymptoticAbscissaSet_nonempty Z) fun _ h => h.1

theorem asymptoticAbscissa_le_zeroAbscissa : asymptoticAbscissa Z ≤ zeroAbscissa Z :=
  csInf_le (bddBelow_asymptoticAbscissaSet Z) (zeroAbscissa_mem_asymptoticAbscissaSet Z)

theorem asymptoticAbscissa_le_one : asymptoticAbscissa Z ≤ 1 :=
  (asymptoticAbscissa_le_zeroAbscissa Z).trans (zeroAbscissa_le_one Z)

theorem pure_iff_zeroAbscissa_eq_half : Pure Z ↔ zeroAbscissa Z = 1 / 2 := by
  rw [pure_iff_forall_re_le]
  constructor
  · intro h
    exact le_antisymm ((zeroAbscissa_le_iff Z).mpr ⟨le_rfl, h⟩) (half_le_zeroAbscissa Z)
  · intro heq ρ hρ
    exact (re_le_zeroAbscissa Z hρ).trans heq.le

theorem approachesLine_iff_asymptoticAbscissa_eq_half :
    ApproachesLine Z ↔ asymptoticAbscissa Z = 1 / 2 := by
  constructor
  · intro hA
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (half_le_asymptoticAbscissa Z)
    refine csInf_le (bddBelow_asymptoticAbscissaSet Z) ⟨by linarith, ?_⟩
    simpa [add_sub_cancel_left] using hA ε hε
  · intro heq h hh
    have hlt : asymptoticAbscissa Z < 1 / 2 + h := by rw [heq]; linarith
    obtain ⟨σ, ⟨_, hfin⟩, hσlt⟩ := exists_lt_of_csInf_lt (asymptoticAbscissaSet_nonempty Z) hlt
    exact hfin.subset fun ρ ⟨hρ, hre⟩ => ⟨hρ, by linarith⟩

theorem abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa :
    AbscissaLaw Z ↔ asymptoticAbscissa Z = zeroAbscissa Z := by
  constructor
  · intro hA
    refine le_antisymm (asymptoticAbscissa_le_zeroAbscissa Z)
      (le_csInf (asymptoticAbscissaSet_nonempty Z) fun σ ⟨h12, hfin⟩ => ?_)
    refine (zeroAbscissa_le_iff Z).mpr ⟨h12, fun ρ hρ => ?_⟩
    have := hA (σ - 1 / 2) (by linarith) hfin ρ hρ
    linarith
  · intro heq h hh hfin ρ hρ
    have hmem : 1 / 2 + h ∈ asymptoticAbscissaSet Z :=
      ⟨by linarith, by simpa [add_sub_cancel_left] using hfin⟩
    have hle : zeroAbscissa Z ≤ 1 / 2 + h := by
      rw [← heq]
      exact csInf_le (bddBelow_asymptoticAbscissaSet Z) hmem
    exact (re_le_zeroAbscissa Z hρ).trans hle

/-- **Equivalence of the abscissa inequality and eventual-to-global implication** for `C ≥ 0`. -/
theorem linearAbscissaLawAt_iff_eventualToGlobalAt {C : ℝ} (hC : 0 ≤ C) :
    LinearAbscissaLawAt Z C ↔ LinearEventualToGlobalAt Z C := by
  constructor
  · intro hL h hh hfin ρ hρ
    have hmem : 1 / 2 + h ∈ asymptoticAbscissaSet Z :=
      ⟨by linarith, by simpa [add_sub_cancel_left] using hfin⟩
    have hle : asymptoticAbscissa Z - 1 / 2 ≤ h := by
      have := csInf_le (bddBelow_asymptoticAbscissaSet Z) hmem
      linarith
    have hmul : C * (asymptoticAbscissa Z - 1 / 2) ≤ C * h := mul_le_mul_of_nonneg_left hle hC
    have hρΘ := re_le_zeroAbscissa Z hρ
    unfold LinearAbscissaLawAt at hL
    linarith
  · intro hE
    unfold LinearAbscissaLawAt
    rcases eq_or_lt_of_le hC with rfl | hCpos
    · rw [zero_mul, sub_nonpos]
      refine (zeroAbscissa_le_iff Z).mpr ⟨le_rfl, fun ρ hρ => ?_⟩
      have := hE (1 / 2) (by norm_num) (by
        simpa [show (1 / 2 : ℝ) + 1 / 2 - 1 / 2 = 1 / 2 by ring] using
          (one_mem_asymptoticAbscissaSet Z).2) ρ hρ
      linarith
    · rw [← div_le_iff₀' hCpos]
      refine le_of_le_of_eq (c := sInf ((fun σ : ℝ => σ - 1 / 2) '' asymptoticAbscissaSet Z)) ?_ ?_
      · refine le_csInf ((asymptoticAbscissaSet_nonempty Z).image _) ?_
        rintro _ ⟨σ, ⟨h12, hfin⟩, rfl⟩
        rw [div_le_iff₀' hCpos]
        have hΘ : zeroAbscissa Z ≤ 1 / 2 + C * (σ - 1 / 2) :=
          (zeroAbscissa_le_iff Z).mpr ⟨by nlinarith, hE (σ - 1 / 2) (by linarith) hfin⟩
        linarith
      · have htr : (fun σ : ℝ => σ - 1 / 2) = (fun σ : ℝ => -1 / 2 + σ) := by
          funext σ; ring
        rw [htr, Real.sInf_image_add]
        unfold asymptoticAbscissa
        ring

theorem linearAbscissaLawAt_mono {C₁ C₂ : ℝ} (h12 : C₁ ≤ C₂) (h : LinearAbscissaLawAt Z C₁) :
    LinearAbscissaLawAt Z C₂ :=
  h.trans (mul_le_mul_of_nonneg_right h12 (sub_nonneg.mpr (half_le_asymptoticAbscissa Z)))

/-- Off `ApproachesLine Z`, the linear abscissa law holds unconditionally at the exact ratio. -/
theorem linearAbscissaLawAt_of_not_approachesLine (hnot : ¬ ApproachesLine Z) :
    LinearAbscissaLawAt Z ((zeroAbscissa Z - 1 / 2) / (asymptoticAbscissa Z - 1 / 2)) := by
  have hne : asymptoticAbscissa Z ≠ 1 / 2 :=
    mt (approachesLine_iff_asymptoticAbscissa_eq_half Z).mpr hnot
  have hpos : 0 < asymptoticAbscissa Z - 1 / 2 :=
    sub_pos.mpr (lt_of_le_of_ne' (half_le_asymptoticAbscissa Z) hne)
  unfold LinearAbscissaLawAt
  rw [div_mul_cancel₀ _ hpos.ne']

/-- **Purity is ZAL plus the linear abscissa law at any fixed real `C`.** -/
theorem pure_iff_approachesLine_and_linearAbscissaLawAt (C : ℝ) :
    Pure Z ↔ ApproachesLine Z ∧ LinearAbscissaLawAt Z C := by
  rw [pure_iff_zeroAbscissa_eq_half, approachesLine_iff_asymptoticAbscissa_eq_half]
  constructor
  · intro hP
    have hle := asymptoticAbscissa_le_zeroAbscissa Z
    have hZ : asymptoticAbscissa Z = 1 / 2 :=
      le_antisymm (hle.trans hP.le) (half_le_asymptoticAbscissa Z)
    refine ⟨hZ, ?_⟩
    unfold LinearAbscissaLawAt
    rw [hP, hZ]
    norm_num
  · rintro ⟨hZ, hL⟩
    unfold LinearAbscissaLawAt at hL
    rw [hZ, sub_self, mul_zero] at hL
    exact le_antisymm (by linarith) (half_le_zeroAbscissa Z)

/-- **AAL is the `C ↓ 1` limit of the linear abscissa law.** -/
theorem abscissaLaw_iff_forall_gt_one_linearAbscissaLawAt :
    AbscissaLaw Z ↔ ∀ C : ℝ, 1 < C → LinearAbscissaLawAt Z C := by
  rw [abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa]
  constructor
  · intro heq C hC
    unfold LinearAbscissaLawAt
    rw [← heq]
    have h0 : 0 ≤ asymptoticAbscissa Z - 1 / 2 := sub_nonneg.mpr (half_le_asymptoticAbscissa Z)
    nlinarith
  · intro hall
    refine le_antisymm (asymptoticAbscissa_le_zeroAbscissa Z) ?_
    by_contra hlt
    push Not at hlt
    rcases eq_or_lt_of_le (half_le_asymptoticAbscissa Z) with heq | hpos
    · have h1 := hall 2 one_lt_two
      unfold LinearAbscissaLawAt at h1
      rw [← heq] at h1
      linarith
    · set C : ℝ := 1 + (zeroAbscissa Z - asymptoticAbscissa Z) /
          (2 * (asymptoticAbscissa Z - 1 / 2)) with hCdef
      have hC1 : 1 < C := by
        rw [hCdef]
        have : 0 < (zeroAbscissa Z - asymptoticAbscissa Z) /
            (2 * (asymptoticAbscissa Z - 1 / 2)) :=
          div_pos (by linarith) (by linarith)
        linarith
      have hL := hall C hC1
      unfold LinearAbscissaLawAt at hL
      have hval : C * (asymptoticAbscissa Z - 1 / 2) =
          (asymptoticAbscissa Z - 1 / 2) + (zeroAbscissa Z - asymptoticAbscissa Z) / 2 := by
        rw [hCdef, add_mul, one_mul, div_mul_eq_mul_div]
        have hne : asymptoticAbscissa Z - 1 / 2 ≠ 0 := by linarith
        field_simp
      rw [hval] at hL
      linarith

/-- **Quantifier collapse on `ZeroConfig`.** Existential linear AAL collapses to
`ApproachesLine Z → Pure Z`. -/
theorem linearAbscissaLaw_tfae :
    [LinearAbscissaLaw Z,
      ∃ C : ℝ, 1 ≤ C ∧ LinearAbscissaLawAt Z C,
      ∃ C : ℝ, LinearEventualToGlobalAt Z C,
      asymptoticAbscissa Z = 1 / 2 → zeroAbscissa Z = 1 / 2,
      ApproachesLine Z → Pure Z,
      ApproachesLine Z → AbscissaLaw Z,
      ¬ ApproachesLine Z ∨ Pure Z].TFAE := by
  tfae_have 1 → 5 := by
    rintro ⟨C, hC⟩ hA
    exact (pure_iff_approachesLine_and_linearAbscissaLawAt Z C).mpr ⟨hA, hC⟩
  tfae_have 5 → 2 := by
    intro himp
    by_cases hA : ApproachesLine Z
    · refine ⟨1, le_rfl, ?_⟩
      exact ((pure_iff_approachesLine_and_linearAbscissaLawAt Z 1).mp (himp hA)).2
    · set C := (zeroAbscissa Z - 1 / 2) / (asymptoticAbscissa Z - 1 / 2)
      have hne : asymptoticAbscissa Z ≠ 1 / 2 :=
        mt (approachesLine_iff_asymptoticAbscissa_eq_half Z).mpr hA
      have hpos : 0 < asymptoticAbscissa Z - 1 / 2 :=
        sub_pos.mpr (lt_of_le_of_ne' (half_le_asymptoticAbscissa Z) hne)
      have hge1 : 1 ≤ C := (one_le_div hpos).mpr
        (sub_le_sub_right (asymptoticAbscissa_le_zeroAbscissa Z) _)
      exact ⟨C, hge1, linearAbscissaLawAt_of_not_approachesLine Z hA⟩
  tfae_have 2 → 3 := by
    rintro ⟨C, hC1, hC⟩
    exact ⟨C, (linearAbscissaLawAt_iff_eventualToGlobalAt Z (by linarith)).mp hC⟩
  tfae_have 3 → 1 := by
    rintro ⟨C, hC⟩
    by_cases h0 : 0 ≤ C
    · exact ⟨C, (linearAbscissaLawAt_iff_eventualToGlobalAt Z h0).mpr hC⟩
    · refine ⟨0, (linearAbscissaLawAt_iff_eventualToGlobalAt Z le_rfl).mpr fun h hh hfin ρ hρ => ?_⟩
      have := hC h hh hfin ρ hρ
      nlinarith
  tfae_have 4 ↔ 5 := by
    rw [approachesLine_iff_asymptoticAbscissa_eq_half, pure_iff_zeroAbscissa_eq_half]
  tfae_have 5 ↔ 6 := by
    constructor
    · intro h hA
      exact ((pure_iff_approachesLine_and_abscissaLaw Z).mp (h hA)).2
    · intro h hA
      exact (pure_iff_approachesLine_and_abscissaLaw Z).mpr ⟨hA, h hA⟩
  tfae_have 5 ↔ 7 := imp_iff_not_or
  tfae_finish

/-- Existential linear AAL implies the finite-stratum law (`h = 0`). -/
theorem abscissaLawAt_zero_of_linearAbscissaLaw (hL : LinearAbscissaLaw Z) :
    AbscissaLawAt Z 0 := by
  intro hfin ρ hρ
  have hA : ApproachesLine Z := fun h hh =>
    hfin.subset fun z ⟨hz, hre⟩ => ⟨hz, by linarith⟩
  have himp : ApproachesLine Z → Pure Z :=
    ((linearAbscissaLaw_tfae Z).out 0 4).mp hL
  rw [himp hA ρ hρ]
  norm_num

end General

/-! ### Explicit witness configurations: strict hierarchy and two-scale impossibility -/

/-- Upper point of the `n`-th horizontal pair at height `n + 1` and depth `δ n`. -/
def seqUpper (δ : ℕ → ℝ) (n : ℕ) : ℂ :=
  ((1 / 2 + δ n : ℝ) : ℂ) + ((n + 1 : ℝ) : ℂ) * I

/-- Lower point `1 − conj (seqUpper δ n)` of the `n`-th horizontal pair. -/
def seqLower (δ : ℕ → ℝ) (n : ℕ) : ℂ :=
  ((1 / 2 - δ n : ℝ) : ℂ) + ((n + 1 : ℝ) : ℂ) * I

theorem reflect_seqUpper (δ : ℕ → ℝ) (n : ℕ) :
    reflect (seqUpper δ n) = seqLower δ n := by
  apply Complex.ext <;> simp [reflect, seqUpper, seqLower] <;> ring

theorem reflect_seqLower (δ : ℕ → ℝ) (n : ℕ) :
    reflect (seqLower δ n) = seqUpper δ n := by
  apply Complex.ext <;> simp [reflect, seqUpper, seqLower] <;> ring

/-- Strip configuration consisting of the pairs `½ ± δ_n + i(n + 1)` (`n : ℕ`) with multiplicity 1. -/
def seqPairConfig (δ : ℕ → ℝ) (h0 : ∀ n, 0 ≤ δ n) (h12 : ∀ n, δ n ≤ 1 / 2) : ZeroConfig where
  carrier := range (seqUpper δ) ∪ range (seqLower δ)
  mult _ := 1
  one_le_mult _ _ := le_rfl
  strip := by
    rintro z (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      exact ⟨by linarith [h0 n], by linarith [h12 n]⟩
    · simp only [seqLower, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      exact ⟨by linarith [h12 n], by linarith [h0 n]⟩
  reflect_mem := by
    rintro z (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact Or.inr ⟨n, (reflect_seqUpper δ n).symm⟩
    · exact Or.inl ⟨n, (reflect_seqLower δ n).symm⟩
  mult_reflect _ _ := rfl
  finite_window T₁ T₂ := by
    set N : ℕ := ⌊max T₂ 0⌋₊ + 1
    refine (((Finset.range N).finite_toSet.image (seqUpper δ)).union
      ((Finset.range N).finite_toSet.image (seqLower δ))).subset ?_
    rintro z ⟨(⟨n, rfl⟩ | ⟨n, rfl⟩), _, hz₂⟩
    · simp only [seqUpper, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at hz₂
      have hn : n < N := by
        have hle : (n : ℝ) ≤ max T₂ 0 := by linarith [le_max_left T₂ 0]
        exact Nat.lt_succ_of_le (Nat.le_floor hle)
      exact Or.inl ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hn), rfl⟩
    · simp only [seqLower, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at hz₂
      have hn : n < N := by
        have hle : (n : ℝ) ≤ max T₂ 0 := by linarith [le_max_left T₂ 0]
        exact Nat.lt_succ_of_le (Nat.le_floor hle)
      exact Or.inr ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hn), rfl⟩

/-- Harmonic accumulating configuration `½ ± 1/(n + 3) + i(n + 1)`: infinitely many off-line zeros,
`ApproachesLine`, global abscissa `5/6`, and failure of `LinearAbscissaLaw`. -/
def harmonicConfig : ZeroConfig :=
  seqPairConfig (fun n : ℕ => 1 / ((n : ℝ) + 3))
    (fun _ => by positivity)
    (fun n => by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Nat.cast_nonneg (α := ℝ) n])

/-- **Strict separation of existential linear AAL from the finite-stratum law.** `harmonicConfig`
has infinitely many off-line zeros (hence satisfies `AbscissaLawAt · 0`), satisfies
`ApproachesLine` (`Θ_∞ = ½`), has `Θ = 5/6`, and violates `LinearAbscissaLaw`. -/
theorem harmonicConfig_separates_linearAbscissaLaw_from_finiteStratum :
    (rightOf harmonicConfig 0).Infinite ∧
      AbscissaLawAt harmonicConfig 0 ∧
      ApproachesLine harmonicConfig ∧
      zeroAbscissa harmonicConfig = 5 / 6 ∧
      ¬ LinearAbscissaLaw harmonicConfig := by
  have hinj : Function.Injective (seqUpper fun n : ℕ => 1 / ((n : ℝ) + 3)) := by
    intro m n hmn
    have him := congrArg Complex.im hmn
    simp only [seqUpper, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add] at him
    exact Nat.cast_injective (by linarith : (m : ℝ) = n)
  have hinf : (rightOf harmonicConfig 0).Infinite := by
    refine (infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Or.inl ⟨n, rfl⟩, ?_⟩
    simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 3) := by positivity
    linarith
  have hB13 : AbscissaLawAt harmonicConfig 0 := fun hfin => absurd hfin hinf
  have hZAL : ApproachesLine harmonicConfig := by
    intro h hh
    set N : ℕ := ⌈1 / h⌉₊ + 1
    refine ((Finset.range N).finite_toSet.image
      (seqUpper fun n : ℕ => 1 / ((n : ℝ) + 3))).subset ?_
    rintro z ⟨(⟨n, rfl⟩ | ⟨n, rfl⟩), hre⟩
    · simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero] at hre
      have hlt : h < 1 / ((n : ℝ) + 3) := by linarith
      have hn : (n : ℝ) + 3 < 1 / h := (lt_div_iff₀ hh).mpr ((lt_div_iff₀ (by positivity)).mp hlt)
      have hnN : n < N := by
        have hceil : 1 / h ≤ (⌈1 / h⌉₊ : ℝ) := Nat.le_ceil _
        have hlt' : (n : ℝ) < (⌈1 / h⌉₊ : ℝ) := by linarith
        exact Nat.lt_succ_of_le (Nat.cast_lt.mp hlt').le
      exact ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hnN), rfl⟩
    · simp only [seqLower, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero] at hre
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 3) := by positivity
      linarith
  have hΘ : zeroAbscissa harmonicConfig = 5 / 6 := by
    refine le_antisymm ?_ ?_
    · refine (zeroAbscissa_le_iff harmonicConfig).mpr ⟨by norm_num, ?_⟩
      rintro z (⟨n, rfl⟩ | ⟨n, rfl⟩)
      · simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero]
        have hle : 1 / ((n : ℝ) + 3) ≤ 1 / 3 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
      · simp only [seqLower, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero]
        have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 3) := by positivity
        linarith
    · have hmem : seqUpper (fun n : ℕ => 1 / ((n : ℝ) + 3)) 0 ∈ harmonicConfig.carrier :=
        Or.inl ⟨0, rfl⟩
      have h0 := re_le_zeroAbscissa harmonicConfig hmem
      simp only [seqUpper, Nat.cast_zero, zero_add, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero] at h0
      linarith
  have hnotL : ¬ LinearAbscissaLaw harmonicConfig := by
    intro hL
    have hP := ((linearAbscissaLaw_tfae harmonicConfig).out 0 4).mp hL hZAL
    have h12 := (pure_iff_zeroAbscissa_eq_half harmonicConfig).mp hP
    linarith
  exact ⟨hinf, hB13, hZAL, hΘ, hnotL⟩

/-- Two-scale witness configuration with asymptotic excess `a`, single-bump excess `b` at index `n₀`,
and `0 ≤ a ≤ b ≤ ½`. -/
def bumpRatioConfig (a b : ℝ) (n₀ : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    ZeroConfig :=
  seqPairConfig (fun n : ℕ => if n = n₀ then b else a)
    (fun n => by split_ifs <;> linarith)
    (fun n => by split_ifs <;> linarith)

theorem bumpRatioConfig_abscissas {a b : ℝ} (n₀ : ℕ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) :
    zeroAbscissa (bumpRatioConfig a b n₀ ha hab hb) = 1 / 2 + b ∧
      asymptoticAbscissa (bumpRatioConfig a b n₀ ha hab hb) = 1 / 2 + a := by
  set Z := bumpRatioConfig a b n₀ ha hab hb
  set δ : ℕ → ℝ := fun n => if n = n₀ then b else a
  have hΘ : zeroAbscissa Z = 1 / 2 + b := by
    refine le_antisymm ?_ ?_
    · refine (zeroAbscissa_le_iff Z).mpr ⟨by linarith, ?_⟩
      rintro z (⟨n, rfl⟩ | ⟨n, rfl⟩)
      · simp only [seqUpper, δ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero]
        split_ifs <;> linarith
      · simp only [seqLower, δ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero]
        split_ifs <;> linarith
    · have hmem : seqUpper δ n₀ ∈ Z.carrier := Or.inl ⟨n₀, rfl⟩
      have h0 := re_le_zeroAbscissa Z hmem
      simp only [seqUpper, δ, if_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, add_zero] at h0
      exact h0
  have hΘinf : asymptoticAbscissa Z = 1 / 2 + a := by
    refine le_antisymm ?_ ?_
    · refine csInf_le (bddBelow_asymptoticAbscissaSet Z) ⟨by linarith, ?_⟩
      refine (finite_singleton (seqUpper δ n₀)).subset ?_
      rintro z ⟨(⟨n, rfl⟩ | ⟨n, rfl⟩), hre⟩
      · simp only [seqUpper, δ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero] at hre
        by_cases hn : n = n₀
        · subst hn; exact mem_singleton _
        · simp only [hn, if_false] at hre; linarith
      · simp only [seqLower, δ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero] at hre
        split_ifs at hre <;> linarith
    · refine le_csInf (asymptoticAbscissaSet_nonempty Z) fun σ ⟨h12, hfin⟩ => ?_
      by_contra hlt
      push Not at hlt
      have hinj : Function.Injective (fun k : ℕ => seqUpper δ (n₀ + 1 + k)) := by
        intro j k hjk
        have him := congrArg Complex.im hjk
        simp only [seqUpper, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
          add_zero, zero_add] at him
        have : (j : ℝ) = k := by push_cast at him; linarith
        exact Nat.cast_injective this
      refine (infinite_range_of_injective hinj) (hfin.subset ?_)
      rintro _ ⟨k, rfl⟩
      refine ⟨Or.inl ⟨n₀ + 1 + k, rfl⟩, ?_⟩
      have hne : n₀ + 1 + k ≠ n₀ := by omega
      simp only [seqUpper, δ, hne, if_false, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero]
      linarith
  exact ⟨hΘ, hΘinf⟩

/-- **Strict separation of slopes.** For every `1 ≤ C₁ < C₂`, there exists a zero configuration
satisfying `LinearAbscissaLawAt · C₂` and violating `LinearAbscissaLawAt · C₁`. -/
theorem exists_linearAbscissaLawAt_not_at_of_lt {C₁ C₂ : ℝ} (hC₁ : 1 ≤ C₁) (hlt : C₁ < C₂) :
    ∃ Z : ZeroConfig, (rightOf Z 0).Infinite ∧ ¬ ApproachesLine Z ∧
      LinearAbscissaLawAt Z C₂ ∧ ¬ LinearAbscissaLawAt Z C₁ := by
  have hC₂ : 0 < C₂ := by linarith
  set a : ℝ := 1 / (4 * C₂)
  set b : ℝ := (C₁ + C₂) / (8 * C₂)
  have ha0 : 0 < a := by positivity
  have hab : a < b := by
    dsimp [a, b]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hb12 : b ≤ 1 / 2 := by
    dsimp [b]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set Z := bumpRatioConfig a b 0 ha0.le hab.le hb12
  obtain ⟨hΘ, hΘinf⟩ := bumpRatioConfig_abscissas 0 ha0.le hab.le hb12
  have hnotZAL : ¬ ApproachesLine Z := by
    rw [approachesLine_iff_asymptoticAbscissa_eq_half, hΘinf]
    linarith
  have hinf : (rightOf Z 0).Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact hnotZAL fun h hh => hfin.subset fun z ⟨hz, hre⟩ => ⟨hz, by linarith⟩
  have hL₂ : LinearAbscissaLawAt Z C₂ := by
    unfold LinearAbscissaLawAt
    rw [hΘ, hΘinf]
    have hval : C₂ * (1 / 2 + a - 1 / 2) = 1 / 4 := by
      dsimp [a]; field_simp; ring
    have hb4 : b < 1 / 4 := by
      dsimp [b]
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hnotL₁ : ¬ LinearAbscissaLawAt Z C₁ := by
    unfold LinearAbscissaLawAt
    rw [hΘ, hΘinf, not_le]
    have hval : C₁ * (1 / 2 + a - 1 / 2) = C₁ / (4 * C₂) := by
      dsimp [a]; ring
    rw [hval]
    have : C₁ / (4 * C₂) < b := by
      dsimp [b]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  exact ⟨Z, hinf, hnotZAL, hL₂, hnotL₁⟩

/-- Existential linear AAL is strictly weaker than `AbscissaLaw`. -/
theorem exists_linearAbscissaLaw_not_abscissaLaw :
    ∃ Z : ZeroConfig, LinearAbscissaLaw Z ∧ ¬ AbscissaLaw Z := by
  obtain ⟨Z, _, _, hL2, hnotL1⟩ := exists_linearAbscissaLawAt_not_at_of_lt le_rfl one_lt_two
  refine ⟨Z, ⟨2, hL2⟩, fun hA => hnotL1 ?_⟩
  rw [abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa] at hA
  unfold LinearAbscissaLawAt
  rw [hA, one_mul]

/-- **No asymptotic property decides existential linear AAL.** -/
theorem exists_not_linearAbscissaLaw_of_isAsymptotic {P : ZeroConfig → Prop}
    (hP : IsAsymptotic P) {Z : ZeroConfig} (hZ : Pure Z) (hPZ : P Z) :
    ∃ Z' : ZeroConfig, P Z' ∧ ApproachesLine Z' ∧ ¬ LinearAbscissaLaw Z' := by
  obtain ⟨Z', hPZ', hZAL, hnot0⟩ := exists_not_abscissaLawAt_zero_of_isAsymptotic hP hZ hPZ
  exact ⟨Z', hPZ', hZAL, mt (abscissaLawAt_zero_of_linearAbscissaLaw Z') hnot0⟩

/-- **No bounded-height verification decides existential linear AAL.** -/
theorem exists_not_linearAbscissaLaw_of_isLocalBelow {T₀ : ℝ} {P : ZeroConfig → Prop}
    (hP : IsLocalBelow T₀ P) {Z : ZeroConfig} (hZ : Pure Z) (hPZ : P Z) :
    ∃ Z' : ZeroConfig, P Z' ∧ ApproachesLine Z' ∧ ¬ LinearAbscissaLaw Z' := by
  obtain ⟨Z', hPZ', hZAL, hnot0⟩ := exists_not_abscissaLawAt_zero_of_isLocalBelow hP hZ hPZ
  exact ⟨Z', hPZ', hZAL, mt (abscissaLawAt_zero_of_linearAbscissaLaw Z') hnot0⟩

/-- **No asymptotic or bounded-height property decides `LinearAbscissaLawAt · C` (`1 ≤ C < 2`)**,
even among configurations with infinitely many off-line zeros. -/
theorem exists_infinite_offLine_not_linearAbscissaLawAt_of_isAsymptotic_and_isLocalBelow
    {C : ℝ} (hC1 : 1 ≤ C) (hC2 : C < 2) :
    ∃ Z₀ : ZeroConfig, AbscissaLaw Z₀ ∧ (rightOf Z₀ 0).Infinite ∧
      (∀ P : ZeroConfig → Prop, IsAsymptotic P → P Z₀ →
        ∃ Z' : ZeroConfig, P Z' ∧ (rightOf Z' 0).Infinite ∧ ¬ LinearAbscissaLawAt Z' C) ∧
      (∀ (T₀ : ℝ) (P : ZeroConfig → Prop), IsLocalBelow T₀ P → P Z₀ →
        ∃ Z' : ZeroConfig, P Z' ∧ (rightOf Z' 0).Infinite ∧ ¬ LinearAbscissaLawAt Z' C) := by
  set Z₀ := bumpRatioConfig (1 / 8) (1 / 8) 0 (by norm_num) le_rfl (by norm_num)
  obtain ⟨hΘ₀, hΘinf₀⟩ := bumpRatioConfig_abscissas (a := 1 / 8) (b := 1 / 8) 0
    (by norm_num) le_rfl (by norm_num)
  have hA₀ : AbscissaLaw Z₀ :=
    (abscissaLaw_iff_asymptoticAbscissa_eq_zeroAbscissa Z₀).mpr (hΘinf₀.trans hΘ₀.symm)
  have hinf_bump : ∀ (b : ℝ) (n₀ : ℕ) (hab : (1 / 8 : ℝ) ≤ b) (hb : b ≤ 1 / 2),
      (rightOf (bumpRatioConfig (1 / 8) b n₀ (by norm_num) hab hb) 0).Infinite := by
    intro b n₀ hab hb
    obtain ⟨_, hΘinf⟩ := bumpRatioConfig_abscissas n₀ (by norm_num) hab hb
    intro hfin
    have hZAL : ApproachesLine (bumpRatioConfig (1 / 8) b n₀ (by norm_num) hab hb) :=
      fun h hh => hfin.subset fun z ⟨hz, hre⟩ => ⟨hz, by linarith⟩
    have := (approachesLine_iff_asymptoticAbscissa_eq_half _).mp hZAL
    linarith
  refine ⟨Z₀, hA₀, hinf_bump (1 / 8) 0 le_rfl (by norm_num), ?_, ?_⟩
  · intro P hP hPZ₀
    set Z' := bumpRatioConfig (1 / 8) (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)
    have hag : ∃ T : ℝ, ∀ z : ℂ, T < |z.im| →
        (z ∈ Z₀.carrier ↔ z ∈ Z'.carrier) ∧ (z ∈ Z₀.carrier → Z₀.mult z = Z'.mult z) := by
      refine ⟨1, fun z hz => ⟨?_, fun _ => rfl⟩⟩
      have hne0 : ∀ n : ℕ, ((n + 1 : ℝ) : ℝ) = z.im → n ≠ 0 := by
        intro n him hn
        subst hn
        simp only [Nat.cast_zero, zero_add] at him
        rw [← him, abs_one] at hz
        exact lt_irrefl _ hz
      constructor
      · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
        · have hn : n ≠ 0 := hne0 n (by simp [seqUpper])
          exact Or.inl ⟨n, by simp [seqUpper, hn]⟩
        · have hn : n ≠ 0 := hne0 n (by simp [seqLower])
          exact Or.inr ⟨n, by simp [seqLower, hn]⟩
      · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
        · have hn : n ≠ 0 := hne0 n (by simp [seqUpper])
          exact Or.inl ⟨n, by simp [seqUpper, hn]⟩
        · have hn : n ≠ 0 := hne0 n (by simp [seqLower])
          exact Or.inr ⟨n, by simp [seqLower, hn]⟩
    obtain ⟨hΘ', hΘinf'⟩ := bumpRatioConfig_abscissas (a := 1 / 8) (b := 1 / 4) 0
      (by norm_num) (by norm_num) (by norm_num)
    have hnot : ¬ LinearAbscissaLawAt Z' C := by
      unfold LinearAbscissaLawAt
      rw [hΘ', hΘinf', not_le]
      linarith
    exact ⟨Z', (hP Z₀ Z' hag).mp hPZ₀, hinf_bump (1 / 4) 0 (by norm_num) (by norm_num), hnot⟩
  · intro T₀ P hP hPZ₀
    set n₀ : ℕ := ⌈|T₀|⌉₊ + 1
    set Z' := bumpRatioConfig (1 / 8) (1 / 4) n₀ (by norm_num) (by norm_num) (by norm_num)
    have hag : ∀ z : ℂ, |z.im| ≤ T₀ →
        (z ∈ Z₀.carrier ↔ z ∈ Z'.carrier) ∧ (z ∈ Z₀.carrier → Z₀.mult z = Z'.mult z) := by
      intro z hz
      have hnen₀ : ∀ n : ℕ, (n : ℝ) + 1 = z.im → n ≠ n₀ := by
        intro n him hn
        subst hn
        have hpos : 0 < (n₀ : ℝ) + 1 := by positivity
        have habs : |z.im| = (n₀ : ℝ) + 1 := by rw [← him, abs_of_pos hpos]
        have hceil : |T₀| ≤ (⌈|T₀|⌉₊ : ℝ) := Nat.le_ceil _
        have hn₀R : (n₀ : ℝ) = (⌈|T₀|⌉₊ : ℝ) + 1 := by simp [n₀]
        linarith [le_abs_self T₀]
      refine ⟨?_, fun _ => rfl⟩
      constructor
      · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
        · have hn : n ≠ n₀ := hnen₀ n (by simp [seqUpper])
          exact Or.inl ⟨n, by simp [seqUpper, hn]⟩
        · have hn : n ≠ n₀ := hnen₀ n (by simp [seqLower])
          exact Or.inr ⟨n, by simp [seqLower, hn]⟩
      · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
        · have hn : n ≠ n₀ := hnen₀ n (by simp [seqUpper])
          exact Or.inl ⟨n, by simp [seqUpper, hn]⟩
        · have hn : n ≠ n₀ := hnen₀ n (by simp [seqLower])
          exact Or.inr ⟨n, by simp [seqLower, hn]⟩
    obtain ⟨hΘ', hΘinf'⟩ := bumpRatioConfig_abscissas (a := 1 / 8) (b := 1 / 4) n₀
      (by norm_num) (by norm_num) (by norm_num)
    have hnot : ¬ LinearAbscissaLawAt Z' C := by
      unfold LinearAbscissaLawAt
      rw [hΘ', hΘinf', not_le]
      linarith
    exact ⟨Z', (hP Z₀ Z' hag).mp hPZ₀, hinf_bump (1 / 4) n₀ (by norm_num) (by norm_num), hnot⟩

/-! ### De Bruijn–Newman heat family: existential linear AAL is RH -/

section HeatFamily

open _root_.RHTower _root_.RHTower.DeBruijn

/-- Global off-axis spectral depth `sup ({0} ∪ {|Im z| : F(z) = 0})`. -/
def spectralDepth (F : ℂ → ℂ) : ℝ :=
  sSup (insert (0 : ℝ) ((fun z : ℂ => |z.im|) '' {z : ℂ | F z = 0}))

/-- Asymptotic off-axis spectral depth `inf {h ≥ 0 : {z : F(z) = 0 ∧ |Im z| > h}.Finite}`. -/
def asymptoticSpectralDepth (F : ℂ → ℂ) : ℝ :=
  sInf {h : ℝ | 0 ≤ h ∧ {z : ℂ | F z = 0 ∧ h < |z.im|}.Finite}

/-- Every positive heat deformation `riemannHeat t` (`t > 0`) has zero asymptotic spectral depth. -/
theorem asymptoticSpectralDepth_riemannHeat_eq_zero {t : ℝ} (ht : 0 < t) :
    asymptoticSpectralDepth (riemannHeat t) = 0 := by
  refine le_antisymm ?_ (le_csInf ?_ fun _ h => h.1)
  · refine csInf_le ⟨0, fun _ h => h.1⟩ ⟨le_rfl, ?_⟩
    exact (riemannHeat_nonreal_zeros_finite ht).subset fun z ⟨hz, him⟩ =>
      ⟨hz, abs_pos.mp him⟩
  · exact ⟨0, le_rfl, (riemannHeat_nonreal_zeros_finite ht).subset fun z ⟨hz, him⟩ =>
      ⟨hz, abs_pos.mp him⟩⟩

theorem spectralDepth_riemannHeat_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ spectralDepth (riemannHeat t) := by
  have hfin := riemannHeat_nonreal_zeros_finite ht
  obtain ⟨M, hM⟩ := (hfin.image fun z : ℂ => |z.im|).bddAbove
  refine le_csSup ⟨max M 0, ?_⟩ (mem_insert _ _)
  rintro x (rfl | ⟨z, hz, rfl⟩)
  · exact le_max_right M 0
  · by_cases him : z.im = 0
    · rw [him, abs_zero]; exact le_max_right M 0
    · exact (hM ⟨z, ⟨hz, him⟩, rfl⟩).trans (le_max_left M 0)

theorem im_eq_zero_of_spectralDepth_riemannHeat_le_zero {t : ℝ} (ht : 0 < t)
    (hle : spectralDepth (riemannHeat t) ≤ 0) {z : ℂ} (hz : riemannHeat t z = 0) :
    z.im = 0 := by
  have hfin := riemannHeat_nonreal_zeros_finite ht
  obtain ⟨M, hM⟩ := (hfin.image fun w : ℂ => |w.im|).bddAbove
  have hbdd : BddAbove (insert (0 : ℝ) ((fun w : ℂ => |w.im|) '' {w : ℂ | riemannHeat t w = 0})) := by
    refine ⟨max M 0, ?_⟩
    rintro x (rfl | ⟨w, hw, rfl⟩)
    · exact le_max_right M 0
    · by_cases him : w.im = 0
      · rw [him, abs_zero]; exact le_max_right M 0
      · exact (hM ⟨w, ⟨hw, him⟩, rfl⟩).trans (le_max_left M 0)
  have habs : |z.im| ≤ 0 :=
    (le_csSup hbdd (mem_insert_of_mem _ ⟨z, hz, rfl⟩)).trans hle
  exact abs_nonpos_iff.mp habs

/-- **Existential linear AAL along the heat flow is `RiemannHypothesis`.** Even allowing a
different constant `C(t)` at each small positive time `t`, the linear abscissa inequality on
`riemannHeat t` is unconditionally equivalent to `RiemannHypothesis`. -/
theorem riemannHypothesis_iff_eventually_heat_linearAbscissaLaw :
    RiemannHypothesis ↔
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ C : ℝ,
        spectralDepth (riemannHeat t) ≤ C * asymptoticSpectralDepth (riemannHeat t) := by
  rw [riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero]
  constructor
  · intro hev
    filter_upwards [hev, self_mem_nhdsWithin] with t ht0 (ht : 0 < t)
    refine ⟨1, ?_⟩
    rw [asymptoticSpectralDepth_riemannHeat_eq_zero ht, mul_zero]
    refine csSup_le (insert_nonempty _ _) ?_
    rintro x (rfl | ⟨z, hz, rfl⟩)
    · exact le_rfl
    · have him0 : z.im = 0 := by
        by_contra hne
        rw [nonrealZeroCount_eq ht] at ht0
        have hmem : z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset :=
          (Set.Finite.mem_toFinset _).mpr ⟨hz, hne⟩
        have hsum0 := Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp ht0 z hmem
        exact absurd (one_le_zeroMult_riemannHeat ht.le hz) (by omega)
      rw [him0, abs_zero]
  · intro hev
    filter_upwards [hev, self_mem_nhdsWithin] with t ⟨C, hC⟩ (ht : 0 < t)
    rw [asymptoticSpectralDepth_riemannHeat_eq_zero ht, mul_zero] at hC
    rw [nonrealZeroCount_eq ht]
    refine Finset.sum_eq_zero fun z hz => ?_
    have hz' := (Set.Finite.mem_toFinset _).mp hz
    exact absurd (im_eq_zero_of_spectralDepth_riemannHeat_le_zero ht hC hz'.1) hz'.2

end HeatFamily

end ConfigAbscissa

/-! ### Specialization to `ζ`: quantifier collapse and symmetric-shift non-invariance -/

namespace ZetaAbscissa

open ConfigAbscissa _root_.RHTower _root_.RHTower.CrossRouteReceiverBridges

theorem zeroAbscissa_zetaZeroConfig :
    zeroAbscissa zetaZeroConfig = zetaZeroAbscissa := by
  refine le_antisymm ?_ ?_
  · refine (zeroAbscissa_le_iff zetaZeroConfig).mpr ⟨half_le_zetaZeroAbscissa, fun ρ hρ => ?_⟩
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
      (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
    rw [← hq]
    exact re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q)
  · refine zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le (half_le_zeroAbscissa zetaZeroConfig)
      fun q => re_le_zeroAbscissa zetaZeroConfig (xiZeroCopy_mem_zetaZeroConfig_carrier q)

theorem asymptoticAbscissaSet_zetaZeroConfig :
    asymptoticAbscissaSet zetaZeroConfig = zetaAsymptoticAbscissaSet := by
  ext σ
  simp only [asymptoticAbscissaSet, zetaAsymptoticAbscissaSet, mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  rw [← finite_copies_iff]
  simp [add_sub_cancel]

theorem asymptoticAbscissa_zetaZeroConfig :
    asymptoticAbscissa zetaZeroConfig = zetaAsymptoticAbscissa := by
  unfold asymptoticAbscissa zetaAsymptoticAbscissa
  rw [asymptoticAbscissaSet_zetaZeroConfig]

/-- **Linear abscissa law for `ζ` at slope `C`**: `Θ − ½ ≤ C (Θ_∞ − ½)`. -/
def ZetaLinearAbscissaLawAt (C : ℝ) : Prop :=
  zetaZeroAbscissa - 1 / 2 ≤ C * (zetaAsymptoticAbscissa - 1 / 2)

/-- **Eventual-to-global linear law for `ζ` at slope `C`**: finitely many `ξ`-zeros right of
`½ + h` force all `ξ`-zeros left of `½ + C h`, for every `h ≥ 0`. -/
def ZetaLinearEventualToGlobalAt (C : ℝ) : Prop :=
  ∀ h : ℝ, 0 ≤ h → {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite →
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + C * h

/-- **Existential linear abscissa law for `ζ`**. -/
def ZetaLinearAbscissaLaw : Prop :=
  ∃ C : ℝ, ZetaLinearAbscissaLawAt C

theorem zetaLinearAbscissaLawAt_iff_config (C : ℝ) :
    ZetaLinearAbscissaLawAt C ↔ LinearAbscissaLawAt zetaZeroConfig C := by
  simp only [ZetaLinearAbscissaLawAt, LinearAbscissaLawAt, zeroAbscissa_zetaZeroConfig,
    asymptoticAbscissa_zetaZeroConfig]

theorem zetaLinearEventualToGlobalAt_iff_config (C : ℝ) :
    ZetaLinearEventualToGlobalAt C ↔ LinearEventualToGlobalAt zetaZeroConfig C := by
  refine forall₂_congr fun h _ => ?_
  rw [finite_copies_iff]
  refine imp_congr_right fun _ =>
    ⟨fun H ρ hρ => ?_, fun H q => H _ (xiZeroCopy_mem_zetaZeroConfig_carrier q)⟩
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
    (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
  rw [← hq]
  exact H q

theorem zetaLinearAbscissaLaw_iff_config :
    ZetaLinearAbscissaLaw ↔ LinearAbscissaLaw zetaZeroConfig :=
  exists_congr zetaLinearAbscissaLawAt_iff_config

/-- **Equivalence of the two linear AAL formulations for `ζ`** when `C ≥ 0`. -/
theorem zetaLinearAbscissaLawAt_iff_eventualToGlobalAt {C : ℝ} (hC : 0 ≤ C) :
    ZetaLinearAbscissaLawAt C ↔ ZetaLinearEventualToGlobalAt C := by
  rw [zetaLinearAbscissaLawAt_iff_config, zetaLinearEventualToGlobalAt_iff_config]
  exact linearAbscissaLawAt_iff_eventualToGlobalAt zetaZeroConfig hC

/-- For `C < 0`, `ZetaLinearEventualToGlobalAt C` is unconditionally false (Hardy's critical-line
zeros violate `Re q ≤ ½ + C · ½` while `{Re q > 1}` is empty), whereas `ZetaLinearAbscissaLawAt C`
is equivalent to `RiemannHypothesis`. -/
theorem not_zetaLinearEventualToGlobalAt_of_neg {C : ℝ} (hC : C < 0) :
    ¬ ZetaLinearEventualToGlobalAt C ∧ (ZetaLinearAbscissaLawAt C ↔ RiemannHypothesis) := by
  refine ⟨fun hE => ?_, ?_⟩
  · obtain ⟨t, _, hzero⟩ := exists_Xi_zero_gt 1
    have hxi : xi ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
      rw [xi_eq_XiC_comp]
      have he : (((1 / 2 : ℂ) + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
        ring_nf; simp only [Complex.I_sq, mul_neg, mul_one, neg_neg]
      rw [he, XiC_ofReal, hzero, Complex.ofReal_zero]
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hfin : {r : XiZeroCopy | 1 / 2 + 1 / 2 < (r.1 : ℂ).re}.Finite := by
      simpa [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using one_mem_zetaAsymptoticAbscissaSet.2
    have hb := hE (1 / 2) (by norm_num) hfin q
    have hre : (q.1 : ℂ).re = 1 / 2 := by rw [hq]; simp
    rw [hre] at hb
    linarith
  · rw [ ← zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
    unfold ZetaLinearAbscissaLawAt
    constructor
    · intro hL
      have h0 : 0 ≤ zetaAsymptoticAbscissa - 1 / 2 := sub_nonneg.mpr half_le_zetaAsymptoticAbscissa
      have hnonpos : C * (zetaAsymptoticAbscissa - 1 / 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC.le h0
      exact le_antisymm (by linarith) half_le_zetaZeroAbscissa
    · intro heq
      have hZ : zetaAsymptoticAbscissa = 1 / 2 :=
        le_antisymm (zetaAsymptoticAbscissa_le_zetaZeroAbscissa.trans heq.le)
          half_le_zetaAsymptoticAbscissa
      rw [heq, hZ]
      norm_num

/-- **RH is ZAL plus `ZetaLinearAbscissaLawAt C` at any real `C` whatsoever.** Once `ZerosApproachLine`
holds, any slope `C` already forces `RiemannHypothesis`, leaving zero gap to `AsymptoticAbscissaLaw`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_zetaLinearAbscissaLawAt (C : ℝ) :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ZetaLinearAbscissaLawAt C := by
  rw [riemannHypothesis_iff_zetaZeroConfig_onLine, ← zetaZeroConfig_approachesLine_iff,
    zetaLinearAbscissaLawAt_iff_config]
  exact pure_iff_approachesLine_and_linearAbscissaLawAt zetaZeroConfig C

/-- **`AsymptoticAbscissaLaw` is the `C ↓ 1` limit of `ZetaLinearAbscissaLawAt C`.** -/
theorem asymptoticAbscissaLaw_iff_forall_gt_one_zetaLinearAbscissaLawAt :
    AsymptoticAbscissaLaw ↔ ∀ C : ℝ, 1 < C → ZetaLinearAbscissaLawAt C := by
  rw [← zetaZeroConfig_abscissaLaw_iff, abscissaLaw_iff_forall_gt_one_linearAbscissaLawAt]
  exact forall₂_congr fun C _ => (zetaLinearAbscissaLawAt_iff_config C).symm

/-- **Master quantifier collapse for `ζ`.** Existential linear AAL is unconditionally equivalent to
`ZerosApproachLine → RiemannHypothesis`. -/
theorem zetaLinearAbscissaLaw_tfae :
    [ZetaLinearAbscissaLaw,
      ∃ C : ℝ, 1 ≤ C ∧ ZetaLinearAbscissaLawAt C,
      ∃ C : ℝ, ZetaLinearEventualToGlobalAt C,
      zetaAsymptoticAbscissa = 1 / 2 → zetaZeroAbscissa = 1 / 2,
      BacklundConverse.ZerosApproachLine → RiemannHypothesis,
      BacklundConverse.ZerosApproachLine → AsymptoticAbscissaLaw,
      ¬ BacklundConverse.ZerosApproachLine ∨ RiemannHypothesis].TFAE := by
  have hcfg := linearAbscissaLaw_tfae zetaZeroConfig
  have hPure : Pure zetaZeroConfig ↔ RiemannHypothesis :=
    riemannHypothesis_iff_zetaZeroConfig_onLine.symm
  tfae_have 1 ↔ 5 := by
    rw [zetaLinearAbscissaLaw_iff_config, ← zetaZeroConfig_approachesLine_iff, ← hPure]
    exact hcfg.out 0 4
  tfae_have 2 ↔ 5 := by
    simp_rw [zetaLinearAbscissaLawAt_iff_config]
    rw [← zetaZeroConfig_approachesLine_iff, ← hPure]
    exact hcfg.out 1 4
  tfae_have 3 ↔ 5 := by
    simp_rw [zetaLinearEventualToGlobalAt_iff_config]
    rw [← zetaZeroConfig_approachesLine_iff, ← hPure]
    exact hcfg.out 2 4
  tfae_have 4 ↔ 5 := by
    rw [← asymptoticAbscissa_zetaZeroConfig, ← zeroAbscissa_zetaZeroConfig,
      ← zetaZeroConfig_approachesLine_iff, ← hPure]
    exact hcfg.out 3 4
  tfae_have 6 ↔ 5 := by
    rw [← zetaZeroConfig_approachesLine_iff, ← zetaZeroConfig_abscissaLaw_iff, ← hPure]
    exact (hcfg.out 4 5).symm
  tfae_have 7 ↔ 5 := by
    rw [← zetaZeroConfig_approachesLine_iff, ← hPure]
    exact (hcfg.out 4 6).symm
  tfae_finish

/-- Off `ZerosApproachLine`, `ZetaLinearAbscissaLawAt` holds unconditionally with explicit slope
`1 / (2 Θ_∞ − 1)`. -/
theorem zetaLinearAbscissaLawAt_of_not_zerosApproachLine
    (hnot : ¬ BacklundConverse.ZerosApproachLine) :
    ZetaLinearAbscissaLawAt (1 / (2 * zetaAsymptoticAbscissa - 1)) := by
  have hne : zetaAsymptoticAbscissa ≠ 1 / 2 :=
    mt zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half.mpr hnot
  have hpos : 0 < zetaAsymptoticAbscissa - 1 / 2 :=
    sub_pos.mpr (lt_of_le_of_ne' half_le_zetaAsymptoticAbscissa hne)
  unfold ZetaLinearAbscissaLawAt
  have hrhs : 1 / (2 * zetaAsymptoticAbscissa - 1) * (zetaAsymptoticAbscissa - 1 / 2) = 1 / 2 := by
    have h2 : 2 * zetaAsymptoticAbscissa - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hrhs]
  linarith [zetaZeroAbscissa_le_one]

/-- Existential linear AAL for `ζ` implies the finite-stratum implication
`{q : XiZeroCopy | Re q ≠ ½}.Finite → RiemannHypothesis`. -/
theorem zetaLinearAbscissaLaw_imp_finiteOffLine_rh (hL : ZetaLinearAbscissaLaw)
    (hfin : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite) :
    RiemannHypothesis := by
  have hZAL : BacklundConverse.ZerosApproachLine := by
    intro δ hδ
    refine hfin.subset fun q hq => ?_
    have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [xiSpectralPoint, Complex.mul_im]
    have hlt : δ < (xiSpectralPoint q).im := hq
    rw [him] at hlt
    intro heq
    linarith
  exact (zetaLinearAbscissaLaw_tfae.out 0 4).mp hL hZAL

/-! ### Failure of symmetric-shift invariance -/

/-- **Unconditional linear eventual-to-global law for every positive symmetric shift.** For every
`a > 0`, `ξ(s + a)ξ(s − a)` satisfies the linear eventual-to-global law unconditionally at
`C = 1 + 1 / (2a)`. Thus existential linear AAL is not invariant under symmetric shifts. -/
theorem symmetricShift_xi_linearEventualToGlobal_unconditional {a : ℝ} (ha : 0 < a) :
    ∀ h : ℝ, 0 ≤ h →
      (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
        symmetricShiftProduct xi a z = 0 → T ≤ |z.im| → z.re ≤ 1 / 2 + h) →
      ∀ z : ℂ, symmetricShiftProduct xi a z = 0 →
        z.re ≤ 1 / 2 + (1 + 1 / (2 * a)) * h := by
  intro h _ hev
  have hev_xi := (symmetricShiftProduct_eventualBound_iff ha.le (1 / 2 + h)).mp hev
  have hah : a ≤ h := by
    have := half_le_of_xi_eventualBound hev_xi
    linarith
  refine (symmetricShiftProduct_globalBound_iff ha.le _).mpr fun w hw => ?_
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hw
  have hlt1 : w.re < 1 := by rw [← hq]; exact (xi_divisor_support_re_mem_open_unit q.1).2
  have hCa : 1 ≤ 1 / 2 + (1 + 1 / (2 * a)) * a - a := by
    field_simp; ring_nf; exact le_rfl
  have hmono : (1 + 1 / (2 * a)) * a ≤ (1 + 1 / (2 * a)) * h :=
    mul_le_mul_of_nonneg_left hah (by positivity)
  linarith

/-- **Uniformity across shifts `a → 0⁺` recovers `ZetaLinearAbscissaLawAt C`.** A single slope
`C ≥ 0` works uniformly for `ξ(s + a)ξ(s − a)` across all `a > 0` iff `ZetaLinearAbscissaLawAt C`
holds for `ζ`. -/
theorem uniform_symmetricShift_linearEventualToGlobal_iff {C : ℝ} (hC : 0 ≤ C) :
    (∀ a : ℝ, 0 < a → ∀ h : ℝ, 0 ≤ h →
      (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
        symmetricShiftProduct xi a z = 0 → T ≤ |z.im| → z.re ≤ 1 / 2 + h) →
      ∀ z : ℂ, symmetricShiftProduct xi a z = 0 → z.re ≤ 1 / 2 + C * h) ↔
    ZetaLinearAbscissaLawAt C := by
  rw [zetaLinearAbscissaLawAt_iff_eventualToGlobalAt hC]
  constructor
  · intro hunif h hh hfin q
    have hmem : 1 / 2 + h ∈ zetaAsymptoticAbscissaSet := ⟨by linarith, hfin⟩
    obtain ⟨_, T, hT, htail⟩ := mem_zetaAsymptoticAbscissaSet_iff_eventually_height.mp hmem
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set a : ℝ := ε / (C + 1)
    have ha : 0 < a := div_pos hε (by linarith)
    have hev_shift : ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
        symmetricShiftProduct xi a z = 0 → T ≤ |z.im| → z.re ≤ 1 / 2 + (h + a) := by
      refine (symmetricShiftProduct_eventualBound_iff ha.le (1 / 2 + (h + a))).mpr
        ⟨T, hT, fun z hz hzT => ?_⟩
      obtain ⟨r, hr⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
      have hb := htail r (by simpa only [hr] using hzT)
      rw [← hr]
      linarith
    have hglob := (symmetricShiftProduct_globalBound_iff ha.le (1 / 2 + C * (h + a))).mp
      (hunif a ha (h + a) (by positivity) hev_shift) (q.1 : ℂ) (xi_xiZeroCopy_eq_zero q)
    have hCa : C * a - a < ε := by
      have : (C - 1) * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_right (by linarith) ha
      rw [mul_div_cancel₀ _ (by linarith)] at this
      dsimp [a]
      linarith
    linarith
  · intro hE a ha h hh hev
    have hev_xi := (symmetricShiftProduct_eventualBound_iff ha.le (1 / 2 + h)).mp hev
    have hah : a ≤ h := by
      have := half_le_of_xi_eventualBound hev_xi
      linarith
    obtain ⟨T, hT, htail⟩ := hev_xi
    have hmem : 1 / 2 + (h - a) ∈ zetaAsymptoticAbscissaSet :=
      mem_zetaAsymptoticAbscissaSet_iff_eventually_height.mpr ⟨by linarith, T, hT, fun q hq => by
        have hb := htail (q.1 : ℂ) (xi_xiZeroCopy_eq_zero q) hq
        linarith⟩
    have hfin : {q : XiZeroCopy | 1 / 2 + (h - a) < (q.1 : ℂ).re}.Finite := hmem.2
    refine (symmetricShiftProduct_globalBound_iff ha.le (1 / 2 + C * h)).mpr fun w hw => ?_
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hw
    have hb := hE (h - a) (by linarith) hfin q
    rw [← hq] at hb
    rcases le_or_gt C 1 with hC1 | hC1
    · have hlt1 : w.re < 1 := by rw [← hq]; exact (xi_divisor_support_re_mem_open_unit q.1).2
      rcases eq_or_lt_of_le hC with rfl | hCpos
      · -- Wait: check `C = 0`!
        sorry
      · sorry
    · nlinarith
