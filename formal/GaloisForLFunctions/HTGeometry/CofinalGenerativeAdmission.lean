import Mathlib

/-!
# Cofinal generative admission

This module formalizes the route-independent core of the paper theorem
`cofinal-generative-admission-gauge-and-three-cone-data-processing-law.md`.

Finite-aperture legality is separated from executable straight-line admission.  Positive linear
comparisons preserve every admitted scale, while an explicit countable carrier is legal on every
finite aperture and has no positive global admission radius.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

section Admission

variable {ι κ : Type*}

/-- The straight perturbation `w + εh` remains in the coordinatewise positive cone. -/
def AdmittedAt (w h : ι → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ i, 0 ≤ w i + ε * h i

/-- The tangent is dominated by `c` copies of the positive base. -/
def DominatedAt (w h : ι → ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ i, 0 ≤ h i + c * w i

/-- Some common positive scale admits the full straight perturbation. -/
def StraightAdmitted (w h : ι → ℝ) : Prop :=
  ∃ ε, AdmittedAt w h ε

/-- Every finite aperture admits a common positive perturbation scale. -/
def FinitelyAdmitted [DecidableEq ι] (w h : ι → ℝ) : Prop :=
  ∀ F : Finset ι, ∃ ε, 0 < ε ∧ ∀ i ∈ F, 0 ≤ w i + ε * h i

/-- The tangent points inward at every currently absent coordinate. -/
def ContingentlyLegal (w h : ι → ℝ) : Prop :=
  ∀ i, w i = 0 → 0 ≤ h i

/-- A linear comparison preserves the coordinatewise positive cone. -/
def IsPositiveLinearMap (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : Prop :=
  ∀ x, (∀ i, 0 ≤ x i) → ∀ j, 0 ≤ A x j

/-- Exact reciprocal feasibility law: admission at `ε` is domination at `ε⁻¹`. -/
theorem admittedAt_iff_dominatedAt_inv {w h : ι → ℝ} {ε : ℝ} (hε : 0 < ε) :
    AdmittedAt w h ε ↔ DominatedAt w h ε⁻¹ := by
  constructor
  · rintro ⟨_, hadm⟩
    refine ⟨le_of_lt (inv_pos.mpr hε), ?_⟩
    intro i
    calc
      0 ≤ ε⁻¹ * (w i + ε * h i) := mul_nonneg (inv_nonneg.mpr hε.le) (hadm i)
      _ = h i + ε⁻¹ * w i := by field_simp [hε.ne']; ring
  · rintro ⟨_, hdom⟩
    refine ⟨hε, ?_⟩
    intro i
    calc
      0 ≤ ε * (h i + ε⁻¹ * w i) := mul_nonneg hε.le (hdom i)
      _ = w i + ε * h i := by field_simp [hε.ne']; ring

/-- Shrinking an admitted scale preserves admission when the base is positive. -/
theorem admitted_coordinate_mono {w h : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {i : ι} {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hadm : 0 ≤ w i + ε * h i) :
    0 ≤ w i + δ * h i := by
  by_cases hh : 0 ≤ h i
  · exact add_nonneg (hw i) (mul_nonneg hδ.le hh)
  · have hmul : ε * h i ≤ δ * h i :=
      mul_le_mul_of_nonpos_right hδε (le_of_not_ge hh)
    linarith

/-- Contingent legality supplies a positive admitted scale at one coordinate. -/
theorem coordinate_admitted {w h : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hcont : ContingentlyLegal w h) (i : ι) :
    ∃ ε, 0 < ε ∧ 0 ≤ w i + ε * h i := by
  by_cases hh : 0 ≤ h i
  · exact ⟨1, by norm_num, add_nonneg (hw i) (by simpa using hh)⟩
  · have hwn : w i ≠ 0 := by
      intro hz
      exact hh (hcont i hz)
    have hwp : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hwn)
    refine ⟨w i / (-h i), div_pos hwp (neg_pos.mpr (lt_of_not_ge hh)), ?_⟩
    field_simp [ne_of_lt (lt_of_not_ge hh)]
    positivity

/-- On every finite aperture, contingent legality is sufficient for a common admitted scale. -/
theorem finitelyAdmitted_of_contingentlyLegal [DecidableEq ι]
    {w h : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hcont : ContingentlyLegal w h) :
    FinitelyAdmitted w h := by
  intro F
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a F ha ih =>
      obtain ⟨ε, hε, hF⟩ := ih
      obtain ⟨δ, hδ, haδ⟩ := coordinate_admitted hw hcont a
      refine ⟨min ε δ, lt_min hε hδ, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact admitted_coordinate_mono hw (lt_min hε hδ) (min_le_right _ _) haδ
      · exact admitted_coordinate_mono hw (lt_min hε hδ) (min_le_left _ _) (hF i hi)

/-- Finite-aperture admission forces every absent-coordinate velocity to point inward. -/
theorem contingentlyLegal_of_finitelyAdmitted [DecidableEq ι]
    {w h : ι → ℝ} (hloc : FinitelyAdmitted w h) :
    ContingentlyLegal w h := by
  intro i hwi
  obtain ⟨ε, hε, hi⟩ := hloc {i}
  have hpoint := hi i (by simp)
  rw [hwi, zero_add] at hpoint
  nlinarith

/-- Exact finite-observer classification: finite admission sees precisely contingent legality. -/
theorem finitelyAdmitted_iff_contingentlyLegal [DecidableEq ι]
    {w h : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    FinitelyAdmitted w h ↔ ContingentlyLegal w h :=
  ⟨contingentlyLegal_of_finitelyAdmitted,
    finitelyAdmitted_of_contingentlyLegal hw⟩

/-- Full straight admission implies admission on every finite aperture. -/
theorem finitelyAdmitted_of_straightAdmitted [DecidableEq ι]
    {w h : ι → ℝ} (hadm : StraightAdmitted w h) :
    FinitelyAdmitted w h := by
  obtain ⟨ε, hε, hall⟩ := hadm
  intro F
  exact ⟨ε, hε, fun i _ => hall i⟩

/-- Positive comparisons preserve each admitted scale: receiver admission obstruction cannot grow. -/
theorem admittedAt_map {w h : ι → ℝ} {ε : ℝ}
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (hA : IsPositiveLinearMap A)
    (hadm : AdmittedAt w h ε) :
    AdmittedAt (A w) (A h) ε := by
  refine ⟨hadm.1, ?_⟩
  have hpos : ∀ i, 0 ≤ (w + ε • h) i := by
    intro i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadm.2 i
  have hmap := hA (w + ε • h) hpos
  intro j
  simpa using hmap j

/-- Positive comparisons preserve every dominating coefficient: receiver gauge cannot grow. -/
theorem dominatedAt_map {w h : ι → ℝ} {c : ℝ}
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (hA : IsPositiveLinearMap A)
    (hdom : DominatedAt w h c) :
    DominatedAt (A w) (A h) c := by
  refine ⟨hdom.1, ?_⟩
  have hpos : ∀ i, 0 ≤ (h + c • w) i := by
    intro i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hdom.2 i
  have hmap := hA (h + c • w) hpos
  intro j
  simpa using hmap j

/-- Positivity is stable under serial comparison. -/
theorem positiveLinearMap_comp {ν : Type*}
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (B : (κ → ℝ) →ₗ[ℝ] (ν → ℝ))
    (hA : IsPositiveLinearMap A) (hB : IsPositiveLinearMap B) :
    IsPositiveLinearMap (B.comp A) := by
  intro x hx j
  exact hB (A x) (hA x hx) j

/-- A family of observers is jointly conservative when positivity of every image reflects
positivity of the source. -/
def JointlyReflectsPositivity {J : Type*}
    (A : J → (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : Prop :=
  ∀ x, (∀ j k, 0 ≤ A j x k) → ∀ i, 0 ≤ x i

/-- Joint positive conservativity turns lax admission transport into an exact fusion law. -/
theorem admittedAt_iff_forall_map {J : Type*}
    {w h : ι → ℝ} {ε : ℝ} (hε : 0 < ε)
    (A : J → (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (hpos : ∀ j, IsPositiveLinearMap (A j))
    (hreflect : JointlyReflectsPositivity A) :
    AdmittedAt w h ε ↔ ∀ j, AdmittedAt (A j w) (A j h) ε := by
  constructor
  · intro hadm j
    exact admittedAt_map (A j) (hpos j) hadm
  · intro hall
    refine ⟨hε, ?_⟩
    have himage : ∀ j k, 0 ≤ A j (w + ε • h) k := by
      intro j k
      have hj := (hall j).2 k
      simpa using hj
    have hsource := hreflect (w + ε • h) himage
    intro i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hsource i

/-- Joint positive conservativity also exactly reconstructs every dominating coefficient. -/
theorem dominatedAt_iff_forall_map {J : Type*}
    {w h : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (A : J → (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (hpos : ∀ j, IsPositiveLinearMap (A j))
    (hreflect : JointlyReflectsPositivity A) :
    DominatedAt w h c ↔ ∀ j, DominatedAt (A j w) (A j h) c := by
  constructor
  · intro hdom j
    exact dominatedAt_map (A j) (hpos j) hdom
  · intro hall
    refine ⟨hc, ?_⟩
    have himage : ∀ j k, 0 ≤ A j (h + c • w) k := by
      intro j k
      have hj := (hall j).2 k
      simpa using hj
    have hsource := hreflect (h + c • w) himage
    intro i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hsource i

/-- If a jointly conservative family rejects a source scale, at least one observer rejects that
same scale. The witness observer may depend on the scale. -/
theorem exists_map_not_admittedAt {J : Type*}
    {w h : ι → ℝ} {ε : ℝ} (hε : 0 < ε)
    (A : J → (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (hpos : ∀ j, IsPositiveLinearMap (A j))
    (hreflect : JointlyReflectsPositivity A)
    (hfail : ¬ AdmittedAt w h ε) :
    ∃ j, ¬ AdmittedAt (A j w) (A j h) ε := by
  by_contra hall
  push Not at hall
  exact hfail ((admittedAt_iff_forall_map hε A hpos hreflect).2 hall)

end Admission

section CofinalCollapse

/-- Constant occupied carrier for the exact cofinal countermodel. -/
def cofinalAdmissionBase (_ : ℕ) : ℝ := 1

/-- Negative density grows linearly through the tail. -/
def cofinalAdmissionTangent (n : ℕ) : ℝ := -(n : ℝ)

/-- Every finite aperture of the countermodel admits a common positive scale. -/
theorem cofinalAdmission_finitelyAdmitted :
    FinitelyAdmitted cofinalAdmissionBase cofinalAdmissionTangent := by
  apply finitelyAdmitted_of_contingentlyLegal
  · intro n
    simp [cofinalAdmissionBase]
  · intro n hn
    simp [cofinalAdmissionBase] at hn

/-- No positive scale admits the full countable perturbation. -/
theorem cofinalAdmission_not_straightAdmitted :
    ¬ StraightAdmitted cofinalAdmissionBase cofinalAdmissionTangent := by
  rintro ⟨ε, hε, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn' : (1 : ℝ) / ε < (n : ℝ) := by simpa [one_div] using hn
  have hlarge' : (1 : ℝ) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn'
  have hlarge : (1 : ℝ) < ε * (n : ℝ) := by nlinarith
  have hpoint := hall n
  simp only [cofinalAdmissionBase, cofinalAdmissionTangent] at hpoint
  linarith

/-- Every finite diagonal coefficient is strictly positive at some common aperture scale. -/
theorem cofinalAdmission_finite_strict (F : Finset ℕ) :
    ∃ ε, 0 < ε ∧
      ∀ n ∈ F, 0 < cofinalAdmissionBase n + ε * cofinalAdmissionTangent n := by
  obtain ⟨ε, hε, hF⟩ := cofinalAdmission_finitelyAdmitted F
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro n hn
  have hpoint := hF n hn
  simp only [cofinalAdmissionBase, cofinalAdmissionTangent] at hpoint ⊢
  nlinarith

/-- Exact cofinal spectral prediction: strict finite positivity coexists with zero global radius. -/
theorem cofinalAdmission_collapse :
    (∀ F : Finset ℕ, ∃ ε, 0 < ε ∧
      ∀ n ∈ F, 0 < cofinalAdmissionBase n + ε * cofinalAdmissionTangent n) ∧
    ¬ StraightAdmitted cofinalAdmissionBase cofinalAdmissionTangent :=
  ⟨cofinalAdmission_finite_strict, cofinalAdmission_not_straightAdmitted⟩

end CofinalCollapse

section ProbabilityCofinalCollapse

/-- Half-density ratio used by the mass-conserving probability countermodel. -/
noncomputable def probabilityAdmissionRatio : ℝ := 1 / 2

/-- A strictly positive geometric probability carrier. -/
noncomputable def probabilityAdmissionBase (n : ℕ) : ℝ :=
  probabilityAdmissionRatio ^ (n + 1)

/-- Unit birth at zero balanced by linearly increasing negative tail density. -/
noncomputable def probabilityAdmissionTangent (n : ℕ) : ℝ :=
  (if n = 0 then 1 else 0) -
    (n : ℝ) * probabilityAdmissionRatio ^ (n + 1)

theorem probabilityAdmissionRatio_norm_lt_one : ‖probabilityAdmissionRatio‖ < 1 := by
  norm_num [probabilityAdmissionRatio, Real.norm_eq_abs]

/-- The geometric base has total mass one. -/
theorem probabilityAdmissionBase_hasSum : HasSum probabilityAdmissionBase 1 := by
  have hg :=
    (hasSum_geometric_of_norm_lt_one probabilityAdmissionRatio_norm_lt_one).mul_left
      probabilityAdmissionRatio
  have hsum :
      probabilityAdmissionRatio * (1 - probabilityAdmissionRatio)⁻¹ = 1 := by
    norm_num [probabilityAdmissionRatio]
  rw [← hsum]
  exact hg.congr (fun n => by
    simp [probabilityAdmissionBase, pow_succ, mul_comm])

/-- The negative tail has total mass one. -/
theorem probabilityAdmissionTail_hasSum :
    HasSum (fun n : ℕ =>
      (n : ℝ) * probabilityAdmissionRatio ^ (n + 1)) 1 := by
  have hg :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      probabilityAdmissionRatio_norm_lt_one).mul_left probabilityAdmissionRatio
  have hsum :
      probabilityAdmissionRatio *
        (probabilityAdmissionRatio / (1 - probabilityAdmissionRatio) ^ 2) = 1 := by
    norm_num [probabilityAdmissionRatio]
  rw [← hsum]
  exact hg.congr (fun n => by
    simp [pow_succ, mul_assoc, mul_comm])

/-- The tangent is exactly mass conserving. -/
theorem probabilityAdmissionTangent_hasSum : HasSum probabilityAdmissionTangent 0 := by
  have hs := (hasSum_ite_eq 0 (1 : ℝ)).sub probabilityAdmissionTail_hasSum
  have hzero : (0 : ℝ) = 1 - 1 := by norm_num
  rw [hzero]
  exact hs.congr (fun n => by rfl)

theorem probabilityAdmissionBase_summable : Summable probabilityAdmissionBase :=
  probabilityAdmissionBase_hasSum.summable

theorem probabilityAdmissionTangent_summable : Summable probabilityAdmissionTangent :=
  probabilityAdmissionTangent_hasSum.summable

theorem probabilityAdmissionBase_pos (n : ℕ) : 0 < probabilityAdmissionBase n := by
  exact pow_pos (by norm_num [probabilityAdmissionRatio]) _

/-- The probability tangent is legal on every finite aperture. -/
theorem probabilityAdmission_finitelyAdmitted :
    FinitelyAdmitted probabilityAdmissionBase probabilityAdmissionTangent := by
  apply finitelyAdmitted_of_contingentlyLegal
  · intro n
    exact (probabilityAdmissionBase_pos n).le
  · intro n hn
    exact False.elim ((probabilityAdmissionBase_pos n).ne' hn)

/-- Despite conservation and finite legality, the probability tangent has no positive global
straight-line admission radius. -/
theorem probabilityAdmission_not_straightAdmitted :
    ¬ StraightAdmitted probabilityAdmissionBase probabilityAdmissionTangent := by
  rintro ⟨ε, hε, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn' : (1 : ℝ) / ε < (n : ℝ) := by simpa [one_div] using hn
  have hlarge' : (1 : ℝ) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn'
  have hlarge : (1 : ℝ) < ε * (n : ℝ) := by nlinarith
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    norm_num at hn'
    exact (not_lt_of_ge hε.le) hn'
  have hpoint := hall n
  have hrewrite :
      probabilityAdmissionBase n + ε * probabilityAdmissionTangent n =
        probabilityAdmissionBase n * (1 - ε * (n : ℝ)) := by
    simp [probabilityAdmissionTangent, probabilityAdmissionBase, hn0]
    ring
  rw [hrewrite] at hpoint
  have hnegative :
      probabilityAdmissionBase n * (1 - ε * (n : ℝ)) < 0 :=
    mul_neg_of_pos_of_neg (probabilityAdmissionBase_pos n) (by linarith)
  exact (not_lt_of_ge hpoint) hnegative

/-- Formal capstone: a mass-one, mass-zero-tangent probability system passes every finite positive
aperture while its global straight perturbation radius is zero. -/
theorem probabilityAdmission_conservative_cofinal_collapse :
    HasSum probabilityAdmissionBase 1 ∧
    HasSum probabilityAdmissionTangent 0 ∧
    FinitelyAdmitted probabilityAdmissionBase probabilityAdmissionTangent ∧
    ¬ StraightAdmitted probabilityAdmissionBase probabilityAdmissionTangent :=
  ⟨probabilityAdmissionBase_hasSum, probabilityAdmissionTangent_hasSum,
    probabilityAdmission_finitelyAdmitted, probabilityAdmission_not_straightAdmitted⟩

end ProbabilityCofinalCollapse

section CoordinateObserverFusion

/-- The `n`-th scalar observer of a countable source. -/
def coordinateAdmissionObserver (n : ℕ) :
    (ℕ → ℝ) →ₗ[ℝ] (Unit → ℝ) where
  toFun x _ := x n
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

theorem coordinateAdmissionObserver_positive (n : ℕ) :
    IsPositiveLinearMap (coordinateAdmissionObserver n) := by
  intro x hx j
  exact hx n

/-- All scalar coordinates jointly reflect positivity exactly. -/
theorem coordinateAdmissionObserver_jointlyReflects :
    JointlyReflectsPositivity coordinateAdmissionObserver := by
  intro x hall i
  exact hall i ()

/-- Every fixed coordinate observer admits the probability tangent at some positive scale. -/
theorem probabilityAdmission_every_coordinate_observer_admitted (n : ℕ) :
    StraightAdmitted
      (coordinateAdmissionObserver n probabilityAdmissionBase)
      (coordinateAdmissionObserver n probabilityAdmissionTangent) := by
  obtain ⟨ε, hε, hn⟩ := probabilityAdmission_finitelyAdmitted {n}
  refine ⟨ε, hε, ?_⟩
  intro u
  simpa [coordinateAdmissionObserver] using hn n (by simp)

/-- Joint-conservativity does not turn pointwise observer radii into one source radius without a
uniform lower bound: every fixed observer admits, while the source does not. -/
theorem probabilityAdmission_migrating_obstruction :
    (∀ n, StraightAdmitted
      (coordinateAdmissionObserver n probabilityAdmissionBase)
      (coordinateAdmissionObserver n probabilityAdmissionTangent)) ∧
    ¬ StraightAdmitted probabilityAdmissionBase probabilityAdmissionTangent :=
  ⟨probabilityAdmission_every_coordinate_observer_admitted,
    probabilityAdmission_not_straightAdmitted⟩

end CoordinateObserverFusion

end GaloisForLFunctions.HTGeometry
