import GaloisForLFunctions.HTGeometry.DoubleSineRationalBaseCollisionMatroid

/-!
# The double-sine parent on an arbitrary ray

The imaginary ray is one line through the origin; the multiple-sine setting puts all periods on a
common ray in the upper half plane.  Both hypotheses of the construction are ray-invariant: the
Barnes cone needs `0 < Im ω`, which holds along any ray with `0 < Im μ`, and the two-period model
needs the ratio of the two radii to be irrational, which is what the common ray direction cancels
out of the frequency computation.

So the whole double-sine parent — source, orbit independence, and the collision matroid of the
shift classes over `ℂ(z)` — holds for periods `μ a`, `μ b` with `Im μ > 0`, `a, b > 0` and `a / b`
irrational.  This is the configuration a maximal face of the `N`-period face complex presents.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance dryDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance dryComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance dryMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance dryMeroCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective

local instance dryComplexDifferential : Differential ℂ where
  deriv := 0

local instance dryComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ⟨fun c => by
    rw [deriv_algebraMap_complex_mero]
    change (0 : meroField (Set.univ : Set ℂ)) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

local instance dryCoordinateDifferential : Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _ meromorphicRationalCoordinateField_derivationClosed

local instance dryCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-! ### Ray geometry -/

theorem im_mul_ofReal_pos {μ : ℂ} (hμ : 0 < μ.im) {a : ℝ} (ha : 0 < a) :
    0 < (μ * (a : ℂ)).im := by
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  exact mul_pos hμ ha

/-- **The double-sine source along a ray.**  For periods `μ a` and `μ b` with `Im μ > 0` and
`a, b > 0` there is a meromorphic source whose structural translation defects are exactly the
cotangents of the other period, up to a constant in the second direction. -/
theorem exists_doubleSine_source_ray {μ : ℂ} (hμ : 0 < μ.im) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (M : meroField (Set.univ : Set ℂ)) (c : ℂ),
      addTranslationMeroEquiv (μ * (a : ℂ)) M - M
          = -periodCotMero (μ * (b : ℂ)) ∧
      addTranslationMeroEquiv (μ * (b : ℂ)) M - M
          = -periodCotMero (μ * (a : ℂ)) + ratMero (RatFunc.C c) := by
  classical
  set ω : Fin 2 → ℂ := ![μ * (a : ℂ), μ * (b : ℂ)] with hω_def
  have hω0 : ω 0 = μ * (a : ℂ) := by simp [hω_def]
  have hω1 : ω 1 = μ * (b : ℂ) := by simp [hω_def]
  have hω : ∀ i : Fin 2, 0 < (ω i).im := by
    intro i
    have : i = 0 ∨ i = 1 := by omega
    rcases this with h | h
    · rw [h, hω0]
      exact im_mul_ofReal_pos hμ ha
    · rw [h, hω1]
      exact im_mul_ofReal_pos hμ hb
  have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
  have hS : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  obtain ⟨r, c, h0, h1⟩ := exists_exact_doubleSine_source ω hω (Finset.univ : Finset (Fin 2))
    0 1 (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) hcard hS
  refine ⟨frameSourceMero ω hω (Finset.univ : Finset (Fin 2)) hS + ratMero r, c, ?_, ?_⟩
  · rw [← hω0, ← hω1]
    exact h0
  · rw [← hω0, ← hω1]
    exact h1

/-- **The two cylinder frequencies along a ray are `ℚ`-independent.**  The ray direction cancels
from the ratio, leaving the irrational ratio of the two radii. -/
theorem linearIndependent_cylinderFrequencies_ray {μ : ℂ} (hμ : μ ≠ 0) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : Irrational (a / b)) :
    LinearIndependent ℚ
      ![2 * (Real.pi : ℂ) * Complex.I / (μ * (a : ℂ)),
        2 * (Real.pi : ℂ) * Complex.I / (μ * (b : ℂ))] := by
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hpi : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have hcne : 2 * (Real.pi : ℂ) * Complex.I / μ ≠ 0 := by
    refine div_ne_zero (mul_ne_zero ?_ Complex.I_ne_zero) hμ
    simp [Real.pi_ne_zero]
  have hratio : Irrational ((1 / a) / (1 / b)) := by
    have heq : (1 / a) / (1 / b) = b / a := by
      field_simp
    rw [heq]
    exact irrational_inv_div ha hb h
  have hbase : LinearIndependent ℚ ![((1 / a : ℝ) : ℂ), ((1 / b : ℝ) : ℂ)] :=
    linearIndependent_rat_ofReal_pair_of_irrational hratio
  have hscaled := linearIndependent_rat_const_mul hbase hcne
  have hfun : (fun i => 2 * (Real.pi : ℂ) * Complex.I / μ *
      (![((1 / a : ℝ) : ℂ), ((1 / b : ℝ) : ℂ)] i))
      = ![2 * (Real.pi : ℂ) * Complex.I / (μ * (a : ℂ)),
        2 * (Real.pi : ℂ) * Complex.I / (μ * (b : ℂ))] := by
    funext i
    have hi2 : i = 0 ∨ i = 1 := by
      rcases i with ⟨iv, hiv⟩
      interval_cases iv
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hi2 with hi | hi
    · rw [hi]
      show 2 * (Real.pi : ℂ) * Complex.I / μ * ((1 / a : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I / (μ * (a : ℂ))
      push_cast
      field_simp
    · rw [hi]
      show 2 * (Real.pi : ℂ) * Complex.I / μ * ((1 / b : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I / (μ * (b : ℂ))
      push_cast
      field_simp
  rwa [hfun] at hscaled

/-! ### The unconditional ray capstone -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The double-sine parent on a ray.**  For periods `μ a`, `μ b` with `Im μ > 0`, `a, b > 0` and
`a / b` irrational there is a meromorphic source with the exact cotangent defect, hypertranscendental
over `ℂ(z)`, whose translate family represents over `ℂ(z)` exactly the collision matroid of the
shift classes modulo the period lattice, with rank the number of distinct classes met. -/
theorem doubleSineRay_rationalBase_matroid {μ : ℂ} (hμ : 0 < μ.im) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hirr : Irrational (a / b)) {κ : Type*} (sh : κ → ℂ) :
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (μ * (a : ℂ)) M - M = -periodCotMero (μ * (b : ℂ)) ∧
        HypertranscendentalOver meromorphicRationalCoordinateField M ∧
        differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
            (fun j : κ => addTranslationMeroEquiv (sh j) M)
          = affineCollisionMatroid (periodClass ![μ * (a : ℂ), μ * (b : ℂ)] ∘ sh) ∧
        ∀ I : Set κ,
          (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
              (fun j : κ => addTranslationMeroEquiv (sh j) M)).eRk I
            = ((periodClass ![μ * (a : ℂ), μ * (b : ℂ)] ∘ sh) '' I).encard := by
  classical
  have hμne : μ ≠ 0 := by
    intro h
    rw [h] at hμ
    simp at hμ
  set ω : Fin 2 → ℂ := ![μ * (a : ℂ), μ * (b : ℂ)] with hωdef
  have hω0 : ω 0 = μ * (a : ℂ) := by simp [hωdef]
  have hω1 : ω 1 = μ * (b : ℂ) := by simp [hωdef]
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hω0ne : ω 0 ≠ 0 := by
    rw [hω0]
    exact mul_ne_zero hμne haC
  have hω1ne : ω 1 ≠ 0 := by
    rw [hω1]
    exact mul_ne_zero hμne hbC
  set l : Fin 2 → ℂ :=
    ![2 * (Real.pi : ℂ) * Complex.I / (μ * (a : ℂ)),
      2 * (Real.pi : ℂ) * Complex.I / (μ * (b : ℂ))] with hldef
  have hl : LinearIndependent ℚ l :=
    linearIndependent_cylinderFrequencies_ray hμne ha hb hirr
  have hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0 := by
    rw [hldef, hω0]
    simp
  have hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1 := by
    rw [hldef, hω1]
    simp
  have hper0 : Complex.exp (l 0 * ω 0) = 1 := by
    rw [hl0, div_mul_cancel₀ _ hω0ne]
    simp
  have hper1 : Complex.exp (l 1 * ω 1) = 1 := by
    rw [hl1, div_mul_cancel₀ _ hω1ne]
    simp
  have hprod : l 1 * ω 0 = 2 * (Real.pi : ℂ) * Complex.I * ((a / b : ℝ) : ℂ) := by
    rw [hl1, hω1, hω0]
    push_cast
    field_simp
  have htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1 := by
    intro n hn
    rw [hprod]
    exact exp_two_pi_I_zpow_ne_one hirr hn
  have hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z := by
    intro z h1 h2
    rw [hω0] at h1
    rw [hω1] at h2
    exact exists_constant_of_two_rayPeriods_fixed hμne hirr h1 h2
  obtain ⟨M, cst, hM0, hM1⟩ := exists_doubleSine_source_ray hμ ha hb
  have hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1) := by
    rw [hω0, hω1]; exact hM0
  have hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst) := by
    rw [hω0, hω1]; exact hM1
  refine ⟨M, hM0, ?_, ?_, ?_⟩
  · have hunit : ∀ i j : Unit, i ≠ j → ∀ m n : ℤ,
        (fun _ : Unit => (0 : ℂ)) i - (fun _ : Unit => (0 : ℂ)) j
          ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
      intro i j hij
      exact absurd (Subsingleton.elim i j) hij
    have hone := doubleSineOrbit_differentialIndependent_rationalBase hl ω hω0ne hω1ne hl0 hl1
      hper0 hper1 htor hfix M cst hd0 hd1 (fun _ : Unit => (0 : ℂ)) hunit
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
    have hrw : (fun j : Unit => addTranslationMeroEquiv ((fun _ : Unit => (0 : ℂ)) j) M)
        = fun _ : Unit => M := by
      funext j
      exact addTranslationMeroEquiv_zero_apply M
    rw [hrw] at hone
    exact hone
  · exact doubleSineOrbit_differentialFamilyMatroid_rationalBase hl ω hω0ne hω1ne hl0 hl1
      hper0 hper1 htor hfix M cst hd0 hd1 sh
  · intro I
    exact doubleSineOrbit_eRk_rationalBase hl ω hω0ne hω1ne hl0 hl1 hper0 hper1
      htor hfix M cst hd0 hd1 sh I

end

end GaloisForLFunctions.HTGeometry
