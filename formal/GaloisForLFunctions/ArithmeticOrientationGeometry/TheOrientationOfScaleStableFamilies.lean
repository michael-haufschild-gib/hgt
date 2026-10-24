import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationIndexOfACycle
import GaloisForLFunctions.ArithmeticOrientationGeometry.SectionsOnTheOrbitOfACycle

/-!
# The orientation of scale-stable families

The orientation theorem decides one orbit at a time. A **family** is a subspace `V` of real tests;
it is **scale-stable** when it contains every logarithmic translate of its members, so it contains
the orbit of each member and is stable under all correspondences. The span of the orbits of
finitely many cycles is the basic example (`orbitFamily`). Which families carry the Hodge index, and
how many negative squares does a family carry?

A family **jointly sees** a zero `ρ` when some member is nonzero at `γ_ρ` and some member is nonzero
at `γ̄_ρ`.

* **Joint seeing is seeing** (`jointlySees_iff`). If `f₁` misses `γ̄_ρ` and `f₂` misses `γ_ρ`, then
  `f₁ + f₂` sees `ρ`: a vector space is not the union of two proper subspaces. Hence a family is
  **jointly blind** to the off-line zeros iff every member is blind (`jointlyBlind_iff_forall_blind`).
* **Orientation of a family** (`scaleStable_nonneg_iff_jointlyBlind`). On a symmetric tempered
  configuration the Weil form is nonnegative on a scale-stable family iff the family is jointly
  blind: at every off-line pair all members vanish at the same point.
* **The oriented subspaces** (`orientedSubspace`, `scaleStable_nonneg_iff_le_orientedSubspace`). A
  choice `χ` of one point in every off-line pair defines the scale-stable subspace of tests vanishing
  at every chosen point; it is jointly blind. The oriented scale-stable families are exactly the
  subfamilies of these: the oriented locus is the union of the oriented subspaces, one for each
  choice, and orientation is not additive across choices.
* **The index of a family** (`scaleStable_index_law`). On every tempered configuration the negative
  index of the Weil form on a scale-stable family is the number of right zeros the family jointly
  sees (`ℕ∞`-valued). The bound holds for every finite family of members
  (`negIndex_family_le`, via the configuration of jointly seen zeros); it is attained on the orbit
  of one generic member (`exists_mem_sees`, `exists_orbit_negIndex_ge`).
* **Riemann–Roch on the surface of a family** (`familySurface_riemannRoch_iff`). An ample section
  cone of nonnegative degree on the restriction of the configuration surface to the family satisfies
  Riemann–Roch iff it contains the open positive cone and the family is jointly blind.
* **Finitely many orbits** (`jointlySees_orbitFamily_iff`). The span of the orbits of a set of tests
  sees `ρ` iff some test is nonzero at `γ_ρ` and some, possibly different, test is nonzero at `γ̄_ρ`:
  two cycles blind at opposite points of a pair span a family that sees it.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.HTGeometry (hermNegIndex)

/-! ### Joint seeing -/

/-- A family of tests is **scale-stable** when it contains every logarithmic translate of its
members. -/
def ScaleStable (V : Submodule ℝ (ℝ → ℝ)) : Prop := ∀ t : ℝ, ∀ f ∈ V, scaleShift t f ∈ V

/-- A family **jointly sees** `ρ`: some member is nonzero at `γ_ρ` and some member is nonzero at
`γ̄_ρ`. -/
def JointlySees (V : Submodule ℝ (ℝ → ℝ)) (ρ : ℂ) : Prop :=
  (∃ f ∈ V, paperFT (cx f) (gammaOf ρ) ≠ 0) ∧ ∃ g ∈ V, paperFT (cx g) (conj (gammaOf ρ)) ≠ 0

/-- A family is **jointly blind** to the off-line zeros when it jointly sees none of them. -/
def JointlyBlindOffLine (V : Submodule ℝ (ℝ → ℝ)) (Z : ZeroConfig) : Prop :=
  ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → ¬ JointlySees V ρ

variable {V : Submodule ℝ (ℝ → ℝ)}

theorem paperFT_cx_add_smul {f w : ℝ → ℝ} (hf : f ∈ realTests) (hw : w ∈ realTests) (t : ℝ)
    (z : ℂ) : paperFT (cx (f + t • w)) z = paperFT (cx f) z + t * paperFT (cx w) z := by
  have htw : t • w ∈ realTests := realTests.smul_mem t hw
  rw [cx_add, paperFT_add (cx_contDiff hf.1).continuous (cx_hasCompactSupport hf.2)
    (cx_contDiff htw.1).continuous (cx_hasCompactSupport htw.2), cx_smul, paperFT_smul]

/-- **A family jointly sees a zero iff one member sees it.** -/
theorem jointlySees_iff (hV : V ≤ realTests) {ρ : ℂ} : JointlySees V ρ ↔ ∃ f ∈ V, Sees f ρ := by
  constructor
  · rintro ⟨⟨f₁, h₁V, h₁⟩, ⟨f₂, h₂V, h₂⟩⟩
    by_cases hs₁ : paperFT (cx f₁) (conj (gammaOf ρ)) = 0
    · by_cases hs₂ : paperFT (cx f₂) (gammaOf ρ) = 0
      · -- `f₁ + f₂` is nonzero at both points
        refine ⟨f₁ + (1 : ℝ) • f₂, V.add_mem h₁V (V.smul_mem _ h₂V), ?_, ?_⟩
        · rw [paperFT_cx_add_smul (hV h₁V) (hV h₂V), hs₂, mul_zero, add_zero]; exact h₁
        · rw [paperFT_cx_add_smul (hV h₁V) (hV h₂V), hs₁, zero_add, ofReal_one, one_mul]; exact h₂
      · exact ⟨f₂, h₂V, hs₂, h₂⟩
    · exact ⟨f₁, h₁V, h₁, hs₁⟩
  · rintro ⟨f, hfV, h1, h2⟩
    exact ⟨⟨f, hfV, h1⟩, ⟨f, hfV, h2⟩⟩

/-- A family is jointly blind iff every member is blind. -/
theorem jointlyBlind_iff_forall_blind (hV : V ≤ realTests) (Z : ZeroConfig) :
    JointlyBlindOffLine V Z ↔ ∀ f ∈ V, BlindOffLine Z f := by
  constructor
  · intro h f hf ρ hρ hre
    by_contra hcon
    push Not at hcon
    exact h ρ hρ hre ((jointlySees_iff hV).mpr ⟨f, hf, hcon.1, hcon.2⟩)
  · intro h ρ hρ hre hj
    obtain ⟨f, hf, h1, h2⟩ := (jointlySees_iff hV).mp hj
    rcases h f hf ρ hρ hre with h' | h'
    · exact h1 h'
    · exact h2 h'

/-! ### The orientation of a family -/

/-- A blind test has nonnegative Weil form, on every configuration. -/
theorem configWeil_self_nonneg_of_blindOffLine (Z : ZeroConfig) {f : ℝ → ℝ}
    (hb : BlindOffLine Z f) : 0 ≤ configWeil Z f f := by
  rw [configWeil]
  refine SquareRootThreshold.re_W_nonneg_of_summand_nonneg Z fun ρ hρ => ?_
  by_cases hre : ρ.re = 1 / 2
  · exact SquareRootThreshold.re_Wsummand_nonneg_of_onLine Z _ hre
  · rcases hb ρ hρ hre with h | h
    · rw [ZeroConfig.Wsummand, h, mul_zero, zero_mul, Complex.zero_re]
    · rw [ZeroConfig.Wsummand, h, map_zero, mul_zero, Complex.zero_re]

/-- **Joint blindness orients a family**, on every configuration. -/
theorem configWeil_nonneg_of_jointlyBlind (hV : V ≤ realTests) (Z : ZeroConfig)
    (hb : JointlyBlindOffLine V Z) : ∀ f ∈ V, 0 ≤ configWeil Z f f := fun f hf =>
  configWeil_self_nonneg_of_blindOffLine Z ((jointlyBlind_iff_forall_blind hV Z).mp hb f hf)

/-- On a scale-stable family with nonnegative Weil form every member is blind: its orbit lies in
the family, so it is oriented. -/
theorem blindOffLine_of_scaleStable_nonneg (hV : V ≤ realTests) (hVs : ScaleStable V)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    (h : ∀ f ∈ V, 0 ≤ configWeil Z f f) {f : ℝ → ℝ} (hf : f ∈ V) : BlindOffLine Z f := by
  have hx : (configScalingDatum Z hZ).OrbitHodgeIndex (0, 0, ⟨f, hV hf⟩) := by
    rw [ScalingDatum.orbitHodgeIndex_iff_defect_nonneg]
    intro S c
    change 0 ≤ (configSurface Z hZ).defect _ _
    rw [configSurface_defect, orbitComb_test]
    exact h _ (Submodule.sum_mem _ fun g _ => V.smul_mem _ (hVs g f hf))
  exact ((orientation_tfae Z hZ hFE (0, 0, ⟨f, hV hf⟩)).out 1 2).mp hx

/-- **The orientation of a scale-stable family.** On a symmetric tempered configuration the Weil
form is nonnegative on a scale-stable family iff the family is jointly blind. -/
theorem scaleStable_nonneg_iff_jointlyBlind (hV : V ≤ realTests) (hVs : ScaleStable V)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z) :
    (∀ f ∈ V, 0 ≤ configWeil Z f f) ↔ JointlyBlindOffLine V Z :=
  ⟨fun h => (jointlyBlind_iff_forall_blind hV Z).mpr fun _ hf =>
      blindOffLine_of_scaleStable_nonneg hV hVs Z hZ hFE h hf,
    configWeil_nonneg_of_jointlyBlind hV Z⟩

/-- **For `ζ`**: Weil's form, computed from primes, Gamma factor and pole, is nonnegative on a
scale-stable family iff the family is jointly blind to the off-line zeros of `ζ`. -/
theorem zeta_scaleStable_nonneg_iff_jointlyBlind (hV : V ≤ realTests) (hVs : ScaleStable V) :
    (∀ f ∈ V, 0 ≤ weilPair f f) ↔ JointlyBlindOffLine V zetaZeroConfig := by
  rw [← scaleStable_nonneg_iff_jointlyBlind hV hVs zetaZeroConfig temperedConfig_zetaZeroConfig
    fesSymmetric_zetaZeroConfig]
  exact forall₂_congr fun f hf => by rw [configWeil_zeta_eq_weilPair (hV hf) (hV hf)]

/-! ### The oriented subspaces -/

/-- A **choice** of one point in every off-line reflection pair. -/
def IsChoice (Z : ZeroConfig) (χ : ℂ → ℂ) : Prop :=
  ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → χ ρ = gammaOf ρ ∨ χ ρ = conj (gammaOf ρ)

/-- The **oriented subspace** of a choice: real tests whose transform vanishes at every chosen
point. -/
def orientedSubspace (Z : ZeroConfig) (χ : ℂ → ℂ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | f ∈ realTests ∧ ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (cx f) (χ ρ) = 0}
  add_mem' {f g} hf hg := ⟨realTests.add_mem hf.1 hg.1, fun ρ hρ hre => by
    have h := paperFT_cx_add_smul hf.1 hg.1 1 (χ ρ)
    rw [one_smul] at h
    rw [h, hf.2 ρ hρ hre, hg.2 ρ hρ hre, mul_zero, add_zero]⟩
  zero_mem' := ⟨realTests.zero_mem, fun ρ _ _ => by simp [cx, paperFT]⟩
  smul_mem' c f hf := ⟨realTests.smul_mem c hf.1, fun ρ hρ hre => by
    rw [cx_smul, paperFT_smul, hf.2 ρ hρ hre, mul_zero]⟩

theorem orientedSubspace_le (Z : ZeroConfig) (χ : ℂ → ℂ) : orientedSubspace Z χ ≤ realTests :=
  fun _ hf => hf.1

theorem scaleStable_orientedSubspace (Z : ZeroConfig) (χ : ℂ → ℂ) :
    ScaleStable (orientedSubspace Z χ) := fun t _ hf =>
  ⟨scaleShift_mem t hf.1, fun ρ hρ hre => by
    rw [paperFT_cx_scaleShift_apply, hf.2 ρ hρ hre, mul_zero]⟩

/-- The oriented subspace of a choice is jointly blind. -/
theorem jointlyBlind_orientedSubspace {Z : ZeroConfig} {χ : ℂ → ℂ} (hχ : IsChoice Z χ) :
    JointlyBlindOffLine (orientedSubspace Z χ) Z := by
  rintro ρ hρ hre ⟨⟨f, hf, h1⟩, ⟨g, hg, h2⟩⟩
  rcases hχ ρ hρ hre with h | h
  · exact h1 (by rw [← h]; exact hf.2 ρ hρ hre)
  · exact h2 (by rw [← h]; exact hg.2 ρ hρ hre)

/-- **The oriented scale-stable families are the subfamilies of the oriented subspaces.** -/
theorem scaleStable_nonneg_iff_le_orientedSubspace (hV : V ≤ realTests) (hVs : ScaleStable V)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z) :
    (∀ f ∈ V, 0 ≤ configWeil Z f f) ↔ ∃ χ, IsChoice Z χ ∧ V ≤ orientedSubspace Z χ := by
  classical
  rw [scaleStable_nonneg_iff_jointlyBlind hV hVs Z hZ hFE]
  constructor
  · intro hb
    refine ⟨fun ρ => if ∀ f ∈ V, paperFT (cx f) (gammaOf ρ) = 0 then gammaOf ρ
      else conj (gammaOf ρ), fun ρ _ _ => ?_, fun f hf => ⟨hV hf, fun ρ hρ hre => ?_⟩⟩
    · dsimp only
      by_cases h : ∀ f ∈ V, paperFT (cx f) (gammaOf ρ) = 0
      · left; rw [if_pos h]
      · right; rw [if_neg h]
    · dsimp only
      by_cases h : ∀ f ∈ V, paperFT (cx f) (gammaOf ρ) = 0
      · rw [if_pos h]; exact h f hf
      · rw [if_neg h]
        push Not at h
        obtain ⟨g, hg, hg0⟩ := h
        by_contra hf0
        exact hb ρ hρ hre ⟨⟨g, hg, hg0⟩, ⟨f, hf, hf0⟩⟩
  · rintro ⟨χ, hχ, hle⟩ ρ hρ hre ⟨⟨f, hf, h1⟩, ⟨g, hg, h2⟩⟩
    exact jointlyBlind_orientedSubspace hχ ρ hρ hre ⟨⟨f, hle hf, h1⟩, ⟨g, hle hg, h2⟩⟩

/-! ### The index of a family -/

theorem jointlySees_reflect {ρ : ℂ} (h : JointlySees V ρ) : JointlySees V (reflect ρ) := by
  rw [JointlySees, gammaOf_reflect, conj_conj]
  exact ⟨h.2, h.1⟩

/-- **The configuration of the zeros jointly seen by a family.** -/
def jointlySeenConfig (Z : ZeroConfig) (V : Submodule ℝ (ℝ → ℝ)) : ZeroConfig where
  carrier := {ρ ∈ Z.carrier | JointlySees V ρ}
  mult := Z.mult
  one_le_mult ρ hρ := Z.one_le_mult ρ hρ.1
  strip ρ hρ := Z.strip ρ hρ.1
  reflect_mem ρ hρ := ⟨Z.reflect_mem ρ hρ.1, jointlySees_reflect hρ.2⟩
  mult_reflect ρ hρ := Z.mult_reflect ρ hρ.1
  finite_window T₁ T₂ := (Z.finite_window T₁ T₂).subset fun _ hρ => ⟨hρ.1.1, hρ.2⟩

theorem temperedConfig_jointlySeenConfig {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (V : Submodule ℝ (ℝ → ℝ)) : TemperedConfig (jointlySeenConfig Z V) :=
  (hZ.comp_injective (Set.inclusion_injective
    (show (jointlySeenConfig Z V).carrier ⊆ Z.carrier from fun _ h => h.1))).congr fun _ => rfl

/-- The right zeros jointly seen by a family. -/
def jointlySeenRightZeros (Z : ZeroConfig) (V : Submodule ℝ (ℝ → ℝ)) : Set ℂ :=
  {ρ ∈ Z.carrier | 1 / 2 < ρ.re ∧ JointlySees V ρ}

theorem rightZeros_jointlySeenConfig (Z : ZeroConfig) (V : Submodule ℝ (ℝ → ℝ)) :
    rightZeros (jointlySeenConfig Z V) = jointlySeenRightZeros Z V := by
  ext ρ
  simp only [rightZeros, jointlySeenRightZeros, jointlySeenConfig, Set.mem_setOf_eq]
  tauto

/-- The summand of two members vanishes at every zero the family does not jointly see. -/
theorem Wsummand_eq_zero_of_not_jointlySees {Z : ZeroConfig} {f g : ℝ → ℝ} (hf : f ∈ V)
    (hg : g ∈ V) {ρ : ℂ} (h : ¬ JointlySees V ρ) : Z.Wsummand (cx f) (cx g) ρ = 0 := by
  rw [JointlySees, not_and_or] at h
  rcases h with h | h
  · push Not at h
    rw [ZeroConfig.Wsummand, h f hf, mul_zero, zero_mul]
  · push Not at h
    rw [ZeroConfig.Wsummand, h g hg, map_zero, mul_zero]

/-- **On a family the Weil form of `Z` is that of the jointly seen zeros.** -/
theorem W_eq_jointlySeenConfig {Z : ZeroConfig} {f g : ℝ → ℝ} (hf : f ∈ V) (hg : g ∈ V) :
    Z.W (cx f) (cx g) = (jointlySeenConfig Z V).W (cx f) (cx g) := by
  set F : ℂ → ℂ := fun ρ => Z.Wsummand (cx f) (cx g) ρ with hF
  have hW : (jointlySeenConfig Z V).W (cx f) (cx g) =
      ∑' ρ : (jointlySeenConfig Z V).carrier, F ρ := rfl
  rw [ZeroConfig.W, hW, _root_.tsum_subtype, _root_.tsum_subtype]
  congr 1
  funext ρ
  by_cases hρ : ρ ∈ Z.carrier
  · by_cases hs : JointlySees V ρ
    · rw [Set.indicator_of_mem hρ, Set.indicator_of_mem
        (show ρ ∈ (jointlySeenConfig Z V).carrier from ⟨hρ, hs⟩)]
    · rw [Set.indicator_of_mem hρ, Set.indicator_of_notMem (fun h => hs h.2),
        Wsummand_eq_zero_of_not_jointlySees hf hg hs]
  · rw [Set.indicator_of_notMem hρ, Set.indicator_of_notMem (fun h => hρ h.1)]

/-- **Upper bound.** On a tempered configuration every finite family of members of `V` has at most
as many negative squares as `V` jointly sees right zeros. -/
theorem negIndex_family_le {Z : ZeroConfig} (hZ : TemperedConfig Z) (hV : V ≤ realTests)
    {ι : Type*} [Fintype ι] (F : ι → ℝ → ℝ) (hF : ∀ i, F i ∈ V) :
    (hermNegIndex (zeroGram Z fun i => cx (F i)) : ℕ∞) ≤ (jointlySeenRightZeros Z V).encard := by
  have h : zeroGram Z (fun i => cx (F i)) = zeroGram (jointlySeenConfig Z V) (fun i => cx (F i)) :=
    Matrix.ext fun i j => W_eq_jointlySeenConfig (hF i) (hF j)
  rw [h, ← rightZeros_jointlySeenConfig]
  exact negIndex_zeroGram_le_of_tempered _ (temperedConfig_jointlySeenConfig hZ V) _
    (fun i => cx_contDiff (hV (hF i)).1) (fun i => cx_hasCompactSupport (hV (hF i)).2)

theorem subsingleton_setOf_add_mul_eq_zero {a b : ℂ} (h : a ≠ 0 ∨ b ≠ 0) :
    {t : ℝ | a + (t : ℂ) * b = 0}.Subsingleton := by
  intro t₁ h₁ t₂ h₂
  have e₁ : a + (t₁ : ℂ) * b = 0 := h₁
  have e₂ : a + (t₂ : ℂ) * b = 0 := h₂
  have hsub : ((t₁ : ℂ) - t₂) * b = 0 := by linear_combination e₁ - e₂
  rcases mul_eq_zero.mp hsub with h0 | h0
  · exact_mod_cast sub_eq_zero.mp h0
  · rcases h with ha | hb
    · exact absurd (by rw [h0, mul_zero, add_zero] at e₁; exact e₁) ha
    · exact absurd h0 hb

/-- **A generic member sees a finite jointly seen set.** For finitely many zeros jointly seen by a
family, some member sees all of them: `F + t w` fails for at most finitely many real `t`. -/
theorem exists_mem_sees (hV : V ≤ realTests) (T : Finset ℂ) (hT : ∀ ρ ∈ T, JointlySees V ρ) :
    ∃ F ∈ V, ∀ ρ ∈ T, Sees F ρ := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, V.zero_mem, fun ρ hρ => absurd hρ (Finset.notMem_empty ρ)⟩
  | insert ρ₀ T _ ih =>
    obtain ⟨F, hFV, hF⟩ := ih fun ρ hρ => hT ρ (Finset.mem_insert_of_mem hρ)
    obtain ⟨w, hwV, hw⟩ := (jointlySees_iff hV).mp (hT ρ₀ (Finset.mem_insert_self _ _))
    -- the parameters `t` for which `F + t w` misses a point
    have hB : (⋃ ρ ∈ ((insert ρ₀ T : Finset ℂ) : Set ℂ),
        ({t : ℝ | paperFT (cx F) (gammaOf ρ) + (t : ℂ) * paperFT (cx w) (gammaOf ρ) = 0} ∪
          {t : ℝ | paperFT (cx F) (conj (gammaOf ρ)) +
            (t : ℂ) * paperFT (cx w) (conj (gammaOf ρ)) = 0})).Finite := by
      refine (insert ρ₀ T).finite_toSet.biUnion fun ρ hρ => ?_
      have hρ' : ρ = ρ₀ ∨ ρ ∈ T := Finset.mem_insert.mp hρ
      refine (Set.Subsingleton.finite (subsingleton_setOf_add_mul_eq_zero ?_)).union
        (Set.Subsingleton.finite (subsingleton_setOf_add_mul_eq_zero ?_))
      · rcases hρ' with rfl | hρT
        · exact Or.inr hw.1
        · exact Or.inl (hF ρ hρT).1
      · rcases hρ' with rfl | hρT
        · exact Or.inr hw.2
        · exact Or.inl (hF ρ hρT).2
    obtain ⟨t, ht⟩ := hB.exists_notMem
    refine ⟨F + t • w, V.add_mem hFV (V.smul_mem t hwV), fun ρ hρ => ⟨?_, ?_⟩⟩
    · rw [paperFT_cx_add_smul (hV hFV) (hV hwV)]
      exact fun h => ht (Set.mem_biUnion (Finset.mem_coe.mpr hρ) (Or.inl h))
    · rw [paperFT_cx_add_smul (hV hFV) (hV hwV)]
      exact fun h => ht (Set.mem_biUnion (Finset.mem_coe.mpr hρ) (Or.inr h))

theorem denseShifts_univ : DenseShifts Set.univ := fun v _ ε hε =>
  ⟨v, Set.mem_univ _, by rw [sub_self, abs_zero]; exact hε⟩

/-- **The index of a scale-stable family is attained on the orbit of one member.** -/
theorem exists_orbit_negIndex_ge (hV : V ≤ realTests) {Z : ZeroConfig}
    (hZ : TemperedConfig Z) {n : ℕ} (hn : (n : ℕ∞) ≤ (jointlySeenRightZeros Z V).encard) :
    ∃ F ∈ V, ∃ S : Finset ℝ, n ≤ hermNegIndex (zeroGram Z fun s : S =>
      ArithmeticCastelnuovoSeveri.translate s (cx F)) := by
  obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_encard_eq hn
  have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
  obtain ⟨F, hFV, hF⟩ := exists_mem_sees hV hTfin.toFinset fun ρ hρ =>
    (hTsub (hTfin.mem_toFinset.mp hρ)).2.2
  have hsub : T ⊆ seenRightZeros Z F := fun ρ hρ =>
    ⟨(hTsub hρ).1, (hTsub hρ).2.1, hF ρ (hTfin.mem_toFinset.mpr hρ)⟩
  have hn' : (n : ℕ∞) ≤ (seenRightZeros Z F).encard := hTcard ▸ Set.encard_le_encard hsub
  obtain ⟨S, -, hS⟩ := (orientationIndex_law Z hZ (hV hFV) denseShifts_univ n).mpr hn'
  exact ⟨F, hFV, S, hS⟩

/-- **The index law of a scale-stable family.** On a tempered configuration, some finite family
of translates of a member of `V` has `n` negative squares iff `V` jointly sees at least `n` right
zeros; and no finite family of members has more. -/
theorem scaleStable_index_law (hV : V ≤ realTests) (hVs : ScaleStable V) {Z : ZeroConfig}
    (hZ : TemperedConfig Z) (n : ℕ) :
    (∃ F ∈ V, ∃ S : Finset ℝ, n ≤ hermNegIndex (zeroGram Z fun s : S =>
      ArithmeticCastelnuovoSeveri.translate s (cx F))) ↔
      (n : ℕ∞) ≤ (jointlySeenRightZeros Z V).encard := by
  refine ⟨fun ⟨F, hFV, S, hS⟩ => ?_, exists_orbit_negIndex_ge hV hZ⟩
  have h := negIndex_family_le hZ hV (fun s : S => scaleShift s F) fun s => hVs s F hFV
  exact (ENat.coe_le_coe.mpr hS).trans h

/-! ### The surface of a family -/

/-- The cycles whose test lies in the family. -/
def familySpan (V : Submodule ℝ (ℝ → ℝ)) : Submodule ℝ ScalingCycle where
  carrier := {x | (x.2.2 : ℝ → ℝ) ∈ V}
  add_mem' hx hy := V.add_mem hx hy
  zero_mem' := V.zero_mem
  smul_mem' c _ hx := V.smul_mem c hx

/-- **The surface of a family**: the configuration surface restricted to the pole plane and `V`. -/
def familySurface (Z : ZeroConfig) (hZ : TemperedConfig Z) (V : Submodule ℝ (ℝ → ℝ)) :
    PolarSurface (familySpan V) :=
  (configSurface Z hZ).restrict (familySpan V) V.zero_mem V.zero_mem

theorem familySurface_defect_nonneg_iff (hV : V ≤ realTests) (Z : ZeroConfig)
    (hZ : TemperedConfig Z) :
    (∀ w : familySpan V, 0 ≤ (familySurface Z hZ V).defect w w) ↔
      ∀ f ∈ V, 0 ≤ configWeil Z f f := by
  constructor
  · intro h f hf
    have := h ⟨(0, 0, ⟨f, hV hf⟩), hf⟩
    rwa [familySurface, PolarSurface.restrict_defect, configSurface_defect] at this
  · intro h w
    rw [familySurface, PolarSurface.restrict_defect, configSurface_defect]
    exact h _ w.2

/-- **Riemann–Roch on the surface of a family is its joint blindness.** For every set of classes
of nonnegative ample degree satisfying the ample axiom, Riemann–Roch holds iff the set contains the
open positive cone and the family is jointly blind to the off-line zeros. -/
theorem familySurface_riemannRoch_iff (hV : V ≤ realTests) (hVs : ScaleStable V) (Z : ZeroConfig)
    (hZ : TemperedConfig Z) (hFE : FESymmetric Z) {E' : Set (familySpan V)}
    (hdeg : ∀ w ∈ E', 0 ≤ (familySurface Z hZ V).pair w (familySurface Z hZ V).ample)
    (hA : (familySurface Z hZ V).AmpleAxiom E') :
    (familySurface Z hZ V).RiemannRochAxiom E' ↔
      (familySurface Z hZ V).openPositiveCone ⊆ E' ∧ JointlyBlindOffLine V Z := by
  rw [(familySurface Z hZ V).riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg hdeg hA,
    familySurface_defect_nonneg_iff hV Z hZ, scaleStable_nonneg_iff_jointlyBlind hV hVs Z hZ hFE]

/-! ### Finitely many orbits -/

/-- The span of the orbits of a set of tests. -/
def orbitFamily (fs : Set (ℝ → ℝ)) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ {g | ∃ f ∈ fs, ∃ t : ℝ, g = scaleShift t f}

theorem orbitFamily_le {fs : Set (ℝ → ℝ)} (hfs : fs ⊆ realTests) : orbitFamily fs ≤ realTests :=
  Submodule.span_le.mpr fun _ ⟨_, hf, t, hg⟩ => hg ▸ scaleShift_mem t (hfs hf)

theorem subset_orbitFamily (fs : Set (ℝ → ℝ)) : fs ⊆ orbitFamily fs := fun f hf =>
  Submodule.subset_span ⟨f, hf, 0, (scaleShift_zero f).symm⟩

theorem scaleStable_orbitFamily (fs : Set (ℝ → ℝ)) : ScaleStable (orbitFamily fs) := by
  intro t _ hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f', hf', s, rfl⟩ := hg
    exact Submodule.subset_span ⟨f', hf', t + s, (scaleShift_add t s f').symm⟩
  | zero => rw [scaleShift_zero_fun]; exact Submodule.zero_mem _
  | add g h _ _ hg hh => rw [scaleShift_add_fun]; exact Submodule.add_mem _ hg hh
  | smul c g _ hg => rw [scaleShift_smul_fun]; exact Submodule.smul_mem _ c hg

/-- If every test of the set vanishes at `z`, so does every member of the span of their orbits. -/
theorem paperFT_eq_zero_of_mem_orbitFamily {fs : Set (ℝ → ℝ)} (hfs : fs ⊆ realTests) {z : ℂ}
    (hz : ∀ f ∈ fs, paperFT (cx f) z = 0) {g : ℝ → ℝ} (hg : g ∈ orbitFamily fs) :
    paperFT (cx g) z = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, hf, t, rfl⟩ := hg
    rw [paperFT_cx_scaleShift_apply, hz f hf, mul_zero]
  | zero => simp [cx, paperFT]
  | add g h hgm hhm hg hh =>
    have e := paperFT_cx_add_smul (orbitFamily_le hfs hgm) (orbitFamily_le hfs hhm) 1 z
    rw [one_smul] at e
    rw [e, hg, hh, mul_zero, add_zero]
  | smul c g _ hg => rw [cx_smul, paperFT_smul, hg, mul_zero]

/-- **The span of finitely many orbits sees `ρ`** iff some test is nonzero at `γ_ρ` and some test
is nonzero at `γ̄_ρ`. -/
theorem jointlySees_orbitFamily_iff {fs : Set (ℝ → ℝ)} (hfs : fs ⊆ realTests) {ρ : ℂ} :
    JointlySees (orbitFamily fs) ρ ↔
      (∃ f ∈ fs, paperFT (cx f) (gammaOf ρ) ≠ 0) ∧
        ∃ g ∈ fs, paperFT (cx g) (conj (gammaOf ρ)) ≠ 0 := by
  constructor
  · rintro ⟨⟨f, hf, h1⟩, ⟨g, hg, h2⟩⟩
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h1 (paperFT_eq_zero_of_mem_orbitFamily hfs hcon hf)
    · by_contra hcon
      push Not at hcon
      exact h2 (paperFT_eq_zero_of_mem_orbitFamily hfs hcon hg)
  · rintro ⟨⟨f, hf, h1⟩, ⟨g, hg, h2⟩⟩
    exact ⟨⟨f, subset_orbitFamily fs hf, h1⟩, ⟨g, subset_orbitFamily fs hg, h2⟩⟩

end GaloisForLFunctions.ArithmeticOrientationGeometry
