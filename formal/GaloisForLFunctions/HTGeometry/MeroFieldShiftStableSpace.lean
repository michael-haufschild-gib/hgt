import GaloisForLFunctions.HTGeometry.RelativeTwoShiftGaugeCharacterization
import GaloisForLFunctions.HTGeometry.AffineFirstOrderDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.DerivInvariantSuperspace

/-!
# Shift-stable finite-dimensional spaces in the meromorphic differential field

Infrastructure for the vector form of the two-shift law: a finite-dimensional space of meromorphic
germs stable under two `ℚ`-independent translations consists of differentially algebraic elements.

This file supplies the three ingredients that the induction needs.

* **`differentialAlgebraicOver_of_deriv`** — differential algebraicity is closed under
  *antiderivatives*: if `x′` is differentially algebraic over `F` then so is `x`.  The relation
  `y₁ − x′ = 0` is a nonzero first-order jet relation over `F⟨x′⟩`, and differential-algebraic
  transitivity descends it to `F`.  This is the converse of `differentialAlgebraicOver_deriv`;
* `addTranslationMeroEquiv_comm` — the translations commute;
* `meroDerivL` — the meromorphic derivation as a `ℂ`-linear map, the complex constants being
  differential constants.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-! ## Antiderivatives -/

/-- **Differential algebraicity is closed under antiderivatives.**  An element whose derivative is
differentially algebraic over `F` is itself differentially algebraic over `F`. -/
theorem differentialAlgebraicOver_of_deriv {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] {x : E}
    (hx : DifferentialAlgebraicOver F x′) : DifferentialAlgebraicOver F x := by
  set S := differentialAdjoin F ({x′} : Set E) with hS
  letI : DifferentialAlgebra S E :=
    ⟨fun c => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F ({x′} : Set E)) c⟩
  have hmem : x′ ∈ S := subset_differentialAdjoin F ({x′} : Set E) rfl
  have hrel : DifferentialAlgebraicOver S x :=
    differentialAlgebraicOver_of_deriv_eq_base (F := S) (E := E) ⟨x′, hmem⟩ rfl
  exact differentialAlgebraicOver_trans hx hrel

/-! ## The translations commute -/

-- The ambient instance set is exactly the one used by the two-shift gauge module, so that its
-- lemmas about `algebraMap ℂ (meroField univ)` apply verbatim.
attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-- Translated germs commute: translating by `p` then by `q` is translating by `q` then by `p`. -/
theorem addTranslationAnalyticEquiv_comm (p q : ℂ) (a : analyticSubring (Set.univ : Set ℂ)) :
    addTranslationAnalyticEquiv p (addTranslationAnalyticEquiv q a) =
      addTranslationAnalyticEquiv q (addTranslationAnalyticEquiv p a) := by
  obtain ⟨A, hA, hAa⟩ := a.2
  have h1 := addTranslationAnalyticEquiv_rep p (addTranslationAnalyticEquiv_rep q hAa)
  have h2 := addTranslationAnalyticEquiv_rep q (addTranslationAnalyticEquiv_rep p hAa)
  apply Subtype.ext
  rw [← h1, ← h2]
  congr 1
  funext z
  congr 1
  ring

/-- The meromorphic translations commute. -/
theorem addTranslationMeroEquiv_comm (p q : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv p (addTranslationMeroEquiv q x) =
      addTranslationMeroEquiv q (addTranslationMeroEquiv p x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (analyticSubring Set.univ) x
  rw [map_div₀, map_div₀, map_div₀, map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, addTranslationAnalyticEquiv_comm p q a,
    addTranslationAnalyticEquiv_comm p q b]

/-! ## The derivation is complex linear -/

/-- The meromorphic derivation as a `ℂ`-linear map. -/
def meroDerivL : meroField (Set.univ : Set ℂ) →ₗ[ℂ] meroField (Set.univ : Set ℂ) where
  toFun := fun x => Differential.deriv x
  map_add' := fun x y => map_add Differential.deriv x y
  map_smul' := fun c x => by
    letI : Algebra ℤ (meroField (Set.univ : Set ℂ)) := Ring.toIntAlgebra _
    simp [Algebra.smul_def, Derivation.leibniz, deriv_algebraMap_complex]

@[simp]
theorem meroDerivL_apply (x : meroField (Set.univ : Set ℂ)) :
    meroDerivL x = Differential.deriv x := rfl

/-! ## The translations are complex linear -/

/-- Translation fixes the embedded complex constants. -/
theorem addTranslationMeroEquiv_algebraMap_complex_self (q c : ℂ) :
    addTranslationMeroEquiv q (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  show addTranslationMeroEquiv q (algebraMap (analyticSubring (Set.univ : Set ℂ))
      (meroField Set.univ) (constToAnalytic Set.univ c)) =
    algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic Set.univ c)
  rw [addTranslationMeroEquiv_algebraMap]
  congr 1

/-- A translation of the global meromorphic field, as a `ℂ`-linear map. -/
def meroShiftL (q : ℂ) :
    meroField (Set.univ : Set ℂ) →ₗ[ℂ] meroField (Set.univ : Set ℂ) where
  toFun := fun x => addTranslationMeroEquiv q x
  map_add' := fun x y => map_add _ x y
  map_smul' := fun c x => by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul,
      addTranslationMeroEquiv_algebraMap_complex_self]

@[simp]
theorem meroShiftL_apply (q : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    meroShiftL q x = addTranslationMeroEquiv q x := rfl

/-! ## The induction -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **A shift-stable finite-dimensional space consists of differentially algebraic germs.**  If a
finite-dimensional complex space of meromorphic germs is stable under two `ℚ`-independent
translations, every one of its elements is differentially algebraic over the rational coordinate
field.  The induction is on the dimension: the two translations are commuting complex-linear
operators, so they have a common eigenvector `y`, which is a constant-multiplier germ and hence
differentially algebraic; dividing the space by `y` — a field operation, so no nonvanishing
hypothesis is needed — gives a shift-stable space containing `1`, whose derivative image is
shift-stable of strictly smaller dimension; and differential algebraicity of a derivative lifts to
the element by `differentialAlgebraicOver_of_deriv`. -/
theorem differentialAlgebraicOver_of_mem_shiftStable {α β : ℂ}
    (hindep : LinearIndependent ℚ ![α, β]) :
    ∀ (n : ℕ) (W : Submodule ℂ (meroField (Set.univ : Set ℂ))),
      FiniteDimensional ℂ W → Module.finrank ℂ W ≤ n →
      (∀ u ∈ W, addTranslationMeroEquiv α u ∈ W) →
      (∀ u ∈ W, addTranslationMeroEquiv β u ∈ W) →
      ∀ u ∈ W, DifferentialAlgebraicOver (RatFunc ℂ) u := by
  have hzero : DifferentialAlgebraicOver (RatFunc ℂ) (0 : meroField (Set.univ : Set ℂ)) := by
    simpa using differentialAlgebraicOver_algebraMap (F := RatFunc ℂ)
      (E := meroField (Set.univ : Set ℂ)) 0
  intro n
  induction n with
  | zero =>
      intro W hfd hrank _ _ u hu
      have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hrank)
      rw [hbot, Submodule.mem_bot] at hu
      rw [hu]
      exact hzero
  | succ n ih =>
      intro W hfd hrank hshα hshβ u hu
      by_cases hW : W = ⊥
      · rw [hW, Submodule.mem_bot] at hu
        rw [hu]
        exact hzero
      haveI hnt : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      set S : Module.End ℂ W := (meroShiftL α).restrict hshα with hS
      set T : Module.End ℂ W := (meroShiftL β).restrict hshβ with hT
      have hcomm : ∀ w : W, S (T w) = T (S w) := by
        intro w
        apply Subtype.ext
        simp only [hS, hT, LinearMap.restrict_apply, meroShiftL_apply]
        exact addTranslationMeroEquiv_comm α β (w : meroField (Set.univ : Set ℂ))
      obtain ⟨v, lam, mu, hv0, hSv, hTv⟩ := exists_common_eigenvector S T hcomm
      set y : meroField (Set.univ : Set ℂ) := (v : meroField (Set.univ : Set ℂ)) with hy
      have hyW : y ∈ W := v.2
      have hy0 : y ≠ 0 := fun h => hv0 (Subtype.ext h)
      have hαy : addTranslationMeroEquiv α y =
          algebraMap ℂ (meroField (Set.univ : Set ℂ)) lam * y := by
        have := congrArg (Subtype.val : W → meroField (Set.univ : Set ℂ)) hSv
        simp only [hS, LinearMap.restrict_apply, meroShiftL_apply, SetLike.val_smul] at this
        rw [this, Algebra.smul_def]
      have hβy : addTranslationMeroEquiv β y =
          algebraMap ℂ (meroField (Set.univ : Set ℂ)) mu * y := by
        have := congrArg (Subtype.val : W → meroField (Set.univ : Set ℂ)) hTv
        simp only [hT, LinearMap.restrict_apply, meroShiftL_apply, SetLike.val_smul] at this
        rw [this, Algebra.smul_def]
      have hlam : lam ≠ 0 := by
        intro h
        apply hy0
        have : addTranslationMeroEquiv α y = 0 := by
          rw [hαy, h, map_zero, zero_mul]
        have h2 := congrArg (addTranslationMeroEquiv α).symm this
        rwa [RingEquiv.symm_apply_apply, map_zero] at h2
      have hmu : mu ≠ 0 := by
        intro h
        apply hy0
        have : addTranslationMeroEquiv β y = 0 := by
          rw [hβy, h, map_zero, zero_mul]
        have h2 := congrArg (addTranslationMeroEquiv β).symm this
        rwa [RingEquiv.symm_apply_apply, map_zero] at h2
      have hyDA : DifferentialAlgebraicOver (RatFunc ℂ) y :=
        differentialAlgebraicOver_of_constant_multipliers hindep hy0 hlam hmu hαy hβy
      -- the divided space
      set W' : Submodule ℂ (meroField (Set.univ : Set ℂ)) :=
        W.map (LinearMap.mulLeft ℂ y⁻¹) with hW'
      haveI : FiniteDimensional ℂ W' := by
        have hrangeW' : W' = LinearMap.range ((LinearMap.mulLeft ℂ y⁻¹).domRestrict W) :=
          (LinearMap.range_domRestrict _ _).symm
        rw [hrangeW']
        infer_instance
      have hmem' : ∀ w ∈ W', ∃ u₀ ∈ W, w = y⁻¹ * u₀ := by
        intro w hw
        obtain ⟨u₀, hu₀, hwu⟩ := hw
        exact ⟨u₀, hu₀, by rw [← hwu]; rfl⟩
      have hone : (1 : meroField (Set.univ : Set ℂ)) ∈ W' := by
        refine ⟨y, hyW, ?_⟩
        show y⁻¹ * y = 1
        exact inv_mul_cancel₀ hy0
      have hshift : ∀ (q : ℂ) (c : ℂ), c ≠ 0 →
          addTranslationMeroEquiv q y = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y →
          (∀ u₀ ∈ W, addTranslationMeroEquiv q u₀ ∈ W) →
          ∀ w ∈ W', addTranslationMeroEquiv q w ∈ W' := by
        intro q c hc hqy hqW w hw
        obtain ⟨u₀, hu₀, rfl⟩ := hmem' w hw
        refine ⟨c⁻¹ • addTranslationMeroEquiv q u₀, W.smul_mem _ (hqW u₀ hu₀), ?_⟩
        show y⁻¹ * (c⁻¹ • addTranslationMeroEquiv q u₀) =
          addTranslationMeroEquiv q (y⁻¹ * u₀)
        rw [map_mul, map_inv₀, hqy, Algebra.smul_def, map_inv₀, mul_inv]
        field_simp
      have hshα' := hshift α lam hlam hαy hshα
      have hshβ' := hshift β mu hmu hβy hshβ
      -- the derivative image
      set U : Submodule ℂ (meroField (Set.univ : Set ℂ)) := W'.map meroDerivL with hU
      haveI : FiniteDimensional ℂ U := by
        have hrangeU : U = LinearMap.range (meroDerivL.domRestrict W') :=
          (LinearMap.range_domRestrict _ _).symm
        rw [hrangeU]
        infer_instance
      have hrankU : Module.finrank ℂ U ≤ n := by
        set δ := meroDerivL.domRestrict W' with hδ
        have hrange : LinearMap.range δ = U := by
          rw [hδ, hU, LinearMap.range_domRestrict]
        have hker : (⟨1, hone⟩ : W') ∈ LinearMap.ker δ := by
          rw [LinearMap.mem_ker]
          show meroDerivL (1 : meroField (Set.univ : Set ℂ)) = 0
          simp
        have hkerne : LinearMap.ker δ ≠ ⊥ := by
          intro hbot
          rw [hbot, Submodule.mem_bot] at hker
          exact one_ne_zero (congrArg (Subtype.val : W' → meroField (Set.univ : Set ℂ)) hker)
        haveI : Nontrivial (LinearMap.ker δ) := Submodule.nontrivial_iff_ne_bot.mpr hkerne
        have hpos : 0 < Module.finrank ℂ (LinearMap.ker δ) :=
          Module.finrank_pos (R := ℂ) (M := LinearMap.ker δ)
        have hsum : Module.finrank ℂ (LinearMap.range δ) + Module.finrank ℂ (LinearMap.ker δ) =
            Module.finrank ℂ W' := LinearMap.finrank_range_add_finrank_ker δ
        have hW'rank : Module.finrank ℂ W' ≤ n + 1 :=
          le_trans (Submodule.finrank_map_le _ W) hrank
        rw [hrange] at hsum
        omega
      have hUα : ∀ w ∈ U, addTranslationMeroEquiv α w ∈ U := by
        intro w hw
        obtain ⟨w₀, hw₀, rfl⟩ := hw
        exact ⟨addTranslationMeroEquiv α w₀, hshα' w₀ hw₀,
          (addTranslationMeroEquiv_deriv α w₀).symm⟩
      have hUβ : ∀ w ∈ U, addTranslationMeroEquiv β w ∈ U := by
        intro w hw
        obtain ⟨w₀, hw₀, rfl⟩ := hw
        exact ⟨addTranslationMeroEquiv β w₀, hshβ' w₀ hw₀,
          (addTranslationMeroEquiv_deriv β w₀).symm⟩
      have hUDA := ih U inferInstance hrankU hUα hUβ
      -- conclude
      have huW' : y⁻¹ * u ∈ W' := ⟨u, hu, rfl⟩
      have hderivDA : DifferentialAlgebraicOver (RatFunc ℂ) ((y⁻¹ * u)′) :=
        hUDA _ ⟨y⁻¹ * u, huW', rfl⟩
      have hquotDA : DifferentialAlgebraicOver (RatFunc ℂ) (y⁻¹ * u) :=
        differentialAlgebraicOver_of_deriv hderivDA
      have : u = y * (y⁻¹ * u) := by field_simp
      rw [this]
      exact differentialAlgebraicOver_mul hyDA hquotDA

/-! ## The vector two-shift law -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **The vector two-shift law in the meromorphic differential field.**  A finite family of
meromorphic germs reproduced by two `ℚ`-independent translations up to *constant* matrices consists
of differentially algebraic germs.  The complex span of the family is finite-dimensional and stable
under both translations. -/
theorem differentialAlgebraicOver_of_constant_matrix_monodromy {α β : ℂ} {m : ℕ}
    (hindep : LinearIndependent ℚ ![α, β]) (x : Fin m → meroField (Set.univ : Set ℂ))
    (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ i, addTranslationMeroEquiv α (x i) =
      ∑ j, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (A i j) * x j)
    (hB : ∀ i, addTranslationMeroEquiv β (x i) =
      ∑ j, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (B i j) * x j)
    (i : Fin m) : DifferentialAlgebraicOver (RatFunc ℂ) (x i) := by
  classical
  set W : Submodule ℂ (meroField (Set.univ : Set ℂ)) := Submodule.span ℂ (Set.range x) with hW
  haveI hfd : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range x)
  have hstab : ∀ (q : ℂ) (M : Matrix (Fin m) (Fin m) ℂ),
      (∀ k, addTranslationMeroEquiv q (x k) =
        ∑ j, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (M k j) * x j) →
      ∀ u ∈ W, addTranslationMeroEquiv q u ∈ W := by
    intro q M hM u hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨k, rfl⟩ := hz
        rw [hM k]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
        have hsm : addTranslationMeroEquiv q (c • a) = c • addTranslationMeroEquiv q a :=
          (meroShiftL q).map_smul c a
        rw [hsm]
        exact Submodule.smul_mem _ _ ha
  exact differentialAlgebraicOver_of_mem_shiftStable hindep (Module.finrank ℂ W) W hfd le_rfl
    (hstab α A hA) (hstab β B hB) (x i) (Submodule.subset_span ⟨i, rfl⟩)

end

end GaloisForLFunctions.HTGeometry
