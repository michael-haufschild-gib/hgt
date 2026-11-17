import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeWalkFiniteness
import GaloisForLFunctions.HTGeometry.DenseFeatureGramUnitary

/-!
# Gram reconstruction of the finite probe dynamics

Ordinary and Weil Gram matrices determine the entire marked reflection hull:
a unique unitary matches probes and intertwines reflection, probe projection,
and every walk iterate. Thus static Gram data reconstruct all finite-time
probe amplitudes, including redundant probe families.

The reflection-sector construction extends the finite character-averaging
mechanism of Aoki, arXiv:2611.20592, Lemma 3.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open GaloisForLFunctions.HTGeometry
open HilbertMetric.NomologicalCrossGram
variable {N : ℕ} (p q : Fin N → {x : ℝ // 1 ≤ x})

/-- An original probe as an element of its minimal reflection hull. -/
def hullProbe (i : Fin N) : reflectionHull p :=
  ⟨probeVec (p i).property, probeSpace_le_reflectionHull p (Submodule.subset_span ⟨i, rfl⟩)⟩

/-- Original and reflected probes form a total feature family of the hull. -/
def hullFeature : Bool × Fin N → reflectionHull p
  | (false, i) => hullProbe p i
  | (true, i) => hullReflection p (hullProbe p i)

theorem hullFeature_reflection (b : Bool) (i : Fin N) :
    hullReflection p (hullFeature p (b, i)) = hullFeature p (!b, i) := by
  cases b
  · rfl
  · exact LinearMap.congr_fun (hullReflection_sq p) (hullProbe p i)

theorem hullFeature_span : Submodule.span ℂ (Set.range (hullFeature p)) = ⊤ := by
  apply top_unique
  intro x _
  let A := Submodule.span ℂ (Set.range (hullFeature p))
  let B := A.map (reflectionHull p).subtype
  have hp : probeSpace p ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨hullFeature p (false, i),
      Submodule.subset_span ⟨(false, i), rfl⟩, rfl⟩
  have hr : (probeSpace p).map zeroReflection.toLinearMap ≤ B := by
    rw [probeSpace, Submodule.map_span, ← Set.range_comp]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨hullFeature p (true, i),
      Submodule.subset_span ⟨(true, i), rfl⟩, rfl⟩
  have hb : reflectionHull p ≤ B := sup_le hp hr
  obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp (hb x.property)
  have hxy : y = x := Subtype.ext he
  rwa [hxy] at hy

theorem hullFeature_synthesis_surjective : Function.Surjective (featureSynthesis (hullFeature p)) := by
  apply LinearMap.range_eq_top.mp
  rw [range_featureSynthesis_eq_span, hullFeature_span]

private theorem reflected_probe_inner (i j : Fin N) :
    inner ℂ (zeroReflection (probeVec (p i).property)) (probeVec (p j).property) =
      probeGram (fun k => (p k).val) j i := by
  exact (bareMixedEnergy_probe_eq_inner (p j).property (p i).property).symm

/-- The ordinary and Weil Gram matrices determine all four blocks of the reflected feature Gram. -/
theorem hullFeature_inner_eq
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val))
    (a b : Bool × Fin N) :
    inner ℂ (hullFeature p a) (hullFeature p b) = inner ℂ (hullFeature q a) (hullFeature q b) := by
  obtain ⟨a, i⟩ := a
  obtain ⟨b, j⟩ := b
  cases a <;> cases b
  · exact congrFun (congrFun hH j) i
  · change inner ℂ (probeVec (p i).property) (zeroReflection (probeVec (p j).property)) =
      inner ℂ (probeVec (q i).property) (zeroReflection (probeVec (q j).property))
    rw [← zeroReflection_inner_left, ← zeroReflection_inner_left,
      reflected_probe_inner, reflected_probe_inner]
    exact congrFun (congrFun hK j) i
  · change inner ℂ (zeroReflection (probeVec (p i).property)) (probeVec (p j).property) =
      inner ℂ (zeroReflection (probeVec (q i).property)) (probeVec (q j).property)
    rw [reflected_probe_inner, reflected_probe_inner]
    exact congrFun (congrFun hK j) i
  · change inner ℂ (zeroReflection (probeVec (p i).property)) (zeroReflection (probeVec (p j).property)) =
      inner ℂ (zeroReflection (probeVec (q i).property)) (zeroReflection (probeVec (q j).property))
    rw [zeroReflection_inner_map_map, zeroReflection_inner_map_map]
    exact congrFun (congrFun hH j) i

/-- Equal ordinary and Weil Grams give the canonical unitary of marked reflection hulls. -/
def markedHullUnitary
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val)) :
    reflectionHull p ≃ₗᵢ[ℂ] reflectionHull q :=
  codomainIsometryEquivOfInnerEq (featureSynthesis (hullFeature p)) (featureSynthesis (hullFeature q))
    (inner_featureSynthesis_eq _ _ (hullFeature_inner_eq p q hH hK))
    (hullFeature_synthesis_surjective p) (hullFeature_synthesis_surjective q)

theorem markedHullUnitary_feature
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val))
    (a : Bool × Fin N) : markedHullUnitary p q hH hK (hullFeature p a) = hullFeature q a := by
  have h := codomainIsometryEquivOfInnerEq_apply
    (featureSynthesis (hullFeature p)) (featureSynthesis (hullFeature q))
    (inner_featureSynthesis_eq _ _ (hullFeature_inner_eq p q hH hK))
    (hullFeature_synthesis_surjective p) (hullFeature_synthesis_surjective q)
    (Finsupp.single a 1)
  simpa only [markedHullUnitary, featureSynthesis_single, one_smul] using h

private theorem linearMap_ext_hullFeature {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f g : reflectionHull p →ₗ[ℂ] W) (h : ∀ a, f (hullFeature p a) = g (hullFeature p a)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := hullFeature_synthesis_surjective p x
  induction a using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add i c a hi hc ih =>
    rw [map_add, featureSynthesis_single, map_add, map_add, map_smul, map_smul, h, ih]

/-- Reconstruction intertwines the actual zero reflection on the complete finite hull. -/
theorem markedHullUnitary_reflection
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val))
    (x : reflectionHull p) :
    markedHullUnitary p q hH hK (hullReflection p x) =
      hullReflection q (markedHullUnitary p q hH hK x) := by
  have he := linearMap_ext_hullFeature p
    ((markedHullUnitary p q hH hK).toLinearMap.comp (hullReflection p))
    ((hullReflection q).comp (markedHullUnitary p q hH hK).toLinearMap) (by
      rintro ⟨b, i⟩
      change markedHullUnitary p q hH hK (hullReflection p (hullFeature p (b, i))) =
        hullReflection q (markedHullUnitary p q hH hK (hullFeature p (b, i)))
      rw [hullFeature_reflection, markedHullUnitary_feature, markedHullUnitary_feature,
        hullFeature_reflection])
  exact LinearMap.congr_fun he x

/-- A reflection-intertwining unitary is fixed uniquely by its action on the original probes. -/
theorem markedHullUnitary_unique
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val))
    (U : reflectionHull p ≃ₗᵢ[ℂ] reflectionHull q)
    (hU : ∀ i, U (hullProbe p i) = hullProbe q i)
    (hR : ∀ x, U (hullReflection p x) = hullReflection q (U x)) :
    U = markedHullUnitary p q hH hK := by
  have he := linearMap_ext_hullFeature p U.toLinearMap (markedHullUnitary p q hH hK).toLinearMap (by
    rintro ⟨b, i⟩
    change U (hullFeature p (b, i)) = markedHullUnitary p q hH hK (hullFeature p (b, i))
    rw [markedHullUnitary_feature]
    cases b
    · exact hU i
    · change U (hullReflection p (hullProbe p i)) = hullReflection q (hullProbe q i)
      rw [hR, hU])
  apply LinearIsometryEquiv.ext
  intro x
  exact LinearMap.congr_fun he x

/-- The pair of Gram matrices is a complete invariant of marked finite reflection representations. -/
theorem probe_gram_pair_iff_unique_unitary :
    (hilbertProbeGram p = hilbertProbeGram q ∧
      probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val)) ↔
    ∃! U : reflectionHull p ≃ₗᵢ[ℂ] reflectionHull q,
      (∀ i, U (hullProbe p i) = hullProbe q i) ∧
      ∀ x, U (hullReflection p x) = hullReflection q (U x) := by
  constructor
  · rintro ⟨hH, hK⟩
    refine ⟨markedHullUnitary p q hH hK, ⟨?_, markedHullUnitary_reflection p q hH hK⟩, ?_⟩
    · intro i
      exact markedHullUnitary_feature p q hH hK (false, i)
    · intro U hU
      exact markedHullUnitary_unique p q hH hK U hU.1 hU.2
  · rintro ⟨U, ⟨hU, hR⟩, _⟩
    constructor
    · ext i j
      have h := U.inner_map_map (hullProbe p j) (hullProbe p i)
      rw [hU, hU] at h
      exact h.symm
    · ext i j
      rw [← reflected_probe_inner p, ← reflected_probe_inner q]
      have h := U.inner_map_map (hullReflection p (hullProbe p j)) (hullProbe p i)
      rw [hR, hU, hU] at h
      exact h.symm

/-- Restricting the original probe projection to its reflection hull. -/
def hullProbeProjection : Module.End ℂ (reflectionHull p) :=
  (probeProjection p).toLinearMap.restrict (fun _ _ =>
    probeSpace_le_reflectionHull p ((probeSpace p).starProjection_apply_mem _))

private theorem unitary_probe_mem
    (U : reflectionHull p ≃ₗᵢ[ℂ] reflectionHull q)
    (hU : ∀ i, U (hullProbe p i) = hullProbe q i)
    (v : ZeroSpace) (hv : v ∈ probeSpace p) :
    (U ⟨v, probeSpace_le_reflectionHull p hv⟩ : ZeroSpace) ∈ probeSpace q := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    change (U (hullProbe p i) : ZeroSpace) ∈ probeSpace q
    rw [hU]
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    change (U 0 : ZeroSpace) ∈ probeSpace q
    rw [map_zero]
    exact (probeSpace q).zero_mem
  | add u v hu hv ihu ihv =>
    change (U (⟨u, probeSpace_le_reflectionHull p hu⟩ + ⟨v, probeSpace_le_reflectionHull p hv⟩) : ZeroSpace) ∈ probeSpace q
    rw [map_add]
    exact (probeSpace q).add_mem ihu ihv
  | smul c v hv ih =>
    change (U (c • ⟨v, probeSpace_le_reflectionHull p hv⟩) : ZeroSpace) ∈ probeSpace q
    rw [map_smul]
    exact (probeSpace q).smul_mem c ih

/-- Matching marked probes forces covariance of their orthogonal projections. -/
theorem markedHullUnitary_projection
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val))
    (x : reflectionHull p) :
    markedHullUnitary p q hH hK (hullProbeProjection p x) =
      hullProbeProjection q (markedHullUnitary p q hH hK x) := by
  let U := markedHullUnitary p q hH hK
  have hU (i : Fin N) : U (hullProbe p i) = hullProbe q i :=
    markedHullUnitary_feature p q hH hK (false, i)
  have hU' (i : Fin N) : U.symm (hullProbe q i) = hullProbe p i := by
    rw [← hU, U.symm_apply_apply]
  apply Subtype.ext
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (unitary_probe_mem p q U hU _ ((probeSpace p).starProjection_apply_mem x))
  intro w hw
  let z : reflectionHull q := ⟨w, probeSpace_le_reflectionHull q hw⟩
  have hz : (U.symm z : ZeroSpace) ∈ probeSpace p :=
    unitary_probe_mem q p U.symm hU' w hw
  have ho : inner ℂ (x - hullProbeProjection p x) (U.symm z) = 0 := by
    change inner ℂ ((x : ZeroSpace) - (probeSpace p).starProjection x) (U.symm z : ZeroSpace) = 0
    exact (probeSpace p).starProjection_inner_eq_zero x _ hz
  have he := U.inner_map_map (x - hullProbeProjection p x) (U.symm z)
  rw [map_sub, U.apply_symm_apply] at he
  exact he.trans ho

/-- The two static Gram matrices reconstruct every step of the actual probe walk. -/
theorem markedHullUnitary_walk
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val))
    (x : reflectionHull p) :
    markedHullUnitary p q hH hK (hullWalk p x) =
      hullWalk q (markedHullUnitary p q hH hK x) := by
  change markedHullUnitary p q hH hK
    (hullReflection p (hullProbeProjection p x + hullProbeProjection p x - x)) =
    hullReflection q (hullProbeProjection q (markedHullUnitary p q hH hK x) +
      hullProbeProjection q (markedHullUnitary p q hH hK x) - markedHullUnitary p q hH hK x)
  rw [markedHullUnitary_reflection, map_sub, map_add,
    markedHullUnitary_projection]

/-- All finite-time probe amplitudes agree under Gram reconstruction. -/
theorem markedHullUnitary_walk_readout
    (hH : hilbertProbeGram p = hilbertProbeGram q)
    (hK : probeGram (fun i => (p i).val) = probeGram (fun i => (q i).val))
    (x : reflectionHull p) (n : ℕ) (i : Fin N) :
    inner ℂ (hullProbe q i) ((hullWalk q ^ n) (markedHullUnitary p q hH hK x)) =
      inner ℂ (hullProbe p i) ((hullWalk p ^ n) x) := by
  have he : ∀ n, markedHullUnitary p q hH hK ((hullWalk p ^ n) x) =
      (hullWalk q ^ n) (markedHullUnitary p q hH hK x) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, markedHullUnitary_walk, ih,
        pow_succ', Module.End.mul_apply]
  have hp : markedHullUnitary p q hH hK (hullProbe p i) = hullProbe q i :=
    markedHullUnitary_feature p q hH hK (false, i)
  rw [← he n, ← hp]
  exact (markedHullUnitary p q hH hK).inner_map_map _ _

#print axioms markedHullUnitary_walk
#print axioms markedHullUnitary_walk_readout

#print axioms probe_gram_pair_iff_unique_unitary
#print axioms markedHullUnitary_reflection
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
