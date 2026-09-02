import GaloisForLFunctions.HTGeometry.PseudoDiffOpValuation
import GaloisForLFunctions.HTGeometry.DifferentialOperatorSemilinearMatrix
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Coefficient automorphisms of the rational pseudodifferential skew field

A derivation-preserving automorphism of `K` acts coefficientwise on `K[∂;δ]`.  The Ore
localization universal property extends that action canonically to `PseudoDiffOp K`; the inverse
coefficient automorphism gives its inverse, and the extension preserves `ordQ` and `v = -ordQ`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

open OreLocalization
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
open scoped OreLocalization nonZeroDivisors

variable {K : Type u} [Field K] [Differential K]

/-- Nonzero denominators embedded as units of the Ore skew field. -/
def numeratorNonzeroUnits : (DiffOp K)⁰ →* Units (PseudoDiffOp K) where
  toFun s := Units.mk0 (numeratorRingHom (s : DiffOp K)) (by
      intro h
      exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
        (numeratorRingHom_injective (h.trans (map_zero _).symm)))
  map_one' := by
    apply Units.ext
    exact OreLocalization.one_def.symm
  map_mul' s t := by
    apply Units.ext
    simp

@[simp] theorem numeratorNonzeroUnit_val (s : (DiffOp K)⁰) :
    (numeratorNonzeroUnits s : PseudoDiffOp K) = numeratorRingHom (s : DiffOp K) := rfl

/-- A ring automorphism sends every nonzero denominator to a unit of the Ore skew field. -/
def mapNonzeroUnits (τ : DiffOp K ≃+* DiffOp K) :
    (DiffOp K)⁰ →* Units (PseudoDiffOp K) where
  toFun s := Units.mk0 (numeratorRingHom (τ (s : DiffOp K))) (by
    intro h
    have h0 : τ (s : DiffOp K) = 0 :=
      numeratorRingHom_injective (h.trans (map_zero _).symm)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
      (τ.injective (h0.trans τ.map_zero.symm)))
  map_one' := by
    apply Units.ext
    change numeratorRingHom (τ (1 : DiffOp K)) = (1 : PseudoDiffOp K)
    rw [τ.map_one]
    exact OreLocalization.one_def.symm
  map_mul' s t := by
    apply Units.ext
    simp

@[simp] theorem mapNonzeroUnits_val (τ : DiffOp K ≃+* DiffOp K) (s : (DiffOp K)⁰) :
    (mapNonzeroUnits τ s : PseudoDiffOp K) = numeratorRingHom (τ (s : DiffOp K)) := rfl

/-- Canonical extension of a derivation-preserving coefficient automorphism to the Ore skew
field. -/
def mapPseudoRingHom (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    PseudoDiffOp K →+* PseudoDiffOp K :=
  OreLocalization.universalHom
    (numeratorRingHom.comp (mapRingEquiv σ hσ).toRingHom)
    (mapNonzeroUnits (mapRingEquiv σ hσ)) (fun _ => rfl)

@[simp] theorem mapPseudoRingHom_numerator (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (p : DiffOp K) :
    mapPseudoRingHom σ hσ (numeratorRingHom p) =
      numeratorRingHom (mapRingEquiv σ hσ p) := by
  exact OreLocalization.universalHom_commutes _ _ _

/-- Two endomorphisms of the Ore skew field agree when they agree on the operator ring. -/
theorem pseudoDiffOp_ringHom_ext (φ ψ : PseudoDiffOp K →+* PseudoDiffOp K)
    (h : ∀ p : DiffOp K, φ (numeratorRingHom p) = ψ (numeratorRingHom p)) : φ = ψ := by
  let f : DiffOp K →+* PseudoDiffOp K := φ.comp numeratorRingHom
  let fS : (DiffOp K)⁰ →* Units (PseudoDiffOp K) :=
    (Units.map φ.toMonoidHom).comp (numeratorNonzeroUnits (K := K))
  have hf : ∀ s : (DiffOp K)⁰, f (s : DiffOp K) = fS s := fun _ => rfl
  calc
    φ = OreLocalization.universalHom f fS hf :=
      OreLocalization.universalHom_unique f fS hf φ (fun _ => rfl)
    _ = ψ := (OreLocalization.universalHom_unique f fS hf ψ (fun p => (h p).symm)).symm

/-- The extended coefficient action is an automorphism of the Ore skew field. -/
def mapPseudoRingEquiv (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    PseudoDiffOp K ≃+* PseudoDiffOp K where
  toFun := mapPseudoRingHom σ hσ
  invFun := mapPseudoRingHom σ.symm (symm_deriv_comm hσ)
  left_inv x := by
    have hcomp : (mapPseudoRingHom σ.symm (symm_deriv_comm hσ)).comp
        (mapPseudoRingHom σ hσ) = RingHom.id (PseudoDiffOp K) := by
      apply pseudoDiffOp_ringHom_ext
      intro p
      change mapPseudoRingHom σ.symm (symm_deriv_comm hσ)
          (mapPseudoRingHom σ hσ (numeratorRingHom p)) = numeratorRingHom p
      rw [mapPseudoRingHom_numerator, mapPseudoRingHom_numerator]
      congr 1
      ext n
      simp
    exact DFunLike.congr_fun hcomp x
  right_inv x := by
    have hcomp : (mapPseudoRingHom σ hσ).comp
        (mapPseudoRingHom σ.symm (symm_deriv_comm hσ)) = RingHom.id (PseudoDiffOp K) := by
      apply pseudoDiffOp_ringHom_ext
      intro p
      change mapPseudoRingHom σ hσ
          (mapPseudoRingHom σ.symm (symm_deriv_comm hσ) (numeratorRingHom p)) = numeratorRingHom p
      rw [mapPseudoRingHom_numerator, mapPseudoRingHom_numerator]
      congr 1
      ext n
      simp
    exact DFunLike.congr_fun hcomp x
  map_mul' := (mapPseudoRingHom σ hσ).map_mul
  map_add' := (mapPseudoRingHom σ hσ).map_add

@[simp] theorem mapPseudoRingEquiv_numerator (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (p : DiffOp K) :
    mapPseudoRingEquiv σ hσ (numeratorRingHom p) =
      numeratorRingHom (mapRingEquiv σ hσ p) :=
  mapPseudoRingHom_numerator σ hσ p

/-- Commutation with the derivation is stable under composition. -/
theorem trans_deriv_comm (σ τ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (hτ : ∀ a : K, τ (a′) = (τ a)′) (a : K) :
    (σ.trans τ) (a′) = ((σ.trans τ) a)′ := by
  rw [RingEquiv.trans_apply, hσ, hτ]
  rfl

/-- The Ore-skew-field coefficient action sends the identity coefficient automorphism to the
identity. -/
theorem mapPseudoRingEquiv_refl :
    mapPseudoRingEquiv (RingEquiv.refl K) (fun _ => rfl) =
      RingEquiv.refl (PseudoDiffOp K) := by
  apply RingEquiv.ext
  apply pseudoDiffOp_ringHom_ext
  intro p
  rw [mapPseudoRingEquiv_numerator]
  congr 1
  ext n
  simp [mapRingEquiv]

/-- The Ore-skew-field coefficient action respects composition. -/
theorem mapPseudoRingEquiv_trans (σ τ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (hτ : ∀ a : K, τ (a′) = (τ a)′) :
    (mapPseudoRingEquiv σ hσ).trans (mapPseudoRingEquiv τ hτ) =
      mapPseudoRingEquiv (σ.trans τ) (trans_deriv_comm σ τ hσ hτ) := by
  apply RingEquiv.ext
  apply pseudoDiffOp_ringHom_ext
  intro p
  change mapPseudoRingEquiv τ hτ
      (mapPseudoRingEquiv σ hσ (numeratorRingHom p)) =
    mapPseudoRingEquiv (σ.trans τ) (trans_deriv_comm σ τ hσ hτ)
      (numeratorRingHom p)
  rw [mapPseudoRingEquiv_numerator, mapPseudoRingEquiv_numerator,
    mapPseudoRingEquiv_numerator]
  congr 1
  ext n
  simp [mapRingEquiv]

/-- Coefficient automorphisms preserve rational pseudodifferential order. -/
theorem ordQ_mapPseudoRingHom (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (x : PseudoDiffOp K) :
    ordQ (mapPseudoRingHom σ hσ x) = ordQ x := by
  induction x using OreLocalization.ind with
  | _ r s =>
    by_cases hr : r = 0
    · have hx : r /ₒ s = (0 : PseudoDiffOp K) := by
        rw [hr]
        exact OreLocalization.zero_oreDiv s
      rw [hx, map_zero, ordQ_zero]
    · let τ : DiffOp K ≃+* DiffOp K := mapRingEquiv σ hσ
      have hs : (s : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
      have hτs : τ (s : DiffOp K) ≠ 0 := fun h => hs (τ.injective (h.trans τ.map_zero.symm))
      have hτr : τ r ≠ 0 := fun h => hr (τ.injective (h.trans τ.map_zero.symm))
      have hnumS : (numeratorRingHom (τ (s : DiffOp K)) : PseudoDiffOp K) ≠ 0 :=
        fun h => hτs (numeratorRingHom_injective (h.trans (map_zero _).symm))
      have hnumR : (numeratorRingHom (τ r) : PseudoDiffOp K) ≠ 0 :=
        fun h => hτr (numeratorRingHom_injective (h.trans (map_zero _).symm))
      rw [mapPseudoRingHom, OreLocalization.universalHom_apply]
      change ordQ ((numeratorRingHom (τ (s : DiffOp K)))⁻¹ * numeratorRingHom (τ r)) =
        ordQ (r /ₒ s)
      rw [ordQ_mul _ _ (inv_ne_zero hnumS) hnumR, ordQ_inv _ hnumS,
        ordQ_numeratorRingHom, if_neg hτs, ordQ_numeratorRingHom, if_neg hτr,
        ordQ_oreDiv, if_neg hr]
      change -((degree (map (σ : K →+* K) (s : DiffOp K)) : ℕ) : ℤ) +
          (degree (map (σ : K →+* K) r) : ℤ) =
        (degree r : ℤ) - (degree (s : DiffOp K) : ℤ)
      rw [degree_map _ σ.injective, degree_map _ σ.injective]
      ring

/-- The extended action is an isometry for the additive valuation. -/
theorem pseudoDiffOpAddValuationValue_mapPseudoRingHom (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (x : PseudoDiffOp K) :
    pseudoDiffOpAddValuationValue (mapPseudoRingHom σ hσ x) =
      pseudoDiffOpAddValuationValue x := by
  classical
  letI : DecidableEq (PseudoDiffOp K) := Classical.decEq _
  by_cases hx : x = 0
  · subst x
    simp
  have hmap : mapPseudoRingHom σ hσ x ≠ 0 := by
    intro h
    have heq := congrArg (mapPseudoRingEquiv σ hσ).symm h
    exact hx (by simpa [mapPseudoRingEquiv] using heq)
  simp [pseudoDiffOpAddValuationValue, hx, hmap, ordQ_mapPseudoRingHom]

/-- A valuation-preserving equivalence of division rings is uniformly continuous for the valued
topologies.  This is the noncommutative form of the standard valued-field transport lemma. -/
theorem uniformContinuous_ringEquiv_of_valuation_eq
    {R S Γ₀ : Type*}
    [DivisionRing R] [DivisionRing S] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (w : Valuation S Γ₀) (e : R ≃+* S)
    (h : ∀ x, w (e x) = v x) :
    UniformContinuous (WithVal.congr v w e) := by
  refine uniformContinuous_of_continuousAt_zero (WithVal.congr v w e).toAddMonoidHom ?_
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero _ _).tendsto_iff
      (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  let δ := WithVal.valueGroupOrderIso₀ w γ.val
  obtain ⟨r, hr⟩ := restrict₀_surjective (.ofClass w) δ
  have hδ : δ ≠ 0 := by
    intro hzero
    have hγ : γ.val = 0 := by
      apply (WithVal.valueGroupOrderIso₀ w).injective
      change (WithVal.valueGroupOrderIso₀ w) γ.val = 0 at hzero
      exact hzero
    exact Units.ne_zero γ hγ
  have hwr : w.restrict r ≠ 0 := by
    change (ValueGroup₀.restrict₀ (.ofClass w)) r ≠ 0
    rw [hr]
    exact hδ
  have hvr : v.restrict (e.symm r) ≠ 0 := by
    intro hzero
    apply hwr
    change (ValueGroup₀.restrict₀ (.ofClass v)) (e.symm r) = 0 at hzero
    change (ValueGroup₀.restrict₀ (.ofClass w)) r = 0
    rw [ValueGroup₀.restrict₀_eq_zero_iff] at hzero ⊢
    calc
      w r = w (e (e.symm r)) := by rw [e.apply_symm_apply]
      _ = v (e.symm r) := h (e.symm r)
      _ = 0 := hzero
  refine ⟨Units.mk0 (Valued.v.restrict (WithVal.toVal v (e.symm r))) ?_, ?_⟩
  · intro hzero
    apply hvr
    have hzero' := congrArg (WithVal.valueGroupOrderIso₀ v) hzero
    change (WithVal.valueGroupOrderIso₀ v)
      ((WithVal.valuation v).restrict (WithVal.toVal v (e.symm r))) =
        (WithVal.valueGroupOrderIso₀ v) 0 at hzero'
    rw [WithVal.valueGroupOrderIso₀_restrict] at hzero'
    simpa using hzero'
  · intro x hx
    change Valued.v.restrict ((WithVal.congr v w e) x) < γ
    have hlt : WithVal.valueGroupOrderIso₀ w
        (Valued.v.restrict ((WithVal.congr v w e) x)) <
        WithVal.valueGroupOrderIso₀ w γ.val := by
      change (WithVal.valueGroupOrderIso₀ w)
        ((WithVal.valuation w).restrict ((WithVal.congr v w e) x)) <
          WithVal.valueGroupOrderIso₀ w γ.val
      rw [WithVal.valueGroupOrderIso₀_restrict]
      change w.restrict (e x.ofVal) < δ
      rw [← hr]
      change w.restrict (e x.ofVal) < w.restrict r
      rw [Valuation.restrict_lt_iff]
      calc
        w (e x.ofVal) = v x.ofVal := h _
        _ < v (e.symm r) := by
          rw [← Valuation.restrict_lt_iff]
          simp only [Set.mem_setOf_eq] at hx
          have hx' := (WithVal.strictMono_valueGroupOrderIso₀ v).lt_iff_lt.mpr hx
          change WithVal.valueGroupOrderIso₀ v ((WithVal.valuation v).restrict x) <
            WithVal.valueGroupOrderIso₀ v
              ((WithVal.valuation v).restrict (WithVal.toVal v (e.symm r))) at hx'
          simpa only [Units.val_mk0, WithVal.valueGroupOrderIso₀_restrict] using hx'
        _ = w (e (e.symm r)) := (h _).symm
        _ = w r := by rw [e.apply_symm_apply]
    exact (WithVal.strictMono_valueGroupOrderIso₀ w).lt_iff_lt.mp hlt

/-- The coefficient action is a uniform equivalence for the order-valued topology. -/
def mapPseudoUniformEquiv (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    WithVal (pseudoDiffOpValuation (K := K)) ≃ᵤ
      WithVal (pseudoDiffOpValuation (K := K)) where
  __ := WithVal.congr pseudoDiffOpValuation pseudoDiffOpValuation (mapPseudoRingEquiv σ hσ)
  uniformContinuous_toFun := uniformContinuous_ringEquiv_of_valuation_eq
    pseudoDiffOpValuation pseudoDiffOpValuation (mapPseudoRingEquiv σ hσ)
    (fun x => congrArg Multiplicative.toAdd
      (pseudoDiffOpAddValuationValue_mapPseudoRingHom σ hσ x))
  uniformContinuous_invFun := by
    change UniformContinuous
      (WithVal.congr pseudoDiffOpValuation pseudoDiffOpValuation
        (mapPseudoRingEquiv σ hσ).symm)
    exact uniformContinuous_ringEquiv_of_valuation_eq
      pseudoDiffOpValuation pseudoDiffOpValuation (mapPseudoRingEquiv σ hσ).symm
      (fun x => by
        change pseudoDiffOpValuation
            (mapPseudoRingHom σ.symm (symm_deriv_comm hσ) x) = pseudoDiffOpValuation x
        exact congrArg Multiplicative.toAdd
          (pseudoDiffOpAddValuationValue_mapPseudoRingHom σ.symm
            (symm_deriv_comm hσ) x))

/-- Canonical extension of a coefficient automorphism to the completed pseudodifferential ring. -/
def mapCompletedPseudoRingEquiv (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K :=
  UniformSpace.Completion.mapRingEquiv
    (WithVal.congr pseudoDiffOpValuation pseudoDiffOpValuation (mapPseudoRingEquiv σ hσ))
    (mapPseudoUniformEquiv σ hσ).continuous
    (mapPseudoUniformEquiv σ hσ).symm.continuous

@[simp] theorem mapCompletedPseudoRingEquiv_coe (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (x : WithVal (pseudoDiffOpValuation (K := K))) :
    mapCompletedPseudoRingEquiv σ hσ (x : CompletedPseudoDiffOp K) =
      (WithVal.congr pseudoDiffOpValuation pseudoDiffOpValuation
          (mapPseudoRingEquiv σ hσ) x :
        WithVal (pseudoDiffOpValuation (K := K))) := by
  rw [mapCompletedPseudoRingEquiv, UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (uniformContinuous_ringEquiv_of_valuation_eq
        pseudoDiffOpValuation pseudoDiffOpValuation (mapPseudoRingEquiv σ hσ)
        (fun y => congrArg Multiplicative.toAdd
          (pseudoDiffOpAddValuationValue_mapPseudoRingHom σ hσ y)))]

end

end DiffOp

end GaloisForLFunctions.HTGeometry
