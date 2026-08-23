import GaloisForLFunctions.HTGeometry.DifferentialAdjoinCoordinateScale
import GaloisForLFunctions.HTGeometry.TorusExpandingProtocolTail
import GaloisForLFunctions.HTGeometry.LogarithmicDerivativeFixedField
import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid

/-!
# Arbitrary-family multiplicative power quotients

For a freely differential multiplicative family, every positive power field is a purely
transcendental ordinary extension of the common logarithmic-derivative field.  Along any strictly
increasing divisibility sequence, these fields descend strictly and their exact infinite
intersection is the logarithmic residue.  Results are proved for arbitrary index types and under
the exact assumption that the constant field contains primitive roots of every positive order.

The embedded theorem removes an ambient-generation hypothesis by running the construction inside
the family's generated differential field and mapping it back to the ambient field.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u v

variable {F E : Type u} {ι : Type v} [Field F] [Field E] [Algebra F E]
  [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F]

/-- A field contains primitive roots of unity of every positive order. -/
def ContainsAllRootsOfUnity (F : Type u) [Field F] : Prop :=
  ∀ N : ℕ, 0 < N → ∃ ζ : F, IsPrimitiveRoot ζ N

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [Algebra F E] in
/-- Algebraically closed characteristic-zero fields contain roots of unity of every order. -/
theorem containsAllRootsOfUnity_of_isAlgClosed [IsAlgClosed F] :
    ContainsAllRootsOfUnity F := by
  intro N hN
  exact exists_primitiveRoot_of_isAlgClosed F hN

/-- The rational-function field `ℂ(z)` contains primitive roots of every positive order. -/
theorem ratFunc_containsAllRootsOfUnity : ContainsAllRootsOfUnity (RatFunc ℂ) := by
  intro N hN
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosed ℂ hN
  exact ⟨algebraMap ℂ (RatFunc ℂ) ζ,
    hζ.map_of_injective (algebraMap ℂ (RatFunc ℂ)).injective⟩

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F] [Algebra F E] in
/-- Expanding scalar protocols separate characters under the exact roots-of-unity hypothesis. -/
theorem scalarProtocol_separates_of_containsAllRootsOfUnity
    (hroots : ContainsAllRootsOfUnity F)
    {r : ℕ} [TopologicalSpace (Fin r → Fˣ)]
    [IsTopologicalGroup (Fin r → Fˣ)] [DiscreteTopology (Fin r → Fˣ)]
    {K : ℕ → ℕ} (hK : ∀ j, 2 ≤ K j) (i : ℕ) (e d : Fin r →₀ ℕ)
    (h : ∀ u ∈ erasedClosure (torusProtocolGroup F (scalarStepMatrix r K)) i,
      (∏ k, ((u k : F)) ^ e k) = ∏ k, ((u k : F)) ^ d k) :
    e = d := by
  classical
  ext k
  by_contra hk
  obtain ⟨n, hn⟩ := exists_scalarPrefixExponent_gt hK i (max (e k) (d k))
  set N : ℕ := scalarPrefixExponent K i n with hN
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hn
  obtain ⟨ζ, hζ⟩ := hroots N hNpos
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hNpos.ne'
  set u : Fin r → Fˣ := fun l ↦ if l = k then Units.mk0 ζ hζ0 else 1 with hu
  have hmemker : u ∈ (torusPowerHom F (fun _ : Fin r ↦ ((N : ℤ)))).ker := by
    rw [mem_ker_torusPowerHom_iff]
    intro l
    by_cases hl : l = k
    · apply Units.ext
      simp only [hu, if_pos hl, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_one]
      rw [zpow_natCast]
      exact hζ.pow_eq_one
    · simp [hu, if_neg hl]
  have hmem : u ∈ erasedClosure (torusProtocolGroup F (scalarStepMatrix r K)) i := by
    refine Subgroup.le_topologicalClosure _ ?_
    rw [mem_erasedSector_iff]
    refine ⟨n, ?_⟩
    rw [prefixHom_torusProtocolGroup, prefixMatrix_scalarStepMatrix,
      torusMonomialHom_diagonal]
    exact hmemker
  have hval := h u hmem
  have hprod : ∀ g : Fin r →₀ ℕ, (∏ l, ((u l : F)) ^ g l) = ζ ^ g k := by
    intro g
    rw [Finset.prod_eq_single k]
    · simp only [hu, if_pos rfl, Units.val_mk0]
    · intro l _ hlk
      simp only [hu, if_neg hlk, Units.val_one, one_pow]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  rw [hprod e, hprod d] at hval
  exact hk (hζ.pow_inj (lt_of_le_of_lt (le_max_left _ _) hn)
    (lt_of_le_of_lt (le_max_right _ _) hn) hval)

omit [Differential F] [CharZero F] in
theorem exists_global_root_extension_of_mem_powerProtocolErasedClosure
    {r : ℕ} [TopologicalSpace (Fin r → Fˣ)] [IsTopologicalGroup (Fin r → Fˣ)]
    [DiscreteTopology (Fin r → Fˣ)]
    (e : Fin r → ι) (he : Function.Injective e) (K : ℕ → ℕ)
    (v : Fin r → Fˣ)
    (hv : v ∈ erasedClosure (torusProtocolGroup F (scalarStepMatrix r K)) 0) :
    ∃ n : ℕ, ∃ U : ι → Fˣ,
      (∀ j, U (e j) = v j) ∧
      ∀ i, (U i : F) ^ scalarPrefixExponent K 0 n = 1 := by
  classical
  have hvSector : v ∈ erasedSector (torusProtocolGroup F (scalarStepMatrix r K)) 0 := by
    rw [erasedClosure_eq_of_isClosed _ _ (isClosed_discrete _)] at hv
    exact hv
  obtain ⟨n, hn⟩ :=
    (mem_erasedSector_iff (torusProtocolGroup F (scalarStepMatrix r K)) 0 v).mp hvSector
  let D : ℕ := scalarPrefixExponent K 0 n
  have hker : v ∈ (torusPowerHom F (fun _ : Fin r ↦ (D : ℤ))).ker := by
    rw [← torusMonomialHom_diagonal, ← prefixMatrix_scalarStepMatrix K 0 n,
      ← prefixHom_torusProtocolGroup]
    exact hn
  have hvUnits : ∀ j, (v j) ^ (D : ℤ) = 1 :=
    (mem_ker_torusPowerHom_iff _ _).mp hker
  have hvPow : ∀ j, (v j : F) ^ D = 1 := by
    intro j
    have h := congrArg Units.val (hvUnits j)
    simpa [zpow_natCast] using h
  let U : ι → Fˣ := fun i ↦
    if hi : i ∈ Set.range e then v (Classical.choose hi) else 1
  have hUe : ∀ j, U (e j) = v j := by
    intro j
    simp only [U, dif_pos (Set.mem_range_self j)]
    have hj : e (Classical.choose (Set.mem_range_self j)) = e j :=
      Classical.choose_spec (Set.mem_range_self j)
    exact congrArg v (he hj)
  refine ⟨n, U, hUe, ?_⟩
  intro i
  by_cases hi : i ∈ Set.range e
  · simp only [U, dif_pos hi]
    exact hvPow (Classical.choose hi)
  · change ((if h : i ∈ Set.range e then v (Classical.choose h) else 1 : Fˣ) : F) ^ D = 1
    rw [dif_neg hi]
    simp

theorem finiteSubpalette_powerProtocol_mem_internalVelocity
    {r : ℕ} [TopologicalSpace (Fin r → Fˣ)] [IsTopologicalGroup (Fin r → Fˣ)]
    [DiscreteTopology (Fin r → Fˣ)]
    (hconst : ∀ c : F, c′ = 0) (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (e : Fin r → ι) (he : Function.Injective e)
    (K : ℕ → ℕ) (hK : ∀ n, 2 ≤ K n)
    (z : differentialAdjoin F (Set.range (x ∘ e)))
    (hz : ∀ n : ℕ, z.1 ∈ differentialAdjoin F
      (Set.range fun i ↦ x i ^ scalarPrefixExponent K 0 n)) :
    z ∈ torusVelocityField F (differentialAdjoinGenerator (F := F) (x ∘ e)) := by
  classical
  let yL : Fin r → differentialAdjoin F (Set.range (x ∘ e)) :=
    differentialAdjoinGenerator (F := F) (x ∘ e)
  let S : Subgroup (Fin r → Fˣ) :=
    erasedClosure (torusProtocolGroup F (scalarStepMatrix r K)) 0
  have hsep : ∀ a b : Fin r →₀ ℕ,
      (∀ v ∈ S, (∏ i, ((v i : F)) ^ a i) = ∏ i, ((v i : F)) ^ b i) → a = b := by
    intro a b hab
    exact scalarProtocol_separates_of_containsAllRootsOfUnity hroots hK 0 a b hab
  have hzVelocity : z ∈ torusVelocityField F yL := by
    rw [← fixedField_torusScaleRep_eq_torusVelocityField
          (differentialIndependent_differentialAdjoinGenerator (x ∘ e) (hx.comp e he))
          (differentialAdjoin_range_differentialAdjoinGenerator_eq_top (x ∘ e))
          hconst S hsep,
      IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨v, hv, rfl⟩ := hσ
    obtain ⟨n, U, hUe, hUPow⟩ :=
      exists_global_root_extension_of_mem_powerProtocolErasedClosure e he K v hv
    let D : ℕ := scalarPrefixExponent K 0 n
    have hglobal : torusScaleEquiv hx hgen U z.1 = z.1 :=
      torusScaleEquiv_fixes_powAdjoin (F := F) (E := E) (x := x)
        hx hgen U D hUPow (hz n)
    change (torusScaleEquiv
      (differentialIndependent_differentialAdjoinGenerator (x ∘ e) (hx.comp e he))
      (differentialAdjoin_range_differentialAdjoinGenerator_eq_top (x ∘ e)) v) z = z
    exact torusScaleEquiv_subpalette_fixed_of_fixed
      (F := F) (E := E) (ι := ι) (k := Fin r) (x := x)
      hx hgen e he U v hUe z hglobal
  exact hzVelocity

theorem finiteSubpalette_powerProtocol_mem_globalLogDeriv
    {r : ℕ} [TopologicalSpace (Fin r → Fˣ)] [IsTopologicalGroup (Fin r → Fˣ)]
    [DiscreteTopology (Fin r → Fˣ)]
    (hconst : ∀ c : F, c′ = 0) (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (e : Fin r → ι) (he : Function.Injective e)
    (K : ℕ → ℕ) (hK : ∀ n, 2 ≤ K n)
    (z : differentialAdjoin F (Set.range (x ∘ e)))
    (hz : ∀ n : ℕ, z.1 ∈ differentialAdjoin F
      (Set.range fun i ↦ x i ^ scalarPrefixExponent K 0 n)) :
    z.1 ∈ differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i)) := by
  let yL : Fin r → differentialAdjoin F (Set.range (x ∘ e)) :=
    differentialAdjoinGenerator (F := F) (x ∘ e)
  have hzVelocity : z ∈ torusVelocityField F yL :=
    finiteSubpalette_powerProtocol_mem_internalVelocity
      (F := F) (E := E) hconst hroots x hx hgen e he K hK z hz
  let V : IntermediateField F E :=
    differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))
  let M : IntermediateField F (differentialAdjoin F (Set.range (x ∘ e))) :=
    V.comap (differentialAdjoin F (Set.range (x ∘ e))).val
  have hMclosed : DerivationClosed M := by
    intro w hw
    change Differential.deriv (w : E) ∈ V
    exact derivationClosed_differentialAdjoin F _ hw
  have hvelLe : torusVelocityField F yL ≤ M := by
    apply differentialAdjoin_le F
    · rintro w ⟨j, rfl⟩
      change Differential.logDeriv (x (e j)) ∈ V
      exact subset_differentialAdjoin F _ ⟨e j, rfl⟩
    · exact hMclosed
  exact hvelLe hzVelocity

theorem arbitraryFamily_powerProtocol_iInter_eq_logDeriv
    (hconst : ∀ c : F, c′ = 0) (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (K : ℕ → ℕ) (hK : ∀ n, 2 ≤ K n) :
    {z : E | ∀ n : ℕ,
        z ∈ differentialAdjoin F
          (Set.range fun i ↦ x i ^ scalarPrefixExponent K 0 n)} =
      (differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (x i)) : Set E) := by
  classical
  ext z
  constructor
  · intro hz
    have hzfull : z ∈ differentialAdjoin F (Set.range x) := by
      rw [hgen]
      exact IntermediateField.mem_top
    obtain ⟨C, hzC⟩ := mem_differentialAdjoin_range_exists_finset x hzfull
    let q : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
    let e : Fin (Fintype.card C) → ι := fun j ↦ (q.symm j).1
    have he : Function.Injective e := by
      intro i j hij
      apply q.symm.injective
      apply Subtype.ext
      exact hij
    have hy : DifferentialIndependent F (x ∘ e) := hx.comp e he
    have hrange : Set.range (x ∘ e) = x '' (C : Set ι) := by
      ext w
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, (q.symm j).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨q ⟨i, hi⟩, ?_⟩
        change x (e (q ⟨i, hi⟩)) = x i
        congr 1
        exact congrArg Subtype.val (q.symm_apply_apply ⟨i, hi⟩)
    have hzY : z ∈ differentialAdjoin F (Set.range (x ∘ e)) := by
      rw [hrange]
      exact hzC
    let zL : differentialAdjoin F (Set.range (x ∘ e)) := ⟨z, hzY⟩
    letI : TopologicalSpace (Fin (Fintype.card C) → Fˣ) := ⊥
    haveI : DiscreteTopology (Fin (Fintype.card C) → Fˣ) := ⟨rfl⟩
    haveI : IsTopologicalGroup (Fin (Fintype.card C) → Fˣ) := inferInstance
    exact finiteSubpalette_powerProtocol_mem_globalLogDeriv
      (F := F) (E := E) hconst hroots x hx hgen e he K hK zL hz
  · intro hz n
    apply differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _) hz
    rintro w ⟨i, rfl⟩
    have hx0 : x i ≠ 0 := by
      intro hxi
      exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
        (hxi ▸ isAlgebraic_zero)
    have hD : scalarPrefixExponent K 0 n ≠ 0 := by
      exact Nat.ne_of_gt (lt_of_lt_of_le (pow_pos (by omega : 0 < (2 : ℕ)) n)
        (two_pow_le_scalarPrefixExponent hK 0 n))
    have hsingle := logDeriv_mem_powAdjoin (F := F) hx0 hD
    exact (differentialAdjoin_mono (F := F)
      (s := ({x i ^ scalarPrefixExponent K 0 n} : Set E))
      (t := Set.range fun j ↦ x j ^ scalarPrefixExponent K 0 n)
      (by rintro v rfl; exact ⟨i, rfl⟩)) hsingle

/-- Quotients which turn a strictly increasing divisibility sequence into its scalar protocol. -/
def strictDivisibilitySteps (D : ℕ → ℕ) : ℕ → ℕ
  | 0 => D 0
  | n + 1 => D (n + 1) / D n

theorem strictDivisibilitySteps_two_le {D : ℕ → ℕ}
    (hD0 : 2 ≤ D 0) (hdiv : ∀ n, D n ∣ D (n + 1))
    (hlt : ∀ n, D n < D (n + 1)) :
    ∀ n, 2 ≤ strictDivisibilitySteps D n := by
  have hpos : ∀ n, 0 < D n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => exact lt_trans ih (hlt n)
  intro n
  cases n with
  | zero => exact hD0
  | succ n =>
      obtain ⟨q, hq⟩ := hdiv n
      have hquot : D (n + 1) / D n = q := by
        rw [hq, Nat.mul_comm, Nat.mul_div_left _ (hpos n)]
      rw [strictDivisibilitySteps, hquot]
      by_contra hq2
      have hqle : q ≤ 1 := by omega
      have hq0 : q ≠ 0 := by
        intro hqz
        have hz : D (n + 1) = 0 := by simpa [hqz] using hq
        exact (Nat.ne_of_gt (hpos (n + 1))) hz
      have hq1 : q ≠ 1 := by
        intro hqo
        have heq : D (n + 1) = D n := by simpa [hqo] using hq
        exact (Nat.ne_of_gt (hlt n)) heq
      omega

theorem scalarPrefixExponent_succ_last (K : ℕ → ℕ) (i n : ℕ) :
    scalarPrefixExponent K i (n + 1) =
      scalarPrefixExponent K i n * K (i + n) := by
  simp [scalarPrefixExponent, Finset.prod_range_succ]

theorem scalarPrefixExponent_strictDivisibilitySteps
    {D : ℕ → ℕ} (hdiv : ∀ n, D n ∣ D (n + 1)) (n : ℕ) :
    scalarPrefixExponent (strictDivisibilitySteps D) 0 (n + 1) = D n := by
  induction n with
  | zero => simp [scalarPrefixExponent, strictDivisibilitySteps]
  | succ n ih =>
      rw [scalarPrefixExponent_succ_last, ih]
      simpa [strictDivisibilitySteps] using Nat.mul_div_cancel' (hdiv n)

theorem arbitraryFamily_strictDivisibility_iInter_eq_logDeriv
    (hconst : ∀ c : F, c′ = 0) (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    {z : E | ∀ n : ℕ,
        z ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ D n)} =
      (differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (x i)) : Set E) := by
  let K := strictDivisibilitySteps D
  have hK : ∀ n, 2 ≤ K n := strictDivisibilitySteps_two_le hD0 hdiv hlt
  rw [← arbitraryFamily_powerProtocol_iInter_eq_logDeriv hconst hroots x hx hgen K hK]
  ext z
  constructor
  · intro hz n
    cases n with
    | zero =>
        simp only [scalarPrefixExponent_zero, pow_one]
        rw [hgen]
        exact IntermediateField.mem_top
    | succ n =>
        rw [scalarPrefixExponent_strictDivisibilitySteps hdiv n]
        exact hz n
  · intro hz n
    simpa only [K, scalarPrefixExponent_strictDivisibilitySteps hdiv n] using hz (n + 1)

omit [CharZero E] [CharZero F] in
/-- Canonical inclusion maps an internally generated power field to the corresponding embedded
power field. -/
theorem map_differentialAdjoin_generator_pow
    (x : ι → E) (N : ℕ) :
    IntermediateField.map (differentialAdjoin F (Set.range x)).val
        (differentialAdjoin F
          (Set.range fun i ↦ (differentialAdjoinGenerator (F := F) x i) ^ N)) =
      differentialAdjoin F (Set.range fun i ↦ x i ^ N) := by
  rw [map_differentialAdjoin_algHom _ (fun _ ↦ rfl)]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(differentialAdjoinGenerator (F := F) x i) ^ N, ⟨i, rfl⟩, by simp⟩

omit [CharZero E] [CharZero F] in
/-- Canonical inclusion maps the internal logarithmic-residue field to the corresponding embedded
residue field. -/
theorem map_differentialAdjoin_generator_logDeriv
    (x : ι → E) :
    IntermediateField.map (differentialAdjoin F (Set.range x)).val
        (differentialAdjoin F
          (Set.range fun i ↦ Differential.logDeriv
            (differentialAdjoinGenerator (F := F) x i))) =
      differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i)) := by
  rw [map_differentialAdjoin_algHom _ (fun _ ↦ rfl)]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Differential.logDeriv (differentialAdjoinGenerator (F := F) x i),
      ⟨i, rfl⟩, by rfl⟩

omit [CharZero E] in
/-- Embedded form of the arbitrary-family intersection theorem.  No ambient-generation hypothesis
is needed: the proof runs internally in the differential field generated by the family and maps
the exact result back to the ambient field. -/
theorem arbitraryFamily_strictDivisibility_iInter_eq_logDeriv_embedded
    (hconst : ∀ c : F, c′ = 0) (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    {z : E | ∀ n : ℕ,
        z ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ D n)} =
      (differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (x i)) : Set E) := by
  classical
  let M : IntermediateField F E := differentialAdjoin F (Set.range x)
  let y : ι → M := differentialAdjoinGenerator (F := F) x
  have hy : DifferentialIndependent F y :=
    differentialIndependent_differentialAdjoinGenerator x hx
  have hytop : differentialAdjoin F (Set.range y) = ⊤ :=
    differentialAdjoin_range_differentialAdjoinGenerator_eq_top x
  have hint := arbitraryFamily_strictDivisibility_iInter_eq_logDeriv
    (F := F) (E := M) hconst hroots y hy hytop D hD0 hdiv hlt
  ext z
  constructor
  · intro hz
    have hzM : z ∈ M := by
      have hle : differentialAdjoin F (Set.range fun i ↦ x i ^ D 0) ≤ M := by
        apply differentialAdjoin_le F
        · rintro w ⟨i, rfl⟩
          exact pow_mem (subset_differentialAdjoin F _ (Set.mem_range_self i)) (D 0)
        · exact derivationClosed_differentialAdjoin F _
      exact hle (hz 0)
    let zM : M := ⟨z, hzM⟩
    have hzInternal : ∀ n,
        zM ∈ differentialAdjoin F (Set.range fun i ↦ y i ^ D n) := by
      intro n
      have hzMap : z ∈ IntermediateField.map M.val
          (differentialAdjoin F (Set.range fun i ↦ y i ^ D n)) := by
        rw [map_differentialAdjoin_generator_pow (F := F) x (D n)]
        exact hz n
      obtain ⟨w, hw, hwz⟩ := hzMap
      have hw_eq : w = zM := Subtype.ext hwz
      simpa [hw_eq] using hw
    have hzResidueInternal : zM ∈ differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (y i)) := by
      have hzSet : zM ∈ {w : M | ∀ n,
          w ∈ differentialAdjoin F (Set.range fun i ↦ y i ^ D n)} := hzInternal
      rw [hint] at hzSet
      exact hzSet
    have hzMap : z ∈ IntermediateField.map M.val
        (differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (y i))) :=
      ⟨zM, hzResidueInternal, rfl⟩
    rw [map_differentialAdjoin_generator_logDeriv (F := F) x] at hzMap
    exact hzMap
  · intro hz n
    apply differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _) hz
    rintro w ⟨i, rfl⟩
    have hxi : x i ≠ 0 := by
      intro h
      exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
        (h ▸ isAlgebraic_zero)
    have hDn : D n ≠ 0 := by
      have hpos : 0 < D n := by
        induction n with
        | zero => omega
        | succ n ih => exact lt_trans ih (hlt n)
      omega
    have hsingle := logDeriv_mem_powAdjoin (F := F) hxi hDn
    exact (differentialAdjoin_mono (F := F)
      (s := ({x i ^ D n} : Set E)) (t := Set.range fun j ↦ x j ^ D n)
      (by rintro v rfl; exact Set.mem_range_self i)) hsingle

omit [CharZero F] in
/-- The logarithmic residue retains the full arbitrary-family differential rank. -/
theorem arbitraryFamily_logDeriv_differentialIndependent
    (x : ι → E) (hx : DifferentialIndependent F x) :
    DifferentialIndependent F (fun i ↦ Differential.logDeriv (x i)) := by
  exact (differentialIndependent_deriv_div_self_iff (F := F) x).mp hx

omit [CharZero F] in
/-- Ordinary field obtained from the logarithmic residue by adjoining one common power of every
coordinate. -/
def powerFamilyOrdinaryExtension (F : Type u) [Field F] [Algebra F E]
    (x : ι → E) (N : ℕ) : IntermediateField F E :=
  IntermediateField.adjoin F
    (((differentialAdjoin F
      (Set.range fun i ↦ Differential.logDeriv (x i)) : IntermediateField F E) : Set E) ∪
      Set.range fun i ↦ x i ^ N)

/-- A root of unity in a characteristic-zero differential field is a differential constant. -/
theorem deriv_eq_zero_of_pow_eq_one
    {c : F} {N : ℕ} (hN : 0 < N) (hpow : c ^ N = 1) : c′ = 0 := by
  have hderiv : (c ^ N)′ = 0 := by
    rw [hpow, Differential.deriv.map_one_eq_zero]
  rw [Derivation.leibniz_pow] at hderiv
  simp only [nsmul_eq_mul, smul_eq_mul] at hderiv
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, zero_pow hN.ne'] at hpow
    exact zero_ne_one hpow
  rcases mul_eq_zero.mp hderiv with h | h
  · exact (hN0 h).elim
  · rcases mul_eq_zero.mp h with h | h
    · exact ((pow_ne_zero _ hc0) h).elim
    · exact h

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F] [Algebra F E] in
/-- Coordinate scalings whose every component has finite multiplicative order. -/
def torsionCoordinateScales (F : Type u) [Field F] (ι : Type v) : Subgroup (ι → Fˣ) where
  carrier := {u | ∀ i, IsOfFinOrder (u i)}
  one_mem' := fun _ ↦ isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by omega, one_pow 1⟩
  mul_mem' hu hv i := (hu i).mul (hv i)
  inv_mem' hu i := (hu i).inv

omit [Differential E] [DifferentialAlgebra F E] [CharZero E] [Algebra F E] in
/-- Every component of a torsion coordinate scaling is a differential constant. -/
theorem torsionCoordinateScale_deriv_eq_zero
    (u : torsionCoordinateScales F ι) (i : ι) : ((u.1 i : F))′ = 0 := by
  obtain ⟨N, hN, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (u.2 i)
  have hpow' : (u.1 i : F) ^ N = 1 := by
    have h := congrArg Units.val hpow
    simpa using h
  exact deriv_eq_zero_of_pow_eq_one hN hpow'

omit [CharZero E] [CharZero F] in
/-- Coordinate scaling fixes each logarithmic derivative in an arbitrary family. -/
theorem torusScaleEquiv_logDeriv_family
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : ι → Fˣ) (huconst : ∀ i, ((u i : F))′ = 0) (i : ι) :
    torusScaleEquiv hx hgen u (Differential.logDeriv (x i)) =
      Differential.logDeriv (x i) := by
  have hx0 : x i ≠ 0 := by
    intro hxi
    exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
      (hxi ▸ isAlgebraic_zero)
  have hc0 : algebraMap F E (u i : F) ≠ 0 := by
    simp only [ne_eq, map_eq_zero]
    exact (u i).ne_zero
  have hcderiv : Differential.logDeriv (algebraMap F E (u i : F)) = 0 := by
    rw [Differential.logDeriv, deriv_algebraMap, huconst, map_zero, zero_div]
  have hmap : torusScaleEquiv hx hgen u (Differential.logDeriv (x i)) =
      Differential.logDeriv (torusScaleEquiv hx hgen u (x i)) := by
    rw [Differential.logDeriv, Differential.logDeriv, map_div₀, torusScaleEquiv_deriv]
  rw [hmap, torusScaleEquiv_apply,
    Differential.logDeriv_mul _ _ hc0 hx0, hcderiv, zero_add]

omit [CharZero E] [CharZero F] in
/-- Coordinate scaling fixes the full logarithmic-residue field of an arbitrary family. -/
theorem torusScaleEquiv_fixes_logDerivAdjoin
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : ι → Fˣ) (huconst : ∀ i, ((u i : F))′ = 0) {z : E}
    (hz : z ∈ differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))) :
    torusScaleEquiv hx hgen u z = z := by
  let σ := torusScaleEquiv hx hgen u
  rw [differentialAdjoin] at hz
  apply IntermediateField.adjoin_induction F
    (s := differentialJetSet (Set.range fun i ↦ Differential.logDeriv (x i)))
    (p := fun w _ ↦ σ w = w)
  · rintro w ⟨v, ⟨i, rfl⟩, n, rfl⟩
    induction n with
    | zero =>
        simp only [differentialJet_zero]
        exact torusScaleEquiv_logDeriv_family x hx hgen u huconst i
    | succ n ih =>
        rw [differentialJet_succ]
        change torusScaleEquiv hx hgen u (differentialJet n (Differential.logDeriv (x i)))′ = _
        rw [torusScaleEquiv_deriv, ih]
  · intro c
    exact σ.commutes c
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]
  · exact hz

omit [CharZero E] in
/-- Coordinate scaling as an automorphism over the arbitrary-family logarithmic-residue field. -/
def torusScaleEquivLogDerivFamily
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (u : ι → Fˣ) (huconst : ∀ i, ((u i : F))′ = 0) :
    E ≃ₐ[↥(differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i)))] E where
  toRingEquiv := (torusScaleEquiv hx hgen u).toRingEquiv
  commutes' z := torusScaleEquiv_fixes_logDerivAdjoin x hx hgen u huconst z.2

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F] in
/-- Monomial character of an arbitrary coordinate torus. -/
def torusFamilyMonomialCharacter (F E : Type u) [Field F] [Field E] [Algebra F E]
    (N : ℕ) (e : ι →₀ ℕ) : (ι → Fˣ) →* E where
  toFun u := ∏ i ∈ e.support, (algebraMap F E (u i : F)) ^ (N * e i)
  map_one' := by simp
  map_mul' u v := by
    simp only [Pi.mul_apply, Units.val_mul, map_mul, mul_pow, Finset.prod_mul_distrib]

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F] in
theorem torusFamilyMonomialCharacter_apply (N : ℕ) (e : ι →₀ ℕ) (u : ι → Fˣ) :
    torusFamilyMonomialCharacter F E N e u =
      ∏ i ∈ e.support, (algebraMap F E (u i : F)) ^ (N * e i) := rfl

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  in
/-- Distinct exponent vectors define distinct characters of an arbitrary coordinate torus. -/
theorem torusFamilyMonomialCharacter_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (torusFamilyMonomialCharacter F E (ι := ι) N) := by
  classical
  intro e f hef
  ext j
  have htwo : (2 : F) ≠ 0 := two_ne_zero
  let u : ι → Fˣ := fun i ↦ if i = j then Units.mk0 (2 : F) htwo else 1
  have hval := congrFun
    (congrArg (fun g : (ι → Fˣ) →* E ↦ (g : (ι → Fˣ) → E)) hef) u
  have hprod : ∀ g : ι →₀ ℕ,
      (∏ i ∈ g.support, (algebraMap F E (u i : F)) ^ (N * g i)) =
        (2 : E) ^ (N * g j) := by
    intro g
    by_cases hj : j ∈ g.support
    · rw [Finset.prod_eq_single j]
      · simp [u, map_ofNat]
      · intro i hi hij
        simp [u, hij]
      · exact fun h ↦ (h hj).elim
    · have hgj : g j = 0 := Finsupp.notMem_support_iff.mp hj
      rw [Finset.prod_eq_one]
      · simp [hgj]
      · intro i hi
        have hij : i ≠ j := by
          intro hij
          exact hj (hij ▸ hi)
        simp [u, hij]
  change (∏ i ∈ e.support, (algebraMap F E (u i : F)) ^ (N * e i)) =
    (∏ i ∈ f.support, (algebraMap F E (u i : F)) ^ (N * f i)) at hval
  rw [hprod e, hprod f] at hval
  have hcast : ((2 ^ (N * e j) : ℕ) : E) = ((2 ^ (N * f j) : ℕ) : E) := by
    push_cast
    exact hval
  have hnat : (2 : ℕ) ^ (N * e j) = 2 ^ (N * f j) := Nat.cast_injective hcast
  have hmul : N * e j = N * f j := Nat.pow_right_injective (le_refl 2) hnat
  exact Nat.mul_left_cancel hN hmul

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F] in
/-- Restriction of a monomial character to coordinatewise torsion scalings. -/
def torsionTorusFamilyMonomialCharacter
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    (N : ℕ) (e : ι →₀ ℕ) : torsionCoordinateScales F ι →* E :=
  (torusFamilyMonomialCharacter F E N e).comp (torsionCoordinateScales F ι).subtype

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F] in
theorem torsionTorusFamilyMonomialCharacter_apply
    (N : ℕ) (e : ι →₀ ℕ) (u : torsionCoordinateScales F ι) :
    torsionTorusFamilyMonomialCharacter F E N e u =
      ∏ i ∈ e.support, (algebraMap F E (u.1 i : F)) ^ (N * e i) := rfl

omit [Differential F] [Differential E] [DifferentialAlgebra F E]
  [CharZero E] [CharZero F] in
/-- Roots of every order make restricted torsion characters separate all exponent vectors. -/
theorem torsionTorusFamilyMonomialCharacter_injective
    (hroots : ContainsAllRootsOfUnity F) {N : ℕ} (hN : 0 < N) :
    Function.Injective (torsionTorusFamilyMonomialCharacter F E (ι := ι) N) := by
  classical
  intro e f hef
  ext j
  let Q : ℕ := max (N * e j) (N * f j) + 1
  have hQ : 0 < Q := by omega
  obtain ⟨ζ, hζ⟩ := hroots Q hQ
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hQ.ne'
  let uRaw : ι → Fˣ := fun i ↦ if i = j then Units.mk0 ζ hζ0 else 1
  have huTorsion : ∀ i, IsOfFinOrder (uRaw i) := by
    intro i
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨Q, hQ, ?_⟩
    apply Units.ext
    by_cases hi : i = j
    · simp [uRaw, hi, hζ.pow_eq_one]
    · simp [uRaw, hi]
  let u : torsionCoordinateScales F ι := ⟨uRaw, huTorsion⟩
  have hval := congrFun
    (congrArg (fun g : torsionCoordinateScales F ι →* E ↦
      (g : torsionCoordinateScales F ι → E)) hef) u
  have hprod : ∀ g : ι →₀ ℕ,
      (∏ i ∈ g.support, (algebraMap F E (uRaw i : F)) ^ (N * g i)) =
        (algebraMap F E ζ) ^ (N * g j) := by
    intro g
    by_cases hj : j ∈ g.support
    · rw [Finset.prod_eq_single j]
      · simp [uRaw]
      · intro i hi hij
        simp [uRaw, hij]
      · exact fun h ↦ (h hj).elim
    · have hgj : g j = 0 := Finsupp.notMem_support_iff.mp hj
      rw [Finset.prod_eq_one]
      · simp [hgj]
      · intro i hi
        have hij : i ≠ j := by
          intro hij
          exact hj (hij ▸ hi)
        simp [uRaw, hij]
  change torusFamilyMonomialCharacter F E N e uRaw =
    torusFamilyMonomialCharacter F E N f uRaw at hval
  rw [torusFamilyMonomialCharacter_apply, torusFamilyMonomialCharacter_apply,
    hprod e, hprod f] at hval
  have hζval : ζ ^ (N * e j) = ζ ^ (N * f j) := by
    apply (algebraMap F E).injective
    simpa only [map_pow] using hval
  have hmul : N * e j = N * f j := hζ.pow_inj (by dsimp [Q]; omega)
    (by dsimp [Q]; omega) hζval
  exact Nat.mul_left_cancel hN hmul

omit [CharZero E] in
/-- Every common positive power of an arbitrary freely differential family is algebraically
independent over its complete logarithmic-residue field. -/
theorem algebraicIndependent_pow_family_over_logDerivAdjoin
    (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    {N : ℕ} (hN : 0 < N) :
    AlgebraicIndependent
      (↥(differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))))
      (fun i ↦ x i ^ N) := by
  classical
  let L : IntermediateField F E :=
    differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))
  have hx0 : ∀ i, x i ^ N ≠ 0 := by
    intro i
    have hxi : x i ≠ 0 := by
      intro h
      exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
        (h ▸ isAlgebraic_zero)
    exact pow_ne_zero N hxi
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hpne
  have hzero : ∀ u : torsionCoordinateScales F ι,
      ∑ e ∈ p.support,
        ((algebraMap L E) (MvPolynomial.coeff e p) *
          ∏ i ∈ e.support, (x i ^ N) ^ e i) *
            torsionTorusFamilyMonomialCharacter F E N e u = 0 := by
    intro u
    have huconst : ∀ i, ((u.1 i : F))′ = 0 := torsionCoordinateScale_deriv_eq_zero u
    have hσ0 : (torusScaleEquivLogDerivFamily x hx hgen u.1 huconst).toAlgHom
        (MvPolynomial.aeval (fun i ↦ x i ^ N) p) = 0 := by
      rw [hp, map_zero]
    rw [MvPolynomial.comp_aeval_apply (fun i ↦ x i ^ N)
      (torusScaleEquivLogDerivFamily x hx hgen u.1 huconst).toAlgHom p] at hσ0
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq] at hσ0
    rw [← hσ0]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    have hfun : ∀ i : ι,
        ((torusScaleEquivLogDerivFamily x hx hgen u.1 huconst).toAlgHom (x i ^ N)) =
          (algebraMap F E (u.1 i : F)) ^ N * x i ^ N := by
      intro i
      change torusScaleEquiv hx hgen u.1 (x i ^ N) = _
      rw [map_pow, torusScaleEquiv_apply, mul_pow]
    have hexp : (∏ i ∈ e.support,
        ((torusScaleEquivLogDerivFamily x hx hgen u.1 huconst).toAlgHom (x i ^ N)) ^ e i) =
        (∏ i ∈ e.support, (algebraMap F E (u.1 i : F)) ^ (N * e i)) *
          ∏ i ∈ e.support, (x i ^ N) ^ e i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ by rw [hfun i, mul_pow, ← pow_mul]
    rw [hexp]
    rw [torsionTorusFamilyMonomialCharacter_apply]
    dsimp only [L]
    ring
  have hinj : Function.Injective
      (fun e : ↥(p.support : Finset (ι →₀ ℕ)) ↦
        torsionTorusFamilyMonomialCharacter F E N (e : ι →₀ ℕ)) :=
    fun e f hef ↦ Subtype.ext
      (torsionTorusFamilyMonomialCharacter_injective
        (F := F) (E := E) hroots hN hef)
  have hindep : LinearIndependent E
      (fun e : ↥(p.support : Finset (ι →₀ ℕ)) ↦
        ((torsionTorusFamilyMonomialCharacter F E N (e : ι →₀ ℕ) :
          torsionCoordinateScales F ι → E))) :=
    (linearIndependent_monoidHom (torsionCoordinateScales F ι) E).comp _ hinj
  have hsum : ∑ e : ↥(p.support : Finset (ι →₀ ℕ)),
      ((algebraMap L E) (MvPolynomial.coeff (e : ι →₀ ℕ) p) *
          ∏ i ∈ (e : ι →₀ ℕ).support, (x i ^ N) ^ ((e : ι →₀ ℕ) i)) •
        ((torsionTorusFamilyMonomialCharacter F E N (e : ι →₀ ℕ) :
          torsionCoordinateScales F ι → E)) = 0 := by
    funext u
    have hz := hzero u
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_coe_sort p.support
      (fun e ↦ ((algebraMap L E) (MvPolynomial.coeff e p) *
        ∏ i ∈ e.support, (x i ^ N) ^ e i) *
          torsionTorusFamilyMonomialCharacter F E N e u)] at hz
    exact hz
  have hcoeffs := (Fintype.linearIndependent_iff.mp hindep) _ hsum
  apply hpne
  ext e
  by_cases he : e ∈ p.support
  · have hzeroa := hcoeffs ⟨e, he⟩
    have hxe : (∏ i ∈ e.support, (x i ^ N) ^ e i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hx0 i)
    have hc : (algebraMap L E) (MvPolynomial.coeff e p) = 0 := by
      rcases mul_eq_zero.mp hzeroa with h | h
      · exact h
      · exact absurd h hxe
    have hcz : MvPolynomial.coeff e p = 0 :=
      (algebraMap L E).injective (by rw [hc, map_zero])
    simp [hcz]
  · simp [MvPolynomial.notMem_support_iff.mp he]

omit [CharZero E] in
/-- The unpowered family is the first rational-coordinate level over its logarithmic residue. -/
theorem algebraicIndependent_family_over_logDerivAdjoin
    (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤) :
    AlgebraicIndependent
      (↥(differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i)))) x := by
  simpa using algebraicIndependent_pow_family_over_logDerivAdjoin
    hroots x hx hgen (N := 1) (by omega)

omit [CharZero E] [CharZero F] in
/-- Adjoining an arbitrary multiplicative family to its logarithmic-residue field is derivation
closed. -/
theorem derivationClosed_adjoin_logDeriv_family
    (x : ι → E) (hx : DifferentialIndependent F x) :
    DerivationClosed (IntermediateField.adjoin
      (↥(differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))))
      (Set.range x)) := by
  let L : IntermediateField F E :=
    differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))
  letI : Differential ↥L :=
    derivationClosedDifferential L (derivationClosed_differentialAdjoin F _)
  letI : DifferentialAlgebra (↥L) E :=
    ⟨fun c ↦ derivationClosedDifferential_apply L
      (derivationClosed_differentialAdjoin F _) c⟩
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i h
    exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
      (h ▸ isAlgebraic_zero)
  refine derivationClosed_adjoin_range_of_deriv_mem x fun i ↦ ?_
  have hlog : Differential.logDeriv (x i) ∈ L :=
    subset_differentialAdjoin F _ (Set.mem_range_self i)
  have hsolve : (x i)′ = Differential.logDeriv (x i) * x i := by
    rw [Differential.logDeriv, div_mul_cancel₀ _ (hx0 i)]
  rw [hsolve]
  exact mul_mem (IntermediateField.algebraMap_mem _
      (⟨Differential.logDeriv (x i), hlog⟩ : ↥L))
    (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))

omit [CharZero E] [CharZero F] in
/-- A freely differential family generates its ambient field as an ordinary extension of its
logarithmic-residue field. -/
theorem adjoin_logDeriv_family_eq_top
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤) :
    IntermediateField.adjoin
      (↥(differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))))
      (Set.range x) = ⊤ := by
  let L : IntermediateField F E :=
    differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))
  let A : IntermediateField (↥L) E := IntermediateField.adjoin (↥L) (Set.range x)
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i h
    exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
      (h ▸ isAlgebraic_zero)
  have hle : differentialAdjoin F (Set.range x) ≤ A.restrictScalars F := by
    rw [differentialAdjoin, IntermediateField.adjoin_le_iff]
    rintro w ⟨v, ⟨i, rfl⟩, n, rfl⟩
    have hjet : differentialJet n (x i) ∈ differentialAdjoin F ({x i} : Set E) :=
      differentialJet_mem_differentialAdjoin F (Set.mem_singleton (x i)) n
    rw [differentialAdjoin_eq_logCurrentOrdinaryExtension (hx0 i)] at hjet
    unfold logCurrentOrdinaryExtension at hjet
    have hscalarLe : IntermediateField.adjoin F
        (((differentialAdjoin F ({Differential.logDeriv (x i)} : Set E) :
          IntermediateField F E) : Set E) ∪ {x i}) ≤ A.restrictScalars F := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro y hy
      rcases hy with hyLog | hyx
      · have hyL : y ∈ L := (differentialAdjoin_mono (F := F)
            (s := ({Differential.logDeriv (x i)} : Set E))
            (t := Set.range fun j ↦ Differential.logDeriv (x j))
            (by rintro q rfl; exact Set.mem_range_self i)) hyLog
        exact IntermediateField.algebraMap_mem A (⟨y, hyL⟩ : ↥L)
      · rw [Set.mem_singleton_iff.mp hyx]
        exact IntermediateField.subset_adjoin (↥L) (Set.range x)
          (Set.mem_range_self i)
    exact hscalarLe hjet
  rw [hgen] at hle
  have hres : A.restrictScalars F = ⊤ := top_le_iff.mp hle
  have htop : (⊤ : IntermediateField (↥L) E).restrictScalars F = ⊤ :=
    IntermediateField.restrictScalars_top
  exact IntermediateField.restrictScalars_injective F (hres.trans htop.symm)

/-- Finite-support invariant reduction using only torsion scalings.  This is the exact version for
a possibly nonconstant differential base field. -/
theorem finiteSubpalette_powerProtocol_mem_internalVelocity_of_roots
    {r : ℕ} [TopologicalSpace (Fin r → Fˣ)] [IsTopologicalGroup (Fin r → Fˣ)]
    [DiscreteTopology (Fin r → Fˣ)]
    (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (e : Fin r → ι) (he : Function.Injective e)
    (K : ℕ → ℕ) (hK : ∀ n, 2 ≤ K n)
    (z : differentialAdjoin F (Set.range (x ∘ e)))
    (hz : ∀ n : ℕ, z.1 ∈ differentialAdjoin F
      (Set.range fun i ↦ x i ^ scalarPrefixExponent K 0 n)) :
    z ∈ torusVelocityField F (differentialAdjoinGenerator (F := F) (x ∘ e)) := by
  classical
  let yL : Fin r → differentialAdjoin F (Set.range (x ∘ e)) :=
    differentialAdjoinGenerator (F := F) (x ∘ e)
  let S : Subgroup (Fin r → Fˣ) :=
    erasedClosure (torusProtocolGroup F (scalarStepMatrix r K)) 0
  have hy : DifferentialIndependent F yL :=
    differentialIndependent_differentialAdjoinGenerator (x ∘ e) (hx.comp e he)
  have hytop : differentialAdjoin F (Set.range yL) = ⊤ :=
    differentialAdjoin_range_differentialAdjoinGenerator_eq_top (x ∘ e)
  have hsep : ∀ a b : Fin r →₀ ℕ,
      (∀ v ∈ S, (∏ i, ((v i : F)) ^ a i) = ∏ i, ((v i : F)) ^ b i) → a = b := by
    intro a b hab
    exact scalarProtocol_separates_of_containsAllRootsOfUnity hroots hK 0 a b hab
  have hSconst : ∀ v ∈ S, ∀ j, ((v j : F))′ = 0 := by
    intro v hv j
    obtain ⟨n, U, hUe, hUPow⟩ :=
      exists_global_root_extension_of_mem_powerProtocolErasedClosure
        (ι := Fin r) (fun i ↦ i) Function.injective_id K v hv
    have hDpos : 0 < scalarPrefixExponent K 0 n :=
      lt_of_lt_of_le (pow_pos (by omega : 0 < (2 : ℕ)) n)
        (two_pow_le_scalarPrefixExponent hK 0 n)
    have hvPow : (v j : F) ^ scalarPrefixExponent K 0 n = 1 := by
      rw [← hUe j]
      exact hUPow j
    exact deriv_eq_zero_of_pow_eq_one hDpos hvPow
  let V : IntermediateField F (differentialAdjoin F (Set.range (x ∘ e))) :=
    differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (yL i))
  have hyAlg : AlgebraicIndependent (↥V) yL :=
    algebraicIndependent_family_over_logDerivAdjoin hroots yL hy hytop
  have hVtop : IntermediateField.adjoin (↥V) (Set.range yL) = ⊤ := by
    exact adjoin_logDeriv_family_eq_top yL hy hytop
  have hzV : z ∈ V := by
    apply mem_of_torusScale_invariant hy hytop V hyAlg
      (fun v hv w hw ↦
        torusScaleEquiv_fixes_logDerivAdjoin yL hy hytop v (hSconst v hv) hw)
      hsep
    · rw [hVtop]
      exact IntermediateField.mem_top
    · intro v hv
      obtain ⟨n, U, hUe, hUPow⟩ :=
        exists_global_root_extension_of_mem_powerProtocolErasedClosure e he K v hv
      have hglobal : torusScaleEquiv hx hgen U z.1 = z.1 :=
        torusScaleEquiv_fixes_powAdjoin (F := F) (E := E) (x := x)
          hx hgen U (scalarPrefixExponent K 0 n) hUPow (hz n)
      exact torusScaleEquiv_subpalette_fixed_of_fixed
        (F := F) (E := E) (ι := ι) (k := Fin r) (x := x)
        hx hgen e he U v hUe z hglobal
  simpa only [V, torusVelocityField] using hzV

/-- Arbitrary-family expanding-protocol intersection over a nonconstant differential base. -/
theorem arbitraryFamily_powerProtocol_iInter_eq_logDeriv_of_roots
    (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (K : ℕ → ℕ) (hK : ∀ n, 2 ≤ K n) :
    {z : E | ∀ n : ℕ,
        z ∈ differentialAdjoin F
          (Set.range fun i ↦ x i ^ scalarPrefixExponent K 0 n)} =
      (differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (x i)) : Set E) := by
  classical
  ext z
  constructor
  · intro hz
    have hzfull : z ∈ differentialAdjoin F (Set.range x) := by
      rw [hgen]
      exact IntermediateField.mem_top
    obtain ⟨C, hzC⟩ := mem_differentialAdjoin_range_exists_finset x hzfull
    let q : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
    let e : Fin (Fintype.card C) → ι := fun j ↦ (q.symm j).1
    have he : Function.Injective e := by
      intro i j hij
      apply q.symm.injective
      apply Subtype.ext
      exact hij
    have hrange : Set.range (x ∘ e) = x '' (C : Set ι) := by
      ext w
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, (q.symm j).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨q ⟨i, hi⟩, ?_⟩
        change x (e (q ⟨i, hi⟩)) = x i
        congr 1
        exact congrArg Subtype.val (q.symm_apply_apply ⟨i, hi⟩)
    have hzY : z ∈ differentialAdjoin F (Set.range (x ∘ e)) := by
      rw [hrange]
      exact hzC
    let zL : differentialAdjoin F (Set.range (x ∘ e)) := ⟨z, hzY⟩
    letI : TopologicalSpace (Fin (Fintype.card C) → Fˣ) := ⊥
    haveI : DiscreteTopology (Fin (Fintype.card C) → Fˣ) := ⟨rfl⟩
    haveI : IsTopologicalGroup (Fin (Fintype.card C) → Fˣ) := inferInstance
    have hzVelocity := finiteSubpalette_powerProtocol_mem_internalVelocity_of_roots
      (F := F) (E := E) hroots x hx hgen e he K hK zL hz
    let V : IntermediateField F E :=
      differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))
    let M : IntermediateField F (differentialAdjoin F (Set.range (x ∘ e))) :=
      V.comap (differentialAdjoin F (Set.range (x ∘ e))).val
    have hMclosed : DerivationClosed M := by
      intro w hw
      change Differential.deriv (w : E) ∈ V
      exact derivationClosed_differentialAdjoin F _ hw
    have hvelLe : torusVelocityField F
        (differentialAdjoinGenerator (F := F) (x ∘ e)) ≤ M := by
      apply differentialAdjoin_le F
      · rintro w ⟨j, rfl⟩
        change Differential.logDeriv (x (e j)) ∈ V
        exact subset_differentialAdjoin F _ ⟨e j, rfl⟩
      · exact hMclosed
    exact hvelLe hzVelocity
  · intro hz n
    apply differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _) hz
    rintro w ⟨i, rfl⟩
    have hxi : x i ≠ 0 := by
      intro h
      exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
        (h ▸ isAlgebraic_zero)
    have hD : scalarPrefixExponent K 0 n ≠ 0 :=
      Nat.ne_of_gt (lt_of_lt_of_le (pow_pos (by omega : 0 < (2 : ℕ)) n)
        (two_pow_le_scalarPrefixExponent hK 0 n))
    have hsingle := logDeriv_mem_powAdjoin (F := F) hxi hD
    exact (differentialAdjoin_mono (F := F)
      (s := ({x i ^ scalarPrefixExponent K 0 n} : Set E))
      (t := Set.range fun j ↦ x j ^ scalarPrefixExponent K 0 n)
      (by rintro v rfl; exact Set.mem_range_self i)) hsingle

/-- Exact strict-divisibility intersection over an arbitrary differential base. -/
theorem arbitraryFamily_strictDivisibility_iInter_eq_logDeriv_of_roots
    (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    {z : E | ∀ n : ℕ,
        z ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ D n)} =
      (differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (x i)) : Set E) := by
  let K := strictDivisibilitySteps D
  have hK : ∀ n, 2 ≤ K n := strictDivisibilitySteps_two_le hD0 hdiv hlt
  rw [← arbitraryFamily_powerProtocol_iInter_eq_logDeriv_of_roots
    hroots x hx hgen K hK]
  ext z
  constructor
  · intro hz n
    cases n with
    | zero =>
        simp only [scalarPrefixExponent_zero, pow_one]
        rw [hgen]
        exact IntermediateField.mem_top
    | succ n =>
        rw [scalarPrefixExponent_strictDivisibilitySteps hdiv n]
        exact hz n
  · intro hz n
    simpa only [K, scalarPrefixExponent_strictDivisibilitySteps hdiv n] using hz (n + 1)

omit [CharZero E] in
/-- Embedded exact intersection over a possibly nonconstant differential base. -/
theorem arbitraryFamily_strictDivisibility_iInter_eq_logDeriv_embedded_of_roots
    (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    {z : E | ∀ n : ℕ,
        z ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ D n)} =
      (differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (x i)) : Set E) := by
  classical
  let M : IntermediateField F E := differentialAdjoin F (Set.range x)
  let y : ι → M := differentialAdjoinGenerator (F := F) x
  have hy : DifferentialIndependent F y :=
    differentialIndependent_differentialAdjoinGenerator x hx
  have hytop : differentialAdjoin F (Set.range y) = ⊤ :=
    differentialAdjoin_range_differentialAdjoinGenerator_eq_top x
  have hint := arbitraryFamily_strictDivisibility_iInter_eq_logDeriv_of_roots
    (F := F) (E := M) hroots y hy hytop D hD0 hdiv hlt
  ext z
  constructor
  · intro hz
    have hzM : z ∈ M := by
      have hle : differentialAdjoin F (Set.range fun i ↦ x i ^ D 0) ≤ M := by
        apply differentialAdjoin_le F
        · rintro w ⟨i, rfl⟩
          exact pow_mem (subset_differentialAdjoin F _ (Set.mem_range_self i)) (D 0)
        · exact derivationClosed_differentialAdjoin F _
      exact hle (hz 0)
    let zM : M := ⟨z, hzM⟩
    have hzInternal : ∀ n,
        zM ∈ differentialAdjoin F (Set.range fun i ↦ y i ^ D n) := by
      intro n
      have hzMap : z ∈ IntermediateField.map M.val
          (differentialAdjoin F (Set.range fun i ↦ y i ^ D n)) := by
        rw [map_differentialAdjoin_generator_pow (F := F) x (D n)]
        exact hz n
      obtain ⟨w, hw, hwz⟩ := hzMap
      have hw_eq : w = zM := Subtype.ext hwz
      simpa [hw_eq] using hw
    have hzResidueInternal : zM ∈ differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (y i)) := by
      have hzSet : zM ∈ {w : M | ∀ n,
          w ∈ differentialAdjoin F (Set.range fun i ↦ y i ^ D n)} := hzInternal
      rw [hint] at hzSet
      exact hzSet
    have hzMap : z ∈ IntermediateField.map M.val
        (differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (y i))) :=
      ⟨zM, hzResidueInternal, rfl⟩
    rw [map_differentialAdjoin_generator_logDeriv (F := F) x] at hzMap
    exact hzMap
  · intro hz n
    apply differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _) hz
    rintro w ⟨i, rfl⟩
    have hxi : x i ≠ 0 := by
      intro h
      exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
        (h ▸ isAlgebraic_zero)
    have hDn : D n ≠ 0 := by
      have hpos : 0 < D n := by
        induction n with
        | zero => omega
        | succ n ih => exact lt_trans ih (hlt n)
      omega
    have hsingle := logDeriv_mem_powAdjoin (F := F) hxi hDn
    exact (differentialAdjoin_mono (F := F)
      (s := ({x i ^ D n} : Set E)) (t := Set.range fun j ↦ x j ^ D n)
      (by rintro v rfl; exact Set.mem_range_self i)) hsingle

omit [CharZero E] in
/-- Every positive power field is exactly an ordinary extension of the common logarithmic
residue field by the powered coordinates. -/
theorem differentialAdjoin_range_pow_eq_powerFamilyOrdinaryExtension
    (x : ι → E) (hx : DifferentialIndependent F x)
    {N : ℕ} (hN : 0 < N) :
    differentialAdjoin F (Set.range fun i ↦ x i ^ N) =
      powerFamilyOrdinaryExtension F x N := by
  classical
  let L : IntermediateField F E :=
    differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))
  let T : IntermediateField F E :=
    differentialAdjoin F (Set.range fun i ↦ x i ^ N)
  let A : IntermediateField F E := powerFamilyOrdinaryExtension F x N
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i hxi
    exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i)
      (hxi ▸ isAlgebraic_zero)
  have hpowT : ∀ i, x i ^ N ∈ T := fun i ↦
    subset_differentialAdjoin F _ (Set.mem_range_self i)
  have hlogT : ∀ i, Differential.logDeriv (x i) ∈ T := by
    intro i
    have hsingle := logDeriv_mem_powAdjoin (F := F) (hx0 i) (Nat.ne_of_gt hN)
    exact (differentialAdjoin_mono (F := F)
      (s := ({x i ^ N} : Set E)) (t := Set.range fun j ↦ x j ^ N)
      (by rintro v rfl; exact Set.mem_range_self i)) hsingle
  have hLleT : L ≤ T :=
    differentialAdjoin_le F (by rintro w ⟨i, rfl⟩; exact hlogT i)
      (derivationClosed_differentialAdjoin F _)
  have hAleT : A ≤ T := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    rcases hy with hyL | ⟨i, rfl⟩
    · exact hLleT hyL
    · exact hpowT i
  have hAclosed : DerivationClosed A := by
    intro y hy
    apply IntermediateField.adjoin_induction F
      (s := ((L : Set E) ∪ Set.range fun i ↦ x i ^ N))
      (p := fun w _ ↦ w′ ∈ A)
    · intro w hw
      rcases hw with hwL | ⟨i, rfl⟩
      · have hw' : w′ ∈ L := derivationClosed_differentialAdjoin F _ hwL
        exact IntermediateField.subset_adjoin F _ (Set.mem_union_left _ hw')
      · have hlogA : Differential.logDeriv (x i) ∈ A :=
          IntermediateField.subset_adjoin F _
            (Set.mem_union_left _ (subset_differentialAdjoin F _ (Set.mem_range_self i)))
        have hnatA : (N : E) ∈ A := by
          rw [← map_natCast (algebraMap F E) N]
          exact A.algebraMap_mem (N : F)
        have hpowA : x i ^ N ∈ A :=
          IntermediateField.subset_adjoin F _
            (Set.mem_union_right _ (Set.mem_range_self i))
        have hderiv : (x i ^ N)′ =
            ((N : E) * Differential.logDeriv (x i)) * x i ^ N := by
          calc
            (x i ^ N)′ = Differential.logDeriv (x i ^ N) * x i ^ N := by
              rw [Differential.logDeriv, div_mul_cancel₀ _ (pow_ne_zero N (hx0 i))]
            _ = ((N : E) * Differential.logDeriv (x i)) * x i ^ N := by
              rw [differential_logDeriv_pow (x i) (hx0 i) N]
        rw [hderiv]
        exact A.mul_mem (A.mul_mem hnatA hlogA) hpowA
    · intro c
      rw [deriv_algebraMap]
      exact A.algebraMap_mem _
    · intro a b ha hb hda hdb
      rw [map_add]
      exact A.add_mem hda hdb
    · intro a ha hda
      rw [Derivation.leibniz_inv]
      have hsq : a⁻¹ ^ (2 : ℕ) ∈ A := by
        simpa [pow_two] using A.mul_mem (A.inv_mem ha) (A.inv_mem ha)
      exact A.mul_mem (A.neg_mem hsq) hda
    · intro a b ha hb hda hdb
      rw [Derivation.leibniz]
      exact A.add_mem (A.mul_mem ha hdb) (A.mul_mem hb hda)
    · exact hy
  have hTleA : T ≤ A := by
    apply differentialAdjoin_le F
    · rintro w ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin F _
        (Set.mem_union_right _ (Set.mem_range_self i))
    · exact hAclosed
  exact le_antisymm hTleA hAleT

omit [CharZero E] [CharZero F] in
theorem differentialAdjoin_range_pow_le_of_dvd
    (x : ι → E) {d N : ℕ} (hdvd : d ∣ N) :
    differentialAdjoin F (Set.range fun i ↦ x i ^ N) ≤
      differentialAdjoin F (Set.range fun i ↦ x i ^ d) := by
  obtain ⟨c, rfl⟩ := hdvd
  apply differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
  rintro w ⟨i, rfl⟩
  change x i ^ (d * c) ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ d)
  rw [pow_mul]
  exact pow_mem (subset_differentialAdjoin F _ (Set.mem_range_self i)) c

omit [CharZero F] in
theorem differentialAdjoin_range_pow_lt_of_dvd_of_lt
    [Nonempty ι] (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (hroots : ContainsAllRootsOfUnity F)
    {d N : ℕ} (hd : 0 < d) (hdvd : d ∣ N) (hdN : d < N) :
    differentialAdjoin F (Set.range fun i ↦ x i ^ N) <
      differentialAdjoin F (Set.range fun i ↦ x i ^ d) := by
  classical
  have hle := differentialAdjoin_range_pow_le_of_dvd (F := F) x hdvd
  refine lt_of_le_of_ne hle ?_
  intro heq
  let i₀ : ι := Classical.choice inferInstance
  have hx0 : x i₀ ≠ 0 := by
    intro hxi
    exact ((algebraicIndependent_of_differentialIndependent hx).transcendental i₀)
      (hxi ▸ isAlgebraic_zero)
  have hmemd : x i₀ ^ d ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ d) :=
    subset_differentialAdjoin F _ (Set.mem_range_self i₀)
  have hmemN : x i₀ ^ d ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ N) := by
    rw [heq]
    exact hmemd
  have hN : 0 < N := lt_trans hd hdN
  obtain ⟨ζ, hζ⟩ := hroots N hN
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  let u : ι → Fˣ := fun i ↦ if i = i₀ then Units.mk0 ζ hζ0 else 1
  have hroot : ∀ i, (u i : F) ^ N = 1 := by
    intro i
    by_cases hi : i = i₀
    · simp [u, hi, hζ.pow_eq_one]
    · simp [u, hi]
  have hfix : torusScaleEquiv hx hgen u (x i₀ ^ d) = x i₀ ^ d :=
    torusScaleEquiv_fixes_powAdjoin x hx hgen u N hroot hmemN
  rw [map_pow, torusScaleEquiv_apply, mul_pow, ← map_pow] at hfix
  have hcoefE : algebraMap F E ((u i₀ : F) ^ d) = 1 := by
    apply mul_right_cancel₀ (pow_ne_zero d hx0)
    simpa only [one_mul] using hfix
  have hcoefF : (u i₀ : F) ^ d = 1 := by
    apply (algebraMap F E).injective
    simpa using hcoefE
  have hζd : ζ ^ d = 1 := by simpa [u] using hcoefF
  have hdeq : d = 0 := hζ.pow_inj hdN hN (by simpa using hζd)
  omega

omit [CharZero F] in
/-- Every strict divisibility step in an arbitrary-family power tower is a strict field descent. -/
theorem arbitraryFamily_strictDivisibility_powerField_strict
    [Nonempty ι]
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (hroots : ContainsAllRootsOfUnity F)
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    ∀ n, differentialAdjoin F (Set.range fun i ↦ x i ^ D (n + 1)) <
      differentialAdjoin F (Set.range fun i ↦ x i ^ D n) := by
  have hpos : ∀ n, 0 < D n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => exact lt_trans ih (hlt n)
  intro n
  exact differentialAdjoin_range_pow_lt_of_dvd_of_lt
    x hx hgen hroots (hpos n) (hdiv n) (hlt n)

/-- Complete arbitrary-family power-quotient residue theorem: every level is a purely
transcendental ordinary extension of the common logarithmic residue, the infinite intersection is
exactly that residue, every divisibility step is strict, and the residue retains full differential
independence. -/
theorem arbitraryFamily_powerQuotientResidue
    [Nonempty ι]
    (hroots : ContainsAllRootsOfUnity F)
    (x : ι → E) (hx : DifferentialIndependent F x)
    (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (D : ℕ → ℕ) (hD0 : 2 ≤ D 0)
    (hdiv : ∀ n, D n ∣ D (n + 1)) (hlt : ∀ n, D n < D (n + 1)) :
    (∀ n, differentialAdjoin F (Set.range fun i ↦ x i ^ D n) =
      powerFamilyOrdinaryExtension F x (D n)) ∧
    (∀ n, AlgebraicIndependent
      (↥(differentialAdjoin F (Set.range fun i ↦ Differential.logDeriv (x i))))
      (fun i ↦ x i ^ D n)) ∧
    ({z : E | ∀ n : ℕ,
        z ∈ differentialAdjoin F (Set.range fun i ↦ x i ^ D n)} =
      (differentialAdjoin F
        (Set.range fun i ↦ Differential.logDeriv (x i)) : Set E)) ∧
    (∀ n, differentialAdjoin F (Set.range fun i ↦ x i ^ D (n + 1)) <
      differentialAdjoin F (Set.range fun i ↦ x i ^ D n)) ∧
    DifferentialIndependent F (fun i ↦ Differential.logDeriv (x i)) := by
  have hpos : ∀ n, 0 < D n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => exact lt_trans ih (hlt n)
  refine ⟨fun n ↦ differentialAdjoin_range_pow_eq_powerFamilyOrdinaryExtension
      x hx (hpos n), ?_, ?_, ?_, arbitraryFamily_logDeriv_differentialIndependent x hx⟩
  · intro n
    exact algebraicIndependent_pow_family_over_logDerivAdjoin
      hroots x hx hgen (hpos n)
  · exact arbitraryFamily_strictDivisibility_iInter_eq_logDeriv_of_roots
      hroots x hx hgen D hD0 hdiv hlt
  · exact arbitraryFamily_strictDivisibility_powerField_strict
      x hx hgen hroots D hD0 hdiv hlt

end

end GaloisForLFunctions.HTGeometry
