import GaloisForLFunctions.HTGeometry.ConstitutiveCarrierBifurcation

/-!
# Serial carrier composition and primary--secondary law birth

For composable linear carriers `E --S--> K --T--> A`, primary obstruction lives in the
outer cokernel.  Once it vanishes, secondary obstruction lives modulo both the inner range and
the outer kernel.  These sectors form a canonical short exact sequence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x

variable {𝕜 : Type u} {E : Type v} {K : Type w} {A : Type x}
variable [Field 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup K] [Module 𝕜 K]
variable [AddCommGroup A] [Module 𝕜 A]

def secondaryCarrierSubmodule (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Submodule 𝕜 K :=
  LinearMap.range S ⊔ LinearMap.ker T

def secondaryCarrierObstruction (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (k : K) :
    K ⧸ secondaryCarrierSubmodule S T :=
  (secondaryCarrierSubmodule S T).mkQ k

def compositeCarrierObstruction (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (a : A) :
    A ⧸ LinearMap.range (T.comp S) :=
  (LinearMap.range (T.comp S)).mkQ a

def outerCarrierObstruction (T : K →ₗ[𝕜] A) (a : A) :
    A ⧸ LinearMap.range T :=
  (LinearMap.range T).mkQ a

theorem secondaryCarrierObstruction_eq_zero_iff
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (k : K) :
    secondaryCarrierObstruction S T k = 0 ↔
      k ∈ LinearMap.range S ⊔ LinearMap.ker T := by
  exact Submodule.Quotient.mk_eq_zero _

theorem compositeCarrierObstruction_eq_zero_iff
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (a : A) :
    compositeCarrierObstruction S T a = 0 ↔
      ∃ e, T (S e) = a := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem outerCarrierObstruction_eq_zero_iff
    (T : K →ₗ[𝕜] A) (a : A) :
    outerCarrierObstruction T a = 0 ↔ ∃ k, T k = a := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem serialCarrierBirth_phase_trichotomy
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (a : A) :
    a ∉ LinearMap.range T ∨
      a ∈ LinearMap.range (T.comp S) ∨
      (a ∈ LinearMap.range T ∧ a ∉ LinearMap.range (T.comp S)) := by
  by_cases hp : a ∈ LinearMap.range T
  · by_cases hc : a ∈ LinearMap.range (T.comp S)
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨hp, hc⟩)
  · exact Or.inl hp

theorem compositeCarrierObstruction_eq_zero_iff_secondary
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (a : A) (k : K)
    (hk : T k = a) :
    compositeCarrierObstruction S T a = 0 ↔
      secondaryCarrierObstruction S T k = 0 := by
  rw [compositeCarrierObstruction_eq_zero_iff,
    secondaryCarrierObstruction_eq_zero_iff, Submodule.mem_sup]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨S e, ⟨e, rfl⟩, k - S e, ?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hk, he, sub_self]
    · abel
  · rintro ⟨s, ⟨e, rfl⟩, n, hn, hsum⟩
    refine ⟨e, ?_⟩
    calc
      T (S e) = T (S e + n) := by
        rw [map_add, LinearMap.mem_ker.mp hn, add_zero]
      _ = T k := congrArg T hsum
      _ = a := hk

theorem secondaryCarrierObstruction_independent
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (k k' : K)
    (hkk' : T k = T k') :
    secondaryCarrierObstruction S T k =
      secondaryCarrierObstruction S T k' := by
  rw [secondaryCarrierObstruction, secondaryCarrierObstruction,
    show (secondaryCarrierSubmodule S T).mkQ k =
        (secondaryCarrierSubmodule S T).mkQ k' ↔ _ from
      Submodule.Quotient.eq (secondaryCarrierSubmodule S T)]
  apply Submodule.mem_sup_right
  rw [LinearMap.mem_ker, map_sub, hkk', sub_self]

def secondaryCarrierMap (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    K →ₗ[𝕜] (A ⧸ LinearMap.range (T.comp S)) :=
  (LinearMap.range (T.comp S)).mkQ.comp T

theorem ker_secondaryCarrierMap
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    LinearMap.ker (secondaryCarrierMap S T) = secondaryCarrierSubmodule S T := by
  ext k
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk (T k) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change T k ∈ LinearMap.range (T.comp S) ↔
    k ∈ LinearMap.range S ⊔ LinearMap.ker T
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨S e, ⟨e, rfl⟩, k - S e, ?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub]
      change T k - T (S e) = 0
      rw [show T (S e) = T k from (by
        simpa only [LinearMap.comp_apply] using he), sub_self]
    · abel
  · rintro ⟨s, ⟨e, rfl⟩, n, hn, hsum⟩
    refine ⟨e, ?_⟩
    calc
      T (S e) = T (S e + n) := by
        rw [map_add, LinearMap.mem_ker.mp hn, add_zero]
      _ = T k := congrArg T hsum

def secondaryToComposite (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (K ⧸ secondaryCarrierSubmodule S T) →ₗ[𝕜]
      (A ⧸ LinearMap.range (T.comp S)) :=
  Submodule.liftQ (secondaryCarrierSubmodule S T) (secondaryCarrierMap S T) (by
    rw [← ker_secondaryCarrierMap S T])

@[simp]
theorem secondaryToComposite_mkQ
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (k : K) :
    secondaryToComposite S T ((secondaryCarrierSubmodule S T).mkQ k) =
      (LinearMap.range (T.comp S)).mkQ (T k) :=
  rfl

theorem secondaryToComposite_injective
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Function.Injective (secondaryToComposite S T) := by
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | _ k => ?_
  induction y using Submodule.Quotient.induction_on with | _ k' => ?_
  change (secondaryToComposite S T) ((secondaryCarrierSubmodule S T).mkQ k) =
    (secondaryToComposite S T) ((secondaryCarrierSubmodule S T).mkQ k') at hxy
  change (secondaryCarrierSubmodule S T).mkQ k =
    (secondaryCarrierSubmodule S T).mkQ k'
  rw [secondaryToComposite_mkQ, secondaryToComposite_mkQ] at hxy
  rw [show (secondaryCarrierSubmodule S T).mkQ k =
        (secondaryCarrierSubmodule S T).mkQ k' ↔ _ from
      Submodule.Quotient.eq (secondaryCarrierSubmodule S T)]
  rw [show (LinearMap.range (T.comp S)).mkQ (T k) =
        (LinearMap.range (T.comp S)).mkQ (T k') ↔ _ from
      Submodule.Quotient.eq (LinearMap.range (T.comp S))] at hxy
  change T k - T k' ∈ LinearMap.range (T.comp S) at hxy
  change k - k' ∈ LinearMap.range S ⊔ LinearMap.ker T
  obtain ⟨e, he⟩ := hxy
  rw [Submodule.mem_sup]
  refine ⟨S e, ⟨e, rfl⟩, (k - k') - S e, ?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, map_sub]
    change (T k - T k') - T (S e) = 0
    rw [show T (S e) = T k - T k' from (by
      simpa only [LinearMap.comp_apply] using he), sub_self]
  · abel

theorem compositeRange_le_outerRange (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    LinearMap.range (T.comp S) ≤ LinearMap.range T := by
  intro a ha
  obtain ⟨e, he⟩ := ha
  refine ⟨S e, ?_⟩
  simpa only [LinearMap.comp_apply] using he

def compositeToOuter (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (A ⧸ LinearMap.range (T.comp S)) →ₗ[𝕜] (A ⧸ LinearMap.range T) :=
  Submodule.factor (compositeRange_le_outerRange S T)

@[simp]
theorem compositeToOuter_mkQ
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) (a : A) :
    compositeToOuter S T ((LinearMap.range (T.comp S)).mkQ a) =
      (LinearMap.range T).mkQ a :=
  Submodule.factor_mk (compositeRange_le_outerRange S T) a

theorem compositeToOuter_surjective
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Function.Surjective (compositeToOuter S T) := by
  exact Submodule.factor_surjective (compositeRange_le_outerRange S T)

theorem range_secondaryToComposite_eq_ker_compositeToOuter
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    LinearMap.range (secondaryToComposite S T) =
      LinearMap.ker (compositeToOuter S T) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with | _ k => ?_
    change (secondaryToComposite S T) ((secondaryCarrierSubmodule S T).mkQ k) ∈
      LinearMap.ker (compositeToOuter S T)
    rw [LinearMap.mem_ker, secondaryToComposite_mkQ, compositeToOuter_mkQ]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨k, rfl⟩
  · intro hx
    induction x using Submodule.Quotient.induction_on with | _ a => ?_
    change (LinearMap.range (T.comp S)).mkQ a ∈
      LinearMap.ker (compositeToOuter S T) at hx
    change (LinearMap.range (T.comp S)).mkQ a ∈
      LinearMap.range (secondaryToComposite S T)
    rw [LinearMap.mem_ker, compositeToOuter_mkQ] at hx
    change Submodule.Quotient.mk a = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨(secondaryCarrierSubmodule S T).mkQ k, ?_⟩
    rw [secondaryToComposite_mkQ]
    exact (Submodule.Quotient.eq _).2 (by
      change T k - a ∈ LinearMap.range (T.comp S)
      rw [show T k = a from hk]
      simp)

theorem carrierComposition_short_exact
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Function.Injective (secondaryToComposite S T) ∧
      LinearMap.range (secondaryToComposite S T) =
        LinearMap.ker (compositeToOuter S T) ∧
      Function.Surjective (compositeToOuter S T) :=
  ⟨secondaryToComposite_injective S T,
    range_secondaryToComposite_eq_ker_compositeToOuter S T,
    compositeToOuter_surjective S T⟩

section Laboratories

def firstCarrierEmbedding : ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun x := (x, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

def sumOuterCarrier : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := x.1 + x.2
  map_add' x y := by simp [add_left_comm, add_comm]
  map_smul' c x := by simp [smul_eq_mul, mul_add]

def secondOuterCarrier : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun x := x.2
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp]
theorem firstCarrierEmbedding_apply (x : ℝ) :
    firstCarrierEmbedding x = (x, 0) :=
  rfl

@[simp]
theorem sumOuterCarrier_apply (x : ℝ × ℝ) :
    sumOuterCarrier x = x.1 + x.2 :=
  rfl

@[simp]
theorem secondOuterCarrier_apply (x : ℝ × ℝ) :
    secondOuterCarrier x = x.2 :=
  rfl

theorem verticalLift_not_mem_firstCarrierRange :
    ((0, 1) : ℝ × ℝ) ∉ LinearMap.range firstCarrierEmbedding := by
  rintro ⟨x, hx⟩
  have h := congrArg Prod.snd hx
  norm_num at h

theorem sumCarrier_kernel_cancels_vertical :
    ((0, 1) : ℝ × ℝ) - firstCarrierEmbedding 1 ∈
      LinearMap.ker sumOuterCarrier := by
  rw [LinearMap.mem_ker]
  norm_num [sumOuterCarrier, firstCarrierEmbedding]

theorem sumCarrier_secondary_obstruction_zero :
    secondaryCarrierObstruction firstCarrierEmbedding sumOuterCarrier (0, 1) = 0 := by
  rw [← compositeCarrierObstruction_eq_zero_iff_secondary
    firstCarrierEmbedding sumOuterCarrier 1 (0, 1) (by norm_num [sumOuterCarrier])]
  rw [compositeCarrierObstruction_eq_zero_iff]
  exact ⟨1, by norm_num [firstCarrierEmbedding, sumOuterCarrier]⟩

theorem secondCarrier_primary_obstruction_zero :
    outerCarrierObstruction secondOuterCarrier 1 = 0 := by
  rw [outerCarrierObstruction_eq_zero_iff]
  exact ⟨(0, 1), by norm_num [secondOuterCarrier]⟩

theorem secondCarrier_secondary_obstruction_nonzero :
    secondaryCarrierObstruction firstCarrierEmbedding secondOuterCarrier (0, 1) ≠ 0 := by
  intro hs
  have hc : compositeCarrierObstruction firstCarrierEmbedding secondOuterCarrier 1 = 0 :=
    (compositeCarrierObstruction_eq_zero_iff_secondary
      firstCarrierEmbedding secondOuterCarrier 1 (0, 1)
        (by norm_num [secondOuterCarrier])).2 hs
  rw [compositeCarrierObstruction_eq_zero_iff] at hc
  obtain ⟨e, he⟩ := hc
  norm_num [firstCarrierEmbedding, secondOuterCarrier] at he

theorem serialCarrierBirthMechanism_closed :
    ((0, 1) : ℝ × ℝ) ∉ LinearMap.range firstCarrierEmbedding ∧
      secondaryCarrierObstruction firstCarrierEmbedding sumOuterCarrier (0, 1) = 0 ∧
      outerCarrierObstruction secondOuterCarrier 1 = 0 ∧
      secondaryCarrierObstruction firstCarrierEmbedding secondOuterCarrier (0, 1) ≠ 0 :=
  ⟨verticalLift_not_mem_firstCarrierRange,
    sumCarrier_secondary_obstruction_zero,
    secondCarrier_primary_obstruction_zero,
    secondCarrier_secondary_obstruction_nonzero⟩

end Laboratories

end

end GaloisForLFunctions.HTGeometry
