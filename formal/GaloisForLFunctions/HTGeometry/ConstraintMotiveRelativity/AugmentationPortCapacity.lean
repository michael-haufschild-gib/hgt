import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CofinalInverseCapacity
import Mathlib

/-!
# The augmentation port of an orthonormal family

The prime augmentation functional `x ↦ ∑ x_p`, restricted to the finitely supported vectors of a
Hilbert space with orthonormal family `e`, is the model case of the cofinal inverse-capacity law.
Its finite sections are surjective, the `n`-th capacity is `n`, and the uniform lift of `1` has
squared norm `1/n`.  The limiting filling seminorm therefore vanishes identically and the closed
graph is totally vertical.
-/

open Filter GaloisForLFunctions.HTGeometry
open scoped Topology InnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section AugmentationPort

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
variable (e : ℕ → X)

/-- Finite formal combinations of the family, realized in `X`. -/
noncomputable def augEmbed : (ℕ →₀ 𝕜) →ₗ[𝕜] X := Finsupp.linearCombination 𝕜 e

/-- The total-mass functional on finite formal combinations. -/
noncomputable def augMass : (ℕ →₀ 𝕜) →ₗ[𝕜] 𝕜 := Finsupp.lsum 𝕜 fun _ => LinearMap.id

@[simp] theorem augMass_single (i : ℕ) (c : 𝕜) : augMass (Finsupp.single i c) = c := by
  simp [augMass]

theorem augEmbed_injective (he : Orthonormal 𝕜 e) :
    Function.Injective (augEmbed (𝕜 := 𝕜) e) :=
  Orthonormal.linearIndependent he

/-- The **augmentation port**: the functional `x ↦ ∑ x_i` on the span of the family. -/
noncomputable def augPort (he : Orthonormal 𝕜 e) : X →ₗ.[𝕜] 𝕜 where
  domain := LinearMap.range (augEmbed (𝕜 := 𝕜) e)
  toFun := augMass ∘ₗ (LinearEquiv.ofInjective _ (augEmbed_injective e he)).symm.toLinearMap

@[simp] theorem augPort_domain (he : Orthonormal 𝕜 e) :
    (augPort e he).domain = LinearMap.range (augEmbed (𝕜 := 𝕜) e) := rfl

theorem augPort_apply (he : Orthonormal 𝕜 e) (l : ℕ →₀ 𝕜)
    (hmem : augEmbed (𝕜 := 𝕜) e l ∈ LinearMap.range (augEmbed (𝕜 := 𝕜) e)) :
    augPort e he ⟨augEmbed (𝕜 := 𝕜) e l, hmem⟩ = augMass l := by
  have hval : (LinearEquiv.ofInjective _ (augEmbed_injective e he)) l
      = (⟨augEmbed (𝕜 := 𝕜) e l, hmem⟩ : LinearMap.range (augEmbed (𝕜 := 𝕜) e)) :=
    Subtype.ext rfl
  have hsymm : (LinearEquiv.ofInjective _ (augEmbed_injective e he)).symm
      (⟨augEmbed (𝕜 := 𝕜) e l, hmem⟩ : LinearMap.range (augEmbed (𝕜 := 𝕜) e)) = l := by
    rw [← hval, LinearEquiv.symm_apply_apply]
  exact congrArg augMass hsymm

theorem augEmbed_single (i : ℕ) (c : 𝕜) :
    augEmbed (𝕜 := 𝕜) e (Finsupp.single i c) = c • e i := by
  simp [augEmbed]

theorem range_augEmbed :
    LinearMap.range (augEmbed (𝕜 := 𝕜) e) = Submodule.span 𝕜 (Set.range e) :=
  Finsupp.range_linearCombination (R := 𝕜) (v := e)

/-! ### The finite-section tower -/

/-- The `n`-th finite section: the span of the first `n` members of the family. -/
def augStage (n : ℕ) : Submodule 𝕜 X := Submodule.span 𝕜 (e '' Set.Iio n)

theorem augStage_mono : Monotone (augStage (𝕜 := 𝕜) e) := by
  intro m n hmn
  exact Submodule.span_mono (Set.image_mono fun _ hx => lt_of_lt_of_le hx hmn)

theorem mem_augStage (i n : ℕ) (h : i < n) : e i ∈ augStage (𝕜 := 𝕜) e n :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem iSup_augStage : ⨆ n, augStage (𝕜 := 𝕜) e n = Submodule.span 𝕜 (Set.range e) := by
  refine le_antisymm (iSup_le fun n => Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, -, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (i + 1) (mem_augStage e i (i + 1) (Nat.lt_succ_self i))

theorem augStage_le_domain (he : Orthonormal 𝕜 e) (n : ℕ) :
    augStage (𝕜 := 𝕜) e n ≤ (augPort e he).domain := by
  rw [augPort_domain, range_augEmbed, ← iSup_augStage]
  exact le_iSup (augStage (𝕜 := 𝕜) e) n

theorem augPort_filling (he : Orthonormal 𝕜 e) {n : ℕ} (hn : 1 ≤ n) :
    PortFilling (augPort e he) (augStage e n) := by
  intro y
  have hmem : augEmbed (𝕜 := 𝕜) e (Finsupp.single 0 y)
      ∈ LinearMap.range (augEmbed (𝕜 := 𝕜) e) := ⟨Finsupp.single 0 y, rfl⟩
  refine ⟨⟨augEmbed (𝕜 := 𝕜) e (Finsupp.single 0 y), hmem⟩, ?_, ?_⟩
  · show augEmbed (𝕜 := 𝕜) e (Finsupp.single 0 y) ∈ augStage e n
    rw [augEmbed_single]
    exact Submodule.smul_mem _ _ (mem_augStage e 0 n hn)
  · rw [augPort_apply e he, augMass_single]

/-- The cofinal port tower of finite sections. -/
noncomputable def augTower (he : Orthonormal 𝕜 e) : PortTower (augPort e he) where
  stage := augStage e
  mono := augStage_mono e
  exhaust := by rw [iSup_augStage, augPort_domain, range_augEmbed]
  base := 1
  filling := fun _ hn => augPort_filling e he hn

/-! ### The uniform lift and the vanishing of the limiting filling seminorm -/

/-- The uniform formal lift of the total mass `1` supported on the first `n` members. -/
noncomputable def augUniform (n : ℕ) : ℕ →₀ 𝕜 :=
  ∑ i ∈ Finset.range n, Finsupp.single i ((n : 𝕜)⁻¹)

theorem augMass_augUniform {n : ℕ} (hn : 1 ≤ n) : augMass (augUniform (𝕜 := 𝕜) n) = 1 := by
  have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [augUniform, map_sum]
  simp only [augMass_single, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem augEmbed_augUniform (n : ℕ) :
    augEmbed (𝕜 := 𝕜) e (augUniform n) = ∑ i ∈ Finset.range n, ((n : 𝕜)⁻¹) • e i := by
  rw [augUniform, map_sum]
  exact Finset.sum_congr rfl fun i _ => augEmbed_single e i _

theorem normSq_augEmbed_augUniform (he : Orthonormal 𝕜 e) {n : ℕ} (hn : 1 ≤ n) :
    ‖augEmbed (𝕜 := 𝕜) e (augUniform n)‖ ^ (2 : ℕ) = (n : ℝ)⁻¹ := by
  have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [augEmbed_augUniform]
  set c : 𝕜 := (n : 𝕜)⁻¹ with hc
  have hinner := Orthonormal.inner_sum he (fun _ => c) (fun _ => c) (Finset.range n)
  have hnorm : ‖∑ i ∈ Finset.range n, c • e i‖ ^ (2 : ℕ)
      = RCLike.re ⟪∑ i ∈ Finset.range n, c • e i, ∑ i ∈ Finset.range n, c • e i⟫_𝕜 :=
    (inner_self_eq_norm_sq _).symm
  rw [hnorm, hinner]
  have hsum : ∑ i ∈ Finset.range n, (starRingEnd 𝕜) c * c = (n : 𝕜) * ((starRingEnd 𝕜) c * c) := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  have hcc : (starRingEnd 𝕜) c * c = ((‖c‖ ^ (2 : ℕ) : ℝ) : 𝕜) := by
    rw [RCLike.conj_mul]
    push_cast
    simp
  rw [hcc]
  have hcnorm : ‖c‖ = (n : ℝ)⁻¹ := by
    rw [hc, norm_inv, RCLike.norm_natCast]
  rw [hcnorm]
  have : ((n : 𝕜) * (((((n : ℝ)⁻¹) ^ (2 : ℕ) : ℝ)) : 𝕜)) = (((n : ℝ) * ((n : ℝ)⁻¹) ^ (2 : ℕ) : ℝ) : 𝕜) := by
    push_cast
    ring
  rw [this, RCLike.ofReal_re]
  field_simp

theorem tendsto_norm_augEmbed_augUniform (he : Orthonormal 𝕜 e) :
    Tendsto (fun n => ‖augEmbed (𝕜 := 𝕜) e (augUniform n)‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => ‖augEmbed (𝕜 := 𝕜) e (augUniform (n + 1))‖ ^ (2 : ℕ)) atTop
      (𝓝 0) := by
    have : ∀ n : ℕ, ‖augEmbed (𝕜 := 𝕜) e (augUniform (n + 1))‖ ^ (2 : ℕ) = ((n : ℝ) + 1)⁻¹ := by
      intro n
      rw [normSq_augEmbed_augUniform e he (Nat.le_add_left 1 n)]
      push_cast
      ring_nf
    simp only [this]
    exact tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by rw [one_div]
  have hshift : Tendsto (fun n : ℕ => ‖augEmbed (𝕜 := 𝕜) e (augUniform (n + 1))‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ => Real.sqrt r) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    have := hc.comp hsq
    refine this.congr fun n => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- **Totally vertical augmentation port.**  The closed graph of the augmentation functional of an
orthonormal family is maximally multivalued. -/
theorem augPort_multivaluedHorizon (he : Orthonormal 𝕜 e) :
    multivaluedHorizon (augPort e he) = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  have hmem : ∀ n : ℕ, augEmbed (𝕜 := 𝕜) e (y • augUniform n)
      ∈ LinearMap.range (augEmbed (𝕜 := 𝕜) e) := fun n => ⟨y • augUniform n, rfl⟩
  refine mem_multivaluedHorizon_of_tendsto
    (fun n => ⟨augEmbed (𝕜 := 𝕜) e (y • augUniform (n + 1)), hmem (n + 1)⟩) (fun j => ?_) ?_
  · rw [augPort_apply e he, map_smul, augMass_augUniform (Nat.le_add_left 1 j), smul_eq_mul,
      mul_one]
  · have hscale : ∀ n : ℕ, ‖augEmbed (𝕜 := 𝕜) e (y • augUniform (n + 1))‖
        = ‖y‖ * ‖augEmbed (𝕜 := 𝕜) e (augUniform (n + 1))‖ := by
      intro n
      rw [map_smul, norm_smul]
    simp only [hscale]
    have hbase : Tendsto (fun n : ℕ => ‖augEmbed (𝕜 := 𝕜) e (augUniform (n + 1))‖) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr (tendsto_norm_augEmbed_augUniform e he)
    simpa using hbase.const_mul ‖y‖

/-- The limiting filling seminorm of the augmentation tower vanishes identically. -/
theorem augTower_fillNormInf (he : Orthonormal 𝕜 e) (y : 𝕜) :
    (augTower e he).fillNormInf y = 0 := by
  have h := (augTower e he).multivaluedHorizon_eq
  have hy : y ∈ multivaluedHorizon (augPort e he) := by
    rw [augPort_multivaluedHorizon]; trivial
  rw [h] at hy
  exact hy

end AugmentationPort

end HTGeometry.ConstraintMotiveRelativity
