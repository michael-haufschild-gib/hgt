import GaloisForLFunctions.RHTower.DeningerTensorSeminorm

/-!
# The elementary tensor map and product functionals of a projective tensor seminorm

The class of an elementary tensor in the quotient by the projective tensor seminorm depends only on
the classes of its two factors, since the seminorm of `x ⊗ y` is bounded by `p x · q y`.  This
gives a bilinear map of the two seminorm quotients into the quotient of the tensor product, of norm
at most one, and dually a product of two continuous functionals descends to a continuous functional
on the tensor quotient, of norm at most the product of the norms.

These are the two ingredients of the nuclearity of a tensor product of nuclear maps: the rank one
maps of the factors multiply to rank one maps of the tensor product.

* `deningerTensorBilin`, `_norm_le` : the bilinear map of the quotients.
* `deningerTensorBilinL`, `deningerTensorBilinR` : its two partial maps, as bounded maps.
* `deningerTensorDual`, `_apply`, `_norm_le` : the product of two functionals.
* `deningerTensorSeminorm_mono` : domination of projective tensor seminorms.
-/

namespace RHTower

open scoped TensorProduct

section TensorBilinear

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

/-- **Domination of projective tensor seminorms** follows from domination of the factors. -/
theorem deningerTensorSeminorm_mono {p₁ p₂ : Seminorm 𝕜 E} {q₁ q₂ : Seminorm 𝕜 F} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hp : ∀ x, p₁ x ≤ C * p₂ x) (hq : ∀ y, q₁ y ≤ D * q₂ y)
    (u : E ⊗[𝕜] F) :
    deningerTensorSeminorm p₁ q₁ u ≤ C * D * deningerTensorSeminorm p₂ q₂ u := by
  haveI : Nonempty (deningerTensorLifts u) := (deningerTensorLifts_nonempty u).to_subtype
  simp only [deningerTensorSeminorm_apply, deningerTensorFun]
  rw [Real.mul_iInf_of_nonneg (by positivity : (0 : ℝ) ≤ C * D)]
  refine le_ciInf fun L => ?_
  refine le_trans (deningerTensorFun_le_of_lift L.2) ?_
  rw [deningerTensorAux, deningerTensorAux, ← List.sum_map_mul_left]
  refine List.sum_le_sum fun z _ => ?_
  show p₁ z.1 * q₁ z.2 ≤ C * D * (p₂ z.1 * q₂ z.2)
  calc p₁ z.1 * q₁ z.2 ≤ (C * p₂ z.1) * (D * q₂ z.2) :=
        mul_le_mul (hp z.1) (hq z.2) (apply_nonneg q₁ _) (by positivity)
    _ = C * D * (p₂ z.1 * q₂ z.2) := by ring

/-- **The projective tensor seminorm is functorial**: a pair of maps bounded for the factor
seminorms is bounded for the tensor seminorms, with the product constant. -/
theorem deningerTensorSeminorm_map_le {E' F' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    [AddCommGroup F'] [Module 𝕜 F'] {p : Seminorm 𝕜 E} {p' : Seminorm 𝕜 E'}
    {q : Seminorm 𝕜 F} {q' : Seminorm 𝕜 F'} {f : E →ₗ[𝕜] E'} {g : F →ₗ[𝕜] F'} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hf : ∀ x, p' (f x) ≤ C * p x) (hg : ∀ y, q' (g y) ≤ D * q y)
    (u : E ⊗[𝕜] F) :
    deningerTensorSeminorm p' q' (TensorProduct.map f g u)
      ≤ C * D * deningerTensorSeminorm p q u := by
  haveI : Nonempty (deningerTensorLifts u) := (deningerTensorLifts_nonempty u).to_subtype
  simp only [deningerTensorSeminorm_apply, deningerTensorFun]
  rw [Real.mul_iInf_of_nonneg (by positivity : (0 : ℝ) ≤ C * D)]
  refine le_ciInf fun L => ?_
  obtain ⟨M, hM⟩ := L
  have hlift : M.map (fun z => (f z.1, g z.2))
      ∈ deningerTensorLifts (TensorProduct.map f g u) := by
    show ((M.map (fun z => (f z.1, g z.2))).map fun z => z.1 ⊗ₜ[𝕜] z.2).sum
      = TensorProduct.map f g u
    rw [← (hM : (M.map fun z => z.1 ⊗ₜ[𝕜] z.2).sum = u), map_list_sum, List.map_map,
      List.map_map]
    rfl
  refine le_trans (deningerTensorFun_le_of_lift hlift) ?_
  show _ ≤ C * D * deningerTensorAux p q M
  rw [deningerTensorAux, deningerTensorAux, List.map_map, ← List.sum_map_mul_left]
  refine List.sum_le_sum fun z _ => ?_
  show p' (f z.1) * q' (g z.2) ≤ C * D * (p z.1 * q z.2)
  calc p' (f z.1) * q' (g z.2) ≤ (C * p z.1) * (D * q z.2) :=
        mul_le_mul (hf z.1) (hg z.2) (apply_nonneg q' _) (by positivity)
    _ = C * D * (p z.1 * q z.2) := by ring

variable (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)

/-- The class of an elementary tensor, bilinearly in its two factors. -/
noncomputable def deningerTensorMk :
    E →ₗ[𝕜] F →ₗ[𝕜] DeningerSeminormSpace (deningerTensorSeminorm p q) :=
  (TensorProduct.mk 𝕜 E F).compr₂ (deningerSeminormMk (deningerTensorSeminorm p q))

theorem deningerTensorMk_apply (x : E) (y : F) :
    deningerTensorMk p q x y
      = deningerSeminormMk (deningerTensorSeminorm p q) (x ⊗ₜ[𝕜] y) := rfl

theorem deningerTensorMk_norm_le (x : E) (y : F) :
    ‖deningerTensorMk p q x y‖ ≤ p x * q y := by
  rw [deningerTensorMk_apply, deningerSeminormMk_norm]
  exact deningerTensorSeminorm_tmul_le p q x y

/-- The elementary tensor map descends in its second variable. -/
noncomputable def deningerTensorMkR (x : E) :
    DeningerSeminormSpace q →ₗ[𝕜] DeningerSeminormSpace (deningerTensorSeminorm p q) :=
  Submodule.liftQ (deningerSeminormKer q) (deningerTensorMk p q x) (by
    intro y hy
    have hq : q y = 0 := hy
    have hnorm : ‖deningerTensorMk p q x y‖ = 0 :=
      le_antisymm (by simpa [hq] using deningerTensorMk_norm_le p q x y) (norm_nonneg _)
    exact norm_eq_zero.mp hnorm)

theorem deningerTensorMkR_apply (x : E) (y : F) :
    deningerTensorMkR p q x (deningerSeminormMk q y) = deningerTensorMk p q x y := rfl

/-- **The bilinear map of the two seminorm quotients into the tensor quotient.** -/
noncomputable def deningerTensorBilin :
    DeningerSeminormSpace p →ₗ[𝕜] DeningerSeminormSpace q →ₗ[𝕜]
      DeningerSeminormSpace (deningerTensorSeminorm p q) :=
  Submodule.liftQ (deningerSeminormKer p)
    { toFun := fun x => deningerTensorMkR p q x
      map_add' := by
        intro x x'
        refine LinearMap.ext fun w => ?_
        obtain ⟨y, rfl⟩ := deningerSeminormMk_surjective q w
        show deningerTensorMk p q (x + x') y
          = deningerTensorMk p q x y + deningerTensorMk p q x' y
        rw [map_add]
        rfl
      map_smul' := by
        intro c x
        refine LinearMap.ext fun w => ?_
        obtain ⟨y, rfl⟩ := deningerSeminormMk_surjective q w
        show deningerTensorMk p q (c • x) y = c • deningerTensorMk p q x y
        rw [map_smul]
        rfl }
    (by
      intro x hx
      have hp : p x = 0 := hx
      refine LinearMap.ext fun w => ?_
      obtain ⟨y, rfl⟩ := deningerSeminormMk_surjective q w
      show deningerTensorMk p q x y = 0
      have hnorm : ‖deningerTensorMk p q x y‖ = 0 :=
        le_antisymm (by simpa [hp] using deningerTensorMk_norm_le p q x y) (norm_nonneg _)
      exact norm_eq_zero.mp hnorm)

theorem deningerTensorBilin_mk (x : E) (y : F) :
    deningerTensorBilin p q (deningerSeminormMk p x) (deningerSeminormMk q y)
      = deningerSeminormMk (deningerTensorSeminorm p q) (x ⊗ₜ[𝕜] y) := rfl

theorem deningerTensorBilin_norm_le (a : DeningerSeminormSpace p) (b : DeningerSeminormSpace q) :
    ‖deningerTensorBilin p q a b‖ ≤ ‖a‖ * ‖b‖ := by
  obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective p a
  obtain ⟨y, rfl⟩ := deningerSeminormMk_surjective q b
  rw [deningerTensorBilin_mk, deningerSeminormMk_norm, deningerSeminormMk_norm,
    deningerSeminormMk_norm]
  exact deningerTensorSeminorm_tmul_le p q x y

/-- The bilinear map with its first variable fixed, as a bounded map. -/
noncomputable def deningerTensorBilinL (a : DeningerSeminormSpace p) :
    DeningerSeminormSpace q →L[𝕜] DeningerSeminormSpace (deningerTensorSeminorm p q) :=
  LinearMap.mkContinuous (deningerTensorBilin p q a) ‖a‖ (deningerTensorBilin_norm_le p q a)

theorem deningerTensorBilinL_apply (a : DeningerSeminormSpace p) (b : DeningerSeminormSpace q) :
    deningerTensorBilinL p q a b = deningerTensorBilin p q a b := rfl

/-- The bilinear map with its second variable fixed, as a bounded map. -/
noncomputable def deningerTensorBilinR (b : DeningerSeminormSpace q) :
    DeningerSeminormSpace p →L[𝕜] DeningerSeminormSpace (deningerTensorSeminorm p q) :=
  LinearMap.mkContinuous ((deningerTensorBilin p q).flip b) ‖b‖ (fun a => by
    rw [mul_comm]
    exact deningerTensorBilin_norm_le p q a b)

theorem deningerTensorBilinR_apply (a : DeningerSeminormSpace p) (b : DeningerSeminormSpace q) :
    deningerTensorBilinR p q b a = deningerTensorBilin p q a b := rfl

end TensorBilinear

section TensorDual

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]
variable (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)

/-- The product of two functionals on the seminorm quotients, before descending. -/
noncomputable def deningerTensorDualAux (φ : DeningerSeminormSpace p →L[𝕜] 𝕜)
    (ψ : DeningerSeminormSpace q →L[𝕜] 𝕜) : (E ⊗[𝕜] F) →ₗ[𝕜] 𝕜 :=
  TensorProduct.lift
    ((LinearMap.mul 𝕜 𝕜).compl₁₂ (φ.toLinearMap.comp (deningerSeminormMk p))
      (ψ.toLinearMap.comp (deningerSeminormMk q)))

theorem deningerTensorDualAux_tmul (φ : DeningerSeminormSpace p →L[𝕜] 𝕜)
    (ψ : DeningerSeminormSpace q →L[𝕜] 𝕜) (x : E) (y : F) :
    deningerTensorDualAux p q φ ψ (x ⊗ₜ[𝕜] y)
      = φ (deningerSeminormMk p x) * ψ (deningerSeminormMk q y) := rfl

theorem deningerTensorDualAux_norm_le (φ : DeningerSeminormSpace p →L[𝕜] 𝕜)
    (ψ : DeningerSeminormSpace q →L[𝕜] 𝕜) (u : E ⊗[𝕜] F) :
    ‖deningerTensorDualAux p q φ ψ u‖ ≤ ‖φ‖ * ‖ψ‖ * deningerTensorSeminorm p q u := by
  refine deningerTensorSeminorm_dual_bound
    (φ := φ.toLinearMap.comp (deningerSeminormMk p))
    (ψ := ψ.toLinearMap.comp (deningerSeminormMk q))
    (deningerTensorDualAux_tmul p q φ ψ)
    (norm_nonneg φ) (norm_nonneg ψ) (fun x => ?_) (fun y => ?_) u
  · have h := φ.le_opNorm (deningerSeminormMk p x)
    rwa [deningerSeminormMk_norm] at h
  · have h := ψ.le_opNorm (deningerSeminormMk q y)
    rwa [deningerSeminormMk_norm] at h

/-- **The product of two continuous functionals**, as a functional on the tensor quotient. -/
noncomputable def deningerTensorDual (φ : DeningerSeminormSpace p →L[𝕜] 𝕜)
    (ψ : DeningerSeminormSpace q →L[𝕜] 𝕜) :
    DeningerSeminormSpace (deningerTensorSeminorm p q) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer (deningerTensorSeminorm p q))
      (deningerTensorDualAux p q φ ψ) (by
        intro u hu
        have hzero : deningerTensorSeminorm p q u = 0 := hu
        have hnorm : ‖deningerTensorDualAux p q φ ψ u‖ = 0 :=
          le_antisymm (by simpa [hzero] using deningerTensorDualAux_norm_le p q φ ψ u)
            (norm_nonneg _)
        exact norm_eq_zero.mp hnorm))
    (‖φ‖ * ‖ψ‖)
    (by
      rintro ⟨u⟩
      exact deningerTensorDualAux_norm_le p q φ ψ u)

theorem deningerTensorDual_mk (φ : DeningerSeminormSpace p →L[𝕜] 𝕜)
    (ψ : DeningerSeminormSpace q →L[𝕜] 𝕜) (x : E) (y : F) :
    deningerTensorDual p q φ ψ
        (deningerSeminormMk (deningerTensorSeminorm p q) (x ⊗ₜ[𝕜] y))
      = φ (deningerSeminormMk p x) * ψ (deningerSeminormMk q y) := rfl

theorem deningerTensorDual_norm_le (φ : DeningerSeminormSpace p →L[𝕜] 𝕜)
    (ψ : DeningerSeminormSpace q →L[𝕜] 𝕜) : ‖deningerTensorDual p q φ ψ‖ ≤ ‖φ‖ * ‖ψ‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end TensorDual

end RHTower
