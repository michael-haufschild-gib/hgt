import GaloisForLFunctions.HTGeometry.FreeDifferentialScalingAutomorphism

/-!
# The logarithmic derivative is the scaling-invariant coordinate

In a freely differentially generated field `F⟨y⟩` the scaling automorphisms `y ↦ a·y` fix the
logarithmic derivative `ℓ = y′/y`, and every jet of `y` is a `F⟨ℓ⟩`-multiple of `y`.  So `y`
generates the whole field over `F⟨ℓ⟩` by a single ordinary adjunction, and the multiplicative deck
group acts on that single coordinate.

This is the `G_m` case of the position–velocity splitting: the erased sector is the whole group,
the reversible position is trivial, and the persistent information is exactly the Maurer–Cartan
velocity `ℓ`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- **The scaling automorphisms fix the logarithmic derivative.** -/
theorem scalingAutomorphism_logDeriv (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    scalingAutomorphism hF ha hy hytop (y′ / y) = y′ / y := by
  have hσ := scalingAutomorphism_deriv hF ha hy hytop y
  have hgen := scalingAutomorphism_generator hF ha hy hytop
  have haE : algebraMap F E a ≠ 0 := by
    intro h
    exact ha ((algebraMap F E).injective (by rw [h, map_zero]))
  rw [map_div₀, hσ, hgen]
  have hderiv : (algebraMap F E a * y)′ = algebraMap F E a * y′ := by
    have hleib := Differential.deriv.leibniz (algebraMap F E a) y
    simp only [smul_eq_mul] at hleib
    rw [hleib, hF a, mul_zero, add_zero]
  rw [hderiv, mul_div_mul_left _ _ haE]

/-- **Every jet of the generator is an `F⟨y′/y⟩`-multiple of the generator.** -/
theorem exists_logDerivField_coeff {y : E} (hy0 : y ≠ 0) (n : ℕ) :
    ∃ p ∈ differentialAdjoin F ({y′ / y} : Set E), differentialJet n y = p * y := by
  induction n with
  | zero =>
      refine ⟨1, (differentialAdjoin F ({y′ / y} : Set E)).one_mem, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨p, hp, hpn⟩ := ih
      refine ⟨p′ + p * (y′ / y), ?_, ?_⟩
      · exact (differentialAdjoin F ({y′ / y} : Set E)).add_mem
          (derivationClosed_differentialAdjoin F _ hp)
          ((differentialAdjoin F ({y′ / y} : Set E)).mul_mem hp
            (subset_differentialAdjoin F _ rfl))
      · rw [differentialJet_succ, hpn]
        have hleib := Differential.deriv.leibniz p y
        simp only [smul_eq_mul] at hleib
        rw [hleib]
        field_simp
        ring

/-- **The generator adjoins the whole field to the logarithmic-derivative field.** -/
theorem adjoin_generator_over_logDerivField {y : E} (hy0 : y ≠ 0)
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    (IntermediateField.adjoin (↥(differentialAdjoin F ({y′ / y} : Set E))) ({y} : Set E)
      ).restrictScalars F = ⊤ := by
  set L : IntermediateField F E := differentialAdjoin F ({y′ / y} : Set E) with hL
  set M : IntermediateField F E :=
    (IntermediateField.adjoin (↥L) ({y} : Set E)).restrictScalars F with hM
  have hjet : ∀ n : ℕ, differentialJet n y ∈ M := by
    intro n
    obtain ⟨p, hp, hpn⟩ := exists_logDerivField_coeff (F := F) hy0 n
    have hpM : p ∈ M := by
      have h := (IntermediateField.adjoin (↥L) ({y} : Set E)).algebraMap_mem ⟨p, hp⟩
      change p ∈ IntermediateField.adjoin (↥L) ({y} : Set E)
      simpa using h
    have hyM : y ∈ M := by
      have : y ∈ IntermediateField.adjoin (↥L) ({y} : Set E) :=
        IntermediateField.subset_adjoin _ _ rfl
      exact this
    rw [hpn]
    exact M.mul_mem hpM hyM
  refine top_le_iff.mp ?_
  rw [← hytop]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro z ⟨x, hx, n, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hjet n


/-- The deck automorphism fixes the whole logarithmic-derivative field. -/
theorem scalingAutomorphism_fixes_logDerivField (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤)
    {z : E} (hz : z ∈ differentialAdjoin F ({y′ / y} : Set E)) :
    scalingAutomorphism hF ha hy hytop z = z := by
  set σ := scalingAutomorphism hF ha hy hytop with hσdef
  set F0 : IntermediateField F E :=
    { carrier := {w : E | σ w = w}
      mul_mem' := by intro u v hu hv; simp only [Set.mem_setOf_eq] at *; rw [map_mul, hu, hv]
      one_mem' := by simp
      add_mem' := by intro u v hu hv; simp only [Set.mem_setOf_eq] at *; rw [map_add, hu, hv]
      zero_mem' := by simp
      algebraMap_mem' := by intro r; simp only [Set.mem_setOf_eq]; exact σ.commutes r
      inv_mem' := by
        intro u hu
        simp only [Set.mem_setOf_eq] at *
        rw [map_inv₀, hu] } with hF0def
  have hclosed : DerivationClosed F0 := by
    intro w hw
    have hw' : σ w = w := hw
    show σ (w′) = w′
    rw [scalingAutomorphism_deriv hF ha hy hytop w, hw']
  have hmem : (y′ / y) ∈ F0 := scalingAutomorphism_logDeriv hF ha hy hytop
  have hle : differentialAdjoin F ({y′ / y} : Set E) ≤ F0 :=
    differentialAdjoin_le F (by simpa using hmem) hclosed
  exact hle hz

/-- The deck automorphism, viewed as an automorphism over the logarithmic-derivative field. -/
def scalingAutomorphismOverLogDeriv (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    E ≃ₐ[↥(differentialAdjoin F ({y′ / y} : Set E))] E where
  toFun := scalingAutomorphism hF ha hy hytop
  invFun := (scalingAutomorphism hF ha hy hytop).symm
  left_inv := (scalingAutomorphism hF ha hy hytop).left_inv
  right_inv := (scalingAutomorphism hF ha hy hytop).right_inv
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := fun l => scalingAutomorphism_fixes_logDerivField hF ha hy hytop l.2

/-- **The generator is transcendental over the logarithmic-derivative field.**  The deck orbit of
the generator is infinite, so it cannot sit inside the finite root set of a polynomial. -/
theorem transcendental_over_logDerivField [CharZero F]
    (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) (hy0 : y ≠ 0) :
    Transcendental (↥(differentialAdjoin F ({y′ / y} : Set E))) y := by
  classical
  set L : IntermediateField F E := differentialAdjoin F ({y′ / y} : Set E) with hLdef
  intro halg
  obtain ⟨p, hp0, hpy⟩ := halg
  have hmapne : p.map (algebraMap (↥L) E) ≠ 0 := by
    intro h
    exact hp0 ((Polynomial.map_eq_zero_iff (algebraMap (↥L) E).injective).mp h)
  have hroot : ∀ a : F, a ≠ 0 → (p.map (algebraMap (↥L) E)).IsRoot (algebraMap F E a * y) := by
    intro a ha
    have hσ : (scalingAutomorphismOverLogDeriv hF ha hy hytop) y = algebraMap F E a * y :=
      scalingAutomorphism_generator hF ha hy hytop
    have hzero : Polynomial.aeval
        ((scalingAutomorphismOverLogDeriv hF ha hy hytop).toAlgHom y) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, hpy, map_zero]
    have hval : (scalingAutomorphismOverLogDeriv hF ha hy hytop).toAlgHom y
        = algebraMap F E a * y := hσ
    rw [hval] at hzero
    simpa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] using hzero
  have hinj : Function.Injective (fun a : F => algebraMap F E a * y) := by
    intro a b hab
    simp only at hab
    exact (algebraMap F E).injective (mul_right_cancel₀ hy0 hab)
  haveI : Infinite F := CharZero.infinite F
  have hnz : {a : F | a ≠ 0}.Infinite := by
    have hfin0 : ({0} : Set F).Finite := Set.finite_singleton 0
    simpa [Set.compl_def] using hfin0.infinite_compl
  have himg : ((fun a : F => algebraMap F E a * y) '' {a : F | a ≠ 0}).Infinite :=
    hnz.image (Set.injOn_of_injective hinj)
  have hsub : (fun a : F => algebraMap F E a * y) '' {a : F | a ≠ 0} ⊆
      {x : E | (p.map (algebraMap (↥L) E)).IsRoot x} := by
    rintro _ ⟨a, ha, rfl⟩
    exact hroot a ha
  have hfin : {x : E | (p.map (algebraMap (↥L) E)).IsRoot x}.Finite :=
    (p.map (algebraMap (↥L) E)).setOf_isRoot_finite hmapne
  exact himg (hfin.subset hsub)

end

end GaloisForLFunctions.HTGeometry
