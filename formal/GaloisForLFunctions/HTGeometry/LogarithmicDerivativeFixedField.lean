import GaloisForLFunctions.HTGeometry.FreeDifferentialScalingAutomorphism
import GaloisForLFunctions.HTGeometry.ScalingInvariantRationalFunction
import GaloisForLFunctions.HTGeometry.TranscendentalMobius

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
  set sc := scalingAutomorphism hF ha hy hytop with hscdef
  set F0 : IntermediateField F E :=
    { carrier := {w : E | sc w = w}
      mul_mem' := by intro u v hu hv; simp only [Set.mem_setOf_eq] at *; rw [map_mul, hu, hv]
      one_mem' := by simp
      add_mem' := by intro u v hu hv; simp only [Set.mem_setOf_eq] at *; rw [map_add, hu, hv]
      zero_mem' := by simp
      algebraMap_mem' := by intro r; simp only [Set.mem_setOf_eq]; exact sc.commutes r
      inv_mem' := by
        intro u hu
        simp only [Set.mem_setOf_eq] at *
        rw [map_inv₀, hu] } with hF0def
  have hclosed : DerivationClosed F0 := by
    intro w hw
    have hw' : sc w = w := hw
    show sc (Differential.deriv w) = Differential.deriv w
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
  haveI : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
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
    Polynomial.finite_setOf_isRoot hmapne
  exact himg (hfin.subset hsub)


/-- Evaluation of a rational function at the generator, through numerator and denominator. -/
theorem ratFuncEval_eq_div {L : Type*} [Field L] {K : Type*} [Field K] [Algebra L K]
    {y : K} (hy : Transcendental L y) (f : RatFunc L) :
    ratFuncEval y hy f = Polynomial.aeval y f.num / Polynomial.aeval y f.denom := by
  have hpoly : ∀ P : Polynomial L,
      ratFuncEval y hy (algebraMap (Polynomial L) (RatFunc L) P) = Polynomial.aeval y P := by
    intro P
    induction P using Polynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp [hp, hq]
    | monomial n c ih =>
        simp only [Polynomial.C_mul_X_pow_eq_monomial] at ih ⊢
        simp [RatFunc.algebraMap_X]
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀, hpoly, hpoly]

/-- **A scaling-invariant element lies in the logarithmic-derivative field.** -/
theorem mem_logDerivField_of_scaling_invariant [CharZero F]
    (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) (hy0 : y ≠ 0)
    {a : F} (ha : a ≠ 0)
    (hsep : ∀ i j : ℕ, i ≠ j → (algebraMap F E a) ^ i ≠ (algebraMap F E a) ^ j)
    {x : E} (hx : scalingAutomorphism hF ha hy hytop x = x) :
    x ∈ differentialAdjoin F ({y′ / y} : Set E) := by
  classical
  set L : IntermediateField F E := differentialAdjoin F ({y′ / y} : Set E) with hLdef
  have hytr : Transcendental (↥L) y := transcendental_over_logDerivField hF hy hytop hy0
  have hinj : Function.Injective (Polynomial.aeval (R := ↥L) y) :=
    transcendental_iff_injective.mp hytr
  have hgen : IntermediateField.adjoin (↥L) ({y} : Set E) = ⊤ :=
    IntermediateField.restrictScalars_injective F
      (by simpa using adjoin_generator_over_logDerivField (F := F) hy0 hytop)
  have hxmem : x ∈ IntermediateField.adjoin (↥L) ({y} : Set E) := by rw [hgen]; trivial
  set f : RatFunc (↥L) := (RatFunc.algEquivOfTranscendental y hytr).symm ⟨x, hxmem⟩ with hfdef
  have hxeval : ratFuncEval y hytr f = x := by
    simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hfdef,
      AlgEquiv.apply_symm_apply]
    rfl
  set P : Polynomial (↥L) := f.num with hP
  set Q : Polynomial (↥L) := f.denom with hQ
  have hQ0 : Q ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime P Q := RatFunc.isCoprime_num_denom f
  have hQy : Polynomial.aeval y Q ≠ 0 := fun h => hQ0 (hinj (by simpa using h))
  have hxdiv : x = Polynomial.aeval y P / Polynomial.aeval y Q := by
    rw [← hxeval, ratFuncEval_eq_div]
  set α : ↥L := ⟨algebraMap F E a, L.algebraMap_mem a⟩ with hα
  have hα0 : α ≠ 0 := by
    intro h
    exact ha ((algebraMap F E).injective (by
      have : algebraMap F E a = 0 := congrArg Subtype.val h
      rw [this, map_zero]))
  have hαsep : ∀ i j : ℕ, i ≠ j → α ^ i ≠ α ^ j := fun i j hij hcon =>
    hsep i j hij (congrArg Subtype.val hcon)
  -- the deck automorphism transports a polynomial value to the scaled polynomial value
  have hscale : ∀ R : Polynomial (↥L),
      scalingAutomorphism hF ha hy hytop (Polynomial.aeval y R)
        = Polynomial.aeval y (R.comp (Polynomial.C α * Polynomial.X)) := by
    intro R
    have h1 := Polynomial.aeval_algHom_apply
      (scalingAutomorphismOverLogDeriv hF ha hy hytop).toAlgHom y R
    have h2 : (scalingAutomorphismOverLogDeriv hF ha hy hytop).toAlgHom y = algebraMap F E a * y :=
      scalingAutomorphism_generator hF ha hy hytop
    rw [h2] at h1
    have h3 : Polynomial.aeval y (Polynomial.C α * Polynomial.X : Polynomial (↥L))
        = algebraMap F E a * y := by simp [hα]
    rw [Polynomial.aeval_comp, h3]
    exact h1.symm
  have hQ'0 : Q.comp (Polynomial.C α * Polynomial.X) ≠ 0 := comp_scaling_ne_zero hα0 hQ0
  have hQ'y : Polynomial.aeval y (Q.comp (Polynomial.C α * Polynomial.X)) ≠ 0 :=
    fun h => hQ'0 (hinj (by simpa using h))
  have hcross : Polynomial.aeval y (P.comp (Polynomial.C α * Polynomial.X)) *
      Polynomial.aeval y Q
      = Polynomial.aeval y P * Polynomial.aeval y (Q.comp (Polynomial.C α * Polynomial.X)) := by
    have hσx : scalingAutomorphism hF ha hy hytop x = x := hx
    rw [hxdiv, map_div₀, hscale, hscale] at hσx
    field_simp [hQy, hQ'y] at hσx
    linear_combination hσx
  have heq : (P.comp (Polynomial.C α * Polynomial.X)) * Q
      = P * (Q.comp (Polynomial.C α * Polynomial.X)) := by
    refine hinj ?_
    simpa using hcross
  rcases eq_or_ne P 0 with hP0 | hP0
  · rw [hxdiv, hP0]
    simp
  obtain ⟨hdP, hdQ⟩ := natDegree_eq_zero_of_scaling_invariant hα0 hαsep hP0 hQ0 hcop heq
  rw [hxdiv, Polynomial.eq_C_of_natDegree_eq_zero hdP,
    Polynomial.eq_C_of_natDegree_eq_zero hdQ]
  simp only [Polynomial.aeval_C]
  exact L.div_mem (P.coeff 0).2 (Q.coeff 0).2


omit [Differential F] [Differential E] [DifferentialAlgebra F E] in
/-- In characteristic zero the powers of `2` are pairwise distinct. -/
theorem two_pow_ne_of_ne [CharZero F] {i j : ℕ} (hij : i ≠ j) :
    (algebraMap F E (2 : F)) ^ i ≠ (algebraMap F E (2 : F)) ^ j := by
  intro h
  have h1 : algebraMap F E ((2 : F) ^ i) = algebraMap F E ((2 : F) ^ j) := by
    simpa using h
  have h2 : (2 : F) ^ i = (2 : F) ^ j := (algebraMap F E).injective h1
  have h3 : (((2 ^ i : ℕ) : F)) = (((2 ^ j : ℕ) : F)) := by push_cast; exact h2
  have h4 : (2 : ℕ) ^ i = 2 ^ j := Nat.cast_injective h3
  exact hij (Nat.pow_right_injective (le_refl 2) h4)

/-- **The Maurer--Cartan coordinate is exactly the scaling-invariant field.**  In a freely
differentially generated field over a base of constants, the elements fixed by every scaling
automorphism `y ↦ a·y` are exactly the differential rational functions of the logarithmic
derivative `y′/y`. -/
theorem fixedField_scaling_eq_logDerivField [CharZero F]
    (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) (hy0 : y ≠ 0) :
    {x : E | ∀ (a : F) (ha : a ≠ 0), scalingAutomorphism hF ha hy hytop x = x}
      = (differentialAdjoin F ({y′ / y} : Set E) : Set E) := by
  ext x
  constructor
  · intro hx
    have htwo : (2 : F) ≠ 0 := two_ne_zero
    exact mem_logDerivField_of_scaling_invariant hF hy hytop hy0 htwo
      (fun i j hij => two_pow_ne_of_ne (E := E) hij) (hx 2 htwo)
  · intro hx a ha
    exact scalingAutomorphism_fixes_logDerivField hF ha hy hytop hx

end

end GaloisForLFunctions.HTGeometry
