import GaloisForLFunctions.Hurwitz.IntegerTranslationDifferentialMatroid
import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionRankLaw
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.CategoryTheory.Action

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev HurwitzCharacterLattice (I : Type*) := I → ℤ
abbrev HurwitzTorus (I : Type*) := I → ℂˣ
abbrev HurwitzLaurentRing (I : Type*) := AddMonoidAlgebra ℂ (HurwitzCharacterLattice I)

@[simp]
theorem additiveComplexUnits_toMul_zero : (0 : Additive ℂˣ).toMul = 1 := rfl

@[simp]
theorem additiveComplexUnits_toMul_ofMul (z : ℂˣ) :
    (Additive.ofMul z : Additive ℂˣ).toMul = z := rfl

def hurwitzTorusCharacterHom {I : Type*} [Fintype I]
    (x : HurwitzTorus I) : HurwitzCharacterLattice I →+ Additive ℂˣ where
  toFun u := Additive.ofMul (∏ i, x i ^ u i)
  map_zero' := by simp
  map_add' u v := by
    change Additive.ofMul (∏ i, x i ^ (u i + v i)) =
      Additive.ofMul ((∏ i, x i ^ u i) * ∏ i, x i ^ v i)
    congr 1
    simp only [zpow_add]
    exact Finset.prod_mul_distrib

def hurwitzTorusCharacter {I : Type*} [Fintype I]
    (x : HurwitzTorus I) (u : HurwitzCharacterLattice I) : ℂˣ :=
  (hurwitzTorusCharacterHom x u).toMul

@[simp]
theorem hurwitzTorusCharacterHom_toMul {I : Type*} [Fintype I]
    (x : HurwitzTorus I) (u : HurwitzCharacterLattice I) :
    (hurwitzTorusCharacterHom x u).toMul = hurwitzTorusCharacter x u := rfl

@[simp]
theorem coe_hurwitzTorusCharacter {I : Type*} [Fintype I]
    (x : HurwitzTorus I) (u : HurwitzCharacterLattice I) :
    (hurwitzTorusCharacter x u : ℂ) = ∏ i : I, (x i : ℂ) ^ u i := by
  simp [hurwitzTorusCharacter, hurwitzTorusCharacterHom]

@[simp]
theorem hurwitzTorusCharacter_zero {I : Type*} [Fintype I]
    (x : HurwitzTorus I) : hurwitzTorusCharacter x 0 = 1 := by
  exact congrArg Additive.toMul (map_zero (hurwitzTorusCharacterHom x))

@[simp]
theorem hurwitzTorusCharacter_add {I : Type*} [Fintype I]
    (x : HurwitzTorus I) (u v : HurwitzCharacterLattice I) :
    hurwitzTorusCharacter x (u + v) =
      hurwitzTorusCharacter x u * hurwitzTorusCharacter x v := by
  exact congrArg Additive.toMul (map_add (hurwitzTorusCharacterHom x) u v)

def hurwitzResonanceLattice {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : Submodule ℤ (HurwitzCharacterLattice I) :=
  (hurwitzTorusCharacterHom q).ker.toIntSubmodule

theorem mem_hurwitzResonanceLattice_iff {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (u : HurwitzCharacterLattice I) :
    u ∈ hurwitzResonanceLattice q ↔ hurwitzTorusCharacter q u = 1 := by
  change hurwitzTorusCharacterHom q u = 0 ↔ _
  rfl

def hurwitzLaurentEval {I : Type*} [Fintype I]
    (x : HurwitzTorus I) : HurwitzLaurentRing I →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (HurwitzCharacterLattice I)
    { toFun := fun u => (hurwitzTorusCharacter x u.toAdd : ℂ)
      map_one' := by simp
      map_mul' := by
        intro u v
        exact congrArg Units.val (hurwitzTorusCharacter_add x u.toAdd v.toAdd) }

@[simp]
theorem hurwitzLaurentEval_single {I : Type*} [Fintype I]
    (x : HurwitzTorus I) (u : HurwitzCharacterLattice I) (c : ℂ) :
    hurwitzLaurentEval x (AddMonoidAlgebra.single u c) =
      c * (hurwitzTorusCharacter x u : ℂ) := by
  simp [hurwitzLaurentEval]

def hurwitzTranslationGenerator {I : Type*} [Fintype I]
    (q : HurwitzTorus I) :
    Multiplicative (HurwitzCharacterLattice I) →* HurwitzLaurentRing I where
  toFun u := AddMonoidAlgebra.single u.toAdd (hurwitzTorusCharacter q u.toAdd : ℂ)
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' u v := by
    change AddMonoidAlgebra.single (u.toAdd + v.toAdd)
      (hurwitzTorusCharacter q (u.toAdd + v.toAdd) : ℂ) = _
    rw [AddMonoidAlgebra.single_mul_single]
    congr 1
    exact congrArg Units.val (hurwitzTorusCharacter_add q u.toAdd v.toAdd)

def hurwitzLaurentTranslation {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : HurwitzLaurentRing I →ₐ[ℂ] HurwitzLaurentRing I :=
  AddMonoidAlgebra.lift ℂ (HurwitzLaurentRing I) (HurwitzCharacterLattice I)
    (hurwitzTranslationGenerator q)

@[simp]
theorem hurwitzLaurentTranslation_single {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (u : HurwitzCharacterLattice I) (c : ℂ) :
    hurwitzLaurentTranslation q (AddMonoidAlgebra.single u c) =
      AddMonoidAlgebra.single u (c * (hurwitzTorusCharacter q u : ℂ)) := by
  simp [hurwitzLaurentTranslation, hurwitzTranslationGenerator, Algebra.smul_def]

theorem coeff_hurwitzLaurentTranslation {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (f : HurwitzLaurentRing I)
    (u : HurwitzCharacterLattice I) :
    (hurwitzLaurentTranslation q f).coeff u =
      f.coeff u * (hurwitzTorusCharacter q u : ℂ) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, add_mul]
  | single v c =>
      by_cases h : v = u
      · subst h
        simp
      · simp [h]

def hurwitzInvariantLaurentSubalgebra {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : Subalgebra ℂ (HurwitzLaurentRing I) :=
  AlgHom.equalizer (hurwitzLaurentTranslation q) (AlgHom.id ℂ _)

theorem mem_hurwitzInvariantLaurentSubalgebra_iff {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (f : HurwitzLaurentRing I) :
    f ∈ hurwitzInvariantLaurentSubalgebra q ↔
      ∀ u ∈ f.coeff.support, u ∈ hurwitzResonanceLattice q := by
  constructor
  · intro hf u hu
    change hurwitzLaurentTranslation q f = f at hf
    have hc := congrArg (fun g : HurwitzLaurentRing I => g.coeff u) hf
    rw [coeff_hurwitzLaurentTranslation] at hc
    have hcu : f.coeff u ≠ 0 := Finsupp.mem_support_iff.mp hu
    have hchar : (hurwitzTorusCharacter q u : ℂ) = 1 := by
      apply (mul_left_cancel₀ hcu)
      simpa using hc
    exact (mem_hurwitzResonanceLattice_iff q u).mpr
      (Units.ext hchar)
  · intro hf
    change hurwitzLaurentTranslation q f = f
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro u
    rw [coeff_hurwitzLaurentTranslation]
    by_cases hu : u ∈ f.coeff.support
    · rw [show (hurwitzTorusCharacter q u : ℂ) = 1 by
          exact congrArg Units.val (hf u hu), mul_one]
    · rw [Finsupp.notMem_support_iff.mp hu, zero_mul]

def hurwitzResonanceAlgebraInclusion {I : Type*} [Fintype I]
    (q : HurwitzTorus I) :
    AddMonoidAlgebra ℂ (hurwitzResonanceLattice q) →ₐ[ℂ] HurwitzLaurentRing I :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (hurwitzResonanceLattice q).subtype

theorem hurwitzResonanceAlgebraInclusion_injective {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : Function.Injective (hurwitzResonanceAlgebraInclusion q) := by
  exact AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

theorem hurwitzResonanceAlgebraInclusion_range {I : Type*} [Fintype I]
    (q : HurwitzTorus I) :
    (hurwitzResonanceAlgebraInclusion q).range =
      hurwitzInvariantLaurentSubalgebra q := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    rw [mem_hurwitzInvariantLaurentSubalgebra_iff]
    intro u hu
    have hrange : u ∈ Set.range ((hurwitzResonanceLattice q).subtype :
        hurwitzResonanceLattice q → HurwitzCharacterLattice I) := by
      change u ∈ (AddMonoidAlgebra.mapDomain
        ((hurwitzResonanceLattice q).subtype :
          hurwitzResonanceLattice q → HurwitzCharacterLattice I) g).coeff.support at hu
      have hsupp : (AddMonoidAlgebra.mapDomain
          ((hurwitzResonanceLattice q).subtype :
            hurwitzResonanceLattice q → HurwitzCharacterLattice I) g).coeff.support =
          Finset.image ((hurwitzResonanceLattice q).subtype :
            hurwitzResonanceLattice q → HurwitzCharacterLattice I) g.coeff.support := by
        rw [AddMonoidAlgebra.coeff_mapDomain,
          Finsupp.mapDomain_support_of_injective
            (hurwitzResonanceLattice q).subtype_injective]
      rw [hsupp] at hu
      rcases Finset.mem_image.mp hu with ⟨v, _hv, hvu⟩
      exact ⟨v, hvu⟩
    rcases hrange with ⟨v, rfl⟩
    exact v.2
  · intro hf
    rw [mem_hurwitzInvariantLaurentSubalgebra_iff] at hf
    let g : AddMonoidAlgebra ℂ (hurwitzResonanceLattice q) :=
      AddMonoidAlgebra.comapDomain Subtype.val Subtype.val_injective f
    refine ⟨g, ?_⟩
    change AddMonoidAlgebra.mapDomain
      ((hurwitzResonanceLattice q).subtype :
        hurwitzResonanceLattice q → HurwitzCharacterLattice I) g = f
    exact AddMonoidAlgebra.mapDomain_comapDomain (by
      intro u hu
      exact ⟨⟨u, hf u hu⟩, rfl⟩) Subtype.val_injective

noncomputable def hurwitzInvariantLaurentAlgEquiv {I : Type*} [Fintype I]
    (q : HurwitzTorus I) :
    AddMonoidAlgebra ℂ (hurwitzResonanceLattice q) ≃ₐ[ℂ]
      hurwitzInvariantLaurentSubalgebra q :=
  (AlgEquiv.ofInjective (hurwitzResonanceAlgebraInclusion q)
      (hurwitzResonanceAlgebraInclusion_injective q)).trans
    (Subalgebra.equivOfEq _ _ (hurwitzResonanceAlgebraInclusion_range q))

/-! ## Power-orbit closure in an arbitrary diagonalizable group -/

def addCharacterPowerHom {G : Type*} [AddCommGroup G]
    (χ : G →+ Additive ℂˣ) (n : ℕ) : Multiplicative G →* ℂ where
  toFun g := ((χ g.toAdd).toMul : ℂ) ^ n
  map_one' := by simp
  map_mul' g h := by
    change ((χ (g.toAdd + h.toAdd)).toMul : ℂ) ^ n = _
    rw [map_add]
    change (((χ g.toAdd).toMul : ℂ) * ((χ h.toAdd).toMul : ℂ)) ^ n = _
    exact mul_pow _ _ _

def addCharacterPowerEval {G : Type*} [AddCommGroup G]
    (χ : G →+ Additive ℂˣ) (n : ℕ) :
    AddMonoidAlgebra ℂ G →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ G (addCharacterPowerHom χ n)

@[simp]
theorem addCharacterPowerEval_single {G : Type*} [AddCommGroup G]
    (χ : G →+ Additive ℂˣ) (n : ℕ) (g : G) (c : ℂ) :
    addCharacterPowerEval χ n (AddMonoidAlgebra.single g c) =
      c * ((χ g).toMul : ℂ) ^ n := by
  simp [addCharacterPowerEval, addCharacterPowerHom]

/-- Distinct characters make the nonnegative power orbit Zariski dense in the diagonalizable
group with character lattice `G`. -/
theorem addMonoidAlgebra_powerOrbit_zero {G : Type*} [AddCommGroup G]
    (χ : G →+ Additive ℂˣ) (hχ : Function.Injective χ)
    (f : AddMonoidAlgebra ℂ G)
    (h : ∀ n : ℕ, addCharacterPowerEval χ n f = 0) : f = 0 := by
  classical
  let e := Fintype.equivFin f.coeff.support
  let b : Fin (Fintype.card f.coeff.support) → ℂ := fun k =>
    ((χ (e.symm k).1).toMul : ℂ)
  let c : Fin (Fintype.card f.coeff.support) → ℂ := fun k => f.coeff (e.symm k).1
  have hb : Function.Injective b := by
    intro k l hkl
    apply e.symm.injective
    apply Subtype.ext
    apply hχ
    apply Additive.toMul.injective
    exact Units.ext hkl
  have hsum : ∀ n : ℕ, ∑ k, c k * b k ^ n = 0 := by
    intro n
    have hn := h n
    rw [addCharacterPowerEval, AddMonoidAlgebra.lift_apply] at hn
    have hn' : ∑ d : f.coeff.support,
        f.coeff d.1 * ((χ d.1).toMul : ℂ) ^ n = 0 := by
      change (∑ d ∈ f.coeff.support,
        f.coeff d * ((χ d).toMul : ℂ) ^ n) = 0 at hn
      rw [← Finset.sum_attach] at hn
      exact hn
    have he := e.symm.sum_comp (fun d : f.coeff.support =>
      f.coeff d.1 * ((χ d.1).toMul : ℂ) ^ n)
    simpa [b, c] using he.trans hn'
  have hc := HurwitzJointOrbit.power_sum_coeff_zero hb hsum
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  by_cases hg : g ∈ f.coeff.support
  · let gs : f.coeff.support := ⟨g, hg⟩
    have hcg := congrFun hc (e gs)
    simpa [c, gs] using hcg
  · simp [Finsupp.notMem_support_iff.mp hg]

def addCharacterPowerGridHom {G : Type*} [AddCommGroup G] {L : ℕ}
    (χ : G →+ Additive ℂˣ) (m : Fin L → ℕ) :
    Multiplicative (Fin L → G) →* ℂ where
  toFun d := ∏ n : Fin L, ((χ (d.toAdd n)).toMul : ℂ) ^ m n
  map_one' := by simp
  map_mul' d e := by
    change (∏ n : Fin L, ((χ (d.toAdd n + e.toAdd n)).toMul : ℂ) ^ m n) = _
    simp_rw [map_add]
    change (∏ n : Fin L,
      (((χ (d.toAdd n)).toMul : ℂ) * ((χ (e.toAdd n)).toMul : ℂ)) ^ m n) = _
    simp_rw [mul_pow]
    exact Finset.prod_mul_distrib

def addCharacterPowerGridEval {G : Type*} [AddCommGroup G] {L : ℕ}
    (χ : G →+ Additive ℂˣ) (m : Fin L → ℕ) :
    AddMonoidAlgebra ℂ (Fin L → G) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin L → G) (addCharacterPowerGridHom χ m)

noncomputable def addCharacterGridNodeFinset {G : Type*} [AddCommGroup G] {L : ℕ}
    (f : AddMonoidAlgebra ℂ (Fin L → G)) : Finset G := by
  classical
  exact f.coeff.support.biUnion fun d => Finset.univ.image d

theorem mem_addCharacterGridNodeFinset {G : Type*} [AddCommGroup G] {L : ℕ}
    (f : AddMonoidAlgebra ℂ (Fin L → G)) {d : Fin L → G}
    (hd : d ∈ f.coeff.support) (n : Fin L) :
    d n ∈ addCharacterGridNodeFinset f := by
  classical
  rw [addCharacterGridNodeFinset, Finset.mem_biUnion]
  exact ⟨d, hd, Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩⟩

noncomputable def addCharacterSupportNodeTuple {G : Type*} [AddCommGroup G] {L : ℕ}
    (f : AddMonoidAlgebra ℂ (Fin L → G)) (d : Fin L → G)
    (hd : d ∈ f.coeff.support) : Fin L → addCharacterGridNodeFinset f :=
  fun n => ⟨d n, mem_addCharacterGridNodeFinset f hd n⟩

theorem addCharacterGrid_sum_eq_finsuppSum {G : Type*} [AddCommGroup G] {L : ℕ}
    (χ : G →+ Additive ℂˣ) (f : AddMonoidAlgebra ℂ (Fin L → G))
    (m : Fin L → ℕ) :
    (∑ a : Fin L → addCharacterGridNodeFinset f,
      f.coeff (fun n => (a n).1) *
        ∏ n : Fin L, ((χ (a n).1).toMul : ℂ) ^ m n) =
      f.coeff.sum fun d c => c *
        ∏ n : Fin L, ((χ (d n)).toMul : ℂ) ^ m n := by
  classical
  let emb : (Fin L → addCharacterGridNodeFinset f) → (Fin L → G) :=
    fun a n => (a n).1
  have hemb : Function.Injective emb := by
    intro a b hab
    funext n
    exact Subtype.ext (congrFun hab n)
  let nodes : Finset (Fin L → G) := Finset.univ.image emb
  let term : (Fin L → G) → ℂ := fun d =>
    f.coeff d * ∏ n : Fin L, ((χ (d n)).toMul : ℂ) ^ m n
  have hsupp : f.coeff.support ⊆ nodes := by
    intro d hd
    change d ∈ Finset.univ.image emb
    rw [Finset.mem_image]
    refine ⟨addCharacterSupportNodeTuple f d hd, Finset.mem_univ _, ?_⟩
    rfl
  have hzero : ∀ d ∈ nodes, d ∉ f.coeff.support → term d = 0 := by
    intro d _ hd
    simp [term, Finsupp.notMem_support_iff.mp hd]
  calc
    _ = ∑ a : Fin L → addCharacterGridNodeFinset f, term (emb a) := by rfl
    _ = ∑ d ∈ nodes, term d := by
      change (∑ a : Fin L → addCharacterGridNodeFinset f, term (emb a)) =
        ∑ d ∈ Finset.univ.image emb, term d
      rw [Finset.sum_image]
      exact fun a _ b _ hab => hemb hab
    _ = ∑ d ∈ f.coeff.support, term d :=
      (Finset.sum_subset hsupp hzero).symm
    _ = _ := by rfl

/-- Tensor Vandermonde density for an arbitrary character lattice. Independent nonnegative
column times make the product of a character-injective cyclic orbit Zariski dense. -/
theorem addMonoidAlgebra_powerGrid_zero {G : Type*} [AddCommGroup G]
    (χ : G →+ Additive ℂˣ) (hχ : Function.Injective χ) :
    ∀ (L : ℕ) (f : AddMonoidAlgebra ℂ (Fin L → G)),
      (∀ m : Fin L → ℕ, addCharacterPowerGridEval χ m f = 0) → f = 0 := by
  intro L f h
  classical
  let V := addCharacterGridNodeFinset f
  let qV : V → ℂ := fun v => ((χ v.1).toMul : ℂ)
  let cV : (Fin L → V) → ℂ := fun a => f.coeff (fun n => (a n).1)
  have hqV : Function.Injective qV := by
    intro a b hab
    apply Subtype.ext
    apply hχ
    apply Additive.toMul.injective
    exact Units.ext hab
  have hsum : ∀ m : Fin L → ℕ,
      ∑ a : Fin L → V, cV a * ∏ n : Fin L, qV (a n) ^ m n = 0 := by
    intro m
    have hm := h m
    rw [addCharacterPowerGridEval, AddMonoidAlgebra.lift_apply] at hm
    change f.coeff.sum (fun d c => c *
      ∏ n : Fin L, ((χ (d n)).toMul : ℂ) ^ m n) = 0 at hm
    rw [← addCharacterGrid_sum_eq_finsuppSum χ f m] at hm
    exact hm
  have hc := HurwitzJointOrbit.tensor_power_sum_coeff_zero qV hqV L cV hsum
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro d
  by_cases hd : d ∈ f.coeff.support
  · have hcd := congrFun hc (addCharacterSupportNodeTuple f d hd)
    simpa [cV, addCharacterSupportNodeTuple] using hcd
  · simp [Finsupp.notMem_support_iff.mp hd]

/-- Actual common-loop `ℤ`-translation `m • x = q^m x` on the marked torus. -/
@[reducible]
def hurwitzCommonLoopAction {I : Type*} (q : HurwitzTorus I) :
    AddAction ℤ (HurwitzTorus I) where
  vadd m x := fun i => q i ^ m * x i
  zero_vadd x := by
    funext i
    change q i ^ (0 : ℤ) * x i = x i
    simp
  add_vadd m n x := by
    funext i
    change q i ^ (m + n) * x i = q i ^ m * (q i ^ n * x i)
    rw [zpow_add]
    ac_rfl

theorem hurwitzCommonLoopAction_apply {I : Type*} (q x : HurwitzTorus I) (m : ℤ) :
    letI := hurwitzCommonLoopAction q
    m +ᵥ x = fun i => q i ^ m * x i := rfl

@[reducible]
def hurwitzCommonLoopMulAction {I : Type*} (q : HurwitzTorus I) :
    MulAction (Multiplicative ℤ) (HurwitzTorus I) where
  smul m x := fun i => q i ^ m.toAdd * x i
  one_smul x := by
    funext i
    change q i ^ (0 : ℤ) * x i = x i
    simp
  mul_smul m n x := by
    funext i
    change q i ^ (m.toAdd + n.toAdd) * x i =
      q i ^ m.toAdd * (q i ^ n.toAdd * x i)
    rw [zpow_add]
    ac_rfl

/-- Groupoid presentation of the marked quotient lawstack `[T / ℤ]`. -/
abbrev HurwitzMonodromyLawstack {I : Type*} (q : HurwitzTorus I) :=
  @CategoryTheory.ActionCategory (Multiplicative ℤ) inferInstance
    (HurwitzTorus I) (hurwitzCommonLoopMulAction q)

def hurwitzPowerPoint {I : Type*} (q : HurwitzTorus I) (n : ℕ) : HurwitzTorus I :=
  fun i => q i ^ n

theorem hurwitzTorusCharacter_powerPoint {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (n : ℕ) (u : HurwitzCharacterLattice I) :
    hurwitzTorusCharacter (hurwitzPowerPoint q n) u =
      hurwitzTorusCharacter q u ^ n := by
  unfold hurwitzTorusCharacter hurwitzTorusCharacterHom hurwitzPowerPoint
  change (∏ i, (q i ^ n) ^ u i) = (∏ i, q i ^ u i) ^ n
  calc
    _ = ∏ i, (q i ^ u i) ^ n := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    _ = _ := Finset.prod_pow Finset.univ n (fun i => q i ^ u i)

/-- Literal affine Zariski closure: common zero locus in the complex torus of every Laurent
polynomial vanishing on all nonnegative powers of `q`. -/
def hurwitzMonodromyZariskiClosure {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : Set (HurwitzTorus I) :=
  {x | ∀ f : HurwitzLaurentRing I,
    (∀ n : ℕ, hurwitzLaurentEval (hurwitzPowerPoint q n) f = 0) →
      hurwitzLaurentEval x f = 0}

/-- Character annihilator of the resonance lattice. -/
def hurwitzResonanceAnnihilator {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : Set (HurwitzTorus I) :=
  {x | ∀ u ∈ hurwitzResonanceLattice q, hurwitzTorusCharacter x u = 1}

def hurwitzQuotientCharacter {I : Type*} [Fintype I]
    (q : HurwitzTorus I) :
    (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q) →+ Additive ℂˣ :=
  (((hurwitzTorusCharacterHom q).toIntLinearMap.range.subtype).comp
      (hurwitzTorusCharacterHom q).toIntLinearMap.quotKerEquivRange.toLinearMap).toAddMonoidHom

@[simp]
theorem hurwitzQuotientCharacter_mk {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (u : HurwitzCharacterLattice I) :
    hurwitzQuotientCharacter q ((hurwitzResonanceLattice q).mkQ u) =
      hurwitzTorusCharacterHom q u := by
  rfl

theorem hurwitzQuotientCharacter_injective {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : Function.Injective (hurwitzQuotientCharacter q) := by
  exact (hurwitzTorusCharacterHom q).toIntLinearMap.range.subtype_injective.comp
    (hurwitzTorusCharacterHom q).toIntLinearMap.quotKerEquivRange.injective

def hurwitzQuotientPush {I : Type*} [Fintype I]
    (q : HurwitzTorus I) :
    HurwitzLaurentRing I →ₐ[ℂ]
      AddMonoidAlgebra ℂ (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (hurwitzResonanceLattice q).mkQ.toAddMonoidHom

theorem hurwitzQuotientPowerEval_push {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (n : ℕ) (f : HurwitzLaurentRing I) :
    addCharacterPowerEval (hurwitzQuotientCharacter q) n (hurwitzQuotientPush q f) =
      hurwitzLaurentEval (hurwitzPowerPoint q n) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single u c =>
      rw [show hurwitzQuotientPush q (AddMonoidAlgebra.single u c) =
          AddMonoidAlgebra.single ((hurwitzResonanceLattice q).mkQ u) c by
            simp [hurwitzQuotientPush],
        addCharacterPowerEval_single, hurwitzQuotientCharacter_mk,
        hurwitzLaurentEval_single, hurwitzTorusCharacter_powerPoint]
      rfl

def hurwitzAnnihilatorQuotientCharacter {I : Type*} [Fintype I]
    {q x : HurwitzTorus I} (hx : x ∈ hurwitzResonanceAnnihilator q) :
    (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q) →+ Additive ℂˣ :=
  (hurwitzResonanceLattice q).liftQ (hurwitzTorusCharacterHom x).toIntLinearMap
    (by
      intro u hu
      change hurwitzTorusCharacterHom x u = 0
      apply Additive.toMul.injective
      exact hx u hu)
    |>.toAddMonoidHom

@[simp]
theorem hurwitzAnnihilatorQuotientCharacter_mk {I : Type*} [Fintype I]
    {q x : HurwitzTorus I} (hx : x ∈ hurwitzResonanceAnnihilator q)
    (u : HurwitzCharacterLattice I) :
    hurwitzAnnihilatorQuotientCharacter hx ((hurwitzResonanceLattice q).mkQ u) =
      hurwitzTorusCharacterHom x u := by
  rfl

theorem hurwitzAnnihilatorEval_push {I : Type*} [Fintype I]
    {q x : HurwitzTorus I} (hx : x ∈ hurwitzResonanceAnnihilator q)
    (f : HurwitzLaurentRing I) :
    AddMonoidAlgebra.lift ℂ ℂ _
        { toFun := fun u => ((hurwitzAnnihilatorQuotientCharacter hx u.toAdd).toMul : ℂ)
          map_one' := by simp
          map_mul' := by
            intro u v
            change ((hurwitzAnnihilatorQuotientCharacter hx
              (u.toAdd + v.toAdd)).toMul : ℂ) = _
            rw [map_add]
            rfl }
        (hurwitzQuotientPush q f) =
      hurwitzLaurentEval x f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single u c =>
      rw [show hurwitzQuotientPush q (AddMonoidAlgebra.single u c) =
          AddMonoidAlgebra.single ((hurwitzResonanceLattice q).mkQ u) c by
            simp [hurwitzQuotientPush],
        AddMonoidAlgebra.lift_single]
      rw [hurwitzLaurentEval_single]
      simp only [Algebra.smul_def]
      change c * ((hurwitzAnnihilatorQuotientCharacter hx
          ((hurwitzResonanceLattice q).mkQ u)).toMul : ℂ) =
        c * (hurwitzTorusCharacter x u : ℂ)
      rw [hurwitzAnnihilatorQuotientCharacter_mk]
      rfl

/-- The literal Zariski closure of the cyclic monodromy orbit is exactly the subtorus (possibly
disconnected) annihilated by the resonance lattice. -/
theorem hurwitzMonodromyZariskiClosure_eq_resonanceAnnihilator
    {I : Type*} [Fintype I] (q : HurwitzTorus I) :
    hurwitzMonodromyZariskiClosure q = hurwitzResonanceAnnihilator q := by
  ext x
  constructor
  · intro hx u hu
    let f : HurwitzLaurentRing I :=
      AddMonoidAlgebra.single u 1 - AddMonoidAlgebra.single 0 1
    have hvan : ∀ n : ℕ, hurwitzLaurentEval (hurwitzPowerPoint q n) f = 0 := by
      intro n
      simp [f, hurwitzTorusCharacter_powerPoint,
        (mem_hurwitzResonanceLattice_iff q u).mp hu]
    have hzero := hx f hvan
    simp [f] at hzero
    apply Units.ext
    rw [coe_hurwitzTorusCharacter]
    exact sub_eq_zero.mp hzero
  · intro hx f hf
    have hpush : hurwitzQuotientPush q f = 0 := by
      apply addMonoidAlgebra_powerOrbit_zero (hurwitzQuotientCharacter q)
        (hurwitzQuotientCharacter_injective q)
      intro n
      rw [hurwitzQuotientPowerEval_push]
      exact hf n
    rw [← hurwitzAnnihilatorEval_push hx, hpush, map_zero]

/-! ## Independent branch-loop grids -/

def hurwitzProductTorusCharacterHom {I : Type*} [Fintype I] {L : ℕ}
    (x : Fin L → HurwitzTorus I) :
    (Fin L → HurwitzCharacterLattice I) →+ Additive ℂˣ where
  toFun d := Additive.ofMul (∏ n : Fin L, hurwitzTorusCharacter (x n) (d n))
  map_zero' := by simp
  map_add' d e := by
    change Additive.ofMul
        (∏ n : Fin L, hurwitzTorusCharacter (x n) (d n + e n)) =
      Additive.ofMul ((∏ n : Fin L, hurwitzTorusCharacter (x n) (d n)) *
        ∏ n : Fin L, hurwitzTorusCharacter (x n) (e n))
    congr 1
    simp_rw [hurwitzTorusCharacter_add]
    exact Finset.prod_mul_distrib

def hurwitzProductLaurentEval {I : Type*} [Fintype I] {L : ℕ}
    (x : Fin L → HurwitzTorus I) :
    AddMonoidAlgebra ℂ (Fin L → HurwitzCharacterLattice I) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ _
    { toFun := fun d => ((hurwitzProductTorusCharacterHom x d.toAdd).toMul : ℂ)
      map_one' := by simp
      map_mul' := by
        intro d e
        change ((hurwitzProductTorusCharacterHom x (d.toAdd + e.toAdd)).toMul : ℂ) = _
        rw [map_add]
        rfl }

@[simp]
theorem hurwitzProductLaurentEval_single {I : Type*} [Fintype I] {L : ℕ}
    (x : Fin L → HurwitzTorus I) (d : Fin L → HurwitzCharacterLattice I) (c : ℂ) :
    hurwitzProductLaurentEval x (AddMonoidAlgebra.single d c) =
      c * ∏ n : Fin L, (hurwitzTorusCharacter (x n) (d n) : ℂ) := by
  simp [hurwitzProductLaurentEval, hurwitzProductTorusCharacterHom]

@[simp]
theorem addCharacterPowerGridEval_single {G : Type*} [AddCommGroup G] {L : ℕ}
    (χ : G →+ Additive ℂˣ) (m : Fin L → ℕ) (d : Fin L → G) (c : ℂ) :
    addCharacterPowerGridEval χ m (AddMonoidAlgebra.single d c) =
      c * ∏ n : Fin L, ((χ (d n)).toMul : ℂ) ^ m n := by
  simp [addCharacterPowerGridEval, addCharacterPowerGridHom]

def hurwitzIndependentPowerGridPoint {I : Type*} {L : ℕ}
    (q : HurwitzTorus I) (m : Fin L → ℕ) : Fin L → HurwitzTorus I :=
  fun n => hurwitzPowerPoint q (m n)

theorem hurwitzProductEval_independentPowerGrid {I : Type*} [Fintype I] {L : ℕ}
    (q : HurwitzTorus I) (m : Fin L → ℕ)
    (f : AddMonoidAlgebra ℂ (Fin L → HurwitzCharacterLattice I)) :
    hurwitzProductLaurentEval (hurwitzIndependentPowerGridPoint q m) f =
      addCharacterPowerGridEval (hurwitzTorusCharacterHom q) m f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single d c =>
      rw [hurwitzProductLaurentEval_single, addCharacterPowerGridEval_single]
      congr 1
      apply Finset.prod_congr rfl
      intro n _
      change (hurwitzTorusCharacter (hurwitzPowerPoint q (m n)) (d n) : ℂ) = _
      rw [hurwitzTorusCharacter_powerPoint]
      rfl

/-- Literal affine Zariski closure of the independent branch-loop grid. -/
def hurwitzIndependentPowerGridZariskiClosure {I : Type*} [Fintype I] (L : ℕ)
    (q : HurwitzTorus I) : Set (Fin L → HurwitzTorus I) :=
  {x | ∀ f : AddMonoidAlgebra ℂ (Fin L → HurwitzCharacterLattice I),
    (∀ m : Fin L → ℕ,
      hurwitzProductLaurentEval (hurwitzIndependentPowerGridPoint q m) f = 0) →
    hurwitzProductLaurentEval x f = 0}

def hurwitzProductResonanceAnnihilator {I : Type*} [Fintype I] (L : ℕ)
    (q : HurwitzTorus I) : Set (Fin L → HurwitzTorus I) :=
  {x | ∀ n, x n ∈ hurwitzResonanceAnnihilator q}

def hurwitzProductQuotientMap {I : Type*} [Fintype I] (L : ℕ)
    (q : HurwitzTorus I) :
    (Fin L → HurwitzCharacterLattice I) →+
      (Fin L → (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q)) where
  toFun d n := (hurwitzResonanceLattice q).mkQ (d n)
  map_zero' := by ext; simp
  map_add' d e := by ext; simp

def hurwitzProductQuotientPush {I : Type*} [Fintype I] (L : ℕ)
    (q : HurwitzTorus I) :
    AddMonoidAlgebra ℂ (Fin L → HurwitzCharacterLattice I) →ₐ[ℂ]
      AddMonoidAlgebra ℂ
        (Fin L → (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q)) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (hurwitzProductQuotientMap L q)

theorem hurwitzProductQuotientPowerEval_push {I : Type*} [Fintype I] (L : ℕ)
    (q : HurwitzTorus I) (m : Fin L → ℕ)
    (f : AddMonoidAlgebra ℂ (Fin L → HurwitzCharacterLattice I)) :
    addCharacterPowerGridEval (hurwitzQuotientCharacter q) m
        (hurwitzProductQuotientPush L q f) =
      hurwitzProductLaurentEval (hurwitzIndependentPowerGridPoint q m) f := by
  rw [hurwitzProductEval_independentPowerGrid]
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single d c =>
      rw [show hurwitzProductQuotientPush L q (AddMonoidAlgebra.single d c) =
          AddMonoidAlgebra.single (hurwitzProductQuotientMap L q d) c by
            simp [hurwitzProductQuotientPush],
        addCharacterPowerGridEval_single]
      rw [addCharacterPowerGridEval_single]
      congr 1

def hurwitzProductAnnihilatorQuotientCharacter {I : Type*} [Fintype I] {L : ℕ}
    {q : HurwitzTorus I} {x : Fin L → HurwitzTorus I}
    (hx : x ∈ hurwitzProductResonanceAnnihilator L q) :
    (Fin L → (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q)) →+
      Additive ℂˣ where
  toFun d := Additive.ofMul (∏ n : Fin L,
    ((hurwitzAnnihilatorQuotientCharacter (hx n) (d n)).toMul : ℂˣ))
  map_zero' := by simp
  map_add' d e := by
    change Additive.ofMul (∏ n : Fin L,
        ((hurwitzAnnihilatorQuotientCharacter (hx n)) (d n + e n)).toMul) =
      Additive.ofMul ((∏ n : Fin L,
        ((hurwitzAnnihilatorQuotientCharacter (hx n)) (d n)).toMul) *
        ∏ n : Fin L,
          ((hurwitzAnnihilatorQuotientCharacter (hx n)) (e n)).toMul)
    congr 1
    simp_rw [map_add]
    change (∏ n : Fin L,
        ((hurwitzAnnihilatorQuotientCharacter (hx n) (d n)).toMul *
          (hurwitzAnnihilatorQuotientCharacter (hx n) (e n)).toMul)) = _
    exact Finset.prod_mul_distrib

theorem hurwitzProductAnnihilatorEval_push {I : Type*} [Fintype I] {L : ℕ}
    {q : HurwitzTorus I} {x : Fin L → HurwitzTorus I}
    (hx : x ∈ hurwitzProductResonanceAnnihilator L q)
    (f : AddMonoidAlgebra ℂ (Fin L → HurwitzCharacterLattice I)) :
    addCharacterPowerEval (hurwitzProductAnnihilatorQuotientCharacter hx) 1
        (hurwitzProductQuotientPush L q f) =
      hurwitzProductLaurentEval x f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single d c =>
      rw [show hurwitzProductQuotientPush L q (AddMonoidAlgebra.single d c) =
          AddMonoidAlgebra.single (hurwitzProductQuotientMap L q d) c by
            simp [hurwitzProductQuotientPush],
        addCharacterPowerEval_single, hurwitzProductLaurentEval_single]
      simp only [pow_one]
      congr 1
      simp only [hurwitzProductAnnihilatorQuotientCharacter,
        hurwitzProductQuotientMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [additiveComplexUnits_toMul_ofMul]
      rw [Units.coe_prod]
      apply Finset.prod_congr rfl
      intro n _
      rw [hurwitzAnnihilatorQuotientCharacter_mk]
      exact congrArg Units.val (hurwitzTorusCharacterHom_toMul (x n) (d n))

/-- Independent branch-loop grid closure is the Cartesian power of the common-loop closure. -/
theorem hurwitzIndependentPowerGridZariskiClosure_eq_pi
    {I : Type*} [Fintype I] (L : ℕ) (q : HurwitzTorus I) :
    hurwitzIndependentPowerGridZariskiClosure L q =
      {x | ∀ n, x n ∈ hurwitzMonodromyZariskiClosure q} := by
  rw [hurwitzMonodromyZariskiClosure_eq_resonanceAnnihilator]
  change hurwitzIndependentPowerGridZariskiClosure L q =
    hurwitzProductResonanceAnnihilator L q
  ext x
  constructor
  · intro hx n u hu
    let d : Fin L → HurwitzCharacterLattice I := Pi.single n u
    let f : AddMonoidAlgebra ℂ (Fin L → HurwitzCharacterLattice I) :=
      AddMonoidAlgebra.single d 1 - AddMonoidAlgebra.single 0 1
    have hvan : ∀ m : Fin L → ℕ,
        hurwitzProductLaurentEval (hurwitzIndependentPowerGridPoint q m) f = 0 := by
      intro m
      rw [hurwitzProductEval_independentPowerGrid]
      rw [map_sub, addCharacterPowerGridEval_single,
        addCharacterPowerGridEval_single, sub_eq_zero]
      simp only [one_mul, Pi.zero_apply, map_zero]
      simp only [additiveComplexUnits_toMul_zero, Units.val_one, one_pow,
        Finset.prod_const_one]
      change (∏ r : Fin L,
          ((hurwitzTorusCharacterHom q (d r)).toMul : ℂ) ^ m r) = 1
      rw [Finset.prod_eq_single n]
      · simp [d, (mem_hurwitzResonanceLattice_iff q u).mp hu]
      · intro r _ hr
        simp [d, hr]
      · intro hn
        exact (hn (Finset.mem_univ n)).elim
    have hzero := hx f hvan
    rw [map_sub, hurwitzProductLaurentEval_single,
      hurwitzProductLaurentEval_single, sub_eq_zero] at hzero
    simp only [Pi.zero_apply, hurwitzTorusCharacter_zero, Units.val_one,
      Finset.prod_const_one, mul_one, one_mul] at hzero
    rw [Finset.prod_eq_single n] at hzero
    · have hdn : d n = u := by simp [d]
      rw [hdn] at hzero
      exact Units.ext hzero
    · intro r _ hr
      simp [d, hr]
    · intro hn
      exact (hn (Finset.mem_univ n)).elim
  · intro hx f hf
    have hpush : hurwitzProductQuotientPush L q f = 0 := by
      apply addMonoidAlgebra_powerGrid_zero (hurwitzQuotientCharacter q)
        (hurwitzQuotientCharacter_injective q) L
      intro m
      rw [hurwitzProductQuotientPowerEval_push]
      exact hf m
    rw [← hurwitzProductAnnihilatorEval_push hx, hpush, map_zero]

/-! ## Separation, full closure, and the affine observer point -/

def hurwitzFinsuppDifference {I : Type*} [Fintype I]
    (d e : I →₀ ℕ) : HurwitzCharacterLattice I :=
  fun i => (d i : ℤ) - (e i : ℤ)

theorem hurwitzTorusCharacter_finsuppDifference {I : Type*} [Fintype I]
    (q : HurwitzTorus I) (d e : I →₀ ℕ) :
    (hurwitzTorusCharacter q (hurwitzFinsuppDifference d e) : ℂ) =
      HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ)) d /
        HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ)) e := by
  classical
  rw [coe_hurwitzTorusCharacter]
  change (∏ i : I, (q i : ℂ) ^ ((d i : ℤ) - (e i : ℤ))) = _
  rw [HurwitzJointOrbit.monomialValue, HurwitzJointOrbit.monomialValue,
    Finsupp.prod_fintype, Finsupp.prod_fintype]
  · calc
      (∏ i : I, (q i : ℂ) ^ ((d i : ℤ) - (e i : ℤ))) =
          ∏ i : I, ((q i : ℂ) ^ (d i : ℤ) / (q i : ℂ) ^ (e i : ℤ)) := by
            apply Finset.prod_congr rfl
            intro i _
            rw [zpow_sub₀ (Units.ne_zero (q i))]
      _ = (∏ i : I, (q i : ℂ) ^ (d i : ℤ)) /
          ∏ i : I, (q i : ℂ) ^ (e i : ℤ) := by
            exact (Finset.prod_div_distrib (s := (Finset.univ : Finset I))
              (fun i : I => (q i : ℂ) ^ (d i : ℤ))
              (fun i : I => (q i : ℂ) ^ (e i : ℤ)))
      _ = _ := by simp only [zpow_natCast]
  · simp
  · simp

theorem hurwitzResonanceLattice_eq_bot_iff_monomialValue_injective
    {I : Type*} [Fintype I] [DecidableEq I] (q : HurwitzTorus I) :
    hurwitzResonanceLattice q = ⊥ ↔
      Function.Injective
        (HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ))) := by
  constructor
  · intro hR d e hde
    let u := hurwitzFinsuppDifference d e
    have hmono_ne : HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ)) e ≠ 0 := by
      unfold HurwitzJointOrbit.monomialValue
      exact Finsupp.prod_ne_zero_iff.mpr (by
        intro i _
        exact pow_ne_zero _ (Units.ne_zero (q i)))
    have hu : u ∈ hurwitzResonanceLattice q := by
      rw [mem_hurwitzResonanceLattice_iff]
      apply Units.ext
      rw [hurwitzTorusCharacter_finsuppDifference, hde, div_self hmono_ne]
      rfl
    have hu0 : u = 0 := by
      rw [hR] at hu
      exact hu
    apply Finsupp.ext
    intro i
    have hi := congrFun hu0 i
    change (d i : ℤ) - (e i : ℤ) = 0 at hi
    exact_mod_cast sub_eq_zero.mp hi
  · intro hmono
    apply le_antisymm
    · intro u hu
      let d : I →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (u i).toNat
      let e : I →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (-u i).toNat
      have hueq : u = hurwitzFinsuppDifference d e := by
        funext i
        simp only [hurwitzFinsuppDifference, d, e]
        exact (Int.toNat_sub_toNat_neg (u i)).symm
      have hchar : (hurwitzTorusCharacter q (hurwitzFinsuppDifference d e) : ℂ) = 1 := by
        rw [← hueq]
        exact congrArg Units.val ((mem_hurwitzResonanceLattice_iff q u).mp hu)
      rw [hurwitzTorusCharacter_finsuppDifference] at hchar
      have hne : HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ)) e ≠ 0 :=
        by
          unfold HurwitzJointOrbit.monomialValue
          exact Finsupp.prod_ne_zero_iff.mpr (by
            intro i _
            exact pow_ne_zero _ (Units.ne_zero (q i)))
      have hde : HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ)) d =
          HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ)) e := by
        apply (div_eq_one_iff_eq hne).mp hchar
      have de := hmono hde
      rw [hueq, de]
      funext i
      simp [hurwitzFinsuppDifference]
    · exact bot_le

theorem exists_hurwitzTorusCharacter_ne_one {I : Type*} [Fintype I]
    (u : HurwitzCharacterLattice I) (hu : u ≠ 0) :
    ∃ x : HurwitzTorus I, hurwitzTorusCharacter x u ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  let two : ℂˣ := Units.mk0 2 (by norm_num)
  let x : HurwitzTorus I := Function.update (fun _ => 1) i two
  refine ⟨x, ?_⟩
  intro hchar
  have hpow : ((2 : ℂ) ^ u i) = 1 := by
    have hc := congrArg Units.val hchar
    unfold hurwitzTorusCharacter hurwitzTorusCharacterHom at hc
    change (∏ j : I, ((x j) ^ u j : ℂˣ)) = 1 at hchar
    have hunit : (∏ j : I, (x j) ^ u j) = two ^ u i := by
      rw [Finset.prod_eq_single i]
      · simp [x]
      · intro j _ hji
        simp [x, hji]
      · intro hbad
        exact (hbad (Finset.mem_univ i)).elim
    rw [hunit] at hchar
    simpa [two] using congrArg Units.val hchar
  have hreal : (2 : ℝ) ^ u i = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_zpow]
    norm_num
    exact hpow
  exact hi ((zpow_eq_one_iff_right₀ (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (2 : ℝ) ≠ 1)).mp hreal)

theorem hurwitzMonodromyZariskiClosure_eq_univ_iff
    {I : Type*} [Fintype I] (q : HurwitzTorus I) :
    hurwitzMonodromyZariskiClosure q = Set.univ ↔
      hurwitzResonanceLattice q = ⊥ := by
  rw [hurwitzMonodromyZariskiClosure_eq_resonanceAnnihilator]
  constructor
  · intro hfull
    apply le_antisymm
    · intro u hu
      by_contra hu0
      obtain ⟨x, hx⟩ := exists_hurwitzTorusCharacter_ne_one u hu0
      have hxann : x ∈ hurwitzResonanceAnnihilator q := by
        rw [hfull]
        trivial
      exact hx (hxann u hu)
    · exact bot_le
  · intro hR
    ext x
    simp only [Set.mem_univ, iff_true]
    intro u hu
    rw [hR] at hu
    subst u
    simp

def hurwitzAffineObserverIsPoint {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : Prop :=
  hurwitzInvariantLaurentSubalgebra q = ⊥

theorem hurwitzAffineObserverIsPoint_iff {I : Type*} [Fintype I]
    (q : HurwitzTorus I) :
    hurwitzAffineObserverIsPoint q ↔ hurwitzResonanceLattice q = ⊥ := by
  constructor
  · intro hpoint
    apply le_antisymm
    · intro u hu
      have hinv : AddMonoidAlgebra.single u (1 : ℂ) ∈
          hurwitzInvariantLaurentSubalgebra q := by
        rw [mem_hurwitzInvariantLaurentSubalgebra_iff]
        intro v hv
        have hvu : v = u := by simpa using hv
        simpa [hvu] using hu
      rw [hpoint, Algebra.mem_bot] at hinv
      rcases hinv with ⟨c, hc⟩
      by_contra hu0
      have hcoeff := congrArg
        (fun f : HurwitzLaurentRing I => f.coeff u) hc
      have hu0' : u ≠ 0 := by simpa using hu0
      have : (0 : ℂ) = 1 := by
        simp [hu0'] at hcoeff
      exact zero_ne_one this
    · exact bot_le
  · intro hR
    ext f
    constructor
    · intro hf
      rw [mem_hurwitzInvariantLaurentSubalgebra_iff] at hf
      rw [Algebra.mem_bot]
      refine ⟨f.coeff 0, ?_⟩
      apply AddMonoidAlgebra.coeff_injective
      apply Finsupp.ext
      intro u
      by_cases hu0 : u = 0
      · subst u
        simp
      · have hnot : u ∉ f.coeff.support := by
          intro hu
          have hur := hf u hu
          rw [hR] at hur
          exact hu0 hur
        simp [Finsupp.notMem_support_iff.mp hnot, hu0]
    · intro hf
      exact (show (⊥ : Subalgebra ℂ (HurwitzLaurentRing I)) ≤
        hurwitzInvariantLaurentSubalgebra q from bot_le) hf

/-- Exact equivalence package for the published monodromy-character sufficient chamber. -/
theorem hurwitzMonodromyCharacterSeparation_equivalences
    {I : Type*} [Fintype I] [DecidableEq I] (q : HurwitzTorus I) :
    Function.Injective
          (HurwitzJointOrbit.monomialValue (fun i => (q i : ℂ))) ↔
      hurwitzResonanceLattice q = ⊥ ∧
      hurwitzMonodromyZariskiClosure q = Set.univ ∧
      hurwitzAffineObserverIsPoint q := by
  rw [← hurwitzResonanceLattice_eq_bot_iff_monomialValue_injective,
    hurwitzMonodromyZariskiClosure_eq_univ_iff,
    hurwitzAffineObserverIsPoint_iff]
  tauto


noncomputable def hurwitzMonodromyClosureDimension {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : ℕ :=
  Module.finrank ℤ (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q)

noncomputable def hurwitzResonanceRank {I : Type*} [Fintype I]
    (q : HurwitzTorus I) : ℕ :=
  Module.finrank ℤ (hurwitzResonanceLattice q)

theorem hurwitzMonodromyClosureDimension_add_resonanceRank
    {I : Type*} [Fintype I] (q : HurwitzTorus I) :
    hurwitzMonodromyClosureDimension q + hurwitzResonanceRank q = Fintype.card I := by
  change Module.finrank ℤ (HurwitzCharacterLattice I ⧸ hurwitzResonanceLattice q) +
      Module.finrank ℤ (hurwitzResonanceLattice q) = Fintype.card I
  calc
    _ = Module.finrank ℤ (HurwitzCharacterLattice I) :=
      (hurwitzResonanceLattice q).finrank_quotient_add_finrank
    _ = Fintype.card I := Module.finrank_fintype_fun_eq_card ℤ

theorem hurwitzMonodromyClosureDimension_lt_card_of_resonance
    {I : Type*} [Fintype I] (q : HurwitzTorus I)
    (hR : 0 < hurwitzResonanceRank q) :
    hurwitzMonodromyClosureDimension q < Fintype.card I := by
  have hsum := hurwitzMonodromyClosureDimension_add_resonanceRank q
  omega

/-- The actual common-loop Hurwitz monodromy point `exp (-2πis)`. -/
noncomputable def hurwitzMonodromyTorusPoint {I : Type*} (s : I → ℂ) :
    HurwitzTorus I := fun i =>
  Units.mk0 (HurwitzOrbit.monoScalar (s i))
    (HurwitzOrbit.monoScalar_ne_zero (s i))

@[simp]
theorem coe_hurwitzMonodromyTorusPoint {I : Type*} (s : I → ℂ) (i : I) :
    (hurwitzMonodromyTorusPoint s i : ℂ) = HurwitzOrbit.monoScalar (s i) := rfl

theorem hurwitzMonodromyTorusPoint_monomialValue_injective
    {I : Type*} [Fintype I] [DecidableEq I] {s : I → ℂ}
    (hR : hurwitzResonanceLattice (hurwitzMonodromyTorusPoint s) = ⊥) :
    Function.Injective
      (HurwitzJointOrbit.monomialValue (fun i => HurwitzOrbit.monoScalar (s i))) := by
  simpa using
    (hurwitzResonanceLattice_eq_bot_iff_monomialValue_injective
      (hurwitzMonodromyTorusPoint s)).mp hR

/-- The full-closure chamber gives every finite algebraic Hurwitz jet rectangle. -/
theorem hurwitz_fullMonodromyClosure_rectangle_algebraicIndependent
    {I : Type*} [Fintype I] [DecidableEq I] {s : I → ℂ}
    (hs : ∀ i, 1 < (s i).re)
    (hR : hurwitzResonanceLattice (hurwitzMonodromyTorusPoint s) = ⊥)
    (N : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    AlgebraicIndependent (RatFunc ℂ)
      (HurwitzJointLadder.jointHzetaUpperEndFieldJet hs N) := by
  exact HurwitzJointLadder.joint_hzeta_upperEnd_rectangle_algebraicIndependent hs
    (hurwitzMonodromyTorusPoint_monomialValue_injective hR) N

/-- The full-closure chamber gives object-level differential independence. -/
theorem hurwitz_fullMonodromyClosure_differentialIndependent
    {I : Type*} [Fintype I] [DecidableEq I] {s : I → ℂ}
    (hs : ∀ i, 1 < (s i).re)
    (hR : hurwitzResonanceLattice (hurwitzMonodromyTorusPoint s) = ⊥) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => HurwitzJointLadder.hzetaUpperEndMero (s i) (hs i)) := by
  exact HurwitzJointLadder.joint_hzeta_upperEnd_differentialIndependent_finite hs
    (hurwitzMonodromyTorusPoint_monomialValue_injective hR)

/-! ### The resonant `(2,4)` boundary witness -/

noncomputable def hurwitzTwoFourTorusPoint : HurwitzTorus (Fin 2) := fun i =>
  if i = 0 then Units.mk0 2 (by norm_num) else Units.mk0 4 (by norm_num)

@[simp]
theorem hurwitzTwoFourTorusPoint_character (u : HurwitzCharacterLattice (Fin 2)) :
    (hurwitzTorusCharacter hurwitzTwoFourTorusPoint u : ℂ) =
      (2 : ℂ) ^ (u 0 + 2 * u 1) := by
  unfold hurwitzTorusCharacter hurwitzTorusCharacterHom hurwitzTwoFourTorusPoint
  change (∏ i : Fin 2, (((if i = 0 then Units.mk0 2 (by norm_num)
    else Units.mk0 4 (by norm_num)) ^ u i : ℂˣ) : ℂ)) = _
  simp only [Fin.prod_univ_two]
  norm_num
  rw [show (4 : ℂ) = 2 ^ 2 by norm_num]
  rw [← zpow_natCast (2 : ℂ) 2]
  rw [← zpow_mul]
  rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  congr 1

def hurwitzTwoFourRelation : HurwitzCharacterLattice (Fin 2) →ₗ[ℤ] ℤ where
  toFun u := u 0 + 2 * u 1
  map_add' u v := by simp; ring
  map_smul' z u := by simp; ring

theorem hurwitzTwoFour_character_eq_one_iff
    (u : HurwitzCharacterLattice (Fin 2)) :
    hurwitzTorusCharacter hurwitzTwoFourTorusPoint u = 1 ↔
      hurwitzTwoFourRelation u = 0 := by
  rw [← Units.val_inj, hurwitzTwoFourTorusPoint_character]
  change (2 : ℂ) ^ (u 0 + 2 * u 1) = 1 ↔ _
  constructor
  · intro h
    have hr : (2 : ℝ) ^ (u 0 + 2 * u 1) = 1 := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_zpow]
      norm_num
      exact h
    change u 0 + 2 * u 1 = 0
    exact (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≠ 1)).mp hr
  · intro h
    change u 0 + 2 * u 1 = 0 at h
    rw [h]
    simp

theorem hurwitzTwoFour_resonanceLattice_eq_ker :
    hurwitzResonanceLattice hurwitzTwoFourTorusPoint =
      LinearMap.ker hurwitzTwoFourRelation := by
  ext u
  rw [mem_hurwitzResonanceLattice_iff,
    hurwitzTwoFour_character_eq_one_iff, LinearMap.mem_ker]

theorem hurwitzTwoFourRelation_surjective :
    Function.Surjective hurwitzTwoFourRelation := by
  intro z
  refine ⟨fun i => if i = 0 then z else 0, ?_⟩
  simp [hurwitzTwoFourRelation]

theorem hurwitzTwoFour_resonanceRank :
    hurwitzResonanceRank hurwitzTwoFourTorusPoint = 1 := by
  rw [hurwitzResonanceRank, hurwitzTwoFour_resonanceLattice_eq_ker]
  have hquot :=
    (LinearMap.quotKerEquivOfSurjective hurwitzTwoFourRelation
      hurwitzTwoFourRelation_surjective).finrank_eq
  have hsum := (LinearMap.ker hurwitzTwoFourRelation).finrank_quotient_add_finrank
  have hdom : Module.finrank ℤ (HurwitzCharacterLattice (Fin 2)) = 2 := by
    exact Module.finrank_fintype_fun_eq_card (R := ℤ) (η := Fin 2)
  have hcod : Module.finrank ℤ ℤ = 1 := Module.finrank_self ℤ
  rw [hquot, hdom, hcod] at hsum
  omega

theorem hurwitzTwoFour_monodromyClosureDimension :
    hurwitzMonodromyClosureDimension hurwitzTwoFourTorusPoint = 1 := by
  have hsum :=
    hurwitzMonodromyClosureDimension_add_resonanceRank hurwitzTwoFourTorusPoint
  rw [hurwitzTwoFour_resonanceRank] at hsum
  norm_num at hsum ⊢
  omega

/-- An exponent in the convergent half-plane realizing prescribed positive monodromy `r`. -/
noncomputable def hurwitzPositiveMonodromyExponent (r : ℝ) : ℂ :=
  2 + Complex.ofReal (Real.log r / (2 * Real.pi)) * Complex.I

@[simp]
theorem hurwitzPositiveMonodromyExponent_re (r : ℝ) :
    (hurwitzPositiveMonodromyExponent r).re = 2 := by
  norm_num [hurwitzPositiveMonodromyExponent, Complex.mul_re, Complex.div_im]

@[simp]
theorem hurwitzPositiveMonodromyExponent_im (r : ℝ) :
    (hurwitzPositiveMonodromyExponent r).im = Real.log r / (2 * Real.pi) := by
  norm_num [hurwitzPositiveMonodromyExponent, Complex.mul_im, Complex.div_re,
    Complex.div_im]
  field_simp [Real.pi_ne_zero]
  ring

theorem monoScalar_hurwitzPositiveMonodromyExponent {r : ℝ} (hr : 0 < r) :
    HurwitzOrbit.monoScalar (hurwitzPositiveMonodromyExponent r) = (r : ℂ) := by
  rw [HurwitzOrbit.monoScalar]
  have harg : -(2 * (Real.pi : ℂ) * Complex.I *
      hurwitzPositiveMonodromyExponent r) =
      (Real.log r : ℂ) - 4 * (Real.pi : ℂ) * Complex.I := by
    unfold hurwitzPositiveMonodromyExponent
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    norm_num
    field_simp [hpi]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [harg, Complex.exp_sub]
  have hlog : Complex.exp (Real.log r : ℂ) = (r : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hr]
  have hperiod : Complex.exp (4 * (Real.pi : ℂ) * Complex.I) = 1 := by
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨2, ?_⟩
    push_cast
    ring
  rw [hlog, hperiod, div_one]

noncomputable def hurwitzTwoFourExponents : Fin 2 → ℂ := fun i =>
  hurwitzPositiveMonodromyExponent (if i = 0 then 2 else 4)

theorem hurwitzTwoFourExponents_gt_one :
    ∀ i, 1 < (hurwitzTwoFourExponents i).re := by
  intro i
  simp [hurwitzTwoFourExponents]

theorem hurwitzTwoFourExponents_monoScalar (i : Fin 2) :
    HurwitzOrbit.monoScalar (hurwitzTwoFourExponents i) =
      if i = 0 then (2 : ℂ) else 4 := by
  fin_cases i <;> simp [hurwitzTwoFourExponents,
    monoScalar_hurwitzPositiveMonodromyExponent (by norm_num : (0 : ℝ) < 2),
    monoScalar_hurwitzPositiveMonodromyExponent (by norm_num : (0 : ℝ) < 4)]

theorem hurwitzTwoFourExponents_nonintegral :
    ∀ i, ∀ m : ℤ, hurwitzTwoFourExponents i ≠ (m : ℂ) := by
  intro i m h
  have him := congrArg Complex.im h
  fin_cases i
  · simp only [hurwitzTwoFourExponents, hurwitzPositiveMonodromyExponent_im,
      Complex.intCast_im] at him
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpi : 0 < Real.pi := Real.pi_pos
    have hne : Real.log 2 / (2 * Real.pi) ≠ 0 := by positivity
    exact hne him
  · simp only [hurwitzTwoFourExponents, hurwitzPositiveMonodromyExponent_im,
      Complex.intCast_im] at him
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hpi : 0 < Real.pi := Real.pi_pos
    have hne : Real.log 4 / (2 * Real.pi) ≠ 0 := by positivity
    exact hne him

theorem hurwitzTwoFourExponents_monoScalar_injective :
    Function.Injective
      (fun i => HurwitzOrbit.monoScalar (hurwitzTwoFourExponents i)) := by
  intro i j h
  change HurwitzOrbit.monoScalar (hurwitzTwoFourExponents i) =
    HurwitzOrbit.monoScalar (hurwitzTwoFourExponents j) at h
  rw [hurwitzTwoFourExponents_monoScalar,
    hurwitzTwoFourExponents_monoScalar] at h
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact hi.trans hj.symm
  · simp [hi, hj] at h
  · simp [hi, hj] at h
  · apply Fin.ext
    omega

/-- Positive-rank local resonance does not imply a Hurwitz differential relation. -/
theorem hurwitzTwoFourExponents_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => HurwitzJointLadder.hzetaUpperEndMero (hurwitzTwoFourExponents i)
        (hurwitzTwoFourExponents_gt_one i)) := by
  rw [HurwitzJointLadder.hurwitz_intrinsic_residue_differentialMatroid_law
    hurwitzTwoFourExponents hurwitzTwoFourExponents_gt_one
      hurwitzTwoFourExponents_nonintegral]
  exact hurwitzTwoFourExponents_monoScalar_injective

/-! ### Finite common monodromy orbit with full differential rank -/

theorem monoScalar_pow_eq_one_iff_nat (s : ℂ) (n : ℕ) :
    HurwitzOrbit.monoScalar s ^ n = 1 ↔
      ∃ m : ℤ, (n : ℂ) * s = (m : ℂ) := by
  rw [HurwitzOrbit.monoScalar, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    push_cast at hm ⊢
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hfac : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have hprod : (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * s) =
        (2 * (Real.pi : ℂ) * Complex.I) * (-(m : ℂ)) := by
      linear_combination -hm
    exact mul_left_cancel₀ hfac hprod
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    push_cast at hm ⊢
    linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * hm

noncomputable def hurwitzThreeHalvesFourThirdsExponents : Fin 2 → ℂ := fun i =>
  if i = 0 then (3 / 2 : ℂ) else (4 / 3 : ℂ)

theorem threeHalves_ne_int (m : ℤ) : (3 / 2 : ℂ) ≠ (m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hm1 : (1 : ℤ) < m := by
    exact_mod_cast (show (1 : ℝ) < (m : ℝ) by linarith)
  have hm2 : m < (2 : ℤ) := by
    exact_mod_cast (show (m : ℝ) < (2 : ℝ) by linarith)
  omega

theorem fourThirds_ne_int (m : ℤ) : (4 / 3 : ℂ) ≠ (m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hm1 : (1 : ℤ) < m := by
    exact_mod_cast (show (1 : ℝ) < (m : ℝ) by linarith)
  have hm2 : m < (2 : ℤ) := by
    exact_mod_cast (show (m : ℝ) < (2 : ℝ) by linarith)
  omega

theorem eightThirds_ne_int (m : ℤ) : (8 / 3 : ℂ) ≠ (m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hm1 : (2 : ℤ) < m := by
    exact_mod_cast (show (2 : ℝ) < (m : ℝ) by linarith)
  have hm2 : m < (3 : ℤ) := by
    exact_mod_cast (show (m : ℝ) < (3 : ℝ) by linarith)
  omega

theorem hurwitzThreeHalvesFourThirds_zero_order :
    orderOf (hurwitzMonodromyTorusPoint
      hurwitzThreeHalvesFourThirdsExponents 0) = 2 := by
  apply (orderOf_eq_iff (by norm_num : 0 < 2)).mpr
  constructor
  · apply Units.ext
    change HurwitzOrbit.monoScalar (3 / 2 : ℂ) ^ 2 = 1
    exact (monoScalar_pow_eq_one_iff_nat (3 / 2 : ℂ) 2).mpr ⟨3, by norm_num⟩
  · intro m hm hpos
    have hm1 : m = 1 := by omega
    subst m
    intro h
    have hc : HurwitzOrbit.monoScalar (3 / 2 : ℂ) = 1 := by
      simpa [hurwitzMonodromyTorusPoint,
        hurwitzThreeHalvesFourThirdsExponents] using congrArg Units.val h
    obtain ⟨z, hz⟩ :=
      (HurwitzOrbit.monoScalar_eq_one_iff (3 / 2 : ℂ)).mp hc
    exact threeHalves_ne_int z hz

theorem hurwitzThreeHalvesFourThirds_one_order :
    orderOf (hurwitzMonodromyTorusPoint
      hurwitzThreeHalvesFourThirdsExponents 1) = 3 := by
  apply (orderOf_eq_iff (by norm_num : 0 < 3)).mpr
  constructor
  · apply Units.ext
    change HurwitzOrbit.monoScalar (4 / 3 : ℂ) ^ 3 = 1
    exact (monoScalar_pow_eq_one_iff_nat (4 / 3 : ℂ) 3).mpr ⟨4, by norm_num⟩
  · intro m hm hpos
    interval_cases m
    · intro h
      have hc : HurwitzOrbit.monoScalar (4 / 3 : ℂ) = 1 := by
        simpa [hurwitzMonodromyTorusPoint,
          hurwitzThreeHalvesFourThirdsExponents] using congrArg Units.val h
      obtain ⟨z, hz⟩ :=
        (HurwitzOrbit.monoScalar_eq_one_iff (4 / 3 : ℂ)).mp hc
      exact fourThirds_ne_int z hz
    · intro h
      have hc : HurwitzOrbit.monoScalar (4 / 3 : ℂ) ^ 2 = 1 := by
        simpa [hurwitzMonodromyTorusPoint,
          hurwitzThreeHalvesFourThirdsExponents] using congrArg Units.val h
      obtain ⟨z, hz⟩ :=
        (monoScalar_pow_eq_one_iff_nat (4 / 3 : ℂ) 2).mp hc
      norm_num at hz
      exact eightThirds_ne_int z hz

/-- The common monodromy point of `(3/2,4/3)` has exactly six elements in its orbit. -/
theorem hurwitzThreeHalvesFourThirds_commonMonodromy_order :
    orderOf (hurwitzMonodromyTorusPoint
      hurwitzThreeHalvesFourThirdsExponents) = 6 := by
  let q := hurwitzMonodromyTorusPoint hurwitzThreeHalvesFourThirdsExponents
  have hpow : q ^ 6 = 1 := by
    funext i
    change (q i) ^ 6 = 1
    by_cases hi : i = 0
    · subst i
      exact orderOf_dvd_iff_pow_eq_one.mp (by
        change orderOf (hurwitzMonodromyTorusPoint
          hurwitzThreeHalvesFourThirdsExponents 0) ∣ 6
        rw [hurwitzThreeHalvesFourThirds_zero_order]
        norm_num)
    · have hi1 : i = 1 := by
        apply Fin.ext
        omega
      subst i
      exact orderOf_dvd_iff_pow_eq_one.mp (by
        change orderOf (hurwitzMonodromyTorusPoint
          hurwitzThreeHalvesFourThirdsExponents 1) ∣ 6
        rw [hurwitzThreeHalvesFourThirds_one_order]
        norm_num)
  have hdvd6 : orderOf q ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have h2 : 2 ∣ orderOf q := by
    have h := orderOf_apply_dvd_orderOf (x := q) 0
    change orderOf (hurwitzMonodromyTorusPoint
      hurwitzThreeHalvesFourThirdsExponents 0) ∣ orderOf q at h
    rw [hurwitzThreeHalvesFourThirds_zero_order] at h
    exact h
  have h3 : 3 ∣ orderOf q := by
    have h := orderOf_apply_dvd_orderOf (x := q) 1
    change orderOf (hurwitzMonodromyTorusPoint
      hurwitzThreeHalvesFourThirdsExponents 1) ∣ orderOf q at h
    rw [hurwitzThreeHalvesFourThirds_one_order] at h
    exact h
  have h6 : 6 ∣ orderOf q :=
    (by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
  exact Nat.dvd_antisymm hdvd6 h6

/-- Despite order-six common monodromy, the two ordinary Hurwitz functions have rank two. -/
theorem hurwitzThreeHalvesFourThirds_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i : Fin 2 => HurwitzJointLadder.hzetaUpperEndMero
        (if i = 0 then (3 / 2 : ℂ) else (4 / 3 : ℂ))
        (by split <;> norm_num)) :=
  HurwitzJointLadder.hurwitz_threeHalves_fourThirds_differentialIndependent

end

end GaloisForLFunctions.HTGeometry
