import GaloisForLFunctions.HTGeometry.AlgebraicGroupJet
import Mathlib.RingTheory.Etale.Basic

/-!
# Formal-étale compatibility with truncated arcs

For a formally étale ring map `A → B` and a nilpotent surjective augmentation `T → R`,
maps `B → T` are exactly pairs consisting of a map `A → T` and a compatible map `B → R`.
This is the affine functor-of-points form of the cartesian identity

`Jⁿ(X) ≅ Jⁿ(Y) ×_Y X`

for an étale morphism `X → Y`.  The final specialization proves the statement for the genuine
truncated arc algebra `R[t]/(tⁿ⁺¹)` used by `AlgebraicGroupJet`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

universe u v w x

variable {A : Type u} {B : Type v} {T : Type w} {R : Type x}
variable [CommRing A] [CommRing B] [CommRing T] [CommRing R]

/-- The set-theoretic pullback of arcs on `A` and points on `B` over points on `A`. -/
structure EtaleArcPullback (f : A →+* B) (augmentation : T →+* R) where
  baseArc : A →+* T
  sourcePoint : B →+* R
  compatible : augmentation.comp baseArc = sourcePoint.comp f

@[ext]
theorem EtaleArcPullback.ext {f : A →+* B} {augmentation : T →+* R}
    {p q : EtaleArcPullback f augmentation}
    (hbase : p.baseArc = q.baseArc) (hpoint : p.sourcePoint = q.sourcePoint) : p = q := by
  cases p
  cases q
  simp_all

/-- A source arc gives its image arc and its source point at the augmentation. -/
def etaleArcPullbackMap (f : A →+* B) (augmentation : T →+* R) :
    (B →+* T) → EtaleArcPullback f augmentation := fun sourceArc =>
  { baseArc := sourceArc.comp f
    sourcePoint := augmentation.comp sourceArc
    compatible := by simp only [RingHom.comp_assoc] }

/-- Formal unramifiedness makes a lift across a nilpotent augmentation unique. -/
theorem etaleArcPullbackMap_injective (f : A →+* B) (augmentation : T →+* R)
    (hf : f.FormallyEtale) (hker : IsNilpotent (RingHom.ker augmentation)) :
    Function.Injective (etaleArcPullbackMap f augmentation) := by
  intro g₁ g₂ h
  have hbase : g₁.comp f = g₂.comp f := congrArg EtaleArcPullback.baseArc h
  have hres : augmentation.comp g₁ = augmentation.comp g₂ :=
    congrArg EtaleArcPullback.sourcePoint h
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A T := (g₁.comp f).toAlgebra
  haveI : Algebra.FormallyEtale A B := hf
  let g₁' : B →ₐ[A] T := { g₁ with commutes' := fun _ => rfl }
  let g₂' : B →ₐ[A] T :=
    { g₂ with commutes' := fun a => RingHom.congr_fun hbase.symm a }
  have hlift : g₁' = g₂' :=
    Algebra.FormallyUnramified.ext' augmentation hker g₁' g₂' fun b =>
      RingHom.congr_fun hres b
  exact RingHom.ext fun b => AlgHom.congr_fun hlift b

/-- Formal smoothness supplies a lift across a surjective nilpotent augmentation. -/
theorem etaleArcPullbackMap_surjective (f : A →+* B) (augmentation : T →+* R)
    (hf : f.FormallyEtale) (haugmentation : Function.Surjective augmentation)
    (hker : IsNilpotent (RingHom.ker augmentation)) :
    Function.Surjective (etaleArcPullbackMap f augmentation) := by
  intro p
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A T := p.baseArc.toAlgebra
  letI : Algebra A R := (augmentation.comp p.baseArc).toAlgebra
  haveI : Algebra.FormallyEtale A B := hf
  let augmentation' : T →ₐ[A] R := { augmentation with commutes' := fun _ => rfl }
  let sourcePoint' : B →ₐ[A] R :=
    { p.sourcePoint with
      commutes' := fun a => RingHom.congr_fun p.compatible.symm a }
  let lift : B →ₐ[A] T :=
    Algebra.FormallySmooth.liftOfSurjective sourcePoint' augmentation'
      haugmentation hker
  let sourceArc : B →+* T := lift.toRingHom
  refine ⟨sourceArc, EtaleArcPullback.ext ?_ ?_⟩
  · exact RingHom.ext fun a => lift.commutes a
  · exact RingHom.ext fun b =>
      Algebra.FormallySmooth.liftOfSurjective_apply sourcePoint' augmentation'
        haugmentation hker b

/-- Formally étale maps satisfy the exact cartesian arc-lifting property across every surjective
nilpotent augmentation. -/
theorem etaleArcPullbackMap_bijective (f : A →+* B) (augmentation : T →+* R)
    (hf : f.FormallyEtale) (haugmentation : Function.Surjective augmentation)
    (hker : IsNilpotent (RingHom.ker augmentation)) :
    Function.Bijective (etaleArcPullbackMap f augmentation) :=
  ⟨etaleArcPullbackMap_injective f augmentation hf hker,
    etaleArcPullbackMap_surjective f augmentation hf haugmentation hker⟩

/-- Arcs based at a fixed point of an affine scheme. -/
abbrev BasedRingArc (augmentation : T →+* R) (p : B →+* R) :=
  { g : B →+* T // augmentation.comp g = p }

/-- Restriction of a based source arc along an affine morphism. -/
def etaleBasedArcMap (f : A →+* B) (augmentation : T →+* R) (p : B →+* R) :
    BasedRingArc augmentation p → BasedRingArc augmentation (p.comp f) := fun g =>
  ⟨g.1.comp f, by
    ext a
    exact RingHom.congr_fun g.2 (f a)⟩

/-- Formal étaleness identifies arcs based at a source point with arcs based at its image. -/
theorem etaleBasedArcMap_bijective (f : A →+* B) (augmentation : T →+* R)
    (p : B →+* R) (hf : f.FormallyEtale) (haugmentation : Function.Surjective augmentation)
    (hker : IsNilpotent (RingHom.ker augmentation)) :
    Function.Bijective (etaleBasedArcMap f augmentation p) := by
  have hglobal := etaleArcPullbackMap_bijective f augmentation hf haugmentation hker
  constructor
  · intro g₁ g₂ h
    apply Subtype.ext
    apply hglobal.1
    apply EtaleArcPullback.ext
    · exact congrArg Subtype.val h
    · exact g₁.2.trans g₂.2.symm
  · intro a
    let q : EtaleArcPullback f augmentation :=
      { baseArc := a.1
        sourcePoint := p
        compatible := a.2 }
    obtain ⟨g, hg⟩ := hglobal.2 q
    have hpoint : augmentation.comp g = p :=
      congrArg EtaleArcPullback.sourcePoint hg
    refine ⟨⟨g, hpoint⟩, ?_⟩
    apply Subtype.ext
    exact congrArg EtaleArcPullback.baseArc hg

/-- Equivalence form of based formal-étale arc lifting. -/
noncomputable def etaleBasedArcEquiv (f : A →+* B) (augmentation : T →+* R)
    (p : B →+* R) (hf : f.FormallyEtale) (haugmentation : Function.Surjective augmentation)
    (hker : IsNilpotent (RingHom.ker augmentation)) :
    BasedRingArc augmentation p ≃ BasedRingArc augmentation (p.comp f) :=
  Equiv.ofBijective (etaleBasedArcMap f augmentation p)
    (etaleBasedArcMap_bijective f augmentation p hf haugmentation hker)

section Algebra

variable {K : Type*} [CommRing K]
variable [Algebra K A] [Algebra K B] [Algebra K T] [Algebra K R]

/-- Based arcs in the category of `K`-algebras. -/
abbrev BasedAlgArc (augmentation : T →ₐ[K] R) (p : B →ₐ[K] R) :=
  { g : B →ₐ[K] T // augmentation.comp g = p }

/-- Restriction of a based algebra arc along an algebra morphism. -/
def etaleBasedAlgArcMap (f : A →ₐ[K] B) (augmentation : T →ₐ[K] R) (p : B →ₐ[K] R) :
    BasedAlgArc augmentation p → BasedAlgArc augmentation (p.comp f) := fun g =>
  ⟨g.1.comp f, by
    ext a
    exact DFunLike.congr_fun g.2 (f a)⟩

/-- Formal-étale based lifting remains exact after imposing the base-algebra structure. -/
theorem etaleBasedAlgArcMap_bijective (f : A →ₐ[K] B) (augmentation : T →ₐ[K] R)
    (p : B →ₐ[K] R) (hf : f.toRingHom.FormallyEtale)
    (haugmentation : Function.Surjective augmentation)
    (hker : IsNilpotent (RingHom.ker augmentation.toRingHom)) :
    Function.Bijective (etaleBasedAlgArcMap f augmentation p) := by
  have hring := etaleBasedArcMap_bijective f.toRingHom augmentation.toRingHom p.toRingHom
    hf haugmentation hker
  constructor
  · intro g₁ g₂ h
    let g₁r : BasedRingArc augmentation.toRingHom p.toRingHom :=
      ⟨g₁.1.toRingHom, congrArg AlgHom.toRingHom g₁.2⟩
    let g₂r : BasedRingArc augmentation.toRingHom p.toRingHom :=
      ⟨g₂.1.toRingHom, congrArg AlgHom.toRingHom g₂.2⟩
    have hm : etaleBasedArcMap f.toRingHom augmentation.toRingHom p.toRingHom g₁r =
        etaleBasedArcMap f.toRingHom augmentation.toRingHom p.toRingHom g₂r := by
      apply Subtype.ext
      exact congrArg AlgHom.toRingHom (congrArg Subtype.val h)
    have hg := congrArg Subtype.val (hring.1 hm)
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    exact RingHom.congr_fun hg b
  · intro a
    let ar : BasedRingArc augmentation.toRingHom (p.comp f).toRingHom :=
      ⟨a.1.toRingHom, congrArg AlgHom.toRingHom a.2⟩
    obtain ⟨g, hg⟩ := hring.2 ar
    have hbase : g.1.comp f.toRingHom = a.1.toRingHom := congrArg Subtype.val hg
    let gAlg : B →ₐ[K] T :=
      { g.1 with
        commutes' := fun k => by
          calc
            g.1 (algebraMap K B k) = g.1 (f (algebraMap K A k)) := by rw [f.commutes]
            _ = a.1 (algebraMap K A k) := RingHom.congr_fun hbase _
            _ = algebraMap K T k := a.1.commutes k }
    have hpoint : augmentation.comp gAlg = p := by
      apply AlgHom.ext
      intro b
      exact RingHom.congr_fun g.2 b
    refine ⟨⟨gAlg, hpoint⟩, ?_⟩
    apply Subtype.ext
    apply AlgHom.ext
    intro a'
    exact RingHom.congr_fun hbase a'

/-- Equivalence form of based formal-étale lifting in `K`-algebras. -/
noncomputable def etaleBasedAlgArcEquiv (f : A →ₐ[K] B) (augmentation : T →ₐ[K] R)
    (p : B →ₐ[K] R) (hf : f.toRingHom.FormallyEtale)
    (haugmentation : Function.Surjective augmentation)
    (hker : IsNilpotent (RingHom.ker augmentation.toRingHom)) :
    BasedAlgArc augmentation p ≃ BasedAlgArc augmentation (p.comp f) :=
  Equiv.ofBijective (etaleBasedAlgArcMap f augmentation p)
    (etaleBasedAlgArcMap_bijective f augmentation p hf haugmentation hker)

end Algebra

section TruncatedArc

variable {R₀ : Type u} [CommRing R₀]

/-- The constant-term augmentation of a truncated arc algebra is surjective. -/
theorem truncatedArcAugmentation_surjective (n : ℕ) :
    Function.Surjective (truncatedArcAugmentation (R := R₀) n) := by
  intro r
  exact ⟨algebraMap R₀ (TruncatedArcAlgebra R₀ n) r,
    truncatedArcAugmentation_algebraMap (R := R₀) n r⟩

/-- Every element in the augmentation ideal is represented by a polynomial divisible by `X`. -/
theorem truncatedArcAugmentation_ker_le_map_span_X (n : ℕ) :
    RingHom.ker (truncatedArcAugmentation (R := R₀) n) ≤
      Ideal.map (Ideal.Quotient.mk (truncatedArcIdeal R₀ n)) (Ideal.span {Polynomial.X}) := by
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.mem_map_of_mem
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
  have hz' := hz
  rw [RingHom.mem_ker, truncatedArcAugmentation_mk] at hz'
  simpa [Polynomial.coeff_zero_eq_eval_zero] using hz'

/-- The image of `(X)` in `R[X]/(Xⁿ⁺¹)` has zero `(n+1)`-st power. -/
theorem map_span_X_pow_eq_bot (n : ℕ) :
    (Ideal.map (Ideal.Quotient.mk (truncatedArcIdeal R₀ n))
      (Ideal.span {Polynomial.X})) ^ (n + 1) = ⊥ := by
  rw [← Ideal.map_pow, Ideal.span_singleton_pow]
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  rw [Ideal.span_le]
  intro p hp
  simp only [Set.mem_singleton_iff] at hp
  subst p
  change Ideal.Quotient.mk (truncatedArcIdeal R₀ n) (Polynomial.X ^ (n + 1)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The augmentation ideal of `R[X]/(Xⁿ⁺¹)` is nilpotent. -/
theorem truncatedArcAugmentation_ker_isNilpotent (n : ℕ) :
    IsNilpotent (RingHom.ker (truncatedArcAugmentation (R := R₀) n)) := by
  refine ⟨n + 1, le_antisymm ?_ bot_le⟩
  calc
    RingHom.ker (truncatedArcAugmentation (R := R₀) n) ^ (n + 1) ≤
        (Ideal.map (Ideal.Quotient.mk (truncatedArcIdeal R₀ n))
          (Ideal.span {Polynomial.X})) ^ (n + 1) :=
      pow_le_pow_left' (truncatedArcAugmentation_ker_le_map_span_X (R₀ := R₀) n) _
    _ = ⊥ := map_span_X_pow_eq_bot (R₀ := R₀) n

/-- **Finite-étale jet compatibility.** For every formally étale affine morphism and every order,
source truncated arcs are exactly the pullback of target truncated arcs along source points. -/
theorem formallyEtale_truncatedArc_pullback_bijective
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FormallyEtale) (n : ℕ) :
    Function.Bijective
      (etaleArcPullbackMap f (truncatedArcAugmentation (R := R₀) n).toRingHom) :=
  etaleArcPullbackMap_bijective f _ hf
    (truncatedArcAugmentation_surjective (R₀ := R₀) n)
    (truncatedArcAugmentation_ker_isNilpotent (R₀ := R₀) n)

/-- Based form of finite-étale jet compatibility for truncated arcs. -/
noncomputable def formallyEtale_truncatedArc_basedEquiv
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.FormallyEtale) (p : B →+* R₀) (n : ℕ) :
    BasedRingArc (truncatedArcAugmentation (R := R₀) n).toRingHom p ≃
      BasedRingArc (truncatedArcAugmentation (R := R₀) n).toRingHom (p.comp f) :=
  etaleBasedArcEquiv f _ p hf
    (truncatedArcAugmentation_surjective (R₀ := R₀) n)
    (truncatedArcAugmentation_ker_isNilpotent (R₀ := R₀) n)

/-- Based finite-étale jet compatibility in `R₀`-algebras. -/
noncomputable def formallyEtale_truncatedArc_basedAlgEquiv
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra R₀ A] [Algebra R₀ B]
    (f : A →ₐ[R₀] B) (hf : f.toRingHom.FormallyEtale) (p : B →ₐ[R₀] R₀) (n : ℕ) :
    BasedAlgArc (truncatedArcAugmentation (R := R₀) n) p ≃
      BasedAlgArc (truncatedArcAugmentation (R := R₀) n) (p.comp f) :=
  etaleBasedAlgArcEquiv f _ p hf
    (truncatedArcAugmentation_surjective (R₀ := R₀) n)
    (truncatedArcAugmentation_ker_isNilpotent (R₀ := R₀) n)

end TruncatedArc

end GaloisForLFunctions.HTGeometry
