import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import GaloisForLFunctions.Bottcher.MonodromyObstruction

/-!
# Finite-cover invariance across a divisible kernel

Let `f : G →* H` be a surjective group homomorphism whose kernel is divisible, i.e. every
element of `ker f` is an `n`-th power inside `ker f` for every `n ≥ 1`.  Divisibility is used
only through the weaker property that `ker f` admits no nontrivial homomorphism to a finite
group.

Three consequences are proved here.

* Restriction of scalars `Action FintypeCat H ⥤ Action FintypeCat G` along `f` is an
  equivalence of categories.  Concretely: every action of `G` on a finite set descends
  uniquely along `f`, and equivariance for `G` and for `H` agree.
* Taking preimages is an order isomorphism from the finite-index normal subgroups of `H` onto
  those of `G`, and the matched finite quotients are canonically isomorphic.
* The induced map of profinite completions is an isomorphism.

When `G` and `H` are fundamental groups of connected spaces and finite covering spaces are
classified by finite `π₁`-sets, the first statement says that `f` induces an equivalence of the
categories of finite covers, and the third that it identifies profinite completions.
-/

namespace RHTower

open CategoryTheory

universe u

section DivisibleFiber

/-- A group in which every element is an `n`-th power for every `n ≥ 1`. -/
def DeningerPowerDivisible (K : Type u) [Group K] : Prop :=
  ∀ n : ℕ, 0 < n → ∀ k : K, ∃ u : K, u ^ n = k

/-- A group with no nontrivial finite quotient: every homomorphism into a finite group is
trivial. -/
def DeningerNoFiniteQuotient (K : Type u) [Group K] : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q] (φ : K →* Q) (k : K), φ k = 1

/-- Divisibility is a sufficient source condition: a power-divisible group has no nontrivial
finite quotient, because a finite group has exponent dividing its cardinality. -/
theorem deningerNoFiniteQuotient_of_powerDivisible {K : Type u} [Group K]
    (h : DeningerPowerDivisible K) : DeningerNoFiniteQuotient K := by
  intro Q _ _ φ k
  exact Bottcher.monoidHom_eq_one_of_powerDivisible_finite_codomain φ h k

variable {G H : Type u} [Group G] [Group H] {f : G →* H}

/-- A kernel without finite quotients is contained in the kernel of every homomorphism from the
ambient group to a finite group. -/
theorem deningerKer_le_ker (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G))
    {Q : Type u} [Group Q] [Finite Q] (φ : G →* Q) : f.ker ≤ φ.ker := by
  intro k hk
  have := hker Q (φ.comp f.ker.subtype) ⟨k, hk⟩
  simpa [MonoidHom.mem_ker] using this

/-- Descent of a homomorphism along a surjection that kills its kernel. -/
noncomputable def deningerDescendHom {M : Type u} [Monoid M] (hsurj : Function.Surjective f)
    (φ : G →* M) (h : ∀ k ∈ f.ker, φ k = 1) : H →* M :=
  (QuotientGroup.lift f.ker φ h).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm.toMonoidHom

/-- The descended homomorphism restricts to the original one. -/
theorem deningerDescendHom_apply {M : Type u} [Monoid M] (hsurj : Function.Surjective f)
    (φ : G →* M) (h : ∀ k ∈ f.ker, φ k = 1) (g : G) :
    deningerDescendHom hsurj φ h (f g) = φ g := by
  have hgg : (QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm (f g)
      = (QuotientGroup.mk g : G ⧸ f.ker) := by
    apply (QuotientGroup.quotientKerEquivOfSurjective f hsurj).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  show (QuotientGroup.lift f.ker φ h)
      ((QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm (f g)) = φ g
  rw [hgg]
  rfl

/-- The kernel acts trivially on every finite `G`-set: its image in the finite permutation
group of the underlying set is trivial. -/
theorem deningerRho_ker_eq_id (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G))
    (A : Action FintypeCat.{u} G) {k : G} (hk : k ∈ f.ker) : A.ρ k = 𝟙 A.V := by
  have h1 : (MulAction.toPermHom G A.V) k = 1 :=
    MonoidHom.mem_ker.mp (deningerKer_le_ker hker (MulAction.toPermHom G A.V) hk)
  have hx : ∀ x : A.V, k • x = x := by
    intro x
    simpa using congrArg (fun p : Equiv.Perm A.V => p x) h1
  show @Eq (A.V ⟶ A.V) (A.ρ k) (𝟙 A.V)
  ext x
  exact hx x

/-- The action of `H` obtained by descending a finite `G`-set along `f`. -/
noncomputable def deningerDescend (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) (A : Action FintypeCat.{u} G) :
    Action FintypeCat.{u} H where
  V := A.V
  ρ := deningerDescendHom hsurj A.ρ fun _ hk => deningerRho_ker_eq_id hker A hk

/-- The descended action restricts to the original one. -/
theorem deningerDescend_rho (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) (A : Action FintypeCat.{u} G)
    (g : G) : (deningerDescend hsurj hker A).ρ (f g) = A.ρ g :=
  deningerDescendHom_apply hsurj A.ρ _ g

/-- Restriction of the descended action along `f` recovers the original finite `G`-set. -/
noncomputable def deningerDescendIso (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) (A : Action FintypeCat.{u} G) :
    (Action.res FintypeCat.{u} f).obj (deningerDescend hsurj hker A) ≅ A :=
  Action.mkIso (Iso.refl A.V) (by
    intro g
    have h : @Eq (A.V ⟶ A.V) ((deningerDescend hsurj hker A).ρ (f g)) (A.ρ g) :=
      deningerDescend_rho hsurj hker A g
    exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))

/-- Every finite `G`-set descends along `f`. -/
theorem deningerRes_essSurj (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    (Action.res FintypeCat.{u} f).EssSurj :=
  ⟨fun A => ⟨deningerDescend hsurj hker A, ⟨deningerDescendIso hsurj hker A⟩⟩⟩

/-- **Finite-cover invariance.** Restriction along a surjection whose kernel has no nontrivial
finite quotient is faithful, full and essentially surjective. -/
theorem deningerRes_isEquivalence (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    (Action.res FintypeCat.{u} f).IsEquivalence where
  faithful := inferInstance
  full := Action.full_res FintypeCat.{u} f hsurj
  essSurj := deningerRes_essSurj hsurj hker

/-- The equivalence between finite `H`-sets and finite `G`-sets. -/
noncomputable def deningerFiniteActionEquiv (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    Action FintypeCat.{u} H ≌ Action FintypeCat.{u} G :=
  haveI := deningerRes_isEquivalence hsurj hker
  (Action.res FintypeCat.{u} f).asEquivalence

/-- The equivalence is implemented by restriction of scalars. -/
theorem deningerFiniteActionEquiv_functor (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    (deningerFiniteActionEquiv hsurj hker).functor = Action.res FintypeCat.{u} f := rfl

/-- Divisible-kernel form of finite-cover invariance. -/
noncomputable def deningerFiniteActionEquivOfDivisible (hsurj : Function.Surjective f)
    (hdiv : DeningerPowerDivisible (f.ker : Subgroup G)) :
    Action FintypeCat.{u} H ≌ Action FintypeCat.{u} G :=
  deningerFiniteActionEquiv hsurj (deningerNoFiniteQuotient_of_powerDivisible hdiv)

end DivisibleFiber

section FiniteQuotients

variable {G H : Type u} [Group G] [Group H] {f : G →* H}

/-- The kernel lies in every normal subgroup of finite index. -/
theorem deningerKer_le_of_finiteIndex (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G))
    (M : Subgroup G) [M.Normal] [M.FiniteIndex] : f.ker ≤ M := by
  intro k hk
  have h := deningerKer_le_ker hker (QuotientGroup.mk' M) hk
  simpa [QuotientGroup.ker_mk'] using h

/-- Restated for the bundled finite-index normal subgroups. -/
theorem deningerKer_le_finiteIndexNormal (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G))
    (N : FiniteIndexNormalSubgroup G) : f.ker ≤ N.toSubgroup :=
  deningerKer_le_of_finiteIndex hker N.toSubgroup

/-- The image of a normal subgroup under a surjection is normal. -/
theorem deningerMap_normal (hsurj : Function.Surjective f) (M : Subgroup G) [M.Normal] :
    (M.map f).Normal :=
  Subgroup.Normal.map ‹M.Normal› f hsurj

/-- The image of a finite-index normal subgroup under a surjection again has finite index: the
finite quotient `G ⧸ M` surjects onto `H ⧸ M.map f`. -/
theorem deningerMap_finiteIndex (hsurj : Function.Surjective f) (M : Subgroup G) [M.Normal]
    [M.FiniteIndex] : (M.map f).FiniteIndex := by
  haveI := deningerMap_normal hsurj M
  have hle : M ≤ (M.map f).comap f := Subgroup.le_comap_map f M
  have hq : Function.Surjective (QuotientGroup.map M (M.map f) f hle) := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, rfl⟩ := hsurj h
    exact ⟨QuotientGroup.mk g, rfl⟩
  haveI : Finite (H ⧸ M.map f) := Finite.of_surjective _ hq
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Preimage followed by image is the identity on subgroups of `H`. -/
theorem deningerMap_comap (hsurj : Function.Surjective f) (N : Subgroup H) :
    (N.comap f).map f = N :=
  Subgroup.map_comap_eq_self_of_surjective hsurj N

/-- Image followed by preimage is the identity on finite-index normal subgroups of `G`. -/
theorem deningerComap_map (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G))
    (M : Subgroup G) [M.Normal] [M.FiniteIndex] : (M.map f).comap f = M :=
  Subgroup.comap_map_eq_self (deningerKer_le_of_finiteIndex hker M)

/-- The image of a finite-index normal subgroup of `G`, bundled. -/
def deningerMapFiniteIndexNormal (hsurj : Function.Surjective f)
    (M : FiniteIndexNormalSubgroup G) : FiniteIndexNormalSubgroup H where
  toSubgroup := M.toSubgroup.map f
  isNormal' := deningerMap_normal hsurj M.toSubgroup
  isFiniteIndex' := deningerMap_finiteIndex hsurj M.toSubgroup

/-- **Finite-quotient invariance.** Taking preimages along `f` is an order isomorphism from the
finite-index normal subgroups of `H` onto those of `G`. -/
def deningerFiniteIndexNormalEquiv (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    FiniteIndexNormalSubgroup H ≃o FiniteIndexNormalSubgroup G where
  toFun := FiniteIndexNormalSubgroup.comap f
  invFun := deningerMapFiniteIndexNormal hsurj
  left_inv N := by
    apply FiniteIndexNormalSubgroup.toSubgroup_injective
    show (N.toSubgroup.comap f).map f = N.toSubgroup
    exact deningerMap_comap hsurj N.toSubgroup
  right_inv M := by
    apply FiniteIndexNormalSubgroup.toSubgroup_injective
    show (M.toSubgroup.map f).comap f = M.toSubgroup
    exact deningerComap_map hker M.toSubgroup
  map_rel_iff' {N N'} := by
    constructor
    · intro h
      have hmap : (N.toSubgroup.comap f).map f ≤ (N'.toSubgroup.comap f).map f :=
        Subgroup.map_mono h
      rw [deningerMap_comap hsurj, deningerMap_comap hsurj] at hmap
      exact hmap
    · intro h
      exact FiniteIndexNormalSubgroup.comap_mono f h

/-- The finite quotients matched by `deningerFiniteIndexNormalEquiv` are canonically
isomorphic. -/
noncomputable def deningerQuotientEquiv (hsurj : Function.Surjective f) (N : Subgroup H)
    [N.Normal] : G ⧸ N.comap f ≃* H ⧸ N := by
  haveI : (N.comap f).Normal := Subgroup.Normal.comap ‹N.Normal› f
  have hcomp : Function.Surjective ((QuotientGroup.mk' N).comp f) :=
    (QuotientGroup.mk'_surjective N).comp hsurj
  have hkereq : ((QuotientGroup.mk' N).comp f).ker = N.comap f := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact (QuotientGroup.quotientMulEquivOfEq hkereq).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hcomp)

end FiniteQuotients

section ProfiniteCompletion

variable {G H : Type u} [Group G] [Group H] (f : G →* H)

open ProfiniteGrp ProfiniteCompletion

/-- The canonical map to the profinite completion kills the kernel, because the kernel lies in
every finite-index normal subgroup. -/
theorem deningerEta_ker (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) {k : G}
    (hk : k ∈ f.ker) : (eta (GrpCat.of G)).hom k = 1 := by
  apply Subtype.ext
  funext N
  exact (QuotientGroup.eq_one_iff k).mpr (deningerKer_le_finiteIndexNormal hker N hk)

/-- The factorization of the completion unit of `G` through `H`. -/
noncomputable def deningerEtaDescend (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    GrpCat.of H ⟶ GrpCat.of (completion (GrpCat.of G)) :=
  GrpCat.ofHom
    (deningerDescendHom hsurj (eta (GrpCat.of G)).hom fun _ hk => deningerEta_ker f hker hk)

/-- Precomposing the factorization with `f` returns the completion unit. -/
theorem deningerEtaDescend_comp (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    GrpCat.ofHom f ≫ deningerEtaDescend f hsurj hker = eta (GrpCat.of G) := by
  ext g
  exact deningerDescendHom_apply hsurj (eta (GrpCat.of G)).hom
    (fun _ hk => deningerEta_ker f hker hk) g

/-- **Profinite-completion invariance.** A surjection whose kernel has no nontrivial finite
quotient induces an isomorphism of profinite completions. -/
theorem deningerIsIso_profiniteCompletion_map (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    IsIso (profiniteCompletion.map (GrpCat.ofHom f)) := by
  haveI : Epi (GrpCat.ofHom f) := (GrpCat.epi_iff_surjective _).mpr hsurj
  show IsIso (lift (GrpCat.ofHom f ≫ eta (GrpCat.of H)))
  refine ⟨lift (deningerEtaDescend f hsurj hker), ?_, ?_⟩
  · apply lift_unique
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, lift_eta, Category.assoc, lift_eta,
      deningerEtaDescend_comp]
    exact (Category.comp_id (eta (GrpCat.of G))).symm
  · apply lift_unique
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, lift_eta,
      ← cancel_epi (GrpCat.ofHom f), ← Category.assoc, deningerEtaDescend_comp, lift_eta]
    exact congrArg (fun t => GrpCat.ofHom f ≫ t) (Category.comp_id (eta (GrpCat.of H))).symm

/-- The isomorphism of profinite completions. -/
noncomputable def deningerProfiniteCompletionIso (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G)) :
    profiniteCompletion.obj (GrpCat.of G) ≅ profiniteCompletion.obj (GrpCat.of H) :=
  haveI := deningerIsIso_profiniteCompletion_map f hsurj hker
  asIso (profiniteCompletion.map (GrpCat.ofHom f))

/-- Divisible-kernel form of profinite-completion invariance. -/
noncomputable def deningerProfiniteCompletionIsoOfDivisible (hsurj : Function.Surjective f)
    (hdiv : DeningerPowerDivisible (f.ker : Subgroup G)) :
    profiniteCompletion.obj (GrpCat.of G) ≅ profiniteCompletion.obj (GrpCat.of H) :=
  deningerProfiniteCompletionIso f hsurj (deningerNoFiniteQuotient_of_powerDivisible hdiv)

end ProfiniteCompletion

end RHTower
