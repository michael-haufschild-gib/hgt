import GaloisForLFunctions.RHTower.DeningerBaumslagRationalProjective

/-!
# Pullbacks of the packet's surjection

The homotopy pullback of `Ba_U` has no counterpart in mathlib, but its group-theoretic shadow does:
the fibre product of `a_U : R_U ↠ A` along any homomorphism `H → A`.  That fibre product surjects
onto `H` with kernel `K_U`, which is divisible, so the divisible-fibre theorem applies verbatim: the
pullback induces an equivalence of finite covering categories and an isomorphism of profinite
completions.

* `deningerBauPullback` : the fibre product.
* `deningerBauPullbackProj_surjective`, `deningerBauPullbackProj_ker_divisible` : it is a surjection
  with divisible kernel.
* `deningerBauPullbackFiniteActionEquiv`, `deningerBauPullbackProfiniteIso` : the two consequences.
-/

namespace RHTower

open CategoryTheory

section BaumslagPullback

universe u

variable {ι A H : Type u} [AddCommGroup A] [Module ℚ A] [Group H]

/-- **The fibre product of `a_U` along a homomorphism into the rational vector space.** -/
noncomputable def deningerBauPullback (b : ι → A) (f : H →* Multiplicative A) :
    Subgroup (H × DeningerBau (FreeGroup ι)) :=
  MonoidHom.eqLocus (f.comp (MonoidHom.fst H (DeningerBau (FreeGroup ι))))
    ((deningerBauFreeMap b).comp (MonoidHom.snd H (DeningerBau (FreeGroup ι))))

theorem deningerBauPullback_mem {b : ι → A} {f : H →* Multiplicative A}
    {p : H × DeningerBau (FreeGroup ι)} :
    p ∈ deningerBauPullback b f ↔ f p.1 = deningerBauFreeMap b p.2 := Iff.rfl

/-- The projection of the fibre product to the base. -/
noncomputable def deningerBauPullbackProj (b : ι → A) (f : H →* Multiplicative A) :
    (deningerBauPullback b f : Subgroup (H × DeningerBau (FreeGroup ι))) →* H :=
  (MonoidHom.fst H (DeningerBau (FreeGroup ι))).comp (deningerBauPullback b f).subtype

@[simp]
theorem deningerBauPullbackProj_apply (b : ι → A) (f : H →* Multiplicative A)
    (p : (deningerBauPullback b f : Subgroup (H × DeningerBau (FreeGroup ι)))) :
    deningerBauPullbackProj b f p = (p : H × DeningerBau (FreeGroup ι)).1 := rfl

/-- **The projection is onto**, because `a_U` is. -/
theorem deningerBauPullbackProj_surjective (b : ι → A)
    (hb : Submodule.span ℚ (Set.range b) = ⊤) (f : H →* Multiplicative A) :
    Function.Surjective (deningerBauPullbackProj b f) := by
  intro h
  obtain ⟨r, hr⟩ := deningerBauFree_surjective b hb (f h)
  exact ⟨⟨(h, r), by rw [deningerBauPullback_mem]; exact hr.symm⟩, rfl⟩

/-- **The kernel of the projection is `K_U`, hence divisible.** -/
theorem deningerBauPullbackProj_ker_divisible (b : ι → A) (f : H →* Multiplicative A) :
    DeningerPowerDivisible
      (((deningerBauPullbackProj b f).ker :
        Subgroup (deningerBauPullback b f : Subgroup (H × DeningerBau (FreeGroup ι))))) := by
  intro n hn k
  obtain ⟨⟨⟨h₀, r⟩, hmem⟩, hk⟩ := k
  have h1 : h₀ = 1 := hk
  subst h1
  have hr : deningerBauFreeMap b r = 1 := by
    have h := deningerBauPullback_mem.1 hmem
    rw [map_one] at h
    exact h.symm
  obtain ⟨u, hu, -⟩ := deningerBauFreeKer_uniquelyDivisible b n hn
    ⟨r, MonoidHom.mem_ker.2 hr⟩
  have huval : (u : DeningerBau (FreeGroup ι)) ^ n = r := congrArg Subtype.val hu
  have hu1 : deningerBauFreeMap b (u : DeningerBau (FreeGroup ι)) = 1 := MonoidHom.mem_ker.1 u.2
  have hvmem : ((1 : H), (u : DeningerBau (FreeGroup ι))) ∈ deningerBauPullback b f := by
    rw [deningerBauPullback_mem]
    rw [map_one, hu1]
  refine ⟨⟨⟨((1 : H), (u : DeningerBau (FreeGroup ι))), hvmem⟩, ?_⟩, ?_⟩
  · show ((1 : H), (u : DeningerBau (FreeGroup ι))).1 = 1
    rfl
  · refine Subtype.ext (Subtype.ext ?_)
    show (((1 : H), (u : DeningerBau (FreeGroup ι))) ^ n : H × DeningerBau (FreeGroup ι)) =
      ((1 : H), r)
    rw [Prod.pow_mk, one_pow, huval]

/-- **Clause 5's consequence at the actual object.**  Pulling `a_U` back along any homomorphism into
`A` gives a surjection with divisible kernel, hence an equivalence of finite covering categories. -/
noncomputable def deningerBauPullbackFiniteActionEquiv (b : ι → A)
    (hb : Submodule.span ℚ (Set.range b) = ⊤) (f : H →* Multiplicative A) :
    Action FintypeCat.{u} H ≌
      Action FintypeCat.{u} (deningerBauPullback b f : Subgroup (H × DeningerBau (FreeGroup ι))) :=
  deningerFiniteActionEquivOfDivisible (deningerBauPullbackProj_surjective b hb f)
    (deningerBauPullbackProj_ker_divisible b f)

/-- The same pullback identifies profinite completions. -/
noncomputable def deningerBauPullbackProfiniteIso (b : ι → A)
    (hb : Submodule.span ℚ (Set.range b) = ⊤) (f : H →* Multiplicative A) :
    ProfiniteGrp.profiniteCompletion.obj
        (GrpCat.of (deningerBauPullback b f : Subgroup (H × DeningerBau (FreeGroup ι)))) ≅
      ProfiniteGrp.profiniteCompletion.obj (GrpCat.of H) :=
  deningerProfiniteCompletionIsoOfDivisible (deningerBauPullbackProj b f)
    (deningerBauPullbackProj_surjective b hb f) (deningerBauPullbackProj_ker_divisible b f)

end BaumslagPullback

end RHTower
