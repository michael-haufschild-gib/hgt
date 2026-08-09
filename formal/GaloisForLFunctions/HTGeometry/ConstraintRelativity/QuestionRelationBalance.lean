import Mathlib

/-!
# The dynamic question–relation balance law

For a nested pair of potential-law objects `P ≤ P'` and relation objects `R ≤ R'` with
`R ≤ P` and `R' ≤ P'`, the exposed freedoms `F = P/R` and `F' = P'/R'` are joined by a natural
four-term exact sequence

`0 → K → F → F' → C → 0`,  `K = (P ∩ R')/R`,  `C = P'/(P + R')`.

`K` is the old freedom killed by the new relations and `C` is the genuinely new freedom.  Passing
to dimensions gives the balance `dim F' + dim K = dim F + dim C`: a scalar rank increment cannot
tell creation from annihilation.

All four objects are realized here as submodules of ambient quotients, so exactness is a chain of
submodule identities; the accompanying linear equivalences certify that they are the quotients
named above.
-/

namespace HTGeometry.ConstraintRelativity

open Submodule LinearMap Module

variable {𝕜 M : Type*} [Ring 𝕜] [AddCommGroup M] [Module 𝕜 M]

/-! ## Two reusable submodule lemmas -/

/-- Two submodules containing `N` intersect after passing to `M ⧸ N` exactly as they do in `M`. -/
theorem map_mkQ_inf (N A B : Submodule 𝕜 M) (hA : N ≤ A) (hB : N ≤ B) :
    Submodule.map N.mkQ (A ⊓ B) = Submodule.map N.mkQ A ⊓ Submodule.map N.mkQ B := by
  have hkerA : LinearMap.ker N.mkQ ≤ A := by rwa [Submodule.ker_mkQ]
  have hkerB : LinearMap.ker N.mkQ ≤ B := by rwa [Submodule.ker_mkQ]
  have hsurj : Function.Surjective N.mkQ := N.mkQ_surjective
  have h1 : Submodule.comap N.mkQ (Submodule.map N.mkQ A ⊓ Submodule.map N.mkQ B) = A ⊓ B := by
    rw [Submodule.comap_inf, Submodule.comap_map_eq_self hkerA, Submodule.comap_map_eq_self hkerB]
  calc Submodule.map N.mkQ (A ⊓ B)
      = Submodule.map N.mkQ
          (Submodule.comap N.mkQ (Submodule.map N.mkQ A ⊓ Submodule.map N.mkQ B)) := by rw [h1]
    _ = Submodule.map N.mkQ A ⊓ Submodule.map N.mkQ B :=
        Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)

/-- The image of `A` in `M ⧸ N` is the quotient of `A` by the trace of `N` on it. -/
noncomputable def mapMkQEquivQuotient (N A : Submodule 𝕜 M) :
    (A ⧸ N.submoduleOf A) ≃ₗ[𝕜] Submodule.map N.mkQ A := by
  classical
  refine (Submodule.quotEquivOfEq _ _ ?_).symm.trans
    (((N.mkQ.comp A.subtype).quotKerEquivRange).trans (LinearEquiv.ofEq _ _ ?_))
  · rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  · rw [LinearMap.range_comp, Submodule.range_subtype]

/-- Rank–nullity for the restriction of a linear map to a submodule. -/
theorem finrank_map_add_finrank_inf_ker {K V W : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] (f : V →ₗ[K] W)
    (p : Submodule K V) :
    finrank K (Submodule.map f p) + finrank K (p ⊓ LinearMap.ker f : Submodule K V)
      = finrank K p := by
  have hrn := (f.domRestrict p).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
  have hEq : finrank K ((LinearMap.ker f).comap p.subtype)
      = finrank K (p ⊓ LinearMap.ker f : Submodule K V) := by
    rw [← Submodule.map_comap_subtype p (LinearMap.ker f)]
    exact (Submodule.equivMapOfInjective p.subtype (Submodule.injective_subtype p) _).finrank_eq
  rw [hEq] at hrn
  exact hrn

/-! ## The constraint stress sequence -/

variable (Rold Pold Pnew Rnew : Submodule 𝕜 M)

/-- Exposed old freedom `F = P/R`, realized inside `M ⧸ R`. -/
def freedomOld : Submodule 𝕜 (M ⧸ Rold) := Submodule.map Rold.mkQ Pold

/-- Exposed new freedom `F' = P'/R'`, realized inside `M ⧸ R'`. -/
def freedomNew : Submodule 𝕜 (M ⧸ Rnew) := Submodule.map Rnew.mkQ Pnew

/-- Killed old freedom `K = (P ∩ R')/R`, realized inside `M ⧸ R`. -/
def killedFreedom : Submodule 𝕜 (M ⧸ Rold) := Submodule.map Rold.mkQ (Pold ⊓ Rnew)

/-- Genuinely new freedom `C = P'/(P + R')`, realized inside `M ⧸ (P + R')`. -/
def createdFreedom : Submodule 𝕜 (M ⧸ (Pold ⊔ Rnew)) := Submodule.map (Pold ⊔ Rnew).mkQ Pnew

/-- The constraint-stress map `F → F'`, induced by `P ⊆ P'` and `R ⊆ R'`. -/
def stressMap (h : Rold ≤ Rnew) : (M ⧸ Rold) →ₗ[𝕜] M ⧸ Rnew :=
  Submodule.mapQ Rold Rnew LinearMap.id h

/-- The cokernel projection `F' → C`. -/
def cokerMap : (M ⧸ Rnew) →ₗ[𝕜] M ⧸ (Pold ⊔ Rnew) :=
  Submodule.mapQ Rnew (Pold ⊔ Rnew) LinearMap.id le_sup_right

variable {Rold Pold Pnew Rnew}

@[simp]
theorem stressMap_mkQ (h : Rold ≤ Rnew) (m : M) :
    stressMap Rold Rnew h (Rold.mkQ m) = Rnew.mkQ m := by
  simp [stressMap]

@[simp]
theorem cokerMap_mkQ (m : M) :
    cokerMap Pold Rnew (Rnew.mkQ m) = (Pold ⊔ Rnew).mkQ m := by
  simp [cokerMap]

theorem ker_stressMap (h : Rold ≤ Rnew) :
    LinearMap.ker (stressMap Rold Rnew h) = Submodule.map Rold.mkQ Rnew := by
  ext x
  obtain ⟨m, rfl⟩ := Rold.mkQ_surjective x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, stressMap_mkQ] at hx
    exact ⟨m, (Submodule.Quotient.mk_eq_zero _).1 hx, rfl⟩
  · rintro ⟨n, hn, hnm⟩
    rw [LinearMap.mem_ker, stressMap_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hnm
    have hm : m = n - (n - m) := (sub_sub_cancel n m).symm
    rw [hm]
    exact Rnew.sub_mem hn (h hnm)

theorem ker_cokerMap :
    LinearMap.ker (cokerMap Pold Rnew) = Submodule.map Rnew.mkQ (Pold ⊔ Rnew) := by
  ext x
  obtain ⟨m, rfl⟩ := Rnew.mkQ_surjective x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, cokerMap_mkQ] at hx
    exact ⟨m, (Submodule.Quotient.mk_eq_zero _).1 hx, rfl⟩
  · rintro ⟨n, hn, hnm⟩
    rw [LinearMap.mem_ker, cokerMap_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hnm
    have hm : m = n - (n - m) := (sub_sub_cancel n m).symm
    rw [hm]
    exact Submodule.sub_mem _ hn ((le_sup_right : Rnew ≤ Pold ⊔ Rnew) hnm)

/-- The killed-freedom term sits inside the old freedom. -/
theorem killedFreedom_le_freedomOld : killedFreedom Rold Pold Rnew ≤ freedomOld Rold Pold :=
  Submodule.map_mono inf_le_left

/-- **Exactness at `F`.**  The kernel of the constraint-stress map on the old freedom is exactly
the killed old freedom `(P ∩ R')/R`. -/
theorem freedomOld_inf_ker_stressMap (hRP : Rold ≤ Pold) (hRR : Rold ≤ Rnew) :
    freedomOld Rold Pold ⊓ LinearMap.ker (stressMap Rold Rnew hRR)
      = killedFreedom Rold Pold Rnew := by
  rw [ker_stressMap, freedomOld, killedFreedom, map_mkQ_inf Rold Pold Rnew hRP hRR]

/-- The image of the old freedom under the constraint-stress map is `(P + R')/R'`. -/
theorem map_stressMap_freedomOld (hRR : Rold ≤ Rnew) :
    Submodule.map (stressMap Rold Rnew hRR) (freedomOld Rold Pold)
      = Submodule.map Rnew.mkQ Pold := by
  rw [freedomOld, ← Submodule.map_comp]
  congr 1

/-- **Exactness at `F'`.**  The image of the old freedom is exactly the kernel of the projection
onto the created freedom. -/
theorem map_stressMap_eq_freedomNew_inf_ker (hRR : Rold ≤ Rnew) (hPP : Pold ≤ Pnew)
    (hRP' : Rnew ≤ Pnew) :
    Submodule.map (stressMap Rold Rnew hRR) (freedomOld Rold Pold)
      = freedomNew Pnew Rnew ⊓ LinearMap.ker (cokerMap Pold Rnew) := by
  rw [map_stressMap_freedomOld, ker_cokerMap, freedomNew,
    ← map_mkQ_inf Rnew Pnew (Pold ⊔ Rnew) hRP' le_sup_right,
    inf_eq_right.2 (sup_le hPP hRP'), Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]

/-- **Exactness at `C`.**  The projection from the new freedom onto the created freedom is
surjective. -/
theorem map_cokerMap_freedomNew :
    Submodule.map (cokerMap Pold Rnew) (freedomNew Pnew Rnew)
      = createdFreedom Pold Pnew Rnew := by
  rw [freedomNew, ← Submodule.map_comp, createdFreedom]
  congr 1

/-! ## Identification of the four terms -/

/-- `F = P/R`. -/
noncomputable def freedomOldEquiv :
    (Pold ⧸ Rold.submoduleOf Pold) ≃ₗ[𝕜] freedomOld Rold Pold :=
  mapMkQEquivQuotient Rold Pold

/-- `F' = P'/R'`. -/
noncomputable def freedomNewEquiv :
    (Pnew ⧸ Rnew.submoduleOf Pnew) ≃ₗ[𝕜] freedomNew Pnew Rnew :=
  mapMkQEquivQuotient Rnew Pnew

/-- `K = (P ∩ R')/R`. -/
noncomputable def killedFreedomEquiv :
    ((Pold ⊓ Rnew : Submodule 𝕜 M) ⧸ Rold.submoduleOf (Pold ⊓ Rnew))
      ≃ₗ[𝕜] killedFreedom Rold Pold Rnew :=
  mapMkQEquivQuotient Rold (Pold ⊓ Rnew)

/-- `C = P'/(P + R')`. -/
noncomputable def createdFreedomEquiv :
    (Pnew ⧸ (Pold ⊔ Rnew).submoduleOf Pnew) ≃ₗ[𝕜] createdFreedom Pold Pnew Rnew :=
  mapMkQEquivQuotient (Pold ⊔ Rnew) Pnew

/-! ## The dimension balance -/

section Dimension

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Rold Pold Pnew Rnew : Submodule K V}

/-- **Exact question–relation balance in dimensions.**
`dim F' + dim K = dim F + dim C`: the net freedom increment is the created freedom minus the
killed freedom, and a scalar rank change cannot separate the two. -/
theorem finrank_balance (hRP : Rold ≤ Pold) (hPP : Pold ≤ Pnew) (hRR : Rold ≤ Rnew)
    (hRP' : Rnew ≤ Pnew) :
    finrank K (freedomNew Pnew Rnew) + finrank K (killedFreedom Rold Pold Rnew)
      = finrank K (freedomOld Rold Pold) + finrank K (createdFreedom Pold Pnew Rnew) := by
  have h1 := finrank_map_add_finrank_inf_ker (stressMap Rold Rnew hRR) (freedomOld Rold Pold)
  have h2 := finrank_map_add_finrank_inf_ker (cokerMap Pold Rnew) (freedomNew Pnew Rnew)
  rw [freedomOld_inf_ker_stressMap hRP hRR] at h1
  rw [← map_stressMap_eq_freedomNew_inf_ker hRR hPP hRP', map_cokerMap_freedomNew] at h2
  omega

/-- The signed balance `dim F' - dim F = dim C - dim K`. -/
theorem finrank_balance_sub (hRP : Rold ≤ Pold) (hPP : Pold ≤ Pnew) (hRR : Rold ≤ Rnew)
    (hRP' : Rnew ≤ Pnew) :
    (finrank K (freedomNew Pnew Rnew) : ℤ) - finrank K (freedomOld Rold Pold)
      = (finrank K (createdFreedom Pold Pnew Rnew) : ℤ)
        - finrank K (killedFreedom Rold Pold Rnew) := by
  have := finrank_balance hRP hPP hRR hRP'
  omega

end Dimension

/-! ## The three phases -/

/-- **Pure question creation.**  If the relations do not change, no old freedom is killed. -/
theorem killedFreedom_eq_bot_of_rel_eq (h : Rnew = Rold) :
    killedFreedom Rold Pold Rnew = ⊥ := by
  subst h
  rw [killedFreedom, eq_bot_iff]
  rintro x ⟨m, hm, rfl⟩
  simp only [Submodule.mem_bot, Submodule.mkQ_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2 hm.2

/-- **Pure relation creation.**  If the potential-law object does not change, no new freedom is
created. -/
theorem createdFreedom_eq_bot_of_pot_eq (h : Pnew = Pold) :
    createdFreedom Pold Pnew Rnew = ⊥ := by
  subst h
  rw [createdFreedom, eq_bot_iff]
  rintro x ⟨m, hm, rfl⟩
  simp only [Submodule.mem_bot, Submodule.mkQ_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2 ((le_sup_left : Pnew ≤ Pnew ⊔ Rnew) hm)

/-- In the pure-relation phase the killed freedom is exactly `R'/R`. -/
theorem killedFreedom_of_le (hRP' : Rnew ≤ Pold) :
    killedFreedom Rold Pold Rnew = Submodule.map Rold.mkQ Rnew := by
  rw [killedFreedom, inf_eq_right.2 hRP']

/-! ## Non-recoverability of the oriented event pair -/

section Witness

variable (K : Type*) [Field K]

/-- The trivial source operation: no freedom is killed and none is created, and the net freedom
increment is zero. -/
theorem trivial_event :
    finrank K (killedFreedom (⊥ : Submodule K (K × K)) ⊥ ⊥) = 0 ∧
      finrank K (createdFreedom (⊥ : Submodule K (K × K)) ⊥ ⊥) = 0 ∧
      finrank K (freedomNew (⊥ : Submodule K (K × K)) ⊥)
        = finrank K (freedomOld (⊥ : Submodule K (K × K)) ⊥) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [killedFreedom, inf_idem, Submodule.map_bot, finrank_bot]
  · rw [createdFreedom, Submodule.map_bot, finrank_bot]
  · rw [freedomNew, freedomOld]

/-- A coupled source operation with the same zero net freedom increment but a nontrivial oriented
event pair: one dimension of old freedom is killed and one dimension of new freedom is created.
Together with `trivial_event` this shows the endpoint difference `dim F' - dim F` does not
determine `(K, C)`. -/
theorem coupled_event :
    finrank K (killedFreedom (⊥ : Submodule K (K × K)) (Submodule.span K {((1 : K), (0 : K))})
        (Submodule.span K {((1 : K), (0 : K))})) = 1 ∧
      finrank K (createdFreedom (Submodule.span K {((1 : K), (0 : K))}) ⊤
        (Submodule.span K {((1 : K), (0 : K))})) = 1 ∧
      finrank K (freedomNew (⊤ : Submodule K (K × K)) (Submodule.span K {((1 : K), (0 : K))}))
        = finrank K (freedomOld (⊥ : Submodule K (K × K))
            (Submodule.span K {((1 : K), (0 : K))})) := by
  have hne : ((1 : K), (0 : K)) ≠ 0 := by simp [Prod.ext_iff]
  have hspan : finrank K (Submodule.span K {((1 : K), (0 : K))}) = 1 :=
    finrank_span_singleton hne
  have hbotinj : Function.Injective (⊥ : Submodule K (K × K)).mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
  have hbot : ∀ P : Submodule K (K × K),
      finrank K (Submodule.map (⊥ : Submodule K (K × K)).mkQ P) = finrank K P := fun P =>
    ((Submodule.equivMapOfInjective _ hbotinj P).finrank_eq).symm
  have hquot : finrank K ((K × K) ⧸ Submodule.span K {((1 : K), (0 : K))}) = 1 := by
    have hq := (Submodule.span K {((1 : K), (0 : K))}).finrank_quotient_add_finrank
    rw [hspan] at hq
    simp only [Module.finrank_prod, Module.finrank_self] at hq
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [killedFreedom, inf_idem, hbot, hspan]
  · rw [createdFreedom, sup_idem, Submodule.map_top, Submodule.range_mkQ, finrank_top]
    exact hquot
  · rw [freedomNew, freedomOld, Submodule.map_top, Submodule.range_mkQ, finrank_top, hbot, hspan,
      hquot]

end Witness

end HTGeometry.ConstraintRelativity
