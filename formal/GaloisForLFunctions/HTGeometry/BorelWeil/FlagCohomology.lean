import GaloisForLFunctions.HTGeometry.BorelWeil.FlagCech
import GaloisForLFunctions.HTGeometry.BorelWeil.BottProjectiveSpace

/-!
# The cohomology of the Bruhat cover

With the Čech differential of `FlagCech` squaring to zero, the cochains, cocycles and coboundaries
of the Bruhat cover are submodules and their subquotient is the Čech cohomology of `L_λ` on the
flag variety.  In degree zero it receives the Borel–Weil module: every global polynomial section is
a cocycle, injectively.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.cechDModuleLin` — the differential as a linear map.
* `GaloisForLFunctions.HTGeometry.BorelWeil.flagCochains`, `flagCocycles`, `flagCoboundaries`
* `GaloisForLFunctions.HTGeometry.BorelWeil.flagCohomology` — `H^p(G/B, L_λ)`.

## Main results

* `flagCoboundaries_le_flagCocycles` — the subquotient is well formed.
* `polySectionsToH0` — the Borel–Weil module maps into `H⁰`, injectively.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

/-- The Čech differential as a linear map. -/
noncomputable def cechDModuleLin {T : Type*} [DecidableEq T] [LinearOrder T]
    (k : Type*) [CommRing k] {M : Type*} [AddCommGroup M] [Module k M] :
    (Finset T → M) →ₗ[k] (Finset T → M) where
  toFun := cechDModule k
  map_add' ω ω' := by
    funext I
    simp only [cechDModule, Pi.add_apply, smul_add, ← Finset.sum_add_distrib]
  map_smul' c ω := by
    funext I
    show cechDModule k (c • ω) I = c • cechDModule k ω I
    rw [cechDModule, cechDModule, Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [Pi.smul_apply, smul_comm]

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Čech `p`-cochains of the Bruhat cover. -/
noncomputable def flagCochains (N : ℕ) (k : Type*) [Field k] [Infinite k] (lam : Fin N → ℤ)
    (p : ℕ) : Submodule k (Finset (Equiv.Perm (Fin N)) → FlagLoc N k) where
  carrier := {ω | IsFlagCochain lam p ω}
  add_mem' := by
    intro ω ω' hω hω'
    exact ⟨fun I hI => by rw [Pi.add_apply, hω.card I hI, hω'.card I hI, add_zero],
      fun I => Submodule.add_mem _ (hω.mem I) (hω'.mem I)⟩
  zero_mem' := ⟨fun I _ => rfl, fun I => Submodule.zero_mem _⟩
  smul_mem' := by
    intro c ω hω
    exact ⟨fun I hI => by rw [Pi.smul_apply, hω.card I hI, smul_zero],
      fun I => Submodule.smul_mem _ c (hω.mem I)⟩

theorem mem_flagCochains {lam : Fin N → ℤ} {p : ℕ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} :
    ω ∈ flagCochains N k lam p ↔ IsFlagCochain lam p ω := Iff.rfl

/-- Čech `p`-cocycles. -/
noncomputable def flagCocycles (N : ℕ) (k : Type*) [Field k] [Infinite k] (lam : Fin N → ℤ)
    (p : ℕ) : Submodule k (Finset (Equiv.Perm (Fin N)) → FlagLoc N k) :=
  flagCochains N k lam p ⊓ LinearMap.ker (cechDModuleLin k)

/-- Čech `p`-coboundaries. -/
noncomputable def flagCoboundaries (N : ℕ) (k : Type*) [Field k] [Infinite k] (lam : Fin N → ℤ) :
    ℕ → Submodule k (Finset (Equiv.Perm (Fin N)) → FlagLoc N k)
  | 0 => ⊥
  | (q + 1) => Submodule.map (cechDModuleLin k) (flagCochains N k lam q)

theorem flagCoboundaries_le_flagCocycles {lam : Fin N → ℤ} {p : ℕ} :
    flagCoboundaries N k lam p ≤ flagCocycles N k lam p := by
  cases p with
  | zero => exact bot_le
  | succ q =>
    rintro _ ⟨ω, hω, rfl⟩
    exact ⟨flagCechD_isFlagCochain (lam := lam) (p := q) hω, cechDModule_cechDModule k ω⟩

/-- **`H^p(G/B, L_λ)` for the Bruhat cover.** -/
noncomputable abbrev flagCohomology (N : ℕ) (k : Type*) [Field k] [Infinite k]
    (lam : Fin N → ℤ) (p : ℕ) :=
  (flagCocycles N k lam p) ⧸
    Submodule.comap (flagCocycles N k lam p).subtype (flagCoboundaries N k lam p)

/-- The Čech `0`-cochain attached to a global polynomial section. -/
noncomputable def globalCochain (lam : Fin N → ℤ) (p : MvPolynomial (Fin N × Fin N) k) :
    Finset (Equiv.Perm (Fin N)) → FlagLoc N k :=
  fun I => if I.card = 1 then
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p else 0

theorem globalCochain_mem_flagCocycles {lam : Fin N → ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p ∈ polySections lam) :
    globalCochain (fun i => (lam i : ℤ)) p ∈ flagCocycles N k (fun i => (lam i : ℤ)) 0 := by
  classical
  refine ⟨algebraMap_isFlagCochain_zero hp, ?_⟩
  show cechDModule k (globalCochain (fun i => (lam i : ℤ)) p) = 0
  funext I
  simp only [cechDModule, Pi.zero_apply]
  by_cases hI : I.card = 2
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hI
    rcases lt_trichotomy u v with h | rfl | h
    · rw [Finset.sum_pair huv]
      have he1 : ({u, v} : Finset (Equiv.Perm (Fin N))).erase u = {v} := by
        ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => hw.2.resolve_left hw.1, fun hw => ⟨by rw [hw]; exact fun hc => huv hc.symm,
          Or.inr hw⟩⟩
      have he2 : ({u, v} : Finset (Equiv.Perm (Fin N))).erase v = {u} := by
        ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => hw.2.resolve_right hw.1, fun hw => ⟨by rw [hw]; exact huv, Or.inl hw⟩⟩
      rw [he1, he2, cechSign_pair_left (k := k) h, cechSign_pair_right (k := k) h, globalCochain,
        globalCochain, if_pos (Finset.card_singleton v), if_pos (Finset.card_singleton u),
        one_smul, neg_smul, one_smul, add_neg_cancel]
    · exact absurd rfl huv
    · rw [Finset.sum_pair huv]
      have he1 : ({u, v} : Finset (Equiv.Perm (Fin N))).erase u = {v} := by
        ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => hw.2.resolve_left hw.1, fun hw => ⟨by rw [hw]; exact fun hc => huv hc.symm,
          Or.inr hw⟩⟩
      have he2 : ({u, v} : Finset (Equiv.Perm (Fin N))).erase v = {u} := by
        ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => hw.2.resolve_right hw.1, fun hw => ⟨by rw [hw]; exact huv, Or.inl hw⟩⟩
      have hpair : ({u, v} : Finset (Equiv.Perm (Fin N))) = {v, u} := Finset.pair_comm u v
      rw [he1, he2, hpair, cechSign_pair_left (k := k) h, cechSign_pair_right (k := k) h,
        globalCochain, globalCochain, if_pos (Finset.card_singleton v),
        if_pos (Finset.card_singleton u), one_smul, neg_smul, one_smul]
      abel
  · refine Finset.sum_eq_zero fun u hu => ?_
    have hcard : (I.erase u).card ≠ 1 := by
      rw [Finset.card_erase_of_mem hu]
      have hpos : 0 < I.card := Finset.card_pos.mpr ⟨u, hu⟩
      omega
    rw [globalCochain, if_neg hcard, smul_zero]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem algebraMap_flagLoc_injective :
    Function.Injective
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)) := by
  refine IsLocalization.injective (M := Submonoid.powers (totalDenom N k)) (FlagLoc N k) ?_
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact pow_mem (mem_nonZeroDivisors_of_ne_zero totalDenom_ne_zero) n

/-- **The Borel–Weil module injects into `H⁰(G/B, L_λ)`.**  In degree zero there are no
coboundaries, so a global polynomial section is determined by its Čech class. -/
theorem globalCochain_injective {lam : Fin N → ℤ}
    {p q : MvPolynomial (Fin N × Fin N) k}
    (h : globalCochain lam p = globalCochain (k := k) lam q) : p = q := by
  classical
  have hcard : ({(1 : Equiv.Perm (Fin N))} : Finset (Equiv.Perm (Fin N))).card = 1 :=
    Finset.card_singleton _
  have h1 := congrFun h {(1 : Equiv.Perm (Fin N))}
  rw [globalCochain, globalCochain, if_pos hcard, if_pos hcard] at h1
  exact algebraMap_flagLoc_injective h1

theorem flagCoboundaries_zero (lam : Fin N → ℤ) : flagCoboundaries N k lam 0 = ⊥ := rfl

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- Above the size of the cover there are no cochains. -/
theorem flagCochains_eq_bot_of_card_lt {lam : Fin N → ℤ} {p : ℕ}
    (hp : Fintype.card (Equiv.Perm (Fin N)) < p + 1) : flagCochains N k lam p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun ω hω => ?_
  funext I
  refine hω.card I ?_
  have hcard : I.card ≤ Fintype.card (Equiv.Perm (Fin N)) := Finset.card_le_univ I
  omega

/-- **Vanishing above the size of the cover.**  The Čech cohomology of the Bruhat cover vanishes in
degrees at least `|W|`. -/
theorem flagCohomology_subsingleton_of_card_lt {lam : Fin N → ℤ} {p : ℕ}
    (hp : Fintype.card (Equiv.Perm (Fin N)) < p + 1) :
    Subsingleton (flagCohomology N k lam p) := by
  have hbot : flagCocycles N k lam p = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun ω hω => ?_
    have := (Submodule.eq_bot_iff _).mp (flagCochains_eq_bot_of_card_lt (k := k) hp) ω hω.1
    exact this
  haveI hsub : Subsingleton ↥(flagCocycles N k lam p) := by
    rw [hbot]
    infer_instance
  infer_instance

/-- In degree zero there are no coboundaries, so `H⁰` is the module of cocycles. -/
theorem flagCohomology_zero_eq :
    ∀ (lam : Fin N → ℤ),
      Submodule.comap (flagCocycles N k lam 0).subtype (flagCoboundaries N k lam 0) = ⊥ := by
  intro lam
  rw [flagCoboundaries_zero, Submodule.comap_bot, Submodule.ker_subtype]

end GaloisForLFunctions.HTGeometry.BorelWeil
