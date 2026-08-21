import GaloisForLFunctions.HTGeometry.BorelWeil.CellSections
import GaloisForLFunctions.HTGeometry.BorelWeil.CechHomotopy

/-!
# The Čech complex of the Bruhat cover

With the cover of `G/B` by the `|W|` Bruhat cells (`BruhatCover`), the sections of `L_λ` over each
intersection of cells (`CellSections`), and the inclusions between them, the Čech cochains of the
cover are the families `ω` indexed by subsets of the Weyl group with `ω I` a section over the
intersection of the cells in `I`, supported in one cardinality.  The differential is the usual
alternating sum, which makes sense because the inclusions are inclusions of submodules of one
ambient localization.

The Weyl group carries no canonical order, so one is fixed arbitrarily; it only enters through the
Čech signs and different choices give isomorphic complexes.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.cechDModule` — the Čech differential on module-valued
  families.
* `GaloisForLFunctions.HTGeometry.BorelWeil.IsFlagCochain`
* `GaloisForLFunctions.HTGeometry.BorelWeil.flagCechD`

## Main results

* `flagCechD_isFlagCochain` — the differential raises the degree of a Čech cochain by one.
* `algebraMap_isFlagCochain_zero` — a global polynomial section gives a Čech `0`-cochain.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

/-- The Čech differential on families valued in a module. -/
noncomputable def cechDModule {T : Type*} [DecidableEq T] [LinearOrder T]
    (k : Type*) [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
    (ω : Finset T → M) : Finset T → M :=
  fun I => ∑ u ∈ I, (cechSign I u : k) • ω (I.erase u)

variable {N : ℕ} {k : Type*} [Field k]

/-- An arbitrary linear order on the Weyl group; it only fixes the Čech signs. -/
noncomputable scoped instance weylLinearOrder (N : ℕ) : LinearOrder (Equiv.Perm (Fin N)) :=
  LinearOrder.lift' (Fintype.equivFin (Equiv.Perm (Fin N))) (Equiv.injective _)

/-- The Čech cochain conditions for the Bruhat cover. -/
structure IsFlagCochain [Infinite k] (lam : Fin N → ℤ) (p : ℕ)
    (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) : Prop where
  card : ∀ I : Finset (Equiv.Perm (Fin N)), I.card ≠ p + 1 → ω I = 0
  mem : ∀ I : Finset (Equiv.Perm (Fin N)), ω I ∈ cellSections N k I lam

/-- The Čech differential of the Bruhat cover. -/
noncomputable def flagCechD (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) :
    Finset (Equiv.Perm (Fin N)) → FlagLoc N k :=
  cechDModule k ω

/-- **The differential raises the Čech degree by one.** -/
theorem flagCechD_isFlagCochain [Infinite k] {lam : Fin N → ℤ} {p : ℕ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} (hω : IsFlagCochain lam p ω) :
    IsFlagCochain lam (p + 1) (flagCechD ω) := by
  classical
  constructor
  · intro I hI
    rw [flagCechD, cechDModule]
    refine Finset.sum_eq_zero fun u hu => ?_
    have hcard : (I.erase u).card ≠ p + 1 := by
      rw [Finset.card_erase_of_mem hu]
      have hpos : 0 < I.card := Finset.card_pos.mpr ⟨u, hu⟩
      omega
    rw [hω.card _ hcard, smul_zero]
  · intro I
    rw [flagCechD, cechDModule]
    refine Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ ?_
    exact cellSections_mono (Finset.erase_subset u I) lam (hω.mem (I.erase u))

/-- **A global polynomial section is a Čech `0`-cochain.** -/
theorem algebraMap_isFlagCochain_zero [Infinite k] {lam : Fin N → ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p ∈ polySections lam) :
    IsFlagCochain (fun i => (lam i : ℤ)) 0
      (fun I => if I.card = 1 then
        algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p else 0) := by
  classical
  constructor
  · intro I hI
    rw [if_neg hI]
  · intro I
    by_cases hI : I.card = 1
    · rw [if_pos hI]
      exact algebraMap_mem_cellSections hp I
    · rw [if_neg hI]
      exact Submodule.zero_mem _

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

/-- The two ways of removing a pair of indices carry opposite Čech signs. -/
theorem cechSign_erase_add {T : Type*} [DecidableEq T] [LinearOrder T] {k : Type*} [CommRing k]
    {I : Finset T} {u v : T} (hu : u ∈ I) (hv : v ∈ I) (huv : u ≠ v) :
    (cechSign I u : k) * cechSign (I.erase u) v
      + (cechSign I v : k) * cechSign (I.erase v) u = 0 := by
  rw [cechSign, cechSign, cechSign, cechSign, ← pow_add, ← pow_add]
  rcases lt_or_gt_of_ne huv with h | h
  · have h1 : belowCard (I.erase u) v + 1 = belowCard I v := belowCard_erase_of_lt hu h
    have h2 : belowCard (I.erase v) u = belowCard I u :=
      belowCard_erase_of_not_lt (not_lt.mpr h.le)
    have hexp : belowCard I v + belowCard (I.erase v) u
        = (belowCard I u + belowCard (I.erase u) v) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  · have h1 : belowCard (I.erase v) u + 1 = belowCard I u := belowCard_erase_of_lt hv h
    have h2 : belowCard (I.erase u) v = belowCard I v :=
      belowCard_erase_of_not_lt (not_lt.mpr h.le)
    have hexp : belowCard I u + belowCard (I.erase u) v
        = (belowCard I v + belowCard (I.erase v) u) + 1 := by omega
    rw [hexp, pow_succ]
    ring

/-- **The Čech differential squares to zero.** -/
theorem cechDModule_cechDModule {T : Type*} [DecidableEq T] [LinearOrder T]
    (k : Type*) [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
    (ω : Finset T → M) : cechDModule k (cechDModule k ω) = 0 := by
  classical
  funext I
  simp only [Pi.zero_apply]
  have hstep : ∀ u ∈ I, (cechSign I u : k) • cechDModule k ω (I.erase u)
      = ∑ v ∈ I.erase u,
          ((cechSign I u : k) * cechSign (I.erase u) v) • ω ((I.erase u).erase v) := by
    intro u _
    rw [cechDModule, Finset.smul_sum]
    exact Finset.sum_congr rfl fun v _ => smul_smul _ _ _
  rw [cechDModule, Finset.sum_congr rfl hstep,
    Finset.sum_sigma' I (fun u => I.erase u)
      (fun u v => ((cechSign I u : k) * cechSign (I.erase u) v) • ω ((I.erase u).erase v))]
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hu, hv⟩ := hx
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    have hvI : v ∈ I := Finset.mem_of_mem_erase hv
    have herase : (I.erase v).erase u = (I.erase u).erase v := by
      ext w
      simp only [Finset.mem_erase]
      tauto
    show ((cechSign I u : k) * cechSign (I.erase u) v) • ω ((I.erase u).erase v)
      + ((cechSign I v : k) * cechSign (I.erase v) u) • ω ((I.erase v).erase u) = 0
    rw [herase, ← add_smul, cechSign_erase_add hu hvI (Ne.symm hvu), zero_smul]
  · rintro ⟨u, v⟩ hx _
    rw [Finset.mem_sigma] at hx
    have hvu : v ≠ u := (Finset.mem_erase.mp hx.2).1
    intro hcon
    exact hvu (congrArg Sigma.fst hcon)
  · rintro ⟨u, v⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hu, hv⟩ := hx
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_of_mem_erase hv,
      Finset.mem_erase.mpr ⟨fun hc => (Finset.mem_erase.mp hv).1 hc.symm, hu⟩⟩
  · rintro ⟨u, v⟩ _
    rfl

/-- **The Čech complex of the Bruhat cover is a complex.** -/
theorem flagCechD_flagCechD {N : ℕ} {k : Type*} [Field k]
    (ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k) : flagCechD (flagCechD ω) = 0 :=
  cechDModule_cechDModule k ω

end GaloisForLFunctions.HTGeometry.BorelWeil
