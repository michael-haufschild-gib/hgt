import GaloisForLFunctions.HTGeometry.BorelWeil.FlagCech

/-!
# The cone homotopy of the alternating Čech complex with module coefficients

For functions `ω : Finset T → M` with values in a module, the Čech differential
`(dω) I = ∑_{u ∈ I} ε(I, u) ω(I ∖ u)` and, for an index `u₀`, the cone operator

`(h ω) I = if u₀ ∈ I then 0 else ε(I ∪ u₀, u₀) ω(I ∪ u₀)`

satisfy `d ∘ h + h ∘ d = id` on every subset `I`, including the empty one.  This is the module
form of the scalar identity `cechD_cechH_add`: inserting `u₀` and then deleting it again returns
the original subset with sign `ε² = 1`, while deleting `u ≠ u₀` before or after inserting `u₀`
produces the same subset with opposite signs.

* `HTGeometry.cechHModule` : the cone operator.
* `HTGeometry.cechDModule_cechHModule_add` : the homotopy identity.
-/

namespace HTGeometry

open GaloisForLFunctions.HTGeometry.BorelWeil

variable {T : Type*} [DecidableEq T] [LinearOrder T] (k : Type*) [CommRing k]
  {M : Type*} [AddCommGroup M] [Module k M]

/-- The cone operator attached to an index `u₀`. -/
def cechHModule (u₀ : T) (ω : Finset T → M) : Finset T → M :=
  fun I => if u₀ ∈ I then 0 else (cechSign (insert u₀ I) u₀ : k) • ω (insert u₀ I)

/-- The two sign products in the cone identity are opposite. -/
theorem cechSign_insert_erase {I : Finset T} {u₀ u : T} (hu₀ : u₀ ∉ I) (hu : u ∈ I) :
    (cechSign (insert u₀ I) u₀ : k) * cechSign (insert u₀ I) u
      = -((cechSign I u : k) * cechSign (insert u₀ (I.erase u)) u₀) := by
  have hne : u ≠ u₀ := fun hc => hu₀ (hc ▸ hu)
  rw [cechSign, cechSign, cechSign, cechSign, ← pow_add, ← pow_add, belowCard_insert_self]
  have hexp : belowCard I u₀ + belowCard (insert u₀ I) u
      = belowCard I u + belowCard (insert u₀ (I.erase u)) u₀ + 1 := by
    have h1 : belowCard (insert u₀ (I.erase u)) u₀ = belowCard (I.erase u) u₀ :=
      belowCard_insert_self _ _
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h2 : belowCard (insert u₀ I) u = belowCard I u :=
        belowCard_insert_of_not_lt (not_lt.mpr (le_of_lt hlt))
      have h3 := belowCard_erase_of_lt hu hlt
      omega
    · have h2 : belowCard (insert u₀ I) u = belowCard I u + 1 :=
        belowCard_insert_of_lt hgt hu₀
      have h3 : belowCard (I.erase u) u₀ = belowCard I u₀ :=
        belowCard_erase_of_not_lt (not_lt.mpr (le_of_lt hgt))
      omega
  rw [hexp, pow_succ]
  ring

/-- **The cone homotopy identity** `d h + h d = id`, in every subset. -/
theorem cechDModule_cechHModule_add (u₀ : T) (ω : Finset T → M) (I : Finset T) :
    cechDModule k (cechHModule k u₀ ω) I + cechHModule k u₀ (cechDModule k ω) I = ω I := by
  by_cases hu₀ : u₀ ∈ I
  · have hH : cechHModule k u₀ (cechDModule k ω) I = 0 := by rw [cechHModule, if_pos hu₀]
    rw [hH, add_zero, cechDModule, Finset.sum_eq_single u₀]
    · rw [cechHModule, if_neg (Finset.notMem_erase u₀ I), Finset.insert_erase hu₀, smul_smul,
        cechSign_mul_self, one_smul]
    · intro u _ hne
      have : u₀ ∈ I.erase u := Finset.mem_erase.mpr ⟨fun hc => hne hc.symm, hu₀⟩
      rw [cechHModule, if_pos this, smul_zero]
    · intro hcon; exact absurd hu₀ hcon
  · have hins : ∀ u ∈ I, u₀ ∉ I.erase u := fun u _ hc => hu₀ (Finset.mem_of_mem_erase hc)
    have hD : cechDModule k (cechHModule k u₀ ω) I
        = ∑ u ∈ I, ((cechSign I u : k) * cechSign (insert u₀ (I.erase u)) u₀)
            • ω (insert u₀ (I.erase u)) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [cechHModule, if_neg (hins u hu), smul_smul]
    have hsplit : cechDModule k ω (insert u₀ I)
        = (cechSign (insert u₀ I) u₀ : k) • ω I
          + ∑ u ∈ I, (cechSign (insert u₀ I) u : k) • ω ((insert u₀ I).erase u) := by
      rw [cechDModule, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self u₀ I),
        Finset.erase_insert hu₀]
    have hH : cechHModule k u₀ (cechDModule k ω) I
        = ω I + ∑ u ∈ I, ((cechSign (insert u₀ I) u₀ : k) * cechSign (insert u₀ I) u)
            • ω (insert u₀ (I.erase u)) := by
      rw [cechHModule, if_neg hu₀, hsplit, smul_add, smul_smul, cechSign_mul_self, one_smul,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun u hu => ?_
      have hne : u ≠ u₀ := fun hc => hu₀ (hc ▸ hu)
      rw [smul_smul, Finset.erase_insert_of_ne (Ne.symm hne)]
    rw [hD, hH, ← add_assoc, add_comm _ (ω I), add_assoc, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero fun u hu => by rw [cechSign_insert_erase k hu₀ hu, neg_smul,
        add_neg_cancel], add_zero]

theorem cechDModule_add (ω₁ ω₂ : Finset T → M) :
    cechDModule k (ω₁ + ω₂) = cechDModule k ω₁ + cechDModule k ω₂ := by
  funext I
  simp only [cechDModule, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem cechHModule_add (u₀ : T) (ω₁ ω₂ : Finset T → M) :
    cechHModule k u₀ (ω₁ + ω₂) = cechHModule k u₀ ω₁ + cechHModule k u₀ ω₂ := by
  funext I
  by_cases h : u₀ ∈ I <;> simp [cechHModule, h, smul_add]

/-- The cone operator lowers the cardinality of the support by one. -/
theorem cechHModule_eq_zero_of_card {u₀ : T} {ω : Finset T → M} {p : ℕ}
    (hω : ∀ I : Finset T, I.card ≠ p → ω I = 0) (I : Finset T) (hI : I.card + 1 ≠ p) :
    cechHModule k u₀ ω I = 0 := by
  rw [cechHModule]
  split_ifs with h
  · rfl
  · rw [hω _ (by rwa [Finset.card_insert_of_notMem h]), smul_zero]

end HTGeometry
