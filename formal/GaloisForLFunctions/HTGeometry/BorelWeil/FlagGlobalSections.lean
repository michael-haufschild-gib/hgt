import GaloisForLFunctions.HTGeometry.BorelWeil.FlagDenominator
import GaloisForLFunctions.HTGeometry.BorelWeil.FlagCohomology
import Mathlib.Algebra.CharZero.Infinite

/-!
# Global sections of the line bundle on the flag variety

A Čech `0`-cocycle for the Bruhat cover is a single element of the localization that is regular on
every cell and semi-invariant of weight `λ`.  A power of the determinant clears its denominator, and
the resulting polynomial is a section of weight `λ + M`, hence divisible by `det^M` with quotient a
section of weight `λ`.  So the cocycle is a global polynomial section, and

`H⁰(G/B, L_λ) ≅ H⁰(λ)`,

the irreducible representation of highest weight `λ`.  This is the Borel–Weil theorem for the flag
variety itself rather than for its coordinate model.

## Main results

* `exists_polySections_eq_algebraMap` — an element regular on all cells is a polynomial section.
* `exists_globalCochain_eq` — every `0`-cocycle comes from a global polynomial section.
* `polySectionsEquivH0` — `H⁰(λ) ≃ₗ H⁰(G/B, L_λ)`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem denomOf_singleton (σ : Equiv.Perm (Fin N)) :
    denomOf N k {σ} = cellDenomPoly N k σ := by
  rw [denomOf, Finset.prod_singleton]

theorem exists_pow_mem_denomIdeal {x : FlagLoc N k} {σ : Equiv.Perm (Fin N)}
    (hx : x ∈ denomBounded N k {σ}) : ∃ m : ℕ, cellDenomPoly N k σ ^ m ∈ denomIdeal x := by
  obtain ⟨m, p, hp⟩ := hx
  rw [denomOf_singleton] at hp
  exact ⟨m, p, by rw [map_pow]; exact hp⟩

/-- The product of semi-invariants is semi-invariant of the sum of the weights. -/
theorem mul_mem_flagSemiInv {lam mu : Fin N → ℤ} {x y : FlagLoc N k}
    (hx : x ∈ flagSemiInv N k lam) (hy : y ∈ flagSemiInv N k mu) :
    x * y ∈ flagSemiInv N k (fun i => lam i + mu i) := by
  intro B hB
  rw [map_mul, hx B hB, hy B hB, smul_mul_smul_comm]
  congr 1
  rw [borelCharZ, borelCharZ, borelCharZ, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (zpow_add₀ (hB.2 i) _ _).symm

theorem borelCharMat_add (lam mu : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) k) :
    borelCharMat (fun i => lam i + mu i) B = borelCharMat lam B * borelCharMat mu B := by
  rw [borelCharMat, borelCharMat, borelCharMat, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun _ _ => pow_add _ _ _

/-- The product of semi-invariants of natural-number weights, in cast form. -/
theorem mul_mem_flagSemiInv_natCast {lam mu : Fin N → ℕ} {x y : FlagLoc N k}
    (hx : x ∈ flagSemiInv N k (fun i => (lam i : ℤ)))
    (hy : y ∈ flagSemiInv N k (fun i => (mu i : ℤ))) :
    x * y ∈ flagSemiInv N k (fun i => ((lam i + mu i : ℕ) : ℤ)) := by
  intro B hB
  rw [map_mul, hx B hB, hy B hB, smul_mul_smul_comm, borelCharZ_natCast, borelCharZ_natCast,
    borelCharZ_natCast, borelCharMat_add]

theorem one_mem_polySections : (1 : MvPolynomial (Fin N × Fin N) k) ∈ polySections (fun _ => 0) := by
  intro g B _
  rw [borelCharMat]
  simp

/-- A polynomial that is semi-invariant in the localization is a polynomial section. -/
theorem mem_polySections_of_algebraMap_mem_flagSemiInv {lam : Fin N → ℕ}
    {p : MvPolynomial (Fin N × Fin N) k}
    (hp : algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p
      ∈ flagSemiInv N k (fun i => (lam i : ℤ))) :
    p ∈ polySections lam := by
  intro g B hB
  have h := hp B hB
  rw [substRightAway_algebraMap, borelCharZ_natCast] at h
  have h2 : substRight B p = MvPolynomial.C (borelCharMat lam B) * p := by
    refine algebraMap_flagLoc_inj ?_
    rw [h, map_mul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)]
    simp only [MvPolynomial.algebraMap_eq]
  have h3 := congrArg (matEval g) h2
  rw [matEval_substRight, matEval_mul] at h3
  have hC : matEval g (MvPolynomial.C (borelCharMat lam B)) = borelCharMat lam B := by
    simp [matEval]
  rwa [hC] at h3

theorem algebraMap_detPow_ne_zero (M : ℕ) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) ((detPoly N k) ^ M) ≠ 0 := by
  intro h
  exact pow_ne_zero M detPoly_ne_zero (algebraMap_flagLoc_inj (by rw [h, map_zero]))

/-- **Clearing the denominator of a section regular on every cell.**  A power of the determinant
turns it into a polynomial section of the correspondingly shifted weight. -/
theorem exists_shifted_polySections {lam : Fin N → ℕ} {x : FlagLoc N k}
    (hsemi : x ∈ flagSemiInv N k (fun i => (lam i : ℤ)))
    (hden : ∀ σ : Equiv.Perm (Fin N), x ∈ denomBounded N k {σ}) :
    ∃ (M : ℕ) (q : MvPolynomial (Fin N × Fin N) k), q ∈ polySections (fun i => lam i + M) ∧
      x * algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) ((detPoly N k) ^ M)
        = algebraMap _ _ q := by
  obtain ⟨M, q, hq⟩ :=
    exists_detPow_mem_denomIdeal (fun σ => exists_pow_mem_denomIdeal (hden σ))
  have hdetpoly' : (detPoly N k) ^ M ∈ polySections (fun _ : Fin N => M) := by
    have h := detPow_mem_polySections (N := N) (k := k) one_mem_polySections M
    rw [mul_one] at h
    simpa using h
  have hdet : algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) ((detPoly N k) ^ M)
      ∈ flagSemiInv N k (fun i => ((fun _ : Fin N => M) i : ℤ)) :=
    (algebraMap_mem_cellSections hdetpoly' ∅).1
  have hprod := mul_mem_flagSemiInv_natCast hsemi hdet
  rw [hq] at hprod
  exact ⟨M, q, mem_polySections_of_algebraMap_mem_flagSemiInv hprod, hq⟩

/-- **Everything regular on every Bruhat cell is a global polynomial section.** -/
theorem exists_polySections_eq_algebraMap [CharZero k] {lam : Fin N → ℕ} (hlam : Antitone lam)
    {x : FlagLoc N k} (hsemi : x ∈ flagSemiInv N k (fun i => (lam i : ℤ)))
    (hden : ∀ σ : Equiv.Perm (Fin N), x ∈ denomBounded N k {σ}) :
    ∃ p ∈ polySections (k := k) lam,
      x = algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) p := by
  obtain ⟨M, q, hqmem, hq⟩ := exists_shifted_polySections hsemi hden
  obtain ⟨Q, hQ, hQeq⟩ := exists_eq_detPow_mul hlam M hqmem
  refine ⟨Q, hQ, mul_right_cancel₀ (algebraMap_detPow_ne_zero M) ?_⟩
  rw [hq, hQeq, map_mul]
  ring

/-- **Vanishing for a non-dominant weight.**  Nothing nonzero is regular on every cell. -/
theorem eq_zero_of_not_antitone {lam : Fin N → ℕ} (hlam : ¬ Antitone lam) {x : FlagLoc N k}
    (hsemi : x ∈ flagSemiInv N k (fun i => (lam i : ℤ)))
    (hden : ∀ σ : Equiv.Perm (Fin N), x ∈ denomBounded N k {σ}) : x = 0 := by
  obtain ⟨M, q, hqmem, hq⟩ := exists_shifted_polySections hsemi hden
  have hnot : ¬ Antitone (fun i => lam i + M) := by
    intro h
    refine hlam fun i j hij => ?_
    have h2 : lam j + M ≤ lam i + M := h hij
    omega
  rw [polySections_eq_bot_of_not_antitone hnot, Submodule.mem_bot] at hqmem
  rw [hqmem, map_zero] at hq
  exact (mul_eq_zero.mp hq).resolve_right (algebraMap_detPow_ne_zero M)

/-- A `0`-cocycle takes the same value on all singletons. -/
theorem cocycle_singleton_eq_of_lt {lam : Fin N → ℤ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} (hω : ω ∈ flagCocycles N k lam 0)
    {u v : Equiv.Perm (Fin N)} (huv : u < v) : ω {u} = ω {v} := by
  classical
  have hne : u ≠ v := ne_of_lt huv
  have h0 : cechDModule k ω = 0 := LinearMap.mem_ker.mp hω.2
  have he1 : ({u, v} : Finset (Equiv.Perm (Fin N))).erase u = {v} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun hw => hw.2.resolve_left hw.1, fun hw => ⟨by rw [hw]; exact fun hc => hne hc.symm,
      Or.inr hw⟩⟩
  have he2 : ({u, v} : Finset (Equiv.Perm (Fin N))).erase v = {u} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun hw => hw.2.resolve_right hw.1, fun hw => ⟨by rw [hw]; exact hne, Or.inl hw⟩⟩
  have h := congrFun h0 {u, v}
  rw [cechDModule, Finset.sum_pair hne, he1, he2, cechSign_pair_left (k := k) huv,
    cechSign_pair_right (k := k) huv, one_smul, neg_smul, one_smul, Pi.zero_apply] at h
  exact (sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h)).symm

theorem cocycle_singleton_eq {lam : Fin N → ℤ}
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k} (hω : ω ∈ flagCocycles N k lam 0)
    (σ τ : Equiv.Perm (Fin N)) : ω {σ} = ω {τ} := by
  rcases lt_trichotomy σ τ with h | h | h
  · exact cocycle_singleton_eq_of_lt hω h
  · rw [h]
  · exact (cocycle_singleton_eq_of_lt hω h).symm

/-- **Every Čech `0`-cocycle of the Bruhat cover is a global polynomial section.** -/
theorem exists_globalCochain_eq [CharZero k] {lam : Fin N → ℕ} (hlam : Antitone lam)
    {ω : Finset (Equiv.Perm (Fin N)) → FlagLoc N k}
    (hω : ω ∈ flagCocycles N k (fun i => (lam i : ℤ)) 0) :
    ∃ p ∈ polySections (k := k) lam, ω = globalCochain (fun i => (lam i : ℤ)) p := by
  classical
  have hsemi : ω {(1 : Equiv.Perm (Fin N))} ∈ flagSemiInv N k (fun i => (lam i : ℤ)) :=
    (hω.1.mem _).1
  have hden : ∀ σ : Equiv.Perm (Fin N),
      ω {(1 : Equiv.Perm (Fin N))} ∈ denomBounded N k {σ} := by
    intro σ
    have h := (hω.1.mem {σ}).2
    rwa [cocycle_singleton_eq hω 1 σ]
  obtain ⟨p, hp, hx⟩ := exists_polySections_eq_algebraMap hlam hsemi hden
  refine ⟨p, hp, ?_⟩
  funext I
  by_cases hI : I.card = 1
  · obtain ⟨σ, rfl⟩ := Finset.card_eq_one.mp hI
    rw [globalCochain, if_pos hI, ← hx, cocycle_singleton_eq hω σ 1]
  · rw [globalCochain, if_neg hI, hω.1.card I (by simpa using hI)]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **Vanishing of `H⁰` for a non-dominant weight.**  No nonzero Čech `0`-cocycle exists. -/
theorem flagCocycles_zero_eq_bot_of_not_antitone {lam : Fin N → ℕ} (hlam : ¬ Antitone lam) :
    flagCocycles N k (fun i => (lam i : ℤ)) 0 = ⊥ := by
  classical
  refine (Submodule.eq_bot_iff _).mpr fun ω hω => ?_
  funext I
  show ω I = 0
  by_cases hI : I.card = 1
  · obtain ⟨σ, rfl⟩ := Finset.card_eq_one.mp hI
    refine eq_zero_of_not_antitone hlam (hω.1.mem _).1 fun τ => ?_
    have h := (hω.1.mem {τ}).2
    rwa [cocycle_singleton_eq hω σ τ]
  · exact hω.1.card I (by simpa using hI)

theorem flagCohomology_zero_subsingleton_of_not_antitone {lam : Fin N → ℕ}
    (hlam : ¬ Antitone lam) :
    Subsingleton (flagCohomology N k (fun i => (lam i : ℤ)) 0) := by
  haveI : Subsingleton ↥(flagCocycles N k (fun i => (lam i : ℤ)) 0) := by
    rw [flagCocycles_zero_eq_bot_of_not_antitone hlam]
    infer_instance
  infer_instance

theorem algebraMap_flagLoc_smul (c : k) (p : MvPolynomial (Fin N × Fin N) k) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (c • p)
      = c • algebraMap _ _ p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)]

/-- The Čech `0`-cochain attached to a global section, as a linear map. -/
noncomputable def globalCochainLin (lam : Fin N → ℤ) :
    MvPolynomial (Fin N × Fin N) k →ₗ[k] (Finset (Equiv.Perm (Fin N)) → FlagLoc N k) where
  toFun := globalCochain lam
  map_add' p q := by
    funext I
    by_cases hI : I.card = 1
    · simp only [globalCochain, if_pos hI, Pi.add_apply, map_add]
    · simp only [globalCochain, if_neg hI, Pi.add_apply, add_zero]
  map_smul' c p := by
    funext I
    by_cases hI : I.card = 1
    · simp only [globalCochain, if_pos hI, Pi.smul_apply, RingHom.id_apply,
        algebraMap_flagLoc_smul]
    · simp only [globalCochain, if_neg hI, Pi.smul_apply, RingHom.id_apply, smul_zero]

/-- The Borel–Weil module inside the Čech `0`-cocycles. -/
noncomputable def polySectionsToCocycles (lam : Fin N → ℕ) :
    polySections (k := k) lam →ₗ[k] flagCocycles N k (fun i => (lam i : ℤ)) 0 :=
  LinearMap.codRestrict _
    ((globalCochainLin (fun i => (lam i : ℤ))).comp (polySections lam).subtype)
    (fun p => globalCochain_mem_flagCocycles p.2)

/-- **Borel–Weil on the flag variety.**  For a dominant weight the zeroth Čech cohomology of `L_λ`
on `G/B` is the Borel–Weil module `H⁰(λ)`, the irreducible representation of highest weight `λ`. -/
noncomputable def polySectionsEquivH0 [CharZero k] {lam : Fin N → ℕ} (hlam : Antitone lam) :
    polySections (k := k) lam ≃ₗ[k] flagCohomology N k (fun i => (lam i : ℤ)) 0 :=
  (LinearEquiv.ofBijective (polySectionsToCocycles lam)
    ⟨fun p q h => Subtype.ext
      (globalCochain_injective (lam := fun i => (lam i : ℤ)) (congrArg Subtype.val h)),
      fun ω => by
        obtain ⟨p, hp, hpe⟩ := exists_globalCochain_eq hlam ω.2
        exact ⟨⟨p, hp⟩, Subtype.ext hpe.symm⟩⟩).trans
    (Submodule.quotEquivOfEqBot _ (flagCohomology_zero_eq (fun i => (lam i : ℤ)))).symm

/-- **The cohomological Borel–Weil dichotomy.**  `H⁰(G/B, L_λ)` is nonzero exactly for dominant
weights. -/
theorem flagCohomology_zero_nontrivial_iff [CharZero k] {lam : Fin N → ℕ} :
    Nontrivial (flagCohomology N k (fun i => (lam i : ℤ)) 0) ↔ Antitone lam := by
  constructor
  · intro h
    by_contra hcon
    haveI := flagCohomology_zero_subsingleton_of_not_antitone (k := k) hcon
    exact absurd (Subsingleton.elim (α := flagCohomology N k (fun i => (lam i : ℤ)) 0)) (by
      obtain ⟨a, b, hab⟩ := h
      intro hall
      exact hab (hall a b))
  · intro hlam
    haveI : Nontrivial (polySections (k := k) lam) :=
      Submodule.nontrivial_iff_ne_bot.mpr (polySections_ne_bot_iff_antitone.mpr hlam)
    exact (polySectionsEquivH0 hlam).symm.toEquiv.nontrivial

end GaloisForLFunctions.HTGeometry.BorelWeil
