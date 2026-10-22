import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysDescentDegreeAtom

/-!
# The atom criterion for descent

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the lower row.

A normalized polynomial over the perfect closure `L` descends to `κ₀` exactly when the multiplicity
of every atom of its image over the algebraic closure is divisible by the degree of inseparability
of that atom.  The translation between the two formulations is that the atoms of a normalized
irreducible `β` over `L` are distinct, occur in no other normalized irreducible, and the descent
degree of `β` is the degree of inseparability of its atoms.
-/

namespace RHTower

open Polynomial

variable {F L E : Type*} [Field F] [Field L] [Field E]
variable [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
variable [IsPurelyInseparable F L] [IsAlgClosed E] [PerfectField L]

omit [IsAlgClosed E] in
/-- The multiplicity of an atom of `β` in the atoms of a product of normalized irreducibles is the
multiplicity of `β` in the product. -/
theorem deningerRootUnits_prod_count [DecidableEq Eˣ] [DecidableEq (Polynomial L)]
    {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β)
    (hmapβ : (β.map (algebraMap L E)).coeff 0 = 1) {u : Eˣ}
    (hu : u ∈ deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hmapβ) :
    ∀ (S : Multiset (Polynomial L)), (∀ γ ∈ S, γ.coeff 0 = 1 ∧ Irreducible γ) →
      ∀ (hmap : ((S.prod).map (algebraMap L E)).coeff 0 = 1),
        Multiset.count u
            (deningerNormalizedPolynomialRootUnits ((S.prod).map (algebraMap L E)) hmap)
          = Multiset.count β S := by
  classical
  intro S
  induction S using Multiset.induction_on with
  | empty =>
      intro _ hmap
      have h1 : ((0 : Multiset (Polynomial L)).prod).map (algebraMap L E) = 1 := by simp
      have hc := deningerRootUnits_congr
        (P := ((0 : Multiset (Polynomial L)).prod).map (algebraMap L E))
        (Q := (1 : Polynomial E)) hmap (by simp) h1
      rw [hc, deningerRootUnits_one]
      simp
  | cons γ S ih =>
      intro hS hmap
      have hγ := hS γ (Multiset.mem_cons_self γ S)
      have hSmem : ∀ δ ∈ S, δ.coeff 0 = 1 ∧ Irreducible δ :=
        fun δ hδ => hS δ (Multiset.mem_cons_of_mem hδ)
      have hγM : (γ.map (algebraMap L E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, hγ.1, map_one]
      have hSM : ((S.prod).map (algebraMap L E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, deningerProdCoeffZero S (fun δ hδ => (hSmem δ hδ).1), map_one]
      have hsplit : ((γ ::ₘ S).prod).map (algebraMap L E)
          = γ.map (algebraMap L E) * (S.prod).map (algebraMap L E) := by
        rw [Multiset.prod_cons, Polynomial.map_mul]
      have hc := deningerRootUnits_congr (P := ((γ ::ₘ S).prod).map (algebraMap L E))
        (Q := γ.map (algebraMap L E) * (S.prod).map (algebraMap L E)) hmap
        (by rw [← hsplit]; exact hmap) hsplit
      rw [hc, deningerRootUnits_mul _ _ hγM hSM, Multiset.count_add, ih hSmem hSM,
        Multiset.count_cons]
      have hfirst : Multiset.count u
          (deningerNormalizedPolynomialRootUnits (γ.map (algebraMap L E)) hγM)
          = if β = γ then 1 else 0 := by
        by_cases huγ : u ∈ deningerNormalizedPolynomialRootUnits (γ.map (algebraMap L E)) hγM
        · have heq : β = γ :=
            deningerRootUnits_disjoint_of_ne (E := E) hβ0 hβirr hγ.1 hγ.2 hmapβ hγM hu huγ
          rw [if_pos heq]
          have hle := Multiset.nodup_iff_count_le_one.1
            (deningerRootUnits_nodup_of_separable (E := E) hγ.1 hγ.2 hγM) u
          have hge := Multiset.count_pos.2 huγ
          omega
        · have hne : β ≠ γ := by
            intro h
            subst h
            exact huγ (by
              have := deningerRootUnits_congr (P := β.map (algebraMap L E))
                (Q := β.map (algebraMap L E)) hmapβ hγM rfl
              rwa [← this])
          rw [if_neg hne, Multiset.count_eq_zero_of_notMem huγ]
      rw [hfirst]
      exact Nat.add_comm _ _

/-- **Deninger, Proposition 1.3 (`t26n`), the atom criterion.**  A normalized polynomial over the
perfect closure descends to `κ₀` as soon as every atom multiplicity of its image over the algebraic
closure is divisible by the degree of inseparability of that atom. -/
theorem deningerNormalized_descends_of_atom_dvd (q : ℕ) [ExpChar F q] [DecidableEq Eˣ]
    [DecidableEq (Polynomial L)] (P : Polynomial L) (hP : P.coeff 0 = 1)
    (hmap : (P.map (algebraMap L E)).coeff 0 = 1)
    (h : ∀ u : Eˣ, u ∈ deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmap →
      deningerInsepDegree F E q (u : E) ∣ Multiset.count u
        (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmap)) :
    ∃ P₀ : Polynomial F, P₀.coeff 0 = 1 ∧ P₀.map (algebraMap F L) = P := by
  classical
  refine deningerNormalized_descends_of_dvd (E := E) q P hP ?_
  intro β hβ
  obtain ⟨hβ0, hβirr⟩ := deningerNormalizedFactors_mem hP hβ
  have hmapβ : (β.map (algebraMap L E)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hβ0, map_one]
  -- pick an atom of `β`
  have hβne : β.map (algebraMap L E) ≠ 0 := fun hz => by
    rw [hz, Polynomial.coeff_zero] at hmapβ; exact zero_ne_one hmapβ
  have hdeg : 0 < (β.map (algebraMap L E)).natDegree := by
    have := deningerNatDegree_pos_of_normalized hβ0 hβirr
    rwa [Polynomial.natDegree_map_eq_of_injective (algebraMap L E).injective]
  have hcard : (deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hmapβ) ≠ 0 := by
    intro hzero
    have hcoe := congrArg (Multiset.map fun r : Eˣ => (r : E)) hzero
    rw [deningerNormalizedPolynomialRootUnits_coe] at hcoe
    have hroots : (β.map (algebraMap L E)).roots = 0 := by
      have hcard0 := congrArg Multiset.card hcoe
      simp only [Multiset.card_map, Multiset.card_zero] at hcard0
      exact Multiset.card_eq_zero.1 hcard0
    have hsplits : (β.map (algebraMap L E)).roots.card = (β.map (algebraMap L E)).natDegree :=
      Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
    rw [hroots, Multiset.card_zero] at hsplits
    omega
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero hcard
  have hdd : deningerDescentDegree F β = deningerInsepDegree F E q (u : E) :=
    deningerDescentDegree_eq_insepDegree (E := E) q hβ0 hβirr hmapβ hu
  have hcount : Multiset.count u
      (deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmap)
      = Multiset.count β (deningerNormalizedFactors P) := by
    have hspec := deningerNormalizedFactors_spec hP
    have hmap' : (((deningerNormalizedFactors P).prod).map (algebraMap L E)).coeff 0 = 1 := by
      rw [hspec.2]; exact hmap
    have := deningerRootUnits_prod_count (E := E) hβ0 hβirr hmapβ hu
      (deningerNormalizedFactors P) hspec.1 hmap'
    have hc := deningerRootUnits_congr
      (P := ((deningerNormalizedFactors P).prod).map (algebraMap L E))
      (Q := P.map (algebraMap L E)) hmap' hmap (by rw [hspec.2])
    rwa [hc] at this
  have hdvd := h u (by
    have hmem : u ∈ deningerNormalizedPolynomialRootUnits (P.map (algebraMap L E)) hmap := by
      refine Multiset.count_pos.1 ?_
      rw [hcount]
      exact Multiset.count_pos.2 hβ
    exact hmem)
  rw [hdd, ← hcount]
  exact hdvd

end RHTower
