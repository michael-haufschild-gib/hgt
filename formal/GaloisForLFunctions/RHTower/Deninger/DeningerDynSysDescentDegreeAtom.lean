import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittPerfectDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysOmegaAtomBridge

/-!
# The descent degree of a normalized irreducible is the degree of inseparability of its atoms

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`).

For a normalized irreducible `β` over the perfect closure `L = κ₀^perf` the descent degree — the
exponent `d` with `α = β ^ d` for the normalized irreducible `α` over `κ₀` below `β` — equals the
degree of inseparability of any atom of `β` over `κ₀`.  Indeed `β` is separable over the perfect
field `L`, so its atoms over the algebraic closure are distinct, while the atoms of `α` are those
same elements repeated `d` times, and each of them occurs with multiplicity `d_u`.

Distinct normalized irreducibles over `L` have disjoint atoms, because their reverses are monic
irreducible and a common root would force them to be the same minimal polynomial.
-/

namespace RHTower

open Polynomial

variable {F L E : Type*} [Field F] [Field L] [Field E]
variable [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
variable [IsPurelyInseparable F L] [IsAlgClosed E]

omit [IsAlgClosed E] in
/-- The atoms of a normalized irreducible over the perfect closure are distinct. -/
theorem deningerRootUnits_nodup_of_separable [PerfectField L] {β : Polynomial L}
    (_hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β)
    (hmap : (β.map (algebraMap L E)).coeff 0 = 1) :
    (deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hmap).Nodup := by
  have hβsep : β.Separable := PerfectField.separable_of_irreducible hβirr
  have hβsepE : (β.map (algebraMap L E)).Separable := hβsep.map
  refine Multiset.Nodup.of_map (fun r : Eˣ => (r : E)) ?_
  rw [deningerNormalizedPolynomialRootUnits_coe]
  refine Multiset.Nodup.map_on (fun a _ b _ hab => ?_) (nodup_roots hβsepE)
  exact inv_injective hab

/-- **Deninger, Proposition 1.3 (`t26n`).**  The descent degree of a normalized irreducible over
the perfect closure is the degree of inseparability of any of its atoms. -/
theorem deningerDescentDegree_eq_insepDegree [PerfectField L] [DecidableEq Eˣ] (q : ℕ)
    [ExpChar F q] {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β)
    (hmapβ : (β.map (algebraMap L E)).coeff 0 = 1) {u : Eˣ}
    (hu : u ∈ deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hmapβ) :
    deningerDescentDegree F β = deningerInsepDegree F E q (u : E) := by
  classical
  obtain ⟨α, hα0, hαirr, hpow⟩ :=
    deningerDescentDegree_spec (F := F) (L := L) (E := E) q hβ0 hβirr
  set d := deningerDescentDegree F β with hd
  have hmapα : (α.map (algebraMap F E)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hα0, map_one]
  have hmapE : α.map (algebraMap F E) = (β.map (algebraMap L E)) ^ d := by
    have h2 := congrArg (fun p : Polynomial L => p.map (algebraMap L E)) hpow
    simp only [Polynomial.map_pow] at h2
    rw [← h2, Polynomial.map_map, ← IsScalarTower.algebraMap_eq F L E]
  have hcongr := deningerRootUnits_congr (P := α.map (algebraMap F E))
    (Q := (β.map (algebraMap L E)) ^ d) hmapα (by rw [← hmapE]; exact hmapα) hmapE
  have hroot : deningerNormalizedPolynomialRootUnits (α.map (algebraMap F E)) hmapα
      = d • deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hmapβ := by
    rw [hcongr, deningerRootUnits_pow]
  have hcount1 :
      Multiset.count u (deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hmapβ)
        = 1 := by
    have hle := Multiset.nodup_iff_count_le_one.1
      (deningerRootUnits_nodup_of_separable (E := E) hβ0 hβirr hmapβ) u
    have hge := Multiset.count_pos.2 hu
    omega
  have humem : u ∈ deningerNormalizedPolynomialRootUnits (α.map (algebraMap F E)) hmapα := by
    rw [hroot]
    refine Multiset.count_pos.1 ?_
    rw [Multiset.count_nsmul, hcount1, mul_one]
    exact deningerDescentDegree_pos β
  have hcountα := deningerAtomCount_eq_insepDegree (F := F) (E := E) q hα0 hαirr hmapα humem
  rw [hroot, Multiset.count_nsmul, hcount1, mul_one] at hcountα
  exact hcountα

omit [IsAlgClosed E] in
/-- **Deninger, Proposition 1.3 (`t26n`).**  Distinct normalized irreducibles over `L` have
disjoint atoms. -/
theorem deningerRootUnits_disjoint_of_ne {β γ : Polynomial L}
    (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β) (hγ0 : γ.coeff 0 = 1) (hγirr : Irreducible γ)
    (hmapβ : (β.map (algebraMap L E)).coeff 0 = 1)
    (hmapγ : (γ.map (algebraMap L E)).coeff 0 = 1) {u : Eˣ}
    (huβ : u ∈ deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hmapβ)
    (huγ : u ∈ deningerNormalizedPolynomialRootUnits (γ.map (algebraMap L E)) hmapγ) :
    β = γ := by
  classical
  have hune : (u : E) ≠ 0 := u.ne_zero
  haveI : Invertible (u : E) := invertibleOfNonzero hune
  haveI : Invertible ((u : E)⁻¹) := invertibleOfNonzero (inv_ne_zero hune)
  have key : ∀ (δ : Polynomial L), δ.coeff 0 = 1 → Irreducible δ →
      ∀ (hmapδ : (δ.map (algebraMap L E)).coeff 0 = 1),
      u ∈ deningerNormalizedPolynomialRootUnits (δ.map (algebraMap L E)) hmapδ →
      δ.reverse = minpoly L (u : E) := by
    intro δ hδ0 hδirr hmapδ hu
    have hδne : δ.map (algebraMap L E) ≠ 0 := fun h => by
      rw [h, Polynomial.coeff_zero] at hmapδ; exact zero_ne_one hmapδ
    have hcount : Multiset.count u
        (deningerNormalizedPolynomialRootUnits (δ.map (algebraMap L E)) hmapδ)
        = (δ.map (algebraMap L E)).rootMultiplicity ((u : E)⁻¹) :=
      deningerRootUnits_count _ hmapδ u
    have hpos : 0 < (δ.map (algebraMap L E)).rootMultiplicity ((u : E)⁻¹) := by
      rw [← hcount]; exact Multiset.count_pos.2 hu
    have hroot : (δ.map (algebraMap L E)).IsRoot ((u : E)⁻¹) :=
      (Polynomial.rootMultiplicity_pos hδne).1 hpos
    have hevalrev : Polynomial.eval₂ (algebraMap L E) (u : E) δ.reverse = 0 := by
      have h1 : Polynomial.eval₂ (algebraMap L E) (u : E) δ.reverse
          = Polynomial.eval (u : E) (δ.map (algebraMap L E)).reverse := by
        rw [deningerReverse_map (algebraMap L E) (algebraMap L E).injective δ, Polynomial.eval_map]
      rw [h1]
      have h2 : Polynomial.eval₂ (RingHom.id E) (⅟((u : E)⁻¹)) (δ.map (algebraMap L E)).reverse = 0
          ↔ Polynomial.eval₂ (RingHom.id E) ((u : E)⁻¹) (δ.map (algebraMap L E)) = 0 :=
        Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id E) ((u : E)⁻¹) _
      have hinv : (⅟((u : E)⁻¹) : E) = (u : E) := by rw [invOf_eq_inv, inv_inv]
      rw [hinv] at h2
      have h3 : Polynomial.eval₂ (RingHom.id E) ((u : E)⁻¹) (δ.map (algebraMap L E)) = 0 := by
        simpa [Polynomial.eval₂_eq_eval_map] using hroot
      simpa [Polynomial.eval₂_eq_eval_map] using h2.2 h3
    refine minpoly.eq_of_irreducible_of_monic
      (deningerIrreducible_reverse (by rw [hδ0]; exact one_ne_zero) hδirr) ?_
      (deningerReverse_monic hδ0)
    rw [Polynomial.aeval_def]
    exact hevalrev
  have hβm := key β hβ0 hβirr hmapβ huβ
  have hγm := key γ hγ0 hγirr hmapγ huγ
  have hrev : β.reverse = γ.reverse := by rw [hβm, hγm]
  have hβ0' : β.coeff 0 ≠ 0 := by rw [hβ0]; exact one_ne_zero
  have hγ0' : γ.coeff 0 ≠ 0 := by rw [hγ0]; exact one_ne_zero
  have := congrArg Polynomial.reverse hrev
  rwa [deningerReverse_reverse hβ0', deningerReverse_reverse hγ0'] at this

end RHTower
