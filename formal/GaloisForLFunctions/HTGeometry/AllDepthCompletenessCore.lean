import GaloisForLFunctions.HTGeometry.AllDepthAtomClass
import GaloisForLFunctions.HTGeometry.AllDepthSignatureDescent
import GaloisForLFunctions.HTGeometry.TripticOrderBound

/-!
# The bottom charge of an all-depth source is a finite lattice divisor

Three facts prepare the all-depth descent.  The bottom charge is invariant along the whole lattice
`ℤ + ℤ τ k`, not merely along its two generators; its orders are bounded, because there are finitely
many pole classes and the order is a class function; and the surviving directions are free modulo
that lattice, because `1` and the parameters are integrally independent.

* `laurentCoeff_lineLattice_of_periods`;
* **`exists_order_bound_of_lineLattice_invariant`**;
* `lineLattice_free_single`, `lineLattice_free_pair`.
-/

open Filter Set Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

/-! ## Invariance along the whole lattice -/

theorem laurentCoeff_lineLattice_of_periods {V : ℂ → ℂ} {σ : ℂ} {ℓ : ℤ}
    (h1 : ∀ z : ℂ, laurentCoeff V (z + 1) ℓ = laurentCoeff V z ℓ)
    (hσ : ∀ z : ℂ, laurentCoeff V (z + σ) ℓ = laurentCoeff V z ℓ)
    (z : ℂ) {g : ℂ} (hg : g ∈ lineLattice σ) :
    laurentCoeff V (z + g) ℓ = laurentCoeff V z ℓ := by
  obtain ⟨a, b, rfl⟩ := hg
  have hA := laurentCoeff_add_zsmul_of_period h1 z a
  have hB := laurentCoeff_add_zsmul_of_period hσ (z + (a : ℂ) * 1) b
  rw [show z + ((a : ℂ) + (b : ℂ) * σ) = (z + (a : ℂ) * 1) + (b : ℂ) * σ from by ring, hB, hA]

/-! ## The orders are bounded -/

set_option maxHeartbeats 800000 in
/-- **A lattice-invariant germ with finitely many pole classes has bounded pole order.** -/
theorem exists_order_bound_of_lineLattice_invariant {V : ℂ → ℂ} {σ : ℂ}
    (hV : MeromorphicOn V (Set.univ : Set ℂ))
    (hlat : ∀ ℓ : ℤ, ℓ < 0 → ∀ z g : ℂ, g ∈ lineLattice σ →
      laurentCoeff V (z + g) ℓ = laurentCoeff V z ℓ)
    {P : Finset ℂ} (hP : ∀ z : ℂ, meromorphicOrderAt V z < 0 → ∃ q ∈ P, sameLine σ q z) :
    ∃ N : ℕ, ∀ ℓ : ℤ, ℓ < -(N : ℤ) → ∀ p : ℂ, laurentCoeff V p ℓ = 0 := by
  classical
  refine ⟨P.sup fun q => (meromorphicOrderAt V q).untop₀.natAbs, fun ℓ hℓ p => ?_⟩
  by_contra hne
  have hnn : (0 : ℤ) ≤ ((P.sup fun q => (meromorphicOrderAt V q).untop₀.natAbs : ℕ) : ℤ) :=
    Int.natCast_nonneg _
  have hℓneg : ℓ < 0 := by omega
  have hpole : meromorphicOrderAt V p < 0 :=
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hV p (Set.mem_univ p)) hℓneg hne
  obtain ⟨q, hq, hqp⟩ := hP p hpole
  have hcoeff : ∀ ℓ' : ℤ, ℓ' < 0 → laurentCoeff V p ℓ' = laurentCoeff V q ℓ' := by
    intro ℓ' hℓ'
    have hstep := hlat ℓ' hℓ' q (p - q) hqp
    rw [show q + (p - q) = p from by ring] at hstep
    exact hstep
  have horder : meromorphicOrderAt V p = meromorphicOrderAt V q :=
    meromorphicOrderAt_eq_of_laurentCoeff_eq (hV p (Set.mem_univ p)) (hV q (Set.mem_univ q))
      hcoeff hpole
  have hqneg : meromorphicOrderAt V q < 0 := horder ▸ hpole
  have hqne : meromorphicOrderAt V q ≠ ⊤ := by
    intro htop
    rw [htop] at hqneg
    exact absurd hqneg (by simp)
  obtain ⟨nn, hnnq⟩ := WithTop.ne_top_iff_exists.mp hqne
  have hnneg : nn < 0 := by
    rw [← hnnq] at hqneg
    exact_mod_cast hqneg
  have hle : meromorphicOrderAt V p ≤ (ℓ : WithTop ℤ) :=
    meromorphicOrderAt_le_of_laurentCoeff_ne_zero (hV p (Set.mem_univ p)) hne
  rw [horder, ← hnnq] at hle
  have hnl : nn ≤ ℓ := by exact_mod_cast hle
  have hsup : (meromorphicOrderAt V q).untop₀.natAbs
      ≤ P.sup fun r => (meromorphicOrderAt V r).untop₀.natAbs :=
    Finset.le_sup (f := fun r => (meromorphicOrderAt V r).untop₀.natAbs) hq
  rw [← hnnq] at hsup
  simp only [WithTop.untop₀_coe] at hsup
  have hcast : (nn.natAbs : ℤ)
      ≤ ((P.sup fun r => (meromorphicOrderAt V r).untop₀.natAbs : ℕ) : ℤ) := by
    exact_mod_cast hsup
  omega

/-! ## Freeness of the surviving directions -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **One surviving direction has infinite order modulo the distinguished lattice.** -/
theorem lineLattice_free_single (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ)
    {k i : ι} (hik : i ≠ k) (n : ℤ) (h : (n : ℂ) * τ i ∈ lineLattice (τ k)) : n = 0 := by
  classical
  obtain ⟨a, b, hab⟩ := h
  set c : ι → ℤ := fun l => (if l = i then n else 0) + (if l = k then -b else 0) with hc
  have hterm : ∀ l : ι, ((c l : ℤ) : ℂ) * τ l
      = (if l = i then (n : ℂ) * τ l else 0) + (if l = k then ((-b : ℤ) : ℂ) * τ l else 0) := by
    intro l
    simp only [hc]
    push_cast
    split_ifs <;> ring
  have hsum : ∑ l, ((c l : ℤ) : ℂ) * τ l = (n : ℂ) * τ i + ((-b : ℤ) : ℂ) * τ k := by
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun l => (n : ℂ) * τ l),
      Finset.sum_ite_eq' Finset.univ k (fun l => ((-b : ℤ) : ℂ) * τ l)]
    simp
  have hzero : (((-a : ℤ)) : ℂ) + ∑ l, ((c l : ℤ) : ℂ) * τ l = 0 := by
    rw [hsum]
    push_cast
    linear_combination hab
  obtain ⟨-, hcl⟩ := hQ (-a) c hzero
  have hci := hcl i
  simp only [hc, if_pos, if_neg hik, add_zero] at hci
  omega

/-- **Two distinct surviving directions are free modulo the distinguished lattice.** -/
theorem lineLattice_free_pair (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ)
    {k i j : ι} (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j) (n m : ℤ)
    (h : (n : ℂ) * τ i + (m : ℂ) * τ j ∈ lineLattice (τ k)) : n = 0 ∧ m = 0 := by
  classical
  obtain ⟨a, b, hab⟩ := h
  set c : ι → ℤ := fun l =>
    (if l = i then n else 0) + (if l = j then m else 0) + (if l = k then -b else 0) with hc
  have hterm : ∀ l : ι, ((c l : ℤ) : ℂ) * τ l
      = (if l = i then (n : ℂ) * τ l else 0) + (if l = j then (m : ℂ) * τ l else 0)
        + (if l = k then ((-b : ℤ) : ℂ) * τ l else 0) := by
    intro l
    simp only [hc]
    push_cast
    split_ifs <;> ring
  have hsum : ∑ l, ((c l : ℤ) : ℂ) * τ l
      = (n : ℂ) * τ i + (m : ℂ) * τ j + ((-b : ℤ) : ℂ) * τ k := by
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun l => (n : ℂ) * τ l),
      Finset.sum_ite_eq' Finset.univ j (fun l => (m : ℂ) * τ l),
      Finset.sum_ite_eq' Finset.univ k (fun l => ((-b : ℤ) : ℂ) * τ l)]
    simp
  have hzero : (((-a : ℤ)) : ℂ) + ∑ l, ((c l : ℤ) : ℂ) * τ l = 0 := by
    rw [hsum]
    push_cast
    linear_combination hab
  obtain ⟨-, hcl⟩ := hQ (-a) c hzero
  have hci := hcl i
  have hcj := hcl j
  simp only [hc, if_pos, if_neg hik, if_neg hij, if_neg hjk, if_neg (Ne.symm hij),
    add_zero, zero_add] at hci hcj
  omega

/-- **The distinguished direction has infinite order modulo a surviving pair.** -/
theorem tripticPeriodGroup_free (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ)
    {k i j : ι} (hik : i ≠ k) (hjk : j ≠ k) (n : ℤ)
    (h : n • τ k ∈ tripticPeriodGroup (τ j) (τ i)) : n = 0 := by
  classical
  obtain ⟨a, q, r, hqr⟩ := h
  set c : ι → ℤ := fun l =>
    (if l = i then -r else 0) + (if l = j then -q else 0) + (if l = k then n else 0) with hc
  have hterm : ∀ l : ι, ((c l : ℤ) : ℂ) * τ l
      = (if l = i then ((-r : ℤ) : ℂ) * τ l else 0)
        + (if l = j then ((-q : ℤ) : ℂ) * τ l else 0)
        + (if l = k then (n : ℂ) * τ l else 0) := by
    intro l
    simp only [hc]
    push_cast
    split_ifs <;> ring
  have hsum : ∑ l, ((c l : ℤ) : ℂ) * τ l
      = ((-r : ℤ) : ℂ) * τ i + ((-q : ℤ) : ℂ) * τ j + (n : ℂ) * τ k := by
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun l => ((-r : ℤ) : ℂ) * τ l),
      Finset.sum_ite_eq' Finset.univ j (fun l => ((-q : ℤ) : ℂ) * τ l),
      Finset.sum_ite_eq' Finset.univ k (fun l => (n : ℂ) * τ l)]
    simp
  have hzero : (((-a : ℤ)) : ℂ) + ∑ l, ((c l : ℤ) : ℂ) * τ l = 0 := by
    rw [hsum]
    have hsm : n • τ k = (n : ℂ) * τ k := by
      rw [zsmul_eq_mul]
    rw [hsm] at hqr
    push_cast
    linear_combination hqr
  obtain ⟨-, hcl⟩ := hQ (-a) c hzero
  have hck := hcl k
  simp only [hc, if_pos, if_neg (Ne.symm hik), if_neg (Ne.symm hjk), zero_add] at hck
  omega

end

end GaloisForLFunctions
