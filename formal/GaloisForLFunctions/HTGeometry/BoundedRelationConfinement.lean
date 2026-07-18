import GaloisForLFunctions.HTGeometry.PrivatePrimeConfinement

/-!
# Bounded integer-relation confinement

This module packages the additive relation-lattice condition used by bounded-relation
hypertranscendence arguments.  It also proves the finite-atom uniqueness principle needed there:
a full-degree atom supported beyond a confinement threshold is the unique atom of degree at most
that bound with the same valuation.
-/

open Filter Finset

namespace GaloisForLFunctions

noncomputable section

/-- A sequence has bounded-relation confinement when every bounded-height finitely supported
integer relation is confined to a finite prefix. -/
def BoundedRelationConfinement {A : Type*} [AddCommGroup A] (b : ℕ → A) : Prop :=
  ∀ D : ℕ, ∃ M : ℕ, ∀ d : ℕ →₀ ℤ,
    (∀ n, |d n| ≤ (D : ℤ)) →
    d.sum (fun n z => z • b n) = 0 →
    ∀ n ∈ d.support, n < M

/-- The additive valuation of a finite multiplicity vector. -/
def atomValuation {A : Type*} [AddCommMonoid A] (b : ℕ → A) (ν : ℕ →₀ ℕ) : A :=
  ν.sum (fun n k => k • b n)

private def atomRelation (μ ν : ℕ →₀ ℕ) : ℕ →₀ ℤ :=
  Finsupp.mapRange (fun k : ℕ => (k : ℤ)) (by simp) μ -
    Finsupp.mapRange (fun k : ℕ => (k : ℤ)) (by simp) ν

@[simp]
private theorem atomRelation_apply (μ ν : ℕ →₀ ℕ) (i : ℕ) :
    atomRelation μ ν i = (μ i : ℤ) - (ν i : ℤ) := by
  rfl

private theorem finsupp_apply_le_total (ν : ℕ →₀ ℕ) (i : ℕ) :
    ν i ≤ ν.sum (fun _ k => k) := by
  classical
  rw [Finsupp.sum]
  by_cases hi : i ∈ ν.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp [Finsupp.notMem_support_iff.mp hi]

private theorem atomRelation_bound {D : ℕ} {μ ν : ℕ →₀ ℕ}
    (hμ : μ.sum (fun _ k => k) ≤ D)
    (hν : ν.sum (fun _ k => k) ≤ D) :
    ∀ i, |atomRelation μ ν i| ≤ (D : ℤ) := by
  intro i
  have hμi : μ i ≤ D := (finsupp_apply_le_total μ i).trans hμ
  have hνi : ν i ≤ D := (finsupp_apply_le_total ν i).trans hν
  rw [atomRelation_apply, abs_le]
  constructor <;> omega

private theorem atomRelation_sum {A : Type*} [AddCommGroup A]
    (b : ℕ → A) (μ ν : ℕ →₀ ℕ) :
    (atomRelation μ ν).sum (fun n z => z • b n) =
      atomValuation b μ - atomValuation b ν := by
  classical
  have hcast : Function.Injective (fun k : ℕ => (k : ℤ)) := by
    exact_mod_cast Nat.cast_injective
  have hmap : ∀ κ : ℕ →₀ ℕ,
      (Finsupp.mapRange (fun k : ℕ => (k : ℤ)) (by simp) κ).sum
          (fun n z => z • b n) = atomValuation b κ := by
    intro κ
    rw [Finsupp.sum,
      Finsupp.support_mapRange_of_injective (by simp) κ hcast,
      atomValuation, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [atomRelation, Finsupp.sum_sub_index, hmap, hmap]
  intro i z₁ z₂
  exact sub_smul z₁ z₂ (b i)

/-- A full-degree atom supported beyond a bounded-relation threshold is the unique atom of degree
at most that bound with the same additive valuation. -/
theorem atom_eq_of_valuation_eq_of_full_tail
    {A : Type*} [AddCommGroup A] {b : ℕ → A} {D M : ℕ} {ν μ : ℕ →₀ ℕ}
    (hconf : ∀ d : ℕ →₀ ℤ,
      (∀ n, |d n| ≤ (D : ℤ)) →
      d.sum (fun n z => z • b n) = 0 →
      ∀ n ∈ d.support, n < M)
    (hνcount : ν.sum (fun _ k => k) = D)
    (hμcount : μ.sum (fun _ k => k) ≤ D)
    (hνtail : ∀ i, ν i ≠ 0 → M ≤ i)
    (hval : atomValuation b μ = atomValuation b ν) :
    μ = ν := by
  have hνcount_le : ν.sum (fun _ k => k) ≤ D := hνcount.le
  have hrel : (atomRelation μ ν).sum (fun n z => z • b n) = 0 := by
    rw [atomRelation_sum, hval, sub_self]
  have htailEq : ∀ i, M ≤ i → μ i = ν i := by
    intro i hi
    by_contra hne
    have hmem : i ∈ (atomRelation μ ν).support := by
      rw [Finsupp.mem_support_iff, atomRelation_apply]
      exact sub_ne_zero.mpr (by exact_mod_cast hne)
    have := hconf (atomRelation μ ν)
      (atomRelation_bound hμcount hνcount_le) hrel i hmem
    omega
  have hνμ : ν ≤ μ := by
    intro i
    by_cases hi : ν i = 0
    · simp [hi]
    · exact (htailEq i (hνtail i hi)).ge
  let total : (ℕ →₀ ℕ) →+ ℕ :=
    Finsupp.liftAddHom (fun _ : ℕ => AddMonoidHom.id ℕ)
  have hdecomp : μ - ν + ν = μ := tsub_add_cancel_of_le hνμ
  have htotal : total (μ - ν) + total ν = total μ := by
    rw [← map_add, hdecomp]
  have htotalSub : total (μ - ν) = 0 := by
    change total (μ - ν) + ν.sum (fun _ k => k) =
      μ.sum (fun _ k => k) at htotal
    omega
  have hsub : μ - ν = 0 := by
    apply Finsupp.ext
    intro i
    have hi := finsupp_apply_le_total (μ - ν) i
    change (μ - ν) i ≤ total (μ - ν) at hi
    rw [htotalSub] at hi
    exact Nat.eq_zero_of_le_zero hi
  have hμν : μ ≤ ν := by
    intro i
    have hi := Finsupp.ext_iff.mp hsub i
    simpa using (Nat.sub_eq_zero_iff_le.mp hi)
  exact le_antisymm hμν hνμ

/-- Private-prime exposure of a rational sequence gives bounded-relation confinement after the
canonical embedding into the reals. -/
theorem boundedRelationConfinement_of_privatePrime {b : ℕ → ℚ} {p : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime)
    (hpinf : Tendsto p atTop atTop)
    (hbn : ∀ n, 1 < padicNorm (p n) (b n))
    (hbm : ∀ n m, m ≠ n → padicNorm (p n) (b m) ≤ 1) :
    BoundedRelationConfinement (fun n => (b n : ℝ)) := by
  intro D
  obtain ⟨M, hM⟩ := private_prime_bounded_relation_confinement hp hpinf hbn hbm D
  refine ⟨M, fun d hd hrel => hM d hd ?_⟩
  have hcast : ((∑ m ∈ d.support, (d m : ℚ) * b m : ℚ) : ℝ) = 0 := by
    push_cast
    simpa [Finsupp.sum, smul_eq_mul] using hrel
  exact_mod_cast hcast

end

end GaloisForLFunctions
