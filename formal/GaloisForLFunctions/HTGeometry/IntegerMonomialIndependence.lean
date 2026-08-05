import GaloisForLFunctions.HTGeometry.IntegerGradedIndependence

/-!
# Monomials in jets of integer rate

A jet may vanish at a sampled point instead of blowing up.  With integer rates the monomial order is
the same linear form as before, `Σ eₖ dₖ`, only now the `dₖ` may be negative and the sum may be
negative — a monomial that vanishes rather than blows up.

The box is decided exactly as in the non-negative case: by injectivity of the order form on the
exponent family.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The order of a jet monomial when the jets have integer rates. -/
def integerBlowUpOrder {n : ℕ} (d : Fin n → ℤ) (e : Fin n →₀ ℕ) : ℤ :=
  e.sum fun k x => (x : ℤ) * d k

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (t : ℂ) (ht : t ≠ 0) (f : ι → ℤ) :
    ∏ k ∈ s, t ^ (f k) = t ^ (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← zpow_add₀ ht]

theorem prod_mul_zpow_eq_prod_mul_zpow_order {n : ℕ} (d : Fin n → ℤ) (e : Fin n →₀ ℕ)
    (G : Fin n → ℂ) {t : ℂ} (ht : t ≠ 0) :
    ∏ k ∈ e.support, (G k * t ^ (d k)) ^ (e k)
      = (∏ k ∈ e.support, (G k) ^ (e k)) * t ^ (integerBlowUpOrder d e) := by
  rw [Finset.prod_congr rfl fun k _ => mul_pow (G k) (t ^ d k) (e k), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_congr rfl fun k _ => (zpow_natCast (t ^ d k) (e k)).symm]
  rw [Finset.prod_congr rfl fun k _ => (zpow_mul t (d k) ((e k : ℤ))).symm]
  rw [prod_zpow_eq_zpow_sum _ t ht, integerBlowUpOrder, Finsupp.sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Blow-up data with integer rates: a jet may vanish at the sampled points. -/
def IntegerMultiBlowUpData {n : ℕ} (S : Set ℂ) (F : Fin n → ℂ → ℂ) (Z : Set ℂ)
    (d : Fin n → ℤ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ (u : ℕ → ℂ) (t : ℕ → ℂ) (c : Fin n → ℂ),
    (∀ j, u j ∈ S) ∧ (∀ j, t j ≠ 0) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ k, c k ≠ 0) ∧
      ∀ k, Tendsto (fun j => F k (u j) * t j ^ (d k)) atTop (𝓝 (c k))

/-- Jet monomials of integer rate form an integer-graded family. -/
theorem integerGradedFamily_of_integerMultiBlowUp {κ : Type*} {n : ℕ} {S : Set ℂ}
    {F : Fin n → ℂ → ℂ} {Z : Set ℂ} {d : Fin n → ℤ}
    (hdata : IntegerMultiBlowUpData S F Z d) (exponent : κ → (Fin n →₀ ℕ)) :
    IntegerGradedFamily S (fun a w => ∏ k ∈ (exponent a).support, (F k w) ^ (exponent a k)) Z
      (fun a => integerBlowUpOrder d (exponent a)) := by
  obtain ⟨hZ, hblow⟩ := hdata
  refine ⟨hZ, ?_⟩
  intro ζ hζ
  obtain ⟨u, t, c, humem, htne, hu, ht, hcne, hlim⟩ := hblow ζ hζ
  refine ⟨u, t, fun a => ∏ k ∈ (exponent a).support, (c k) ^ (exponent a k),
    humem, htne, hu, ht, ?_, ?_⟩
  · intro a
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hcne k)
  · intro a
    have hprod := tendsto_finsetProd (M := ℂ) (exponent a).support
      (f := fun k j => (F k (u j) * t j ^ (d k)) ^ (exponent a k))
      (a := fun k => (c k) ^ (exponent a k)) (fun k _ => (hlim k).pow _)
    refine hprod.congr fun j => ?_
    exact prod_mul_zpow_eq_prod_mul_zpow_order d (exponent a) (fun k => F k (u j)) (htne j)

/-- **The expanded monomial box, with integer jet rates.**  Jets that vanish at the sampled points
are admitted; only injectivity of the order form is required. -/
theorem linearIndependent_restrict_expandedMonomialFamily_of_integerMultiBlowUp
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n q : ℕ} {S : Set ℂ} {F : Fin n → ℂ → ℂ}
    {Z : Set ℂ} {d : Fin n → ℤ} (hdata : IntegerMultiBlowUpData S F Z d)
    {exponent : κ → (Fin n →₀ ℕ)}
    (hord : Function.Injective fun a => integerBlowUpOrder d (exponent a)) :
    LinearIndependent ℂ
      (fun c : κ × Fin (q + 1) => Set.restrict S (expandedMonomialFamily F exponent q c)) := by
  have hgen := linearIndependent_restrict_degreeBox_of_integerGraded (q := q)
    (integerGradedFamily_of_integerMultiBlowUp hdata exponent) hord
  have hfam : (fun c : κ × Fin (q + 1) => Set.restrict S (expandedMonomialFamily F exponent q c))
      = (fun p : κ × Fin (q + 1) => Set.restrict S
          (fun w => w ^ (p.2 : ℕ) * ∏ k ∈ (exponent p.1).support, (F k w) ^ (exponent p.1 k))) := by
    funext p x
    exact expandedMonomialFamily_apply F exponent p (x : ℂ)
  rw [hfam]
  exact hgen


/-! ## Analytic order supplies the negative rate -/

/-- **A zero of order `V` is graded of order `−V`.**  The factorization of an analytic germ at a
zero of finite order turns the vanishing into a negative rate with a nonzero leading value — exactly
the datum an integer-graded family asks for. -/
theorem exists_tendsto_zpow_neg_of_analyticOrderAt {f : ℂ → ℂ} {ζ : ℂ} {V : ℕ}
    (hf : AnalyticAt ℂ f ζ) (hord : analyticOrderAt f ζ = (V : ℕ))
    {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝 ζ)) (hune : ∀ j, u j ≠ ζ) :
    ∃ C : ℂ, C ≠ 0 ∧
      Tendsto (fun j => f (u j) * (u j - ζ) ^ (-(V : ℤ))) atTop (𝓝 C) := by
  obtain ⟨g, hg, hg0, hev⟩ := (hf.analyticOrderAt_eq_natCast (n := V)).mp hord
  refine ⟨g ζ, hg0, ?_⟩
  have hcont : Tendsto (fun j => g (u j)) atTop (𝓝 (g ζ)) := hg.continuousAt.tendsto.comp hu
  refine Tendsto.congr' ?_ hcont
  filter_upwards [hu.eventually hev] with j hj
  have hne : u j - ζ ≠ 0 := sub_ne_zero.mpr (hune j)
  rw [hj, smul_eq_mul, mul_comm ((u j - ζ) ^ V) (g (u j)), mul_assoc,
    ← zpow_natCast (u j - ζ) V, ← zpow_add₀ hne]
  simp

end GaloisForLFunctions.HTGeometry
