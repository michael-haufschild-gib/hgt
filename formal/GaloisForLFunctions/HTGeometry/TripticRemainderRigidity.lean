import GaloisForLFunctions.HTGeometry.MeromorphicLaurentLeading
import GaloisForLFunctions.HTGeometry.TripticEntireRigidity

/-!
# The pole-free remainder

Subtracting the atoms from a source of vanishing orbital divisor leaves a function with no principal
part anywhere.  Such a function has nonnegative order at every point, so its canonical normal form
is entire.  The class relations survive only off the poles that were removed — a countable set — but
the complement of a countable set in `ℂ` is dense, so the relations extend to the whole plane by
continuity, and the entire rigidity theorem applies.

* `differentiable_toMeromorphicNFOn_of_no_principal_part` — no principal part makes the normal form
  entire;
* `const_of_entire_of_class_off_countable` — the class relations need only hold off a countable set.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- **A meromorphic function with no principal part has an entire normal form.** -/
theorem differentiable_toMeromorphicNFOn_of_no_principal_part {G : ℂ → ℂ}
    (hG : MeromorphicOn G Set.univ)
    (hpp : ∀ (w : ℂ) (ℓ : ℤ), ℓ < 0 → laurentCoeff G w ℓ = 0) :
    Differentiable ℂ (toMeromorphicNFOn G Set.univ) := by
  intro z
  have hord : 0 ≤ meromorphicOrderAt G z :=
    meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero (hG z (Set.mem_univ z))
      (fun ℓ hℓ => hpp z ℓ hℓ)
  have hNF : MeromorphicNFOn (toMeromorphicNFOn G Set.univ) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  have hord' : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn G Set.univ) z := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hG (Set.mem_univ z)]
    exact hord
  exact ((hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hord').differentiableAt

/-- Two continuous functions agreeing off a countable set agree everywhere. -/
theorem eq_of_eqOn_compl_countable {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {S : Set ℂ} (hS : S.Countable) (h : ∀ z ∉ S, f z = g z) : ∀ z, f z = g z := by
  have hdense : Dense (Sᶜ : Set ℂ) := hS.dense_compl ℂ
  have heq : Set.EqOn f g (Sᶜ : Set ℂ) := fun z hz => h z hz
  exact fun z => congrFun (hf.ext_on hdense hg heq) z

/-- **Pole-free rigidity off a countable set.**  An entire function that is `1`-periodic and has
constant mixed second difference outside a countable set is constant, and that constant is `0`. -/
theorem const_of_entire_of_class_off_countable {H : ℂ → ℂ} {τ σ C : ℂ}
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hH : Differentiable ℂ H) {S : Set ℂ} (hS : S.Countable)
    (hper : ∀ z ∉ S, H (z + 1) = H z)
    (hmix : ∀ z ∉ S, H (z + τ + σ) - H (z + τ) - (H (z + σ) - H z) = C) :
    (∀ x y, H x = H y) ∧ C = 0 := by
  have hcont : Continuous H := hH.continuous
  have hper' : Function.Periodic H 1 := by
    intro z
    exact eq_of_eqOn_compl_countable (f := fun w => H (w + 1)) (g := H)
      (hcont.comp (continuous_id.add continuous_const)) hcont hS hper z
  have hmix' : ∀ z, H (z + τ + σ) - H (z + τ) - (H (z + σ) - H z) = C := by
    have hL : Continuous fun z : ℂ => H (z + τ + σ) - H (z + τ) - (H (z + σ) - H z) := by
      fun_prop
    exact eq_of_eqOn_compl_countable hL continuous_const hS hmix
  exact const_of_entire_of_periodic_of_mixed_const hindepτ hindepσ hH hper' hmix'

end

end GaloisForLFunctions.HTGeometry
