import GaloisForLFunctions.HTGeometry.AlgebraicMonicScaling
import GaloisForLFunctions.HTGeometry.AlgebraicReciprocalParameter

/-!
# An actual meromorphic chart at infinity for a non-coordinate plane curve

Every irreducible bivariate complex polynomial with positive degree in both
coordinates has a meromorphic branch `(s^(-N), f(s))` at infinity. The second
coordinate is not locally constant; the first eventually avoids every finite
set. Reciprocal parameter, monic scaling, formal Newton–Puiseux and exact
finite-jet division construct the branch without assuming convergence.

This closes the classical analytic normalization input used in the
reflected-cosine component argument. It is not the component theorem or an
RH result, and no new scientific knowledge is claimed for normalization.
-/

namespace GaloisForLFunctions.HTGeometry.AlgebraicInfinityBranch

open Polynomial AlgebraicFiniteJetBranch AlgebraicMonicScaling AlgebraicReciprocalParameter
open scoped Topology

noncomputable section


/-- An irreducible curve involving the parameter cannot have a constant dependent branch. -/
theorem eval_C_ne_zero_of_parameterDegree_pos (P : BiPoly) (hirr : Irreducible P)
    (hx : 0 < parameterDegree P) (c : ℂ) : P.eval (C c) ≠ 0 := by
  intro hc
  obtain ⟨Q, hQ⟩ := (Polynomial.dvd_iff_isRoot (a := C c)).mpr hc
  have hqu : IsUnit Q :=
    (hirr.isUnit_or_isUnit hQ).resolve_left (Polynomial.not_isUnit_X_sub_C (C c))
  obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.mp hqu
  obtain ⟨b, _, rfl⟩ := Polynomial.isUnit_iff.mp ha
  have hdeg : parameterDegree P = 0 := by
    rw [hQ]
    unfold parameterDegree
    apply Finset.sup_eq_zero.mpr
    intro i hi
    simp only [Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_X,
      Polynomial.coeff_C]
    split_ifs <;> simp_all
    rw [← Polynomial.C_mul, Polynomial.natDegree_C]
  omega

theorem evalAt_const (P : BiPoly) (s c : ℂ) :
    evalAt P s c = (P.eval (C c)).eval s := by
  rw [evalAt, specialize, Polynomial.eval_map]
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval₂_at_apply (p := P) (Polynomial.evalRingHom s) (C c))

theorem not_eventually_constant_of_root (P : BiPoly) (N : ℕ) (hN : 0 < N)
    (f : ℂ → ℂ) (hroot : ∀ᶠ s in 𝓝[≠] (0 : ℂ), evalAt P (s ^ N) (f s) = 0)
    (hconst : ∀ c : ℂ, P.eval (C c) ≠ 0) :
    ∀ c : ℂ, ¬ ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s = c := by
  intro c hc
  let p := Polynomial.expand ℂ N (P.eval (C c))
  have hp : p ≠ 0 := by
    intro heq
    exact hconst c (Polynomial.expand_injective hN
      (heq.trans (map_zero (Polynomial.expand ℂ N)).symm))
  have hpzero : ∀ᶠ s in 𝓝[≠] (0 : ℂ), p.eval s = 0 := by
    filter_upwards [hroot, hc] with s hs hsc
    rw [hsc, evalAt_const] at hs
    simpa [p, Polynomial.expand_eq_comp_X_pow, Polynomial.eval_comp] using hs
  obtain ⟨s, hs0, hsne⟩ := (hpzero.and (polynomial_eventually_ne_zero hp)).exists
  exact hsne hs0

theorem exists_branch_at_infinity (P : BiPoly) (hirr : Irreducible P)
    (hd : 0 < P.natDegree) :
    ∃ (N : ℕ) (f : ℂ → ℂ), 0 < N ∧ MeromorphicAt f 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), evalAt P (s ^ N)⁻¹ (f s) = 0) := by
  have hi : Irreducible (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
    ((hirr.isPrimitive (ne_of_gt hd)).irreducible_iff_irreducible_map_fraction_map).mp hirr
  obtain ⟨N, f, hN, hf, hroot⟩ := exists_ramified_meromorphic_root
    (reciprocalParameter P) (reciprocalParameter_natDegree_pos P hd)
    (irreducible_map_reciprocalParameter P hi)
  refine ⟨N, f, hN, hf, ?_⟩
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs
  filter_upwards [hroot, hne] with s hs hs0
  rw [evalAt_reciprocalParameter P _ _ (pow_ne_zero N hs0)] at hs
  exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero _ (pow_ne_zero N hs0))

theorem exists_nonconstant_branch_at_infinity (P : BiPoly) (hirr : Irreducible P)
    (hd : 0 < P.natDegree) (hconst : ∀ c : ℂ, P.eval (C c) ≠ 0) :
    ∃ (N : ℕ) (f : ℂ → ℂ), 0 < N ∧ MeromorphicAt f 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), evalAt P (s ^ N)⁻¹ (f s) = 0) ∧
      (∀ c : ℂ, ¬ ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s = c) := by
  have hi : Irreducible (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
    ((hirr.isPrimitive (ne_of_gt hd)).irreducible_iff_irreducible_map_fraction_map).mp hirr
  obtain ⟨N, f, hN, hf, hroot⟩ := exists_ramified_meromorphic_root
    (reciprocalParameter P) (reciprocalParameter_natDegree_pos P hd)
    (irreducible_map_reciprocalParameter P hi)
  refine ⟨N, f, hN, hf, ?_, ?_⟩
  · have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hs
    filter_upwards [hroot, hne] with s hs hs0
    rw [evalAt_reciprocalParameter P _ _ (pow_ne_zero N hs0)] at hs
    exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero _ (pow_ne_zero N hs0))
  · exact not_eventually_constant_of_root (reciprocalParameter P) N hN f hroot
      (fun c => reciprocalParameter_eval_C_ne_zero P c (hconst c))

theorem exists_branch_of_noncoordinate (P : BiPoly) (hirr : Irreducible P)
    (hx : 0 < parameterDegree P) (hy : 0 < P.natDegree) :
    ∃ (N : ℕ) (f : ℂ → ℂ), 0 < N ∧ MeromorphicAt f 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), evalAt P (s ^ N)⁻¹ (f s) = 0) ∧
      (∀ c : ℂ, ¬ ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s = c) :=
  exists_nonconstant_branch_at_infinity P hirr hy
    (eval_C_ne_zero_of_parameterDegree_pos P hirr hx)

theorem inverse_pow_eventually_ne_const (N : ℕ) (hN : 0 < N) (c : ℂ) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), (s ^ N)⁻¹ ≠ c := by
  let p : Polynomial ℂ := 1 - C c * X ^ N
  have hp : p ≠ 0 := by
    intro heq
    have hh := congrArg (fun q : Polynomial ℂ => q.coeff 0) heq
    simp [p, (ne_of_gt hN).symm] at hh
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs
  filter_upwards [polynomial_eventually_ne_zero hp, hne] with s hs hs0
  intro heq
  have hh : c * s ^ N = 1 := by rw [← heq, inv_mul_cancel₀ (pow_ne_zero N hs0)]
  apply hs
  simp [p, hh]

theorem inverse_pow_eventually_avoids_finite (N : ℕ) (hN : 0 < N) (B : Finset ℂ) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), (s ^ N)⁻¹ ∉ B := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert c B hc ih =>
      filter_upwards [inverse_pow_eventually_ne_const N hN c, ih] with s hs hc
      simpa using And.intro hs hc

/-- The normalization input, with both coordinate conditions and finite exclusions discharged. -/
theorem exists_meromorphic_infinity_chart (P : BiPoly) (hirr : Irreducible P)
    (hx : 0 < parameterDegree P) (hy : 0 < P.natDegree) :
    ∃ (N : ℕ) (f : ℂ → ℂ), 0 < N ∧
      MeromorphicAt (fun s : ℂ => (s ^ N)⁻¹) 0 ∧ MeromorphicAt f 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), evalAt P (s ^ N)⁻¹ (f s) = 0) ∧
      (∀ c : ℂ, ¬ ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s = c) ∧
      (∀ B : Finset ℂ, ∀ᶠ s in 𝓝[≠] (0 : ℂ), (s ^ N)⁻¹ ∉ B) := by
  obtain ⟨N, f, hN, hf, hroot, hnc⟩ := exists_branch_of_noncoordinate P hirr hx hy
  exact ⟨N, f, hN, (analyticAt_id.pow N).meromorphicAt.inv, hf, hroot, hnc,
    inverse_pow_eventually_avoids_finite N hN⟩

end

end GaloisForLFunctions.HTGeometry.AlgebraicInfinityBranch
