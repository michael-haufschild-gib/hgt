import GaloisForLFunctions.HTGeometry.GermSliceAdmissible
import GaloisForLFunctions.HTGeometry.SliceWeierstrassUnit
import GaloisForLFunctions.HTGeometry.SliceWeierstrassFactorization
import GaloisForLFunctions.HTGeometry.WeierstrassPolynomial

/-!
# Weierstrass preparation of a germ

Assembling the admissibility package with the slice preparation theorem: a holomorphic function
near the origin of `ℂ^(n+1)` whose slice in the distinguished variable is not identically zero is,
on a polydisc, a *distinguished* monic polynomial in that variable — coefficients holomorphic in
the parameters and vanishing at the origin — times a nowhere vanishing holomorphic unit.

The coefficients are the elementary symmetric functions of the moving root multiset, and at the
origin every root is the origin, because the radius was chosen so that the slice has no other zero
in the closed disc.
-/

open Complex Metric Set Filter
open scoped Real Topology BigOperators

namespace HTGeometry

variable {n : ℕ}

/-- Every element of a replicated multiset of zeros is zero, so all its higher elementary
symmetric functions vanish. -/
theorem esymm_eq_zero_of_forall_eq_zero {M : Multiset ℂ} (hM : ∀ r ∈ M, r = 0) {k : ℕ}
    (hk : 0 < k) : M.esymm k = 0 := by
  classical
  rw [Multiset.esymm]
  refine Multiset.sum_eq_zero ?_
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
  have hsub : s ≤ M := (Multiset.mem_powersetCard.mp hs).1
  have hcard : Multiset.card s = k := (Multiset.mem_powersetCard.mp hs).2
  have hne : s ≠ 0 := by
    intro h
    rw [h] at hcard
    simp only [Multiset.card_zero] at hcard
    omega
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne
  have hr0 : r = 0 := hM r (Multiset.mem_of_le hsub hr)
  exact Multiset.prod_eq_zero (by rwa [hr0] at hr)

/-- **The roots of the slice at the origin all sit at the origin.** -/
theorem sliceRoots_eq_zero_of_isolated {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    (hadm : SliceAdmissible f t (0 : Fin n → ℂ))
    (hiso : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ t → f (Fin.cons z (0 : Fin n → ℂ)) ≠ 0) :
    ∀ r ∈ sliceRoots f t (0 : Fin n → ℂ), r = 0 := by
  intro r hr
  by_contra hr0
  have hlt : ‖r‖ < t := sliceRoots_norm_lt ht hadm r hr
  exact hiso r hr0 hlt.le ((slice_eq_zero_iff_mem_sliceRoots ht hadm hlt).mpr hr)

/-- **Weierstrass preparation of a germ.**  A holomorphic function whose slice in the distinguished
variable is not identically zero near the origin factors on a polydisc as a distinguished monic
polynomial times a nowhere vanishing unit. -/
theorem germ_weierstrass_preparation {f : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U) (h0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ (t δ : ℝ) (d : ℕ) (a : ℕ → (Fin n → ℂ) → ℂ) (u : (Fin (n + 1) → ℂ) → ℂ),
      0 < t ∧ 0 < δ ∧
      (∀ j, DifferentiableOn ℂ (a j) (ball (0 : Fin n → ℂ) δ)) ∧
      (∀ j, j < d → a j (0 : Fin n → ℂ) = 0) ∧
      DifferentiableOn ℂ u
        {w : Fin (n + 1) → ℂ | Fin.tail w ∈ ball (0 : Fin n → ℂ) δ ∧ ‖w 0‖ < t} ∧
      (∀ y ∈ ball (0 : Fin n → ℂ) δ, ∀ z : ℂ, ‖z‖ < t →
        f (Fin.cons z y)
            = (z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j) * u (Fin.cons z y)
          ∧ u (Fin.cons z y) ≠ 0) := by
  classical
  obtain ⟨t, δ, htpos, hδpos, hdisc2, hdisc, hnez, hadm, hiso⟩ :=
    exists_sliceAdmissible_nhds hU h0 hf hreg
  set V : Set (Fin n → ℂ) := ball (0 : Fin n → ℂ) δ with hV
  have hVopen : IsOpen V := isOpen_ball
  have hVconn : IsPreconnected V := (convex_ball (0 : Fin n → ℂ) δ).isPreconnected
  have h0V : (0 : Fin n → ℂ) ∈ V := mem_ball_self hδpos
  set d : ℕ := Multiset.card (sliceRoots f t (0 : Fin n → ℂ)) with hd
  have hcard : ∀ y ∈ V, Multiset.card (sliceRoots f t y) = d := fun y hy =>
    card_sliceRoots_const_of_isPreconnected hU hVopen hf htpos hdisc hnez hadm hVconn hy h0V
  refine ⟨t, δ, d, fun j y => (-1) ^ (d - j) * (sliceRoots f t y).esymm (d - j),
    sliceUnit f t, htpos, hδpos, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ((differentiableOn_esymm_sliceRoots hU hVopen hf htpos hdisc hnez hadm
      (d - j)).const_mul ((-1 : ℂ) ^ (d - j)))
  · intro j hj
    have hzero : (sliceRoots f t (0 : Fin n → ℂ)).esymm (d - j) = 0 :=
      esymm_eq_zero_of_forall_eq_zero
        (sliceRoots_eq_zero_of_isolated htpos (hadm _ h0V) hiso) (by omega)
    show (-1 : ℂ) ^ (d - j) * (sliceRoots f t (0 : Fin n → ℂ)).esymm (d - j) = 0
    rw [hzero, mul_zero]
  · exact differentiableOn_sliceUnit hU hVopen hf htpos hdisc hnez hadm hVconn h0V
  · intro y hy z hz
    obtain ⟨hfact, hune⟩ :=
      (weierstrass_preparation hU hVopen hf htpos hdisc hnez hadm hVconn h0V).2.2 y hy z hz
    refine ⟨?_, hune⟩
    rw [hfact, sliceWeierstrass_cons, multisetLinearProd_eq_monic, hcard y hy]

end HTGeometry
