import GaloisForLFunctions.HTGeometry.GermWeierstrassPreparation
import GaloisForLFunctions.HTGeometry.SliceWeierstrassDivision

/-!
# Weierstrass division of a germ

Dividing a holomorphic germ by the distinguished polynomial of another one: on a polydisc the
dividend is a holomorphic quotient times the distinguished polynomial, plus a polynomial in the
distinguished variable of degree below its degree, whose coefficients are holomorphic in the
parameters.

Together with the uniqueness of such a decomposition this is the statement that the local ring is
a finite free module over the ring in the remaining variables, which is what carries divisibility
questions from the germ ring to a polynomial ring.
-/

open Complex Metric Set Filter
open scoped Real Topology BigOperators

namespace HTGeometry

variable {n : ℕ}

/-- **Weierstrass division of a germ.** -/
theorem germ_weierstrass_division {f g : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U) (h0 : (0 : Fin (n + 1) → ℂ) ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ (t δ : ℝ) (d : ℕ) (a b : ℕ → (Fin n → ℂ) → ℂ) (q u : (Fin (n + 1) → ℂ) → ℂ),
      0 < t ∧ 0 < δ ∧
      (∀ j, DifferentiableOn ℂ (a j) (ball (0 : Fin n → ℂ) δ)) ∧
      (∀ j, j < d → a j (0 : Fin n → ℂ) = 0) ∧
      (∀ j, DifferentiableOn ℂ (b j) (ball (0 : Fin n → ℂ) δ)) ∧
      DifferentiableOn ℂ q
        {w : Fin (n + 1) → ℂ | Fin.tail w ∈ ball (0 : Fin n → ℂ) δ ∧ ‖w 0‖ < t} ∧
      DifferentiableOn ℂ u
        {w : Fin (n + 1) → ℂ | Fin.tail w ∈ ball (0 : Fin n → ℂ) δ ∧ ‖w 0‖ < t} ∧
      (∀ y ∈ ball (0 : Fin n → ℂ) δ, ∀ z : ℂ, ‖z‖ < t →
        f (Fin.cons z y)
            = (z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j) * u (Fin.cons z y)
          ∧ u (Fin.cons z y) ≠ 0) ∧
      (∀ y ∈ ball (0 : Fin n → ℂ) δ, ∀ z : ℂ, ‖z‖ < t →
        g (Fin.cons z y)
          = q (Fin.cons z y) * (z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j)
            + ∑ j ∈ Finset.range d, b j y * z ^ j) := by
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
    fun j y => sliceDivRemainderCoeff f g t y j, sliceDivQuotient f g t, sliceUnit f t,
    htpos, hδpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ((differentiableOn_esymm_sliceRoots hU hVopen hf htpos hdisc hnez hadm
      (d - j)).const_mul ((-1 : ℂ) ^ (d - j)))
  · intro j hj
    have hzero : (sliceRoots f t (0 : Fin n → ℂ)).esymm (d - j) = 0 :=
      esymm_eq_zero_of_forall_eq_zero
        (sliceRoots_eq_zero_of_isolated htpos (hadm _ h0V) hiso) (by omega)
    show (-1 : ℂ) ^ (d - j) * (sliceRoots f t (0 : Fin n → ℂ)).esymm (d - j) = 0
    rw [hzero, mul_zero]
  · intro j y hy
    exact (differentiableAt_sliceDivRemainderCoeff hU hVopen hf hg htpos hdisc hnez hadm
      hVconn hy j).differentiableWithinAt
  · exact differentiableOn_sliceDivQuotient hU hVopen hf hg htpos hdisc hnez hadm hVconn h0V
  · exact differentiableOn_sliceUnit hU hVopen hf htpos hdisc hnez hadm hVconn h0V
  · intro y hy z hz
    obtain ⟨hfact, hune⟩ :=
      (weierstrass_preparation hU hVopen hf htpos hdisc hnez hadm hVconn h0V).2.2 y hy z hz
    refine ⟨?_, hune⟩
    rw [hfact, sliceWeierstrass_cons, multisetLinearProd_eq_monic, hcard y hy]
  · intro y hy z hz
    have hgslice : DifferentiableOn ℂ (fun w : ℂ => g (Fin.cons w y)) (ball (0 : ℂ) (2 * t)) := by
      intro w hw
      have hmem : (Fin.cons w y : Fin (n + 1) → ℂ) ∈ U := by
        refine hdisc2 y hy w ?_
        simpa [dist_zero_right] using (mem_ball_zero_iff.mp hw).le
      exact DifferentiableWithinAt.comp w (hg _ hmem)
        (differentiable_consFirst y w).differentiableWithinAt (fun v hv => by
          refine hdisc2 y hy v ?_
          simpa [dist_zero_right] using (mem_ball_zero_iff.mp hv).le)
    have hdiv := weierstrass_division htpos (hadm y hy) (by linarith : t < 2 * t) hgslice z
      (by simpa using hz)
    rw [hdiv, sliceWeierstrass_cons, multisetLinearProd_eq_monic, hcard y hy]

end HTGeometry
