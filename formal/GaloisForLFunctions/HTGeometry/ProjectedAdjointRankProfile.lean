import GaloisForLFunctions.HTGeometry.ProjectedAdjointDefectRank

/-!
# Arbitrary-rank profile of a projected adjoint defect

Finite and infinite negative index are treated uniformly: the projected contraction defect carries
an `r`-dimensional negative tuple exactly when the contraction adjoint restricted to the projection
range has algebraic rank at least `r`.  No finite-dimensionality or injectivity assumption is used.
-/

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A real form carries a finite negative dimension witnessed by a tuple. -/
def HasFiniteFormNegativeDimension (q : H → ℝ) (r : ℕ) : Prop :=
  ∃ v : Fin r → H, ∀ c : Fin r → ℂ, c ≠ 0 →
    q (∑ i, c i • v i) < 0

/-- The adjoint restricted to a subspace has algebraic rank at least `r`. -/
def RestrictedAdjointRankAtLeast
    (K : Submodule ℂ H) (C : H →L[ℂ] H) (r : ℕ) : Prop :=
  ∃ v : Fin r → K,
    LinearIndependent ℂ (fun i => C.adjoint (v i : H))

/-- Exact arbitrary-rank classification of the projected adjoint defect. -/
theorem projectedAdjointDefect_hasFiniteNegativeDimension_iff_rankAtLeast
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (C : H →L[ℂ] H) (hC : ‖C‖ ≤ 1) (r : ℕ) :
    HasFiniteFormNegativeDimension (projectedAdjointDefectForm K C) r ↔
      RestrictedAdjointRankAtLeast K C r := by
  constructor
  · rintro ⟨v, hv⟩
    let w : Fin r → K := fun i => K.orthogonalProjectionOnto (v i)
    refine ⟨w, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    by_contra hci
    have hc0 : c ≠ 0 := by
      intro hzero
      exact hci (congrFun hzero i)
    let d : H := ∑ j, c j • v j
    let u : H := K.starProjection d
    let y : H := d - u
    have huK : u ∈ K := K.starProjection_apply_mem d
    have hAu : C.adjoint u = 0 := by
      have hsumw : (∑ j, c j • (w j : H)) = u := by
        change (∑ j, c j • K.starProjection (v j)) =
          K.starProjection (∑ j, c j • v j)
        simp only [map_sum, map_smul]
      have hmap : C.adjoint (∑ j, c j • (w j : H)) = 0 := by
        simpa only [map_sum, map_smul] using hc
      rwa [hsumw] at hmap
    have hyKperp : y ∈ Kᗮ := K.sub_starProjection_mem_orthogonal d
    have hperp : (inner ℂ u y : ℂ) = 0 :=
      ((K.mem_orthogonal y).1 hyKperp u huK)
    have hsplit : d = u + y := by
      change d = u + (d - u)
      abel
    have hpyth : ‖d‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ) := by
      rw [hsplit]
      simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u y hperp
    have hadj : C.adjoint d = C.adjoint y := by
      rw [hsplit, map_add, hAu, zero_add]
    have hstar : K.starProjection d = u := rfl
    have hnonneg : 0 ≤ projectedAdjointDefectForm K C d := by
      rw [projectedAdjointDefectForm, hstar, hadj, hpyth]
      have hbound := adjoint_norm_le_self_of_opNorm_le_one C hC y
      nlinarith [norm_nonneg y, norm_nonneg (C.adjoint y)]
    exact (not_lt_of_ge hnonneg) (hv c hc0)
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (v i : H), ?_⟩
    intro c hc
    let x : H := ∑ i, c i • (v i : H)
    have hxK : x ∈ K := by
      dsimp only [x]
      exact Submodule.sum_mem K fun i _ => K.smul_mem (c i) (v i).property
    have hAx : C.adjoint x ≠ 0 := by
      intro hzero
      have hsum : ∑ i, c i • C.adjoint (v i : H) = 0 := by
        change C.adjoint (∑ i, c i • (v i : H)) = 0 at hzero
        simpa only [map_sum, map_smul] using hzero
      have hcAll : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp hv c hsum
      apply hc
      funext i
      exact hcAll i
    have hstar : K.starProjection x = x :=
      Submodule.starProjection_eq_self_iff.mpr hxK
    change projectedAdjointDefectForm K C x < 0
    rw [projectedAdjointDefectForm, hstar]
    nlinarith [norm_pos_iff.mpr hAx]

end GaloisForLFunctions.HTGeometry
