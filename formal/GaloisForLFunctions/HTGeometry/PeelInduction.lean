import GaloisForLFunctions.HTGeometry.PeelEntry

/-!
# The peel, iterated down the flag

Every hypothesis of the peel step is reproduced by the peel step, so the step can be chained.  The
induction bottoms out at a `1×1` determinant, whose single entry is the logarithmic derivative up to
a degree-`−2` correction and is therefore nonzero: its scaled value at infinity is the degree of the
denominator.

Hence the logarithmic Jacobian is nonsingular at every height, and the card's law holds for every
polynomial-coefficient cascade of every length.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Q v : ℕ → Polynomial ℂ}

/-! ## The induction's hypothesis package -/

/-- The data the peel consumes and reproduces. -/
structure PeelHyp (Q v : ℕ → Polynomial ℂ) (m' : ℕ) (u : ℕ → CascadeField) : Prop where
  mem : ∀ l, u l ∈ lowSub Q v (m' + 1)
  vanish : ∀ l, m' + 1 < l → u l = 0
  shape : BorderShape Q (m' + 1) u
  lim : ∀ l, TopLim (m' + 1) (u l) (logBorder Q m' l)

/-- The border row satisfies the package. -/
theorem peelHyp_logBorder (Q v : ℕ → Polynomial ℂ) {m' : ℕ}
    (hq : 1 ≤ (Q (m' + 1)).natDegree) :
    PeelHyp Q v m' (logBorder Q (m' + 1)) where
  mem := fun l => logBorder_mem_lowSub Q v (m' + 1) l
  vanish := fun l hl => logBorder_of_gt (by omega)
  shape := borderShape_logBorder' Q (m' + 1)
  lim := fun l => topLim_logBorder hq l

/-! ## The base case -/

/-- **A border-shaped newest entry is nonzero**: its scaled value at infinity is the degree of the
denominator. -/
theorem ne_zero_of_borderShape {n : ℕ} (hq : 1 ≤ (Q (n + 1)).natDegree)
    {u : ℕ → CascadeField} (hshape : BorderShape Q (n + 1) u) : u (n + 1) ≠ 0 := by
  intro hzero
  have hlim := topLim_fx_mul_of_borderShape hq hshape
  rw [hzero, mul_zero] at hlim
  have hqne : (algebraMap ℂ CascadeField ((Q (n + 1)).natDegree : ℂ)) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr
      (Nat.cast_ne_zero.mpr (by omega))
  exact hqne (topLim_unique (topFree_algebraMap_complex (n + 1) _) (topFree_zero (n + 1))
    hlim topLim_const)

/-! ## The rescaling factor -/

/-- The factor that restores the shape of the peeled vector. -/
noncomputable def peelScale (Q : ℕ → Polynomial ℂ) (n : ℕ) (α : ℂ) : CascadeField :=
  fact (Q (n + 1)) (n + 1) * prodHead Q (n + 1)
    * algebraMap ℂ CascadeField (α * ((Q (n + 2)).natDegree : ℂ))

theorem peelScale_ne_zero {n : ℕ} (hQ : ∀ j, Q j ≠ 0) {α : ℂ} (hα : α ≠ 0)
    (hq2 : 1 ≤ (Q (n + 2)).natDegree) : peelScale Q n α ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (fact_ne_zero (hQ (n + 1)) (n + 1)) (prodHead_ne_zero hQ (n + 1)))
    ((map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr
      (mul_ne_zero hα (Nat.cast_ne_zero.mpr (by omega))))

theorem inv_peelScale_mem_lowSub {n : ℕ} (Q v : ℕ → Polynomial ℂ) {α : ℂ} :
    (peelScale Q n α)⁻¹ ∈ lowSub Q v (n + 1) := by
  rw [peelScale, mul_inv, mul_inv]
  refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (invQ_mem_lowSub Q v (le_refl (n + 1))) ?_) ?_
  · rw [prodHead, ← Finset.prod_inv_distrib]
    refine Subalgebra.prod_mem _ fun j hj => ?_
    have hjm : j < n + 1 := Finset.mem_range.mp hj
    exact invQ_mem_lowSub Q v (by omega)
  · rw [← map_inv₀]
    exact Subalgebra.algebraMap_mem _ _

/-! ## The induction -/

/-- **The orbit determinant of a peel-shaped vector is nonzero, at every level.** -/
theorem det_jetOrbitMatrix_ne_zero_of_peelHyp (hQ : ∀ j, Q j ≠ 0)
    (hQdeg : ∀ j, 1 ≤ (Q (j + 1)).natDegree)
    (hvlin : ∀ j, ∃ α β : ℂ, α ≠ 0 ∧
      v (j + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    ∀ (m' : ℕ) (u : ℕ → CascadeField), PeelHyp Q v m' u →
      (jetOrbitMatrix Q v (m' + 1) (m' + 1) u).det ≠ 0 := by
  intro m'
  induction m' with
  | zero =>
      intro u hu
      rw [jetOrbitMatrix, Matrix.det_fin_one]
      simpa using ne_zero_of_borderShape (n := 0) (hQdeg 0) hu.shape
  | succ n ih =>
      intro u hu
      obtain ⟨α, β, hα, hv⟩ := hvlin (n + 1)
      have hvd : (v (n + 2)).natDegree = 1 := by
        rw [hv]
        exact Polynomial.natDegree_linear hα
      refine det_jetOrbitMatrix_ne_zero_of_peel Q v hQ hv (hQdeg (n + 1)) hvd hu.mem hu.vanish
        (fun l => logBorder_mem_lowSub Q v (n + 1) l) hu.lim hu.shape ?_ ?_
      · have h := hu.shape
        rw [BorderShape] at h
        exact Subalgebra.sub_mem _ (hu.mem (n + 1 + 1))
          (logFactorQ_mem_lowSub Q v (le_refl (n + 1 + 1)))
      · -- the minor: rescale, then apply the induction hypothesis
        set y : ℕ → CascadeField :=
          limVec Q v (n + 1) α (logBorder Q (n + 1)) (peelRes Q (n + 1)) 1 with hy
        set c : CascadeField := peelScale Q n α with hc
        have hcne : c ≠ 0 := peelScale_ne_zero hQ hα (hQdeg (n + 1))
        have hshape : BorderShape Q (n + 1) (fun l => c⁻¹ * y l) := by
          rw [hc, peelScale, hy]
          exact borderShape_rescaled hQ (hQdeg n) (by
            obtain ⟨α', β', hα', hv'⟩ := hvlin n
            rw [hv']
            exact Polynomial.natDegree_linear hα') hα (hQdeg (n + 1))
            (logBorder_top_eq Q (n + 1))
        have hlim : ∀ l, TopLim (n + 1) (c⁻¹ * y l) (logBorder Q n l) := by
          intro l
          rw [hc, peelScale, hy]
          exact topLim_rescaled_limVec hQ (hQdeg n) (by
            obtain ⟨α', β', hα', hv'⟩ := hvlin n
            rw [hv']
            exact Polynomial.natDegree_linear hα') hα (hQdeg (n + 1)) l
        have hvanish : ∀ l, n + 1 < l → c⁻¹ * y l = 0 := by
          intro l hl
          rw [hy, limVec_succ_of_gt Q v α (logBorder Q (n + 1)) (peelRes Q (n + 1)) 0 l
            (by omega), mul_zero]
        have hmemy : ∀ l, c⁻¹ * y l ∈ lowSub Q v (n + 1) := by
          intro l
          exact Subalgebra.mul_mem _ (inv_peelScale_mem_lowSub Q v)
            (limVec_mem_lowSub Q v (fun l' => logBorder_mem_lowSub Q v (n + 1) l')
              (peelRes_mem_lowSub Q v (n + 1)) 1 l)
        have hhyp : PeelHyp Q v n (fun l => c⁻¹ * y l) :=
          ⟨hmemy, hvanish, hshape, hlim⟩
        have hscaled := ih (fun l => c⁻¹ * y l) hhyp
        rw [det_jetOrbitMatrix_smul Q v (n + 1) (n + 1) c⁻¹ y] at hscaled
        exact fun h0 => hscaled (by rw [h0, mul_zero])

/-! ## The logarithmic Jacobian is nonsingular at every height -/

/-- **The logarithmic Jacobian is nonsingular at every height.** -/
theorem logJetJacobian_det_ne_zero (hQ : ∀ j, Q j ≠ 0)
    (hQdeg : ∀ j, 1 ≤ (Q (j + 1)).natDegree)
    (hvlin : ∀ j, ∃ α β : ℂ, α ≠ 0 ∧
      v (j + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β) (n : ℕ) :
    (logJetJacobian Q v n).det ≠ 0 := by
  rw [logJetJacobian_eq_jetOrbitMatrix]
  exact det_jetOrbitMatrix_ne_zero_of_peelHyp hQ hQdeg hvlin n (logBorder Q (n + 1))
    (peelHyp_logBorder Q v (hQdeg n))

end GaloisForLFunctions.HTGeometry
