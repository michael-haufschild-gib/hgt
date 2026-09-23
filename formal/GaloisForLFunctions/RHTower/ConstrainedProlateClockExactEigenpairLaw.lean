import GaloisForLFunctions.RHTower.ConstrainedProlateClockEnvelope
import GaloisForLFunctions.RHTower.DepthSecularRootSpec

/-!
# Clock-universal exact depth eigenpairs

The clock-envelope theorem identifies the limiting location of the chosen depth root, while the
root-specification theorem turns actual root existence into the exact secular and constraint
identities.  The positive CCM limit closes the apparent gap between them: eventually the chosen
root cannot be the definition's junk value, so existence and the full nonzero constrained
eigenpair hold without adding a bracket hypothesis.
-/

open Filter Set

noncomputable section

namespace RHTower

/-- **Clock-universal exact depth-eigenpair law.**  At every fixed depth, a clock-enveloped CCM
family has both the universal Hermite ratio and, eventually, a genuine nonzero secular vector in
the constrained hyperplane.  Root existence is not an extra assumption: positivity of the
universal ratio rules out the junk branch of `depthSecularRoot`. -/
theorem LadderEnvelope.ccm_depth_ratio_and_exactEigenpair_eventually
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ (2 : ℕ)) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam => depthSecularRoot (D lam) (ℓ lam) k / D lam (k + 1)) atTop
        (nhds (constrainedProlateHermiteTheta k)) ∧
      ∀ᶠ lam in atTop,
        depthSecularRoot (D lam) (ℓ lam) k ∈ Ioo (D lam k) (D lam (k + 1)) ∧
        depthSecular (D lam) (ℓ lam) k (depthSecularRoot (D lam) (ℓ lam) k) = 0 ∧
        (∑' j : ℕ,
          ℓ lam j * secularVector (D lam) (ℓ lam)
            (depthSecularRoot (D lam) (ℓ lam) k) j) = 0 ∧
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) ≠ 0 := by
  have hlim := h.ccm_depth_ratio_tendsto k hsum hbessel hl
  refine ⟨hlim, ?_⟩
  have htheta := constrainedProlateHermiteTheta_mem_Ioo k
  have hratioPos : ∀ᶠ lam in atTop,
      0 < depthSecularRoot (D lam) (ℓ lam) k / D lam (k + 1) := by
    have hnear := hlim.eventually (eventually_gt_nhds (show
      constrainedProlateHermiteTheta k / 2 < constrainedProlateHermiteTheta k by
        linarith [htheta.1]))
    filter_upwards [hnear] with lam hlam
    linarith [htheta.1]
  have hcoordNe : ∀ᶠ lam in atTop, ℓ lam (k + 1) ≠ 0 :=
    (hl (k + 1) le_rfl).eventually_ne
      (constrainedProlateHermiteCoordinate_ne_zero (k + 1))
  filter_upwards [hratioPos, h.depth_struct k, hsum, hcoordNe]
    with lam hratio hstruct hsumLam hcoordLam
  obtain ⟨⟨hhead, hk01, hk12⟩, hfloor⟩ := hstruct
  have hDpos : 0 < D lam (k + 1) :=
    lt_of_le_of_lt (hhead k le_rfl).1 hk01
  have hrootPos : 0 < depthSecularRoot (D lam) (ℓ lam) k := by
    rw [div_pos_iff] at hratio
    rcases hratio with hratio | hratio
    · exact hratio.1
    · linarith [hratio.2, hDpos]
  have hex : ∃ μ ∈ Ioo (D lam k) (D lam (k + 1)),
      depthSecular (D lam) (ℓ lam) k μ = 0 := by
    by_contra hno
    have hrootZero : depthSecularRoot (D lam) (ℓ lam) k = 0 := by
      unfold depthSecularRoot
      rw [dif_neg hno]
    rw [hrootZero] at hrootPos
    exact lt_irrefl 0 hrootPos
  have hmem := depthSecularRoot_mem_Ioo hex
  have hsecular := depthSecular_depthSecularRoot_eq_zero hex
  have hconstraint : (∑' j : ℕ,
      ℓ lam j * secularVector (D lam) (ℓ lam)
        (depthSecularRoot (D lam) (ℓ lam) k) j) = 0 :=
    tsum_mul_secularVector_depthSecularRoot_eq_zero hfloor hsumLam
      (lt_trans hmem.2 hk12) hex
  have hvectorNe :
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) ≠ 0 := by
    have hdenom : D lam (k + 1) - depthSecularRoot (D lam) (ℓ lam) k ≠ 0 :=
      ne_of_gt (sub_pos.mpr hmem.2)
    have hatCoord :
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) (k + 1) ≠ 0 := by
      unfold secularVector
      exact div_ne_zero hcoordLam hdenom
    intro hv
    have hvCoord := congrFun hv (k + 1)
    simp only [Pi.zero_apply] at hvCoord
    exact hatCoord hvCoord
  exact ⟨hmem, hsecular, hconstraint, hvectorNe⟩

end RHTower

end
