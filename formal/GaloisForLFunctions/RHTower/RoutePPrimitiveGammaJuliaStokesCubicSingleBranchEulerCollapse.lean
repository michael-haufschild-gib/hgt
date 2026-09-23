import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicMicrolocalWittSignatureRigidity

/-!
# Cubic Xi single-branch Euler collapse

When every marked point has one coefficient-generated Puiseux branch and one Stokes orbit, all
local irregular root terms cancel at unit Rees scale.  The global Witt value becomes the purely
topological quantity `2 * (1 - genus) * rank²`, independently of covers, slopes, exponent ceilings,
and puncture count.

Therefore genus-zero and genus-one unit-Rees systems of this type cannot land at the negative cubic
wall--Xi Malgrange residual.  Any viable low-genus completed-Xi landing must contain genuine
multibranch irregular geometry at some marked point.

No landing existence or arithmetic source-to-charge map is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

private theorem singleOrbitBranch_localWittForm_eq_two_rank_sq
    {K N : ℕ} (d : PuiseuxOrbitCoareaDatum 1 1 K N) (x : Fin 1 → ℝ) :
    localWittForm d x = 2 * localRankLinear d x ^ (2 : ℕ) := by
  have horbit : d.orbit 0 = 0 := Subsingleton.elim _ _
  have hcontact : d.toOrbitCoareaDatum.cuts.contact 0 0 = 0 := by
    change d.branches.canonicalCuts.contact 0 0 = 0
    rw [d.branches.canonicalCuts_contact_eq]
    simp
  have hcontactPairing : d.toOrbitCoareaDatum.contactPairing x = 0 := by
    simp [OrbitCoareaDatum.contactPairing, hcontact]
  rw [localWittForm_apply, OrbitCoareaDatum.cartanQuadratic]
  rw [hcontactPairing]
  simp [OrbitCoareaDatum.terminalEnergy, OrbitCoareaDatum.physicalRank,
    OrbitCoareaDatum.liftCharge, PuiseuxOrbitCoareaDatum.toOrbitCoareaDatum,
    localRankLinear_apply, horbit]
  ring

/-- Unit Rees fusion of one Puiseux branch and one Stokes orbit at every marked point forgets all
irregular slopes and cover degrees: only the Euler characteristic rank square survives. -/
theorem routePPrimitiveGammaJuliaStokesSingleOrbitBranchUnitReesWittForm_eulerCollapse
    {p : ℕ} {K N : Fin (p + 1) → ℕ}
    (genus : ℕ)
    (d : LocalData p (fun _ => 1) (fun _ => 1) K N)
    (x : compatibleCharges d) :
    globalReesWittForm genus d (fun _ _ => 1) x =
      2 * (1 - (genus : ℝ)) * commonRankLinear d x ^ (2 : ℕ) := by
  rw [globalReesWittForm_one, globalWittForm, QuadraticMap.add_apply,
    QuadraticMap.sum_apply, QuadraticMap.smul_apply, QuadraticMap.comp_apply,
    QuadraticMap.sq_apply]
  simp only [smul_eq_mul]
  have hrank : ∀ a, localRankLinear (d a) (x.1 a) = commonRankLinear d x :=
    compatible_localRank d x
  simp_rw [QuadraticMap.comp_apply, localProjection_apply,
    singleOrbitBranch_localWittForm_eq_two_rank_sq, hrank]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold fusionCoefficient
  push_cast
  ring

/-- No genus-zero coefficient-generated single-branch/single-orbit unit system can carry the
negative completed-Xi cubic Malgrange anomaly, regardless of its local irregular slopes. -/
theorem not_nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_singleOrbitBranch
    {p : ℕ} {K N : Fin (p + 1) → ℕ}
    {d : LocalData p (fun _ => 1) (fun _ => 1) K N} :
    ¬ Nonempty (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      0 d (fun _ _ => 1)) := by
  rintro ⟨x⟩
  have hneg := routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg x
  rw [routePPrimitiveGammaJuliaStokesSingleOrbitBranchUnitReesWittForm_eulerCollapse
    0 d x.1] at hneg
  have hrank_ne :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_commonRank_ne_zero
      (fun _ _ => zero_le_one) x
  have hrank_pos : 0 < commonRankLinear d x.1 ^ (2 : ℕ) := sq_pos_of_ne_zero hrank_ne
  norm_num at hneg
  nlinarith

/-- No genus-one coefficient-generated single-branch/single-orbit unit system can carry the
negative completed-Xi cubic Malgrange anomaly. -/
theorem not_nonempty_routePPrimitiveGammaJuliaStokesCubicTorusUnitLandingFiber_singleOrbitBranch
    {p : ℕ} {K N : Fin (p + 1) → ℕ}
    {d : LocalData p (fun _ => 1) (fun _ => 1) K N} :
    ¬ Nonempty (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      1 d (fun _ _ => 1)) := by
  rintro ⟨x⟩
  have hneg := routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg x
  rw [routePPrimitiveGammaJuliaStokesSingleOrbitBranchUnitReesWittForm_eulerCollapse
    1 d x.1] at hneg
  norm_num at hneg

end

end RHTower
