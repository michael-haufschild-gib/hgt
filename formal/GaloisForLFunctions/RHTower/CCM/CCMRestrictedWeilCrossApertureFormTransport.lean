import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilExactFiniteSchur

/-!
# Cross-aperture transport of the literal restricted Weil form

The completed archimedean--polar--prime form does not change on a form vector already supported
in a smaller aperture.  Earlier work established this only on the diagonal.  This module upgrades
that fact to every mixed matrix coefficient by complex polarization.  Consequently, enlarging an
aperture alters a Suzuki covariance only through the inverse problem on the new shell (and its
coercive metric), never through an unaccounted change to the retained completed source form.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The literal completed restricted-Weil form is preserved on every mixed pair of old-aperture
form vectors.  This is complex, not merely real-diagonal, transport: prime, polar, and Γ terms
remain coupled throughout the polarization. -/
theorem ccmRestrictedWeilForm_eq_of_val_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u v : CCMArchimedeanFormDomain a} {u' v' : CCMArchimedeanFormDomain b}
    (hu : u'.1 = u.1) (hv : v'.1 = v.1) :
    ccmRestrictedWeilForm b u' v' = ccmRestrictedWeilForm a u v := by
  let Ta := ccmRestrictedWeilZeroFormOperator a
  let Tb := ccmRestrictedWeilZeroFormOperator b
  have hTa : IsSelfAdjoint Ta :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr
      (ccmRestrictedWeilZeroFormOperator_adjoint a)
  have hTb : IsSelfAdjoint Tb :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr
      (ccmRestrictedWeilZeroFormOperator_adjoint b)
  have hTaSymm : (Ta : CCMArchimedeanFormDomain a →ₗ[ℂ]
      CCMArchimedeanFormDomain a).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTa
  have hTbSymm : (Tb : CCMArchimedeanFormDomain b →ₗ[ℂ]
      CCMArchimedeanFormDomain b).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTb
  have hdiag : ∀ {x : CCMArchimedeanFormDomain a} {y : CCMArchimedeanFormDomain b},
      y.1 = x.1 →
        inner ℂ ((Tb : CCMArchimedeanFormDomain b →ₗ[ℂ]
          CCMArchimedeanFormDomain b) y) y =
        inner ℂ ((Ta : CCMArchimedeanFormDomain a →ₗ[ℂ]
          CCMArchimedeanFormDomain a) x) x := by
    intro x y hxy
    have hsource := ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hxy
    have hbsource : (inner ℂ (Tb y) y).re =
        ccmRestrictedWeilSourceQuadratic b y := by
      rw [show Tb = ccmRestrictedWeilZeroFormOperator b by rfl,
        inner_ccmRestrictedWeilZeroFormOperator,
        ccmRestrictedWeilForm_self_re_eq_source]
    have hasource : (inner ℂ (Ta x) x).re =
        ccmRestrictedWeilSourceQuadratic a x := by
      rw [show Ta = ccmRestrictedWeilZeroFormOperator a by rfl,
        inner_ccmRestrictedWeilZeroFormOperator,
        ccmRestrictedWeilForm_self_re_eq_source]
    calc
      inner ℂ (Tb y) y = ((inner ℂ (Tb y) y).re : ℂ) :=
        (hTbSymm.coe_re_inner_apply_self y).symm
      _ = (ccmRestrictedWeilSourceQuadratic b y : ℂ) :=
        congrArg (fun r : ℝ => (r : ℂ)) hbsource
      _ = (ccmRestrictedWeilSourceQuadratic a x : ℂ) :=
        congrArg (fun r : ℝ => (r : ℂ)) hsource
      _ = ((inner ℂ (Ta x) x).re : ℂ) :=
        congrArg (fun r : ℝ => (r : ℂ)) hasource.symm
      _ = inner ℂ (Ta x) x := hTaSymm.coe_re_inner_apply_self x
  rw [← inner_ccmRestrictedWeilZeroFormOperator b,
    ← inner_ccmRestrictedWeilZeroFormOperator a]
  change inner ℂ ((Tb : CCMArchimedeanFormDomain b →ₗ[ℂ]
      CCMArchimedeanFormDomain b) u') v' =
    inner ℂ ((Ta : CCMArchimedeanFormDomain a →ₗ[ℂ]
      CCMArchimedeanFormDomain a) u) v
  rw [
    hTbSymm.inner_map_polarization u' v',
    hTaSymm.inner_map_polarization u v]
  have hadd : (u' + v').1 = (u + v).1 := by
    change u'.1 + v'.1 = u.1 + v.1
    rw [hu, hv]
  have hsub : (u' - v').1 = (u - v).1 := by
    change u'.1 - v'.1 = u.1 - v.1
    rw [hu, hv]
  have hiadd : (u' + (RCLike.I : ℂ) • v').1 =
      (u + (RCLike.I : ℂ) • v).1 := by
    change u'.1 + (RCLike.I : ℂ) • v'.1 = u.1 + (RCLike.I : ℂ) • v.1
    rw [hu, hv]
  have hisub : (u' - (RCLike.I : ℂ) • v').1 =
      (u - (RCLike.I : ℂ) • v).1 := by
    change u'.1 - (RCLike.I : ℂ) • v'.1 = u.1 - (RCLike.I : ℂ) • v.1
    rw [hu, hv]
  rw [hdiag hadd, hdiag hsub, hdiag hiadd, hdiag hisub]

end RHTower
