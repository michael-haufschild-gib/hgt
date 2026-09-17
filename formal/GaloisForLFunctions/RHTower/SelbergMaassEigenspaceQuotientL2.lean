import GaloisForLFunctions.RHTower.SelbergMaassHeckeEigenspace
import GaloisForLFunctions.RHTower.MaassQuotientL2

/-!
# Principal Maass eigenspaces in quotient `L²`

The zero-inclusive principal `GL(2,ℝ)` Maass eigenspace has a canonical
injective linear realization in the actual integral quotient `L²` space.  It
maps the original Maass source to its existing quotient vector.  This is the
carrier needed before a source-specific Laplacian and compact-resolvent proof
can establish finite multiplicity; it supplies neither that operator nor a
finite-place factor.
-/

open MeasureTheory UpperHalfPlane Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

namespace PrincipalMaassEigenspaceL2

variable (N : ℕ) {lam : ℝ}

/-- Underlying real `SL(2,ℝ)` invariant function of a principal GL Maass eigenspace vector. -/
def toMaassInvariant
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma (N + 1))) :=
  ⟨u.1, by
    intro γ z
    obtain ⟨A, hA, hγ⟩ := γ.2
    rw [← hγ]
    exact u.2.1 ⟨integralSL2ToReal A, ⟨A, hA, rfl⟩⟩ z⟩

/-- Literal inverse lift of the principal GL Maass eigenspace function. -/
def quotientFunction
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N + 1)) → ℂ :=
  maassInvariantQuotientLift _ (toMaassInvariant N u)

/-- A nonzero zero-inclusive eigenspace vector recovers an ordinary Maass cusp eigenform. -/
def toMaassCuspEigenform
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) (hu : u ≠ 0) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam :=
  glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam
    ⟨maassEigenspaceToInvariant u, by
      refine ⟨?_, u.2.2.1, u.2.2.2⟩
      intro hzero
      apply hu
      apply Subtype.ext
      exact hzero⟩

/-- Away from zero, the literal quotient function is the existing Maass source function. -/
theorem quotientFunction_eq_sourceFunction
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) (hu : u ≠ 0) :
    quotientFunction N u = MaassQuotientL2.sourceFunction N (toMaassCuspEigenform N u hu) := by
  rfl

/-- Every zero-inclusive principal eigenspace vector is square-integrable on the actual quotient. -/
theorem quotientFunction_memLp
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    MemLp (quotientFunction N u) 2 (MaassQuotientL2.quotientMeasure N) := by
  by_cases hu : u = 0
  · subst u
    have hzero : quotientFunction N (0 : glMaassCuspEigenspace (principalCongruenceGL N) lam) = 0 := by
      funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rfl
    rw [hzero]
    exact MemLp.zero
  · rw [quotientFunction_eq_sourceFunction N u hu]
    exact MaassQuotientL2.sourceFunction_memLp N (toMaassCuspEigenform N u hu)

/-- Quotient `L²` representative of a zero-inclusive principal Maass eigenspace vector. -/
def toLp
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) :=
  (quotientFunction_memLp N u).toLp (quotientFunction N u)

/-- The quotient `L²` representative has its literal quotient function as AE representative. -/
theorem toLp_ae
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    toLp N u =ᵐ[MaassQuotientL2.quotientMeasure N] quotientFunction N u :=
  (quotientFunction_memLp N u).coeFn_toLp

theorem quotientFunction_add
    (u v : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    quotientFunction N (u + v) = quotientFunction N u + quotientFunction N v := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

theorem quotientFunction_smul
    (c : ℂ) (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    quotientFunction N (c • u) = c • quotientFunction N u := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

/-- Smoothness of a zero-inclusive principal GL Maass eigenspace vector. -/
theorem function_continuous
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) : Continuous u.1 := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (u.2.2.1.1.continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_def, ofComplex_apply] using h

/-- The literal quotient function is continuous. -/
theorem quotientFunction_continuous
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    Continuous (quotientFunction N u) :=
  ((function_continuous N u).comp (continuous_inv.smul continuous_const)).quotient_lift _

/-- The quotient function recovers the original upper-half-plane function on its standard section. -/
theorem quotientFunction_section
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) (z : ℍ) :
    quotientFunction N u (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹) = u.1 z := by
  simp only [quotientFunction, maassInvariantQuotientLift_section, toMaassInvariant]

/-- The principal GL eigenspace maps linearly to its genuine quotient `L²` realization. -/
noncomputable def toLpLinear :
    glMaassCuspEigenspace (principalCongruenceGL N) lam →ₗ[ℂ]
      Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) where
  toFun := toLp N
  map_add' u v := by
    apply Lp.ext
    filter_upwards [toLp_ae N (u + v), toLp_ae N u, toLp_ae N v,
      Lp.coeFn_add (toLp N u) (toLp N v)] with q huv hu hv hadd
    rw [huv, hadd]
    change quotientFunction N (u + v) q = (toLp N u) q + (toLp N v) q
    rw [hu, hv, quotientFunction_add]
    rfl
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [toLp_ae N (c • u), toLp_ae N u,
      Lp.coeFn_smul c (toLp N u)] with q hcu hu hsmul
    rw [hcu]
    change quotientFunction N (c • u) q = (c • toLp N u) q
    rw [hsmul]
    change quotientFunction N (c • u) q = c • (toLp N u) q
    rw [hu, quotientFunction_smul]
    rfl

/-- The literal source enters the quotient realization as the existing Maass `L²` vector. -/
theorem quotientFunction_principalMaassCuspEigenform
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    quotientFunction N (principalMaassCuspEigenformToHeckeEigenspace N lam f) =
      MaassQuotientL2.sourceFunction N f := by
  rfl

/-- The canonical linear quotient realization sends the literal Maass source to its known `L²`
vector. -/
theorem toLpLinear_principalMaassCuspEigenform
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    toLpLinear N (principalMaassCuspEigenformToHeckeEigenspace N lam f) =
      MaassQuotientL2.sourceLp N f := by
  change toLp N (principalMaassCuspEigenformToHeckeEigenspace N lam f) =
    MaassQuotientL2.sourceLp N f
  apply Lp.ext
  filter_upwards [toLp_ae N (principalMaassCuspEigenformToHeckeEigenspace N lam f),
    MaassQuotientL2.sourceLp_ae N f] with q hto hsource
  rw [hto, hsource, quotientFunction_principalMaassCuspEigenform]

/-- Equality of quotient `L²` realizations recovers the zero-inclusive principal Maass
 eigenspace vector pointwise. -/
theorem toLpLinear_injective : Function.Injective (toLpLinear N (lam := lam)) := by
  intro u v huv
  change toLp N u = toLp N v at huv
  have hae : quotientFunction N u =ᵐ[MaassQuotientL2.quotientMeasure N]
      quotientFunction N v :=
    (toLp_ae N u).symm.trans (huv ▸ toLp_ae N v)
  have hfun := Measure.eq_of_ae_eq hae (quotientFunction_continuous N u)
    (quotientFunction_continuous N v)
  apply Subtype.ext
  funext z
  simpa only [quotientFunction_section] using
    congrFun hfun (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹)

end PrincipalMaassEigenspaceL2

end

end GaloisForLFunctions.RHTower
