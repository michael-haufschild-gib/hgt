import GaloisForLFunctions.RHTower.MaassLadderDerivativeBounds
import GaloisForLFunctions.RHTower.MaassAutomorphicDifferentialLadder
import GaloisForLFunctions.RHTower.MaassQuotientL2

/-!
# All Maass ladder vectors in the actual quotient Hilbert space

Inversion descends each literal automorphic ladder to G/Gamma. Its compact
character has norm one, so the proved global ladder bound and finite covolume
give L2 admission at every order.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.RHTower
open MaassSmooth MaassCircle
noncomputable section

/-- Inversion sends a literal left-automorphic function to the right-coset quotient. -/
def automorphicQuotientLift {Γ : Subgroup SL2R} (F : automorphicFunctionSpace Γ) :
    SL2R ⧸ Γ → ℂ :=
  Quotient.lift (fun g : SL2R => F.1 g⁻¹) (by
    intro a b hab
    have h := F.2 ⟨a⁻¹*b, QuotientGroup.leftRel_apply.mp hab⟩ b⁻¹
    simpa only [mul_inv_cancel_right] using h)

theorem automorphicQuotientLift_continuous {Γ : Subgroup SL2R}
    (F : automorphicFunctionSpace Γ) (hF : Continuous F.1) :
    Continuous (automorphicQuotientLift F) :=
  (hF.comp continuous_inv).quotient_lift _

theorem smoothSource_continuous (f : FunctionSpace) : Continuous (f : ℍ → ℂ) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  simpa only [Function.comp_def, ofComplex_apply] using
    (regularAt f z).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt

theorem realSphericalKPhase_continuous : Continuous realSphericalKPhase := by
  unfold realSphericalKPhase
  fun_prop

theorem realSphericalKTypeCharacter_norm (m : ℤ) (k : upperHalfPlaneStabilizer) :
    ‖realSphericalKTypeCharacter m k‖ = 1 := by
  rw [realSphericalKTypeCharacter_apply, norm_zpow, Complex.norm_def,
    realSphericalKPhase_normSq, Real.sqrt_one, one_zpow]

theorem weightLift_continuous (m : ℤ) (f : FunctionSpace) : Continuous (weightLift m f) := by
  have hk : Continuous realIwasawaK := realIwasawaHomeomorph.continuous.snd
  have hc : Continuous (fun k => realSphericalKTypeCharacter m k) :=
    realSphericalKPhase_continuous.zpow₀ (2*m) (fun k => Or.inl (realSphericalKPhase_ne_zero k))
  exact ((smoothSource_continuous f).comp (continuous_id.smul continuous_const)).mul (hc.comp hk)

theorem weightLift_norm (m : ℤ) (f : FunctionSpace) (g : SL2R) :
    ‖weightLift m f g‖ = ‖f (g • UpperHalfPlane.I)‖ := by
  rw [weightLift, norm_mul, realSphericalKTypeCharacter_norm, mul_one]

namespace MaassLadderQuotientL2
variable (N : ℕ) {lam : ℝ} (hlam : 0 < lam)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

def raisedFunction (n : ℕ) := automorphicQuotientLift (raisedAutomorphic f n)
def loweredFunction (n : ℕ) := automorphicQuotientLift (loweredAutomorphic f n)

theorem raisedFunction_continuous (n : ℕ) : Continuous (raisedFunction N f n) :=
  automorphicQuotientLift_continuous _ (weightLift_continuous _ _)

theorem loweredFunction_continuous (n : ℕ) : Continuous (loweredFunction N f n) :=
  automorphicQuotientLift_continuous _ (weightLift_continuous _ _)

include hlam in
/-- Every actual raised automorphic vector belongs to the genuine quotient Hilbert space. -/
theorem raisedFunction_memLp (n : ℕ) :
    MemLp (raisedFunction N f n) 2 (MaassQuotientL2.quotientMeasure N) := by
  obtain ⟨C,hC⟩ := (ladders_all_euler_words_bounded N hlam f n).1 []
  apply MemLp.of_bound (raisedFunction_continuous N f n).aestronglyMeasurable C
  apply ae_of_all
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
  change ‖weightLift (n : ℤ) (raised (ofMaass f) n) g⁻¹‖ ≤ C
  rw [weightLift_norm]
  exact hC (g⁻¹ • UpperHalfPlane.I)

include hlam in
/-- Every actual lowered automorphic vector belongs to the genuine quotient Hilbert space. -/
theorem loweredFunction_memLp (n : ℕ) :
    MemLp (loweredFunction N f n) 2 (MaassQuotientL2.quotientMeasure N) := by
  obtain ⟨C,hC⟩ := (ladders_all_euler_words_bounded N hlam f n).2 []
  apply MemLp.of_bound (loweredFunction_continuous N f n).aestronglyMeasurable C
  apply ae_of_all
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
  change ‖weightLift (-(n : ℤ)) (lowered (ofMaass f) n) g⁻¹‖ ≤ C
  rw [weightLift_norm]
  exact hC (g⁻¹ • UpperHalfPlane.I)

def raisedLp (n : ℕ) : Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) :=
  (raisedFunction_memLp N hlam f n).toLp (raisedFunction N f n)

def loweredLp (n : ℕ) : Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) :=
  (loweredFunction_memLp N hlam f n).toLp (loweredFunction N f n)

theorem raisedLp_ae (n : ℕ) : raisedLp N hlam f n =ᵐ[MaassQuotientL2.quotientMeasure N]
    raisedFunction N f n := (raisedFunction_memLp N hlam f n).coeFn_toLp

theorem loweredLp_ae (n : ℕ) : loweredLp N hlam f n =ᵐ[MaassQuotientL2.quotientMeasure N]
    loweredFunction N f n := (loweredFunction_memLp N hlam f n).coeFn_toLp

end MaassLadderQuotientL2
end
end GaloisForLFunctions.RHTower
