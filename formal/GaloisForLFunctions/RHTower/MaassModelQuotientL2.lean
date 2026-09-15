import GaloisForLFunctions.RHTower.MaassLadderQuotientL2
import GaloisForLFunctions.RHTower.MaassModelIntertwiner
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# The finite Maass model inside the actual quotient Hilbert space

All normalized model coefficients are bounded continuous quotient functions.
The canonical map to L2 preserves injectivity because the actual quotient
measure has full support. Evaluation identifies the literal Maass representative.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction
namespace GaloisForLFunctions.RHTower.MaassModelQuotientL2
open MaassSmooth MaassCircle
noncomputable section
variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam.1)

theorem modelSource_bounded (m : ℤ) : ∃ C : ℝ, ∀ z : ℍ, ‖modelSource lam f m z‖ ≤ C := by
  have h : modelSource lam f m ∈ boundedEulerSpace := by
    cases m with
    | ofNat n =>
        exact boundedEulerSpace.smul_mem ((ladderScale lam n)⁻¹)
          (ladders_all_euler_words_bounded N lam.2.1 f n).1
    | negSucc n =>
        exact boundedEulerSpace.smul_mem ((ladderScale lam (n+1))⁻¹)
          (ladders_all_euler_words_bounded N lam.2.1 f (n+1)).2
  exact h []

def modelFunction (m : ℤ) := automorphicQuotientLift (modelVector lam f m)

theorem modelFunction_continuous (m : ℤ) : Continuous (modelFunction N lam f m) := by
  apply automorphicQuotientLift_continuous
  have he : (modelVector lam f m).1 = weightLift m (modelSource lam f m) :=
    funext (modelVector_apply lam f m)
  rw [he]
  exact weightLift_continuous _ _

theorem modelFunction_bounded (m : ℤ) :
    ∃ C : ℝ, ∀ q, ‖modelFunction N lam f m q‖ ≤ C := by
  obtain ⟨C,hC⟩ := modelSource_bounded N lam f m
  refine ⟨C, fun q => ?_⟩
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
  change ‖(modelVector lam f m).1 g⁻¹‖ ≤ C
  rw [modelVector_apply, weightLift_norm]
  exact hC _

/-- Each normalized actual Maass coefficient is bounded and continuous on the quotient. -/
def modelBounded (m : ℤ) :
    (SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N+1))) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (modelFunction N lam f m)
    (modelFunction_continuous N lam f m) (modelFunction_bounded N lam f m).choose
    (modelFunction_bounded N lam f m).choose_spec

/-- The finite differential model realized by actual bounded quotient functions. -/
def modelToBounded : SphericalKFiniteModel →ₗ[ℂ]
    ((SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N+1))) →ᵇ ℂ) :=
  Finsupp.linearCombination ℂ (modelBounded N lam f)

theorem modelToBounded_apply (v : SphericalKFiniteModel) (g : SL2R) :
    modelToBounded N lam f v (QuotientGroup.mk g) = (modelToMaass lam f v).1 g⁻¹ := by
  induction v using Finsupp.induction_linear with
  | zero => rfl
  | add v w hv hw => simpa only [map_add, BoundedContinuousFunction.add_apply, AddMemClass.coe_add, Pi.add_apply] using congrArg₂ (·+·) hv hw
  | single m c =>
      rw [modelToBounded, Finsupp.linearCombination_single, modelToMaass_single]
      rfl

theorem modelToBounded_injective : Function.Injective (modelToBounded N lam f) := by
  intro v w h
  apply modelToMaass_injective lam f
  apply Subtype.ext
  funext g
  have he := congrArg (fun F => F (QuotientGroup.mk g⁻¹)) h
  simpa only [modelToBounded_apply, inv_inv] using he

/-- The finite spherical model realized inside the actual quotient Hilbert space. -/
def modelToLp : SphericalKFiniteModel →ₗ[ℂ] Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) :=
  (BoundedContinuousFunction.toLp 2 (MaassQuotientL2.quotientMeasure N) ℂ).toLinearMap.comp
    (modelToBounded N lam f)

theorem modelToLp_ae (v : SphericalKFiniteModel) :
    modelToLp N lam f v =ᵐ[MaassQuotientL2.quotientMeasure N] modelToBounded N lam f v :=
  BoundedContinuousFunction.coeFn_toLp 2 (MaassQuotientL2.quotientMeasure N) ℂ _

/-- The zero `K`-type in the finite model is the original Maass vector in quotient `L²`. -/
theorem modelToLp_spherical :
    modelToLp N lam f (Finsupp.single 0 1) = MaassQuotientL2.sourceLp N f := by
  apply Lp.ext
  filter_upwards [modelToLp_ae N lam f (Finsupp.single 0 1),
    MaassQuotientL2.sourceLp_ae N f] with q hmodel hsource
  rw [hmodel, hsource]
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [modelToBounded_apply]
  simpa only [MaassQuotientL2.sourceFunction, maassInvariantQuotientLift_mk] using
    modelToMaass_spherical lam f g⁻¹

/-- Passing the whole finite model to almost-everywhere classes preserves injectivity. -/
theorem modelToLp_injective : Function.Injective (modelToLp N lam f) :=
  (BoundedContinuousFunction.toLp_injective (p := 2)
    (μ := MaassQuotientL2.quotientMeasure N) (𝕜 := ℂ)).comp (modelToBounded_injective N lam f)

end
end GaloisForLFunctions.RHTower.MaassModelQuotientL2
