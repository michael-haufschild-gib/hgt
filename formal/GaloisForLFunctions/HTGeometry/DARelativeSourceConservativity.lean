import GaloisForLFunctions.HTGeometry.JointSourceRealizationConservativity
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.GammaPointedSourceNonEffectivity

/-!
# Differential-algebraic-relative source conservativity

Exact reconstruction of a primitive is stronger than reconstruction of its
differential-algebraic gauge class.  This module separates the two gates.

For a linear source fingerprint and a submodule `D` of gauges already invisible to every
source and reporter channel, the descended fingerprint on `K ⧸ D` is injective exactly when
every jointly fixed, jointly invisible gauge belongs to `D`.  When every member of `D` is
differentially algebraic, equality of fingerprints therefore determines the HT/DA phase even
when it does not determine the primitive.

The final exponential control proves that pointed source non-effectivity is not specific to
hypertranscendence: two distinct differentially algebraic exponentials obey the same source
recurrence and pointing.  Thus the source-gauge kernel is kinematics; the HT-relevant object is
its quotient by differentially algebraic gauge.
-/

open Function

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- The complete source boundary and a labelled family of linear reporters, as one linear map. -/
def CommutingDifferenceDifferentialField.familyRealizedBoundaryLinearMap
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) : K →ₗ[C] (ι → K) × (ρ → A) where
  toFun x := (fun i => S.defect i x, fun r => realization r x)
  map_add' x y := by
    apply Prod.ext
    · funext i
      exact S.defect_add i x y
    · funext r
      exact (realization r).map_add x y
  map_smul' c x := by
    apply Prod.ext
    · funext i
      simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
      simp only [CommutingDifferenceDifferentialField.defect, Algebra.smul_def]
      rw [map_mul, S.aut_algebraMap]
      ring
    · funext r
      exact (realization r).map_smul c x

@[simp]
theorem CommutingDifferenceDifferentialField.familyRealizedBoundaryLinearMap_apply
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) (x : K) :
    S.familyRealizedBoundaryLinearMap realization x =
      S.familyRealizedBoundaryFingerprint
        (fun r => (realization r).toAddMonoidHom) x :=
  rfl

/-- The kernel of the linear fingerprint is exactly the jointly fixed gauge invisible to every
reporter. -/
theorem CommutingDifferenceDifferentialField.mem_ker_familyRealizedBoundaryLinearMap_iff
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) (z : K) :
    z ∈ (S.familyRealizedBoundaryLinearMap realization).ker ↔
      JointFixed S z ∧ ∀ r, realization r z = 0 := by
  rw [LinearMap.mem_ker]
  have h := S.familyRealizedBoundaryFingerprint_eq_iff
    (fun r => (realization r).toAddMonoidHom) z 0
  have hzero :
      S.familyRealizedBoundaryFingerprint
          (fun r => (realization r).toAddMonoidHom) 0 = 0 := by
    apply Prod.ext
    · funext i
      simp [familyRealizedBoundaryFingerprint, boundaryFingerprint,
        CommutingDifferenceDifferentialField.defect]
    · funext r
      simp [familyRealizedBoundaryFingerprint]
  rw [← hzero]
  simpa [familyRealizedBoundaryLinearMap] using! h

/-- Descend the complete source/reporter fingerprint through a prescribed invisible gauge
submodule. -/
def CommutingDifferenceDifferentialField.quotientFamilyRealizedBoundaryLinearMap
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) (D : Submodule C K)
    (hD : D ≤ (S.familyRealizedBoundaryLinearMap realization).ker) :
    (K ⧸ D) →ₗ[C] (ι → K) × (ρ → A) :=
  D.liftQ (S.familyRealizedBoundaryLinearMap realization) hD

@[simp]
theorem CommutingDifferenceDifferentialField.quotientFamilyRealizedBoundaryLinearMap_mkQ
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) (D : Submodule C K)
    (hD : D ≤ (S.familyRealizedBoundaryLinearMap realization).ker) (x : K) :
    S.quotientFamilyRealizedBoundaryLinearMap realization D hD (D.mkQ x) =
      S.familyRealizedBoundaryLinearMap realization x := by
  exact LinearMap.congr_fun (Submodule.liftQ_mkQ D
    (S.familyRealizedBoundaryLinearMap realization) hD) x

/-- A linear fingerprint descended through `D` is injective exactly when its original kernel is
already contained in `D`.  Together with the descent hypothesis, this says `D` is the exact
forgotten gauge. -/
theorem CommutingDifferenceDifferentialField.quotientFamilyRealizedBoundaryLinearMap_injective_iff
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) (D : Submodule C K)
    (hD : D ≤ (S.familyRealizedBoundaryLinearMap realization).ker) :
    Function.Injective
        (S.quotientFamilyRealizedBoundaryLinearMap realization D hD) ↔
      (S.familyRealizedBoundaryLinearMap realization).ker ≤ D := by
  constructor
  · intro hinjective z hz
    have hzero :
        S.quotientFamilyRealizedBoundaryLinearMap realization D hD (D.mkQ z) = 0 := by
      rw [S.quotientFamilyRealizedBoundaryLinearMap_mkQ]
      exact hz
    have hclass : D.mkQ z = 0 := hinjective (by simpa using hzero)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hclass
    exact hclass
  · intro hkernel
    rw [← LinearMap.ker_eq_bot]
    rw [eq_bot_iff]
    intro q hq
    induction q using Quotient.inductionOn with
    | _ z =>
        have hzker : z ∈ (S.familyRealizedBoundaryLinearMap realization).ker := by
          rw [LinearMap.mem_ker]
          simpa using! hq
        exact Submodule.Quotient.mk_eq_zero D |>.2 (hkernel hzker)

/-- **DA-relative joint conservativity.**  The descended observation reconstructs classes modulo
`D` exactly when every jointly fixed gauge invisible to every reporter lies in `D`. -/
theorem CommutingDifferenceDifferentialField.quotientFamilyRealizedBoundaryLinearMap_injective_iff_jointFixed
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) (D : Submodule C K)
    (hD : D ≤ (S.familyRealizedBoundaryLinearMap realization).ker) :
    Function.Injective
        (S.quotientFamilyRealizedBoundaryLinearMap realization D hD) ↔
      ∀ z, JointFixed S z → (∀ r, realization r z = 0) → z ∈ D := by
  rw [S.quotientFamilyRealizedBoundaryLinearMap_injective_iff]
  constructor
  · intro h z hfixed hinvisible
    apply h
    exact (S.mem_ker_familyRealizedBoundaryLinearMap_iff realization z).2
      ⟨hfixed, hinvisible⟩
  · intro h z hz
    obtain ⟨hfixed, hinvisible⟩ :=
      (S.mem_ker_familyRealizedBoundaryLinearMap_iff realization z).1 hz
    exact h z hfixed hinvisible

/-- Hypertranscendence is constant on every additive gauge class whose differences are
differentially algebraic. -/
theorem hypertranscendentalOver_iff_of_sub_mem_daGauge
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (D : Submodule F E)
    (hDda : ∀ d, d ∈ D → DifferentialAlgebraicOver F d)
    {x y : E} (hxy : x - y ∈ D) :
    HypertranscendentalOver F x ↔ HypertranscendentalOver F y := by
  have hd : DifferentialAlgebraicOver F (x - y) := hDda (x - y) hxy
  have h := hypertranscendentalOver_add_differentialAlgebraic_iff
    (x := y) hd
  have hsum : y + (x - y) = x := by abel
  simpa only [hsum] using h

/-- **Positive successor to pointed-source non-effectivity.**  If the common invisible source
gauge is only differentially algebraic modulo `D`, then the observation may fail to reconstruct
the primitive but still reconstructs its exact HT/DA phase. -/
theorem CommutingDifferenceDifferentialField.fingerprint_determines_hypertranscendence_mod_daGauge
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [AddCommGroup A] [Module C A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (realization : ρ → K →ₗ[C] A) (D : Submodule C K)
    (hDda : ∀ d, d ∈ D → DifferentialAlgebraicOver C d)
    (hseparates : ∀ z, JointFixed S z → (∀ r, realization r z = 0) → z ∈ D)
    {x y : K}
    (hobs : S.familyRealizedBoundaryLinearMap realization x =
      S.familyRealizedBoundaryLinearMap realization y) :
    HypertranscendentalOver C x ↔ HypertranscendentalOver C y := by
  have hkernel : JointFixed S (x - y) ∧ ∀ r, realization r (x - y) = 0 := by
    have h := S.familyRealizedBoundaryFingerprint_eq_iff
      (fun r => (realization r).toAddMonoidHom) x y
    apply h.mp
    exact hobs
  exact hypertranscendentalOver_iff_of_sub_mem_daGauge D hDda
    (hseparates (x - y) hkernel.1 hkernel.2)

/-! ## Differentially algebraic control: source non-effectivity is not HT-specific -/

namespace HTGeometry

/-- Elementary exponential source representative. -/
def daPointedExponential (z : ℂ) : ℂ :=
  Complex.exp z

/-- A distinct period-one gauge twist of the same elementary source representative. -/
def daPointedExponentialTwist (z : ℂ) : ℂ :=
  gammaPeriodicMode 1 z * Complex.exp z

/-- Both elementary representatives obey the same multiplicative unit-shift source law. -/
theorem daPointedExponential_source_collision (z : ℂ) :
    daPointedExponential (z + 1) = Complex.exp 1 * daPointedExponential z ∧
    daPointedExponentialTwist (z + 1) =
      Complex.exp 1 * daPointedExponentialTwist z := by
  constructor
  · simp [daPointedExponential, Complex.exp_add, mul_comm]
  · rw [daPointedExponentialTwist, gammaPeriodicMode_add_one,
      Complex.exp_add, daPointedExponentialTwist]
    ring

/-- The source collision survives the regular pointing at `1`. -/
theorem daPointedExponentialTwist_one :
    daPointedExponentialTwist 1 = daPointedExponential 1 := by
  simp [daPointedExponentialTwist, daPointedExponential,
    gammaPeriodicMode, gammaPeriodicFrequency]

/-- The two pointed elementary source representatives are nevertheless distinct. -/
theorem daPointedExponentialTwist_ne :
    daPointedExponentialTwist ≠ daPointedExponential := by
  intro h
  have hhalf := congrFun h (1 / 2)
  rw [daPointedExponentialTwist, gammaPeriodicMode_one_half, neg_one_mul,
    daPointedExponential] at hhalf
  exact Complex.exp_ne_zero (1 / 2) (neg_eq_self.mp hhalf)

/-- The untwisted elementary representative is differentially algebraic. -/
theorem differentiallyAlgebraic_daPointedExponential :
    DifferentiallyAlgebraic daPointedExponential := by
  simpa [daPointedExponential] using! differentiallyAlgebraic_exp

/-- The periodically twisted elementary representative is also differentially algebraic. -/
theorem differentiallyAlgebraic_daPointedExponentialTwist :
    DifferentiallyAlgebraic daPointedExponentialTwist := by
  have h := differentiallyAlgebraic_cexp_linear (1 + gammaPeriodicFrequency 1)
  convert h using 1
  funext z
  rw [daPointedExponentialTwist, gammaPeriodicMode]
  rw [← Complex.exp_add]
  congr 1
  ring

end HTGeometry

end

end GaloisForLFunctions
