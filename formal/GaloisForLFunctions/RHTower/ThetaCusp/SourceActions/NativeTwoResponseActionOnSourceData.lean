import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWNativeTwoResponseAction

/-!
# The native action as a functional of source data

The action uses source functions and full/native event kernels directly.
Responses are the literal source integrals. There are no spectral indices or
analytic proof fields in these data. The actual theta sources retain their
proved absolute admission, contact identity and exhaustion limit.
-/

open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace RHTower.D4BMPWSourceAction
open D4BMModularCore D4BMJointSource D4BMFullAngularCausalPeierls
open D4BMGlobalAngularResponse D4BMFullAngularReconstruction D4BMNativeCircle
open D4BMGeneralTemporalTransposition
open D4BMPWRetardedWeakNative hiding Event
open D4BMPWTwoResponseAction D4BMPWTwoResponseActionLimit D4BMPWNativeTwoResponseAction

/-- Coefficients and literal kernels of two source legs; no admission laws are fields. -/
structure NativeActionSourceData where
  parameter : ℂ
  contact : ℂ
  fullKernel : Event → Event → ℂ
  nativeKernel : Event → Event → ℂ
  source : Bool → ℂ → Event → ℂ

/-- A response is constructed by integration against the full source kernel. -/
def sourceResponse (S : NativeActionSourceData) (b : Bool) (a : ℂ) (r : Event) : ℂ :=
  ∫ p : Event, S.fullKernel r p * S.source b a p ∂eventMeasure

def sourceResponseTest (S : NativeActionSourceData) (chi : Event → ℝ)
    (b : Bool) (a : ℂ) (r : Event) : ℂ :=
  (chi r : ℂ) * sourceResponse S b a r

/-- The original native correction, including its target weight and causal kernel. -/
def sourceNativeBulk (S : NativeActionSourceData) (b : Bool) (a : ℂ)
    (phi : Event → ℂ) (p : Event) : ℂ :=
  ∫ r : Event, S.source b a p * S.parameter * S.nativeKernel r p /
    (Real.cosh r.2 : ℂ) ^ (2 : ℕ) * phi r

/-- Wave-minus-native action, defined entirely from source data. -/
def nativeSourceAction (S : NativeActionSourceData) (chi : Event → ℝ)
    (b c : Bool) (a d : ℂ) : ℂ :=
  ((∫ p : Event, sourceResponse S b a p * eventWave (sourceResponseTest S chi c d) p) -
    (∫ p : Event, sourceResponse S c d p * eventWave (sourceResponseTest S chi b a) p)) -
  ((∫ p : Event, sourceNativeBulk S b a (sourceResponseTest S chi c d) p ∂eventMeasure) -
    (∫ p : Event, sourceNativeBulk S c d (sourceResponseTest S chi b a) p ∂eventMeasure))

/-- The source contact uses only the two retarded source-response pairings. -/
def sourceContact (S : NativeActionSourceData) (b c : Bool) (a d : ℂ) : ℂ :=
  S.contact * ((∫ p : Event, S.source b a p * sourceResponse S c d p ∂eventMeasure) -
    ∫ p : Event, S.source c d p * sourceResponse S b a p ∂eventMeasure)

theorem nativeSourceAction_skew (S : NativeActionSourceData) (chi : Event → ℝ)
    (b c : Bool) (a d : ℂ) :
    nativeSourceAction S chi b c a d = -nativeSourceAction S chi c b d a := by
  unfold nativeSourceAction
  ring

@[simp] theorem nativeSourceAction_self (S : NativeActionSourceData) (chi : Event → ℝ)
    (b : Bool) (a : ℂ) : nativeSourceAction S chi b b a a = 0 := by
  simp only [nativeSourceAction, sub_self]

/-- Actual theta data are mapped into the source domain without retaining an occurrence index. -/
def thetaSourceData (q : XiZeroCopy) (branch : Bool) (X k : ℝ) : NativeActionSourceData where
  parameter := D4BMGlobalAngularResponse.parameter q branch
  contact := fullAngularField q branch ![X, Real.exp k]
  fullKernel r p := angularDirichletKernel q branch (r.1 - p.1) r.2 p.2 X k
  nativeKernel r p := nativeDirichletCausalKernel q (r.1 - p.1) r.2 p.2 X k
  source b a p := timeReducedCoefficient (physicalRate q b) a p.1 p.2

theorem sourceResponse_theta (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (p : Event) :
    sourceResponse (thetaSourceData q branch X k) b a p =
      fullRetardedResponse q branch b a p.1 p.2 X k := rfl

/-- The literal original native action factors exactly through the source data. -/
theorem nativeSourceAction_theta (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (chi : Event → ℝ) :
    nativeSourceAction (thetaSourceData q branch X k) chi b c a d =
      nativeTwoResponseAction chi q branch b c a d X k := rfl

theorem sourceContact_theta (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    sourceContact (thetaSourceData q branch X k) b c a d =
      fullAngularField q branch ![X, Real.exp k] *
        fullCausalSourcePair q branch b c a d X k := by
  rw [fullCausalSourcePair_eq_retarded_skew]
  rfl

/-- Equal source data give equal actions at every cutoff, regardless of spectral labelling. -/
theorem nativeTwoResponseAction_eq_of_sourceData_eq
    (q q' : XiZeroCopy) (branch branch' : Bool) (X k X' k' : ℝ)
    (h : thetaSourceData q branch X k = thetaSourceData q' branch' X' k')
    (chi : Event → ℝ) (b c : Bool) (a d : ℂ) :
    nativeTwoResponseAction chi q branch b c a d X k =
      nativeTwoResponseAction chi q' branch' b c a d X' k' := by
  rw [← nativeSourceAction_theta, ← nativeSourceAction_theta, h]

/-- Every term of the concrete source-data action is absolutely admitted. -/
theorem thetaSourceData_action_admitted (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (X k : ℝ) (n : ℕ) :
    let S := thetaSourceData q branch X k
    Integrable (fun p : Event => sourceResponse S true a p *
      eventWave (sourceResponseTest S (wedgeWindow n) false d) p) ∧
    Integrable (fun p : Event => sourceResponse S false d p *
      eventWave (sourceResponseTest S (wedgeWindow n) true a) p) ∧
    Integrable (sourceNativeBulk S true a (sourceResponseTest S (wedgeWindow n) false d))
      eventMeasure ∧
    Integrable (sourceNativeBulk S false d (sourceResponseTest S (wedgeWindow n) true a))
      eventMeasure :=
  complementary_native_action_admitted q branch a d X k n

/-- The admitted action has its exact cutoff contact expressed entirely in source data. -/
theorem thetaSourceData_action_eq_contact (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (n : ℕ) :
    let S := thetaSourceData q branch X k
    nativeSourceAction S (wedgeWindow n) b c a d =
      S.contact * ((∫ p : Event, S.source b a p *
        sourceResponseTest S (wedgeWindow n) c d p ∂eventMeasure) -
        ∫ p : Event, S.source c d p *
          sourceResponseTest S (wedgeWindow n) b a p ∂eventMeasure) := by
  dsimp only
  rw [nativeSourceAction_theta, nativeTwoResponseAction_eq _ (wedgeWindow_smooth n)
    (wedgeWindow_compact n) (wedgeWindow_support n),
    twoResponseAction_eq_contact _ (wedgeWindow_smooth n) (wedgeWindow_compact n)
      (wedgeWindow_support n)]
  rfl

/-- Exhausting the physical wedge gives the actual source contact, with no new analytic input. -/
theorem thetaSourceData_action_tendsto (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => nativeSourceAction (thetaSourceData q branch X k)
      (wedgeWindow n) true false a d) atTop
      (𝓝 (sourceContact (thetaSourceData q branch X k) true false a d)) := by
  simp only [nativeSourceAction_theta, sourceContact_theta]
  exact complementary_native_action_tendsto q branch a d X k

end RHTower.D4BMPWSourceAction

#print axioms RHTower.D4BMPWSourceAction.nativeSourceAction_theta
#print axioms RHTower.D4BMPWSourceAction.thetaSourceData_action_admitted
#print axioms RHTower.D4BMPWSourceAction.thetaSourceData_action_eq_contact
#print axioms RHTower.D4BMPWSourceAction.thetaSourceData_action_tendsto
