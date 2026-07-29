import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison

/-!
# Involutive-clock dephasing is static observable erasure

Relational quantum-clock models produce double-commutator decoherence terms.  For a two-reading
clock the algebraic content of that term is already present in the observer conditional
expectation: if `U ^ 2 = 1`, then

`[U,[U,X]] = 4 * (X - E_U(X))`,

where `E_U` is the two-element observable twirl.  Thus the dephasing generator measures the
part of the observable that the clock cannot resolve; it does not require a temporal evolution.

The zero criterion below needs only involutivity.  In particular it removes the unitarity and
self-adjointness hypotheses used by the existing Kadison-defect criterion.

Physics provenance: R. Gambini, R. A. Porto, and J. Pullin, *A relational solution to the
problem of time in quantum mechanics and quantum gravity induces a fundamental mechanism for
quantum decoherence*, New J. Phys. 6 (2004), arXiv:gr-qc/0402118, equations (40)--(42).
-/

namespace HTGeometry

noncomputable section

variable {k E : Type*} [RCLike k]
  [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]

/-- The clock double commutator `[U,[U,X]]`.  This is the dissipative operator appearing in
relational-clock Lindblad terms when the clock observable is an involution. -/
def finiteInvolutiveClockDoubleCommutator
    (U X : E →L[k] E) : E →L[k] E :=
  U * (U * X - X * U) - (U * X - X * U) * U

omit [CompleteSpace E] in
/-- **Relational-clock dephasing/observability identity.**  For an involutive clock, its double
commutator is four times the observable component erased by the two-reading conditional
expectation.  The identity is operator-valued and assumes no state, Hamiltonian, positivity,
unitarity, or self-adjointness. -/
theorem finiteInvolutiveClockDoubleCommutator_eq_four_smul_disturbance
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) :
    finiteInvolutiveClockDoubleCommutator U X =
      (4 : k) • (X - finiteCyclicObservableTwirl U X 2) := by
  have hUU : U * U = 1 := by
    simpa only [pow_two] using hsq
  calc
    finiteInvolutiveClockDoubleCommutator U X =
        (X - U * (X * U)) + (X - U * (X * U)) := by
      rw [finiteInvolutiveClockDoubleCommutator, mul_sub, sub_mul,
        ← mul_assoc U U X, hUU, one_mul, mul_assoc X U U, hUU, mul_one]
      noncomm_ring
    _ = (4 : k) • (X - finiteCyclicObservableTwirl U X 2) := by
      rw [finiteInvolutiveObservableTwirl_eq_symmetrizer U X hsq,
        mul_assoc U X U]
      module

omit [CompleteSpace E] in
/-- On a clock-fixed state the double commutator is twice the ordinary clock--observable
commutator.  This is the state-value conversion used to compare dephasing strength with quantum
Fisher information. -/
theorem finiteInvolutiveClockDoubleCommutator_apply_of_fixed
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) {ψ : E} (hψ : U ψ = ψ) :
    finiteInvolutiveClockDoubleCommutator U X ψ =
      (2 : k) • ((X * U - U * X) ψ) := by
  rw [finiteInvolutiveClockDoubleCommutator_eq_four_smul_disturbance U X hsq,
    _root_.smul_apply,
    sub_finiteInvolutiveObservableTwirl_eq_half_commutator_mul U X hsq,
    _root_.smul_apply, mul_apply_eq_comp, hψ]
  module

omit [CompleteSpace E] in
/-- Twirl-fixed observables are exactly the clock commutant.  Unlike the corresponding
Kadison-defect theorem, this exact conditional-expectation criterion needs neither unitarity
of the clock nor self-adjointness of the observable. -/
theorem sub_finiteInvolutiveObservableTwirl_eq_zero_iff_commutes
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) :
    X - finiteCyclicObservableTwirl U X 2 = 0 ↔ U * X = X * U := by
  constructor
  · intro hzero
    have hfixed : X = finiteCyclicObservableTwirl U X 2 := sub_eq_zero.mp hzero
    calc
      U * X = U * finiteCyclicObservableTwirl U X 2 :=
        congrArg (fun Y => U * Y) hfixed
      _ = finiteCyclicObservableTwirl U X 2 * U :=
        finiteCyclicObservableTwirl_commutes U X 2 hsq
      _ = X * U := congrArg (fun Y => Y * U) hfixed.symm
  · intro hcomm
    rw [finiteCyclicObservableTwirl_eq_self_of_commutes
      U X 2 (by norm_num) hsq hcomm, sub_self]

omit [CompleteSpace E] in
/-- **Hypothesis-free dephasing detector.**  For an involutive clock, vanishing of the
relational-clock double commutator is equivalent to belonging to the observable commutant.
No self-adjointness or unitary/isometric premise remains. -/
theorem finiteInvolutiveClockDoubleCommutator_eq_zero_iff_commutes
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) :
    finiteInvolutiveClockDoubleCommutator U X = 0 ↔ U * X = X * U := by
  rw [finiteInvolutiveClockDoubleCommutator_eq_four_smul_disturbance U X hsq]
  constructor
  · intro hzero
    have hdisturbance : X - finiteCyclicObservableTwirl U X 2 = 0 := by
      exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact (sub_finiteInvolutiveObservableTwirl_eq_zero_iff_commutes U X hsq).mp
      hdisturbance
  · intro hcomm
    rw [(sub_finiteInvolutiveObservableTwirl_eq_zero_iff_commutes U X hsq).mpr hcomm,
      smul_zero]

end

end HTGeometry
