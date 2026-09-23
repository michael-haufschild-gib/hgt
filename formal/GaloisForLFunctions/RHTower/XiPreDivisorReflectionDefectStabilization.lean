import GaloisForLFunctions.RHTower.XiReflectionDefectOnePortSewing
import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaXiLanding
import GaloisForLFunctions.RHTower.EulerSquarefreeWickHedenmalmReflectionCrossing

/-!
# Pre-divisor reflection-defect stabilization

This module removes the remaining zero-indexing from the reflection-defect one-port interface.
The signed prime/Gamma reservoir matrix is defined at every spectral point before asking whether
Xi vanishes.  It specializes exactly to the multiplicity-labelled source matrix on the Xi
divisor and reverses under critical-line reflection.

The proposed constitutive law is a global stabilization identity.  One fixed coefficient-generated
Stokes carrier receives both orientations after adding the same positive rank-one bulk square,
weighted by `normSq (xi s)`.  This weight is source-first: the EWQ replica diagonal already lands
on completed Xi before divisor selection.  At a Xi zero the bulk stabilizer disappears, so an
off-line point would expose two negative source directions to a one-port Stokes carrier.

No stabilization is constructed here.  Unlike a family manufactured after selecting zeros, this
interface requires identities at every spectral point, one fixed target, and one shared bulk port.
The EWQ--Hedenmalm crossing does supply a concrete whole-plane reflection-odd port candidate below;
its square is reflection invariant.  What remains unconstructed is the global stabilization/weld,
not oriented pre-divisor data itself.
-/

open GaloisForLFunctions

namespace RHTower

noncomputable section

namespace PreDivisorReflectionDefectStabilization

open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt
open ReflectionDefectOnePortSewing

/-- Critical-line reflection on the full spectral plane, before divisor selection. -/
def preDivisorLineConj (s : ℂ) : ℂ := 1 - star s

@[simp] theorem preDivisorLineConj_involutive (s : ℂ) :
    preDivisorLineConj (preDivisorLineConj s) = s := by
  simp [preDivisorLineConj]

/-- Horizontal source rate on the full spectral plane. -/
def preDivisorCenteredRate (s : ℂ) : ℝ := 2 * s.re - 1

/-- Complete-resolution orientation read before a zero is selected. -/
def preDivisorTailLog (s : ℂ) : ℝ := (1 / 2 - s.re) * Real.log 2

/-- Sign of the complete-resolution source orientation. -/
def preDivisorOrientation (s : ℂ) : ℝ := Real.sign (preDivisorTailLog s)

/-- Prime-labelled Gamma/Bockstein carrier on the full spectral plane. -/
def preDivisorPrimeCarrier (s : ℂ) (p : Nat.Primes) : ℝ :=
  primeGammaCofinalBocksteinCoefficient (preDivisorCenteredRate s) p

/-- Positive magnitudes retained before the common reservoir incidence is formed. -/
def preDivisorSharedWeights {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) : Fin m → ℝ :=
  fun i => |preDivisorPrimeCarrier s (p i)|

/-- Source-first signed shared-reservoir matrix at an arbitrary spectral point. -/
def preDivisorSharedReservoirMatrix {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) : Matrix (Fin m) (Fin m) ℝ :=
  orientedSourceSharedReservoirMatrix (preDivisorOrientation s)
    (preDivisorSharedWeights s p)

@[simp] theorem preDivisorCenteredRate_lineConj (s : ℂ) :
    preDivisorCenteredRate (preDivisorLineConj s) = -preDivisorCenteredRate s := by
  simp [preDivisorCenteredRate, preDivisorLineConj]
  ring

@[simp] theorem preDivisorTailLog_lineConj (s : ℂ) :
    preDivisorTailLog (preDivisorLineConj s) = -preDivisorTailLog s := by
  simp [preDivisorTailLog, preDivisorLineConj]
  ring

@[simp] theorem preDivisorOrientation_lineConj (s : ℂ) :
    preDivisorOrientation (preDivisorLineConj s) = -preDivisorOrientation s := by
  rw [preDivisorOrientation, preDivisorTailLog_lineConj, Real.sign_neg]
  rfl

@[simp] theorem preDivisorPrimeCarrier_lineConj (s : ℂ) (p : Nat.Primes) :
    preDivisorPrimeCarrier (preDivisorLineConj s) p =
      -preDivisorPrimeCarrier s p := by
  rw [preDivisorPrimeCarrier, preDivisorCenteredRate_lineConj,
    primeGammaCofinalBocksteinCoefficient_neg]
  rfl

@[simp] theorem preDivisorSharedWeights_lineConj {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) :
    preDivisorSharedWeights (preDivisorLineConj s) p =
      preDivisorSharedWeights s p := by
  funext i
  simp [preDivisorSharedWeights]

@[simp] theorem preDivisorSharedReservoirMatrix_lineConj {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) :
    preDivisorSharedReservoirMatrix (preDivisorLineConj s) p =
      -preDivisorSharedReservoirMatrix s p := by
  rw [preDivisorSharedReservoirMatrix, preDivisorSharedReservoirMatrix,
    preDivisorOrientation_lineConj, preDivisorSharedWeights_lineConj]
  ext i j
  simp [orientedSourceSharedReservoirMatrix]

theorem preDivisorTailLog_neg_of_right
    (s : ℂ) (hright : 1 / 2 < s.re) :
    preDivisorTailLog s < 0 := by
  rw [preDivisorTailLog]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num))

theorem preDivisorOrientation_eq_neg_one_of_right
    (s : ℂ) (hright : 1 / 2 < s.re) :
    preDivisorOrientation s = -1 := by
  rw [preDivisorOrientation,
    Real.sign_of_neg (preDivisorTailLog_neg_of_right s hright)]

theorem preDivisorSharedWeights_pos_of_offLine {m : ℕ}
    (s : ℂ) (hoff : s.re ≠ 1 / 2)
    (p : Fin m → Nat.Primes) (i : Fin m) :
    0 < preDivisorSharedWeights s p i := by
  rw [preDivisorSharedWeights, abs_pos]
  intro hzero
  apply hoff
  have hrate :=
    (primeGammaCofinalBocksteinCoefficient_eq_zero_iff
      (preDivisorCenteredRate s) (p i)).mp
      (by simpa [preDivisorPrimeCarrier] using hzero)
  rw [preDivisorCenteredRate] at hrate
  linarith

theorem preDivisorSharedReservoirMatrix_toQuadraticForm_of_right {m : ℕ}
    (s : ℂ) (hright : 1 / 2 < s.re) (p : Fin m → Nat.Primes) :
    (preDivisorSharedReservoirMatrix s p).toQuadraticForm' =
      -(reservoirWeightedForm (preDivisorSharedWeights s p)) := by
  rw [preDivisorSharedReservoirMatrix,
    preDivisorOrientation_eq_neg_one_of_right s hright]
  exact orientedSourceSharedReservoirMatrix_toQuadraticForm_neg_one
    (fun i => (preDivisorSharedWeights_pos_of_offLine s
      (ne_of_gt hright) p i).le)

/-- The pre-divisor centered rate specializes to the existing divisor source rate. -/
theorem preDivisorCenteredRate_at_zeroCopy (q : XiZeroCopy) :
    preDivisorCenteredRate (q.1 : ℂ) = primeDepthBVWoldXiCenteredRate q.1 := by
  rfl

/-- The generic complete-source orientation specializes without choosing a new gauge. -/
theorem preDivisorOrientation_at_zeroCopy (q : XiZeroCopy) :
    preDivisorOrientation (q.1 : ℂ) = sourceZeroHorizontalOrientation q := by
  rw [preDivisorOrientation, sourceZeroHorizontalOrientation,
    (completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog 0 q).2]
  rfl

/-- Each generic prime carrier specializes coefficient-for-coefficient. -/
theorem preDivisorPrimeCarrier_at_zeroCopy (q : XiZeroCopy) (p : Nat.Primes) :
    preDivisorPrimeCarrier (q.1 : ℂ) p = sourceZeroHorizontalPrimeCarrier q p := by
  rfl

/-- Generic source weights retain the existing divisor packet exactly. -/
theorem preDivisorSharedWeights_at_zeroCopy {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) :
    preDivisorSharedWeights (q.1 : ℂ) p = sourceZeroHorizontalSharedWeights q p := by
  rfl

/-- The full generic matrix specializes exactly to the divisor-resolved matrix. -/
theorem preDivisorSharedReservoirMatrix_at_zeroCopy {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) :
    preDivisorSharedReservoirMatrix (q.1 : ℂ) p =
      sourceZeroHorizontalSharedReservoirMatrix q p := by
  rw [preDivisorSharedReservoirMatrix, sourceZeroHorizontalSharedReservoirMatrix,
    preDivisorOrientation_at_zeroCopy, preDivisorSharedWeights_at_zeroCopy]

/-- Critical-line reflection of the generic point agrees with multiplicity-copy reflection. -/
theorem preDivisorLineConj_at_zeroCopy (q : XiZeroCopy) :
    preDivisorLineConj (q.1 : ℂ) = ((xiZeroCopyLineConjEquiv q).1 : ℂ) := by
  rfl

/-- Positive completed-source bulk amplitude.  Its zero set is exactly the Xi divisor. -/
def completedSourceBulkSlack (s : ℂ) : ℝ := Complex.normSq (xi s)

theorem completedSourceBulkSlack_nonneg (s : ℂ) :
    0 ≤ completedSourceBulkSlack s := Complex.normSq_nonneg _

theorem completedSourceBulkSlack_eq_zero_iff (s : ℂ) :
    completedSourceBulkSlack s = 0 ↔ xi s = 0 := by
  exact Complex.normSq_eq_zero

@[simp] theorem completedSourceBulkSlack_lineConj (s : ℂ) :
    completedSourceBulkSlack (preDivisorLineConj s) = completedSourceBulkSlack s := by
  rw [completedSourceBulkSlack, completedSourceBulkSlack, preDivisorLineConj,
    xi_one_sub]
  change Complex.normSq (xi ((starRingEnd ℂ) s)) = Complex.normSq (xi s)
  rw [xi_conj]
  simp

/-! ## Corpus-selected transverse-port candidate -/

/--
Whole-plane extension of the exact EWQ--Hedenmalm oriented moving-horizon amplitude.  This is
defined before divisor selection and retains the non-scalar reflected crossing that positive
Fock energy erases.
-/
def preDivisorEWQHedenmalmAmplitude (s : ℂ) (p : Nat.Primes) : ℝ :=
  preDivisorCenteredRate s *
    routeNGammaSewnTwistedCriticalChannelAmplitude (preDivisorCenteredRate s) p

@[simp] theorem preDivisorEWQHedenmalmAmplitude_lineConj
    (s : ℂ) (p : Nat.Primes) :
    preDivisorEWQHedenmalmAmplitude (preDivisorLineConj s) p =
      -preDivisorEWQHedenmalmAmplitude s p := by
  rw [preDivisorEWQHedenmalmAmplitude, preDivisorEWQHedenmalmAmplitude,
    preDivisorCenteredRate_lineConj]
  simp only [routeNGammaSewnTwistedCriticalChannelAmplitude, abs_neg]
  ring

/-- The generic amplitude specializes coefficient-for-coefficient to the existing reflected
EWQ--Hedenmalm crossing on every Xi copy. -/
theorem preDivisorEWQHedenmalmAmplitude_at_zeroCopy
    (q : XiZeroCopy) (p : Nat.Primes) :
    preDivisorEWQHedenmalmAmplitude (q.1 : ℂ) p =
      GaloisForLFunctions.RHTower.ewqHedenmalmCovariantAmplitude p q := by
  rw [GaloisForLFunctions.RHTower.ewqHedenmalmCovariantAmplitude,
    HedenmalmThetaSource.thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime,
    HedenmalmThetaSource.thetaWardHorizontalOrientation_mul_abs_centeredRate,
    preDivisorEWQHedenmalmAmplitude, preDivisorCenteredRate_at_zeroCopy]

/-- Finite prime-packet functional supplied by the oriented EWQ--Hedenmalm amplitudes. -/
def preDivisorEWQHedenmalmPort {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, preDivisorEWQHedenmalmAmplitude s (p i) * x i
  map_add' := by
    intro x y
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem preDivisorEWQHedenmalmPort_apply {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) (x : Fin m → ℝ) :
    preDivisorEWQHedenmalmPort s p x =
      ∑ i, preDivisorEWQHedenmalmAmplitude s (p i) * x i := rfl

/-- Reflection reverses the oriented port, while its stabilizing square is unchanged. -/
@[simp] theorem preDivisorEWQHedenmalmPort_lineConj {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) :
    preDivisorEWQHedenmalmPort (preDivisorLineConj s) p =
      -preDivisorEWQHedenmalmPort s p := by
  apply LinearMap.ext
  intro x
  rw [preDivisorEWQHedenmalmPort_apply, LinearMap.neg_apply,
    preDivisorEWQHedenmalmPort_apply]
  simp_rw [preDivisorEWQHedenmalmAmplitude_lineConj]
  rw [← Finset.sum_neg_distrib (s := Finset.univ)
    (fun i => preDivisorEWQHedenmalmAmplitude s (p i) * x i)]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- At a zero copy the whole packet is exactly the already-formalized EWQ--Hedenmalm amplitude
packet, not a newly fitted functional. -/
theorem preDivisorEWQHedenmalmPort_at_zeroCopy {m : ℕ}
    (q : XiZeroCopy) (p : Fin m → Nat.Primes) (x : Fin m → ℝ) :
    preDivisorEWQHedenmalmPort (q.1 : ℂ) p x =
      ∑ i, GaloisForLFunctions.RHTower.ewqHedenmalmCovariantAmplitude (p i) q * x i := by
  rw [preDivisorEWQHedenmalmPort_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [preDivisorEWQHedenmalmAmplitude_at_zeroCopy]

/-! ## Central-port no-go -/

/-- Weighted longitudinal reservoir port.  This is the source counterpart of the unique
coefficient-generated Stokes physical-rank port. -/
def reservoirWeightedCentralPort {m : ℕ} (w : Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] ℝ :=
  (reservoirSumLinear m).comp (reservoirScaleLinear w)

@[simp] theorem reservoirWeightedCentralPort_apply {m : ℕ}
    (w : Fin m → ℝ) (x : Fin m → ℝ) :
    reservoirWeightedCentralPort w x = ∑ i, Real.sqrt (w i) * x i := rfl

theorem reservoirWeightedCentralPort_surjective {m : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (hm : 0 < m) :
    Function.Surjective (reservoirWeightedCentralPort w) := by
  intro r
  obtain ⟨y, hy⟩ := reservoirSumLinear_surjective hm r
  refine ⟨(reservoirScaleEquiv w hw).symm y, ?_⟩
  change reservoirSumLinear m
      (reservoirScaleLinear w ((reservoirScaleEquiv w hw).symm y)) = r
  have hscale :
      reservoirScaleLinear w ((reservoirScaleEquiv w hw).symm y) = y := by
    exact (reservoirScaleEquiv w hw).apply_symm_apply y
  rw [hscale]
  exact hy

/-- The transverse reservoir plane has codimension one. -/
theorem finrank_reservoirWeightedCentralPort_ker {m : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (hm : 0 < m) :
    Module.finrank ℝ (reservoirWeightedCentralPort w).ker = m - 1 := by
  have hrange : (reservoirWeightedCentralPort w).range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _
      (reservoirWeightedCentralPort_surjective w hw hm)
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (reservoirWeightedCentralPort w)
  rw [hrange] at hdim
  have htop : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by simp
  rw [htop, Module.finrank_fin_fun ℝ] at hdim
  omega

/-- The weighted reservoir form is strictly positive on its transverse plane. -/
theorem reservoirWeightedForm_restrict_centralKer_posDef {m : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) :
    ((reservoirWeightedForm w).restrict
      (reservoirWeightedCentralPort w).ker).PosDef := by
  intro x hx
  rw [QuadraticMap.restrict_apply, reservoirWeightedForm,
    QuadraticMap.comp_apply, reservoirBaseForm_apply]
  have hsum :
      ∑ i, reservoirScaleLinear w x.1 i = 0 := x.2
  rw [hsum, zero_pow (by norm_num), sub_zero]
  have hscaled : reservoirScaleLinear w x.1 ≠ 0 := by
    intro hzero
    apply hx
    apply Subtype.ext
    funext i
    have hi := congrFun hzero i
    change Real.sqrt (w i) * x.1 i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left
      (ne_of_gt (Real.sqrt_pos.2 (hw i)))
  have hex : ∃ i, reservoirScaleLinear w x.1 i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hscaled (funext h)
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg _
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- Reflected reservoir after adding an arbitrary square of the longitudinal central port. -/
def centralStabilizedReflectedReservoirForm {m : ℕ}
    (w : Fin m → ℝ) (c : ℝ) : QuadraticForm ℝ (Fin m → ℝ) :=
  -(reservoirWeightedForm w) +
    c • (QuadraticMap.sq.comp (reservoirWeightedCentralPort w))

/-- Every longitudinal correction vanishes on the full transverse plane, which therefore remains
negative definite after reflection. -/
theorem centralStabilizedReflectedReservoirForm_centralKer_negDef {m : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (c : ℝ) :
    ((-(centralStabilizedReflectedReservoirForm w c)).restrict
      (reservoirWeightedCentralPort w).ker).PosDef := by
  intro x hx
  have hpos := reservoirWeightedForm_restrict_centralKer_posDef w hw x hx
  rw [QuadraticMap.restrict_apply] at hpos ⊢
  rw [QuadraticMap.neg_apply, centralStabilizedReflectedReservoirForm,
    QuadraticMap.add_apply, QuadraticMap.neg_apply, QuadraticMap.smul_apply,
    QuadraticMap.comp_apply, QuadraticMap.sq_apply, x.2]
  simp only [smul_eq_mul, mul_zero, add_zero, neg_neg]
  exact hpos

/-- **Central-port no-go.**  A longitudinal square cannot reduce the reflected reservoir's
negative inertia: all m-1 transverse directions remain negative. -/
theorem centralStabilizedReflectedReservoirForm_sigNeg_ge {m : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (hm : 0 < m) (c : ℝ) :
    m - 1 ≤ sigNeg (centralStabilizedReflectedReservoirForm w c) := by
  have hle := le_sigNeg_of_negDef
    (centralStabilizedReflectedReservoirForm w c)
    (centralStabilizedReflectedReservoirForm_centralKer_negDef w hw c)
  rw [finrank_reservoirWeightedCentralPort_ker w hw hm] at hle
  exact hle

/-- Three source labels retain at least two negative transverse directions under every central
rank-port correction. -/
theorem centralStabilizedReflectedReservoirForm_three_sigNeg_ge_two
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (c : ℝ) :
    2 ≤ sigNeg (centralStabilizedReflectedReservoirForm w c) := by
  simpa using centralStabilizedReflectedReservoirForm_sigNeg_ge
    w hw (by norm_num) c

/--
Global pre-divisor stabilization law.  One target carrier and one rank-one positive bulk port are
fixed before any Xi zero is read.  The same bulk square repairs the forward and reflected source
forms; its coefficient is the completed source amplitude `|Xi(s)|²`.
-/
structure XiGlobalPreDivisorOnePortStabilization where
  markedPointDepth : ℕ
  orbitCount : Fin (markedPointDepth + 1) → ℕ
  fiberRank : Fin (markedPointDepth + 1) → ℕ
  coverDegree : Fin (markedPointDepth + 1) → ℕ
  jetDepth : Fin (markedPointDepth + 1) → ℕ
  genus : ℕ
  localData : LocalData markedPointDepth orbitCount fiberRank coverDegree jetDepth
  primes : Fin 3 → Nat.Primes
  stabilizerPort : ℂ → (Fin 3 → ℝ) →ₗ[ℝ] ℝ
  stabilizerPort_reflectionParity : ∀ s,
    stabilizerPort (preDivisorLineConj s) = stabilizerPort s ∨
      stabilizerPort (preDivisorLineConj s) = -stabilizerPort s
  stabilizerPort_continuous : ∀ x, Continuous (fun s => stabilizerPort s x)
  forward : ℂ → (Fin 3 → ℝ) →ₗ[ℝ] compatibleCharges localData
  reflected : ℂ → (Fin 3 → ℝ) →ₗ[ℝ] compatibleCharges localData
  forward_continuous : ∀ x, Continuous (fun s => forward s x)
  reflected_continuous : ∀ x, Continuous (fun s => reflected s x)
  forward_stabilized : ∀ s x,
    (preDivisorSharedReservoirMatrix s primes).toQuadraticForm' x +
        completedSourceBulkSlack s * (stabilizerPort s x) ^ (2 : ℕ) =
      globalWittForm genus localData (forward s x)
  reflected_stabilized : ∀ s x,
    (preDivisorSharedReservoirMatrix (preDivisorLineConj s) primes).toQuadraticForm' x +
        completedSourceBulkSlack s * (stabilizerPort s x) ^ (2 : ℕ) =
      globalWittForm genus localData (reflected s x)

/-- At a Xi zero the positive stabilizer vanishes, leaving an exact forward Stokes landing. -/
theorem XiGlobalPreDivisorOnePortStabilization.forward_exact_of_xi_zero
    (S : XiGlobalPreDivisorOnePortStabilization) {s : ℂ} (hs : xi s = 0) (x) :
    (preDivisorSharedReservoirMatrix s S.primes).toQuadraticForm' x =
      globalWittForm S.genus S.localData (S.forward s x) := by
  have h := S.forward_stabilized s x
  rw [completedSourceBulkSlack, hs, Complex.normSq_zero, zero_mul, add_zero] at h
  exact h

/-- At the same Xi zero the reflected orientation also loses the shared bulk stabilizer. -/
theorem XiGlobalPreDivisorOnePortStabilization.reflected_exact_of_xi_zero
    (S : XiGlobalPreDivisorOnePortStabilization) {s : ℂ} (hs : xi s = 0) (x) :
    (preDivisorSharedReservoirMatrix (preDivisorLineConj s) S.primes).toQuadraticForm' x =
      globalWittForm S.genus S.localData (S.reflected s x) := by
  have h := S.reflected_stabilized s x
  rw [completedSourceBulkSlack, hs, Complex.normSq_zero, zero_mul, add_zero] at h
  exact h

/-- A valid stabilization cannot use the longitudinal central rank port on the right half-plane.
That square leaves the two-dimensional reflected transverse plane negative, while every pullback
of the fixed Stokes target has negative inertia at most one. -/
theorem XiGlobalPreDivisorOnePortStabilization.stabilizerPort_not_central_of_right
    (S : XiGlobalPreDivisorOnePortStabilization)
    {s : ℂ} (hright : 1 / 2 < s.re) :
    ¬ ∃ c : ℝ, S.stabilizerPort s =
      c • reservoirWeightedCentralPort
        (preDivisorSharedWeights s S.primes) := by
  rintro ⟨c, hcentral⟩
  let w : Fin 3 → ℝ := preDivisorSharedWeights s S.primes
  have hw : ∀ i, 0 < w i :=
    fun i => preDivisorSharedWeights_pos_of_offLine s
      (ne_of_gt hright) S.primes i
  have hsource :
      (preDivisorSharedReservoirMatrix s S.primes).toQuadraticForm' =
        -(reservoirWeightedForm w) := by
    exact preDivisorSharedReservoirMatrix_toQuadraticForm_of_right
      s hright S.primes
  have hpull : ∀ x,
      centralStabilizedReflectedReservoirForm w
          (completedSourceBulkSlack s * c ^ (2 : ℕ)) x =
        globalWittForm S.genus S.localData (S.forward s x) := by
    intro x
    have h := S.forward_stabilized s x
    rw [hsource, hcentral] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    rw [centralStabilizedReflectedReservoirForm,
      QuadraticMap.add_apply, QuadraticMap.neg_apply,
      QuadraticMap.smul_apply, QuadraticMap.comp_apply,
      QuadraticMap.sq_apply]
    simp only [smul_eq_mul]
    calc
      -reservoirWeightedForm w x +
          completedSourceBulkSlack s * c ^ (2 : ℕ) *
            (reservoirWeightedCentralPort w x *
              reservoirWeightedCentralPort w x) =
        -reservoirWeightedForm w x +
          completedSourceBulkSlack s *
            (c * reservoirWeightedCentralPort w x) ^ (2 : ℕ) := by ring
      _ = globalWittForm S.genus S.localData (S.forward s x) := h
  have hupper := sigNeg_le_one_of_onePort_pullback
    (centralStabilizedReflectedReservoirForm w
      (completedSourceBulkSlack s * c ^ (2 : ℕ)))
    (globalWittForm S.genus S.localData) (S.forward s)
    (GlobalPuiseuxWittLanding.rankCorrection S.genus S.localData)
    (GlobalPuiseuxWittLanding.globalWittForm_add_rankCorrection_nonneg
      S.genus S.localData) hpull
  have hlower :=
    centralStabilizedReflectedReservoirForm_three_sigNeg_ge_two
      w hw (completedSourceBulkSlack s * c ^ (2 : ℕ))
  omega

/-- The same classifier on either side of the critical line: any surviving bulk stabilizer must
be genuinely transverse, not a scalar central holonomy/Noether/rank port. -/
theorem XiGlobalPreDivisorOnePortStabilization.stabilizerPort_not_central_of_offLine
    (S : XiGlobalPreDivisorOnePortStabilization)
    {s : ℂ} (hoff : s.re ≠ 1 / 2) :
    ¬ ∃ c : ℝ, S.stabilizerPort s =
      c • reservoirWeightedCentralPort
        (preDivisorSharedWeights s S.primes) := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · intro hcentral
    have hreflectRight : 1 / 2 < (preDivisorLineConj s).re := by
      simp [preDivisorLineConj]
      linarith
    apply S.stabilizerPort_not_central_of_right hreflectRight
    obtain ⟨c, hc⟩ := hcentral
    rcases S.stabilizerPort_reflectionParity s with heven | hodd
    · refine ⟨c, ?_⟩
      rw [heven, preDivisorSharedWeights_lineConj, hc]
    · refine ⟨-c, ?_⟩
      rw [hodd, preDivisorSharedWeights_lineConj, hc]
      exact (neg_smul c
        (reservoirWeightedCentralPort
          (preDivisorSharedWeights s S.primes))).symm
  · exact S.stabilizerPort_not_central_of_right hright

/-- Forgetting the whole-plane stabilization yields the earlier divisor-level one-port sewing. -/
def XiGlobalPreDivisorOnePortStabilization.toGlobalOnePortSewing
    (S : XiGlobalPreDivisorOnePortStabilization) : XiGlobalOnePortSewing where
  markedPointDepth := S.markedPointDepth
  orbitCount := S.orbitCount
  fiberRank := S.fiberRank
  coverDegree := S.coverDegree
  jetDepth := S.jetDepth
  genus := S.genus
  localData := S.localData
  primes := S.primes
  forward q := S.forward (q.1 : ℂ)
  reflected q := S.reflected (q.1 : ℂ)
  forward_preserves q x := by
    rw [← preDivisorSharedReservoirMatrix_at_zeroCopy q S.primes]
    exact S.forward_exact_of_xi_zero (xi_eq_zero_of_mem_divisor_support q.1) x
  reflected_preserves q x := by
    rw [← preDivisorSharedReservoirMatrix_at_zeroCopy
      (xiZeroCopyLineConjEquiv q) S.primes]
    rw [← preDivisorLineConj_at_zeroCopy q]
    exact S.reflected_exact_of_xi_zero (xi_eq_zero_of_mem_divisor_support q.1) x

/--
Source-first endpoint: a global rank-one stabilization law proves RH.  Zeros are not generated by
the law; they are precisely points where the positive bulk repair disappears and the incompatible
reflection defect must fit through one global Stokes port.
-/
theorem riemannHypothesis_of_globalPreDivisorOnePortStabilization
    (S : XiGlobalPreDivisorOnePortStabilization) : RiemannHypothesis :=
  riemannHypothesis_of_globalOnePortSewing S.toGlobalOnePortSewing

end PreDivisorReflectionDefectStabilization

end

end RHTower
