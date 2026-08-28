import GaloisForLFunctions.RHTower.FEPairedPrimeJetBarycentricRigidity
import GaloisForLFunctions.RHTower.CenteredRealEvenPolynomialDensity
import GaloisForLFunctions.RHTower.DeningerArithmeticContinuousJets
import GaloisForLFunctions.RHTower.PrimeLogExponentialTypeUniqueness
import GaloisForLFunctions.HTGeometry.LowDegreeVanishing
import GaloisForLFunctions.HTGeometry.LogDerivUniformLimit
import GaloisForLFunctions.HTGeometry.WeierstrassPaddedGenusProduct

/-!
# Prime-jet formation transport

Finite odd laws are written uniquely as `P(z) = z Q(z²)` with `deg Q < n`.  Evaluation at
nonzero square-distinct radii is an exact linear chart.  Inclusion of bounded-degree laws therefore
induces strict source-generated transport between every pair of such charts.  The origin derivative
is the barycentric reporter and is conserved contravariantly by transport.

The companion analytic and Hilbert-graph laws are developed below from the same chart.  The
infinite-sampling counterexample explicitly assumes escaping squared nodes; strict increase alone
does not imply this and is insufficient.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial
open RHTower

/-- Degree-`< n` square-coordinate factor of an odd polynomial law `z Q(z²)`. -/
abbrev PrimeJetOddLaw (n : ℕ) := Polynomial.degreeLT ℂ n

/-- Odd polynomial represented by its square-coordinate factor. -/
def primeJetOddLawValue {n : ℕ} (Q : PrimeJetOddLaw n) (z : ℂ) : ℂ :=
  z * Q.1.eval (z ^ 2)

/-- Reflected sample `P(r)-P(-r)=2rQ(r²)` of an odd law. -/
def primeJetOddSample {n : ℕ} (r : Fin n → ℂ) (Q : PrimeJetOddLaw n)
    (i : Fin n) : ℂ :=
  2 * r i * Q.1.eval (r i ^ 2)

/-- Square reflected-sample chart. -/
def primeJetSampleMap {n : ℕ} (r : Fin n → ℂ) :
    PrimeJetOddLaw n →ₗ[ℂ] (Fin n → ℂ) where
  toFun Q := primeJetOddSample r Q
  map_add' Q S := by
    ext i
    simp [primeJetOddSample]
    ring
  map_smul' c Q := by
    ext i
    simp [primeJetOddSample]
    ring

/-- Origin derivative reporter `P'(0)=Q(0)`. -/
def primeJetOriginReporter (n : ℕ) : PrimeJetOddLaw n →ₗ[ℂ] ℂ where
  toFun Q := Q.1.eval 0
  map_add' Q S := by simp
  map_smul' c Q := by simp

theorem primeJetSampleMap_injective {n : ℕ} {r : Fin n → ℂ}
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    Function.Injective (primeJetSampleMap r) := by
  intro Q S hQS
  apply Subtype.ext
  let D : PrimeJetOddLaw n := Q - S
  have hzero : primeJetSampleMap r D = 0 := by
    rw [map_sub, hQS, sub_self]
  have heval : ∀ i : Fin n, D.1.eval (r i ^ 2) = 0 := by
    intro i
    have hi := congrFun hzero i
    simp [primeJetSampleMap, primeJetOddSample, hr0 i] at hi
    exact hi
  have hdeg : D.1.degree <
      (((Finset.univ : Finset (Fin n)).card : ℕ) : WithBot ℕ) := by
    simpa using (Polynomial.mem_degreeLT.mp D.2)
  have hinterp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin n))) (v := fun i => r i ^ 2)
    hr2inj.injOn hdeg
  have hD : D.1 = 0 := by
    rw [hinterp, Lagrange.interpolate_apply]
    simp [heval]
  change Q.1 - S.1 = 0 at hD
  exact sub_eq_zero.mp hD

/-- Reflected sampling is a linear equivalence at nonzero square-distinct radii. -/
def primeJetSampleEquiv {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    PrimeJetOddLaw n ≃ₗ[ℂ] (Fin n → ℂ) := by
  let E := Polynomial.degreeLTEquiv ℂ n
  let F := (primeJetSampleMap r).comp E.symm.toLinearMap
  have hFinj : Function.Injective F :=
    (primeJetSampleMap_injective hr0 hr2inj).comp E.symm.injective
  have hFsurj : Function.Surjective F := LinearMap.surjective_of_injective hFinj
  have hsurj : Function.Surjective (primeJetSampleMap r) := by
    intro y
    obtain ⟨x, hx⟩ := hFsurj y
    exact ⟨E.symm x, hx⟩
  exact LinearEquiv.ofBijective (primeJetSampleMap r)
    ⟨primeJetSampleMap_injective hr0 hr2inj, hsurj⟩

@[simp] theorem primeJetSampleEquiv_apply {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (Q : PrimeJetOddLaw n) :
    primeJetSampleEquiv r hr0 hr2inj Q = primeJetSampleMap r Q := rfl

/-- Inclusion of degree-`< n` odd laws into degree-`< m` odd laws. -/
def primeJetLawInclusion {n m : ℕ} (hnm : n ≤ m) :
    PrimeJetOddLaw n →ₗ[ℂ] PrimeJetOddLaw m :=
  Submodule.inclusion (Polynomial.degreeLT_mono hnm)

@[simp] theorem primeJetLawInclusion_apply {n m : ℕ} (hnm : n ≤ m)
    (Q : PrimeJetOddLaw n) :
    (primeJetLawInclusion hnm Q).1 = Q.1 :=
  Submodule.coe_inclusion (Polynomial.degreeLT_mono hnm) Q

theorem primeJetLawInclusion_trans {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    (primeJetLawInclusion hmk).comp (primeJetLawInclusion hnm) =
      primeJetLawInclusion (hnm.trans hmk) := by
  apply LinearMap.ext
  intro Q
  apply Subtype.ext
  calc
    ((primeJetLawInclusion hmk) ((primeJetLawInclusion hnm) Q)).1 =
        (primeJetLawInclusion hnm Q).1 := primeJetLawInclusion_apply hmk _
    _ = Q.1 := primeJetLawInclusion_apply hnm Q
    _ = (primeJetLawInclusion (hnm.trans hmk) Q).1 :=
      (primeJetLawInclusion_apply (hnm.trans hmk) Q).symm

/-- Source-generated transport between two finite reflected-sample charts. -/
def primeJetTransport {n m : ℕ} (rn : Fin n → ℂ) (rm : Fin m → ℂ)
    (hrn0 : ∀ i, rn i ≠ 0) (hrn2 : Function.Injective fun i => rn i ^ 2)
    (hrm0 : ∀ i, rm i ≠ 0) (hrm2 : Function.Injective fun i => rm i ^ 2)
    (hnm : n ≤ m) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  (primeJetSampleEquiv rm hrm0 hrm2).toLinearMap.comp
    ((primeJetLawInclusion hnm).comp
      (primeJetSampleEquiv rn hrn0 hrn2).symm.toLinearMap)

theorem primeJetTransport_eq_chart_conjugation {n m : ℕ}
    (rn : Fin n → ℂ) (rm : Fin m → ℂ)
    (hrn0 : ∀ i, rn i ≠ 0) (hrn2 : Function.Injective fun i => rn i ^ 2)
    (hrm0 : ∀ i, rm i ≠ 0) (hrm2 : Function.Injective fun i => rm i ^ 2)
    (hnm : n ≤ m) (y : Fin n → ℂ) :
    primeJetTransport rn rm hrn0 hrn2 hrm0 hrm2 hnm y =
      primeJetSampleEquiv rm hrm0 hrm2
        (primeJetLawInclusion hnm ((primeJetSampleEquiv rn hrn0 hrn2).symm y)) := rfl

/-- Formation transports compose strictly, with no projective scalar or cocycle. -/
theorem primeJetTransport_trans {n m k : ℕ}
    (rn : Fin n → ℂ) (rm : Fin m → ℂ) (rk : Fin k → ℂ)
    (hrn0 : ∀ i, rn i ≠ 0) (hrn2 : Function.Injective fun i => rn i ^ 2)
    (hrm0 : ∀ i, rm i ≠ 0) (hrm2 : Function.Injective fun i => rm i ^ 2)
    (hrk0 : ∀ i, rk i ≠ 0) (hrk2 : Function.Injective fun i => rk i ^ 2)
    (hnm : n ≤ m) (hmk : m ≤ k) :
    (primeJetTransport rm rk hrm0 hrm2 hrk0 hrk2 hmk).comp
        (primeJetTransport rn rm hrn0 hrn2 hrm0 hrm2 hnm) =
      primeJetTransport rn rk hrn0 hrn2 hrk0 hrk2 (hnm.trans hmk) := by
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, primeJetTransport]
  have hcancel := (primeJetSampleEquiv rm hrm0 hrm2).symm_apply_apply
    (primeJetLawInclusion hnm ((primeJetSampleEquiv rn hrn0 hrn2).symm y))
  let Q := (primeJetSampleEquiv rn hrn0 hrn2).symm y
  calc
    primeJetSampleEquiv rk hrk0 hrk2
        (primeJetLawInclusion hmk
          ((primeJetSampleEquiv rm hrm0 hrm2).symm
            (primeJetSampleEquiv rm hrm0 hrm2 (primeJetLawInclusion hnm Q)))) =
      primeJetSampleEquiv rk hrk0 hrk2
        (primeJetLawInclusion hmk (primeJetLawInclusion hnm Q)) :=
      congrArg (fun S => primeJetSampleEquiv rk hrk0 hrk2
        (primeJetLawInclusion hmk S)) hcancel
    _ = primeJetSampleEquiv rk hrk0 hrk2
        (primeJetLawInclusion (hnm.trans hmk) Q) := by
      rw [← LinearMap.comp_apply, primeJetLawInclusion_trans]

/-- Reporter on sample coordinates, transported from the origin derivative. -/
def primeJetCoordinateReporter {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (primeJetOriginReporter n).comp (primeJetSampleEquiv r hr0 hr2inj).symm.toLinearMap

/-- Contravariant reporter conservation under every source-generated transport. -/
theorem primeJetCoordinateReporter_transport {n m : ℕ}
    (rn : Fin n → ℂ) (rm : Fin m → ℂ)
    (hrn0 : ∀ i, rn i ≠ 0) (hrn2 : Function.Injective fun i => rn i ^ 2)
    (hrm0 : ∀ i, rm i ≠ 0) (hrm2 : Function.Injective fun i => rm i ^ 2)
    (hnm : n ≤ m) :
    (primeJetCoordinateReporter rm hrm0 hrm2).comp
        (primeJetTransport rn rm hrn0 hrn2 hrm0 hrm2 hnm) =
      primeJetCoordinateReporter rn hrn0 hrn2 := by
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, primeJetCoordinateReporter, primeJetTransport]
  have hcancel := (primeJetSampleEquiv rm hrm0 hrm2).symm_apply_apply
    (primeJetLawInclusion hnm ((primeJetSampleEquiv rn hrn0 hrn2).symm y))
  let Q := (primeJetSampleEquiv rn hrn0 hrn2).symm y
  calc
    primeJetOriginReporter m
        ((primeJetSampleEquiv rm hrm0 hrm2).symm
          (primeJetSampleEquiv rm hrm0 hrm2 (primeJetLawInclusion hnm Q))) =
      primeJetOriginReporter m (primeJetLawInclusion hnm Q) :=
      congrArg (primeJetOriginReporter m) hcancel
    _ = primeJetOriginReporter n Q := by
      simp [primeJetOriginReporter, primeJetLawInclusion_apply]

/-- The coordinate reporter is exactly the barycentric coefficient packet. -/
theorem primeJetCoordinateReporter_eq_barycentric {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℂ) (hr0 : ∀ i, r i ≠ 0)
    (hr2inj : Function.Injective fun i => r i ^ 2) (y : Fin n → ℂ) :
    primeJetCoordinateReporter r hr0 hr2inj y =
      ∑ i : Fin n, fePairedOriginCoefficient r i * y i := by
  let Q := (primeJetSampleEquiv r hr0 hr2inj).symm y
  have hmom := originInterpolationWeight_moments (fun i => r i ^ 2) hr2inj
  have hrecover := weighted_eval_eq_coeff_zero_of_finMoments hn
    (fun i => r i ^ 2) (originInterpolationWeight fun i => r i ^ 2) Q.1
    (by
      by_cases hQ : Q.1 = 0
      · simp [hQ, hn]
      · exact (Polynomial.natDegree_lt_iff_degree_lt hQ).mpr
          (Polynomial.mem_degreeLT.mp Q.2)) hmom
  change Q.1.eval 0 = _
  calc
    Q.1.eval 0 = Q.1.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero Q.1).symm
    _ = ∑ i : Fin n,
        originInterpolationWeight (fun j => r j ^ 2) i * Q.1.eval (r i ^ 2) :=
      hrecover.symm
    _ = ∑ i : Fin n, fePairedOriginCoefficient r i * y i := by
      apply Finset.sum_congr rfl
      intro i _
      have hy := congrFun ((primeJetSampleEquiv r hr0 hr2inj).apply_symm_apply y) i
      change 2 * r i * Q.1.eval (r i ^ 2) = y i at hy
      rw [← hy]
      simp only [fePairedOriginCoefficient]
      field_simp [hr0 i]

/-! ## One-step transport and locality defect -/

/-- Prefix radii before one new boundary node is adjoined. -/
def primeJetPrefixRadii {n : ℕ} (r : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun i => r i.castSucc

theorem primeJetPrefixRadii_ne_zero {n : ℕ} {r : Fin (n + 1) → ℂ}
    (hr0 : ∀ i, r i ≠ 0) : ∀ i, primeJetPrefixRadii r i ≠ 0 :=
  fun i => hr0 i.castSucc

theorem primeJetPrefixRadii_sq_injective {n : ℕ} {r : Fin (n + 1) → ℂ}
    (hr2inj : Function.Injective fun i => r i ^ 2) :
    Function.Injective fun i => primeJetPrefixRadii r i ^ 2 := by
  intro i j hij
  exact Fin.castSucc_inj.mp (hr2inj hij)

/-- Terminal coordinate added by one formation step. -/
def primeJetTailReporter {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun y := 2 * r (Fin.last n) *
    ((primeJetSampleEquiv (primeJetPrefixRadii r)
      (primeJetPrefixRadii_ne_zero hr0)
      (primeJetPrefixRadii_sq_injective hr2inj)).symm y).1.eval (r (Fin.last n) ^ 2)
  map_add' y z := by
    simp
    ring
  map_smul' c y := by
    simp
    ring

/-- One-step formation transport is the graph of its terminal reporter. -/
def primeJetOneStepTransport {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun y := Fin.snoc y (primeJetTailReporter r hr0 hr2inj y)
  map_add' y z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Old coordinates are unchanged by one-step transport. -/
theorem primeJetOneStepTransport_castSucc {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (y : Fin n → ℂ) (i : Fin n) :
    primeJetOneStepTransport r hr0 hr2inj y i.castSucc = y i := by
  simp [primeJetOneStepTransport]

@[simp] theorem primeJetOneStepTransport_last {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (y : Fin n → ℂ) :
    primeJetOneStepTransport r hr0 hr2inj y (Fin.last n) =
      primeJetTailReporter r hr0 hr2inj y := by simp [primeJetOneStepTransport]

/-- One-step graph transport is exactly law inclusion in reflected-sample charts. -/
theorem primeJetOneStepTransport_sample {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (Q : PrimeJetOddLaw n) :
    primeJetOneStepTransport r hr0 hr2inj
        (primeJetSampleEquiv (primeJetPrefixRadii r)
          (primeJetPrefixRadii_ne_zero hr0)
          (primeJetPrefixRadii_sq_injective hr2inj) Q) =
      primeJetSampleEquiv r hr0 hr2inj
        (primeJetLawInclusion (Nat.le_succ n) Q) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [primeJetOneStepTransport_last]
    rw [show primeJetTailReporter r hr0 hr2inj
        (primeJetSampleEquiv (primeJetPrefixRadii r)
          (primeJetPrefixRadii_ne_zero hr0)
          (primeJetPrefixRadii_sq_injective hr2inj) Q) =
        2 * r (Fin.last n) * Q.1.eval (r (Fin.last n) ^ 2) by
      change 2 * r (Fin.last n) *
        ((primeJetSampleEquiv (primeJetPrefixRadii r)
          (primeJetPrefixRadii_ne_zero hr0)
          (primeJetPrefixRadii_sq_injective hr2inj)).symm
            (primeJetSampleEquiv (primeJetPrefixRadii r)
              (primeJetPrefixRadii_ne_zero hr0)
              (primeJetPrefixRadii_sq_injective hr2inj) Q)).1.eval
              (r (Fin.last n) ^ 2) = _
      rw [LinearEquiv.symm_apply_apply]]
    change 2 * r (Fin.last n) * Q.1.eval (r (Fin.last n) ^ 2) =
      primeJetOddSample r (primeJetLawInclusion (Nat.le_succ n) Q) (Fin.last n)
    simp [primeJetOddSample, primeJetLawInclusion_apply]
  · rw [primeJetOneStepTransport_castSucc]
    change primeJetOddSample (primeJetPrefixRadii r) Q i =
      primeJetOddSample r (primeJetLawInclusion (Nat.le_succ n) Q) i.castSucc
    simp [primeJetOddSample, primeJetPrefixRadii, primeJetLawInclusion_apply]

/-- One-step graph transport conserves the origin reporter. -/
theorem primeJetCoordinateReporter_oneStep {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    (primeJetCoordinateReporter r hr0 hr2inj).comp
        (primeJetOneStepTransport r hr0 hr2inj) =
      primeJetCoordinateReporter (primeJetPrefixRadii r)
        (primeJetPrefixRadii_ne_zero hr0) (primeJetPrefixRadii_sq_injective hr2inj) := by
  apply LinearMap.ext
  intro y
  let E := primeJetSampleEquiv (primeJetPrefixRadii r)
    (primeJetPrefixRadii_ne_zero hr0) (primeJetPrefixRadii_sq_injective hr2inj)
  let Q := E.symm y
  have hy : E Q = y := E.apply_symm_apply y
  simp only [LinearMap.comp_apply]
  rw [← hy]
  calc
    primeJetCoordinateReporter r hr0 hr2inj
        (primeJetOneStepTransport r hr0 hr2inj (E Q)) =
      primeJetCoordinateReporter r hr0 hr2inj
        (primeJetSampleEquiv r hr0 hr2inj
          (primeJetLawInclusion (Nat.le_succ n) Q)) :=
      congrArg (primeJetCoordinateReporter r hr0 hr2inj)
        (primeJetOneStepTransport_sample r hr0 hr2inj Q)
    _ = primeJetOriginReporter (n + 1) (primeJetLawInclusion (Nat.le_succ n) Q) := by
      simp only [primeJetCoordinateReporter, LinearMap.comp_apply]
      exact congrArg (primeJetOriginReporter (n + 1))
        ((primeJetSampleEquiv r hr0 hr2inj).symm_apply_apply
          (primeJetLawInclusion (Nat.le_succ n) Q))
    _ = primeJetOriginReporter n Q := by
      simp [primeJetOriginReporter, primeJetLawInclusion_apply]
    _ = primeJetCoordinateReporter (primeJetPrefixRadii r)
        (primeJetPrefixRadii_ne_zero hr0)
        (primeJetPrefixRadii_sq_injective hr2inj) (E Q) := by
      simp only [primeJetCoordinateReporter, LinearMap.comp_apply]
      change primeJetOriginReporter n Q = primeJetOriginReporter n (E.symm (E Q))
      exact congrArg (primeJetOriginReporter n) (E.symm_apply_apply Q).symm

/-- Append a zero terminal coordinate. -/
def primeJetZeroExtend (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun y := Fin.snoc y 0
  map_add' y z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem primeJetZeroExtend_castSucc {n : ℕ} (y : Fin n → ℂ) (i : Fin n) :
    primeJetZeroExtend n y i.castSucc = y i := by simp [primeJetZeroExtend]

@[simp] theorem primeJetZeroExtend_last {n : ℕ} (y : Fin n → ℂ) :
    primeJetZeroExtend n y (Fin.last n) = 0 := by simp [primeJetZeroExtend]

/-- One-step transport is the graph of its terminal reporter. -/
theorem primeJetOneStepTransport_eq_graph {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (y : Fin n → ℂ) :
    primeJetOneStepTransport r hr0 hr2inj y =
      primeJetZeroExtend n y +
        primeJetTailReporter r hr0 hr2inj y • Pi.single (Fin.last n) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [primeJetOneStepTransport_castSucc]

/-- Exact coefficient transmutation when one node is adjoined. -/
theorem primeJetOriginCoefficient_transmutation {n : ℕ} (hn : 0 < n)
    (r : Fin (n + 1) → ℂ) (hr0 : ∀ i, r i ≠ 0)
    (hr2inj : Function.Injective fun i => r i ^ 2) (i : Fin n) :
    fePairedOriginCoefficient (primeJetPrefixRadii r) i =
      fePairedOriginCoefficient r i.castSucc +
        fePairedOriginCoefficient r (Fin.last n) *
          primeJetTailReporter r hr0 hr2inj (Pi.single i 1) := by
  classical
  let ro := primeJetPrefixRadii r
  let hro0 := primeJetPrefixRadii_ne_zero hr0
  let hro2 := primeJetPrefixRadii_sq_injective hr2inj
  have hconserve := LinearMap.congr_fun
    (primeJetCoordinateReporter_oneStep r hr0 hr2inj) (Pi.single i 1)
  simp only [LinearMap.comp_apply] at hconserve
  rw [primeJetCoordinateReporter_eq_barycentric (Nat.succ_pos n) r hr0 hr2inj,
    primeJetCoordinateReporter_eq_barycentric hn ro hro0 hro2] at hconserve
  rw [Fin.sum_univ_castSucc] at hconserve
  simpa [ro, Pi.single_apply, primeJetOneStepTransport_castSucc] using hconserve.symm

/-- Locality defect equals one coefficient times the new terminal reporter. -/
theorem primeJetReporter_localityDefect {n : ℕ}
    (r : Fin (n + 1) → ℂ) (hr0 : ∀ i, r i ≠ 0)
    (hr2inj : Function.Injective fun i => r i ^ 2) :
    primeJetCoordinateReporter (primeJetPrefixRadii r)
        (primeJetPrefixRadii_ne_zero hr0) (primeJetPrefixRadii_sq_injective hr2inj) -
      (primeJetCoordinateReporter r hr0 hr2inj).comp (primeJetZeroExtend n) =
        fePairedOriginCoefficient r (Fin.last n) •
          primeJetTailReporter r hr0 hr2inj := by
  apply LinearMap.ext
  intro y
  let ro := primeJetPrefixRadii r
  let hro0 := primeJetPrefixRadii_ne_zero hr0
  let hro2 := primeJetPrefixRadii_sq_injective hr2inj
  have hconserve := LinearMap.congr_fun
    (primeJetCoordinateReporter_oneStep r hr0 hr2inj) y
  simp only [LinearMap.comp_apply] at hconserve
  have hgraph := primeJetOneStepTransport_eq_graph r hr0 hr2inj y
  have hlast : primeJetCoordinateReporter r hr0 hr2inj (Pi.single (Fin.last n) 1) =
      fePairedOriginCoefficient r (Fin.last n) := by
    rw [primeJetCoordinateReporter_eq_barycentric (Nat.succ_pos n)]
    simp [Pi.single_apply]
  change primeJetCoordinateReporter ro hro0 hro2 y -
      primeJetCoordinateReporter r hr0 hr2inj (primeJetZeroExtend n y) = _
  rw [← hconserve, hgraph, map_add, map_smul, hlast]
  simp
  ring

/-! ## Explicit Lagrange tail -/

/-- Barycentric coefficient of the newly formed terminal sample. -/
def primeJetTailWeight {n : ℕ} (r : Fin (n + 1) → ℂ) (i : Fin n) : ℂ :=
  (r (Fin.last n) / r i.castSucc) *
    (Lagrange.basis Finset.univ (fun j : Fin n => r j.castSucc ^ 2) i).eval
      (r (Fin.last n) ^ 2)

/-- Explicit Lagrange formula `τᵢ=(r*/rᵢ)Lᵢ(r*²)` for the terminal reporter. -/
theorem primeJetTailReporter_eq_sum {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (y : Fin n → ℂ) :
    primeJetTailReporter r hr0 hr2inj y =
      ∑ i : Fin n, primeJetTailWeight r i * y i := by
  classical
  let ro := primeJetPrefixRadii r
  let hro0 := primeJetPrefixRadii_ne_zero hr0
  let hro2 := primeJetPrefixRadii_sq_injective hr2inj
  let Q := (primeJetSampleEquiv ro hro0 hro2).symm y
  have hy := (primeJetSampleEquiv ro hro0 hro2).apply_symm_apply y
  have hdeg : Q.1.degree <
      (((Finset.univ : Finset (Fin n)).card : ℕ) : WithBot ℕ) := by
    simpa using (Polynomial.mem_degreeLT.mp Q.2)
  have hpoly := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin n)))
    (v := fun i => ro i ^ 2) hro2.injOn hdeg
  have heval := congrArg (Polynomial.eval (r (Fin.last n) ^ 2)) hpoly
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at heval
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
  change 2 * r (Fin.last n) * Q.1.eval (r (Fin.last n) ^ 2) = _
  calc
    2 * r (Fin.last n) * Q.1.eval (r (Fin.last n) ^ 2) =
        2 * r (Fin.last n) *
          ∑ i : Fin n, Q.1.eval (ro i ^ 2) *
            (Lagrange.basis Finset.univ (fun j : Fin n => ro j ^ 2) i).eval
              (r (Fin.last n) ^ 2) := by rw [heval]
    _ = ∑ i : Fin n, primeJetTailWeight r i * y i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hyi := congrFun hy i
      change 2 * ro i * Q.1.eval (ro i ^ 2) = y i at hyi
      rw [← hyi]
      simp only [primeJetTailWeight, ro, primeJetPrefixRadii]
      field_simp [hr0 i.castSucc]

/-- Every terminal Lagrange coefficient is nonzero. -/
theorem primeJetTailWeight_ne_zero {n : ℕ} (r : Fin (n + 1) → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (i : Fin n) : primeJetTailWeight r i ≠ 0 := by
  classical
  apply mul_ne_zero (div_ne_zero (hr0 (Fin.last n)) (hr0 i.castSucc))
  rw [Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjlast : j.castSucc ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    have hjn : (j : ℕ) = n := by simpa using this
    exact (Nat.ne_of_lt j.isLt) hjn
  have hij : i ≠ j := Ne.symm hji
  have hcast : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_inj.mp h)
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact mul_ne_zero
    (inv_ne_zero (sub_ne_zero.mpr (hr2inj.ne hcast)))
    (sub_ne_zero.mpr (hr2inj.ne (Ne.symm hjlast)))

/-- For every nonempty prefix, terminal reporter is genuinely nonzero. -/
theorem primeJetTailReporter_ne_zero {n : ℕ} (hn : 0 < n)
    (r : Fin (n + 1) → ℂ) (hr0 : ∀ i, r i ≠ 0)
    (hr2inj : Function.Injective fun i => r i ^ 2) :
    primeJetTailReporter r hr0 hr2inj ≠ 0 := by
  let i : Fin n := ⟨0, hn⟩
  intro hzero
  have hi := LinearMap.congr_fun hzero (Pi.single i 1)
  simp only [LinearMap.zero_apply] at hi
  rw [primeJetTailReporter_eq_sum] at hi
  have hi0 : primeJetTailWeight r i = 0 := by
    simpa [i, Pi.single_apply] using hi
  exact primeJetTailWeight_ne_zero r hr0 hr2inj i hi0

/-- Locality defect is a nonzero rank-one functional for every nonempty prefix. -/
theorem primeJetReporter_localityDefect_ne_zero {n : ℕ} (hn : 0 < n)
    (r : Fin (n + 1) → ℂ) (hr0 : ∀ i, r i ≠ 0)
    (hr2inj : Function.Injective fun i => r i ^ 2) :
    primeJetCoordinateReporter (primeJetPrefixRadii r)
        (primeJetPrefixRadii_ne_zero hr0) (primeJetPrefixRadii_sq_injective hr2inj) -
      (primeJetCoordinateReporter r hr0 hr2inj).comp (primeJetZeroExtend n) ≠ 0 := by
  rw [primeJetReporter_localityDefect]
  exact smul_ne_zero
    (fePairedOriginCoefficient_ne_zero r hr2inj hr0 (Fin.last n))
    (primeJetTailReporter_ne_zero hn r hr0 hr2inj)

/-! ## Boundary-port transmutation -/

/-- Square-coordinate boundary factor vanishing at every old node. -/
def primeJetBoundaryFactor {n : ℕ} (r : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (r i ^ 2))

theorem primeJetBoundaryFactor_natDegree {n : ℕ} (r : Fin n → ℂ) :
    (primeJetBoundaryFactor r).natDegree = n := by
  classical
  calc
    (primeJetBoundaryFactor r).natDegree =
        ∑ i : Fin n, (Polynomial.X - Polynomial.C (r i ^ 2)).natDegree := by
      rw [primeJetBoundaryFactor,
        Polynomial.natDegree_prod _ _ (fun i _ => Polynomial.X_sub_C_ne_zero (r i ^ 2))]
    _ = ∑ _i : Fin n, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Polynomial.natDegree_X_sub_C (r i ^ 2)
    _ = n := by simp

theorem primeJetBoundaryFactor_ne_zero {n : ℕ} (r : Fin n → ℂ) :
    primeJetBoundaryFactor r ≠ 0 := by
  classical
  rw [primeJetBoundaryFactor]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero (r i ^ 2)

/-- The boundary odd law `z∏ᵢ(z²-rᵢ²)` in the next law space. -/
def primeJetBoundaryLaw {n : ℕ} (r : Fin n → ℂ) : PrimeJetOddLaw (n + 1) :=
  ⟨primeJetBoundaryFactor r, by
    apply Polynomial.mem_degreeLT.mpr
    exact (Polynomial.natDegree_lt_iff_degree_lt (primeJetBoundaryFactor_ne_zero r)).mp
      (by rw [primeJetBoundaryFactor_natDegree]; omega)⟩

/-- Old samples of a law in the enlarged law space. -/
def primeJetOldSampleMap {n : ℕ} (r : Fin n → ℂ) :
    PrimeJetOddLaw (n + 1) →ₗ[ℂ] (Fin n → ℂ) where
  toFun Q i := 2 * r i * Q.1.eval (r i ^ 2)
  map_add' Q S := by
    ext i
    simp
    ring
  map_smul' c Q := by
    ext i
    simp
    ring

/-- Boundary law is invisible to all old samples. -/
theorem primeJetOldSampleMap_boundaryLaw {n : ℕ} (r : Fin n → ℂ) :
    primeJetOldSampleMap r (primeJetBoundaryLaw r) = 0 := by
  classical
  ext i
  change 2 * r i * (primeJetBoundaryFactor r).eval (r i ^ 2) = 0
  apply mul_eq_zero_of_right
  rw [primeJetBoundaryFactor, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Boundary law has nonzero origin reporter when old radii are nonzero. -/
theorem primeJetOriginReporter_boundaryLaw_ne_zero {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) :
    primeJetOriginReporter (n + 1) (primeJetBoundaryLaw r) ≠ 0 := by
  classical
  change (primeJetBoundaryFactor r).eval 0 ≠ 0
  rw [primeJetBoundaryFactor, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (hr0 i))

/-- Enhanced old-sample chart with the derived origin port. -/
def primeJetEnhancedMap {n : ℕ} (r : Fin n → ℂ) :
    PrimeJetOddLaw (n + 1) →ₗ[ℂ] ((Fin n → ℂ) × ℂ) where
  toFun Q := (primeJetOldSampleMap r Q, primeJetOriginReporter (n + 1) Q)
  map_add' Q S := by simp
  map_smul' c Q := by simp

/-- Pair/prefix coordinates as a `Fin (n+1)` vector. -/
def primeJetPairEquiv (n : ℕ) : ((Fin n → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun yz := Fin.snoc yz.1 yz.2
  invFun v := (fun i => v i.castSucc, v (Fin.last n))
  left_inv yz := by
    apply Prod.ext
    · funext i
      simp
    · simp
  right_inv v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_add' yz uv := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c yz := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem primeJetEnhancedMap_injective {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    Function.Injective (primeJetEnhancedMap r) := by
  intro Q S hQS
  let D : PrimeJetOddLaw (n + 1) := Q - S
  have hzero : primeJetEnhancedMap r D = 0 := by
    rw [map_sub, hQS, sub_self]
  have hsamples : primeJetOldSampleMap r D = 0 := congrArg Prod.fst hzero
  have hreport : primeJetOriginReporter (n + 1) D = 0 := congrArg Prod.snd hzero
  let nodes : Fin (n + 1) → ℂ := Fin.snoc (fun i : Fin n => r i ^ 2) 0
  have hnodes : Function.Injective nodes := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
      · apply Fin.castSucc_inj.mpr
        apply hr2inj
        simpa [nodes] using hij
      · exfalso
        have ha0 : r a = 0 := by simpa [nodes] using hij
        exact hr0 a ha0
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
      · exfalso
        have hb0 : r b = 0 := by simpa [nodes] using hij.symm
        exact hr0 b hb0
      · rfl
  have heval : ∀ i : Fin (n + 1), D.1.eval (nodes i) = 0 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [primeJetOriginReporter, nodes] using hreport
    · have hj := congrFun hsamples j
      simp only [primeJetOldSampleMap, Pi.zero_apply] at hj
      have hr : 2 * r j ≠ 0 := mul_ne_zero (by norm_num) (hr0 j)
      have hz : D.1.eval (r j ^ 2) = 0 := (mul_eq_zero.mp hj).resolve_left hr
      simpa only [nodes, Fin.snoc_castSucc] using hz
  have hdeg : D.1.degree <
      (((Finset.univ : Finset (Fin (n + 1))).card : ℕ) : WithBot ℕ) := by
    simpa using (Polynomial.mem_degreeLT.mp D.2)
  have hinterp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin (n + 1)))) (v := nodes) hnodes.injOn hdeg
  have hD : D.1 = 0 := by
    rw [hinterp, Lagrange.interpolate_apply]
    simp [heval]
  apply Subtype.ext
  change Q.1 - S.1 = 0 at hD
  exact sub_eq_zero.mp hD

/-- Enhanced old-sample/reporter map is a linear equivalence. -/
def primeJetEnhancedEquiv {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2) :
    PrimeJetOddLaw (n + 1) ≃ₗ[ℂ] ((Fin n → ℂ) × ℂ) := by
  let E := Polynomial.degreeLTEquiv ℂ (n + 1)
  let P := primeJetPairEquiv n
  let F := P.toLinearMap.comp ((primeJetEnhancedMap r).comp E.symm.toLinearMap)
  have hFinj : Function.Injective F :=
    P.injective.comp ((primeJetEnhancedMap_injective r hr0 hr2inj).comp E.symm.injective)
  have hFsurj : Function.Surjective F := LinearMap.surjective_of_injective hFinj
  have hsurj : Function.Surjective (primeJetEnhancedMap r) := by
    intro yz
    obtain ⟨x, hx⟩ := hFsurj (P yz)
    refine ⟨E.symm x, P.injective ?_⟩
    exact hx
  exact LinearEquiv.ofBijective (primeJetEnhancedMap r)
    ⟨primeJetEnhancedMap_injective r hr0 hr2inj, hsurj⟩

/-- Old-sample kernel is exactly the boundary-law line. -/
theorem primeJetOldSampleMap_eq_zero_iff {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (Q : PrimeJetOddLaw (n + 1)) :
    primeJetOldSampleMap r Q = 0 ↔
      ∃ c : ℂ, Q = c • primeJetBoundaryLaw r := by
  constructor
  · intro hQ
    let B := primeJetBoundaryLaw r
    let b := primeJetOriginReporter (n + 1) B
    have hb : b ≠ 0 := primeJetOriginReporter_boundaryLaw_ne_zero r hr0
    let c := primeJetOriginReporter (n + 1) Q / b
    refine ⟨c, ?_⟩
    apply primeJetEnhancedMap_injective r hr0 hr2inj
    apply Prod.ext
    · change primeJetOldSampleMap r Q = primeJetOldSampleMap r (c • B)
      rw [map_smul, primeJetOldSampleMap_boundaryLaw, smul_zero, hQ]
    · change primeJetOriginReporter (n + 1) Q =
        primeJetOriginReporter (n + 1) (c • B)
      rw [map_smul]
      change primeJetOriginReporter (n + 1) Q = c * b
      dsimp [c]
      field_simp
  · rintro ⟨c, rfl⟩
    rw [map_smul, primeJetOldSampleMap_boundaryLaw, smul_zero]

theorem primeJetOldSampleMap_inclusion {n : ℕ} (r : Fin n → ℂ)
    (Q : PrimeJetOddLaw n) :
    primeJetOldSampleMap r (primeJetLawInclusion (Nat.le_succ n) Q) =
      primeJetSampleMap r Q := by
  ext i
  change 2 * r i * (primeJetLawInclusion (Nat.le_succ n) Q).1.eval (r i ^ 2) =
    2 * r i * Q.1.eval (r i ^ 2)
  rw [primeJetLawInclusion_apply]

/-- Old law space lands as graph of its conserved reporter in enhanced coordinates. -/
theorem primeJetEnhancedMap_inclusion_graph {n : ℕ} (r : Fin n → ℂ)
    (hr0 : ∀ i, r i ≠ 0) (hr2inj : Function.Injective fun i => r i ^ 2)
    (y : Fin n → ℂ) :
    primeJetEnhancedMap r
        (primeJetLawInclusion (Nat.le_succ n)
          ((primeJetSampleEquiv r hr0 hr2inj).symm y)) =
      (y, primeJetCoordinateReporter r hr0 hr2inj y) := by
  apply Prod.ext
  · change primeJetOldSampleMap r
      (primeJetLawInclusion (Nat.le_succ n)
        ((primeJetSampleEquiv r hr0 hr2inj).symm y)) = y
    rw [primeJetOldSampleMap_inclusion]
    exact (primeJetSampleEquiv r hr0 hr2inj).apply_symm_apply y
  · change primeJetOriginReporter (n + 1)
      (primeJetLawInclusion (Nat.le_succ n)
        ((primeJetSampleEquiv r hr0 hr2inj).symm y)) =
      primeJetOriginReporter n ((primeJetSampleEquiv r hr0 hr2inj).symm y)
    simp [primeJetOriginReporter, primeJetLawInclusion_apply]

end

end GaloisForLFunctions.HTGeometry
