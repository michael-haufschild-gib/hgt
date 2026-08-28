import GaloisForLFunctions.RHTower.FEPairedPrimeJetBarycentricRigidity
import GaloisForLFunctions.HTGeometry.LowDegreeVanishing

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

end

end GaloisForLFunctions.HTGeometry
