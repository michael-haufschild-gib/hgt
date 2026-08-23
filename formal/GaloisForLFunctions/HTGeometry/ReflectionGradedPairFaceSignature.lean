import GaloisForLFunctions.HTGeometry.AllDepthOperatorCriterion
import GaloisForLFunctions.HTGeometry.AllDepthCompleteness
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorClassFunction

/-!
# Reflection-graded complete pair-face signature

Functional-equation reflection acts on every all-depth pair-face signature through affine
principal-part reflection together with reversal of the orbital boundary orientation.  The latter
contributes an extra minus sign missing from the paper draft's provisional convention.

This module proves the corrected component action, its involutivity, exact fixed-submodule image,
the differentially algebraic kernel on the reflection-fixed class, and a concrete nonzero fixed
signature realized at two distinct prime-log periods.
-/

open Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

theorem taylorCoeffZero_const_mul_comp_neg (g : ℂ → ℂ) (c : ℂ) (m : ℕ) :
    taylorCoeffZero (fun t => c * g (-t)) m =
      c * (-1 : ℂ) ^ m * taylorCoeffZero g m := by
  simp only [taylorCoeffZero, iteratedDeriv_const_mul_field]
  have hneg : (fun t : ℂ => g (-t)) = fun t => g ((-1 : ℂ) * t) := by
    funext t
    congr 1
    ring
  rw [hneg, iteratedDeriv_comp_mul_left_uncond]
  simp
  ring

theorem laurentCoeff_comp_const_sub_negSucc
    (f : ℂ → ℂ) (a c : ℂ) (n : ℕ) (hf : MeromorphicAt f (c - a)) :
    laurentCoeff (fun z => f (c - z)) a (-((n : ℤ) + 1)) =
      (-1 : ℂ) ^ (n + 1) * laurentCoeff f (c - a) (-((n : ℤ) + 1)) := by
  obtain ⟨k, hkN, hk⟩ :=
    exists_analyticAt_laurentShift_ge hf (n + 1)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkN
  have hshift :
      laurentShift (fun z => f (c - z)) a (n + 1 + j) =
        fun t => (-1 : ℂ) ^ (n + 1 + j) *
          laurentShift f (c - a) (n + 1 + j) (-t) := by
    funext t
    simp only [laurentShift]
    rw [neg_pow t]
    have hs : (-1 : ℂ) ^ (n + 1 + j) * (-1) ^ (n + 1 + j) = 1 := by
      rw [← pow_add]
      simp [show (n + 1 + j) + (n + 1 + j) = 2 * (n + 1 + j) by omega,
        pow_mul]
    have hfactor : (-1 : ℂ) ^ (n + 1 + j) *
        ((-1) ^ (n + 1 + j) * t ^ (n + 1 + j) * f (c - a + -t)) =
        t ^ (n + 1 + j) * f (c - a + -t) := by
      calc
        _ = ((-1 : ℂ) ^ (n + 1 + j) * (-1) ^ (n + 1 + j)) *
            (t ^ (n + 1 + j) * f (c - a + -t)) := by ring
        _ = _ := by rw [hs, one_mul]
    rw [hfactor]
    exact congrArg (fun u : ℂ => t ^ (n + 1 + j) * f u) (by ring)
  have hrefAnalytic : AnalyticAt ℂ
      (laurentShift (fun z => f (c - z)) a (n + 1 + j)) 0 := by
    rw [hshift]
    have hneg : AnalyticAt ℂ (fun t : ℂ => -t) 0 := by fun_prop
    have hcomp : AnalyticAt ℂ
        (fun t : ℂ => laurentShift f (c - a) (n + 1 + j) (-t)) 0 := by
      exact AnalyticAt.comp (g := laurentShift f (c - a) (n + 1 + j))
        (f := fun t : ℂ => -t) (x := (0 : ℂ)) (by simpa using hk) hneg
    exact analyticAt_const.mul hcomp
  rw [laurentCoeff_eq_taylorCoeffZero hrefAnalytic (by push_cast; omega),
    laurentCoeff_eq_taylorCoeffZero hk (by push_cast; omega), hshift,
    taylorCoeffZero_const_mul_comp_neg]
  have hidx : (-((n : ℤ) + 1) + ((n + 1 + j : ℕ) : ℤ)).toNat = j := by
    push_cast
    omega
  rw [hidx]
  have hj : (-1 : ℂ) ^ j * (-1) ^ j = 1 := by
    rw [← pow_add]
    simp [show j + j = 2 * j by omega, pow_mul]
  change (-1 : ℂ) ^ (n + 1 + j) * (-1) ^ j *
      taylorCoeffZero (laurentShift f (c - a) (n + 1 + j)) j =
    (-1) ^ (n + 1) * taylorCoeffZero (laurentShift f (c - a) (n + 1 + j)) j
  rw [pow_add]
  calc
    ((-1 : ℂ) ^ (n + 1) * (-1) ^ j) * (-1) ^ j *
          taylorCoeffZero (laurentShift f (c - a) (n + 1 + j)) j =
        (-1) ^ (n + 1) * (((-1) ^ j * (-1) ^ j) *
          taylorCoeffZero (laurentShift f (c - a) (n + 1 + j)) j) := by ring
    _ = _ := by rw [hj, one_mul]

theorem laurentCoeff_neg {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (ℓ : ℤ) :
    laurentCoeff (fun z => -f z) a ℓ = -laurentCoeff f a ℓ := by
  have hzero : MeromorphicAt (fun _ : ℂ => (0 : ℂ)) a := by fun_prop
  have hfun : (fun z => -f z) = fun z => (0 : ℂ) - f z := by funext z; simp
  rw [hfun, laurentCoeff_sub hzero hf]
  have hz : laurentCoeff (fun _ : ℂ => (0 : ℂ)) a ℓ = 0 := by
    have h := laurentCoeff_sum (∅ : Finset (Fin 0))
      (fun _ : Fin 0 => fun _ : ℂ => (0 : ℂ)) (fun _ => (0 : ℂ)) a ℓ (by simp)
    simpa using h
  rw [hz, zero_sub]

theorem additiveOrbitalDivisorAt_comp_const_sub_negSucc
    (F : ℂ → ℂ) (hF : MeromorphicOn F Set.univ) (σ p c : ℂ) (n : ℕ) :
    additiveOrbitalDivisorAt (fun z => F (c - z)) σ p (-((n : ℤ) + 1)) =
      -((-1 : ℂ) ^ (n + 1)) *
        additiveOrbitalDivisorAt F σ (c - p) (-((n : ℤ) + 1)) := by
  let H : ℂ → ℂ := fun z => F (z + σ) - F z
  have hH : MeromorphicOn H Set.univ := by
    intro z hz
    exact (meromorphicAt_comp_add.mpr (hF (z + σ) (Set.mem_univ _))).sub
      (hF z (Set.mem_univ _))
  have hboundary : (fun z => F (c - (z + σ)) - F (c - z)) =
      fun z => -(H ((c - σ) - z)) := by
    funext z
    simp only [H]
    ring_nf
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z => F (c - (z + σ)) - F (c - z))
          (p + (m : ℂ) * σ) (-((n : ℤ) + 1)) =
        -((-1 : ℂ) ^ (n + 1)) *
          laurentCoeff H ((c - p) + ((-m - 1 : ℤ) : ℂ) * σ) (-((n : ℤ) + 1)) := by
    intro m
    rw [hboundary]
    have href := laurentCoeff_comp_const_sub_negSucc
      (f := fun z => -H z) (a := p + (m : ℂ) * σ) (c := c - σ) n
      ((hH ((c - σ) - (p + (m : ℂ) * σ)) (Set.mem_univ _)).neg)
    rw [href, laurentCoeff_neg
      (hH ((c - σ) - (p + (m : ℂ) * σ)) (Set.mem_univ _))]
    have hpoint : (c - σ) - (p + (m : ℂ) * σ) =
        (c - p) + ((-m - 1 : ℤ) : ℂ) * σ := by
      push_cast
      ring
    rw [hpoint]
    ring
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, finsum_congr hterm,
    ← mul_finsum]
  congr 1
  let e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.addRight (-1))
  have he (m : ℤ) : e m = -m - 1 := by simp [e]; omega
  have hre := finsum_comp_equiv e
    (f := fun m : ℤ => laurentCoeff H ((c - p) + (m : ℂ) * σ) (-((n : ℤ) + 1)))
  simpa only [he] using hre

theorem meromorphicOn_comp_const_sub {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (c : ℂ) :
    MeromorphicOn (fun z => F (c - z)) Set.univ := by
  intro z hz
  change MeromorphicAt (F ∘ fun w : ℂ => c - w) z
  exact MeromorphicAt.comp_analyticAt (hF (c - z) (Set.mem_univ _)) (by fun_prop)

theorem diffCube_comp_const_sub {ι : Type*} [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (F : ℂ → ℂ) (c : ℂ) :
    HTGeometry.diffCube τ s (fun z => F (c - z)) =
      fun z => (-1 : ℂ) ^ s.card *
        HTGeometry.diffCube τ s F (c - (∑ i ∈ s, τ i) - z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert q s hq ih =>
      rw [HTGeometry.diffCube_insert τ hq, ih, HTGeometry.diffCube_insert τ hq]
      funext z
      simp only [HTGeometry.shiftDiffFun, Finset.card_insert_of_notMem hq,
        Finset.sum_insert hq, pow_succ]
      ring_nf

theorem pairFaceWitnessFun_comp_one_sub {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (i j : ι) (F : ℂ → ℂ) :
    pairFaceWitnessFun (ι := ι) τ s i j (fun z => F (1 - z)) =
      fun z => (-1 : ℂ) ^ (s \ {i, j}).card *
        pairFaceWitnessFun (ι := ι) τ s i j F
          (1 - (∑ k ∈ s \ {i, j}, τ k) - z) := by
  simpa only [pairFaceWitnessFun] using
    diffCube_comp_const_sub τ (s \ {i, j}) F 1

/-- Correct component action: principal-part parity and orbit-orientation reversal. -/
def pairSigReflection {ι : Type} [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (D : ι → ι → ℤ → ℂ → ℂ) :
    ι → ι → ℤ → ℂ → ℂ :=
  fun i j ℓ p =>
    -(((-1 : ℂ) ^ (s \ {i, j}).card) * (-1 : ℂ) ^ ℓ.natAbs) *
      D i j ℓ (1 - (∑ k ∈ s \ {i, j}, τ k) - p)

theorem pairSig_comp_one_sub {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (i j : ι) {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (n : ℕ) (p : ℂ) :
    pairSig (ι := ι) τ s (fun z => F (1 - z)) i j (-((n : ℤ) + 1)) p =
      pairSigReflection τ s
        (fun (i j : ι) (ℓ : ℤ) (p : ℂ) => pairSig (ι := ι) τ s F i j ℓ p)
        i j (-((n : ℤ) + 1)) p := by
  let t : Finset ι := s \ {i, j}
  let W : ℂ → ℂ := pairFaceWitnessFun (ι := ι) τ s i j F
  let c : ℂ := 1 - ∑ k ∈ t, τ k
  have hW : MeromorphicOn W Set.univ := meromorphicOn_diffCube τ t hF
  have hRefW : MeromorphicOn (fun z => W (c - z)) Set.univ :=
    meromorphicOn_comp_const_sub hW c
  rw [pairSig, pairFaceWitnessFun_comp_one_sub]
  change additiveOrbitalDivisorAt
      (fun z => (-1 : ℂ) ^ t.card * W (c - z)) (τ i) p (-((n : ℤ) + 1)) = _
  rw [additiveOrbitalDivisorAt_const_mul hRefW,
    additiveOrbitalDivisorAt_comp_const_sub_negSucc W hW]
  have habs : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
  simp only [pairSigReflection, t, c, habs]
  change (-1 : ℂ) ^ t.card *
      (-((-1 : ℂ) ^ (n + 1)) * pairSig τ s F i j (-((n : ℤ) + 1)) (c - p)) =
    -((-1 : ℂ) ^ t.card * (-1 : ℂ) ^ (n + 1)) *
      pairSig τ s F i j (-((n : ℤ) + 1)) (c - p)
  ring

theorem pairSig_comp_one_sub_of_neg {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (i j : ι) {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    pairSig τ s (fun z => F (1 - z)) i j ℓ p =
      pairSigReflection τ s
        (fun (i j : ι) (ℓ : ℤ) (p : ℂ) => pairSig τ s F i j ℓ p) i j ℓ p := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, ℓ = -((n : ℤ) + 1) :=
    ⟨(-ℓ - 1).toNat, by omega⟩
  exact pairSig_comp_one_sub τ s i j hF n p

theorem pairSigReflection_involutive {ι : Type} [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (D : ι → ι → ℤ → ℂ → ℂ)
    (i j : ι) (ℓ : ℤ) (p : ℂ) :
    pairSigReflection τ s (pairSigReflection τ s D) i j ℓ p = D i j ℓ p := by
  classical
  simp only [pairSigReflection]
  have hs : (-1 : ℂ) ^ (s \ {i, j}).card * (-1 : ℂ) ^ ℓ.natAbs *
      ((-1) ^ (s \ {i, j}).card * (-1) ^ ℓ.natAbs) = 1 := by
    have h1 : (-1 : ℂ) ^ (s \ {i, j}).card * (-1) ^ (s \ {i, j}).card = 1 := by
      rw [← pow_add]
      simp [show (s \ {i, j}).card + (s \ {i, j}).card =
        2 * (s \ {i, j}).card by omega, pow_mul]
    have h2 : (-1 : ℂ) ^ ℓ.natAbs * (-1) ^ ℓ.natAbs = 1 := by
      rw [← pow_add]
      simp [show ℓ.natAbs + ℓ.natAbs = 2 * ℓ.natAbs by omega, pow_mul]
    calc
      _ = ((-1 : ℂ) ^ (s \ {i, j}).card * (-1) ^ (s \ {i, j}).card) *
          ((-1) ^ ℓ.natAbs * (-1) ^ ℓ.natAbs) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hp : 1 - (∑ k ∈ s \ {i, j}, τ k) -
      (1 - (∑ k ∈ s \ {i, j}, τ k) - p) = p := by ring
  rw [hp]
  let A : ℂ := (-1 : ℂ) ^ (s \ {i, j}).card * (-1) ^ ℓ.natAbs
  change -A * (-A * D i j ℓ p) = D i j ℓ p
  calc
    _ = (A * A) * D i j ℓ p := by ring
    _ = _ := by rw [show A * A = 1 by simpa [A] using hs, one_mul]

theorem periodicOneGerm_comp_one_sub {F : ℂ → ℂ}
    (hF : PeriodicOneGerm F) : PeriodicOneGerm (fun z => F (1 - z)) := by
  intro z
  have hper : ∀ᶠ w in 𝓝[≠] (0 - z), F (w + 1) = F w := by
    simpa using hF (-z)
  have hpull := (tendsto_nhdsNE_const_sub z 0).eventually hper
  filter_upwards [hpull] with w hw
  have hleft : 1 - (w + 1) = -w := by ring
  have hright : 1 - w = -w + 1 := by ring
  rw [hleft, hright]
  simpa only [zero_sub] using hw.symm

theorem mixedConstGermSet_comp_one_sub {ι : Type*} [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) {F : ℂ → ℂ} {Cst : ℂ}
    (hF : MixedConstGermSet τ s F Cst) :
    MixedConstGermSet τ s (fun z => F (1 - z)) ((-1 : ℂ) ^ s.card * Cst) := by
  classical
  intro z
  let c : ℂ := 1 - ∑ i ∈ s, τ i
  have hpull := (tendsto_nhdsNE_const_sub z c).eventually (hF (c - z))
  filter_upwards [hpull] with w hw
  rw [congrFun (diffCube_comp_const_sub τ s F 1) w, hw]

/-- Exact compatibility conditions in the all-depth pair-face image theorem. -/
def PairSigAdmissible {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (D : ι → ι → ℤ → ℂ → ℂ) : Prop :=
  (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 →
      DivInvariant (tripticPeriodGroup (τ j) (τ i)) (D i j ℓ)) ∧
  (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 →
      DivFiniteClasses (tripticPeriodGroup (τ j) (τ i)) (D i j ℓ)) ∧
  (∃ N : ℕ, ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < -(N : ℤ) →
      ∀ p, D i j ℓ p = 0) ∧
  (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → D i j ℓ = D j i ℓ) ∧
  (∀ i ∈ s, ∀ j ∈ s, ∀ l ∈ s, i ≠ j → i ≠ l → j ≠ l →
      ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
        (∑ᶠ n : ℤ, D i j ℓ (p + (n : ℂ) * τ l)) =
          ∑ᶠ n : ℤ, D i l ℓ (p + (n : ℂ) * τ j))

/-- Fixed points of the corrected twisted component reflection on every active pair. -/
def PairSigReflectionFixed {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (D : ι → ι → ℤ → ℂ → ℂ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
    pairSigReflection τ s D i j ℓ p = D i j ℓ p

/-- A compatible signature realized by a reflection-symmetric member of the mixed class. -/
def ReflectionSymmetricPairSigRealizable {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (s : Finset ι) (D : ι → ι → ℤ → ℂ → ℂ) : Prop :=
  ∃ (F : ℂ → ℂ) (Cst : ℂ),
    MeromorphicOn F Set.univ ∧ PeriodicOneGerm F ∧ MixedConstGermSet τ s F Cst ∧
    (∀ z : ℂ, F (1 - z) = F z) ∧
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
      pairSig τ s F i j ℓ p = D i j ℓ p

/-- Characteristic-zero averaging over the functional-equation reflection. -/
def reflectionAverage (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (2 : ℂ)⁻¹ * (F z + F (1 - z))

theorem reflectionAverage_one_sub (F : ℂ → ℂ) (z : ℂ) :
    reflectionAverage F (1 - z) = reflectionAverage F z := by
  simp only [reflectionAverage]
  rw [show 1 - (1 - z) = z by ring]
  ring

theorem pairSig_realizable_iff_admissible {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im) (hQ : PeriodsIntegrallyIndependent τ)
    (s : Finset ι) (hs : 2 ≤ s.card) (D : ι → ι → ℤ → ℂ → ℂ) :
    (∃ (F : ℂ → ℂ) (Cst : ℂ),
        MeromorphicOn F Set.univ ∧ PeriodicOneGerm F ∧ MixedConstGermSet τ s F Cst ∧
        ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
          pairSig τ s F i j ℓ p = D i j ℓ p) ↔ PairSigAdmissible τ s D := by
  simpa only [PairSigAdmissible] using
    exists_class_member_with_prescribed_pairSig_iff τ hτ hQ s hs D

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 900000 in
/-- Exact fixed-submodule image of reflection-symmetric all-depth constrained functions. -/
theorem reflectionSymmetricPairSigRealizable_iff
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im) (hQ : PeriodsIntegrallyIndependent τ)
    (s : Finset ι) (hs : 2 ≤ s.card) (D : ι → ι → ℤ → ℂ → ℂ) :
    ReflectionSymmetricPairSigRealizable τ s D ↔
      PairSigAdmissible τ s D ∧ PairSigReflectionFixed τ s D := by
  classical
  constructor
  · rintro ⟨F, Cst, hmero, hper, hmixed, hsymm, hsig⟩
    have hadm : PairSigAdmissible τ s D :=
      (pairSig_realizable_iff_admissible τ hτ hQ s hs D).mp
        ⟨F, Cst, hmero, hper, hmixed, hsig⟩
    refine ⟨hadm, ?_⟩
    intro i hi j hj hij ℓ hℓ p
    have href := pairSig_comp_one_sub_of_neg τ s i j hmero hℓ p
    have hfun : (fun z => F (1 - z)) = F := funext hsymm
    rw [hfun] at href
    calc
      pairSigReflection τ s D i j ℓ p =
          pairSigReflection τ s
            (fun (i j : ι) (ℓ : ℤ) (p : ℂ) => pairSig τ s F i j ℓ p) i j ℓ p := by
        simp only [pairSigReflection]
        rw [hsig i hi j hj hij ℓ hℓ]
      _ = pairSig τ s F i j ℓ p := href.symm
      _ = D i j ℓ p := hsig i hi j hj hij ℓ hℓ p
  · rintro ⟨hadm, hfixed⟩
    obtain ⟨F, Cst, hmero, hper, hmixed, hsig⟩ :=
      (pairSig_realizable_iff_admissible τ hτ hQ s hs D).mpr hadm
    let RF : ℂ → ℂ := fun z => F (1 - z)
    let A : ℂ → ℂ := reflectionAverage F
    have hRFmero : MeromorphicOn RF Set.univ := meromorphicOn_comp_const_sub hmero 1
    have hRFper : PeriodicOneGerm RF := periodicOneGerm_comp_one_sub hper
    have hRFmixed : MixedConstGermSet τ s RF ((-1 : ℂ) ^ s.card * Cst) :=
      mixedConstGermSet_comp_one_sub τ s hmixed
    have hsumMero : MeromorphicOn (fun z => F z + RF z) Set.univ := by
      intro z hz
      exact (hmero z (Set.mem_univ _)).add (hRFmero z (Set.mem_univ _))
    have hAmero : MeromorphicOn A Set.univ := by
      intro z hz
      exact analyticAt_const.meromorphicAt.mul (hsumMero z (Set.mem_univ _))
    have hAper : PeriodicOneGerm A :=
      periodicOneGerm_const_mul'
        (periodicOneGerm_add hper hRFper) (2 : ℂ)⁻¹
    have hAmixed : MixedConstGermSet τ s A
        ((2 : ℂ)⁻¹ * (Cst + (-1 : ℂ) ^ s.card * Cst)) :=
      mixedConstGermSet_const_mul τ s
        (mixedConstGermSet_add τ s hmixed hRFmixed) (2 : ℂ)⁻¹
    refine ⟨A, (2 : ℂ)⁻¹ * (Cst + (-1 : ℂ) ^ s.card * Cst),
      hAmero, hAper, hAmixed, ?_, ?_⟩
    · exact reflectionAverage_one_sub F
    · intro i hi j hj hij ℓ hℓ p
      have hRFsig : pairSig τ s RF i j ℓ p = D i j ℓ p := by
        calc
          pairSig τ s RF i j ℓ p =
              pairSigReflection τ s
                (fun (i j : ι) (ℓ : ℤ) (p : ℂ) => pairSig τ s F i j ℓ p)
                i j ℓ p := pairSig_comp_one_sub_of_neg τ s i j hmero hℓ p
          _ = pairSigReflection τ s D i j ℓ p := by
            simp only [pairSigReflection]
            rw [hsig i hi j hj hij ℓ hℓ]
          _ = D i j ℓ p := hfixed i hi j hj hij ℓ hℓ p
      change pairSig τ s (fun z => (2 : ℂ)⁻¹ * (F z + RF z)) i j ℓ p = D i j ℓ p
      rw [pairSig_const_mul τ s i j hsumMero (2 : ℂ)⁻¹ ℓ p,
        pairSig_add τ hτ hQ s hij hi hj hmero hper hmixed hRFmero hRFper hRFmixed hℓ p,
        hsig i hi j hj hij ℓ hℓ p, hRFsig]
      ring

noncomputable def depthTwoReflectionClassDivisor (τ : Bool → ℂ) :
    Bool → Bool → ℤ → ℂ → ℂ := by
  classical
  exact fun i j ℓ p =>
    if ℓ = -1 ∧ p - (1 / 2 : ℂ) ∈ tripticPeriodGroup (τ j) (τ i) then 1 else 0

theorem depthTwoReflectionClassDivisor_admissible (τ : Bool → ℂ) :
    PairSigAdmissible τ Finset.univ (depthTwoReflectionClassDivisor τ) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij ℓ hℓ p g hg
    have hmem : p + g - (1 / 2 : ℂ) ∈ tripticPeriodGroup (τ j) (τ i) ↔
        p - (1 / 2 : ℂ) ∈ tripticPeriodGroup (τ j) (τ i) := by
      constructor
      · intro h
        have heq : p - (1 / 2 : ℂ) = (p + g - (1 / 2 : ℂ)) + (-g) := by ring
        rw [heq]
        exact AddSubgroup.add_mem _ h (AddSubgroup.neg_mem _ hg)
      · intro h
        have heq : p + g - (1 / 2 : ℂ) = (p - (1 / 2 : ℂ)) + g := by ring
        rw [heq]
        exact AddSubgroup.add_mem _ h hg
    simp only [depthTwoReflectionClassDivisor, hmem]
  · intro i hi j hj hij ℓ hℓ
    refine ⟨{(1 / 2 : ℂ)}, ?_⟩
    intro p hp
    by_cases hcond : ℓ = -1 ∧ p - (1 / 2 : ℂ) ∈ tripticPeriodGroup (τ j) (τ i)
    · exact ⟨(1 / 2 : ℂ), by simp, hcond.2⟩
    · rw [depthTwoReflectionClassDivisor, if_neg hcond] at hp
      exact (hp rfl).elim
  · refine ⟨1, ?_⟩
    intro i hi j hj hij ℓ hℓ p
    have hne : ℓ ≠ -1 := by omega
    simp [depthTwoReflectionClassDivisor, hne]
  · intro i hi j hj hij ℓ hℓ
    funext p
    simp only [depthTwoReflectionClassDivisor]
    rw [tripticPeriodGroup_comm (τ j) (τ i)]
  · intro i hi j hj l hl hij hil hjl ℓ hℓ p
    cases i <;> cases j <;> cases l <;> simp_all

theorem half_reflection_class_mem_iff (H : AddSubgroup ℂ) (p : ℂ) :
    (1 - p) - (1 / 2 : ℂ) ∈ H ↔ p - (1 / 2 : ℂ) ∈ H := by
  have heq : (1 - p) - (1 / 2 : ℂ) = -(p - (1 / 2 : ℂ)) := by ring
  rw [heq]
  exact H.neg_mem_iff

theorem depthTwoReflectionClassDivisor_fixed (τ : Bool → ℂ) :
    PairSigReflectionFixed τ Finset.univ (depthTwoReflectionClassDivisor τ) := by
  classical
  intro i hi j hj hij ℓ hℓ p
  have ht : (Finset.univ : Finset Bool) \ {i, j} = ∅ := by
    ext k
    cases i <;> cases j <;> cases k <;> simp_all
  by_cases horder : ℓ = -1
  · subst ℓ
    have hD : depthTwoReflectionClassDivisor τ i j (-1) (1 - p) =
        depthTwoReflectionClassDivisor τ i j (-1) p := by
      simp only [depthTwoReflectionClassDivisor, true_and]
      rw [half_reflection_class_mem_iff]
    rw [pairSigReflection, ht, Finset.card_empty, Finset.sum_empty,
      show 1 - 0 - p = 1 - p by ring, hD]
    norm_num
  · have hD1 : depthTwoReflectionClassDivisor τ i j ℓ
        (1 - (∑ k ∈ (Finset.univ : Finset Bool) \ {i, j}, τ k) - p) = 0 := by
      simp [depthTwoReflectionClassDivisor, horder]
    have hD2 : depthTwoReflectionClassDivisor τ i j ℓ p = 0 := by
      simp [depthTwoReflectionClassDivisor, horder]
    rw [pairSigReflection, hD1, hD2]
    simp

theorem depthTwoReflectionClassDivisor_half (τ : Bool → ℂ) :
    depthTwoReflectionClassDivisor τ false true (-1) (1 / 2 : ℂ) = 1 := by
  simp [depthTwoReflectionClassDivisor]

def reflectionPairPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

def reflectionPairPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

def reflectionPrimePair : Bool → Nat.Primes :=
  fun b => if b then reflectionPairPrimeTwo else reflectionPairPrimeThree

def reflectionPairPeriods : Bool → ℂ := logPrimePeriod reflectionPrimePair

theorem reflectionPrimePair_injective : Function.Injective reflectionPrimePair := by
  intro i j hij
  cases i <;> cases j
  · rfl
  · have hv := congrArg Subtype.val hij
    norm_num [reflectionPrimePair, reflectionPairPrimeTwo, reflectionPairPrimeThree] at hv
  · have hv := congrArg Subtype.val hij
    norm_num [reflectionPrimePair, reflectionPairPrimeTwo, reflectionPairPrimeThree] at hv
  · rfl

theorem reflectionPairPeriods_im_pos (i : Bool) : 0 < (reflectionPairPeriods i).im :=
  logPrimePeriod_im_pos reflectionPrimePair i

theorem reflectionPairPeriods_integrallyIndependent :
    PeriodsIntegrallyIndependent reflectionPairPeriods :=
  periodsIntegrallyIndependent_logPrimePeriod reflectionPrimePair_injective

/-- A concrete nonzero fixed signature and its reflection-symmetric constrained realization. -/
theorem exists_reflectionSymmetric_depthTwo_nonzero_pairSig :
    ∃ (F : ℂ → ℂ) (Cst : ℂ),
      MeromorphicOn F Set.univ ∧ PeriodicOneGerm F ∧
      MixedConstGermSet reflectionPairPeriods Finset.univ F Cst ∧
      (∀ z : ℂ, F (1 - z) = F z) ∧
      (∀ i : Bool, ∀ j : Bool, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
        pairSig reflectionPairPeriods Finset.univ F i j ℓ p =
          depthTwoReflectionClassDivisor reflectionPairPeriods i j ℓ p) ∧
      pairSig reflectionPairPeriods Finset.univ F false true (-1) (1 / 2 : ℂ) = 1 := by
  have hreal : ReflectionSymmetricPairSigRealizable reflectionPairPeriods Finset.univ
      (depthTwoReflectionClassDivisor reflectionPairPeriods) :=
    (reflectionSymmetricPairSigRealizable_iff reflectionPairPeriods
      reflectionPairPeriods_im_pos reflectionPairPeriods_integrallyIndependent Finset.univ
      (by simp) (depthTwoReflectionClassDivisor reflectionPairPeriods)).mpr
      ⟨depthTwoReflectionClassDivisor_admissible reflectionPairPeriods,
        depthTwoReflectionClassDivisor_fixed reflectionPairPeriods⟩
  obtain ⟨F, Cst, hmero, hper, hmixed, hsymm, hsig⟩ := hreal
  refine ⟨F, Cst, hmero, hper, hmixed, hsymm, ?_, ?_⟩
  · intro i j hij ℓ hℓ p
    exact hsig i (by simp) j (by simp) hij ℓ hℓ p
  · rw [hsig false (by simp) true (by simp) Bool.false_ne_true (-1) (by omega)
      (1 / 2 : ℂ), depthTwoReflectionClassDivisor_half]

set_option synthInstance.maxHeartbeats 900000 in
/-- Kernel on the reflection-fixed mixed class is exactly the differentially algebraic class. -/
theorem differentialAlgebraicOver_iff_pairSig_zero_of_reflectionSymmetric
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ)
    (s : Finset ι) (hs : 2 ≤ s.card)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {F : ℂ → ℂ} (hx : RealizesMero x F)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGermSet τ s F Cst)
    (_hsymm : ∀ z : ℂ, F (1 - z) = F z) :
    DifferentialAlgebraicOver ℂ x ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ p : ℂ, ∀ ℓ : ℤ, ℓ < 0 →
        pairSig τ s F i j ℓ p = 0 := by
  simpa only [pairSig] using
    differentialAlgebraicOver_iff_pairFace_eq_zero τ hτ hQ s hs hx hper hmixed

end

end GaloisForLFunctions

