import GaloisForLFunctions.RHTower.HBFiniteCrossFrequencyJetPositiveClockNoGo
import GaloisForLFunctions.RHTower.DeBrangesHTGaugeSaturation
import GaloisForLFunctions.RHTower.BakerProof.MultipointSchwarz
import GaloisForLFunctions.HTGeometry.MinimalTypeProjectiveSeparation
import GaloisForLFunctions.HTGeometry.SampledSmallComplex

/-!
# Closed-discrete finite jets do not identify positive-clock HB all-pass phase

The finite-packet no-go is strengthened to every closed-discrete complex frequency passport,
with an arbitrary finite jet depth at each site and no uniform bound on those depths.  A corpus
Weierstrass passport supplies a nonzero Schwarz-real entire carrier flat to every prescribed
order.  Odd symmetrization, an exact entire primitive, and exponential phase splitting produce
two distinct entire zero-free responses with unit real-boundary modulus, exact FE--Schwarz
symmetry, strictly positive logarithmic-derivative clocks, and identical prescribed jets.

Therefore no closed-discrete collection of pointwise finite-order response data can identify the
source-FE all-pass phase needed to force unit cocycle gain.  In the shared frontier chain, such a
producer cannot reach fixed Ward orientation, HB optical extinction, FZZ-P equilibrium, PW-B
partner balance, RBH leading balance, or RH.  A survivor must use a finite accumulation/continuum,
an infinite jet, or a source-global minimum-phase, winding, growth, or singular boundary law.

The theorem does not address Hardy/Schur growth classes or source-global constraints.

`[NEW] [HB ROUTE-CLASS KILL] [CLOSED-DISCRETE] [LEAN-PROVED]`
-/

open Complex Real Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RHTower

def cdOddFlatPhase (Q : ℂ → ℂ) (z : ℂ) : ℂ := Q z * (z * Q (-z))

def cdClockDensity (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 + deriv H z ^ (2 : ℕ)

def cdSchwarzOddPrimitive (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((F z + suzukiEntireSharp F z) -
    (F (-z) + suzukiEntireSharp F (-z))) / 4

def cdPositivePhasePlus (Q K : ℂ → ℂ) (z : ℂ) : ℂ :=
  K z + cdOddFlatPhase Q z

def cdPositivePhaseMinus (Q K : ℂ → ℂ) (z : ℂ) : ℂ :=
  K z - cdOddFlatPhase Q z

def cdPositiveClockAllPassPlus (Q K : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (I * cdPositivePhasePlus Q K z)

def cdPositiveClockAllPassMinus (Q K : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (I * cdPositivePhaseMinus Q K z)

def cdPositiveClockAllPassPlusClock (Q K : ℂ → ℂ) (x : ℝ) : ℝ :=
  (logDeriv (cdPositiveClockAllPassPlus Q K) (x : ℂ)).im

def cdPositiveClockAllPassMinusClock (Q K : ℂ → ℂ) (x : ℝ) : ℝ :=
  (logDeriv (cdPositiveClockAllPassMinus Q K) (x : ℂ)).im

theorem hasDerivAt_suzukiEntireSharp_of {F G : ℂ → ℂ}
    (hF : ∀ z, HasDerivAt F (G z) z) (z : ℂ) :
    HasDerivAt (suzukiEntireSharp F)
      ((starRingEnd ℂ) (G ((starRingEnd ℂ) z))) z := by
  have h := (hF ((starRingEnd ℂ) z)).star_conj
  have h' : HasDerivAt
    (fun x => (starRingEnd ℂ) (F ((starRingEnd ℂ) x)))
    ((starRingEnd ℂ) (G ((starRingEnd ℂ) z)))
    ((starRingEnd ℂ) ((starRingEnd ℂ) z)) := by
      exact h
  change HasDerivAt
    (fun x => (starRingEnd ℂ) (F ((starRingEnd ℂ) x)))
    ((starRingEnd ℂ) (G ((starRingEnd ℂ) z))) z
  have hzz : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by simp
  rw [hzz] at h'
  exact h'

theorem cdOddFlatPhase_differentiable {Q : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) : Differentiable ℂ (cdOddFlatPhase Q) := by
  unfold cdOddFlatPhase
  fun_prop

theorem cdOddFlatPhase_neg (Q : ℂ → ℂ) (z : ℂ) :
    cdOddFlatPhase Q (-z) = -cdOddFlatPhase Q z := by
  simp [cdOddFlatPhase]
  ring

theorem cdOddFlatPhase_schwarzReal {Q : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) : SchwarzRealGauge (cdOddFlatPhase Q) := by
  intro z
  have hQz := hQ z
  have hQneg := hQ (-z)
  rw [suzukiEntireSharp] at hQz hQneg ⊢
  change (starRingEnd ℂ)
      (Q ((starRingEnd ℂ) z) *
        (((starRingEnd ℂ) z) * Q (-((starRingEnd ℂ) z)))) =
    Q z * (z * Q (-z))
  rw [map_mul, map_mul]
  have hneg : (starRingEnd ℂ) (-z) = -((starRingEnd ℂ) z) := by simp
  rw [hQz]
  rw [hneg] at hQneg
  rw [hQneg]
  simp

theorem cdOddFlatPhase_ne_zero {Q : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hQne : Q ≠ 0) : cdOddFlatPhase Q ≠ 0 := by
  let qneg : ℂ → ℂ := fun z => Q (-z)
  have hqneg : Differentiable ℂ qneg := by
    dsimp [qneg]
    fun_prop
  have hqneg_ne : qneg ≠ 0 := by
    intro hz
    apply hQne
    funext z
    have := congrFun hz (-z)
    simpa [qneg] using this
  have hid : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
  have hid_ne : (fun z : ℂ => z) ≠ 0 := by
    intro hz
    have := congrFun hz 1
    norm_num at this
  have hinner : (fun z : ℂ => z * qneg z) ≠ 0 :=
    GaloisForLFunctions.HTGeometry.differentiable_mul_ne_zero hid hqneg hid_ne hqneg_ne
  have hprod : (fun z : ℂ => Q z * (z * qneg z)) ≠ 0 :=
    GaloisForLFunctions.HTGeometry.differentiable_mul_ne_zero hQ
      (hid.mul hqneg) hQne hinner
  change (fun z : ℂ => Q z * (z * Q (-z))) ≠ 0
  exact hprod

theorem cdOddFlatPhase_order {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) {S : Set ℂ} (m : S → ℕ)
    (horder : ∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt Q a) (a : S) :
    (m a + 1 : ℕ∞) ≤ analyticOrderAt (cdOddFlatPhase Q) a := by
  have hQneg : AnalyticAt ℂ (fun z => Q (-z)) a := by
    have hneg : AnalyticAt ℂ (fun z : ℂ => -z) (a : ℂ) := by fun_prop
    exact (hQ (-(a : ℂ)) (Set.mem_univ (-(a : ℂ)))).comp hneg
  have hR : AnalyticAt ℂ (fun z => z * Q (-z)) a := analyticAt_id.mul hQneg
  change (m a + 1 : ℕ∞) ≤ analyticOrderAt (Q * fun z => z * Q (-z)) a
  rw [analyticOrderAt_mul (hQ a (Set.mem_univ a)) hR]
  exact (horder a).trans (le_add_right le_rfl)

theorem deriv_cdOddFlatPhase_even {Q : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (z : ℂ) :
    deriv (cdOddFlatPhase Q) (-z) = deriv (cdOddFlatPhase Q) z := by
  let H := cdOddFlatPhase Q
  have hH : Differentiable ℂ H := cdOddFlatPhase_differentiable hQ
  have hleft := (hH (-z)).hasDerivAt.comp z (hasDerivAt_neg z)
  have hleft' : HasDerivAt (fun w : ℂ => H (-w)) (-deriv H (-z)) z := by
    simpa [Function.comp_def] using hleft
  have hright' : HasDerivAt (fun w : ℂ => -H w) (-deriv H z) z :=
    (hH z).hasDerivAt.fun_neg
  have heq : (fun w : ℂ => H (-w)) = fun w => -H w := by
    funext w
    exact cdOddFlatPhase_neg Q w
  rw [heq] at hleft'
  exact neg_injective (hleft'.unique hright')

theorem deriv_cdOddFlatPhase_schwarzReal {Q : ℂ → ℂ}
    (hQsym : SchwarzRealGauge Q) :
    SchwarzRealGauge (deriv (cdOddFlatPhase Q)) := by
  let H := cdOddFlatPhase Q
  have hHsym : suzukiEntireSharp H = H :=
    funext (cdOddFlatPhase_schwarzReal hQsym)
  have hfun : (starRingEnd ℂ) ∘ H ∘ (starRingEnd ℂ) = H := by
    funext z
    have hz := congrFun hHsym z
    change (starRingEnd ℂ) (H ((starRingEnd ℂ) z)) = H z at hz
    simpa [Function.comp_def] using hz
  have hder := congrArg deriv hfun
  rw [deriv_conj_conj] at hder
  intro z
  have hz := congrFun hder z
  simpa [H, suzukiEntireSharp, Function.comp_def] using hz

theorem cdClockDensity_differentiable {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) : Differentiable ℂ (cdClockDensity H) := by
  unfold cdClockDensity
  have hd : Differentiable ℂ (deriv H) :=
    HTGeometry.differentiable_deriv_of_entire hH
  fun_prop

theorem cdClockDensity_even {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (z : ℂ) :
    cdClockDensity (cdOddFlatPhase Q) (-z) =
      cdClockDensity (cdOddFlatPhase Q) z := by
  rw [cdClockDensity, cdClockDensity, deriv_cdOddFlatPhase_even hQ z]

theorem cdClockDensity_schwarzReal {Q : ℂ → ℂ}
    (hQsym : SchwarzRealGauge Q) :
    SchwarzRealGauge (cdClockDensity (cdOddFlatPhase Q)) := by
  let d : ℂ → ℂ := deriv (cdOddFlatPhase Q)
  have hdsym : SchwarzRealGauge d := deriv_cdOddFlatPhase_schwarzReal hQsym
  intro z
  have hdz := hdsym z
  rw [suzukiEntireSharp] at hdz ⊢
  change (starRingEnd ℂ) (1 + d ((starRingEnd ℂ) z) ^ (2 : ℕ)) =
    1 + d z ^ (2 : ℕ)
  rw [map_add, map_one, map_pow, hdz]

theorem cdSchwarzOddPrimitive_neg (F : ℂ → ℂ) (z : ℂ) :
    cdSchwarzOddPrimitive F (-z) = -cdSchwarzOddPrimitive F z := by
  simp [cdSchwarzOddPrimitive]
  ring

theorem cdSchwarzOddPrimitive_schwarzReal (F : ℂ → ℂ) :
    SchwarzRealGauge (cdSchwarzOddPrimitive F) := by
  let R : ℂ → ℂ := fun z => F z + suzukiEntireSharp F z
  have hR : SchwarzRealGauge R := by
    intro z
    rw [suzukiEntireSharp]
    simp [R, suzukiEntireSharp]
    ring
  intro z
  have hRz := hR z
  have hRneg := hR (-z)
  rw [suzukiEntireSharp] at hRz hRneg ⊢
  have hneg : (starRingEnd ℂ) (-z) = -((starRingEnd ℂ) z) := by simp
  rw [hneg] at hRneg
  change (starRingEnd ℂ)
      ((R ((starRingEnd ℂ) z) - R (-((starRingEnd ℂ) z))) / 4) =
    (R z - R (-z)) / 4
  rw [map_div₀, map_sub, hRz, hRneg, map_ofNat]

theorem hasDerivAt_cdSchwarzOddPrimitive {F G : ℂ → ℂ}
    (hF : ∀ z, HasDerivAt F (G z) z)
    (hGeven : ∀ z, G (-z) = G z)
    (hGsym : SchwarzRealGauge G) (z : ℂ) :
    HasDerivAt (cdSchwarzOddPrimitive F) (G z) z := by
  have hsharp0 := hasDerivAt_suzukiEntireSharp_of hF z
  have hGz := hGsym z
  rw [suzukiEntireSharp] at hGz
  have hsharp : HasDerivAt (suzukiEntireSharp F) (G z) z := by
    rw [hGz] at hsharp0
    exact hsharp0
  have hR : HasDerivAt (fun w => F w + suzukiEntireSharp F w)
      (G z + G z) z := (hF z).fun_add hsharp
  have hsharpNeg0 := hasDerivAt_suzukiEntireSharp_of hF (-z)
  have hGneg := hGsym (-z)
  rw [suzukiEntireSharp] at hGneg
  have hsharpNeg : HasDerivAt (suzukiEntireSharp F) (G (-z)) (-z) := by
    rw [hGneg] at hsharpNeg0
    exact hsharpNeg0
  have hRneg0 : HasDerivAt (fun w => F w + suzukiEntireSharp F w)
      (G (-z) + G (-z)) (-z) := (hF (-z)).fun_add hsharpNeg
  have hRneg := hRneg0.comp z (hasDerivAt_neg z)
  have hsub := hR.fun_sub hRneg
  have hdiv := hsub.div_const (4 : ℂ)
  have hdiv' : HasDerivAt
      (fun x => (F x + suzukiEntireSharp F x -
        (F (-x) + suzukiEntireSharp F (-x))) / 4)
      ((G z + G z - (G (-z) + G (-z)) * -1) / 4) z := by
    simpa only [Function.comp_apply] using hdiv
  rw [hGeven z] at hdiv'
  have hcoef' : (G z + G z - (G z + G z) * -1) / 4 = G z := by ring
  rw [hcoef'] at hdiv'
  change HasDerivAt
    (fun x => (F x + suzukiEntireSharp F x -
      (F (-x) + suzukiEntireSharp F (-x))) / 4) (G z) z
  exact hdiv'

theorem exists_cdSchwarzOddClockPrimitive {Q : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hQsym : SchwarzRealGauge Q) :
    ∃ K : ℂ → ℂ,
      (∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z) ∧
      (∀ z, K (-z) = -K z) ∧ SchwarzRealGauge K := by
  let H := cdOddFlatPhase Q
  let G := cdClockDensity H
  have hGdiff : Differentiable ℂ G := cdClockDensity_differentiable
    (cdOddFlatPhase_differentiable hQ)
  obtain ⟨F, hF⟩ := hGdiff.isExactOn_univ
  have hF' : ∀ z, HasDerivAt F (G z) z := fun z => hF z (Set.mem_univ z)
  let K := cdSchwarzOddPrimitive F
  refine ⟨K, ?_, cdSchwarzOddPrimitive_neg F,
    cdSchwarzOddPrimitive_schwarzReal F⟩
  intro z
  exact hasDerivAt_cdSchwarzOddPrimitive hF'
    (cdClockDensity_even hQ)
    (cdClockDensity_schwarzReal hQsym) z

theorem cdPositivePhasePlus_neg {Q K : ℂ → ℂ}
    (hKodd : ∀ z, K (-z) = -K z) (z : ℂ) :
    cdPositivePhasePlus Q K (-z) = -cdPositivePhasePlus Q K z := by
  change K (-z) + cdOddFlatPhase Q (-z) =
    -(K z + cdOddFlatPhase Q z)
  rw [hKodd, cdOddFlatPhase_neg]
  ring

theorem cdPositivePhaseMinus_neg {Q K : ℂ → ℂ}
    (hKodd : ∀ z, K (-z) = -K z) (z : ℂ) :
    cdPositivePhaseMinus Q K (-z) = -cdPositivePhaseMinus Q K z := by
  change K (-z) - cdOddFlatPhase Q (-z) =
    -(K z - cdOddFlatPhase Q z)
  rw [hKodd, cdOddFlatPhase_neg]
  ring

theorem cdPositivePhasePlus_schwarzReal {Q K : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (hK : SchwarzRealGauge K) :
    SchwarzRealGauge (cdPositivePhasePlus Q K) := by
  intro z
  have hKz := hK z
  have hHz := cdOddFlatPhase_schwarzReal hQ z
  rw [suzukiEntireSharp] at hKz hHz ⊢
  change (starRingEnd ℂ)
      (K ((starRingEnd ℂ) z) + cdOddFlatPhase Q ((starRingEnd ℂ) z)) =
    K z + cdOddFlatPhase Q z
  rw [map_add, hKz, hHz]

theorem cdPositivePhaseMinus_schwarzReal {Q K : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (hK : SchwarzRealGauge K) :
    SchwarzRealGauge (cdPositivePhaseMinus Q K) := by
  intro z
  have hKz := hK z
  have hHz := cdOddFlatPhase_schwarzReal hQ z
  rw [suzukiEntireSharp] at hKz hHz ⊢
  change (starRingEnd ℂ)
      (K ((starRingEnd ℂ) z) - cdOddFlatPhase Q ((starRingEnd ℂ) z)) =
    K z - cdOddFlatPhase Q z
  rw [map_sub, hKz, hHz]

theorem hasDerivAt_cdPositivePhasePlus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) :
    HasDerivAt (cdPositivePhasePlus Q K)
      (cdClockDensity (cdOddFlatPhase Q) z + deriv (cdOddFlatPhase Q) z) z := by
  change HasDerivAt (fun w => K w + cdOddFlatPhase Q w) _ z
  exact (hK z).fun_add ((cdOddFlatPhase_differentiable hQ z).hasDerivAt)

theorem hasDerivAt_cdPositivePhaseMinus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) :
    HasDerivAt (cdPositivePhaseMinus Q K)
      (cdClockDensity (cdOddFlatPhase Q) z - deriv (cdOddFlatPhase Q) z) z := by
  change HasDerivAt (fun w => K w - cdOddFlatPhase Q w) _ z
  exact (hK z).fun_sub ((cdOddFlatPhase_differentiable hQ z).hasDerivAt)

theorem hasDerivAt_cdPositiveClockAllPassPlus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) :
    HasDerivAt (cdPositiveClockAllPassPlus Q K)
      (cdPositiveClockAllPassPlus Q K z *
        (I * (cdClockDensity (cdOddFlatPhase Q) z +
          deriv (cdOddFlatPhase Q) z))) z := by
  have h := ((hasDerivAt_cdPositivePhasePlus hQ hK z).const_mul I).cexp
  change HasDerivAt
    (fun w => Complex.exp (I * cdPositivePhasePlus Q K w))
    (Complex.exp (I * cdPositivePhasePlus Q K z) *
      (I * (cdClockDensity (cdOddFlatPhase Q) z +
        deriv (cdOddFlatPhase Q) z))) z
  simpa [mul_assoc] using h

theorem hasDerivAt_cdPositiveClockAllPassMinus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) :
    HasDerivAt (cdPositiveClockAllPassMinus Q K)
      (cdPositiveClockAllPassMinus Q K z *
        (I * (cdClockDensity (cdOddFlatPhase Q) z -
          deriv (cdOddFlatPhase Q) z))) z := by
  have h := ((hasDerivAt_cdPositivePhaseMinus hQ hK z).const_mul I).cexp
  change HasDerivAt
    (fun w => Complex.exp (I * cdPositivePhaseMinus Q K w))
    (Complex.exp (I * cdPositivePhaseMinus Q K z) *
      (I * (cdClockDensity (cdOddFlatPhase Q) z -
        deriv (cdOddFlatPhase Q) z))) z
  simpa [mul_assoc] using h

theorem analyticAt_cdPositiveClockAllPassPlus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) : AnalyticAt ℂ (cdPositiveClockAllPassPlus Q K) z := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate
  exact fun w => (hasDerivAt_cdPositiveClockAllPassPlus hQ hK w).differentiableAt

theorem analyticAt_cdPositiveClockAllPassMinus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) : AnalyticAt ℂ (cdPositiveClockAllPassMinus Q K) z := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate
  exact fun w => (hasDerivAt_cdPositiveClockAllPassMinus hQ hK w).differentiableAt

theorem analyticAt_cdPositivePhasePlus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) : AnalyticAt ℂ (cdPositivePhasePlus Q K) z := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate
  exact fun w => (hasDerivAt_cdPositivePhasePlus hQ hK w).differentiableAt

theorem analyticAt_cdPositivePhaseMinus {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (z : ℂ) : AnalyticAt ℂ (cdPositivePhaseMinus Q K) z := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate
  exact fun w => (hasDerivAt_cdPositivePhaseMinus hQ hK w).differentiableAt

theorem cdPositiveClockAllPassPlus_neg_star {Q K : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (hKsym : SchwarzRealGauge K)
    (hKodd : ∀ z, K (-z) = -K z) (z : ℂ) :
    cdPositiveClockAllPassPlus Q K (-((starRingEnd ℂ) z)) =
      (starRingEnd ℂ) (cdPositiveClockAllPassPlus Q K z) := by
  rw [cdPositiveClockAllPassPlus,
    cdPositivePhasePlus_neg hKodd]
  have hphase :
      cdPositivePhasePlus Q K ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (cdPositivePhasePlus Q K z) := by
    have hs := (cdPositivePhasePlus_schwarzReal hQ hKsym)
      ((starRingEnd ℂ) z)
    rw [suzukiEntireSharp] at hs
    have hzz : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by simp
    rw [hzz] at hs
    exact hs.symm
  rw [hphase]
  change Complex.exp (I * -((starRingEnd ℂ) (cdPositivePhasePlus Q K z))) =
    (starRingEnd ℂ) (Complex.exp (I * cdPositivePhasePlus Q K z))
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem cdPositiveClockAllPassMinus_neg_star {Q K : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (hKsym : SchwarzRealGauge K)
    (hKodd : ∀ z, K (-z) = -K z) (z : ℂ) :
    cdPositiveClockAllPassMinus Q K (-((starRingEnd ℂ) z)) =
      (starRingEnd ℂ) (cdPositiveClockAllPassMinus Q K z) := by
  rw [cdPositiveClockAllPassMinus,
    cdPositivePhaseMinus_neg hKodd]
  have hphase :
      cdPositivePhaseMinus Q K ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (cdPositivePhaseMinus Q K z) := by
    have hs := (cdPositivePhaseMinus_schwarzReal hQ hKsym)
      ((starRingEnd ℂ) z)
    rw [suzukiEntireSharp] at hs
    have hzz : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by simp
    rw [hzz] at hs
    exact hs.symm
  rw [hphase]
  change Complex.exp (I * -((starRingEnd ℂ) (cdPositivePhaseMinus Q K z))) =
    (starRingEnd ℂ) (Complex.exp (I * cdPositivePhaseMinus Q K z))
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem norm_cdPositiveClockAllPassPlus {Q K : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (hK : SchwarzRealGauge K) (x : ℝ) :
    ‖cdPositiveClockAllPassPlus Q K (x : ℂ)‖ = 1 := by
  rw [cdPositiveClockAllPassPlus, Complex.norm_exp]
  have hphase := schwarzReal_value_ofReal
    (cdPositivePhasePlus_schwarzReal hQ hK) x
  have him : (cdPositivePhasePlus Q K (x : ℂ)).im = 0 := by
    rw [hphase]
    simp
  rw [Complex.mul_re, him]
  norm_num

theorem norm_cdPositiveClockAllPassMinus {Q K : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (hK : SchwarzRealGauge K) (x : ℝ) :
    ‖cdPositiveClockAllPassMinus Q K (x : ℂ)‖ = 1 := by
  rw [cdPositiveClockAllPassMinus, Complex.norm_exp]
  have hphase := schwarzReal_value_ofReal
    (cdPositivePhaseMinus_schwarzReal hQ hK) x
  have him : (cdPositivePhaseMinus Q K (x : ℂ)).im = 0 := by
    rw [hphase]
    simp
  rw [Complex.mul_re, him]
  norm_num

theorem cdPositiveClockAllPassPlusClock_eq {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hQsym : SchwarzRealGauge Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (x : ℝ) :
    cdPositiveClockAllPassPlusClock Q K x =
      1 + (deriv (cdOddFlatPhase Q) (x : ℂ)).re ^ (2 : ℕ) +
        (deriv (cdOddFlatPhase Q) (x : ℂ)).re := by
  have hresp := hasDerivAt_cdPositiveClockAllPassPlus hQ hK (x : ℂ)
  rw [cdPositiveClockAllPassPlusClock, logDeriv_apply, hresp.deriv]
  have hne : cdPositiveClockAllPassPlus Q K (x : ℂ) ≠ 0 :=
    Complex.exp_ne_zero _
  have hcancel :
      cdPositiveClockAllPassPlus Q K (x : ℂ) *
          (I * (cdClockDensity (cdOddFlatPhase Q) (x : ℂ) +
            deriv (cdOddFlatPhase Q) (x : ℂ))) /
        cdPositiveClockAllPassPlus Q K (x : ℂ) =
      I * (cdClockDensity (cdOddFlatPhase Q) (x : ℂ) +
        deriv (cdOddFlatPhase Q) (x : ℂ)) := by
    field_simp
  rw [hcancel, cdClockDensity]
  have hdreal := schwarzReal_value_ofReal
    (deriv_cdOddFlatPhase_schwarzReal hQsym) x
  rw [hdreal]
  norm_num [pow_two]

theorem cdPositiveClockAllPassMinusClock_eq {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hQsym : SchwarzRealGauge Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (x : ℝ) :
    cdPositiveClockAllPassMinusClock Q K x =
      1 + (deriv (cdOddFlatPhase Q) (x : ℂ)).re ^ (2 : ℕ) -
        (deriv (cdOddFlatPhase Q) (x : ℂ)).re := by
  have hresp := hasDerivAt_cdPositiveClockAllPassMinus hQ hK (x : ℂ)
  rw [cdPositiveClockAllPassMinusClock, logDeriv_apply, hresp.deriv]
  have hne : cdPositiveClockAllPassMinus Q K (x : ℂ) ≠ 0 :=
    Complex.exp_ne_zero _
  have hcancel :
      cdPositiveClockAllPassMinus Q K (x : ℂ) *
          (I * (cdClockDensity (cdOddFlatPhase Q) (x : ℂ) -
            deriv (cdOddFlatPhase Q) (x : ℂ))) /
        cdPositiveClockAllPassMinus Q K (x : ℂ) =
      I * (cdClockDensity (cdOddFlatPhase Q) (x : ℂ) -
        deriv (cdOddFlatPhase Q) (x : ℂ)) := by
    field_simp
  rw [hcancel, cdClockDensity]
  have hdreal := schwarzReal_value_ofReal
    (deriv_cdOddFlatPhase_schwarzReal hQsym) x
  rw [hdreal]
  norm_num [pow_two]

theorem cdPositiveClockAllPassPlusClock_pos {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hQsym : SchwarzRealGauge Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (x : ℝ) : 0 < cdPositiveClockAllPassPlusClock Q K x := by
  rw [cdPositiveClockAllPassPlusClock_eq hQ hQsym hK]
  nlinarith [sq_nonneg ((deriv (cdOddFlatPhase Q) (x : ℂ)).re + 1 / 2)]

theorem cdPositiveClockAllPassMinusClock_pos {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hQsym : SchwarzRealGauge Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (x : ℝ) : 0 < cdPositiveClockAllPassMinusClock Q K x := by
  rw [cdPositiveClockAllPassMinusClock_eq hQ hQsym hK]
  nlinarith [sq_nonneg ((deriv (cdOddFlatPhase Q) (x : ℂ)).re - 1 / 2)]

theorem cdPositiveClockAllPass_pair_iteratedDeriv_eq
    {S : Set ℂ} (m : S → ℕ) {a : S} {j : ℕ}
    (hQ : Differentiable ℂ Q)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z)
    (horder : (m a + 1 : ℕ∞) ≤ analyticOrderAt (cdOddFlatPhase Q) a)
    (hj : j ≤ m a) :
    iteratedDeriv j (cdPositiveClockAllPassPlus Q K) a =
      iteratedDeriv j (cdPositiveClockAllPassMinus Q K) a := by
  have hHanalytic : ∀ z, AnalyticAt ℂ (cdOddFlatPhase Q) z := by
    intro z
    apply GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate
    exact cdOddFlatPhase_differentiable hQ
  obtain ⟨U, hU, hfac⟩ :=
    BakerProof.exists_entire_factor_of_natCast_le_analyticOrderAt
      (cdOddFlatPhase Q) hHanalytic (a : ℂ) (m a + 1) horder
  let Lp : ℂ → ℂ := fun z =>
    I * cdPositivePhasePlus Q K ((a : ℂ) + z)
  let Lm : ℂ → ℂ := fun z =>
    I * cdPositivePhaseMinus Q K ((a : ℂ) + z)
  let W : ℂ → ℂ := fun z => 2 * I * U ((a : ℂ) + z)
  have hLp : ∀ z, AnalyticAt ℂ Lp z := by
    intro z
    exact analyticAt_const.mul
      ((analyticAt_cdPositivePhasePlus hQ hK ((a : ℂ) + z)).comp
        (analyticAt_const.add analyticAt_id))
  have hLm : ∀ z, AnalyticAt ℂ Lm z := by
    intro z
    exact analyticAt_const.mul
      ((analyticAt_cdPositivePhaseMinus hQ hK ((a : ℂ) + z)).comp
        (analyticAt_const.add analyticAt_id))
  have hW : AnalyticAt ℂ W 0 := by
    exact analyticAt_const.mul
      ((hU ((a : ℂ) + 0)).comp (analyticAt_const.add analyticAt_id))
  have hflat : ∀ᶠ z in 𝓝 (0 : ℂ),
      Lp z - Lm z = z ^ (m a + 1) * W z := by
    filter_upwards [] with z
    have hf := hfac ((a : ℂ) + z)
    have hcoord : (a : ℂ) + z - (a : ℂ) = z := by ring
    rw [hcoord] at hf
    dsimp [Lp, Lm, W]
    rw [cdPositivePhasePlus, cdPositivePhaseMinus, hf]
    ring
  have hjet := GaloisForLFunctions.HTGeometry.iteratedDeriv_exp_congr_of_flat
    hLp hLm hW hflat hj
  have hplusShift := GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_add j
    (G := cdPositiveClockAllPassPlus Q K)
    (fun z => analyticAt_cdPositiveClockAllPassPlus hQ hK z) (a : ℂ) 0
  have hminusShift := GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_add j
    (G := cdPositiveClockAllPassMinus Q K)
    (fun z => analyticAt_cdPositiveClockAllPassMinus hQ hK z) (a : ℂ) 0
  change iteratedDeriv j
      (fun z => cdPositiveClockAllPassPlus Q K ((a : ℂ) + z)) 0 =
    iteratedDeriv j (cdPositiveClockAllPassPlus Q K) ((a : ℂ) + 0)
      at hplusShift
  change iteratedDeriv j
      (fun z => cdPositiveClockAllPassMinus Q K ((a : ℂ) + z)) 0 =
    iteratedDeriv j (cdPositiveClockAllPassMinus Q K) ((a : ℂ) + 0)
      at hminusShift
  change iteratedDeriv j
      (fun z => cdPositiveClockAllPassPlus Q K ((a : ℂ) + z)) 0 =
    iteratedDeriv j
      (fun z => cdPositiveClockAllPassMinus Q K ((a : ℂ) + z)) 0 at hjet
  have hplusShift' : iteratedDeriv j
      (fun z => cdPositiveClockAllPassPlus Q K ((a : ℂ) + z)) 0 =
    iteratedDeriv j (cdPositiveClockAllPassPlus Q K) (a : ℂ) := by
    simpa using hplusShift
  have hminusShift' : iteratedDeriv j
      (fun z => cdPositiveClockAllPassMinus Q K ((a : ℂ) + z)) 0 =
    iteratedDeriv j (cdPositiveClockAllPassMinus Q K) (a : ℂ) := by
    simpa using hminusShift
  rw [← hplusShift', ← hminusShift']
  exact hjet

theorem cdPositiveClockAllPass_pair_ne {Q K : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hQne : Q ≠ 0)
    (hK : ∀ z, HasDerivAt K (cdClockDensity (cdOddFlatPhase Q) z) z) :
    cdPositiveClockAllPassPlus Q K ≠
      cdPositiveClockAllPassMinus Q K := by
  intro heq
  have hd : ∀ z, deriv (cdOddFlatPhase Q) z = 0 := by
    intro z
    have hder := congrArg (fun A : ℂ → ℂ => deriv A z) heq
    rw [(hasDerivAt_cdPositiveClockAllPassPlus hQ hK z).deriv,
      (hasDerivAt_cdPositiveClockAllPassMinus hQ hK z).deriv] at hder
    have hval := congrFun heq z
    rw [hval] at hder
    have hrespne : cdPositiveClockAllPassMinus Q K z ≠ 0 :=
      Complex.exp_ne_zero _
    have hc := mul_left_cancel₀ hrespne hder
    have hc' := mul_left_cancel₀ Complex.I_ne_zero hc
    linear_combination (1 / 2 : ℂ) * hc'
  have hconst : ∀ z, cdOddFlatPhase Q z = cdOddFlatPhase Q 0 :=
    fun z => is_const_of_deriv_eq_zero
      (cdOddFlatPhase_differentiable hQ) hd z 0
  have hzero : cdOddFlatPhase Q 0 = 0 := by simp [cdOddFlatPhase]
  apply cdOddFlatPhase_ne_zero hQ hQne
  funext z
  simpa using (hconst z).trans hzero

/-- Two positive-clock FE--Schwarz all-pass responses share every prescribed pointwise finite
jet on an arbitrary closed-discrete complex frequency set. -/
theorem exists_closedDiscreteJetSchwarzPositiveClockAllPass_pair
    (S : Set ℂ) (hSd : IsDiscrete S) (hSc : IsClosed S) (m : S → ℕ) :
    ∃ A B : ℂ → ℂ,
      (∀ z, AnalyticAt ℂ A z) ∧
      (∀ z, AnalyticAt ℂ B z) ∧
      (∀ z, A z ≠ 0) ∧
      (∀ z, B z ≠ 0) ∧
      (∀ x : ℝ, ‖A (x : ℂ)‖ = 1) ∧
      (∀ x : ℝ, ‖B (x : ℂ)‖ = 1) ∧
      (∀ z, A (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (A z)) ∧
      (∀ z, B (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (B z)) ∧
      (∀ x : ℝ, 0 < (logDeriv A (x : ℂ)).im) ∧
      (∀ x : ℝ, 0 < (logDeriv B (x : ℂ)).im) ∧
      (∀ a : S, ∀ j ≤ m a, iteratedDeriv j A a = iteratedDeriv j B a) ∧
      A ≠ B := by
  obtain ⟨Q, hQanalytic, hQsym, _hQHT, hQne, hQorder⟩ :=
    exists_symmetric_hypertranscendental_passport_exponent hSd hSc m
  have hQdiff : Differentiable ℂ Q := by
    rw [← Complex.analyticOnNhd_univ_iff_differentiable]
    exact hQanalytic
  have hQfunne : Q ≠ 0 := by
    obtain ⟨z, hz⟩ := hQne
    intro hzero
    exact hz (congrFun hzero z)
  obtain ⟨K, hKderiv, hKodd, hKsym⟩ :=
    exists_cdSchwarzOddClockPrimitive hQdiff hQsym
  refine ⟨cdPositiveClockAllPassPlus Q K,
    cdPositiveClockAllPassMinus Q K,
    analyticAt_cdPositiveClockAllPassPlus hQdiff hKderiv,
    analyticAt_cdPositiveClockAllPassMinus hQdiff hKderiv,
    ?_, ?_,
    norm_cdPositiveClockAllPassPlus hQsym hKsym,
    norm_cdPositiveClockAllPassMinus hQsym hKsym,
    cdPositiveClockAllPassPlus_neg_star hQsym hKsym hKodd,
    cdPositiveClockAllPassMinus_neg_star hQsym hKsym hKodd,
    ?_, ?_, ?_,
    cdPositiveClockAllPass_pair_ne hQdiff hQfunne hKderiv⟩
  · intro z
    exact Complex.exp_ne_zero _
  · intro z
    exact Complex.exp_ne_zero _
  · intro x
    exact cdPositiveClockAllPassPlusClock_pos hQdiff hQsym hKderiv x
  · intro x
    exact cdPositiveClockAllPassMinusClock_pos hQdiff hQsym hKderiv x
  · intro a j hj
    exact cdPositiveClockAllPass_pair_iteratedDeriv_eq m hQdiff hKderiv
      (cdOddFlatPhase_order hQanalytic m hQorder a) hj

/-- Closed-discrete finite-order response-jet identifiability asserted by the killed HB
phase-sensitive producer class. -/
def HBClosedDiscreteCrossFrequencyJetAllPassUnique
    (S : Set ℂ) (m : S → ℕ) : Prop :=
  ∀ A B : ℂ → ℂ,
    (∀ z, AnalyticAt ℂ A z) →
    (∀ z, AnalyticAt ℂ B z) →
    (∀ z, A z ≠ 0) →
    (∀ z, B z ≠ 0) →
    (∀ x : ℝ, ‖A (x : ℂ)‖ = 1) →
    (∀ x : ℝ, ‖B (x : ℂ)‖ = 1) →
    (∀ z, A (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (A z)) →
    (∀ z, B (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (B z)) →
    (∀ x : ℝ, 0 < (logDeriv A (x : ℂ)).im) →
    (∀ x : ℝ, 0 < (logDeriv B (x : ℂ)).im) →
    (∀ a : S, ∀ j ≤ m a, iteratedDeriv j A a = iteratedDeriv j B a) →
    A = B

theorem not_hbClosedDiscreteCrossFrequencyJetAllPassUnique
    (S : Set ℂ) (hSd : IsDiscrete S) (hSc : IsClosed S) (m : S → ℕ) :
    ¬ HBClosedDiscreteCrossFrequencyJetAllPassUnique S m := by
  obtain ⟨A, B, hAanalytic, hBanalytic, hAne, hBne, hAnorm, hBnorm,
    hASchwarz, hBSchwarz, hAclock, hBclock, hjets, hne⟩ :=
      exists_closedDiscreteJetSchwarzPositiveClockAllPass_pair S hSd hSc m
  intro hunique
  exact hne (hunique A B hAanalytic hBanalytic hAne hBne hAnorm hBnorm
    hASchwarz hBSchwarz hAclock hBclock hjets)

/-- Premise-free route-class certificate: no closed-discrete frequency passport with arbitrary
pointwise finite jet depths identifies positive-clock FE--Schwarz all-pass phase. -/
def D4HBClosedDiscreteFiniteJetPositiveClockAllPassRouteKilled : Prop :=
  ∀ (S : Set ℂ) (_ : IsDiscrete S) (_ : IsClosed S) (m : S → ℕ),
    ¬ HBClosedDiscreteCrossFrequencyJetAllPassUnique S m

theorem d4HBClosedDiscreteFiniteJetPositiveClockAllPassRouteKilled :
    D4HBClosedDiscreteFiniteJetPositiveClockAllPassRouteKilled := by
  intro S hSd hSc m
  exact not_hbClosedDiscreteCrossFrequencyJetAllPassUnique S hSd hSc m

end GaloisForLFunctions.RHTower
