import GaloisForLFunctions.RHTower.SourceGammaCentralModuleGhostRigidity

/-!
# Equimodular prime-dependent source--Gamma ghosts are rigid

Central shared ghosts are already rigid at primes two and three.  This module removes the shared
forward-leg assumption: the forward ghost may now depend arbitrarily on the prime label and may
change direction in any real normed space.  Only its source norm is required to be the same at the
two retained primes.

If `u₂` and `u₃` share one reflected leg `v`, the two physical Gamma Ward equations give

`2^(2*t) • u₂ = v = 3^(2*t) • u₃`.

Taking norms yields the exact distortion law

`‖u₂‖ / ‖u₃‖ = (3/2)^(2*t)`.

Consequently equal nonzero source norms force `t = 0`, regardless of dimension, direction,
linearity, or how the two legs were produced.  Conversely, once equal norm is dropped, explicit
prime-fitted legs exist at every grade.  Equal norm is therefore the sharp boundary: an off-wall
prime-dependent ghost must encode the horizontal displacement in a prime-dependent radial
distortion, not merely in a noncentral change of direction.

Universal equimodular descent over the actual Xi divisor is equivalent to RH and to the shared
HB/FZZ-P/PW-B/RBH Ward endpoint.  This kills every isometric/equimodular prime-dependent ghost
producer as an independent route.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [SOURCE-PURE] [LEAN-PROVED]`
-/

open Complex Matrix

namespace RHTower

noncomputable section

universe u

/-- Converse to local central fitting: the fitted ray relation supplies the physical Gamma Ward
equation. -/
theorem primeGammaCentralModuleGhostWardEquation_of_fitted
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {u v : V} {t : ℝ} {p : Nat.Primes}
    (h : ((p : ℝ) ^ (2 * t)) • u = v) :
    primeGammaCentralModuleGhostWardEquation u v t p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hscalar : (p : ℝ) ^ (-t) * (p : ℝ) ^ (2 * t) =
      (p : ℝ) ^ t := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  change (-((p : ℝ) ^ t)) • u = (-((p : ℝ) ^ (-t))) • v
  rw [← h, smul_smul]
  rw [show -((p : ℝ) ^ (-t)) * (p : ℝ) ^ (2 * t) =
      -((p : ℝ) ^ t) by rw [neg_mul, hscalar]]

/-- Exact radial balance forced by two prime-dependent forward legs sharing one reflected leg. -/
theorem primeGammaTwoThreePrimeDependentGhost_norm_balance
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u₂ u₃ v : V} (t : ℝ)
    (htwo : primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo)
    (hthree : primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree) :
    (2 : ℝ) ^ (2 * t) * ‖u₂‖ = (3 : ℝ) ^ (2 * t) * ‖u₃‖ := by
  have htwo' := primeGammaCentralModuleGhostWardEquation_fitted htwo
  have hthree' := primeGammaCentralModuleGhostWardEquation_fitted hthree
  have hvectors : ((2 : ℝ) ^ (2 * t)) • u₂ =
      ((3 : ℝ) ^ (2 * t)) • u₃ := by
    simpa [deningerCalderonWittPrimeTwo, deningerCalderonWittPrimeThree] using
      htwo'.trans hthree'.symm
  have hnorms := congrArg norm hvectors
  rw [norm_smul, norm_smul] at hnorms
  simpa [Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _),
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)] using hnorms

/-- **Exact prime-dependent distortion law.**  Any nonzero prime-three leg must differ radially
from the prime-two leg by precisely the physical horizontal character `(3/2)^(2*t)`. -/
theorem primeGammaTwoThreePrimeDependentGhost_norm_ratio
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u₂ u₃ v : V} (hu₃ : u₃ ≠ 0) (t : ℝ)
    (htwo : primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo)
    (hthree : primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree) :
    ‖u₂‖ / ‖u₃‖ = ((3 : ℝ) / 2) ^ (2 * t) := by
  have hbalance := primeGammaTwoThreePrimeDependentGhost_norm_balance t htwo hthree
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_eq_div_iff (norm_ne_zero_iff.mpr hu₃)
    ((Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne')).2
  nlinarith

/-- **Rank-free equimodular rigidity.**  Prime-dependent directions do not evade two-prime Gamma
rigidity when their nonzero source norms agree. -/
theorem primeGammaTwoThreePrimeDependentGhost_equimodular_rigidity
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u₂ u₃ v : V} (hu₂ : u₂ ≠ 0) (hnorm : ‖u₂‖ = ‖u₃‖) (t : ℝ)
    (htwo : primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo)
    (hthree : primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree) :
    t = 0 := by
  have hbalance := primeGammaTwoThreePrimeDependentGhost_norm_balance t htwo hthree
  rw [hnorm] at hbalance
  have hnormpos : 0 < ‖u₃‖ := by
    rw [← hnorm]
    exact norm_pos_iff.mpr hu₂
  have hpowers : (2 : ℝ) ^ (2 * t) = (3 : ℝ) ^ (2 * t) := by
    nlinarith
  have hlogs := congrArg Real.log hpowers
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hlogs
  have hlogne : Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
    intro h
    have hexp := congrArg Real.exp h
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 3)] at hexp
    norm_num at hexp
  have hmul : (2 * t) * (Real.log (2 : ℝ) - Real.log (3 : ℝ)) = 0 := by
    linear_combination hlogs
  have ht : 2 * t = 0 :=
    (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hlogne)
  linarith

/-- A prime-dependent ghost with equal nonzero forward norms and one shared reflected leg. -/
def PrimeGammaTwoThreeEquimodularModuleGhostWard
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : ℝ) : Prop :=
  ∃ u₂ u₃ v : V, u₂ ≠ 0 ∧ ‖u₂‖ = ‖u₃‖ ∧
    primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree

/-- Equimodular prime-dependent ghosts exist exactly at neutral horizontal grade in every
nontrivial real normed space. -/
theorem primeGammaTwoThreeEquimodularModuleGhostWard_iff
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (t : ℝ) :
    PrimeGammaTwoThreeEquimodularModuleGhostWard V t ↔ t = 0 := by
  constructor
  · rintro ⟨u₂, u₃, v, hu₂, hnorm, htwo, hthree⟩
    exact primeGammaTwoThreePrimeDependentGhost_equimodular_rigidity
      hu₂ hnorm t htwo hthree
  · rintro rfl
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    refine ⟨u, u, u, hu, rfl, ?_, ?_⟩
    · exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)
    · exact primeGammaCentralModuleGhostWardEquation_of_fitted (by simp)

/-- The same prime-dependent Ward problem without radial matching. -/
def PrimeGammaTwoThreeUnconstrainedModuleGhostWard
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (t : ℝ) : Prop :=
  ∃ u₂ u₃ v : V, u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
    primeGammaCentralModuleGhostWardEquation
      u₂ v t deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      u₃ v t deningerCalderonWittPrimeThree

/-- **Sharpness.**  Without the equal-norm source law, prime-fitted nonzero legs solve both Ward
equations at every horizontal grade. -/
theorem primeGammaTwoThreeUnconstrainedModuleGhostWard_exists
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (t : ℝ) :
    PrimeGammaTwoThreeUnconstrainedModuleGhostWard V t := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let u₂ : V := ((2 : ℝ) ^ (-2 * t)) • v
  let u₃ : V := ((3 : ℝ) ^ (-2 * t)) • v
  have hu₂ : u₂ ≠ 0 := smul_ne_zero
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne' hv
  have hu₃ : u₃ ≠ 0 := smul_ne_zero
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne' hv
  refine ⟨u₂, u₃, v, hu₂, hu₃, ?_, ?_⟩
  · apply primeGammaCentralModuleGhostWardEquation_of_fitted
    change ((2 : ℝ) ^ (2 * t)) • u₂ = v
    dsimp only [u₂]
    rw [smul_smul]
    have hpow : (2 : ℝ) ^ (2 * t) * (2 : ℝ) ^ (-2 * t) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    rw [hpow, one_smul]
  · apply primeGammaCentralModuleGhostWardEquation_of_fitted
    change ((3 : ℝ) ^ (2 * t)) • u₃ = v
    dsimp only [u₃]
    rw [smul_smul]
    have hpow : (3 : ℝ) ^ (2 * t) * (3 : ℝ) ^ (-2 * t) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      simp
    rw [hpow, one_smul]

/-- Pointwise equimodular prime-dependent descent on an actual Xi divisor support. -/
def FrankensteinEquimodularPrimeDependentGammaGhostDescendsAt
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (rho : XiDivisorSupport) : Prop :=
  PrimeGammaTwoThreeEquimodularModuleGhostWard V
    (2 * (rho : ℂ).re - 1)

/-- Universal equimodular prime-dependent descent over actual Xi support. -/
def EveryFrankensteinEquimodularPrimeDependentGammaGhostDescends
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∀ rho : XiDivisorSupport,
    FrankensteinEquimodularPrimeDependentGammaGhostDescendsAt V rho

/-- In every nontrivial real normed space, universal equimodular descent is exactly RH. -/
theorem everyFrankensteinEquimodularPrimeDependentGammaGhostDescends_iff_riemannHypothesis
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] :
    EveryFrankensteinEquimodularPrimeDependentGammaGhostDescends V ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      have ht := (primeGammaTwoThreeEquimodularModuleGhostWard_iff V _).mp (h rho)
      linarith
  · intro h rho
    apply (primeGammaTwoThreeEquimodularModuleGhostWard_iff V _).mpr
    have hr := xi_divisor_support_re_eq_half_of_rh h rho
    linarith

/-- Universal equimodular descent is also exactly the common four-route Ward endpoint. -/
theorem everyFrankensteinEquimodularPrimeDependentGammaGhostDescends_iff_sharedFourRouteWardEndpoint
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] :
    EveryFrankensteinEquimodularPrimeDependentGammaGhostDescends V ↔
      SharedFourRouteWardEndpoint := by
  have hshared : SharedFourRouteWardEndpoint ↔ RiemannHypothesis :=
    everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint.symm.trans
      everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis
  exact
    (everyFrankensteinEquimodularPrimeDependentGammaGhostDescends_iff_riemannHypothesis V).trans
      hshared.symm

/-- Closed classification over every nontrivial real normed space. -/
def SharedWardEquimodularPrimeDependentGammaGhostRouteKilled : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V],
    (∀ t : ℝ, PrimeGammaTwoThreeEquimodularModuleGhostWard V t ↔ t = 0) ∧
    (∀ t : ℝ, PrimeGammaTwoThreeUnconstrainedModuleGhostWard V t) ∧
    (EveryFrankensteinEquimodularPrimeDependentGammaGhostDescends V ↔
      SharedFourRouteWardEndpoint) ∧
    (EveryFrankensteinEquimodularPrimeDependentGammaGhostDescends V ↔
      RiemannHypothesis)

/-- **[SHARED-WARD ROUTE-CLASS KILL].**  Arbitrary prime-dependent directional mixing in any
nontrivial real normed space cannot manufacture the missing source law if the two retained source
legs are equimodular.  Such universal descent is only the existing four-route/RH wall receiver.
The exact survivor is prime-dependent radial distortion; without a source law fixing that
distortion, fitted ghosts exist at every grade. -/
theorem sharedWardEquimodularPrimeDependentGammaGhostRouteKilled :
    SharedWardEquimodularPrimeDependentGammaGhostRouteKilled := by
  intro V _ _ _
  exact ⟨primeGammaTwoThreeEquimodularModuleGhostWard_iff V,
    primeGammaTwoThreeUnconstrainedModuleGhostWard_exists V,
    everyFrankensteinEquimodularPrimeDependentGammaGhostDescends_iff_sharedFourRouteWardEndpoint V,
    everyFrankensteinEquimodularPrimeDependentGammaGhostDescends_iff_riemannHypothesis V⟩

end

end RHTower
