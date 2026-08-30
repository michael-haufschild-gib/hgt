import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityLeadingJetBalance
import GaloisForLFunctions.HTGeometry.ExpRayL2

/-!
# Reflected bi-heat source-faithful Markov normalization no-go

The literal multiplicity-leading RBH channels form an ordered positive pair.  This file closes two
proposed ways of producing their missing equality.

First, any injective reflection-equivariant normalization reflects fixed points.  Hence no
nonlinear source-faithful normalization can turn an off-wall RBH pair into a balanced output; doing
so necessarily identifies the two points of a free reflection orbit.

Second, every reflection-equivariant, mass-conserving real two-channel Markov generator is

`L_r(u,v) = (r(v-u), r(u-v))`, with one rate `r >= 0`.

Its exact flow multiplies channel difference by `exp(-2 r t)`.  The flow is positive at
nonnegative time, obeys the semigroup law, solves the classified generator equation, and is
injective at every finite time.  Thus finite-time balance is exactly the original RBH wall
condition and globally is exactly RH.  At positive rate, however, the difference tends to zero for
every input at infinite time, so limiting equilibrium is universal and nonselective.

This kills source-faithful normalization and reflection-symmetric Markov heat equilibration as
independent RBH producers.  A surviving proof needs an additional source law forcing the raw Ward
charge to vanish.

`[NEW] [CLASSIFICATION] [ROUTE-CLASS NO-GO] [EXACT RECEIVER] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## Arbitrary nonlinear source-faithful normalizations -/

/-- Exchange of two reflected source channels. -/
def reflectedBiHeatChannelSwap {α : Type*} (p : α × α) : α × α := (p.2, p.1)

/-- A two-channel source is reflection-fixed exactly when its channels agree. -/
theorem reflectedBiHeatChannelSwap_fixed_iff {α : Type*} (p : α × α) :
    reflectedBiHeatChannelSwap p = p ↔ p.1 = p.2 := by
  constructor
  · intro h
    exact (congrArg Prod.fst h).symm
  · intro h
    apply Prod.ext
    · exact h.symm
    · exact h

/-- Every injective equivariant normalization reflects the fixed locus.  No algebraic,
topological, metric, or finite-dimensional structure on source or target is required. -/
theorem reflectedBiHeatSourceFaithful_fixed_iff
    {X Y : Type*} (sourceReflection : X → X) (targetReflection : Y → Y)
    (normalize : X → Y)
    (hequiv : ∀ x, normalize (sourceReflection x) = targetReflection (normalize x))
    (hfaithful : Function.Injective normalize) (x : X) :
    targetReflection (normalize x) = normalize x ↔ sourceReflection x = x := by
  constructor
  · intro hfixed
    apply hfaithful
    rw [hequiv]
    exact hfixed
  · intro hfixed
    rw [← hequiv, hfixed]

/-- Sending a free reflected source orbit to a fixed output necessarily destroys source
faithfulness. -/
theorem not_injective_reflectedBiHeatNormalization_of_fixed_free
    {X Y : Type*} (sourceReflection : X → X) (targetReflection : Y → Y)
    (normalize : X → Y)
    (hequiv : ∀ x, normalize (sourceReflection x) = targetReflection (normalize x))
    {x : X} (hfixed : targetReflection (normalize x) = normalize x)
    (hfree : sourceReflection x ≠ x) :
    ¬ Function.Injective normalize := by
  intro hfaithful
  apply hfree
  apply hfaithful
  rw [hequiv]
  exact hfixed

/-! ## Complete two-channel Markov-generator classification -/

/-- General real linear two-channel generator in coordinates. -/
def reflectedBiHeatTwoChannelGenerator
    (A B C D : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (A * p.1 + B * p.2, C * p.1 + D * p.2)

/-- A real two-channel generator commutes with reflection exactly when its diagonal entries agree
and its off-diagonal entries agree. -/
theorem reflectedBiHeatTwoChannelGenerator_commutes_swap_iff
    (A B C D : ℝ) :
    (∀ p, reflectedBiHeatTwoChannelGenerator A B C D
          (reflectedBiHeatChannelSwap p) =
        reflectedBiHeatChannelSwap
          (reflectedBiHeatTwoChannelGenerator A B C D p)) ↔
      A = D ∧ B = C := by
  constructor
  · intro h
    have h10 := h (1, 0)
    have hfst := congrArg Prod.fst h10
    have hsnd := congrArg Prod.snd h10
    norm_num [reflectedBiHeatTwoChannelGenerator,
      reflectedBiHeatChannelSwap] at hfst hsnd
    exact ⟨hsnd.symm, hfst⟩
  · rintro ⟨rfl, rfl⟩ p
    apply Prod.ext <;>
      simp [reflectedBiHeatTwoChannelGenerator,
        reflectedBiHeatChannelSwap] <;> ring

/-- Infinitesimal conservation of total channel mass is exactly the pair of column-sum laws. -/
theorem reflectedBiHeatTwoChannelGenerator_mass_zero_iff
    (A B C D : ℝ) :
    (∀ p, (reflectedBiHeatTwoChannelGenerator A B C D p).1 +
        (reflectedBiHeatTwoChannelGenerator A B C D p).2 = 0) ↔
      A + C = 0 ∧ B + D = 0 := by
  constructor
  · intro h
    have h10 := h (1, 0)
    have h01 := h (0, 1)
    simpa [reflectedBiHeatTwoChannelGenerator] using And.intro h10 h01
  · rintro ⟨hAC, hBD⟩ p
    dsimp [reflectedBiHeatTwoChannelGenerator]
    linear_combination p.1 * hAC + p.2 * hBD

/-- Complete classification of reflection-equivariant conservative two-channel Markov
generators: one nonnegative exchange rate and no other freedom. -/
theorem reflectedBiHeatTwoChannelGenerator_markov_classification
    (A B C D : ℝ) :
    ((∀ p, reflectedBiHeatTwoChannelGenerator A B C D
          (reflectedBiHeatChannelSwap p) =
        reflectedBiHeatChannelSwap
          (reflectedBiHeatTwoChannelGenerator A B C D p)) ∧
      (∀ p, (reflectedBiHeatTwoChannelGenerator A B C D p).1 +
        (reflectedBiHeatTwoChannelGenerator A B C D p).2 = 0) ∧
      0 ≤ B ∧ 0 ≤ C) ↔
    ∃ r : ℝ, 0 ≤ r ∧ A = -r ∧ B = r ∧ C = r ∧ D = -r := by
  constructor
  · rintro ⟨hswap, hmass, hB, _hC⟩
    have hs :=
      (reflectedBiHeatTwoChannelGenerator_commutes_swap_iff A B C D).mp hswap
    have hm :=
      (reflectedBiHeatTwoChannelGenerator_mass_zero_iff A B C D).mp hmass
    refine ⟨B, hB, ?_, rfl, hs.2.symm, ?_⟩
    · linarith [hm.1]
    · linarith [hm.2]
  · rintro ⟨r, hr, hA, hB, hC, hD⟩
    subst A
    subst B
    subst C
    subst D
    refine ⟨
      (reflectedBiHeatTwoChannelGenerator_commutes_swap_iff
        (-r) r r (-r)).mpr ⟨rfl, rfl⟩,
      (reflectedBiHeatTwoChannelGenerator_mass_zero_iff
        (-r) r r (-r)).mpr ?_, hr, hr⟩
    constructor <;> ring

/-! ## Exact finite-time flow and infinite-time erasure -/

/-- Exact flow of the unique reflection-symmetric two-channel Markov generator with exchange
rate `r`.  Mean is fixed and difference is multiplied by `exp(-2 r t)`. -/
def reflectedBiHeatMarkovFlow (r t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 + Real.exp (-2 * r * t) * (p.1 - p.2)) / 2,
   (p.1 + p.2 - Real.exp (-2 * r * t) * (p.1 - p.2)) / 2)

/-- Exact transverse evolution law. -/
theorem reflectedBiHeatMarkovFlow_sub (r t : ℝ) (p : ℝ × ℝ) :
    (reflectedBiHeatMarkovFlow r t p).1 -
        (reflectedBiHeatMarkovFlow r t p).2 =
      Real.exp (-2 * r * t) * (p.1 - p.2) := by
  unfold reflectedBiHeatMarkovFlow
  ring

/-- The symmetric Markov flow preserves total mass. -/
theorem reflectedBiHeatMarkovFlow_add (r t : ℝ) (p : ℝ × ℝ) :
    (reflectedBiHeatMarkovFlow r t p).1 +
        (reflectedBiHeatMarkovFlow r t p).2 = p.1 + p.2 := by
  unfold reflectedBiHeatMarkovFlow
  ring

/-- The symmetric Markov flow commutes with channel reflection. -/
theorem reflectedBiHeatMarkovFlow_swap (r t : ℝ) (p : ℝ × ℝ) :
    reflectedBiHeatMarkovFlow r t (reflectedBiHeatChannelSwap p) =
      reflectedBiHeatChannelSwap (reflectedBiHeatMarkovFlow r t p) := by
  apply Prod.ext <;>
    simp [reflectedBiHeatMarkovFlow, reflectedBiHeatChannelSwap] <;> ring

/-- At nonnegative rate and time, the flow sends the positive channel cone to itself. -/
theorem reflectedBiHeatMarkovFlow_nonnegative
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {p : ℝ × ℝ} (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2) :
    0 ≤ (reflectedBiHeatMarkovFlow r t p).1 ∧
      0 ≤ (reflectedBiHeatMarkovFlow r t p).2 := by
  have hrt : 0 ≤ r * t := mul_nonneg hr ht
  have harg : -2 * r * t ≤ 0 := by linarith
  have hq0 : 0 ≤ Real.exp (-2 * r * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * r * t) ≤ 1 := Real.exp_le_one_iff.mpr harg
  constructor <;> unfold reflectedBiHeatMarkovFlow <;> dsimp
  · have : 0 ≤ (1 + Real.exp (-2 * r * t)) * p.1 +
        (1 - Real.exp (-2 * r * t)) * p.2 := by positivity
    nlinarith
  · have : 0 ≤ (1 - Real.exp (-2 * r * t)) * p.1 +
        (1 + Real.exp (-2 * r * t)) * p.2 := by positivity
    nlinarith

/-- Exact semigroup law. -/
theorem reflectedBiHeatMarkovFlow_semigroup
    (r s t : ℝ) (p : ℝ × ℝ) :
    reflectedBiHeatMarkovFlow r (s + t) p =
      reflectedBiHeatMarkovFlow r s (reflectedBiHeatMarkovFlow r t p) := by
  have hexp : Real.exp (-2 * r * (s + t)) =
      Real.exp (-2 * r * s) * Real.exp (-2 * r * t) := by
    rw [show -2 * r * (s + t) = -2 * r * s + -2 * r * t by ring,
      Real.exp_add]
  rw [Prod.ext_iff]
  constructor <;> unfold reflectedBiHeatMarkovFlow <;> dsimp <;>
    rw [hexp] <;> ring

/-- Time zero is identity. -/
theorem reflectedBiHeatMarkovFlow_zero (r : ℝ) (p : ℝ × ℝ) :
    reflectedBiHeatMarkovFlow r 0 p = p := by
  apply Prod.ext
  · simp only [reflectedBiHeatMarkovFlow, mul_zero, Real.exp_zero, one_mul]
    ring
  · simp only [reflectedBiHeatMarkovFlow, mul_zero, Real.exp_zero, one_mul]
    ring

/-- First coordinate solves the classified exchange-generator equation. -/
theorem hasDerivAt_reflectedBiHeatMarkovFlow_fst
    (r t : ℝ) (p : ℝ × ℝ) :
    HasDerivAt (fun u => (reflectedBiHeatMarkovFlow r u p).1)
      (r * ((reflectedBiHeatMarkovFlow r t p).2 -
        (reflectedBiHeatMarkovFlow r t p).1)) t := by
  have hlin : HasDerivAt (fun u : ℝ => -2 * r * u) (-2 * r) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-2 * r)
  have h :=
    ((hlin.exp.mul_const (p.1 - p.2)).add_const (p.1 + p.2)).div_const 2
  have hfun : (fun u => (reflectedBiHeatMarkovFlow r u p).1) =
      fun u => (Real.exp (-2 * r * u) * (p.1 - p.2) +
        (p.1 + p.2)) / 2 := by
    funext u
    simp only [reflectedBiHeatMarkovFlow]
    ring
  have hderiv :
      r * ((reflectedBiHeatMarkovFlow r t p).2 -
          (reflectedBiHeatMarkovFlow r t p).1) =
        Real.exp (-2 * r * t) * (-2 * r) * (p.1 - p.2) / 2 := by
    simp only [reflectedBiHeatMarkovFlow]
    ring
  rw [hfun, hderiv]
  exact h

/-- Second coordinate solves the classified exchange-generator equation. -/
theorem hasDerivAt_reflectedBiHeatMarkovFlow_snd
    (r t : ℝ) (p : ℝ × ℝ) :
    HasDerivAt (fun u => (reflectedBiHeatMarkovFlow r u p).2)
      (r * ((reflectedBiHeatMarkovFlow r t p).1 -
        (reflectedBiHeatMarkovFlow r t p).2)) t := by
  have hlin : HasDerivAt (fun u : ℝ => -2 * r * u) (-2 * r) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-2 * r)
  have h := (((hlin.exp.mul_const (p.1 - p.2)).neg).add_const
    (p.1 + p.2)).div_const 2
  have hfun : (fun u => (reflectedBiHeatMarkovFlow r u p).2) =
      fun u => (-(Real.exp (-2 * r * u) * (p.1 - p.2)) +
        (p.1 + p.2)) / 2 := by
    funext u
    simp only [reflectedBiHeatMarkovFlow]
    ring
  have hderiv :
      r * ((reflectedBiHeatMarkovFlow r t p).1 -
          (reflectedBiHeatMarkovFlow r t p).2) =
        -(Real.exp (-2 * r * t) * (-2 * r) * (p.1 - p.2)) / 2 := by
    simp only [reflectedBiHeatMarkovFlow]
    ring
  rw [hfun, hderiv]
  exact h

/-- Every finite-time flow map is injective, including at positive Markov rate. -/
theorem reflectedBiHeatMarkovFlow_injective (r t : ℝ) :
    Function.Injective (reflectedBiHeatMarkovFlow r t) := by
  intro p q h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    unfold reflectedBiHeatMarkovFlow at h1 h2
    dsimp at h1 h2
    linarith
  have hdiff : p.1 - p.2 = q.1 - q.2 := by
    have he : Real.exp (-2 * r * t) ≠ 0 := (Real.exp_pos _).ne'
    have hsub := congrArg (fun z : ℝ × ℝ => z.1 - z.2) h
    rw [reflectedBiHeatMarkovFlow_sub,
      reflectedBiHeatMarkovFlow_sub] at hsub
    exact mul_left_cancel₀ he hsub
  apply Prod.ext <;> linarith

/-- No finite time creates balance: the flow is balanced exactly when the input was balanced. -/
theorem reflectedBiHeatMarkovFlow_balance_iff
    (r t : ℝ) (p : ℝ × ℝ) :
    (reflectedBiHeatMarkovFlow r t p).1 =
        (reflectedBiHeatMarkovFlow r t p).2 ↔
      p.1 = p.2 := by
  constructor
  · intro h
    have hzero : Real.exp (-2 * r * t) * (p.1 - p.2) = 0 := by
      rw [← reflectedBiHeatMarkovFlow_sub]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hzero).resolve_left (Real.exp_pos _).ne')
  · intro h
    apply sub_eq_zero.mp
    rw [reflectedBiHeatMarkovFlow_sub, sub_eq_zero.mpr h, mul_zero]

/-- At positive rate, the transverse channel tends to zero for every input. -/
theorem reflectedBiHeatMarkovFlow_sub_tendsto
    {r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    Tendsto (fun t : ℝ =>
      (reflectedBiHeatMarkovFlow r t p).1 -
        (reflectedBiHeatMarkovFlow r t p).2) atTop (𝓝 0) := by
  simp_rw [reflectedBiHeatMarkovFlow_sub]
  have hdecay :=
    GaloisForLFunctions.HTGeometry.tendsto_exp_neg_mul_atTop_nhds_zero
      (show 0 < 2 * r by positivity)
  have hmul := hdecay.mul_const (p.1 - p.2)
  simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using hmul

/-! ## Actual RBH multiplicity-leading source and route capstone -/

/-- Ordered pair of actual multiplicity-leading RBH jet norms at aperture two. -/
def reflectedBiHeatActualLeadingNormPair (rho : XiDivisorSupport) : ℝ × ℝ :=
  (‖iteratedDeriv (xiSupportMultiplicity rho)
      (reflectedBiHeatLeftResponse 2) (rho : ℂ)‖,
   ‖iteratedDeriv (xiSupportMultiplicity rho)
      (reflectedBiHeatRightResponse 2) (rho : ℂ)‖)

/-- The actual ordered norm pair is balanced exactly on the critical wall. -/
theorem reflectedBiHeatActualLeadingNormPair_balance_iff
    (rho : XiDivisorSupport) :
    (reflectedBiHeatActualLeadingNormPair rho).1 =
        (reflectedBiHeatActualLeadingNormPair rho).2 ↔
      (rho : ℂ).re = 1 / 2 := by
  exact reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff rho

/-- Every arbitrary nonlinear source-faithful reflection-natural normalization of the actual RBH
pair has fixed output exactly on the critical wall. -/
theorem reflectedBiHeatActualLeadingNormPair_faithful_fixed_iff
    {Y : Type*} (targetReflection : Y → Y) (normalize : (ℝ × ℝ) → Y)
    (hequiv : ∀ p, normalize (reflectedBiHeatChannelSwap p) =
      targetReflection (normalize p))
    (hfaithful : Function.Injective normalize) (rho : XiDivisorSupport) :
    targetReflection (normalize (reflectedBiHeatActualLeadingNormPair rho)) =
        normalize (reflectedBiHeatActualLeadingNormPair rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatSourceFaithful_fixed_iff
      reflectedBiHeatChannelSwap targetReflection normalize hequiv hfaithful,
    reflectedBiHeatChannelSwap_fixed_iff,
    reflectedBiHeatActualLeadingNormPair_balance_iff]

/-- If an off-wall actual RBH pair becomes fixed after an equivariant normalization, the
normalization necessarily loses source information. -/
theorem reflectedBiHeatActualLeadingNormPair_not_injective_of_offWall_fixed
    {Y : Type*} (targetReflection : Y → Y) (normalize : (ℝ × ℝ) → Y)
    (hequiv : ∀ p, normalize (reflectedBiHeatChannelSwap p) =
      targetReflection (normalize p))
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2)
    (hfixed :
      targetReflection (normalize (reflectedBiHeatActualLeadingNormPair rho)) =
        normalize (reflectedBiHeatActualLeadingNormPair rho)) :
    ¬ Function.Injective normalize := by
  apply not_injective_reflectedBiHeatNormalization_of_fixed_free
    reflectedBiHeatChannelSwap targetReflection normalize hequiv hfixed
  intro hswap
  have hbalance :=
    (reflectedBiHeatChannelSwap_fixed_iff
      (reflectedBiHeatActualLeadingNormPair rho)).mp hswap
  exact hoff ((reflectedBiHeatActualLeadingNormPair_balance_iff rho).mp hbalance)

/-- Finite-time Markov evolution of the actual RBH pair balances exactly on the critical wall. -/
theorem reflectedBiHeatActualLeadingNormPair_markovFlow_balance_iff
    (r t : ℝ) (rho : XiDivisorSupport) :
    (reflectedBiHeatMarkovFlow r t
        (reflectedBiHeatActualLeadingNormPair rho)).1 =
      (reflectedBiHeatMarkovFlow r t
        (reflectedBiHeatActualLeadingNormPair rho)).2 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatMarkovFlow_balance_iff,
    reflectedBiHeatActualLeadingNormPair_balance_iff]

/-- At every fixed finite Markov time, universal actual RBH balance remains exactly RH. -/
theorem riemannHypothesis_iff_reflectedBiHeatActualLeadingNormPair_markovFlow_balance
    (r t : ℝ) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        (reflectedBiHeatMarkovFlow r t
            (reflectedBiHeatActualLeadingNormPair rho)).1 =
          (reflectedBiHeatMarkovFlow r t
            (reflectedBiHeatActualLeadingNormPair rho)).2 := by
  rw [riemannHypothesis_iff_reflectedBiHeatMultiplicityLeadingJetNorms_two_eq]
  constructor <;> intro h rho
  · exact (reflectedBiHeatMarkovFlow_balance_iff r t _).mpr (h rho)
  · exact (reflectedBiHeatMarkovFlow_balance_iff r t _).mp (h rho)

/-- Closed route-class no-go.  Arbitrary faithful equivariant normalization and every finite-time
symmetric Markov heat flow preserve the exact RBH wall locus; positive-rate infinite-time balance
is instead universal. -/
theorem reflectedBiHeat_sourceFaithfulMarkovNormalization_noGo :
    (∀ {Y : Type} (targetReflection : Y → Y) (normalize : (ℝ × ℝ) → Y),
      (∀ p, normalize (reflectedBiHeatChannelSwap p) =
        targetReflection (normalize p)) →
      Function.Injective normalize →
      ∀ rho : XiDivisorSupport,
        targetReflection
            (normalize (reflectedBiHeatActualLeadingNormPair rho)) =
          normalize (reflectedBiHeatActualLeadingNormPair rho) ↔
            (rho : ℂ).re = 1 / 2) ∧
    (∀ A B C D : ℝ,
      ((∀ p, reflectedBiHeatTwoChannelGenerator A B C D
            (reflectedBiHeatChannelSwap p) =
          reflectedBiHeatChannelSwap
            (reflectedBiHeatTwoChannelGenerator A B C D p)) ∧
        (∀ p, (reflectedBiHeatTwoChannelGenerator A B C D p).1 +
          (reflectedBiHeatTwoChannelGenerator A B C D p).2 = 0) ∧
        0 ≤ B ∧ 0 ≤ C) ↔
      ∃ r : ℝ, 0 ≤ r ∧ A = -r ∧ B = r ∧ C = r ∧ D = -r) ∧
    (∀ r t : ℝ, ∀ rho : XiDivisorSupport,
      (reflectedBiHeatMarkovFlow r t
          (reflectedBiHeatActualLeadingNormPair rho)).1 =
        (reflectedBiHeatMarkovFlow r t
          (reflectedBiHeatActualLeadingNormPair rho)).2 ↔
          (rho : ℂ).re = 1 / 2) ∧
    (∀ r t : ℝ, RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        (reflectedBiHeatMarkovFlow r t
            (reflectedBiHeatActualLeadingNormPair rho)).1 =
          (reflectedBiHeatMarkovFlow r t
            (reflectedBiHeatActualLeadingNormPair rho)).2) ∧
    (∀ r : ℝ, 0 < r → ∀ rho : XiDivisorSupport,
      Tendsto (fun t : ℝ =>
        (reflectedBiHeatMarkovFlow r t
            (reflectedBiHeatActualLeadingNormPair rho)).1 -
          (reflectedBiHeatMarkovFlow r t
            (reflectedBiHeatActualLeadingNormPair rho)).2) atTop (𝓝 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Y targetReflection normalize hequiv hfaithful rho
    exact reflectedBiHeatActualLeadingNormPair_faithful_fixed_iff
      targetReflection normalize hequiv hfaithful rho
  · exact reflectedBiHeatTwoChannelGenerator_markov_classification
  · exact reflectedBiHeatActualLeadingNormPair_markovFlow_balance_iff
  · exact riemannHypothesis_iff_reflectedBiHeatActualLeadingNormPair_markovFlow_balance
  · intro r hr rho
    exact reflectedBiHeatMarkovFlow_sub_tendsto hr
      (reflectedBiHeatActualLeadingNormPair rho)

end

end RHTower
