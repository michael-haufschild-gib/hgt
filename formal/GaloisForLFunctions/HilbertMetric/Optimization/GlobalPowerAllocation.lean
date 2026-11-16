import GaloisForLFunctions.HilbertMetric.Optimization.PositivePowerAllocation
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Global optimal allocation at every positive compute budget

The matched logarithmic budget is a continuous increasing bijection of the real
line. Its inverse constructs the unique constrained optimizer at every budget.
Inverse differentiation transfers exponent variance to the actual budget trajectory.
-/

open Set Filter Topology
namespace GaloisForLFunctions.HilbertMetric.Optimization
noncomputable section
variable {n : ℕ}

lemma matchedCapacity_strictMono (a A : ℝ) (c b : Fin (n+1) → ℝ) :
    StrictMono (matchedCapacity a A c b) :=
  strictMono_of_hasDerivAt_pos (matchedCapacity_hasDerivAt a A c b)
    (fun v => div_pos (powerMixtureExponent_pos c b v) (Real.exp_pos a))

lemma matchedBudget_strictMono (a A : ℝ) (c b : Fin (n+1) → ℝ) :
    StrictMono (matchedBudget a A c b) :=
  strictMono_of_hasDerivAt_pos (matchedBudget_hasDerivAt a A c b)
    (fun v => div_pos (add_pos (Real.exp_pos a) (powerMixtureExponent_pos c b v)) (Real.exp_pos a))

/-- The matched path covers every logarithmic compute budget. -/
theorem matchedBudget_surjective (a A : ℝ) (c b : Fin (n+1) → ℝ) :
    Function.Surjective (matchedBudget a A c b) := by
  intro t
  let z := t-matchedCapacity a A c b 0
  have hm := (matchedCapacity_strictMono a A c b).monotone
  have hlo : matchedBudget a A c b (min 0 z) ≤ t := by
    have hg := hm (min_le_left (0:ℝ) z)
    have hz := min_le_right (0:ℝ) z
    dsimp only [matchedBudget]
    dsimp only [z] at hz
    linarith only [hg,hz]
  have hhi : t ≤ matchedBudget a A c b (max 0 z) := by
    have hg := hm (le_max_left (0:ℝ) z)
    have hz := le_max_right (0:ℝ) z
    dsimp only [matchedBudget]
    dsimp only [z] at hz
    linarith only [hg,hz]
  have hc : Continuous (matchedBudget a A c b) :=
    continuous_iff_continuousAt.mpr fun v => (matchedBudget_hasDerivAt a A c b v).continuousAt
  obtain ⟨v,_,hv⟩ := intermediate_value_Icc
    ((min_le_left (0:ℝ) z).trans (le_max_left (0:ℝ) z)) hc.continuousOn ⟨hlo,hhi⟩
  exact ⟨v,hv⟩

/-- The resource-to-budget correspondence as an order isomorphism. -/
def matchedBudgetIso (a A : ℝ) (c b : Fin (n+1) → ℝ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (matchedBudget a A c b)
    (matchedBudget_strictMono a A c b) (matchedBudget_surjective a A c b)

/-- Optimal log-data resource at the prescribed log-compute budget. -/
def optimalLogData (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) : ℝ :=
  (matchedBudgetIso a A c b).symm t

def optimalLogCapacity (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) : ℝ :=
  matchedCapacity a A c b (optimalLogData a A c b t)

def optimalCapacityShare (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) : ℝ :=
  matchedAllocationShare a c b (optimalLogData a A c b t)

lemma optimalLogData_budget (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) :
    matchedBudget a A c b (optimalLogData a A c b t)=t :=
  (matchedBudgetIso a A c b).apply_symm_apply t

/-- The constructed allocation satisfies the prescribed compute constraint exactly. -/
theorem optimalLogResources_sum (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) :
    optimalLogCapacity a A c b t+optimalLogData a A c b t=t :=
  optimalLogData_budget a A c b t

lemma optimalLogData_hasDerivAt (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) :
    HasDerivAt (optimalLogData a A c b)
      (Real.exp a/(Real.exp a+powerMixtureExponent c b (optimalLogData a A c b t))) t := by
  have hn : (Real.exp a+powerMixtureExponent c b (optimalLogData a A c b t))/Real.exp a ≠ 0 :=
    (div_pos (add_pos (Real.exp_pos a) (powerMixtureExponent_pos c b _)) (Real.exp_pos a)).ne'
  have h := HasDerivAt.of_local_left_inverse
    ((matchedBudgetIso a A c b).symm.continuous.continuousAt)
    (matchedBudget_hasDerivAt a A c b (optimalLogData a A c b t)) hn
    (Eventually.of_forall (optimalLogData_budget a A c b))
  convert! h using 1
  simp only [optimalLogData,inv_div]

/-- The allocation share is the derivative of the actual optimal capacity path. -/
theorem optimalLogCapacity_hasDerivAt (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) :
    HasDerivAt (optimalLogCapacity a A c b) (optimalCapacityShare a A c b t) t := by
  have h := (matchedCapacity_hasDerivAt a A c b (optimalLogData a A c b t)).comp t
    (optimalLogData_hasDerivAt a A c b t)
  convert! h using 1
  unfold optimalCapacityShare matchedAllocationShare
  field_simp [Real.exp_ne_zero]

/-- Global optimality on every iso-compute line, without an assumed minimizer. -/
theorem optimalLogResources_minimum (a A : ℝ) (c b : Fin (n+1) → ℝ) (t u : ℝ) :
    positivePowerRisk a A c b (optimalLogCapacity a A c b t) (optimalLogData a A c b t) ≤
      positivePowerRisk a A c b u (t-u) := by
  have h := matchedCapacity_minimum a A c b (optimalLogData a A c b t)
    (u-optimalLogCapacity a A c b t)
  have hb := optimalLogResources_sum a A c b t
  change positivePowerRisk a A c b (optimalLogCapacity a A c b t) (optimalLogData a A c b t) ≤
    positivePowerRisk a A c b (optimalLogCapacity a A c b t+(u-optimalLogCapacity a A c b t))
      (optimalLogData a A c b t-(u-optimalLogCapacity a A c b t)) at h
  rw [show optimalLogCapacity a A c b t+(u-optimalLogCapacity a A c b t)=u by ring,
    show optimalLogData a A c b t-(u-optimalLogCapacity a A c b t)=t-u by linarith only [hb]] at h
  exact h

/-- Equality characterizes the constructed optimizer for every budget. -/
theorem optimalLogResources_unique (a A : ℝ) (c b : Fin (n+1) → ℝ) (t u : ℝ) :
    positivePowerRisk a A c b u (t-u)=
      positivePowerRisk a A c b (optimalLogCapacity a A c b t) (optimalLogData a A c b t) ↔
        u=optimalLogCapacity a A c b t := by
  have h := matchedCapacity_unique a A c b (optimalLogData a A c b t)
    (u-optimalLogCapacity a A c b t)
  have hb := optimalLogResources_sum a A c b t
  have h₁ : matchedCapacity a A c b (optimalLogData a A c b t)+(u-optimalLogCapacity a A c b t)=u := by
    change optimalLogCapacity a A c b t+(u-optimalLogCapacity a A c b t)=u
    ring
  have h₂ : optimalLogData a A c b t-(u-optimalLogCapacity a A c b t)=t-u := by linarith only [hb]
  rw [h₁,h₂,sub_eq_zero] at h
  simpa only [optimalLogCapacity] using h

/-- The actual budget trajectory obeys the exponent-variance drift law. -/
theorem optimalCapacityShare_hasDerivAt (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) :
    HasDerivAt (optimalCapacityShare a A c b)
      (-(Real.exp a)^2*powerMixtureVariance c b (optimalLogData a A c b t) /
        (Real.exp a+powerMixtureExponent c b (optimalLogData a A c b t))^3) t := by
  have h := (matchedAllocationShare_hasDerivAt a c b (optimalLogData a A c b t)).comp t
    (optimalLogData_hasDerivAt a A c b t)
  convert! h using 1
  field_simp [(add_pos (Real.exp_pos a) (powerMixtureExponent_pos c b _)).ne']

#print axioms matchedBudget_surjective
#print axioms optimalLogResources_minimum
#print axioms optimalLogResources_unique
#print axioms optimalLogCapacity_hasDerivAt
#print axioms optimalCapacityShare_hasDerivAt

/-- The actual optimum shifts monotonically away from capacity as the exponent mixture changes. -/
theorem optimalCapacityShare_deriv_nonpos (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) :
    deriv (optimalCapacityShare a A c b) t ≤ 0 := by
  rw [(optimalCapacityShare_hasDerivAt a A c b t).deriv]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (powerMixtureVariance_nonneg _ _ _))
    (pow_nonneg (add_pos (Real.exp_pos a) (powerMixtureExponent_pos c b _)).le _)

/-- A constant local allocation share is possible exactly when the data spectrum has one exponent. -/
theorem optimalCapacityShare_deriv_eq_zero_iff (a A : ℝ) (c b : Fin (n+1) → ℝ) (t : ℝ) :
    deriv (optimalCapacityShare a A c b) t=0 ↔ ∃ r : ℝ, ∀ i, b i=r := by
  rw [(optimalCapacityShare_hasDerivAt a A c b t).deriv,div_eq_zero_iff]
  have hn := (add_pos (Real.exp_pos a) (powerMixtureExponent_pos c b (optimalLogData a A c b t))).ne'
  have hd := pow_ne_zero 3 hn
  have he : -(Real.exp a)^2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 (Real.exp_ne_zero a))
  simp only [hd,or_false,mul_eq_zero,he,false_or]
  exact powerMixtureVariance_eq_zero_iff c b _

#print axioms optimalCapacityShare_deriv_nonpos
#print axioms optimalCapacityShare_deriv_eq_zero_iff

/-- Global monotonicity follows from the exact variance law along the constructed optimizer. -/
theorem optimalCapacityShare_antitone (a A : ℝ) (c b : Fin (n+1) → ℝ) :
    Antitone (optimalCapacityShare a A c b) :=
  antitone_of_deriv_nonpos
    (fun t => (optimalCapacityShare_hasDerivAt a A c b t).differentiableAt)
    (optimalCapacityShare_deriv_nonpos a A c b)

#print axioms optimalCapacityShare_antitone
end
end GaloisForLFunctions.HilbertMetric.Optimization
