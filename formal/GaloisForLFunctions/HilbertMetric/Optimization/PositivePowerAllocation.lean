import GaloisForLFunctions.HilbertMetric.Optimization.WeightedSimplexResponse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Positive power mixtures and allocation drift

Logarithmic amplitudes and exponents give positive finite power mixtures.
Their marginal-gradient sampling law has an effective exponent whose derivative
is minus its variance. Matching this marginal to a single capacity power gives
an explicit globally optimal path and a variance-controlled allocation drift.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Optimization
noncomputable section
variable {n : ℕ}

/-- Derivative moments of a positive mixture in logarithmic resource. -/
def powerMixtureMoment (c b : Fin (n+1) → ℝ) (j : ℕ) (v : ℝ) : ℝ :=
  ∑ i, Real.exp (c i) * Real.exp (b i)^j * Real.exp (-Real.exp (b i)*v)

lemma powerMixtureMoment_pos (c b : Fin (n+1) → ℝ) (j : ℕ) (v : ℝ) :
    0 < powerMixtureMoment c b j v := by
  exact Finset.sum_pos (fun i _ => by positivity) Finset.univ_nonempty

lemma powerMixtureMoment_hasDerivAt (c b : Fin (n+1) → ℝ) (j : ℕ) (v : ℝ) :
    HasDerivAt (powerMixtureMoment c b j) (-powerMixtureMoment c b (j+1) v) v := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((hasDerivAt_id v).const_mul (-Real.exp (b i))).exp).const_mul
      (Real.exp (c i)*Real.exp (b i)^j))
  convert! h using 1
  · funext w
    simp only [powerMixtureMoment,Finset.sum_apply,id_eq]
  · simp only [powerMixtureMoment, ← Finset.sum_neg_distrib, pow_succ,id_eq]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The marginal-gradient law is the inverse-metric sampling law already used on the simplex. -/
def powerMixtureSampling (c b : Fin (n+1) → ℝ) (v : ℝ) : Fin (n+1) → ℝ :=
  simplexSampling (fun i => -(c i+b i-Real.exp (b i)*v))

lemma powerMixtureSampling_eq (c b : Fin (n+1) → ℝ) (v : ℝ) (i : Fin (n+1)) :
    powerMixtureSampling c b v i =
      Real.exp (c i)*Real.exp (b i)*Real.exp (-Real.exp (b i)*v) /
        powerMixtureMoment c b 1 v := by
  simp only [powerMixtureSampling,simplexSampling,simplexCompliance,simplexComplianceMass,
    powerMixtureMoment,pow_one,neg_mul,Real.exp_neg,inv_inv,Real.exp_sub,Real.exp_add,div_eq_mul_inv]

/-- Mean exponent under the marginal-gradient law. -/
def powerMixtureExponent (c b : Fin (n+1) → ℝ) (v : ℝ) : ℝ :=
  powerMixtureMoment c b 2 v / powerMixtureMoment c b 1 v

def powerMixtureVariance (c b : Fin (n+1) → ℝ) (v : ℝ) : ℝ :=
  powerMixtureMoment c b 3 v / powerMixtureMoment c b 1 v - powerMixtureExponent c b v^2

lemma powerMixtureExponent_pos (c b : Fin (n+1) → ℝ) (v : ℝ) :
    0 < powerMixtureExponent c b v :=
  div_pos (powerMixtureMoment_pos c b 2 v) (powerMixtureMoment_pos c b 1 v)

lemma powerMixtureSampling_moment (c b : Fin (n+1) → ℝ) (v : ℝ) (j : ℕ) :
    ∑ i, powerMixtureSampling c b v i * Real.exp (b i)^j =
      powerMixtureMoment c b (j+1) v / powerMixtureMoment c b 1 v := by
  simp_rw [powerMixtureSampling_eq,div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

/-- Variance is an actual positive weighted sum of centered squares. -/
theorem powerMixtureVariance_eq_centered (c b : Fin (n+1) → ℝ) (v : ℝ) :
    powerMixtureVariance c b v =
      ∑ i, powerMixtureSampling c b v i * (Real.exp (b i)-powerMixtureExponent c b v)^2 := by
  have hmean : ∑ i, powerMixtureSampling c b v i * Real.exp (b i) = powerMixtureExponent c b v := by
    simpa only [pow_one,powerMixtureExponent] using powerMixtureSampling_moment c b v 1
  have hsum : ∑ i, powerMixtureSampling c b v i = 1 := simplexSampling_sum _
  have hterm (i : Fin (n+1)) :
      powerMixtureSampling c b v i * (Real.exp (b i)-powerMixtureExponent c b v)^2 =
      powerMixtureSampling c b v i * Real.exp (b i)^2 -
        2*powerMixtureExponent c b v * (powerMixtureSampling c b v i*Real.exp (b i)) +
        powerMixtureSampling c b v i * powerMixtureExponent c b v^2 := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,
    hmean,hsum,powerMixtureSampling_moment]
  unfold powerMixtureVariance
  ring

lemma powerMixtureVariance_nonneg (c b : Fin (n+1) → ℝ) (v : ℝ) :
    0 ≤ powerMixtureVariance c b v := by
  rw [powerMixtureVariance_eq_centered]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (simplexSampling_pos _ i).le (sq_nonneg _)

/-- The effective exponent decays at exactly the variance of the exponent spectrum. -/
theorem powerMixtureExponent_hasDerivAt (c b : Fin (n+1) → ℝ) (v : ℝ) :
    HasDerivAt (powerMixtureExponent c b) (-powerMixtureVariance c b v) v := by
  have h := (powerMixtureMoment_hasDerivAt c b 2 v).div
    (powerMixtureMoment_hasDerivAt c b 1 v) (powerMixtureMoment_pos c b 1 v).ne'
  convert! h using 1
  unfold powerMixtureVariance powerMixtureExponent
  field_simp [(powerMixtureMoment_pos c b 1 v).ne']
  ring

/-- Zero drift occurs exactly for a single exponent, including repeated amplitudes. -/
theorem powerMixtureVariance_eq_zero_iff (c b : Fin (n+1) → ℝ) (v : ℝ) :
    powerMixtureVariance c b v=0 ↔ ∃ r : ℝ, ∀ i, b i=r := by
  have hw (i : Fin (n+1)) : 0 < powerMixtureSampling c b v i := simplexSampling_pos _ i
  rw [powerMixtureVariance_eq_centered,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (hw i).le (sq_nonneg _))]
  simp only [Finset.mem_univ,forall_const,mul_eq_zero,(hw _).ne',false_or,
    sq_eq_zero_iff,sub_eq_zero]
  constructor
  · intro h
    refine ⟨b 0,fun i => Real.exp_injective (by rw [h i,h 0])⟩
  · rintro ⟨r,hr⟩
    have hm : powerMixtureExponent c b v=Real.exp r := by
      have h := powerMixtureSampling_moment c b v 1
      simp only [pow_one,hr,← Finset.sum_mul] at h
      rw [show (∑ i,powerMixtureSampling c b v i)=1 from simplexSampling_sum _] at h
      exact h.symm.trans (one_mul _)
    intro i
    rw [hr,hm]

/-- Capacity log-resource where its marginal matches the data mixture at `v`. -/
def matchedCapacity (a A : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) : ℝ :=
  (A+a-Real.log (powerMixtureMoment c b 1 v))/Real.exp a

def matchedBudget (a A : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) : ℝ :=
  matchedCapacity a A c b v+v

def matchedAllocationShare (a : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) : ℝ :=
  powerMixtureExponent c b v / (Real.exp a+powerMixtureExponent c b v)

lemma matchedCapacity_hasDerivAt (a A : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) :
    HasDerivAt (matchedCapacity a A c b)
      (powerMixtureExponent c b v/Real.exp a) v := by
  have h := (((powerMixtureMoment_hasDerivAt c b 1 v).log
    (powerMixtureMoment_pos c b 1 v).ne').const_sub (A+a)).div_const (Real.exp a)
  convert! h using 1
  unfold powerMixtureExponent
  ring

lemma matchedBudget_hasDerivAt (a A : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) :
    HasDerivAt (matchedBudget a A c b)
      ((Real.exp a+powerMixtureExponent c b v)/Real.exp a) v := by
  convert! (matchedCapacity_hasDerivAt a A c b v).add (hasDerivAt_id v) using 1
  all_goals
    field_simp [Real.exp_ne_zero]
    ring

/-- The capacity share is strictly between zero and one. -/
theorem matchedAllocationShare_bounds (a : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) :
    0 < matchedAllocationShare a c b v ∧ matchedAllocationShare a c b v < 1 := by
  have hp := powerMixtureExponent_pos c b v
  have ha := Real.exp_pos a
  constructor
  · exact div_pos hp (add_pos ha hp)
  · exact (div_lt_one (add_pos ha hp)).mpr (lt_add_of_pos_left _ ha)

/-- Divide by the budget derivative to obtain drift per unit log-compute. -/
theorem matchedAllocationShare_hasDerivAt (a : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) :
    HasDerivAt (matchedAllocationShare a c b)
      (-Real.exp a*powerMixtureVariance c b v/(Real.exp a+powerMixtureExponent c b v)^2) v := by
  have hn := (add_pos (Real.exp_pos a) (powerMixtureExponent_pos c b v)).ne'
  have h := (powerMixtureExponent_hasDerivAt c b v).div
    ((powerMixtureExponent_hasDerivAt c b v).const_add (Real.exp a)) hn
  convert! h using 1
  ring

#print axioms powerMixtureVariance_eq_centered
#print axioms powerMixtureExponent_hasDerivAt
#print axioms powerMixtureVariance_eq_zero_iff
#print axioms matchedAllocationShare_hasDerivAt

/-- The two resource risk on the full logarithmic resource plane. -/
def positivePowerRisk (a A : ℝ) (c b : Fin (n+1) → ℝ) (u v : ℝ) : ℝ :=
  Real.exp (A-Real.exp a*u)+powerMixtureMoment c b 0 v

lemma matchedCapacity_balance (a A : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) :
    Real.exp a*Real.exp (A-Real.exp a*matchedCapacity a A c b v)=
      powerMixtureMoment c b 1 v := by
  rw [← Real.exp_add]
  have he : a+(A-Real.exp a*matchedCapacity a A c b v)=
      Real.log (powerMixtureMoment c b 1 v) := by
    unfold matchedCapacity
    field_simp [Real.exp_ne_zero]
    ring
  rw [he,Real.exp_log (powerMixtureMoment_pos c b 1 v)]

private lemma exp_tangent_gap_nonneg (x : ℝ) : 0 ≤ Real.exp x-1-x := by
  linarith only [Real.add_one_le_exp x]

private lemma exp_tangent_gap_pos {x : ℝ} (hx : x ≠ 0) : 0 < Real.exp x-1-x := by
  linarith only [Real.add_one_lt_exp hx]

/-- Exact regret on each fixed-budget line, as positive exponential tangent gaps. -/
theorem matchedCapacity_exact_regret (a A : ℝ) (c b : Fin (n+1) → ℝ) (v h : ℝ) :
    positivePowerRisk a A c b (matchedCapacity a A c b v+h) (v-h)-
      positivePowerRisk a A c b (matchedCapacity a A c b v) v =
      Real.exp (A-Real.exp a*matchedCapacity a A c b v) *
        (Real.exp (-Real.exp a*h)-1+Real.exp a*h) +
      ∑ i, Real.exp (c i)*Real.exp (-Real.exp (b i)*v) *
        (Real.exp (Real.exp (b i)*h)-1-Real.exp (b i)*h) := by
  have hcap : Real.exp (A-Real.exp a*(matchedCapacity a A c b v+h))=
      Real.exp (A-Real.exp a*matchedCapacity a A c b v)*Real.exp (-Real.exp a*h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdata (i : Fin (n+1)) : Real.exp (-Real.exp (b i)*(v-h))=
      Real.exp (-Real.exp (b i)*v)*Real.exp (Real.exp (b i)*h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsplit (i : Fin (n+1)) :
      Real.exp (c i)*Real.exp (-Real.exp (b i)*v) *
        (Real.exp (Real.exp (b i)*h)-1-Real.exp (b i)*h) =
      (Real.exp (c i)*(Real.exp (-Real.exp (b i)*v)*Real.exp (Real.exp (b i)*h))-
        Real.exp (c i)*Real.exp (-Real.exp (b i)*v)) -
        (Real.exp (c i)*Real.exp (b i)*Real.exp (-Real.exp (b i)*v))*h := by ring
  simp only [positivePowerRisk,powerMixtureMoment,pow_zero,mul_one,hcap,hdata,hsplit,
    Finset.sum_sub_distrib,← Finset.sum_mul]
  have hb := matchedCapacity_balance a A c b v
  simp only [powerMixtureMoment,pow_one] at hb
  linear_combination -h*hb

/-- Every point of the explicitly constructed path minimizes its actual fixed-budget risk. -/
theorem matchedCapacity_minimum (a A : ℝ) (c b : Fin (n+1) → ℝ) (v h : ℝ) :
    positivePowerRisk a A c b (matchedCapacity a A c b v) v ≤
      positivePowerRisk a A c b (matchedCapacity a A c b v+h) (v-h) := by
  apply sub_nonneg.mp
  rw [matchedCapacity_exact_regret]
  apply add_nonneg
  · apply mul_nonneg (Real.exp_pos _).le
    simpa only [sub_neg_eq_add,neg_mul] using exp_tangent_gap_nonneg (-Real.exp a*h)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (exp_tangent_gap_nonneg _)

/-- Equality holds only at the matched allocation; no stationary-point premise is required. -/
theorem matchedCapacity_unique (a A : ℝ) (c b : Fin (n+1) → ℝ) (v h : ℝ) :
    positivePowerRisk a A c b (matchedCapacity a A c b v+h) (v-h)=
      positivePowerRisk a A c b (matchedCapacity a A c b v) v ↔ h=0 := by
  constructor
  · intro he
    by_contra hh
    have hc : 0 < Real.exp (A-Real.exp a*matchedCapacity a A c b v) *
        (Real.exp (-Real.exp a*h)-1+Real.exp a*h) := by
      apply mul_pos (Real.exp_pos _)
      simpa only [sub_neg_eq_add,neg_mul] using
        exp_tangent_gap_pos (mul_ne_zero (neg_ne_zero.mpr (Real.exp_ne_zero a)) hh)
    have hd : 0 ≤ ∑ i, Real.exp (c i)*Real.exp (-Real.exp (b i)*v)*
        (Real.exp (Real.exp (b i)*h)-1-Real.exp (b i)*h) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (exp_tangent_gap_nonneg _)
    have hr := matchedCapacity_exact_regret a A c b v h
    rw [he,sub_self] at hr
    linarith only [hr,hc,hd]
  · rintro rfl
    simp only [add_zero,sub_zero]

/-- Allocation drift per unit logarithmic budget is the negative variance times a positive factor. -/
theorem matchedAllocationShare_budget_drift (a A : ℝ) (c b : Fin (n+1) → ℝ) (v : ℝ) :
    deriv (matchedAllocationShare a c b) v / deriv (matchedBudget a A c b) v =
      -(Real.exp a)^2*powerMixtureVariance c b v /
        (Real.exp a+powerMixtureExponent c b v)^3 := by
  rw [(matchedAllocationShare_hasDerivAt a c b v).deriv,
    (matchedBudget_hasDerivAt a A c b v).deriv]
  field_simp [Real.exp_ne_zero,
    (add_pos (Real.exp_pos a) (powerMixtureExponent_pos c b v)).ne']

#print axioms matchedCapacity_exact_regret
#print axioms matchedCapacity_minimum
#print axioms matchedCapacity_unique
#print axioms matchedAllocationShare_budget_drift
end
end GaloisForLFunctions.HilbertMetric.Optimization
