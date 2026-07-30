import GaloisForLFunctions.HilbertMetric.TransverseDegreeCurvature
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Coherent collision jets at the first transverse phase crossing

For fixed real `a` and `b`, put
`y ε = ε² a + ε¹⁰ b`.  This module proves the exact order-ten jets of
`y(ε)^q exp(y(ε))` for `q = 0, 1, 2`.  These are the value and first two scale-derivative
entries needed when the degree-five transverse graph is approached by distinct coherent
vectors.  The statements use `IsLittleO`; no convergence certificate or numerical estimate is
assumed.
-/

open Filter Asymptotics

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

private def taylorFive (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120

private def taylorFour (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24

private def taylorThree (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6

/-- Inner-product exponent along a degree-five transverse coherent collision. -/
def coherentCollisionExponent (a b e : ℝ) : ℝ := e ^ 2 * a + e ^ 10 * b

private def collisionCrossQuotient (a b e : ℝ) : ℝ :=
  e ^ 2 * a * b + e ^ 10 * b ^ 2 / 2 +
  e ^ 4 * a ^ 2 * b / 2 + e ^ 12 * a * b ^ 2 / 2 + e ^ 20 * b ^ 3 / 6 +
  e ^ 6 * a ^ 3 * b / 6 + e ^ 14 * a ^ 2 * b ^ 2 / 4 +
    e ^ 22 * a * b ^ 3 / 6 + e ^ 30 * b ^ 4 / 24 +
  e ^ 8 * a ^ 4 * b / 24 + e ^ 16 * a ^ 3 * b ^ 2 / 12 +
    e ^ 24 * a ^ 2 * b ^ 3 / 12 + e ^ 32 * a * b ^ 4 / 24 +
    e ^ 40 * b ^ 5 / 120

private def collisionFirstCrossQuotient (a b e : ℝ) : ℝ :=
  2 * e ^ 2 * a * b + e ^ 10 * b ^ 2 +
  3 * e ^ 4 * a ^ 2 * b / 2 + 3 * e ^ 12 * a * b ^ 2 / 2 + e ^ 20 * b ^ 3 / 2 +
  2 * e ^ 6 * a ^ 3 * b / 3 + e ^ 14 * a ^ 2 * b ^ 2 +
    2 * e ^ 22 * a * b ^ 3 / 3 + e ^ 30 * b ^ 4 / 6 +
  5 * e ^ 8 * a ^ 4 * b / 24 + 5 * e ^ 16 * a ^ 3 * b ^ 2 / 12 +
    5 * e ^ 24 * a ^ 2 * b ^ 3 / 12 + 5 * e ^ 32 * a * b ^ 4 / 24 +
    e ^ 40 * b ^ 5 / 24

private def collisionSecondCrossQuotient (a b e : ℝ) : ℝ :=
  2 * e ^ 2 * a * b + e ^ 10 * b ^ 2 +
  3 * e ^ 4 * a ^ 2 * b + 3 * e ^ 12 * a * b ^ 2 + e ^ 20 * b ^ 3 +
  2 * e ^ 6 * a ^ 3 * b + 3 * e ^ 14 * a ^ 2 * b ^ 2 +
    2 * e ^ 22 * a * b ^ 3 + e ^ 30 * b ^ 4 / 2 +
  5 * e ^ 8 * a ^ 4 * b / 6 + 5 * e ^ 16 * a ^ 3 * b ^ 2 / 3 +
    5 * e ^ 24 * a ^ 2 * b ^ 3 / 3 + 5 * e ^ 32 * a * b ^ 4 / 6 +
    e ^ 40 * b ^ 5 / 6

private theorem collisionCrossQuotient_eq (a b e : ℝ) :
    (taylorFive (coherentCollisionExponent a b e) - taylorFive (e ^ 2 * a) - e ^ 10 * b) /
        e ^ 10 = collisionCrossQuotient a b e := by
  by_cases he : e = 0
  · subst e
    simp [taylorFive, coherentCollisionExponent, collisionCrossQuotient]
  · field_simp [pow_ne_zero 10 he]
    unfold taylorFive coherentCollisionExponent collisionCrossQuotient
    ring

private theorem collisionFirstCrossQuotient_eq (a b e : ℝ) :
    (coherentCollisionExponent a b e * taylorFour (coherentCollisionExponent a b e) -
        e ^ 2 * a * taylorFour (e ^ 2 * a) - e ^ 10 * b) /
        e ^ 10 = collisionFirstCrossQuotient a b e := by
  by_cases he : e = 0
  · subst e
    simp [taylorFour, coherentCollisionExponent, collisionFirstCrossQuotient]
  · field_simp [pow_ne_zero 10 he]
    unfold taylorFour coherentCollisionExponent collisionFirstCrossQuotient
    ring

private theorem collisionSecondCrossQuotient_eq (a b e : ℝ) :
    (coherentCollisionExponent a b e ^ 2 * taylorThree (coherentCollisionExponent a b e) -
        (e ^ 2 * a) ^ 2 * taylorThree (e ^ 2 * a)) /
        e ^ 10 = collisionSecondCrossQuotient a b e := by
  by_cases he : e = 0
  · subst e
    simp [taylorThree, coherentCollisionExponent, collisionSecondCrossQuotient]
  · field_simp [pow_ne_zero 10 he]
    unfold taylorThree coherentCollisionExponent collisionSecondCrossQuotient
    ring

private theorem tendsto_collisionCrossQuotient_zero (a b : ℝ) :
    Tendsto (collisionCrossQuotient a b) (nhds 0) (nhds 0) := by
  have hcont : ContinuousAt (collisionCrossQuotient a b) 0 := by
    unfold collisionCrossQuotient
    fun_prop
  change Tendsto (collisionCrossQuotient a b) (nhds 0)
    (nhds (collisionCrossQuotient a b 0)) at hcont
  simpa [collisionCrossQuotient] using hcont

private theorem tendsto_collisionFirstCrossQuotient_zero (a b : ℝ) :
    Tendsto (collisionFirstCrossQuotient a b) (nhds 0) (nhds 0) := by
  have hcont : ContinuousAt (collisionFirstCrossQuotient a b) 0 := by
    unfold collisionFirstCrossQuotient
    fun_prop
  change Tendsto (collisionFirstCrossQuotient a b) (nhds 0)
    (nhds (collisionFirstCrossQuotient a b 0)) at hcont
  simpa [collisionFirstCrossQuotient] using hcont

private theorem tendsto_collisionSecondCrossQuotient_zero (a b : ℝ) :
    Tendsto (collisionSecondCrossQuotient a b) (nhds 0) (nhds 0) := by
  have hcont : ContinuousAt (collisionSecondCrossQuotient a b) 0 := by
    unfold collisionSecondCrossQuotient
    fun_prop
  change Tendsto (collisionSecondCrossQuotient a b) (nhds 0)
    (nhds (collisionSecondCrossQuotient a b 0)) at hcont
  simpa [collisionSecondCrossQuotient] using hcont

private theorem collisionCross_isLittleO (a b : ℝ) :
    (fun e => taylorFive (coherentCollisionExponent a b e) - taylorFive (e ^ 2 * a) - e ^ 10 * b)
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hzero : ∀ e : ℝ, e ^ 10 = 0 →
      taylorFive (coherentCollisionExponent a b e) - taylorFive (e ^ 2 * a) - e ^ 10 * b = 0 := by
    intro e he
    have he0 : e = 0 := eq_zero_of_pow_eq_zero he
    subst e
    simp [taylorFive, coherentCollisionExponent]
  exact (isLittleO_iff_tendsto hzero).2 <| by
    simpa only [collisionCrossQuotient_eq] using
      tendsto_collisionCrossQuotient_zero a b

private theorem collisionFirstCross_isLittleO (a b : ℝ) :
    (fun e => coherentCollisionExponent a b e * taylorFour (coherentCollisionExponent a b e) -
        e ^ 2 * a * taylorFour (e ^ 2 * a) - e ^ 10 * b)
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hzero : ∀ e : ℝ, e ^ 10 = 0 →
      coherentCollisionExponent a b e * taylorFour (coherentCollisionExponent a b e) -
        e ^ 2 * a * taylorFour (e ^ 2 * a) - e ^ 10 * b = 0 := by
    intro e he
    have he0 : e = 0 := eq_zero_of_pow_eq_zero he
    subst e
    simp [taylorFour, coherentCollisionExponent]
  exact (isLittleO_iff_tendsto hzero).2 <| by
    simpa only [collisionFirstCrossQuotient_eq] using
      tendsto_collisionFirstCrossQuotient_zero a b

private theorem collisionSecondCross_isLittleO (a b : ℝ) :
    (fun e => coherentCollisionExponent a b e ^ 2 * taylorThree (coherentCollisionExponent a b e) -
        (e ^ 2 * a) ^ 2 * taylorThree (e ^ 2 * a))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hzero : ∀ e : ℝ, e ^ 10 = 0 →
      coherentCollisionExponent a b e ^ 2 * taylorThree (coherentCollisionExponent a b e) -
        (e ^ 2 * a) ^ 2 * taylorThree (e ^ 2 * a) = 0 := by
    intro e he
    have he0 : e = 0 := eq_zero_of_pow_eq_zero he
    subst e
    simp [taylorThree, coherentCollisionExponent]
  exact (isLittleO_iff_tendsto hzero).2 <| by
    simpa only [collisionSecondCrossQuotient_eq] using
      tendsto_collisionSecondCrossQuotient_zero a b

private theorem exp_sub_taylorFive_isLittleO :
    (fun x : ℝ => Real.exp x - taylorFive x) =o[nhds 0] (fun x => x ^ 5) := by
  convert Real.exp_sub_sum_range_succ_isLittleO_pow 5 using 1
  funext x
  unfold taylorFive
  simp [Finset.sum_range_succ, Nat.factorial]

private theorem exp_sub_taylorFour_isLittleO :
    (fun x : ℝ => Real.exp x - taylorFour x) =o[nhds 0] (fun x => x ^ 4) := by
  convert Real.exp_sub_sum_range_succ_isLittleO_pow 4 using 1
  funext x
  unfold taylorFour
  simp [Finset.sum_range_succ, Nat.factorial]

private theorem exp_sub_taylorThree_isLittleO :
    (fun x : ℝ => Real.exp x - taylorThree x) =o[nhds 0] (fun x => x ^ 3) := by
  convert Real.exp_sub_sum_range_succ_isLittleO_pow 3 using 1
  funext x
  unfold taylorThree
  simp [Finset.sum_range_succ, Nat.factorial]

private theorem coherentCollisionExponent_isBigO_sq (a b : ℝ) :
    coherentCollisionExponent a b =O[nhds 0] (fun e : ℝ => e ^ 2) := by
  have hfactor : Tendsto (fun e : ℝ => a + e ^ 8 * b) (nhds 0) (nhds a) := by
    have hcont : Continuous (fun e : ℝ => a + e ^ 8 * b) := by fun_prop
    have hca : ContinuousAt (fun e : ℝ => a + e ^ 8 * b) 0 := hcont.continuousAt
    change Tendsto (fun e : ℝ => a + e ^ 8 * b) (nhds 0)
      (nhds (a + (0 : ℝ) ^ 8 * b)) at hca
    simpa using hca
  have h := (isBigO_refl (fun e : ℝ => e ^ 2) (nhds 0)).mul
    (hfactor.isBigO_one ℝ)
  convert! h using 1
  · funext e
    unfold coherentCollisionExponent
    ring
  · funext e
    ring

private theorem exp_collision_value_isLittleO (a b : ℝ) :
    (fun e => Real.exp (coherentCollisionExponent a b e) - taylorFive (e ^ 2 * a) - e ^ 10 * b)
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hy : Tendsto (coherentCollisionExponent a b) (nhds 0) (nhds 0) := by
    have hcont : Continuous (coherentCollisionExponent a b) := by
      unfold coherentCollisionExponent
      fun_prop
    have hca : ContinuousAt (coherentCollisionExponent a b) 0 := hcont.continuousAt
    change Tendsto (coherentCollisionExponent a b) (nhds 0) (nhds (coherentCollisionExponent a b 0)) at hca
    simpa [coherentCollisionExponent] using hca
  have hrem := exp_sub_taylorFive_isLittleO.comp_tendsto hy
  have hy5 := (coherentCollisionExponent_isBigO_sq a b).pow 5
  have hpows (e : ℝ) : (e ^ 2) ^ 5 = e ^ 10 := by
    ring
  have hrem' :
      (fun e => Real.exp (coherentCollisionExponent a b e) - taylorFive (coherentCollisionExponent a b e))
        =o[nhds 0] (fun e : ℝ => e ^ 10) := by
    exact (hrem.trans_isBigO hy5).congr'
      (Eventually.of_forall fun e => rfl)
      (Eventually.of_forall hpows)
  exact (hrem'.add (collisionCross_isLittleO a b)).congr_left fun e => by
    ring

private theorem exp_collision_first_isLittleO (a b : ℝ) :
    (fun e => coherentCollisionExponent a b e * Real.exp (coherentCollisionExponent a b e) -
        e ^ 2 * a * taylorFour (e ^ 2 * a) - e ^ 10 * b)
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hy : Tendsto (coherentCollisionExponent a b) (nhds 0) (nhds 0) := by
    have hcont : Continuous (coherentCollisionExponent a b) := by
      unfold coherentCollisionExponent
      fun_prop
    have hca : ContinuousAt (coherentCollisionExponent a b) 0 := hcont.continuousAt
    change Tendsto (coherentCollisionExponent a b) (nhds 0) (nhds (coherentCollisionExponent a b 0)) at hca
    simpa [coherentCollisionExponent] using hca
  have hrem := exp_sub_taylorFour_isLittleO.comp_tendsto hy
  have hyO := coherentCollisionExponent_isBigO_sq a b
  have hmul :
      (fun e => coherentCollisionExponent a b e *
        (Real.exp (coherentCollisionExponent a b e) - taylorFour (coherentCollisionExponent a b e)))
        =o[nhds 0] (fun e => coherentCollisionExponent a b e ^ 5) := by
    refine ((isBigO_refl (coherentCollisionExponent a b) (nhds 0)).mul_isLittleO hrem).congr
      (fun _ => rfl) ?_
    intro e
    simp only [Function.comp_apply]
    ring
  have hpows (e : ℝ) : (e ^ 2) ^ 5 = e ^ 10 := by ring
  have hrem' :
      (fun e => coherentCollisionExponent a b e *
        (Real.exp (coherentCollisionExponent a b e) - taylorFour (coherentCollisionExponent a b e)))
        =o[nhds 0] (fun e : ℝ => e ^ 10) := by
    exact (hmul.trans_isBigO (hyO.pow 5)).congr'
      (Eventually.of_forall fun e => rfl)
      (Eventually.of_forall hpows)
  exact (hrem'.add (collisionFirstCross_isLittleO a b)).congr_left fun e => by
    ring

private theorem exp_collision_second_isLittleO (a b : ℝ) :
    (fun e => coherentCollisionExponent a b e ^ 2 * Real.exp (coherentCollisionExponent a b e) -
        (e ^ 2 * a) ^ 2 * taylorThree (e ^ 2 * a))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hy : Tendsto (coherentCollisionExponent a b) (nhds 0) (nhds 0) := by
    have hcont : Continuous (coherentCollisionExponent a b) := by
      unfold coherentCollisionExponent
      fun_prop
    have hca : ContinuousAt (coherentCollisionExponent a b) 0 := hcont.continuousAt
    change Tendsto (coherentCollisionExponent a b) (nhds 0) (nhds (coherentCollisionExponent a b 0)) at hca
    simpa [coherentCollisionExponent] using hca
  have hrem := exp_sub_taylorThree_isLittleO.comp_tendsto hy
  have hyO := coherentCollisionExponent_isBigO_sq a b
  have hmul :
      (fun e => coherentCollisionExponent a b e ^ 2 *
        (Real.exp (coherentCollisionExponent a b e) - taylorThree (coherentCollisionExponent a b e)))
        =o[nhds 0] (fun e => coherentCollisionExponent a b e ^ 5) := by
    refine
      ((isBigO_refl (fun e => coherentCollisionExponent a b e ^ 2) (nhds 0)).mul_isLittleO hrem).congr
        (fun _ => rfl) ?_
    intro e
    simp only [Function.comp_apply]
    ring
  have hpows (e : ℝ) : (e ^ 2) ^ 5 = e ^ 10 := by ring
  have hrem' :
      (fun e => coherentCollisionExponent a b e ^ 2 *
        (Real.exp (coherentCollisionExponent a b e) - taylorThree (coherentCollisionExponent a b e)))
        =o[nhds 0] (fun e : ℝ => e ^ 10) := by
    exact (hmul.trans_isBigO (hyO.pow 5)).congr'
      (Eventually.of_forall fun e => rfl)
      (Eventually.of_forall hpows)
  exact (hrem'.add (collisionSecondCross_isLittleO a b)).congr_left fun e => by
    ring

/-- The coherent Gram entry has its exact degree-five value jet through order ten. -/
theorem coherentCollision_valueJet (a b : ℝ) :
    (fun e => Real.exp (coherentCollisionExponent a b e) -
        ∑ j ∈ Finset.range 6, e ^ (2 * j) * a ^ j / (j.factorial : ℝ) -
        e ^ 10 * b) =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  convert exp_collision_value_isLittleO a b using 1
  funext e
  unfold taylorFive
  simp [Finset.sum_range_succ, Nat.factorial]
  ring

/-- The first scale derivative of a coherent Gram entry has its exact order-ten jet. -/
theorem coherentCollision_firstJet (a b : ℝ) :
    (fun e => coherentCollisionExponent a b e * Real.exp (coherentCollisionExponent a b e) -
        ∑ j ∈ Finset.range 5,
          e ^ (2 * (j + 1)) * a ^ (j + 1) / (j.factorial : ℝ) -
        e ^ 10 * b) =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  convert exp_collision_first_isLittleO a b using 1
  funext e
  unfold taylorFour
  simp [Finset.sum_range_succ, Nat.factorial]
  ring

/-- The second scale derivative of a coherent Gram entry has its exact order-ten jet. -/
theorem coherentCollision_secondJet (a b : ℝ) :
    (fun e => coherentCollisionExponent a b e ^ 2 * Real.exp (coherentCollisionExponent a b e) -
        ∑ j ∈ Finset.range 4,
          e ^ (2 * (j + 2)) * a ^ (j + 2) / (j.factorial : ℝ))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  convert exp_collision_second_isLittleO a b using 1
  funext e
  unfold taylorThree
  simp [Finset.sum_range_succ, Nat.factorial]
  ring

/-! ### Finite recombination -/

/-- Any finite linear recombination of the value-jet remainders is still little-oh of order
ten.  Taking the index type to be a product assembles a recombined Gram entry. -/
theorem coherentCollision_valueJet_finset {ι : Type*} (s : Finset ι)
    (c a b : ι → ℝ) :
    (fun e => ∑ i ∈ s, c i *
      (Real.exp (coherentCollisionExponent (a i) (b i) e) -
        ∑ j ∈ Finset.range 6,
          e ^ (2 * j) * (a i) ^ j / (j.factorial : ℝ) -
        e ^ 10 * b i)) =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  apply IsLittleO.sum
  intro i hi
  exact (coherentCollision_valueJet (a i) (b i)).const_mul_left (c i)

/-- Any finite linear recombination of the first-derivative jet remainders remains little-oh of
order ten. -/
theorem coherentCollision_firstJet_finset {ι : Type*} (s : Finset ι)
    (c a b : ι → ℝ) :
    (fun e => ∑ i ∈ s, c i *
      (coherentCollisionExponent (a i) (b i) e *
          Real.exp (coherentCollisionExponent (a i) (b i) e) -
        ∑ j ∈ Finset.range 5,
          e ^ (2 * (j + 1)) * (a i) ^ (j + 1) / (j.factorial : ℝ) -
        e ^ 10 * b i)) =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  apply IsLittleO.sum
  intro i hi
  exact (coherentCollision_firstJet (a i) (b i)).const_mul_left (c i)

/-- Any finite linear recombination of the second-derivative jet remainders remains little-oh
of order ten. -/
theorem coherentCollision_secondJet_finset {ι : Type*} (s : Finset ι)
    (c a b : ι → ℝ) :
    (fun e => ∑ i ∈ s, c i *
      (coherentCollisionExponent (a i) (b i) e ^ 2 *
          Real.exp (coherentCollisionExponent (a i) (b i) e) -
        ∑ j ∈ Finset.range 4,
          e ^ (2 * (j + 2)) * (a i) ^ (j + 2) / (j.factorial : ℝ)))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  apply IsLittleO.sum
  intro i hi
  exact (coherentCollision_secondJet (a i) (b i)).const_mul_left (c i)

end

end GaloisForLFunctions.HilbertMetric
