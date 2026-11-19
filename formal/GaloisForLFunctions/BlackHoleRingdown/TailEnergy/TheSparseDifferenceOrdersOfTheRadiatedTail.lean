import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.NewtonExtrapolationOfTheModularEnergy

/-!
# Sparse difference orders recover the decay exponent

At order floor(exp(k)/2), the positive Hausdorff difference retains at
least half of every release after time k. Before k its kernel decays
faster than every exponential in the distance from k. Consequently the
sparse readings and the continuous energy tail have the same exponential
envelopes, including an attained endpoint.
-/

open Finset Filter
namespace GaloisForLFunctions.BlackHoleRingdown

noncomputable section

/-- Difference order corresponding to physical time k. -/
def radiationDifferenceOrder (k : ℕ) := ⌊Real.exp (k : ℝ)/2⌋₊

/-- One signed difference at the origin of the integer Laplace grid. -/
def sparseRadiationDifference (h : CompactPulse) (k : ℕ) : ℝ :=
  (-1 : ℝ)^(radiationDifferenceOrder k) *
    (fwdDiff 1)^[radiationDifferenceOrder k] (radiationSample h) 0

private def weight (k i : ℕ) := (1-radiationNode i)^(radiationDifferenceOrder k)

private theorem weight_nonneg (k i : ℕ) : 0 ≤ weight k i :=
  pow_nonneg (sub_nonneg.mpr (radiationNode_le_one i)) _

private theorem weight_le_one (k i : ℕ) : weight k i ≤ 1 :=
  pow_le_one₀ (sub_nonneg.mpr (radiationNode_le_one i)) (sub_le_self _ (radiationNode_pos i).le)

private theorem weight_late {k i : ℕ} (hi : k ≤ i) : 1/2 ≤ weight k i := by
  have hn : (radiationDifferenceOrder k : ℝ) ≤ Real.exp (k:ℝ)/2 := Nat.floor_le (by positivity)
  have he : Real.exp (k:ℝ)*radiationNode i ≤ 1 := by
    rw [radiationNode, ← Real.exp_add, Real.exp_le_one_iff]
    exact sub_nonpos.mpr (Nat.cast_le.mpr hi)
  have h := one_add_mul_le_pow (show -2 ≤ -radiationNode i by linarith only [radiationNode_le_one i])
    (radiationDifferenceOrder k)
  change 1/2 ≤ (1-radiationNode i)^_
  rw [sub_eq_add_neg]
  linarith only [h,mul_le_mul_of_nonneg_right hn (radiationNode_pos i).le,he]

/-- All exponential rates are available to the left of the cutoff. -/
private theorem weight_early (r k i : ℕ) :
    weight k i ≤ (Real.exp 1*2^r*r.factorial)*Real.exp (-(r:ℝ)*((k:ℝ)-i)) := by
  let n := radiationDifferenceOrder k
  let x := radiationNode i
  let y := ((n:ℝ)+1)*x
  have hx : 0 < x := radiationNode_pos i
  have hx₁ : x ≤ 1 := radiationNode_le_one i
  have hy : 0 ≤ y := mul_nonneg (by positivity) hx.le
  have hbase : 1-x ≤ Real.exp (-x) := by linarith only [Real.add_one_le_exp (-x)]
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hx₁) hbase n
  rw [← Real.exp_nat_mul] at hp
  have hn : Real.exp (k:ℝ)/2 < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hh : Real.exp ((k:ℝ)-i) ≤ 2*y := by
    rw [sub_eq_add_neg,Real.exp_add]
    dsimp only [y,x,radiationNode]
    linarith only [mul_le_mul_of_nonneg_right hn.le (Real.exp_pos (-(i:ℝ))).le]
  have hpoly := (div_le_iff₀ (by positivity : 0 < (r.factorial:ℝ))).mp
    (Real.pow_div_factorial_le_exp hy r)
  have hc : Real.exp ((k:ℝ)-i)^r ≤ 2^r*(Real.exp y*r.factorial) :=
    (pow_le_pow_left₀ (Real.exp_pos _).le hh r).trans
      ((mul_pow (2:ℝ) y r).le.trans (mul_le_mul_of_nonneg_left hpoly (by positivity)))
  have h := mul_le_mul hp hc (pow_nonneg (Real.exp_pos _).le r) (Real.exp_pos _).le
  have he : Real.exp ((n:ℝ)* -x)*Real.exp y = Real.exp x := by
    rw [←Real.exp_add]
    congr 1
    dsimp only [y]
    ring
  have h' : weight k i*Real.exp ((r:ℝ)*((k:ℝ)-i)) ≤ Real.exp 1*2^r*r.factorial := by
    rw [Real.exp_nat_mul]
    calc _ ≤ Real.exp ((n:ℝ)* -x)*(2^r*(Real.exp y*r.factorial)) := h
         _ = (Real.exp ((n:ℝ)* -x)*Real.exp y)*2^r*r.factorial := by ring
         _ ≤ _ := by rw [he]; gcongr; exact Real.exp_le_exp.mpr hx₁
  rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
  exact h'

private def term (h : CompactPulse) (k i : ℕ) := weight k i * stepDecrement h i 1

private theorem term_nonneg (h : CompactPulse) (k i : ℕ) : 0 ≤ term h k i :=
  mul_nonneg (weight_nonneg _ _) (stepDecrement_nonneg _ _ _)

private theorem term_sum (h : CompactPulse) (k : ℕ) :
    HasSum (term h k) (sparseRadiationDifference h k) := by
  have hs := summable_radiation_kernel h 0 (radiationDifferenceOrder k)
  simpa only [sparseRadiationDifference,radiationSample_signed_difference,pow_zero,one_mul,term,weight]
    using hs.hasSum

/-- The sparse reading never loses more than half of the remaining energy. -/
theorem tail_le_twice_sparseDifference (h : CompactPulse) (k : ℕ) :
    tailEnergy h k ≤ 2*sparseRadiationDifference h k := by
  have hs := term_sum h k
  have ht := (summable_nat_add_iff k).mpr hs.summable
  have H := hasSum_le (fun i : ℕ =>
    show (1/2 : ℝ)*stepDecrement h (i+k:ℕ) 1 ≤ term h k (i+k) from
      mul_le_mul_of_nonneg_right (weight_late (Nat.le_add_left k i)) (stepDecrement_nonneg _ _ _))
    ((shifted_releases_have_sum h k).mul_left (1/2:ℝ)) ht.hasSum
  have hh := hs.summable.sum_add_tsum_nat_add k
  rw [hs.tsum_eq] at hh
  linarith only [H,hh,sum_nonneg (s := range k) (fun i _ => term_nonneg h k i)]

private theorem early_sum_bound (h : CompactPulse) (k r : ℕ) {b C : ℝ} (hr : b < r) (hC : 0 ≤ C)
    (hrelease : ∀ i : ℕ, stepDecrement h i 1 ≤ C*Real.exp (-b*i)) :
    ∑ i ∈ range k, term h k i ≤
      (Real.exp 1*2^r*r.factorial*C/(Real.exp (r-b)-1))*Real.exp (-b*k) := by
  let A : ℝ := Real.exp 1*2^r*r.factorial*C
  let q := Real.exp (r-b)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hq : 1 < q := Real.one_lt_exp_iff.mpr (sub_pos.mpr hr)
  have hterm (i : ℕ) : term h k i ≤ (A*Real.exp (-(r:ℝ)*k))*q^i := by
    have h := mul_le_mul (weight_early r k i) (hrelease i) (stepDecrement_nonneg _ _ _)
      (by positivity)
    calc _ ≤ _ := h
         _ = _ := by
           dsimp only [A,q]
           rw [← Real.exp_nat_mul]
           calc _ = (Real.exp 1*2^r*r.factorial*C)*
                (Real.exp (-(r:ℝ)*((k:ℝ)-i))*Real.exp (-b*i)) := by ring
                _ = _ := by rw [← Real.exp_add,mul_assoc _ (Real.exp _),←Real.exp_add]; congr 2; ring
  have hs := sum_le_sum (s := range k) (fun i _ => hterm i)
  rw [←mul_sum] at hs
  have hg : (∑ i ∈ range k, q^i) ≤ q^k/(q-1) := by
    rw [le_div_iff₀ (sub_pos.mpr hq),geom_sum_mul]
    linarith
  refine (hs.trans (mul_le_mul_of_nonneg_left hg (mul_nonneg hA (Real.exp_pos _).le))).trans_eq ?_
  dsimp only [q]
  rw [←Real.exp_nat_mul]
  calc _ = A/(Real.exp ((r:ℝ)-b)-1) *
             (Real.exp (-(r:ℝ)*k)*Real.exp ((k:ℝ)*(r-b))) := by ring
       _ = _ := by rw [←Real.exp_add,show -(r:ℝ)*k+(k:ℝ)*(r-b) = -b*k by ring]

/-- Exact equality of the positive exponential decay envelopes, including endpoints,
for a compact pulse and its exponentially spaced Newton-difference orders. -/
theorem sparse_difference_decay_iff_tail_decay (h : CompactPulse) {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ k : ℕ, sparseRadiationDifference h k ≤ C*Real.exp (-b*k)) ↔
      ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → tailEnergy h T ≤ C*Real.exp (-b*T) := by
  constructor
  · rintro ⟨C,hC⟩
    apply (tail_decay_iff_unit_decrement_decay h hb).mpr
    refine ⟨2*C,fun k => ?_⟩
    rw [←tailEnergy_sub_step h _ zero_le_one]
    exact ((sub_le_self _ (tailEnergy_nonneg _ _)).trans (tail_le_twice_sparseDifference h k)).trans
      ((mul_le_mul_of_nonneg_left (hC k) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (mul_assoc ..).symm)
  · rintro ⟨C,hC⟩
    obtain ⟨r,hr⟩ := exists_nat_gt b
    have hC₀ : 0 ≤ C := by simpa using (tailEnergy_nonneg h 0).trans (hC 0 le_rfl)
    let D := Real.exp 1*2^r*r.factorial*C/(Real.exp (r-b)-1)
    refine ⟨D+C,fun k => ?_⟩
    have hrel (i : ℕ) : stepDecrement h i 1 ≤ C*Real.exp (-b*i) := by
      rw [←tailEnergy_sub_step h _ zero_le_one]
      exact (sub_le_self _ (tailEnergy_nonneg _ _)).trans (hC _ (Nat.cast_nonneg _))
    have hs := term_sum h k
    have ht := (summable_nat_add_iff k).mpr hs.summable
    have H := hasSum_le (fun i : ℕ => show term h k (i+k) ≤ stepDecrement h (i+k:ℕ) 1 from
      mul_le_of_le_one_left (stepDecrement_nonneg _ _ _) (weight_le_one _ _))
      ht.hasSum (shifted_releases_have_sum h k)
    rw [← hs.tsum_eq,←hs.summable.sum_add_tsum_nat_add k,add_mul]
    exact add_le_add (early_sum_bound h k r hr hC₀ hrel) (H.trans (hC _ (Nat.cast_nonneg _)))

/-- RH is equivalent to testing the one sparse sequence of difference orders at
each positive decay rate below one half. -/
theorem riemannHypothesis_iff_sparseRadiationDifferences :
    RiemannHypothesis ↔ ∀ h : CompactPulse, ∀ b : ℝ, 0 < b → b < 1/2 →
      ∃ C : ℝ, ∀ k : ℕ, sparseRadiationDifference h k ≤ C*Real.exp (-b*k) := by
  rw [riemannHypothesis_iff_tailEnergy_decay.1]
  constructor
  · intro H h b hb hhalf
    apply (sparse_difference_decay_iff_tail_decay h hb).mpr
    obtain ⟨C,hC⟩ := H _ (by linarith only [hhalf] : 0 < (1/2-b)/2) h
    refine ⟨C,fun T hT => ?_⟩
    convert hC T hT using 3 <;> ring
  · intro H ε hε h
    let b := 1/2-2*ε
    by_cases hb : 0 < b
    · exact (sparse_difference_decay_iff_tail_decay h hb).mp
        (H h b hb (by dsimp only [b]; linarith only [hε]))
    · refine ⟨tailEnergy h 0,fun T hT => ?_⟩
      exact (tailEnergy_anti h hT).trans (le_mul_of_one_le_right (tailEnergy_nonneg _ _)
        (Real.one_le_exp (mul_nonneg (neg_nonneg.mpr (le_of_not_gt hb)) hT)))

#print axioms tail_le_twice_sparseDifference
#print axioms sparse_difference_decay_iff_tail_decay
#print axioms riemannHypothesis_iff_sparseRadiationDifferences

end

end GaloisForLFunctions.BlackHoleRingdown
