import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CumulativeEndpointQuadrature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Critical powers in cumulative mass coordinates

The power-integral alternative of Fino and Majdoub (arXiv:2611.24340,
Lemma 2.1) has a discrete version with uneven mass increments. Bounded
steps preserve the critical exponent when the mass coordinate is replaced
by its logarithm. This also identifies the critical logarithmic correction.
-/

noncomputable section
open Finset Filter Set
open scoped Topology

namespace GaloisForLFunctions.CumulativeQuadrature

/-- One increment discounted by the current cumulative mass to power p. -/
def powerCharge (x : ℕ → ℝ) (p : ℝ) (i : ℕ) : ℝ :=
  (x (i+1)-x i)*(1+x (i+1))^(-p)

private theorem charge_nn {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0) (p : ℝ) (i : ℕ) :
    0 ≤ powerCharge x p i := mul_nonneg (sub_nonneg.mpr (hx (Nat.le_succ i)))
      (Real.rpow_nonneg (add_nonneg zero_le_one (h₀.trans (hx (Nat.zero_le _)))) _)

/-- A supercritical tail is bounded by its remaining continuum integral;
the finite cells may have arbitrary lengths. -/
theorem power_prefix_bound {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0) (K n : ℕ)
    {p : ℝ} (hp : 1 < p) :
    ∑ i ∈ Finset.range n, powerCharge x p (K+i) ≤ (1+x K)^(1-p)/(p-1) := by
  let y := fun i => 1+x (K+i)
  have hy : Monotone y := fun i j hij => add_le_add (le_refl 1) (hx (Nat.add_le_add_left hij K))
  have hpos (i : ℕ) : 0 < y i := add_pos_of_pos_of_nonneg zero_lt_one (h₀.trans (hx (Nat.zero_le _)))
  have ha : AntitoneOn (fun v : ℝ => v^(-p)) (Set.Icc (y 0) (y n)) := fun _ hv _ _ hvw =>
    Real.rpow_le_rpow_of_nonpos ((hpos 0).trans_le hv.1) hvw (by linarith only [hp])
  have hmesh (i : ℕ) (hi : i < n) : y (i+1)-y i ≤ y n :=
    (sub_le_self _ (hpos i).le).trans (hy hi)
  have h := (defect_bounds n hy ha hmesh).1
  have hf : rightSum y (fun v : ℝ => v^(-p)) n = ∑ i ∈ Finset.range n, powerCharge x p (K+i) := by
    apply sum_congr rfl
    intro i _
    simp only [y,powerCharge,Nat.add_assoc,add_sub_add_left_eq_sub]
  have hzero : (0:ℝ) ∉ uIcc (y 0) (y n) := by
    rw [uIcc_of_le (hy (Nat.zero_le n))]
    exact fun h => (hpos 0).not_ge h.1
  rw [defect,hf,integral_rpow (Or.inr ⟨by linarith only [hp],hzero⟩)] at h
  have hden := sub_pos.mpr hp
  have he : ((y n)^(-p+1)-(y 0)^(-p+1))/(-p+1) = ((y 0)^(1-p)-(y n)^(1-p))/(p-1) := by
    rw [show -p+1 = 1-p by ring]
    field_simp [hden.ne',(sub_neg.mpr hp).ne]
    ring
  rw [he] at h
  simpa only [y,Nat.add_zero] using (sub_nonneg.mp h).trans (div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (hpos n).le _)) hden.le)

/-- The reciprocal right charge and the actual log increment are comparable
on each cell. Their ratio is bounded by one plus the cell length. -/
theorem logarithmic_cell {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)/(1+b) ≤ Real.log (1+b)-Real.log (1+a) ∧
    Real.log (1+b)-Real.log (1+a) ≤ (1+(b-a))*((b-a)/(1+b)) := by
  have hA := add_pos_of_pos_of_nonneg zero_lt_one ha
  have hB := add_pos_of_pos_of_nonneg zero_lt_one (ha.trans hab)
  have hl := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have hu := Real.log_le_sub_one_of_pos (div_pos hB hA)
  rw [Real.log_div hA.ne' hB.ne'] at hl
  rw [Real.log_div hB.ne' hA.ne'] at hu
  constructor
  · have e : (1+a)/(1+b)-1 = -((b-a)/(1+b)) := by field_simp; ring
    rw [e] at hl
    linarith only [hl]
  · apply hu.trans
    have e : (1+b)/(1+a)-1 = (b-a)/(1+a) := by field_simp; ring
    rw [e]
    have hratio : (1+b)/(1+a) ≤ 1+(b-a) :=
      (div_le_iff₀ hA).mpr (by nlinarith only [mul_nonneg ha (sub_nonneg.mpr hab)])
    have h := mul_le_mul_of_nonneg_right hratio (div_nonneg (sub_nonneg.mpr hab) hB.le)
    exact (show (b-a)/(1+a) = ((1+b)/(1+a))*((b-a)/(1+b)) by field_simp).trans_le h

/-- Power-discounted charges converge precisely above one, or at every
power if the cumulative mass is bounded. -/
theorem summable_power_charge_iff {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0)
    {M : ℝ} (hm : ∀ i, x (i+1)-x i ≤ M) (p : ℝ) :
    Summable (powerCharge x p) ↔ 1 < p ∨ BddAbove (Set.range x) := by
  have hnn (k : ℕ) := h₀.trans (hx (Nat.zero_le k))
  have hd (k : ℕ) := sub_nonneg.mpr (hx (Nat.le_succ k))
  have hM := (hd 0).trans (hm 0)
  constructor
  · intro hs
    by_cases hp : 1 < p
    · exact Or.inl hp
    right
    let B := ∑' i, powerCharge x p i
    have hlocal (i : ℕ) : Real.log (1+x (i+1))-Real.log (1+x i) ≤ (1+M)*powerCharge x p i := by
      have he := (logarithmic_cell (hnn i) (hx (Nat.le_succ i))).2
      apply he.trans
      apply mul_le_mul (add_le_add (le_refl 1) (hm i)) _
        (div_nonneg (hd i) (add_nonneg zero_le_one (hnn _))) (add_nonneg zero_le_one hM)
      rw [div_eq_mul_inv, powerCharge,←Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        (le_add_of_nonneg_right (hnn _)) (by linarith only [le_of_not_gt hp])) (hd i)
    refine ⟨Real.exp (Real.log (1+x 0)+(1+M)*B),?_⟩
    rintro _ ⟨k,rfl⟩
    have hh := sum_le_sum (s := Finset.range k) fun i _ => hlocal i
    rw [sum_range_sub (fun j => Real.log (1+x j)) k, ←mul_sum] at hh
    have hsum := hs.sum_le_tsum (Finset.range k) (fun i _ => charge_nn hx h₀ p i)
    have hlog := hh.trans (mul_le_mul_of_nonneg_left hsum (add_nonneg zero_le_one hM))
    have he := Real.exp_le_exp.mpr (sub_le_iff_le_add'.mp hlog)
    rw [Real.exp_log (add_pos_of_pos_of_nonneg zero_lt_one (hnn k))] at he
    linarith only [he]
  · rintro (hp|⟨B,hB⟩)
    · apply summable_of_sum_range_le (charge_nn hx h₀ p)
      exact fun n => by simpa only [Nat.zero_add] using power_prefix_bound hx h₀ 0 n hp
    let A := (1+B)^|p|
    have hmax (k : ℕ) := hB (mem_range_self k)
    have hA : 0 ≤ A := Real.rpow_nonneg (add_nonneg zero_le_one (h₀.trans (hmax 0))) _
    apply summable_of_sum_range_le (charge_nn hx h₀ p) (c := B*A)
    intro n
    have hw (i : ℕ) : (1+x (i+1))^(-p) ≤ A :=
      (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (hnn _)) (neg_le_abs p)).trans
        (Real.rpow_le_rpow (add_nonneg zero_le_one (hnn _))
          (add_le_add (le_refl 1) (hmax _)) (abs_nonneg p))
    have h := sum_le_sum (s := Finset.range n) fun i _ => mul_le_mul_of_nonneg_left (hw i) (hd i)
    rw [←sum_mul,sum_range_sub] at h
    exact h.trans (mul_le_mul_of_nonneg_right ((sub_le_self _ h₀).trans (hmax n)) hA)

/-- At the critical reciprocal power, impose a further power of the logarithm. -/
def logPowerCharge (x : ℕ → ℝ) (p : ℝ) (i : ℕ) : ℝ :=
  powerCharge x 1 i * (1+Real.log (1+x (i+1)))^(-p)

/-- At the critical power, the next logarithm has its own sharp threshold
at exponent one. The same finite-mass exception is the only one. -/
theorem summable_log_power_charge_iff {x : ℕ → ℝ} (hx : Monotone x) (h₀ : 0 ≤ x 0)
    {M : ℝ} (hm : ∀ i, x (i+1)-x i ≤ M) (p : ℝ) :
    Summable (logPowerCharge x p) ↔ 1 < p ∨ BddAbove (Set.range x) := by
  let y := fun i => Real.log (1+x i)
  have hn (i : ℕ) := h₀.trans (hx (Nat.zero_le i))
  have hy₀ (i : ℕ) : 0 ≤ y i := Real.log_nonneg (le_add_of_nonneg_right (hn i))
  have hy : Monotone y := fun i j hij => Real.log_le_log
    (add_pos_of_pos_of_nonneg zero_lt_one (hn i)) (add_le_add (le_refl 1) (hx hij))
  have hd (i : ℕ) := sub_nonneg.mpr (hx (Nat.le_succ i))
  have hM := (hd 0).trans (hm 0)
  have hcell (i : ℕ) : powerCharge x 1 i ≤ y (i+1)-y i ∧
      y (i+1)-y i ≤ (1+M)*powerCharge x 1 i := by
    simp only [powerCharge,Real.rpow_neg_one,←div_eq_mul_inv]
    obtain ⟨hl,hu⟩ := logarithmic_cell (hn i) (hx (Nat.le_succ i))
    exact ⟨hl,hu.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) (hm i))
      (div_nonneg (hd i) (add_nonneg zero_le_one (hn _))))⟩
  have hym (i : ℕ) : y (i+1)-y i ≤ (1+M)*M := by
    apply (hcell i).2.trans
    apply mul_le_mul_of_nonneg_left _ (add_nonneg zero_le_one hM)
    rw [powerCharge, Real.rpow_neg_one, ←div_eq_mul_inv]
    exact (div_le_self (hd i) (le_add_of_nonneg_right (hn _))).trans (hm i)
  have hbounded : BddAbove (Set.range y) ↔ BddAbove (Set.range x) := by
    constructor
    · rintro ⟨B,hB⟩
      refine ⟨Real.exp B,?_⟩
      rintro _ ⟨i,rfl⟩
      have hh := Real.exp_le_exp.mpr (hB (mem_range_self i))
      change Real.exp (Real.log (1+x i)) ≤ Real.exp B at hh
      rw [Real.exp_log (add_pos_of_pos_of_nonneg zero_lt_one (hn i))] at hh
      linarith only [hh]
    · rintro ⟨B,hB⟩
      refine ⟨Real.log (1+B),?_⟩
      rintro _ ⟨i,rfl⟩
      exact Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one (hn i))
        (add_le_add (le_refl 1) (hB (mem_range_self i)))
  rw [←hbounded,←summable_power_charge_iff hy (hy₀ 0) hym]
  have hw (i : ℕ) := Real.rpow_nonneg (add_nonneg zero_le_one (hy₀ (i+1))) (-p)
  constructor
  · intro h
    apply (h.mul_left (1+M)).of_nonneg_of_le (charge_nn hy (hy₀ 0) p)
    intro i
    exact (mul_le_mul_of_nonneg_right (hcell i).2 (hw i)).trans_eq (mul_assoc ..)
  · intro h
    exact h.of_nonneg_of_le (fun i => mul_nonneg (charge_nn hx h₀ 1 i) (hw i))
      (fun i => mul_le_mul_of_nonneg_right (hcell i).1 (hw i))

#print axioms summable_log_power_charge_iff
#print axioms logarithmic_cell
#print axioms power_prefix_bound
#print axioms summable_power_charge_iff

end GaloisForLFunctions.CumulativeQuadrature
