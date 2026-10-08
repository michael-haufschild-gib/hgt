import GaloisForLFunctions.RHTower.WeilWorkDeficitRadicalBudget
import GaloisForLFunctions.RHTower.RiemannKernelCuspSeries

/-!
# A common factorial budget for all Riemann-kernel derivatives

One pair of constants controls every derivative order, and hence arbitrary finite
complex derivative packets and their full actual repair-weighted arithmetic tails.
This pays an order-dependent analytic cost; it does not construct positive packets
cancelling the prime moments. Paper proof: WP06 PROOF, C10u.
-/

open Real Polynomial MeasureTheory Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkDeficitDerivativeBudget

private def coeffWeight (δ : ℝ) (k j : ℕ) : ℝ :=
  |(riemannKernelPoly k).coeff j| * (j.factorial : ℝ) / δ^j

private theorem coeffWeight_nonneg {δ : ℝ} (hδ : 0 < δ) (k j : ℕ) :
    0 ≤ coeffWeight δ k j := by unfold coeffWeight; positivity

private theorem coeff_next (k j : ℕ) :
    (riemannKernelPoly (k+1)).coeff (j+1) =
      (2*((j:ℝ)+1)+1/2)*(riemannKernelPoly k).coeff (j+1) -
        2*π*(riemannKernelPoly k).coeff j := by
  rw [riemannKernelPoly, Function.iterate_succ_apply']
  change (cuspDeriv (riemannKernelPoly k)).coeff (j+1) = _
  simp only [cuspDeriv, coeff_sub, coeff_add, mul_assoc, coeff_C_mul,
    coeff_X_mul, coeff_derivative]
  ring

private theorem coeffWeight_zero (δ : ℝ) (k : ℕ) :
    coeffWeight δ (k+1) 0 = (1/2)*coeffWeight δ k 0 := by
  have h : (riemannKernelPoly (k+1)).coeff 0 =
      (1/2)*(riemannKernelPoly k).coeff 0 := by
    rw [riemannKernelPoly, Function.iterate_succ_apply']
    change (cuspDeriv (riemannKernelPoly k)).coeff 0 = _
    simp [cuspDeriv, mul_assoc]
  simp [coeffWeight, h, abs_mul]

private theorem coeffWeight_next {δ : ℝ} (hδ : 0 < δ) (k j : ℕ) :
    coeffWeight δ (k+1) (j+1) ≤
      (2*((j:ℝ)+1)+1/2)*coeffWeight δ k (j+1) +
        (2*π/δ)*((j:ℝ)+1)*coeffWeight δ k j := by
  have hpos : 0 ≤ 2*((j:ℝ)+1)+1/2 := by positivity
  have h := abs_sub ((2*((j:ℝ)+1)+1/2)*(riemannKernelPoly k).coeff (j+1))
    (2*π*(riemannKernelPoly k).coeff j)
  rw [abs_mul, abs_mul, abs_of_nonneg hpos, abs_of_pos (mul_pos (by norm_num) pi_pos)] at h
  unfold coeffWeight
  rw [coeff_next]
  refine (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)).trans_eq ?_
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

private theorem uniform_coefficients {δ : ℝ} (hδ : 0 < δ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ C=3+2*π/δ ∧ ∀ k j : ℕ,
      coeffWeight δ k j ≤ A*C^k*((k+2).factorial:ℝ) := by
  let A := 1+∑ j ∈ Finset.range 3, coeffWeight δ 0 j
  let C := 3+2*π/δ
  have hA : 0 < A := by
    dsimp [A]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range 3) => coeffWeight_nonneg hδ 0 j)
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hC3 : 3 ≤ C := by
    dsimp [C]
    have hp : 0 ≤ 2*π/δ := by positivity
    linarith
  refine ⟨A,C,hA,hC,rfl,?_⟩
  intro k
  induction k with
  | zero =>
    intro j
    by_cases hj : j < 3
    · have hs := Finset.single_le_sum
        (s:=Finset.range 3) (f:=fun i => coeffWeight δ 0 i)
        (fun i _ => coeffWeight_nonneg hδ 0 i) (Finset.mem_range.mpr hj)
      have hw : coeffWeight δ 0 j ≤ A := by dsimp [A]; linarith
      norm_num
      linarith
    · have hz : (riemannKernelPoly 0).coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt ((natDegree_riemannKernelPoly_le 0).trans_lt (by omega))
      simp only [coeffWeight, hz, abs_zero, zero_mul, zero_div]
      positivity
  | succ k ih =>
    have hfac : ((k+1+2).factorial:ℝ) = ((k:ℝ)+3)*((k+2).factorial:ℝ) := by
      rw [show k+1+2 = (k+2)+1 by omega, Nat.factorial_succ]
      push_cast
      ring
    intro j
    cases j with
    | zero =>
      rw [coeffWeight_zero]
      have hb := mul_le_mul_of_nonneg_left (ih 0) (by norm_num : (0:ℝ)≤1/2)
      refine hb.trans ?_
      have hk : (1/2:ℝ) ≤ C*((k:ℝ)+3) := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
      rw [hfac, pow_succ]
      calc (1/2)*(A*C^k*((k+2).factorial:ℝ)) ≤
          (C*((k:ℝ)+3))*(A*C^k*((k+2).factorial:ℝ)) := by gcongr
        _ = _ := by ring
    | succ j =>
      by_cases hj : j+1 ≤ k+3
      · have hjR : (j:ℝ)+1 ≤ (k:ℝ)+3 := by exact_mod_cast hj
        have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
        have hc : (2*((j:ℝ)+1)+1/2)+(2*π/δ)*((j:ℝ)+1) ≤ C*((k:ℝ)+3) := by
          have hp : 0 ≤ 2*π/δ := by positivity
          have hm := mul_le_mul_of_nonneg_left hjR hp
          dsimp [C]
          nlinarith
        have hb := coeffWeight_next hδ k j
        have h1 := mul_le_mul_of_nonneg_left (ih (j+1))
          (show 0 ≤ 2*((j:ℝ)+1)+1/2 by positivity)
        have h2 := mul_le_mul_of_nonneg_left (ih j)
          (show 0 ≤ (2*π/δ)*((j:ℝ)+1) by positivity)
        refine (hb.trans (add_le_add h1 h2)).trans ?_
        rw [hfac, pow_succ]
        calc _ = ((2*((j:ℝ)+1)+1/2)+(2*π/δ)*((j:ℝ)+1)) *
            (A*C^k*((k+2).factorial:ℝ)) := by ring
          _ ≤ (C*((k:ℝ)+3))*(A*C^k*((k+2).factorial:ℝ)) := by gcongr
          _ = _ := by ring
      · have hz : (riemannKernelPoly (k+1)).coeff (j+1) = 0 :=
          coeff_eq_zero_of_natDegree_lt ((natDegree_riemannKernelPoly_le (k+1)).trans_lt (by omega))
        simp only [coeffWeight, hz, abs_zero, zero_mul, zero_div]
        positivity

private theorem polynomial_envelope {δ A C : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hC : 0 < C)
    (hb : ∀ k j : ℕ, coeffWeight δ k j ≤ A*C^k*((k+2).factorial:ℝ))
    (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |(riemannKernelPoly k).eval t| ≤ A*C^k*((k+2).factorial:ℝ)*exp (δ*t) := by
  let B := A*C^k*((k+2).factorial:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (j : ℕ) : |(riemannKernelPoly k).coeff j| *t^j ≤ B*((δ*t)^j/(j.factorial:ℝ)) := by
    have hf : (0:ℝ) < (j.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos j
    have h := (div_le_iff₀ (pow_pos hδ j)).mp (hb k j)
    change |(riemannKernelPoly k).coeff j| *(j.factorial:ℝ) ≤ B*δ^j at h
    have hm := mul_le_mul_of_nonneg_right h (pow_nonneg ht j)
    rw [mul_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hf).mpr
    convert hm using 1 <;> ring
  rw [eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul, abs_pow, abs_of_nonneg ht]
  refine (Finset.sum_le_sum (fun j _ => hterm j)).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (mul_nonneg hδ.le ht) _) hB

private theorem cusp_geometric_bound (P : ℝ[X]) {δ b H : ℝ}
    (hb : 0 < b) (hH : 0 ≤ H) (hδb : δ+b=π)
    (hP : ∀ t : ℝ, 0 ≤ t → |P.eval t| ≤ H*exp (δ*t))
    {u : ℝ} (hu : 0 ≤ u) :
    |cuspSeries P u| ≤ H*exp (u/2)*exp (-(b*exp (2*u)))/(1-exp (-b)) := by
  let Y := exp (2*u)
  have hY : 1 ≤ Y := Real.one_le_exp (by positivity)
  have hq : exp (-b) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hq0 := (exp_pos (-b)).le
  have hterm (n : ℕ) : |cuspTerm P (n+1) u| ≤
      (H*exp (u/2)*exp (-(b*Y)))*exp (-b)^n := by
    let t := ((n+1:ℕ):ℝ)^2*Y
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have htY : Y+n ≤ t := by
      dsimp [t]
      push_cast
      have hh : 0 ≤ (n:ℝ)*((n:ℝ)+2)*(Y-1) := by positivity
      nlinarith [sq_nonneg (n:ℝ)]
    have he : exp (δ*t)*exp (-π*t) = exp (-(b*t)) := by
      rw [← exp_add]
      congr 1
      nlinarith [hδb]
    unfold cuspTerm
    change |exp (u/2)*P.eval t*exp (-π*t)| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
    calc _ ≤ exp (u/2)*(H*exp (δ*t))*exp (-π*t) := by gcongr; exact hP t ht
      _ = H*exp (u/2)*exp (-(b*t)) := by rw [mul_assoc, mul_assoc, he]; ring
      _ ≤ H*exp (u/2)*exp (-(b*(Y+n))) := by
        gcongr
      _ = _ := by
        rw [← exp_nat_mul, mul_assoc (H*exp (u/2)), ← exp_add]
        congr 2
        ring
  have hs := (summable_geometric_of_lt_one hq0 hq).mul_left (H*exp (u/2)*exp (-(b*Y)))
  have h := ((summable_cuspTerm P u).abs).tsum_le_tsum hterm hs
  have hn := norm_tsum_le_tsum_norm ((summable_cuspTerm P u).norm)
  simp only [Real.norm_eq_abs] at hn
  have hfull : |cuspSeries P u| ≤ ∑' n : ℕ, (H*exp (u/2)*exp (-(b*Y)))*exp (-b)^n :=
    hn.trans h
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq] at hfull
  exact hfull.trans_eq (by dsimp [Y]; ring)

/-- One pair of constants controls all actual derivative orders at any subcritical theta rate. -/
theorem kernel_derivative_factorial_envelope {a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ C=3+4*π/(π-a) ∧ ∀ (k : ℕ) (u : ℝ),
      ‖riemannKernelDeriv k u‖ ≤ B*C^k*((k+2).factorial:ℝ)*
        exp (-(a*exp (2*|u|)))*exp (-|u|) := by
  let δ := (π-a)/2
  let b := π-δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb : 0 < b := by dsimp [b,δ]; linarith
  have hδb : δ+b=π := by dsimp [b]; ring
  have hbδ : b=δ+a := by dsimp [b,δ]; ring
  obtain ⟨A,C,hA,hC,hCeq,hcoef⟩ := uniform_coefficients hδ
  have hden : 0 < 1-exp (-b) := by
    have := exp_lt_one_iff.mpr (show -b<0 by linarith)
    linarith
  have hCexplicit : C=3+4*π/(π-a) := by
    rw [hCeq]
    dsimp [δ]
    have hne : π-a ≠ 0 := by linarith
    field_simp [hne]
    ring
  refine ⟨A/δ/(1-exp (-b)),C,by positivity,hC,hCexplicit,?_⟩
  have hright (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
      ‖riemannKernelDeriv k u‖ ≤ (A/δ/(1-exp (-b)))*C^k*((k+2).factorial:ℝ)*
        exp (-(a*exp (2*u)))*exp (-u) := by
    have hpoly (t : ℝ) (ht : 0 ≤ t) := polynomial_envelope hδ hA hC hcoef k ht
    have h := cusp_geometric_bound (riemannKernelPoly k) hb (by positivity) hδb
      (fun t ht => hpoly t ht) hu
    have hy : 0 < exp (2*u) := exp_pos _
    have hp := Real.pow_div_factorial_le_exp (x:=δ*exp (2*u)) (by positivity) 1
    norm_num at hp
    have hex : exp (δ*exp (2*u))*exp (-(δ*exp (2*u))) = 1 := by
      rw [← exp_add]; simp
    have hpay : exp (2*u)*exp (-(δ*exp (2*u))) ≤ 1/δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith [mul_le_mul_of_nonneg_right hp (exp_pos (-(δ*exp (2*u)))).le]
    have hehalf : exp (u/2) ≤ exp (2*u)*exp (-u) := by
      rw [← exp_add]
      exact exp_le_exp.mpr (by linarith)
    have hsmall : exp (u/2)*exp (-(δ*exp (2*u))) ≤ (1/δ)*exp (-u) := by
      calc _ ≤ (exp (2*u)*exp (-u))*exp (-(δ*exp (2*u))) := by gcongr
        _ = (exp (2*u)*exp (-(δ*exp (2*u))))*exp (-u) := by ring
        _ ≤ _ := by gcongr
    have he : exp (-(b*exp (2*u))) =
        exp (-(δ*exp (2*u)))*exp (-(a*exp (2*u))) := by
      rw [← exp_add, hbδ]
      congr 1
      ring
    have hid : ‖riemannKernelDeriv k u‖ = |cuspSeries (riemannKernelPoly k) u| := by
      simp only [riemannKernelDeriv, riemannKernelPoly, Complex.norm_real, Real.norm_eq_abs]
    rw [hid]
    refine h.trans ?_
    rw [he]
    calc _ = (A*C^k*((k+2).factorial:ℝ)/(1-exp (-b)))*
          (exp (u/2)*exp (-(δ*exp (2*u))))*exp (-(a*exp (2*u))) := by ring
      _ ≤ (A*C^k*((k+2).factorial:ℝ)/(1-exp (-b)))*
          ((1/δ)*exp (-u))*exp (-(a*exp (2*u))) := by gcongr
      _ = _ := by ring
  intro k u
  have hn : ‖riemannKernelDeriv k |u|‖ = ‖riemannKernelDeriv k u‖ := by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, norm_riemannKernelDeriv_neg]
  simpa only [hn] using hright k |u| (abs_nonneg u)

/-- Finite synthesis, allowing arbitrary complex coefficients and arbitrary orders. -/
def packet {ι : Type*} [Fintype ι] (k : ι → ℕ) (c : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ j, c j*riemannKernelDeriv (k j) u

/-- The explicit factorial coefficient budget, with no bound imposed on derivative orders. -/
def budget {ι : Type*} [Fintype ι] (C : ℝ) (k : ι → ℕ) (c : ι → ℂ) : ℝ :=
  ∑ j, ‖c j‖*C^(k j)*((k j+2).factorial:ℝ)

private theorem budget_nonneg {ι : Type*} [Fintype ι] {C : ℝ} (hC : 0 < C)
    (k : ι → ℕ) (c : ι → ℂ) : 0 ≤ budget C k c := by
  unfold budget
  exact Finset.sum_nonneg fun j _ => by positivity

private theorem packet_continuous {ι : Type*} [Fintype ι] (k : ι → ℕ) (c : ι → ℂ) :
    Continuous (packet k c) := by
  unfold packet
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_riemannKernelDeriv _))

/-- Common envelope for all finite packets, including growing orders and row counts. -/
theorem packet_factorial_envelope {a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ C=3+4*π/(π-a) ∧ ∀ {ι : Type} [Fintype ι]
      (k : ι → ℕ) (c : ι → ℂ) (u : ℝ),
      ‖packet k c u‖ ≤ B*budget C k c*exp (-(a*exp (2*|u|)))*exp (-|u|) := by
  obtain ⟨B,C,hB,hC,hCeq,h⟩ := kernel_derivative_factorial_envelope ha haπ
  refine ⟨B,C,hB,hC,hCeq,?_⟩
  intro ι _ k c u
  calc ‖packet k c u‖ ≤ ∑ j, ‖c j*riemannKernelDeriv (k j) u‖ := norm_sum_le _ _
    _ = ∑ j, ‖c j‖*‖riemannKernelDeriv (k j) u‖ := by simp only [norm_mul]
    _ ≤ ∑ j, ‖c j‖*(B*C^(k j)*((k j+2).factorial:ℝ)*
        exp (-(a*exp (2*|u|)))*exp (-|u|)) := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h (k j) u) (norm_nonneg _)
    _ = _ := by
      unfold budget
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The literal complete autocorrelation of a derivative packet. -/
def correlation {ι : Type*} [Fintype ι] (k : ι → ℕ) (c : ι → ℂ) (y : ℝ) : ℂ :=
  ∫ u : ℝ, packet k c u * conj (packet k c (u-y))

private theorem exp_pair (u y : ℝ) : 2*exp |y| ≤ exp (2*|u|)+exp (2*|u-y|) := by
  have ht : |y| ≤ |u|+|u-y| := calc
    |y| = |u-(u-y)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
  have he := exp_le_exp.mpr ht
  rw [exp_add] at he
  have h1 : exp (2*|u|) = exp |u|^2 := by rw [show 2*|u|=|u|+|u| by ring, exp_add, sq]
  have h2 : exp (2*|u-y|) = exp |u-y|^2 := by rw [show 2*|u-y|=|u-y|+|u-y| by ring, exp_add, sq]
  rw [h1,h2]
  nlinarith [sq_nonneg (exp |u|-exp |u-y|)]

/-- Full autocorrelation and integrability with one factorial budget for every derivative order. -/
theorem correlation_factorial_bound {a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ C=3+4*π/(π-a) ∧ ∀ {ι : Type} [Fintype ι]
      (k : ι → ℕ) (c : ι → ℂ) (y : ℝ),
      Integrable (fun u : ℝ => packet k c u*conj (packet k c (u-y))) ∧
      ‖correlation k c y‖ ≤ B*(budget C k c)^2*exp (-(2*a*exp |y|)) := by
  obtain ⟨B,C,hB,hC,hCeq,h⟩ := packet_factorial_envelope ha haπ
  refine ⟨2*B^2,C,by positivity,hC,hCeq,?_⟩
  intro ι _ k c y
  have hV := budget_nonneg hC k c
  have hpt (u : ℝ) : ‖packet k c u*conj (packet k c (u-y))‖ ≤
      (B*budget C k c)^2*exp (-(2*a*exp |y|))*exp (-|u|) := by
    rw [norm_mul, Complex.norm_conj]
    have he : exp (-(a*exp (2*|u|)))*exp (-(a*exp (2*|u-y|))) ≤
        exp (-(2*a*exp |y|)) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith [exp_pair u y]
    have hs : exp (-|u-y|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg (u-y)])
    calc _ ≤ (B*budget C k c*exp (-(a*exp (2*|u|)))*exp (-|u|))*
          (B*budget C k c*exp (-(a*exp (2*|u-y|)))*exp (-|u-y|)) :=
        mul_le_mul (h k c u) (h k c (u-y)) (norm_nonneg _) (by positivity)
      _ = (B*budget C k c)^2*(exp (-(a*exp (2*|u|)))*exp (-(a*exp (2*|u-y|))))*
          exp (-|u|)*exp (-|u-y|) := by ring
      _ ≤ (B*budget C k c)^2*exp (-(2*a*exp |y|))*exp (-|u|)*1 := by gcongr
      _ = _ := by ring
  have hg := integrable_exp_neg_abs.const_mul ((B*budget C k c)^2*exp (-(2*a*exp |y|)))
  have hf := packet_continuous k c
  have hi : Integrable (fun u : ℝ => packet k c u*conj (packet k c (u-y))) := by
    apply hg.mono' (hf.mul (Complex.continuous_conj.comp (hf.comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
    exact Eventually.of_forall hpt
  refine ⟨hi,?_⟩
  have hiB := norm_integral_le_of_norm_le hg (Eventually.of_forall hpt)
  rw [integral_const_mul, integral_exp_neg_abs] at hiB
  exact hiB.trans_eq (by ring)

private theorem actual_weight_bound : ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
    WeilWorkDeficitBudget.weight n ≤ D*(n+3)*sqrt (n+2) := by
  obtain ⟨D,hD,hd⟩ := WeilWorkPBAP.atomCost_le_polynomial
  refine ⟨D+1,by positivity,fun n => ?_⟩
  have hA := hd (WeilWorkDeficitBudget.logIndex n)
  have hL := ArithmeticFunction.vonMangoldt_le_log (n:=n+2)
  have hl := Real.log_le_sub_one_of_pos (show (0:ℝ)<n+2 by positivity)
  have hs : 1 ≤ sqrt (n+2:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr
    (by have := Nat.cast_nonneg (α:=ℝ) n; nlinarith)
  have hm : (n+2:ℝ) ≤ (n+3)*sqrt (n+2) := by nlinarith
  dsimp [WeilWorkDeficitBudget.logIndex] at hA
  simp only [Nat.cast_add, Nat.cast_ofNat] at hA hL
  dsimp [WeilWorkDeficitBudget.weight, WeilWorkDeficitBudget.logIndex]
  nlinarith

private theorem actual_weight_nonneg (n : ℕ) : 0 ≤ WeilWorkDeficitBudget.weight n := by
  unfold WeilWorkDeficitBudget.weight
  exact add_nonneg ArithmeticFunction.vonMangoldt_nonneg (WeilWorkPBAP.atomCost_nonneg _)

/-- Full actual repair-weighted term bound, uniform in all derivative orders. -/
theorem weighted_correlation_factorial_bound {r : ℝ} (hr : 0 < r) (hrπ : r < 2*π) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ C=3+16*π/(2*π-r) ∧ ∀ {ι : Type} [Fintype ι]
      (k : ι → ℕ) (c : ι → ℂ) (n : ℕ),
      WeilWorkDeficitBudget.weight n*‖correlation k c (log (n+2))‖ ≤
        B*(budget C k c)^2*exp (-(r*(n+2))) := by
  let a := (r+2*π)/4
  have ha : 0 < a := by dsimp [a]; positivity
  have haπ : a < π := by dsimp [a]; linarith
  have hs : 0 < 2*a-r := by dsimp [a]; linarith
  obtain ⟨B,C,hB,hC,hCeq,hcorr⟩ := correlation_factorial_bound ha haπ
  obtain ⟨D,hD,hweight⟩ := actual_weight_bound
  have hCexplicit : C=3+16*π/(2*π-r) := by
    rw [hCeq]
    have he : π-a=(2*π-r)/4 := by dsimp [a]; ring
    rw [he]
    have hne : 2*π-r ≠ 0 := by linarith
    field_simp [hne]
    ring
  refine ⟨4*D*B/(2*a-r)^2,C,by positivity,hC,hCexplicit,?_⟩
  intro ι _ k c n
  have hn : (0:ℝ)<n+2 := by positivity
  have hn1 : (1:ℝ)≤n+2 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
  have hc := (hcorr k c (log (n+2))).2
  rw [abs_of_nonneg (log_nonneg hn1), exp_log hn] at hc
  have hw : WeilWorkDeficitBudget.weight n ≤ 2*D*(n+2)^2 := by
    have hsqrt : sqrt (n+2:ℝ) ≤ n+2 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hn.le,by nlinarith⟩
    calc _ ≤ D*(n+3)*sqrt (n+2) := hweight n
      _ ≤ D*(n+3)*(n+2) := by gcongr
      _ ≤ D*(2*(n+2))*(n+2) := by gcongr; linarith
      _ = _ := by ring
  have hpoly : (n+2:ℝ)^2*exp (-((2*a-r)*(n+2))) ≤ 2/(2*a-r)^2 := by
    have hp := Real.pow_div_factorial_le_exp (x:=(2*a-r)*(n+2)) (by positivity) 2
    norm_num [mul_pow] at hp
    have hex : exp ((2*a-r)*(n+2))*exp (-((2*a-r)*(n+2))) = 1 := by
      rw [← exp_add]; simp
    have hm := mul_le_mul_of_nonneg_right hp (exp_pos (-((2*a-r)*(n+2)))).le
    apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
    nlinarith
  have he : exp (-(2*a*(n+2))) =
      exp (-((2*a-r)*(n+2)))*exp (-(r*(n+2))) := by
    rw [← exp_add]; congr 1; ring
  calc _ ≤ (2*D*(n+2)^2)*(B*(budget C k c)^2*exp (-(2*a*(n+2)))) :=
      mul_le_mul hw hc (norm_nonneg _) (by positivity)
    _ = (2*D*B*(budget C k c)^2)*((n+2)^2*exp (-((2*a-r)*(n+2))))*
        exp (-(r*(n+2))) := by rw [he]; ring
    _ ≤ (2*D*B*(budget C k c)^2)*(2/(2*a-r)^2)*exp (-(r*(n+2))) := by gcongr
    _ = _ := by ring

/-- The complete actual weighted arithmetic tail, priced uniformly in derivative order. -/
theorem weighted_tail_factorial_bound {r : ℝ} (hr : 0 < r) (hrπ : r < 2*π) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ C=3+16*π/(2*π-r) ∧ ∀ {ι : Type} [Fintype ι]
      (k : ι → ℕ) (c : ι → ℂ) (N : ℕ),
      Summable (fun n : ℕ => WeilWorkDeficitBudget.weight (N+n)*
        ‖correlation k c (log ((N+n:ℕ)+2:ℝ))‖) ∧
      (∑' n : ℕ, WeilWorkDeficitBudget.weight (N+n)*
        ‖correlation k c (log ((N+n:ℕ)+2:ℝ))‖) ≤
          B*(budget C k c)^2*exp (-(r*(N+2))) := by
  obtain ⟨B,C,hB,hC,hCeq,hterm⟩ := weighted_correlation_factorial_bound hr hrπ
  have hq : exp (-r) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hq0 := (exp_pos (-r)).le
  refine ⟨B/(1-exp (-r)),C,by positivity,hC,hCeq,?_⟩
  intro ι _ k c N
  let D := B*(budget C k c)^2*exp (-(r*(N+2)))
  have hb (n : ℕ) : WeilWorkDeficitBudget.weight (N+n)*
      ‖correlation k c (log ((N+n:ℕ)+2:ℝ))‖ ≤ D*exp (-r)^n := by
    refine (hterm k c (N+n)).trans_eq ?_
    dsimp [D]
    rw [← exp_nat_mul]
    have he : exp (-(r*((N+n:ℕ)+2:ℝ))) = exp (-(r*(N+2)))*exp ((n:ℝ)* -r) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [he]; ring
  have hs := (summable_geometric_of_lt_one hq0 hq).mul_left D
  have hsA := hs.of_nonneg_of_le (fun n => mul_nonneg (actual_weight_nonneg (N+n)) (norm_nonneg _)) hb
  refine ⟨hsA,?_⟩
  have h := hsA.tsum_le_tsum hb hs
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq] at h
  exact h.trans_eq (by dsimp [D]; ring)

end RHTower.WeilWorkDeficitDerivativeBudget
