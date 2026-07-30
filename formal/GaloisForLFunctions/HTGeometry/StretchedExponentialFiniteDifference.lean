import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv

open Filter Finset Set Asymptotics Topology

/-!
# Stretched-exponential finite differences

This file proves the exact derivative scale of `exp (x ^ α)` for `α > 0`, controls fixed
translations when `0 < α < 1`, and formalizes the first-nonzero-moment asymptotic for every
finitely supported real difference pattern.  The final corollary proves that its absolute defect
dominates `log x` in little-o form.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The real stretched exponential profile `x ↦ exp (x ^ α)`. -/
def stretchedExp (α x : ℝ) : ℝ := Real.exp (x ^ α)

lemma _root_.OrderedFinpartition.partSize_eq_one_of_length_eq {n : ℕ}
    (c : OrderedFinpartition n) (hlen : c.length = n) (i : Fin c.length) :
    c.partSize i = 1 := by
  have hcard : ∑ j : Fin c.length, c.partSize j = n := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using
      Fintype.card_congr c.equivSigma
  have hsub : ∑ j : Fin c.length, (c.partSize j - 1) = 0 := by
    rw [Finset.sum_tsub_distrib]
    · simp [hcard, hlen]
    · intro j _
      exact c.partSize_pos j
  have hi : c.partSize i - 1 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hsub i (Finset.mem_univ i)
  have hpos := c.partSize_pos i
  omega

lemma _root_.OrderedFinpartition.eq_atomic_of_length_eq {n : ℕ}
    (c : OrderedFinpartition n) (hlen : c.length = n) :
    c = OrderedFinpartition.atomic n := by
  have hsize : ∀ i, c.partSize i = 1 :=
    fun i => c.partSize_eq_one_of_length_eq hlen i
  rcases c with ⟨length, partSize, hpos, emb, hemb, hparts, hdisjoint, hcover⟩
  simp only at hlen hsize ⊢
  subst length
  have hp : partSize = fun _ => 1 := funext hsize
  subst partSize
  have hparts' : StrictMono (fun m : Fin n => emb m 0) := by
    simpa using hparts
  have heq : (fun m : Fin n => emb m 0) = id := by
    funext m
    exact le_antisymm (hparts'.le_id m) (hparts'.id_le m)
  have h₃ (i : Fin n) (j : Fin 1) : emb i j = i := by
    rw [Subsingleton.elim j 0]
    exact congrFun heq i
  have hemb : emb = fun i (_ : Fin 1) => i := by
    funext i j
    exact h₃ i j
  subst emb
  rfl

lemma _root_.OrderedFinpartition.length_lt_of_ne_atomic {n : ℕ}
    (c : OrderedFinpartition n) (hne : c ≠ OrderedFinpartition.atomic n) :
    c.length < n := by
  exact lt_of_le_of_ne c.length_le (fun h => hne (c.eq_atomic_of_length_eq h))

lemma iteratedDeriv_stretchedExp_exact (α x : ℝ) (k : ℕ) (hx : 0 < x) :
    iteratedDeriv k (stretchedExp α) x =
      Real.exp (x ^ α) *
        ∑ c : OrderedFinpartition k,
          (∏ j, (descPochhammer ℝ (c.partSize j)).eval α) *
            x ^ ((c.length : ℝ) * α - k) := by
  have hcomp : stretchedExp α = Real.exp ∘ fun x : ℝ => x ^ α := rfl
  rw [hcomp, iteratedDeriv_comp_eq_sum_orderedFinpartition
    Real.contDiff_exp.contDiffAt (Real.contDiffAt_rpow_const_of_ne hx.ne') le_top]
  simp_rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.iter_deriv_rpow_const]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.prod_mul_distrib]
  have hrpow :
      ∏ j : Fin c.length, x ^ (α - (c.partSize j : ℝ)) =
        x ^ ((c.length : ℝ) * α - k) := by
    rw [← Real.rpow_sum_of_pos hx]
    congr 1
    have hcard : ∑ j : Fin c.length, c.partSize j = k := by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using
        Fintype.card_congr c.equivSigma
    have hcard' : ∑ j : Fin c.length, (c.partSize j : ℝ) = (k : ℝ) := by
      exact_mod_cast hcard
    rw [Finset.sum_sub_distrib, hcard']
    simp
  rw [hrpow]

private def stretchedDerivCoefficient (α : ℝ) {k : ℕ}
    (c : OrderedFinpartition k) : ℝ :=
  ∏ j, (descPochhammer ℝ (c.partSize j)).eval α

private def stretchedDerivTerm (α : ℝ) {k : ℕ}
    (c : OrderedFinpartition k) (x : ℝ) : ℝ :=
  stretchedDerivCoefficient α c * Real.exp (x ^ α) *
    x ^ ((c.length : ℝ) * α - k)

/-- The leading scale of the `k`th derivative of `exp (x ^ α)`. -/
def stretchedDerivativeLeading (α : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  α ^ k * Real.exp (x ^ α) * x ^ ((k : ℝ) * α - k)

private lemma stretchedDerivTerm_isLittleO_leading {α : ℝ} (hα : 0 < α) {k : ℕ}
    (c : OrderedFinpartition k) (hc : c ≠ OrderedFinpartition.atomic k) :
    stretchedDerivTerm α c =o[atTop] stretchedDerivativeLeading α k := by
  have hlen : c.length < k := c.length_lt_of_ne_atomic hc
  have hlen' : (c.length : ℝ) < (k : ℝ) := by exact_mod_cast hlen
  have hδ : 0 < ((k : ℝ) - (c.length : ℝ)) * α :=
    mul_pos (sub_pos.mpr hlen') hα
  refine (isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro hzero
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hα.ne') (Real.exp_ne_zero _))
      (ne_of_gt (Real.rpow_pos_of_pos hx _)) hzero).elim
  · have ht : Tendsto
        (fun x : ℝ => (stretchedDerivCoefficient α c / α ^ k) *
          x ^ (-(((k : ℝ) - (c.length : ℝ)) * α))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hδ).const_mul
        (stretchedDerivCoefficient α c / α ^ k)
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [stretchedDerivTerm, stretchedDerivativeLeading]
    symm
    rw [div_eq_iff]
    · field_simp [pow_ne_zero _ hα.ne']
      rw [mul_assoc, ← Real.rpow_add hx]
      congr 1
      ring_nf
    · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hα.ne') (Real.exp_ne_zero _))
        (ne_of_gt (Real.rpow_pos_of_pos hx _))

private lemma stretchedDerivTerm_atomic (α : ℝ) (k : ℕ) :
    stretchedDerivTerm α (OrderedFinpartition.atomic k) =
      stretchedDerivativeLeading α k := by
  funext x
  simp only [stretchedDerivTerm, stretchedDerivCoefficient, stretchedDerivativeLeading,
    OrderedFinpartition.atomic_partSize, descPochhammer_one, Polynomial.eval_X,
    Finset.prod_const, Finset.card_univ, OrderedFinpartition.atomic_length]
  have hp : α ^ Fintype.card (Fin k) = α ^ k :=
    congrArg (fun m : ℕ => α ^ m) (Fintype.card_fin k)
  exact congrArg (fun y => y * Real.exp (x ^ α) * x ^ ((k : ℝ) * α - k)) hp

theorem iteratedDeriv_stretchedExp_isEquivalent {α : ℝ} (hα : 0 < α) (k : ℕ) :
    (fun x => iteratedDeriv k (stretchedExp α) x) ~[atTop]
      stretchedDerivativeLeading α k := by
  let a : OrderedFinpartition k := OrderedFinpartition.atomic k
  let R : ℝ → ℝ := fun x =>
    ∑ c ∈ (Finset.univ : Finset (OrderedFinpartition k)).erase a,
      stretchedDerivTerm α c x
  have hR : R =o[atTop] stretchedDerivativeLeading α k := by
    exact IsLittleO.sum fun c hc =>
      stretchedDerivTerm_isLittleO_leading hα c (Finset.ne_of_mem_erase hc)
  have heq : (fun x => iteratedDeriv k (stretchedExp α) x) =ᶠ[atTop]
      fun x => stretchedDerivativeLeading α k x + R x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [iteratedDeriv_stretchedExp_exact α x k hx]
    have hsum :
        Real.exp (x ^ α) *
            ∑ c : OrderedFinpartition k,
              (∏ j, (descPochhammer ℝ (c.partSize j)).eval α) *
                x ^ ((c.length : ℝ) * α - k) =
          ∑ c : OrderedFinpartition k, stretchedDerivTerm α c x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      simp only [stretchedDerivTerm, stretchedDerivCoefficient]
      ring
    rw [hsum, ← Finset.sum_erase_add Finset.univ
      (fun c : OrderedFinpartition k => stretchedDerivTerm α c x) (Finset.mem_univ a)]
    rw [stretchedDerivTerm_atomic]
    simp only [R]
    ring
  exact (IsEquivalent.refl.add_isLittleO hR).congr_left (heq.mono fun x hx => hx.symm)

lemma rpow_add_sub_bounds {α x r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hx : 0 < x) (hr : 0 ≤ r) :
    0 ≤ (x + r) ^ α - x ^ α ∧
      (x + r) ^ α - x ^ α ≤ α * r * x ^ (α - 1) := by
  constructor
  · exact sub_nonneg.mpr (Real.rpow_le_rpow hx.le (by linarith) hα0.le)
  · rcases hr.eq_or_lt with rfl | hr
    · simp
    have hconc := Real.concaveOn_rpow hα0.le hα1.le
    have hslope := hconc.slope_le_of_hasDerivAt
      (show x ∈ Ici (0 : ℝ) by exact hx.le)
      (show x + r ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
      (show x < x + r by linarith)
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne'))
    rw [slope_def_field] at hslope
    have hmul := (div_le_iff₀ hr).mp (by simpa using hslope)
    nlinarith

theorem tendsto_rpow_add_sub_atTop_nhds_zero {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun x : ℝ => (x + r) ^ α - x ^ α) atTop (𝓝 0) := by
  have hp : 0 < 1 - α := sub_pos.mpr hα1
  have ht : Tendsto (fun x : ℝ => α * r * x ^ (α - 1)) atTop (𝓝 0) := by
    have ht' := (tendsto_rpow_neg_atTop hp).const_mul (α * r)
    convert ht' using 1
    · funext x
      congr 2
      ring_nf
    · ring_nf
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (rpow_add_sub_bounds hα0 hα1 hx hr).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (rpow_add_sub_bounds hα0 hα1 hx hr).2
  · exact ht

theorem tendsto_exp_rpow_add_sub_atTop_nhds_one {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun x : ℝ => Real.exp ((x + r) ^ α - x ^ α)) atTop (𝓝 1) := by
  exact Real.tendsto_exp_nhds_zero_nhds_one.comp
    (tendsto_rpow_add_sub_atTop_nhds_zero hα0 hα1 r hr)

private def stretchedTaylorRemainderBound
    (C α : ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  C * α ^ (j + 1) * Real.exp ((x + r) ^ α) *
      x ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) * r ^ (j + 1) / (j.factorial : ℝ)

private lemma stretchedTaylorRemainderBound_isLittleO {C α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (j : ℕ) :
    stretchedTaylorRemainderBound C α j r =o[atTop]
      stretchedDerivativeLeading α j := by
  let K : ℝ := C * α * r ^ (j + 1) / (j.factorial : ℝ)
  have hxpow : Tendsto (fun x : ℝ => x ^ (α - 1)) atTop (𝓝 0) := by
    have hp : 0 < 1 - α := sub_pos.mpr hα1
    convert tendsto_rpow_neg_atTop hp using 1
    funext x
    congr 2
    ring
  have hratio : Tendsto
      (fun x : ℝ => K * Real.exp ((x + r) ^ α - x ^ α) * x ^ (α - 1))
      atTop (𝓝 0) := by
    simpa [mul_assoc] using
      ((tendsto_exp_rpow_add_sub_atTop_nhds_one hα0 hα1 r hr).mul hxpow).const_mul K
  refine (isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro hzero
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hα0.ne') (Real.exp_ne_zero _))
      (ne_of_gt (Real.rpow_pos_of_pos hx _)) hzero).elim
  · refine hratio.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [K, stretchedTaylorRemainderBound, stretchedDerivativeLeading]
    symm
    rw [div_eq_iff]
    · rw [Real.exp_sub]
      field_simp [pow_ne_zero _ hα0.ne', Real.exp_ne_zero]
      ring_nf
      have hp :
          x ^ (α * ((1 + j : ℕ) : ℝ) - ((1 + j : ℕ) : ℝ)) =
            x ^ (-1 + α) * x ^ (α * (j : ℝ) - (j : ℝ)) := by
        rw [← Real.rpow_add hx]
        congr 1
        push_cast
        ring
      rw [hp]
      ring
    · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hα0.ne') (Real.exp_ne_zero _))
        (ne_of_gt (Real.rpow_pos_of_pos hx _))

private def iteratedTaylorShift (f : ℝ → ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), iteratedDeriv k f x * r ^ k / (k.factorial : ℝ)

private lemma taylorWithinEval_add_eq_iteratedTaylorShift {f : ℝ → ℝ} {x r : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hr : 0 < r) (j : ℕ) :
    taylorWithinEval f j (uIcc x (x + r)) x (x + r) =
      iteratedTaylorShift f j r x := by
  have hle : x ≤ x + r := by linarith
  rw [uIcc_of_le hle]
  induction j with
  | zero =>
      simp [iteratedTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih]
      simp only [iteratedTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) f (Icc x (x + r)) x =
          iteratedDeriv (j + 1) f x := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
          (hf.of_le (WithTop.coe_le_coe.mpr le_top))
          (left_mem_Icc.mpr hle)
      rw [hderiv]
      rw [Nat.factorial_succ]
      push_cast
      ring

private lemma contDiffAt_stretchedExp {α x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (stretchedExp α) x := by
  exact Real.contDiff_exp.contDiffAt.comp x (Real.contDiffAt_rpow_const_of_ne hx)

private theorem stretchedExp_taylor_remainder_isLittleO {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (j : ℕ) :
    (fun x => stretchedExp α (x + r) - iteratedTaylorShift (stretchedExp α) j r x)
      =o[atTop] stretchedDerivativeLeading α j := by
  rcases hr.eq_or_lt with rfl | hr
  · have heq : ∀ x, iteratedTaylorShift (stretchedExp α) j 0 x = stretchedExp α x := by
      intro x
      rw [iteratedTaylorShift, Finset.sum_eq_single 0]
      · simp [iteratedDeriv_zero]
      · intro k hk hne
        simp [zero_pow hne]
      · simp
    simpa only [add_zero, heq, sub_self] using
      (Asymptotics.isLittleO_zero (stretchedDerivativeLeading α j) atTop)
  have hderivO := (iteratedDeriv_stretchedExp_isEquivalent hα0 (j + 1)).isBigO
  obtain ⟨C, hCnonneg, hC⟩ := hderivO.exists_nonneg
  obtain ⟨Y, hCY⟩ := Filter.eventually_atTop.mp hC.bound
  have hremBound : ∀ᶠ x in atTop,
      ‖stretchedExp α (x + r) - iteratedTaylorShift (stretchedExp α) j r x‖ ≤
        stretchedTaylorRemainderBound C α j r x := by
    filter_upwards [eventually_ge_atTop (max Y 1)] with x hx
    have hx1 : 1 ≤ x := (le_max_right Y 1).trans hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hle : x ≤ x + r := by linarith
    have hlt : x < x + r := by linarith
    have hcont : ContDiffOn ℝ (j + 1 : ℕ) (stretchedExp α) (Icc x (x + r)) := by
      intro y hy
      exact ((contDiffAt_stretchedExp (show y ≠ 0 by linarith [hy.1])).of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
    have hiter : ∀ y ∈ Icc x (x + r),
        ‖iteratedDerivWithin (j + 1) (stretchedExp α) (Icc x (x + r)) y‖ ≤
          C * α ^ (j + 1) * Real.exp ((x + r) ^ α) *
            x ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) := by
      intro y hy
      have hy0 : 0 < y := hx0.trans_le hy.1
      have hyY : Y ≤ y := (le_max_left Y 1).trans hx |>.trans hy.1
      have hfull : iteratedDerivWithin (j + 1) (stretchedExp α)
          (Icc x (x + r)) y = iteratedDeriv (j + 1) (stretchedExp α) y := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
          ((contDiffAt_stretchedExp hy0.ne').of_le (WithTop.coe_le_coe.mpr le_top)) hy
      rw [hfull]
      have hbase := hCY y hyY
      have hleadNorm : ‖stretchedDerivativeLeading α (j + 1) y‖ =
          α ^ (j + 1) * Real.exp (y ^ α) *
            y ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) := by
        rw [Real.norm_eq_abs, abs_of_pos]
        · simp only [stretchedDerivativeLeading]
          congr 2
          ring
        · simp only [stretchedDerivativeLeading]
          positivity
      rw [hleadNorm] at hbase
      have hexp : Real.exp (y ^ α) ≤ Real.exp ((x + r) ^ α) := by
        exact Real.exp_le_exp.mpr (Real.rpow_le_rpow hy0.le hy.2 hα0.le)
      have hexponent : (((j + 1 : ℕ) : ℝ) * (α - 1)) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hα1.le)
      have hrpow : y ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) ≤
          x ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) :=
        Real.rpow_le_rpow_of_nonpos hx0 hy.1 hexponent
      have hprofile :
          α ^ (j + 1) * Real.exp (y ^ α) *
              y ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) ≤
            α ^ (j + 1) * Real.exp ((x + r) ^ α) *
              x ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) := by
        have hstep1 :
            α ^ (j + 1) * Real.exp (y ^ α) *
                y ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) ≤
              α ^ (j + 1) * Real.exp ((x + r) ^ α) *
                y ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp (by positivity)) (Real.rpow_nonneg hy0.le _)
        exact hstep1.trans <| mul_le_mul_of_nonneg_left hrpow (by positivity)
      calc
        ‖iteratedDeriv (j + 1) (stretchedExp α) y‖
            ≤ C * (α ^ (j + 1) * Real.exp (y ^ α) *
              y ^ (((j + 1 : ℕ) : ℝ) * (α - 1))) := hbase
        _ ≤ C * α ^ (j + 1) * Real.exp ((x + r) ^ α) *
              x ^ (((j + 1 : ℕ) : ℝ) * (α - 1)) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprofile hCnonneg
    have htaylor := taylor_mean_remainder_bound hle hcont
      (right_mem_Icc.mpr hle) hiter
    have hteq := taylorWithinEval_add_eq_iteratedTaylorShift
      (f := stretchedExp α) (contDiffAt_stretchedExp (α := α) hx0.ne') hr j
    rw [uIcc_of_le hle] at hteq
    rw [hteq] at htaylor
    simpa [stretchedTaylorRemainderBound, sub_eq_add_neg, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using htaylor
  have hboundLittle := stretchedTaylorRemainderBound_isLittleO hα0 hα1 hr.le j (C := C)
  refine IsLittleO.of_bound fun c hc => ?_
  have hcB := (hboundLittle.forall_isBigOWith hc).bound
  filter_upwards [hremBound, hcB] with x hxrem hxB
  calc
    ‖stretchedExp α (x + r) - iteratedTaylorShift (stretchedExp α) j r x‖
        ≤ stretchedTaylorRemainderBound C α j r x := hxrem
    _ ≤ ‖stretchedTaylorRemainderBound C α j r x‖ := le_abs_self _
    _ ≤ c * ‖stretchedDerivativeLeading α j x‖ := hxB

def stretchedMoment (d : ℕ →₀ ℝ) (k : ℕ) : ℝ :=
  d.sum fun r a => a * (r : ℝ) ^ k

def stretchedFiniteDifference (α : ℝ) (d : ℕ →₀ ℝ) (x : ℝ) : ℝ :=
  d.sum fun r a => a * stretchedExp α (x + r)

lemma finsupp_sum_iteratedTaylorShift_eq {f : ℝ → ℝ} (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0) (x : ℝ) :
    d.sum (fun r a => a * iteratedTaylorShift f j r x) =
      stretchedMoment d j * iteratedDeriv j f x / (j.factorial : ℝ) := by
  classical
  rw [Finsupp.sum]
  simp_rw [iteratedTaylorShift, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hjterm :
      (∑ r ∈ d.support,
          d r * (iteratedDeriv j f x * (r : ℝ) ^ j / (j.factorial : ℝ))) =
        stretchedMoment d j * iteratedDeriv j f x / (j.factorial : ℝ) := by
    rw [stretchedMoment, Finsupp.sum]
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [← hjterm]
  apply Finset.sum_eq_single j
  · intro k hk hkj
    have hkle : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkl : k < j := lt_of_le_of_ne hkle hkj
    have hsum : (∑ r ∈ d.support, d r * (r : ℝ) ^ k) = 0 := by
      simpa only [stretchedMoment, Finsupp.sum] using hcancel k hkl
    calc
      (∑ r ∈ d.support,
          d r * (iteratedDeriv k f x * (r : ℝ) ^ k / (k.factorial : ℝ))) =
          (iteratedDeriv k f x / (k.factorial : ℝ)) *
            ∑ r ∈ d.support, d r * (r : ℝ) ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = 0 := by rw [hsum, mul_zero]
  · simp

def stretchedFiniteDifferenceLeading
    (α : ℝ) (d : ℕ →₀ ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (stretchedMoment d j * α ^ j / (j.factorial : ℝ)) *
    Real.exp (x ^ α) * x ^ ((j : ℝ) * α - j)

theorem stretchedFiniteDifference_isEquivalent {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0) :
    stretchedFiniteDifference α d ~[atTop]
      stretchedFiniteDifferenceLeading α d j := by
  classical
  let A : ℝ := stretchedMoment d j / (j.factorial : ℝ)
  have hA : A ≠ 0 := div_ne_zero hmoment (by positivity)
  let R : ℝ → ℝ := fun x => d.sum fun r a =>
    a * (stretchedExp α (x + r) -
      iteratedTaylorShift (stretchedExp α) j r x)
  have hR : R =o[atTop] fun x => A * stretchedDerivativeLeading α j x := by
    have hs :
        (fun x => ∑ r ∈ d.support,
          d r * (stretchedExp α (x + r) -
            iteratedTaylorShift (stretchedExp α) j r x))
          =o[atTop] fun x => A * stretchedDerivativeLeading α j x := by
      exact IsLittleO.sum fun r hr =>
        ((stretchedExp_taylor_remainder_isLittleO hα0 hα1
          (show (0 : ℝ) ≤ (r : ℝ) by positivity) j).const_mul_left (d r)).const_mul_right hA
    simpa only [R, Finsupp.sum] using hs
  have heq : stretchedFiniteDifference α d =ᶠ[atTop]
      fun x => A * iteratedDeriv j (stretchedExp α) x + R x := by
    apply Eventually.of_forall
    intro x
    have hTaylor := finsupp_sum_iteratedTaylorShift_eq d j hcancel x
      (f := stretchedExp α)
    rw [Finsupp.sum] at hTaylor
    rw [stretchedFiniteDifference, Finsupp.sum]
    have hsplit :
        (∑ r ∈ d.support, d r * stretchedExp α (x + r)) =
          (∑ r ∈ d.support,
              d r * iteratedTaylorShift (stretchedExp α) j r x) +
            ∑ r ∈ d.support,
              d r * (stretchedExp α (x + r) -
                iteratedTaylorShift (stretchedExp α) j r x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hsplit, hTaylor]
    simp only [A, R, Finsupp.sum]
    ring
  have hconst : (fun _ : ℝ => A) ~[atTop] fun _ : ℝ => A := IsEquivalent.refl
  have hmain := hconst.mul (iteratedDeriv_stretchedExp_isEquivalent hα0 j)
  have htotal := hmain.add_isLittleO hR
  have hleft := htotal.congr_left (heq.mono fun x hx => hx.symm)
  refine hleft.congr_right (Eventually.of_forall fun x => ?_)
  change A * stretchedDerivativeLeading α j x = stretchedFiniteDifferenceLeading α d j x
  dsimp [A, stretchedDerivativeLeading, stretchedFiniteDifferenceLeading]
  ring_nf

theorem log_isLittleO_abs_stretchedFiniteDifference {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0) :
    Real.log =o[atTop] fun x => |stretchedFiniteDifference α d x| := by
  let C : ℝ := stretchedMoment d j * α ^ j / (j.factorial : ℝ)
  have hC : C ≠ 0 := div_ne_zero (mul_ne_zero hmoment (pow_ne_zero _ hα0.ne')) (by positivity)
  let p : ℝ := (j : ℝ) * (1 - α)
  let s : ℝ := (1 + p) / α
  have htcore := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s 1 one_pos
  have htcomp := htcore.comp (tendsto_rpow_atTop hα0)
  have ht : Tendsto
      (fun x : ℝ => |C|⁻¹ * ((x ^ α) ^ s * Real.exp (-(x ^ α))))
      atTop (𝓝 0) := by
    simpa using htcomp.const_mul |C|⁻¹
  have hxlead : (fun x : ℝ => x) =o[atTop]
      fun x => |stretchedFiniteDifferenceLeading α d j x| := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      intro hzero
      exact (abs_ne_zero.mpr (by
        simp only [stretchedFiniteDifferenceLeading]
        exact mul_ne_zero
          (mul_ne_zero (div_ne_zero (mul_ne_zero hmoment (pow_ne_zero _ hα0.ne')) (by positivity))
            (Real.exp_ne_zero _)) (ne_of_gt (Real.rpow_pos_of_pos hx _))) hzero).elim
    · refine ht.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [stretchedFiniteDifferenceLeading, C, p, s]
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.rpow_pos_of_pos hx _)]
      rw [← Real.rpow_mul hx.le]
      symm
      rw [div_eq_iff]
      · field_simp [abs_ne_zero.mpr hC, Real.exp_ne_zero]
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
        rw [← Real.rpow_add hx]
        have he : 1 + (j : ℝ) * (1 - α) + (j : ℝ) * (α - 1) = 1 := by ring
        rw [he, Real.rpow_one]
      · exact mul_ne_zero (mul_ne_zero (abs_ne_zero.mpr hC) (Real.exp_ne_zero _))
          (ne_of_gt (Real.rpow_pos_of_pos hx _))
  have hlogLead : Real.log =o[atTop]
      fun x => |stretchedFiniteDifferenceLeading α d j x| := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.trans hxlead
  have heq := stretchedFiniteDifference_isEquivalent hα0 hα1 d j hcancel hmoment
  have htheta := heq.isTheta.norm_left.norm_right
  simpa only [Real.norm_eq_abs] using hlogLead.trans_isTheta htheta.symm

end

end GaloisForLFunctions
