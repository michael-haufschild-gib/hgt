import GaloisForLFunctions.HTGeometry.ReflectionlessWell
import GaloisForLFunctions.HTGeometry.ExponentialKernelTotalPositivity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix

/-!
# Strict total positivity of reflectionless eigenmodes

A positive change of gauge turns each eigenmode into a primitive of a weighted
exponential. Rolle’s theorem gives nonsingularity, and continuous deformation
fixes the sign.
-/

namespace GaloisForLFunctions.HTGeometry.Darboux
open Set Matrix Finset Filter Topology
open scoped Classical
noncomputable section


/-- Rolle's theorem on successive disjoint intervals transfers the
Chebyshev bound from the derivatives to primitives anchored at zero. -/
theorem primitive_collocation_nonsingular {n : ℕ} (F D : Fin n → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (F j) (Ici 0)) (h₀ : ∀ j, F j 0 = 0)
    (hd : ∀ j t, 0 < t → HasDerivAt (F j) (D j t) t)
    (hD : ∀ t : Fin n ↪o Ioi (0:ℝ), (of fun i j => D j (t i).val).det ≠ 0)
    (x : Fin n ↪o Ioi (0:ℝ)) : (of fun i j => F j (x i).val).det ≠ 0 := by
  intro hz
  obtain ⟨c,hcne,hcF⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  let g (t : ℝ) := ∑ j, F j t*c j
  let g' (t : ℝ) := ∑ j, D j t*c j
  have hg : ContinuousOn g (Ici 0) := continuousOn_finsetSum _ fun j _ =>
    (hc j).mul continuousOn_const
  have hg₀ : g 0 = 0 := by simp [g,h₀]
  have hgx (i : Fin n) : g (x i).val = 0 := congrFun hcF i
  have hgd (t : ℝ) (ht : 0 < t) : HasDerivAt g (g' t) t :=
    HasDerivAt.fun_sum fun j _ => (hd j t ht).mul_const _
  let prev (i : Fin n) : ℝ := if i.val = 0 then 0 else (x ⟨i.val-1,by omega⟩).val
  have hp (i : Fin n) : 0 ≤ prev i ∧ prev i < (x i).val ∧ g (prev i) = 0 := by
    dsimp [prev]
    split_ifs with h
    · exact ⟨le_rfl,(x i).property,hg₀⟩
    · exact ⟨(x _).property.le,x.strictMono (show (⟨i.val-1,by omega⟩ : Fin n) < i by
        change i.val-1 < i.val; omega),hgx _⟩
  have hr (i : Fin n) : ∃ t ∈ Ioo (prev i) (x i).val, g' t = 0 :=
    exists_hasDerivAt_eq_zero (hp i).2.1 (hg.mono fun _ h => (hp i).1.trans h.1)
      ((hp i).2.2.trans (hgx i).symm) (fun t ht => hgd t ((hp i).1.trans_lt ht.1))
  choose t ht ht' using hr
  let z (i : Fin n) : Ioi (0:ℝ) := ⟨t i,(hp i).1.trans_lt (ht i).1⟩
  have hmono : StrictMono z := by
    intro i j hij
    have hval : i.val < j.val := hij
    have hj : j.val ≠ 0 := by omega
    have hle : i ≤ (⟨j.val-1,by omega⟩ : Fin n) := by change i.val ≤ j.val-1; omega
    have hx' : (x i).val ≤ prev j := by simpa only [prev,if_neg hj] using x.monotone hle
    exact (ht i).2.trans (hx'.trans_lt (ht j).1)
  apply hD (OrderEmbedding.ofStrictMono z hmono)
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  exact ⟨c,hcne,funext ht'⟩

/-- After the substitution t = exp(x), this is the Darboux-transformed
exponential multiplied by the positive hyperbolic denominator. -/
def wellPrimitive (a b t : ℝ) : ℝ := (b-a)*t^(b+a)+(b+a)*t^(b-a)

private theorem wellPrimitive_deriv {a b t : ℝ} (ht : 0 < t) :
    HasDerivAt (wellPrimitive a b)
      ((t^(a-1)+t^(-a-1))*((b^2-a^2)*t^b)) t := by
  have h₁ := (Real.hasDerivAt_rpow_const (p := b+a) (Or.inl ht.ne')).const_mul (b-a)
  have h₂ := (Real.hasDerivAt_rpow_const (p := b-a) (Or.inl ht.ne')).const_mul (b+a)
  apply (h₁.add h₂).congr_deriv
  rw [show b+a-1 = (a-1)+b by ring,show b-a-1 = (-a-1)+b by ring,
    Real.rpow_add ht,Real.rpow_add ht]
  ring

private theorem wellPrimitive_det_ne {n : ℕ} (a : ℝ) (ha : 0 ≤ a) (b : Fin n ↪o ℝ)
    (hb : ∀ j, a < b j) (x : Fin n ↪o Ioi (0:ℝ)) :
    (of fun i j => wellPrimitive a (b j) (x i).val).det ≠ 0 := by
  apply primitive_collocation_nonsingular (fun j => wellPrimitive a (b j))
    (fun j t => (t^(a-1)+t^(-a-1))*((b j^2-a^2)*t^(b j)))
  · intro j
    apply Continuous.continuousOn
    exact (continuous_const.mul (Real.continuous_rpow_const (by linarith [hb j] : 0 ≤ b j+a))).add
      (continuous_const.mul (Real.continuous_rpow_const (sub_nonneg.mpr (hb j).le)))
  · intro j
    simp [wellPrimitive,Real.zero_rpow (by linarith [hb j] : b j+a ≠ 0),
      Real.zero_rpow (sub_ne_zero.mpr (hb j).ne')]
  · exact fun _ _ ht => wellPrimitive_deriv ht
  · intro t
    rw [det_mul_column,det_mul_row]
    have he : (of fun i j => (t i).val^(b j)) =
        expNodeMatrix (fun i => Real.log (t i).val) b := by
      ext i j
      exact Real.rpow_def_of_pos (t i).property _
    rw [he]
    apply ne_of_gt
    exact mul_pos (prod_pos fun i _ => add_pos (Real.rpow_pos_of_pos (t i).property _)
        (Real.rpow_pos_of_pos (t i).property _))
      (mul_pos (prod_pos fun j _ => by nlinarith only [mul_pos (sub_pos.mpr (hb j))
        (show 0 < b j+a by linarith [hb j])])
        (det_expKernel_pos (fun i j h => Real.log_lt_log (t i).property (t.strictMono h)) b.strictMono))

/-- Varying the potential strength from zero fixes the orientation of every
minor. Thus the actual one-well eigenmodes retain strict total positivity
at all orders on independent spatial and spectral grids. -/
theorem wellPrimitive_det_pos {n : ℕ} (a : ℝ) (ha : 0 ≤ a) (b : Fin n ↪o ℝ)
    (hb : ∀ j, a < b j) (x : Fin n ↪o Ioi (0:ℝ)) :
    0 < (of fun i j => wellPrimitive a (b j) (x i).val).det := by
  let d (s : ℝ) := (of fun i j => wellPrimitive s (b j) (x i).val).det
  have hc : Continuous d := by
    apply Matrix.continuous_det.comp
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun s => (b j-s)*(x i).val^(b j+s)+(b j+s)*(x i).val^(b j-s)
    fun_prop (disch := exact (x i).property.ne')
  have hzero : 0 < d 0 := by
    have he : (of fun i j => wellPrimitive 0 (b j) (x i).val) =
        (of fun i j => (2*b j)*expNodeMatrix (fun i => Real.log (x i).val) b i j) := by
      ext i j
      simp only [of_apply,wellPrimitive,sub_zero,add_zero,expNodeMatrix,
        Real.rpow_def_of_pos (x i).property]
      ring
    dsimp only [d]
    rw [he,det_mul_row]
    exact mul_pos (prod_pos fun j _ => mul_pos zero_lt_two (ha.trans_lt (hb j)))
      (det_expKernel_pos (fun i j h => Real.log_lt_log (x i).property (x.strictMono h)) b.strictMono)
  by_contra! hh
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc' ha hc.continuousOn
    (show (0:ℝ) ∈ Icc (d a) (d 0) from ⟨hh,hzero.le⟩)
  exact wellPrimitive_det_ne s hs.1 b (fun j => hs.2.trans_lt (hb j)) x he

/-- Real exponential modes of the one-soliton Darboux transform. -/
def wellEigenMode (a b x : ℝ) := Real.exp (b*x)*(b-a*Real.tanh (a*x))

private theorem gauge_wellEigenMode (a b x : ℝ) :
    (Real.exp (a*x)+Real.exp (-(a*x)))*wellEigenMode a b x =
      wellPrimitive a b (Real.exp x) := by
  have hn := (add_pos (Real.exp_pos (a*x)) (Real.exp_pos (-(a*x)))).ne'
  simp only [wellPrimitive,wellEigenMode,Real.rpow_def_of_pos (Real.exp_pos x),Real.log_exp,
    Real.tanh_eq,show x*(b+a) = b*x+a*x by ring,show x*(b-a) = b*x+ -(a*x) by ring,
    Real.exp_add]
  field_simp [hn]
  ring

theorem wellEigenMode_minor_pos {n : ℕ} (l : ℝ) (x : Fin n ↪o ℝ)
    (b : Fin n ↪o Ioi (Real.exp l)) :
    0 < (of fun i j => wellEigenMode (Real.exp l) (b j).val (x i)).det := by
  let b' := OrderEmbedding.ofStrictMono (fun j => (b j).val) (fun _ _ h => b.strictMono h)
  let x' := OrderEmbedding.ofStrictMono (fun i => (⟨Real.exp (x i),Real.exp_pos _⟩ : Ioi (0:ℝ)))
    (fun _ _ h => Real.exp_strictMono (x.strictMono h))
  have h := wellPrimitive_det_pos (Real.exp l) (Real.exp_pos l).le b' (fun j => (b j).property) x'
  change 0 < (of fun i j => wellPrimitive (Real.exp l) (b j).val (Real.exp (x i))).det at h
  simp_rw [← gauge_wellEigenMode] at h
  rw [Matrix.det_mul_column] at h
  exact (mul_pos_iff_of_pos_left (prod_pos fun i _ => add_pos (Real.exp_pos _) (Real.exp_pos _))).mp h

/-- The spectral threshold for pointwise positivity is exact. At the endpoint
the pivot mode becomes a positive multiple of the reciprocal hyperbolic cosine. -/
theorem wellEigenMode_pos_iff (l b : ℝ) :
    (∀ x, 0 < wellEigenMode (Real.exp l) b x) ↔ Real.exp l ≤ b := by
  constructor
  · intro h
    have hlim : Tendsto (fun x => Real.exp l*Real.tanh (Real.exp l*x)) atTop (𝓝 (Real.exp l)) := by
      simpa only [mul_one] using (tendsto_tanh_atTop_one.comp
        (tendsto_id.const_mul_atTop (Real.exp_pos l))).const_mul (Real.exp l)
    refine le_of_tendsto hlim (Eventually.of_forall fun x => ?_)
    exact (sub_pos.mp ((mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (h x))).le
  · intro hb x
    apply mul_pos (Real.exp_pos _)
    apply sub_pos.mpr
    exact lt_of_lt_of_le (by simpa only [mul_one] using
      mul_lt_mul_of_pos_left (Real.tanh_lt_one (Real.exp l*x)) (Real.exp_pos l)) hb

theorem wellEigenMode_endpoint (l x : ℝ) :
    wellEigenMode (Real.exp l) (Real.exp l) x = Real.exp l / Real.cosh (Real.exp l*x) := by
  have h := gauge_wellEigenMode (Real.exp l) (Real.exp l) x
  simp only [wellPrimitive,sub_self,zero_mul,zero_add,Real.rpow_zero,mul_one] at h
  apply (eq_div_iff (Real.cosh_pos _).ne').mpr
  rw [Real.cosh_eq]
  linarith only [h,show wellEigenMode (Real.exp l) (Real.exp l) x *
    ((Real.exp (Real.exp l*x)+Real.exp (-(Real.exp l*x)))/2) =
    ((Real.exp (Real.exp l*x)+Real.exp (-(Real.exp l*x)))*wellEigenMode (Real.exp l) (Real.exp l) x)/2 by ring]

end
end GaloisForLFunctions.HTGeometry.Darboux
