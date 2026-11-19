import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.LogCellGaussianGridEntropy
import GaloisForLFunctions.HTGeometry.ReflectedExponentialFisher
import Mathlib.Analysis.Subadditive

/-!
# Strict subadditivity and limiting entropy of the Gaussian grid

At mesh scale the density is a sum of translates of a single Gaussian.
Concatenating two grids increases the density on both parts by a strictly
positive amount. Integrated negative log density is strictly subadditive.
The forward divergences therefore have a limit strictly below every finite
grid cost and bounded below by the positive Fourier-observation cost.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.GaussianGrid
open MeasureTheory ProbabilityTheory InformationTheory HTGeometry Filter Set Finset
open scoped ENNReal Topology

private def atom (j : ℕ) := gaussianPDFReal ((j:ℝ)+1/2) (1/12)

def strip (n : ℕ) (x : ℝ) := ∑ j ∈ range n, atom j x

private theorem atom_pos (j : ℕ) (x : ℝ) : 0 < atom j x := gaussianPDFReal_pos _ _ _ (by norm_num)

private theorem strip_pos {n : ℕ} (hn : 0 < n) (x : ℝ) : 0 < strip n x :=
  Finset.sum_pos' (fun j _ => (atom_pos j x).le) ⟨0,mem_range.mpr hn,atom_pos 0 x⟩

private theorem strip_cont (n : ℕ) : Continuous (strip n) := by
  unfold strip
  unfold atom gaussianPDFReal
  fun_prop

/-- Density on a juxtaposed grid is the sum of the two translated densities. -/
theorem strip_add (n m : ℕ) (x : ℝ) : strip (n+m) x = strip n x+strip m (x-n) := by
  simp only [strip,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [atom,atom,gaussianPDFReal_sub]
  push_cast
  congr 1
  ring

private theorem scaled_atom (n j : ℕ) (x : ℝ) :
    atom j (((n:ℝ)+1)*x) = width n *
      gaussianPDFReal (center n j) (Real.toNNReal ((width n)^2/12)) x := by
  have hw : 0 < width n := by unfold width; positivity
  have he := gaussianPDFReal_inv_mul (μ := (j:ℝ)+1/2) (v := (1/12:ℝ≥0)) hw.ne' x
  have hv : (⟨(width n)^2,sq_nonneg _⟩ : ℝ≥0)*(1/12) = Real.toNNReal ((width n)^2/12) := by
    ext
    simp [Real.coe_toNNReal _ (by positivity : 0 ≤ width n^2/12)]
  have hinv : (width n)⁻¹=(n:ℝ)+1 := by simp [width]
  simpa only [atom,center,hinv,abs_of_pos hw,hv,mul_comm (width n) ((j:ℝ)+1/2)] using he

/-- The physical mixture has a continuous strictly positive density whose
profile in mesh units has fixed Gaussian width. -/
theorem mixture_strip (n : ℕ) : mixture n =
    volume.withDensity fun x => ENNReal.ofReal (strip (n+1) (((n:ℝ)+1)*x)) := by
  let g (j : ℕ) := gaussianPDF (center n j) (Real.toNNReal (width n^2/12))
  have hg (N : ℕ) : Measurable (fun x => ∑ j ∈ range N, g j x) := by
    dsimp only [g]; fun_prop
  have hw : 0 < width n := by unfold width; positivity
  have hv : Real.toNNReal (width n^2/12) ≠ 0 := (Real.toNNReal_pos.mpr (by positivity)).ne'
  have hd (N : ℕ) : volume.withDensity (fun x => ∑ j ∈ range N, g j x) =
      ∑ j ∈ range N, component n j := by
    induction N with
    | zero => simp
    | succ N ih =>
      simp only [sum_range_succ]
      rw [show (fun x => (∑ j ∈ range N, g j x)+g N x) = (fun x => ∑ j ∈ range N, g j x)+g N from rfl,
        withDensity_add_left (hg N),ih,component,gaussianReal_of_var_ne_zero _ hv]
  have hfun : (fun x => ENNReal.ofReal (strip (n+1) (((n:ℝ)+1)*x))) =
      ENNReal.ofReal (width n) • (fun x => ∑ j ∈ range (n+1), g j x) := by
    funext x
    rw [strip,ENNReal.ofReal_sum_of_nonneg (fun j _ => (atom_pos j _).le)]
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,scaled_atom,ENNReal.ofReal_mul hw.le]
    rfl
  rw [hfun,withDensity_smul _ (hg _),hd,mixture]

/-- Extensive entropy of a strip measured in units of one subcell. -/
def stripCost (n : ℕ) := ∫ x in (0:ℝ)..n, -Real.log (strip n x)

private theorem source_eq : (unitIntervalProbabilityMeasure : Measure ℝ) = positionLaw 0 0 := by
  simp [unitIntervalProbabilityMeasure,positionLaw,ProbabilityTheory.cond,Real.volume_Ioc]

/-- Exact finite forward KL in the natural strip coordinates, including every
boundary cell. -/
theorem grid_cost (n : ℕ) :
    let D := klDiv (unitIntervalProbabilityMeasure : Measure ℝ) (mixture n)
    D ≠ ⊤ ∧ D.toReal=stripCost (n+1)/((n:ℝ)+1) := by
  let g := fun x : ℝ => strip (n+1) (((n:ℝ)+1)*x)
  have hc : Continuous g := (strip_cont _).comp (continuous_const.mul continuous_id)
  have hp (x) : 0 < g x := strip_pos (Nat.succ_pos _) _
  have hm : Measurable (fun x => ENNReal.ofReal (g x)) := by fun_prop
  have ha : mixture n ≪ volume := by rw [mixture_strip]; exact withDensity_absolutelyContinuous _ _
  have hb : volume ≪ mixture n := by
    rw [mixture_strip]
    exact ReflectedExponentialFamily.absolutelyContinuous_withDensity_of_pos hm
      (fun x => (ENNReal.ofReal_pos.mpr (hp x)).ne')
  have hd : (mixture n).rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (g x) := by
    rw [mixture_strip]
    exact Measure.rnDeriv_withDensity _ hm
  have H := position_kl_from_density 0 0 hc hp ha hb hd
  dsimp only
  rw [source_eq]
  refine ⟨H.1,?_⟩
  have hn : ((n:ℝ)+1) ≠ 0 := by positivity
  have he := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (1:ℝ))
    (fun x => -Real.log (strip (n+1) x)) hn
  simp only [g,Real.exp_zero,zero_add,zero_sub,div_one,he,mul_zero,mul_one,smul_eq_mul,
    stripCost,Nat.cast_add,Nat.cast_one] at H ⊢
  rw [H.2]
  ring

private theorem score_cont {n : ℕ} (h : 0 < n) : Continuous (fun x => -Real.log (strip n x)) :=
  ((strip_cont n).log (fun x => (strip_pos h x).ne')).neg

private theorem strict_interval {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x < g x) :
    (∫ x in a..b, f x) < ∫ x in a..b, g x := by
  have hp := intervalIntegral.intervalIntegral_pos_of_pos ((hg.sub hf).intervalIntegrable _ _)
    (fun x => sub_pos.mpr (h x)) hab
  rwa [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _),sub_pos] at hp

/-- Both sides of a joined strip benefit strictly from the overlapping Gaussian tails. -/
theorem strip_strict_subadditive (n m : ℕ) (hn : 0<n) (hm : 0 < m) :
    stripCost (n+m) < stripCost n+stripCost m := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hnm := score_cont (Nat.add_pos_left hn m)
  have hl := strict_interval hn' hnm (score_cont hn) fun x => neg_lt_neg
    (Real.log_lt_log (strip_pos hn x) (by rw [strip_add]; exact lt_add_of_pos_right _ (strip_pos hm _)))
  have hr := strict_interval (lt_add_of_pos_right (n:ℝ) hm') hnm
    ((score_cont hm).comp (continuous_id.sub continuous_const)) fun x => neg_lt_neg
      (Real.log_lt_log (strip_pos hm (x-n)) (by rw [strip_add]; exact lt_add_of_pos_left _ (strip_pos hn _)))
  have trans := intervalIntegral.integral_comp_sub_right (a := (n:ℝ)) (b := (n:ℝ)+m)
    (fun x => -Real.log (strip m x)) (n:ℝ)
  simp only [sub_self,add_sub_cancel_left] at trans
  unfold stripCost
  rw [Nat.cast_add,← intervalIntegral.integral_add_adjacent_intervals
    (hnm.intervalIntegrable 0 (n:ℝ)) (hnm.intervalIntegrable (n:ℝ) ((n:ℝ)+m))]
  exact add_lt_add hl (hr.trans_eq trans)

private theorem subadd : Subadditive stripCost := by
  intro n m
  cases n with
  | zero => simp [stripCost]
  | succ n =>
    cases m with
    | zero => simp [stripCost]
    | succ m => exact (strip_strict_subadditive _ _ (Nat.succ_pos _) (Nat.succ_pos _)).le

private theorem lower : BddBelow (Set.range fun n => stripCost n/n) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.cast_succ,← (grid_cost n).2] using
      (ENNReal.toReal_nonneg (a := klDiv (unitIntervalProbabilityMeasure : Measure ℝ) (mixture n)))

/-- The forward KL has a strictly positive limit, and no finite grid attains
it. Thus arbitrarily fine Gaussian fits retain a definite information loss. -/
theorem forward_entropy_limit : ∃ L : ℝ, aliasCost ≤ L ∧
    Tendsto (fun n => (klDiv (unitIntervalProbabilityMeasure : Measure ℝ) (mixture n)).toReal)
      atTop (𝓝 L) ∧
    ∀ n, L < (klDiv (unitIntervalProbabilityMeasure : Measure ℝ) (mixture n)).toReal := by
  have ht := (subadd.tendsto_lim lower).comp (tendsto_add_atTop_nat 1)
  have h : Tendsto (fun n => (klDiv (unitIntervalProbabilityMeasure : Measure ℝ) (mixture n)).toReal)
      atTop (𝓝 subadd.lim) := by simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,← (grid_cost _).2] using ht
  refine ⟨subadd.lim,le_of_tendsto_of_tendsto' tendsto_const_nhds h (fun n => ?_),h,?_⟩
  · have he := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (grid_cost n).1).mpr (mesh_entropy_gap n)
    simpa only [ENNReal.toReal_ofReal aliasCost_pos.le] using he
  · intro n
    let N := n+1
    have hN : 0<N := Nat.succ_pos n
    have hQ : 0<(N:ℝ) := by exact_mod_cast hN
    have he := strip_strict_subadditive N N hN hN
    have hL := subadd.lim_le_div lower (Nat.add_pos_left hN N).ne'
    rw [(grid_cost n).2]
    change subadd.lim < stripCost N/(N:ℝ)
    apply hL.trans_lt
    rw [Nat.cast_add,div_lt_div_iff₀ (add_pos hQ hQ) hQ]
    linear_combination (N:ℝ)*he

#print axioms strip_add
#print axioms mixture_strip
#print axioms grid_cost
#print axioms strip_strict_subadditive
#print axioms forward_entropy_limit
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.GaussianGrid
