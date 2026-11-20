import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Left and right widths of a discrete superlevel component

On each side of an observation site, a level reaches depth i precisely
when it lies below the running minimum through i. This gives a discrete
form of the product of exit distances in Guo, Wang and Yuan, (3.53)–(3.58).
The radial upper bound is sharp exactly for symmetric decreasing profiles.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.ArithmeticPositiveDuality.ComponentWidths

/-- Height of the highest level reaching the indicated depth along one ray. -/
def depthHeight (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | k+1 => min (depthHeight f k) (f (k+1))

theorem le_depthHeight_iff (f : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    x≤depthHeight f n ↔ ∀ i≤n, x≤f i := by
  induction n with
  | zero => simp [depthHeight]
  | succ n ih =>
    rw [depthHeight,le_min_iff,ih]
    constructor
    · rintro ⟨h,h'⟩ i hi
      rcases hi.eq_or_lt with rfl | hl
      · exact h'
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega),h _ le_rfl⟩

private theorem depth_le (f : ℕ → ℝ) (i : ℕ) : depthHeight f i ≤ f i :=
  ((le_depthHeight_iff f _ i).mp le_rfl) _ le_rfl

private theorem depth_antitone (f : ℕ → ℝ) : Antitone (depthHeight f) :=
  antitone_nat_of_succ_le fun i => min_le_left _ _

/-- Common level at which both directed depths are still inside the component. -/
def commonHeight (f g : ℕ → ℝ) (i j : ℕ) : ℝ := min (depthHeight f i) (depthHeight g j)

/-- Integrated product of the truncated left and right component widths. -/
def pairedWidth (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, commonHeight f g i j

/-- Radial price at the original heights, before taking any running minimum. -/
def radialPrice (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, (2*(j:ℝ)+1)*(f j+g j)

private theorem depth_upper_perturbation {f g : ℕ → ℝ} {δ : ℝ} {k : ℕ}
    (h : ∀ i≤k, g i ≤ f i+δ) : depthHeight g k ≤ depthHeight f k+δ := by
  apply sub_le_iff_le_add.mp
  apply (le_depthHeight_iff f _ k).mpr
  intro i hi
  have hl := ((le_depthHeight_iff g _ k).mp le_rfl) i hi
  linarith only [hl,h i hi]

/-- Full price perturbations are paid at most once per ordered pair of
depths. A common translation of all heights attains the coefficient n². -/
theorem pairedWidth_upper_perturbation {f g F G : ℕ → ℝ} (n : ℕ) (δ : ℝ)
    (hl : ∀ i<n, F i≤f i+δ) (hr : ∀ j<n, G j≤g j+δ) :
    pairedWidth F G n ≤ pairedWidth f g n+(n:ℝ)^2*δ := by
  have he (i j : ℕ) (hi : i<n) (hj : j<n) : commonHeight F G i j≤commonHeight f g i j+δ := by
    apply sub_le_iff_le_add.mp
    apply le_min
    · have hp := depth_upper_perturbation (f:=f) (g:=F) (k:=i) (fun k hk => hl k (hk.trans_lt hi))
      have h : commonHeight F G i j≤depthHeight F i := min_le_left _ _
      linarith only [h,hp]
    · have hp := depth_upper_perturbation (f:=g) (g:=G) (k:=j) (fun k hk => hr k (hk.trans_lt hj))
      have h : commonHeight F G i j≤depthHeight G j := min_le_right _ _
      linarith only [h,hp]
  apply (sum_le_sum (s:=range n) (fun i hi => sum_le_sum (s:=range n)
    (fun j hj => he i j (mem_range.mp hi) (mem_range.mp hj)))).trans_eq
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,pairedWidth]
  ring

theorem pairedWidth_shift (f g : ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    pairedWidth (fun i => f i+δ) (fun j => g j+δ) n=pairedWidth f g n+(n:ℝ)^2*δ := by
  apply le_antisymm (pairedWidth_upper_perturbation n δ (fun _ _ => le_rfl) (fun _ _ => le_rfl))
  have hl := pairedWidth_upper_perturbation (f:=fun i => f i+δ) (g:=fun j => g j+δ)
    (F:=f) (G:=g) n (-δ) (by intro i _; linarith only) (by intro j _; linarith only)
  linarith only [hl]

private theorem width_succ (f g : ℕ → ℝ) (n : ℕ) :
    pairedWidth f g (n+1)=pairedWidth f g n +
      (∑ j ∈ range n, commonHeight f g n j)+(∑ i ∈ range n, commonHeight f g i n)+
      commonHeight f g n n := by
  unfold pairedWidth
  rw [sum_range_succ]
  simp_rw [sum_range_succ (f:=fun j => commonHeight f g _ j)]
  rw [sum_add_distrib]
  ring

private theorem diagonal_nonneg (f g : ℕ → ℝ) (j : ℕ) :
    0≤f j+g j-2*commonHeight f g j j := by
  have hl := (min_le_left (depthHeight f j) (depthHeight g j)).trans (depth_le f j)
  have hr := (min_le_right (depthHeight f j) (depthHeight g j)).trans (depth_le g j)
  dsimp only [commonHeight]
  linarith only [hl,hr]

/-- Each diagonal deficit is forced. In particular differences between the
two raw heights and losses at nearer bottlenecks both make the bound strict. -/
theorem diagonal_deficit_bound (f g : ℕ → ℝ) (n : ℕ) :
    2*pairedWidth f g n + ∑ j ∈ range n, (f j+g j-2*commonHeight f g j j) ≤ radialPrice f g n := by
  induction n with
  | zero => simp [pairedWidth,radialPrice]
  | succ n ih =>
    have hl : (∑ j ∈ range n, commonHeight f g n j) ≤ n*f n := by
      simpa only [commonHeight,sum_const,card_range,nsmul_eq_mul] using
        (sum_le_sum (s:=range n) (fun j _ => (min_le_left (depthHeight f n) (depthHeight g j)).trans (depth_le f n)))
    have hr : (∑ i ∈ range n, commonHeight f g i n) ≤ n*g n := by
      simpa only [commonHeight,sum_const,card_range,nsmul_eq_mul] using
        (sum_le_sum (s:=range n) (fun i _ => (min_le_right (depthHeight f i) (depthHeight g n)).trans (depth_le g n)))
    rw [width_succ,sum_range_succ]
    change _ ≤ (∑ j ∈ range (n+1), (2*(j:ℝ)+1)*(f j+g j))
    rw [sum_range_succ]
    change 2*_+_ ≤ radialPrice f g n+_
    linarith only [ih,hl,hr]

theorem twice_pairedWidth_le_radialPrice (f g : ℕ → ℝ) (n : ℕ) :
    2*pairedWidth f g n ≤ radialPrice f g n :=
  (le_add_of_nonneg_right (sum_nonneg fun j _ => diagonal_nonneg f g j)).trans
    (diagonal_deficit_bound f g n)

private theorem width_succ_saturated {f g : ℕ → ℝ} {n : ℕ}
    (hl : commonHeight f g n n=f n) (hr : commonHeight f g n n=g n) :
    2*pairedWidth f g (n+1) = 2*pairedWidth f g n + (2*(n:ℝ)+1)*(f n+g n) := by
  have left (j : ℕ) (hj : j ∈ range n) : commonHeight f g n j=f n := by
    apply le_antisymm ((min_le_left _ _).trans (depth_le f n))
    rw [←hl]
    exact min_le_min_left _ (depth_antitone g (mem_range.mp hj).le)
  have right (i : ℕ) (hi : i ∈ range n) : commonHeight f g i n=g n := by
    apply le_antisymm ((min_le_right _ _).trans (depth_le g n))
    rw [←hr]
    exact min_le_min_right _ (depth_antitone f (mem_range.mp hi).le)
  rw [width_succ,sum_congr rfl left,sum_congr rfl right]
  simp only [sum_const,card_range,nsmul_eq_mul]
  linarith only [hl,hr]

/-- Equality holds precisely when the two rays agree through the last
observed depth and their common profile is nonincreasing. -/
theorem pairedWidth_extremizers (f g : ℕ → ℝ) (n : ℕ) :
    2*pairedWidth f g n=radialPrice f g n ↔
      (∀ j<n, f j=g j) ∧ ∀ i j, i≤j → j<n → f j≤f i := by
  have diag (he : 2*pairedWidth f g n=radialPrice f g n) (j : ℕ) (hj : j<n) :
      commonHeight f g j j=f j ∧ commonHeight f g j j=g j := by
    have hb := diagonal_deficit_bound f g n
    rw [←he] at hb
    have hz := le_antisymm ((add_le_iff_nonpos_right _).mp hb)
      (sum_nonneg fun i _ => diagonal_nonneg f g i)
    have h := (sum_eq_zero_iff_of_nonneg (fun i _ => diagonal_nonneg f g i)).mp hz j (mem_range.mpr hj)
    have hl : commonHeight f g j j≤f j := (min_le_left _ _).trans (depth_le f j)
    have hr : commonHeight f g j j≤g j := (min_le_right _ _).trans (depth_le g j)
    constructor <;> linarith only [h,hl,hr]
  constructor
  · intro he
    refine ⟨fun j hj => (diag he j hj).1.symm.trans (diag he j hj).2,?_⟩
    intro i j hij hj
    rw [←(diag he j hj).1]
    exact ((min_le_left _ _).trans (depth_antitone f hij)).trans (depth_le f i)
  · rintro ⟨hfg,hm⟩
    have dsat (j : ℕ) (hj : j<n) : commonHeight f g j j=f j ∧ commonHeight f g j j=g j := by
      have hl : depthHeight f j=f j := le_antisymm (depth_le f j)
        ((le_depthHeight_iff f _ j).mpr (fun i hi => hm i j hi hj))
      have hr : depthHeight g j=f j := le_antisymm ((depth_le g j).trans_eq (hfg j hj).symm)
        ((le_depthHeight_iff g _ j).mpr (fun i hi => (hm i j hi hj).trans_eq (hfg i (hi.trans_lt hj))))
      simp only [commonHeight,hl,hr,min_self,hfg j hj,and_self]
    have step (k : ℕ) (hk : k≤n) : 2*pairedWidth f g k=radialPrice f g k := by
      induction k with
      | zero => simp [pairedWidth,radialPrice]
      | succ k ih =>
        obtain ⟨hl,hr⟩ := dsat k (by omega)
        rw [width_succ_saturated hl hr,ih (by omega),radialPrice,radialPrice,sum_range_succ]
    exact step n le_rfl

/-- Contributions at level τ are the numbers of depths reached along each ray. -/
def levelWidth (f : ℕ → ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  ∑ i ∈ range n, (Set.Ioc 0 (depthHeight f i)).indicator (fun _ => (1:ℝ)) τ

private theorem level_atom_product (a b τ : ℝ) :
    (Set.Ioc 0 a).indicator (fun _ => (1:ℝ)) τ*(Set.Ioc 0 b).indicator (fun _ => (1:ℝ)) τ =
      (Set.Ioc 0 (min a b)).indicator (fun _ => (1:ℝ)) τ := by
  simp only [Set.indicator_apply,Set.mem_Ioc,le_min_iff]
  split_ifs <;> simp_all

/-- Exact finite layer-cake identity for the product of component widths.
Both rays may have arbitrary oscillations in their original heights. -/
theorem integral_levelWidth_product (f g : ℕ → ℝ) (n : ℕ)
    (hf : ∀ j<n, 0≤f j) (hg : ∀ j<n, 0≤g j) :
    (∫ τ, levelWidth f n τ*levelWidth g n τ)=pairedWidth f g n := by
  let K := fun (i j : ℕ) => (Set.Ioc 0 (commonHeight f g i j)).indicator (fun _ => (1:ℝ))
  have hI (i j : ℕ) : Integrable (K i j) :=
    (integrableOn_const (by simp [Real.volume_Ioc])).integrable_indicator measurableSet_Ioc
  have he (τ : ℝ) : levelWidth f n τ*levelWidth g n τ =
      ∑ i ∈ range n, ∑ j ∈ range n, K i j τ := by
    simp only [levelWidth,Finset.sum_mul,Finset.mul_sum,level_atom_product,K,commonHeight]
    exact sum_comm
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j)]
  apply sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  apply sum_congr rfl
  intro j hj
  have hp : 0≤commonHeight f g i j := le_min
    ((le_depthHeight_iff f 0 i).mpr fun k hk => hf k (hk.trans_lt (mem_range.mp hi)))
    ((le_depthHeight_iff g 0 j).mpr fun k hk => hg k (hk.trans_lt (mem_range.mp hj)))
  simp [K,integral_indicator measurableSet_Ioc,Real.volume_Ioc,Measure.real,ENNReal.toReal_ofReal hp]

private theorem integrable_levelWidth_product (f g : ℕ → ℝ) (n : ℕ) :
    Integrable (fun τ => levelWidth f n τ*levelWidth g n τ) := by
  simp only [levelWidth,Finset.sum_mul,Finset.mul_sum,level_atom_product]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (integrableOn_const (by simp [Real.volume_Ioc])).integrable_indicator measurableSet_Ioc))

private theorem depth_idempotent (f : ℕ → ℝ) (i : ℕ) : depthHeight (depthHeight f) i=depthHeight f i :=
  le_antisymm (depth_le _ i) ((le_depthHeight_iff _ _ i).mpr (fun _ hj => depth_antitone f hj))

private theorem self_width (f : ℕ → ℝ) (n : ℕ) :
    pairedWidth f f n=∑ i ∈ range n, (2*(i:ℝ)+1)*depthHeight f i := by
  have hs := (pairedWidth_extremizers (depthHeight f) (depthHeight f) n).mpr
    ⟨fun _ _ => rfl,fun _ _ h _ => depth_antitone f h⟩
  simp only [pairedWidth,commonHeight,depth_idempotent,radialPrice,←two_mul] at hs
  have he (i : ℕ) : (2*(i:ℝ)+1)*(2*depthHeight f i)=2*((2*(i:ℝ)+1)*depthHeight f i) := by ring
  simp_rw [he] at hs
  rw [←mul_sum] at hs
  exact mul_left_cancel₀ (by norm_num : (2:ℝ)≠0) hs

/-- The loss in the radial bound has two exact nonnegative parts. One
measures height hidden behind nearer minima. The other is the squared
difference of the left and right exit counts integrated over all levels. -/
theorem radial_loss_decomposition (f g : ℕ → ℝ) (n : ℕ)
    (hf : ∀ j<n, 0≤f j) (hg : ∀ j<n, 0≤g j) :
    radialPrice f g n-2*pairedWidth f g n =
      (∫ τ, (levelWidth f n τ-levelWidth g n τ)^2)+
      ∑ j ∈ range n, (2*(j:ℝ)+1)*((f j-depthHeight f j)+(g j-depthHeight g j)) := by
  have hi := integrable_levelWidth_product f g n
  have hdiag : Integrable (fun τ => levelWidth f n τ*levelWidth f n τ + levelWidth g n τ*levelWidth g n τ) :=
    (integrable_levelWidth_product f f n).add (integrable_levelWidth_product g g n)
  have he (x : ℝ) : (levelWidth f n x-levelWidth g n x)^2 =
      (levelWidth f n x*levelWidth f n x+levelWidth g n x*levelWidth g n x)-
      2*(levelWidth f n x*levelWidth g n x) := by ring
  simp_rw [he]
  rw [integral_sub hdiag (hi.const_mul 2),integral_add (integrable_levelWidth_product f f n) (integrable_levelWidth_product g g n),
    integral_const_mul,integral_levelWidth_product f f n hf hf,integral_levelWidth_product g g n hg hg,
    integral_levelWidth_product f g n hf hg,self_width,self_width,radialPrice]
  have h (j : ℕ) : (2*(j:ℝ)+1)*(f j+g j) =
      (2*(j:ℝ)+1)*depthHeight f j+(2*(j:ℝ)+1)*depthHeight g j+
      (2*(j:ℝ)+1)*((f j-depthHeight f j)+(g j-depthHeight g j)) := by ring
  simp_rw [h]
  rw [sum_add_distrib,sum_add_distrib]
  ring

end GaloisForLFunctions.ArithmeticPositiveDuality.ComponentWidths
