import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Joint superlevels on finite grids

Layer sums turn the product of two rounded measurements into a positive
linear combination of weighted upper rectangles. The exact deficit measures
the failure of the joint survival function to be reciprocal in both
coordinates. A product of finite Pareto laws realizes equality.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Price of a joint exceedance at two independently chosen thresholds. -/
def upperRectangle {ι : Type*} (S : Finset ι) (f g w : ι → ℝ) (a b : ℝ) : ℝ :=
  a*b * ∑ i ∈ S.filter (fun i => a≤f i ∧ b≤g i), w i

/-- A step profile specified by its relative jumps at a finite list of
thresholds. Multiple jumps at one threshold add. -/
def layerValue (M : ℕ) (a u : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ r ∈ range M, if u r≤x then a r*u r else 0

/-- Product layer cake with an exact joint superlevel at every pair of
thresholds. It also holds for signed weights and signed increments. -/
theorem product_layers_eq_rectangles {ι : Type*} (S : Finset ι) (f g w : ι → ℝ)
    (M N : ℕ) (a u b v : ℕ → ℝ) :
    ∑ i ∈ S, layerValue M a u (f i)*layerValue N b v (g i)*w i =
      ∑ r ∈ range M, ∑ s ∈ range N, a r*b s*upperRectangle S f g w (u r) (v s) := by
  let F (i : ι) (r s : ℕ) :=
    if u r≤f i ∧ v s≤g i then (a r*b s)*(u r*v s)*w i else 0
  have expand (i : ι) : layerValue M a u (f i)*layerValue N b v (g i)*w i =
      ∑ r ∈ range M, ∑ s ∈ range N, F i r s := by
    unfold layerValue
    rw [sum_mul,sum_mul]
    apply sum_congr rfl
    intro r _
    rw [mul_sum,sum_mul]
    apply sum_congr rfl
    intro s _
    by_cases hu : u r≤f i <;> by_cases hv : v s≤g i <;>
      simp only [F,hu,hv,if_true,if_false,true_and,false_and,and_false,mul_zero,zero_mul]
    ring
  rw [sum_congr rfl (fun i _ => expand i),sum_comm]
  apply sum_congr rfl
  intro r _
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  rw [upperRectangle,←mul_assoc,mul_sum,sum_filter]

/-- Optimal upper-rectangle bound, with the whole deficit resolved by
threshold pair. -/
theorem upper_rectangle_deficit {ι : Type*} (S : Finset ι) (f g w : ι → ℝ)
    (M N : ℕ) (a u b v : ℕ → ℝ) (C : ℝ) :
    (∑ r ∈ range M, a r)*(∑ s ∈ range N, b s)*C-
      (∑ i ∈ S, layerValue M a u (f i)*layerValue N b v (g i)*w i) =
      ∑ r ∈ range M, ∑ s ∈ range N, a r*b s*(C-upperRectangle S f g w (u r) (v s)) := by
  rw [product_layers_eq_rectangles]
  simp only [mul_sub,sum_sub_distrib,←sum_mul,←mul_sum]

/-- With positive layer increments, equality holds exactly when every
rectangle has the same price. -/
theorem upper_rectangle_saturation {ι : Type*} (S : Finset ι) (f g w : ι → ℝ)
    (M N : ℕ) (a u b v : ℕ → ℝ) (C : ℝ)
    (ha : ∀ r<M, 0<a r) (hb : ∀ s<N, 0<b s)
    (hc : ∀ r<M, ∀ s<N, upperRectangle S f g w (u r) (v s)≤C) :
    (∑ i ∈ S, layerValue M a u (f i)*layerValue N b v (g i)*w i) =
        (∑ r ∈ range M, a r)*(∑ s ∈ range N, b s)*C ↔
      ∀ r<M, ∀ s<N, upperRectangle S f g w (u r) (v s)=C := by
  let d r s := a r*b s*(C-upperRectangle S f g w (u r) (v s))
  have pos r (hr : r∈range M) s (hs : s∈range N) : 0≤d r s :=
    mul_nonneg (mul_pos (ha r (mem_range.mp hr)) (hb s (mem_range.mp hs))).le
      (sub_nonneg.mpr (hc r (mem_range.mp hr) s (mem_range.mp hs)))
  have id := upper_rectangle_deficit S f g w M N a u b v C
  change _ = ∑ r ∈ range M, ∑ s ∈ range N, d r s at id
  constructor
  · intro he r hr s hs
    rw [he,sub_self] at id
    have lower := (single_le_sum (pos r (mem_range.mpr hr)) (mem_range.mpr hs)).trans
      (single_le_sum (fun r hr => sum_nonneg (pos r hr)) (mem_range.mpr hr))
    have hd := le_antisymm (lower.trans_eq id.symm) (pos r (mem_range.mpr hr) s (mem_range.mpr hs))
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left ((mul_pos (ha r hr) (hb s hs)).ne'))).symm
  · intro he
    have zero : (∑ r ∈ range M, ∑ s ∈ range N, d r s)=0 :=
      sum_eq_zero fun r hr => sum_eq_zero fun s hs => by simp [d,he r (mem_range.mp hr) s (mem_range.mp hs)]
    exact (sub_eq_zero.mp (id.trans zero)).symm

/-- Relative jumps that round a height down to a power of two. -/
def dyadicRelativeJump (r : ℕ) : ℝ := if r=0 then 1 else 1/2

private theorem dyadic_prefix (n : ℕ) :
    ∑ r ∈ range (n+1), dyadicRelativeJump r*(2:ℝ)^r = 2^n := by
  induction n with
  | zero => simp [dyadicRelativeJump]
  | succ n ih =>
    rw [sum_range_succ,ih,pow_succ]
    simp only [dyadicRelativeJump,Nat.succ_ne_zero,if_false]
    ring

theorem dyadic_relative_mass (n : ℕ) :
    ∑ r ∈ range (n+1), dyadicRelativeJump r = 1+(n:ℝ)/2 := by
  induction n with
  | zero => simp [dyadicRelativeJump]
  | succ n ih =>
    rw [sum_range_succ,ih]
    simp only [dyadicRelativeJump,Nat.succ_ne_zero,if_false,Nat.cast_succ]
    ring

/-- Value of the dyadic step profile at the top of a grid. -/
theorem dyadic_layer_full (n : ℕ) {x : ℝ} (hx : (2:ℝ)^n≤x) :
    layerValue (n+1) dyadicRelativeJump (fun r => (2:ℝ)^r) x = 2^n := by
  rw [←dyadic_prefix n]
  apply sum_congr rfl
  intro r hr
  exact if_pos ((pow_le_pow_right₀ (by norm_num : 1≤(2:ℝ)) (by simpa using mem_range.mp hr)).trans hx)

/-- The rounded observation lies between half the original reading and
the original reading itself throughout the covered range. -/
theorem dyadic_layer_comparison (n : ℕ) {x : ℝ} (hx : 1≤x) (hu : x<(2:ℝ)^(n+1)) :
    let y := layerValue (n+1) dyadicRelativeJump (fun r => (2:ℝ)^r) x
    y≤x ∧ x<2*y := by
  induction n with
  | zero =>
    rw [dyadic_layer_full 0 (by simpa using hx)]
    norm_num at hu ⊢
    exact ⟨hx,hu⟩
  | succ n ih =>
    by_cases h : x<(2:ℝ)^(n+1)
    · have step : layerValue (n+1+1) dyadicRelativeJump (fun r => (2:ℝ)^r) x =
          layerValue (n+1) dyadicRelativeJump (fun r => (2:ℝ)^r) x := by
        simp only [layerValue,sum_range_succ (n:=n+1),if_neg h.not_ge,add_zero]
      rw [step]
      exact ih h
    · rw [dyadic_layer_full (n+1) (le_of_not_gt h)]
      exact ⟨le_of_not_gt h,by simpa only [pow_succ (2:ℝ) (n+1),mul_comm (2:ℝ)] using hu⟩

private theorem dyadic_product_comparison (M N : ℕ) {x y w : ℝ}
    (hx : 1≤x) (hx' : x<(2:ℝ)^(M+1)) (hy : 1≤y) (hy' : y<(2:ℝ)^(N+1)) (hw : 0≤w) :
    x*y*w ≤ 4*(layerValue (M+1) dyadicRelativeJump (fun r => (2:ℝ)^r) x*
      layerValue (N+1) dyadicRelativeJump (fun r => (2:ℝ)^r) y*w) := by
  have hu := (dyadic_layer_comparison M hx hx').2
  have hv := (dyadic_layer_comparison N hy hy').2
  have e := mul_le_mul hu.le hv.le (by linarith only [hy]) (by linarith only [hx,hu])
  linarith only [mul_le_mul_of_nonneg_right e hw]

/-- An upper rectangle captures the unrounded product at cost
`(M+2)(N+2)`. The two observation ranges can have different lengths. -/
theorem exists_dyadic_product_rectangle {ι : Type*} (S : Finset ι) (f g w : ι → ℝ)
    (M N : ℕ) (h : ∀ i ∈ S, 1≤f i ∧ f i<(2:ℝ)^(M+1) ∧
      1≤g i ∧ g i<(2:ℝ)^(N+1) ∧ 0≤w i) :
    ∃ r≤M, ∃ s≤N, (∑ i ∈ S, f i*g i*w i) ≤
      ((M:ℝ)+2)*((N:ℝ)+2)*upperRectangle S f g w (2^r) (2^s) := by
  let J := range (M+1) ×ˢ range (N+1)
  let P (k : ℕ × ℕ) := upperRectangle S f g w (2^k.1) (2^k.2)
  have hJ : J.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩⟩
  obtain ⟨q,hq,hmax⟩ := J.exists_max_image P hJ
  obtain ⟨hq₁,hq₂⟩ := mem_product.mp hq
  refine ⟨q.1,Nat.le_of_lt_succ (mem_range.mp hq₁),q.2,Nat.le_of_lt_succ (mem_range.mp hq₂),?_⟩
  let u (j : ℕ) : ℝ := 2^j
  let F i := layerValue (M+1) dyadicRelativeJump u (f i)
  let G i := layerValue (N+1) dyadicRelativeJump u (g i)
  have point i (hi : i∈S) : f i*g i*w i ≤ 4*(F i*G i*w i) := by
    obtain ⟨hf,hf',hg,hg',hw⟩ := h i hi
    exact dyadic_product_comparison M N hf hf' hg hg' hw
  have hj (r : ℕ) : 0≤dyadicRelativeJump r := by unfold dyadicRelativeJump; split <;> norm_num
  have weight (r : ℕ) (hr : r∈range (M+1)) (s : ℕ) (hs : s∈range (N+1)) :
      dyadicRelativeJump r*dyadicRelativeJump s*P (r,s) ≤ dyadicRelativeJump r*dyadicRelativeJump s*P q :=
    mul_le_mul_of_nonneg_left (hmax _ (mem_product.mpr ⟨hr,hs⟩)) (mul_nonneg (hj r) (hj s))
  have grid := sum_le_sum (fun r hr => sum_le_sum (weight r hr))
  have total (r : ℕ) : (∑ s ∈ range (N+1), dyadicRelativeJump r*dyadicRelativeJump s*P q) =
      dyadicRelativeJump r*(1+(N:ℝ)/2)*P q := by rw [←sum_mul,←mul_sum,dyadic_relative_mass]
  rw [sum_congr rfl (fun r _ => total r),←sum_mul,←sum_mul,dyadic_relative_mass] at grid
  have cmp := sum_le_sum point
  rw [←mul_sum] at cmp
  have exact_grid := product_layers_eq_rectangles S f g w (M+1) (N+1)
    dyadicRelativeJump u dyadicRelativeJump u
  change (∑ i ∈ S, F i*G i*w i) =
    ∑ r ∈ range (M+1), ∑ s ∈ range (N+1), dyadicRelativeJump r*dyadicRelativeJump s*P (r,s) at exact_grid
  rw [exact_grid] at cmp
  change _ ≤ ((M:ℝ)+2)*((N:ℝ)+2)*P q
  linarith only [cmp,grid]

#print axioms exists_dyadic_product_rectangle

/-- Relative area of the occupied joint levels. A pair contributes only if
one sample reaches both thresholds. -/
def occupiedDyadicArea {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (M N : ℕ) : ℝ := by
  classical
  exact ∑ r ∈ range (M+1), ∑ s ∈ range (N+1),
    if ∃ i ∈ S, (2:ℝ)^r≤f i ∧ (2:ℝ)^s≤g i then dyadicRelativeJump r*dyadicRelativeJump s else 0

theorem occupiedDyadicArea_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (M N : ℕ) :
    occupiedDyadicArea S f g M N ≤ (1+(M:ℝ)/2)*(1+(N:ℝ)/2) := by
  classical
  unfold occupiedDyadicArea
  calc _ ≤ ∑ r ∈ range (M+1), ∑ s ∈ range (N+1), dyadicRelativeJump r*dyadicRelativeJump s := by
           refine sum_le_sum fun r _ => sum_le_sum fun s _ => ?_
           split_ifs
           · rfl
           have pos (j : ℕ) : 0≤dyadicRelativeJump j := by unfold dyadicRelativeJump; split <;> norm_num
           exact mul_nonneg (pos _) (pos _)
       _ = _ := by simp only [←mul_sum,←sum_mul,dyadic_relative_mass]

/-- Only occupied pairs enter the loss. Thus the whole moment is bounded
by the largest rectangle times the weighted area below the joint frontier. -/
theorem dyadic_rectangle_occupied_bound {ι : Type*} (S : Finset ι) (f g w : ι → ℝ) (M N : ℕ)
    (C : ℝ) (h : ∀ i ∈ S, 1≤f i ∧ f i<(2:ℝ)^(M+1) ∧
      1≤g i ∧ g i<(2:ℝ)^(N+1) ∧ 0≤w i)
    (hc : ∀ r≤M, ∀ s≤N, upperRectangle S f g w (2^r) (2^s) ≤ C) :
    (∑ i ∈ S, f i*g i*w i) ≤ 4*occupiedDyadicArea S f g M N*C := by
  classical
  let a := dyadicRelativeJump
  let u (r : ℕ) : ℝ := 2^r
  let F i := layerValue (M+1) a u (f i)
  let G i := layerValue (N+1) a u (g i)
  have major i (hi : i∈S) : f i*g i*w i ≤ 4*(F i*G i*w i) := by
    obtain ⟨hf,hf',hg,hg',hw⟩ := h i hi
    exact dyadic_product_comparison M N hf hf' hg hg' hw
  have cost r (hr : r∈range (M+1)) s (hs : s∈range (N+1)) :
      a r*a s*upperRectangle S f g w (u r) (u s) ≤
      (if ∃ i ∈ S, u r≤f i ∧ u s≤g i then a r*a s else 0)*C := by
    by_cases ho : ∃ i ∈ S, u r≤f i ∧ u s≤g i
    · rw [if_pos ho]
      have pos (n : ℕ) : 0≤a n := by dsimp only [a,dyadicRelativeJump]; split <;> norm_num
      exact mul_le_mul_of_nonneg_left (hc r (by simpa using mem_range.mp hr) s
        (by simpa using mem_range.mp hs)) (mul_nonneg (pos r) (pos s))
    · have empty : S.filter (fun i => u r≤f i ∧ u s≤g i)=∅ := eq_empty_iff_forall_notMem.mpr
        (fun i hi => ho ⟨i,(mem_filter.mp hi).1,(mem_filter.mp hi).2⟩)
      simp [upperRectangle,ho,empty]
  have bound := sum_le_sum (fun r hr => sum_le_sum (cost r hr))
  simp only [←sum_mul] at bound
  have cake := product_layers_eq_rectangles S f g w (M+1) (N+1) a u a u
  change (∑ i ∈ S, F i*G i*w i)=_ at cake
  have hm := sum_le_sum major
  rw [←mul_sum,cake] at hm
  change _ ≤ occupiedDyadicArea S f g M N*C at bound
  linarith only [hm,bound]

#print axioms dyadic_rectangle_occupied_bound

/-- Finite reciprocals, with the last atom absorbing the remaining tail. -/
def reciprocalTail (u : ℕ → ℝ) (K r : ℕ) : ℝ := if r≤K then (u r)⁻¹ else 0

def reciprocalAtom (u : ℕ → ℝ) (K r : ℕ) : ℝ :=
  reciprocalTail u K r - reciprocalTail u K (r+1)

private theorem tail_telescope (F : ℕ → ℝ) {r N : ℕ} (h : r≤N) :
    ∑ i ∈ Ico r N, (F i-F (i+1)) = F r-F N := by
  induction N,h using Nat.le_induction with
  | base => simp
  | succ N h ih => rw [sum_Ico_succ_top h,ih]; ring

/-- The product of truncated reciprocal laws saturates every rectangle
at once, for any two increasing positive grids. -/
theorem reciprocal_product_survival (u v : ℕ → ℝ) (K L r s : ℕ) (hr : r≤K) (hs : s≤L) :
    (∑ i ∈ Ico r (K+1), ∑ j ∈ Ico s (L+1), reciprocalAtom u K i*reciprocalAtom v L j) =
      (u r)⁻¹*(v s)⁻¹ := by
  have mass (f : ℕ → ℝ) (k j : ℕ) (hj : j≤k) :
      ∑ i ∈ Ico j (k+1), reciprocalAtom f k i = (f j)⁻¹ := by
    unfold reciprocalAtom
    rw [tail_telescope (reciprocalTail f k) (by omega)]
    simp [reciprocalTail,hj]
  simp only [←mul_sum,←sum_mul,mass u K r hr,mass v L s hs]

/-- Flat rectangle prices determine every point mass. Taking the mixed
difference of the reciprocal tail forces independence, including at the
upper edges of the finite grid. -/
theorem reciprocal_rectangle_rigidity (u v : ℕ → ℝ) (K L : ℕ) (A : ℕ → ℕ → ℝ) (C : ℝ)
    (ht : ∀ r≤K+1, ∀ s≤L+1,
      (∑ i ∈ Ico r (K+1), ∑ j ∈ Ico s (L+1), A i j)=
        C*reciprocalTail u K r*reciprocalTail v L s) :
    ∀ r≤K, ∀ s≤L, A r s=C*reciprocalAtom u K r*reciprocalAtom v L s := by
  let T r s := ∑ i ∈ Ico r (K+1), ∑ j ∈ Ico s (L+1), A i j
  have row r (hr : r≤K) s : T r s-T (r+1) s=∑ j ∈ Ico s (L+1), A r j := by
    dsimp only [T]
    rw [sum_eq_sum_Ico_succ_bot (by omega : r<K+1)]
    ring
  intro r hr s hs
  have one : (∑ j ∈ Ico s (L+1), A r j)-(∑ j ∈ Ico (s+1) (L+1), A r j)=A r s := by
    rw [sum_eq_sum_Ico_succ_bot (by omega : s<L+1)]
    ring
  rw [←row r hr s,←row r hr (s+1)] at one
  dsimp only [T] at one
  rw [ht r (by omega) s (by omega),ht (r+1) (by omega) s (by omega),
    ht r (by omega) (s+1) (by omega),ht (r+1) (by omega) (s+1) (by omega)] at one
  rw [←one]
  unfold reciprocalAtom
  ring

#print axioms upper_rectangle_deficit
#print axioms upper_rectangle_saturation
#print axioms reciprocal_product_survival
#print axioms reciprocal_rectangle_rigidity
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
