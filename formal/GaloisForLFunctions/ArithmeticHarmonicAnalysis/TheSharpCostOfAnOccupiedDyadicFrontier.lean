import GaloisForLFunctions.ArithmeticHarmonicAnalysis.WeightedUpperRectanglesOnFiniteGrids
import Mathlib.Analysis.Real.Sqrt

/-!
# Sharp rectangle prices on a prescribed occupied frontier

A lower set of joint levels need not be a rectangle. Prescribing a
geometric survival function on that set gives nonnegative masses on
every such shape exactly when the two continuation ratios sum to at
most one. The dyadic pair lies at equality. Its extremizer has constant
price on every occupied rectangle and zero price everywhere else.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- A finite lower set of pairs of threshold indices. -/
def IsLowerFrontier (A : Finset (ℕ × ℕ)) : Prop :=
  ∀ ⦃i j r s : ℕ⦄, (i,j) ∈ A → r ≤ i → s ≤ j → (r,s) ∈ A

/-- Geometric survival mass, terminated on leaving the frontier. -/
def frontierTail (A : Finset (ℕ × ℕ)) (a b : ℝ) (i j : ℕ) : ℝ :=
  if (i,j) ∈ A then a^i*b^j else 0

/-- Two-dimensional inclusion-exclusion recovers each atom from survival. -/
def frontierAtom (A : Finset (ℕ × ℕ)) (a b : ℝ) (i j : ℕ) : ℝ :=
  frontierTail A a b i j-frontierTail A a b (i+1) j-
    frontierTail A a b i (j+1)+frontierTail A a b (i+1) (j+1)

private theorem tail_nonneg (A : Finset (ℕ × ℕ)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i j : ℕ) :
    0 ≤ frontierTail A a b i j := by
  unfold frontierTail
  split <;> positivity

/-- The only dangerous corner has both immediate successors and lacks
their common successor. Its loss is exactly 1-a-b times the parent mass. -/
theorem frontierAtom_nonneg {A : Finset (ℕ × ℕ)} (hA : IsLowerFrontier A)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a+b ≤ 1) (i j : ℕ) :
    0 ≤ frontierAtom A a b i j := by
  let F := frontierTail A a b
  have hu : F (i+1) j ≤ a*F i j := by
    by_cases hi : (i+1,j) ∈ A
    · have parent := hA hi (Nat.le_succ i) (le_refl j)
      simp only [F,frontierTail,if_pos hi,if_pos parent,pow_succ]
      exact le_of_eq (by ring)
    · simpa only [F,frontierTail,if_neg hi] using
        (mul_nonneg ha (tail_nonneg A ha hb i j))
  have hv : F i (j+1) ≤ b*F i j := by
    by_cases hj : (i,j+1) ∈ A
    · have parent := hA hj (le_refl i) (Nat.le_succ j)
      simp only [F,frontierTail,if_pos hj,if_pos parent,pow_succ]
      exact le_of_eq (by ring)
    · simpa only [F,frontierTail,if_neg hj] using
        (mul_nonneg hb (tail_nonneg A ha hb i j))
  change 0 ≤ F i j-F (i+1) j-F i (j+1)+F (i+1) (j+1)
  have budget := mul_nonneg (sub_nonneg.mpr h) (tail_nonneg A ha hb i j)
  change 0 ≤ (1-(a+b))*F i j at budget
  linarith only [hu,hv,budget,show 0 ≤ F (i+1) (j+1) from tail_nonneg A ha hb _ _]

private def threeCellCorner : Finset (ℕ × ℕ) := {(0,0),(1,0),(0,1)}

private theorem mem_threeCellCorner (i j : ℕ) : (i,j) ∈ threeCellCorner ↔ i+j ≤ 1 := by
  simp only [threeCellCorner,mem_insert,mem_singleton,Prod.mk.injEq]
  omega

/-- Exact admissible region for geometric survival laws on all finite
joint frontiers. A three-cell corner detects every violation. -/
theorem frontier_nonneg_for_all_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∀ A : Finset (ℕ × ℕ), IsLowerFrontier A → ∀ i j, 0 ≤ frontierAtom A a b i j) ↔ a+b ≤ 1 := by
  constructor
  · intro all
    have lower : IsLowerFrontier threeCellCorner := by
      intro i j r s h hr hs
      exact (mem_threeCellCorner r s).mpr (by have := (mem_threeCellCorner i j).mp h; omega)
    have origin := all threeCellCorner lower 0 0
    simp [frontierAtom,frontierTail,mem_threeCellCorner] at origin
    linarith only [origin]
  · exact fun h A hA => frontierAtom_nonneg hA ha hb h

/-- The joint survival function equals the product of its two margins on
the frontier and vanishes on the missing threshold pairs. -/
theorem frontier_survival_from_margins (A : Finset (ℕ × ℕ)) (lower : IsLowerFrontier A)
    (a b : ℝ) (i j : ℕ) :
    frontierTail A a b i j =
      if (i,j) ∈ A then frontierTail A a b i 0 * frontierTail A a b 0 j else 0 := by
  by_cases h : (i,j) ∈ A
  · simp [frontierTail,h,lower h (le_refl i) (Nat.zero_le j),lower h (Nat.zero_le i) (le_refl j)]
  · simp [frontierTail,h]

/-- With positive continuation ratios, the extremizing law has independent
coordinates exactly on rectangular frontiers. Every missing joint level
whose two margins are occupied is a strict negative dependence. -/
theorem independent_frontier_iff_rectangle (A : Finset (ℕ × ℕ)) (lower : IsLowerFrontier A)
    {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    (∀ i j, frontierTail A a b i j = frontierTail A a b i 0*frontierTail A a b 0 j) ↔ 
      A=A.image Prod.fst ×ˢ A.image Prod.snd := by
  constructor
  · intro h
    apply Subset.antisymm
    · exact fun q hq => mem_product.mpr ⟨mem_image_of_mem Prod.fst hq,mem_image_of_mem Prod.snd hq⟩
    · rintro ⟨i,j⟩ hq
      obtain ⟨hi,hj⟩ := mem_product.mp hq
      obtain ⟨⟨i',s⟩,h₁,he₁⟩ := mem_image.mp hi
      obtain ⟨⟨r,j'⟩,h₂,he₂⟩ := mem_image.mp hj
      change i'=i at he₁
      change j'=j at he₂
      subst i'
      subst j'
      by_contra miss
      have zero := h i j
      simp only [frontierTail,if_neg miss,if_pos (lower h₁ (le_refl i) (Nat.zero_le s)),
        if_pos (lower h₂ (Nat.zero_le r) (le_refl j)),pow_zero,one_mul,mul_one] at zero
      exact (mul_pos (pow_pos ha _) (pow_pos hb _)).ne' zero.symm
  · intro rectangle i j
    rw [frontier_survival_from_margins A lower]
    by_cases ij : (i,j) ∈ A
    · rw [if_pos ij]
    · rw [if_neg ij]
      by_cases hi : (i,0) ∈ A
      · have hj : (0,j) ∉ A := by
          intro e
          apply ij
          rw [rectangle]
          exact mem_product.mpr ⟨mem_image.mpr ⟨(i,0),hi,rfl⟩,mem_image.mpr ⟨(0,j),e,rfl⟩⟩
        simp [frontierTail,hj]
      · simp [frontierTail,hi]

#print axioms independent_frontier_iff_rectangle

private theorem sum_down (f : ℕ → ℝ) {r n : ℕ} (h : r ≤ n) :
    ∑ i ∈ Ico r n, (f i-f (i+1)) = f r-f n := by
  simpa only [neg_sub_neg] using sum_Ico_sub (fun i => -f i) h

/-- Summing the atoms over an upper rectangle recovers the assigned tail,
including zero on every unoccupied rectangle. -/
theorem sum_frontierAtom (A : Finset (ℕ × ℕ)) (a b : ℝ) {M N : ℕ}
    (hbox : ∀ q ∈ A, q.1 ≤ M ∧ q.2 ≤ N) {r s : ℕ} (hr : r ≤ M+1) (hs : s ≤ N+1) :
    ∑ i ∈ Ico r (M+1), ∑ j ∈ Ico s (N+1), frontierAtom A a b i j=frontierTail A a b r s := by
  let F := frontierTail A a b
  have right (i : ℕ) : F i (N+1)=0 := if_neg (fun h => by have := (hbox _ h).2; omega)
  have top (j : ℕ) : F (M+1) j=0 := if_neg (fun h => by have := (hbox _ h).1; omega)
  have row i : (∑ j ∈ Ico s (N+1), frontierAtom A a b i j)=F i s-F (i+1) s := by
    let G (j : ℕ) := F i j-F (i+1) j
    have he j : frontierAtom A a b i j=G j-G (j+1) := by dsimp only [frontierAtom,G,F]; ring
    simp_rw [he]
    rw [sum_down G hs]
    simp only [G,right,sub_self,sub_zero]
  rw [sum_congr rfl (fun i _ => row i),sum_down (fun i => F i s) hr,top,sub_zero]

private theorem dyadic_cell {u : ℝ} (hu : 1 ≤ u) (h2 : u<2) (r i : ℕ) :
    (2:ℝ)^r ≤ u*2^i ↔ r ≤ i := by
  constructor
  · intro h
    by_contra! hi
    have hpow :=  pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show i+1 ≤ r from hi)
    have gap := mul_lt_mul_of_pos_right h2 (by positivity : 0<(2:ℝ)^i)
    rw [pow_succ] at hpow
    linarith only [hpow,h,gap]
  · intro h
    exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h).trans
      (le_mul_of_one_le_left (by positivity) hu)

/-- The constructed finite sample gives price one at every occupied
dyadic rectangle and price zero at every other one. Its readings can
lie arbitrarily close to the upper edges of their dyadic cells. -/
theorem prescribed_dyadic_rectangle_price (A : Finset (ℕ × ℕ)) {M N : ℕ}
    (hbox : ∀ q ∈ A, q.1 ≤ M ∧ q.2 ≤ N) {u : ℝ} (hu : 1 ≤ u) (h2 : u<2)
    {r s : ℕ} (hr : r ≤ M) (hs : s ≤ N) :
    upperRectangle (range (M+1) ×ˢ range (N+1))
      (fun q : ℕ × ℕ => u*2^q.1) (fun q => u*2^q.2)
      (fun q => frontierAtom A (1/2) (1/2) q.1 q.2) (2^r) (2^s) =
        if (r,s) ∈ A then 1 else 0 := by
  have filter_eq : (range (M+1) ×ˢ range (N+1)).filter
      (fun q : ℕ × ℕ => (2:ℝ)^r ≤ u*2^q.1 ∧ (2:ℝ)^s ≤ u*2^q.2) =
      Ico r (M+1) ×ˢ Ico s (N+1) := by
    ext q
    simp only [mem_filter,mem_product,mem_range,mem_Ico,dyadic_cell hu h2]
    tauto
  rw [upperRectangle,filter_eq,sum_product,sum_frontierAtom A _ _ hbox (by omega) (by omega)]
  by_cases h : (r,s) ∈ A
  · simp only [frontierTail,h,if_true,one_div,inv_pow]
    field_simp
  · simp [frontierTail,h]

private theorem atom_vanishes_off_frontier {A : Finset (ℕ × ℕ)} (hA : IsLowerFrontier A)
    {i j : ℕ} (h : (i,j) ∉ A) (a b : ℝ) : frontierAtom A a b i j=0 := by
  have upper {r s : ℕ} (hr : i ≤ r) (hs : j ≤ s) : (r,s) ∉ A := fun e => h (hA e hr hs)
  simp [frontierAtom,frontierTail,h,upper (Nat.le_succ i) (le_refl j),
    upper (le_refl i) (Nat.le_succ j),upper (Nat.le_succ i) (Nat.le_succ j)]

/-- The extremizing sample can itself be restricted to the prescribed
frontier; all atoms at excluded sites already vanish. -/
theorem lower_frontier_rectangle_price (A : Finset (ℕ × ℕ)) (hA : IsLowerFrontier A)
    {M N : ℕ} (hbox : ∀ q ∈ A, q.1 ≤ M ∧ q.2 ≤ N) {u : ℝ} (hu : 1 ≤ u) (h2 : u<2)
    {r s : ℕ} (hr : r ≤ M) (hs : s ≤ N) :
    upperRectangle A (fun q => u*2^q.1) (fun q => u*2^q.2)
      (fun q => frontierAtom A (1/2) (1/2) q.1 q.2) (2^r) (2^s) =
        if (r,s) ∈ A then 1 else 0 := by
  rw [←prescribed_dyadic_rectangle_price A hbox hu h2 hr hs]
  unfold upperRectangle
  congr 1
  have incl : A ⊆ range (M+1) ×ˢ range (N+1) := fun q h =>
    mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hbox q h).1),
      mem_range.mpr (Nat.lt_succ_of_le (hbox q h).2)⟩
  refine sum_subset (filter_subset_filter _ incl) fun q hq e => ?_
  apply atom_vanishes_off_frontier hA
  exact fun ha => e (mem_filter.mpr ⟨ha,(mem_filter.mp hq).2⟩)

private theorem layer_on_cell {M i : ℕ} (hi : i ≤ M) {u : ℝ} (hu : 1 ≤ u) (h2 : u<2) :
    layerValue (M+1) dyadicRelativeJump (fun r => (2:ℝ)^r) (u*2^i)=2^i := by
  induction M,hi using Nat.le_induction with
  | base => exact dyadic_layer_full i ((dyadic_cell hu h2 i i).mpr le_rfl)
  | succ M hi ih =>
    have no : ¬(2:ℝ)^(M+1) ≤ u*2^i := fun h => Nat.not_succ_le_self M (((dyadic_cell hu h2 _ _).mp h).trans hi)
    simpa only [layerValue,sum_range_succ (n:=M+1),if_neg no,add_zero] using ih

private theorem frontier_occupied_iff {A : Finset (ℕ × ℕ)} (hA : IsLowerFrontier A)
    {u : ℝ} (hu : 1 ≤ u) (h2 : u<2) (r s : ℕ) :
    (∃ q ∈ A, (2:ℝ)^r ≤ u*2^q.1 ∧ (2:ℝ)^s ≤ u*2^q.2) ↔ (r,s) ∈ A := by
  simp only [dyadic_cell hu h2]
  exact ⟨fun ⟨q,hq,h⟩ => hA hq h.1 h.2,fun h => ⟨(r,s),h,le_rfl,le_rfl⟩⟩

/-- On every finite lower frontier the unrounded product is precisely
u squared times the occupied area. Letting u approach two shows why the
factor four in the occupied-area estimate cannot be reduced. -/
theorem sharp_frontier_product (A : Finset (ℕ × ℕ)) (hA : IsLowerFrontier A)
    {M N : ℕ} (hbox : ∀ q ∈ A, q.1 ≤ M ∧ q.2 ≤ N) {u : ℝ} (hu : 1 ≤ u) (h2 : u<2) :
    (∑ q ∈ A, (u*2^q.1)*(u*2^q.2)*frontierAtom A (1/2) (1/2) q.1 q.2) =
      u^2*occupiedDyadicArea A (fun q => u*2^q.1) (fun q => u*2^q.2) M N := by
  classical
  let f (q : ℕ × ℕ) := u*2^q.1
  let g (q : ℕ × ℕ) := u*2^q.2
  let w (q : ℕ × ℕ) := frontierAtom A (1/2) (1/2) q.1 q.2
  let t (r : ℕ) : ℝ := 2^r
  have cake := product_layers_eq_rectangles A f g w (M+1) (N+1) dyadicRelativeJump t dyadicRelativeJump t
  have price (r : ℕ) (hr : r ∈ range (M+1)) (s : ℕ) (hs : s ∈ range (N+1)) :
      upperRectangle A f g w (t r) (t s) = if (r,s) ∈ A then 1 else 0 :=
    lower_frontier_rectangle_price A hA hbox hu h2 (Nat.le_of_lt_succ (mem_range.mp hr))
      (Nat.le_of_lt_succ (mem_range.mp hs))
  have grid : (∑ r ∈ range (M+1), ∑ s ∈ range (N+1),
      dyadicRelativeJump r*dyadicRelativeJump s*upperRectangle A f g w (t r) (t s)) =
      occupiedDyadicArea A f g M N := by
    unfold occupiedDyadicArea
    refine sum_congr rfl fun r hr => sum_congr rfl fun s hs => ?_
    rw [price r hr s hs]
    dsimp only [f,g]
    simp only [frontier_occupied_iff hA hu h2 r s]
    split <;> simp
  rw [←grid,←cake,mul_sum]
  apply sum_congr rfl
  intro q hq
  have left : layerValue (M+1) dyadicRelativeJump t (f q)=2^q.1 := layer_on_cell (hbox q hq).1 hu h2
  have right : layerValue (N+1) dyadicRelativeJump t (g q)=2^q.2 := layer_on_cell (hbox q hq).2 hu h2
  rw [left,right]
  dsimp only [w]
  ring

private theorem frontier_area_pos (A : Finset (ℕ × ℕ)) (hA : A.Nonempty) (M N : ℕ)
    {u : ℝ} (hu : 1 ≤ u) (h2 : u<2) :
    0<occupiedDyadicArea A (fun q => u*2^q.1) (fun q => u*2^q.2) M N := by
  classical
  obtain ⟨q,hq⟩ := hA
  let J (r s : ℕ) : ℝ := if ∃ q ∈ A, (2:ℝ)^r ≤ u*2^q.1 ∧ (2:ℝ)^s ≤ u*2^q.2
    then dyadicRelativeJump r*dyadicRelativeJump s else 0
  have good : ∃ a ∈ A, (2:ℝ)^0 ≤ u*2^a.1 ∧ (2:ℝ)^0 ≤ u*2^a.2 :=
    ⟨q,hq,(dyadic_cell hu h2 _ _).mpr (Nat.zero_le _),(dyadic_cell hu h2 _ _).mpr (Nat.zero_le _)⟩
  have price : J 0 0=1 := by
    dsimp only [J]
    rw [if_pos good]
    norm_num [dyadicRelativeJump]
  have nn (r s : ℕ) : 0 ≤ J r s := by
    unfold J dyadicRelativeJump
    split_ifs <;> norm_num
  change 0<∑ r ∈ range (M+1), ∑ s ∈ range (N+1), J r s
  have includes : J 0 0 ≤ _ :=
    (single_le_sum (fun s (_ : s ∈ range (N+1)) => nn 0 s) (mem_range.mpr (Nat.succ_pos N))).trans
      (single_le_sum (fun r (_ : r ∈ range (M+1)) => sum_nonneg fun s _ => nn r s)
        (mem_range.mpr (Nat.succ_pos M)))
  rw [price] at includes
  exact zero_lt_one.trans_le includes

/-- Every nonempty lower frontier requires the full factor four, even
after the occupied shape is fixed and all nonempty rectangles have price
exactly one. Each smaller proposed factor is violated by a finite sample. -/
theorem sharp_factor_four_on_each_frontier (A : Finset (ℕ × ℕ)) (lower : IsLowerFrontier A)
    (nonempty : A.Nonempty) {M N : ℕ} (hbox : ∀ q ∈ A, q.1 ≤ M ∧ q.2 ≤ N) {C : ℝ} (hC : C<4) :
    ∃ u : ℝ, 1 ≤ u ∧ u<2 ∧
      C*occupiedDyadicArea A (fun q => u*2^q.1) (fun q => u*2^q.2) M N <
        ∑ q ∈ A, (u*2^q.1)*(u*2^q.2)*frontierAtom A (1/2) (1/2) q.1 q.2 := by
  let b := Real.sqrt (max C 1)
  have hnon : 0 ≤ max C 1 := zero_le_one.trans (le_max_right _ _)
  have hs : b^2=max C 1 := Real.sq_sqrt hnon
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have below : b<2 := by
    have hmax : max C 1 < 4 := max_lt hC (by norm_num)
    nlinarith only [hs,hmax,hb]
  let u := (2+b)/2
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hb]
  have h2 : u<2 := by dsimp only [u]; linarith only [below]
  have gap : b<u := by dsimp only [u]; linarith only [below]
  have hsq : C < u^2 := (le_max_left C 1).trans_lt
    (hs ▸ (sq_lt_sq₀ hb (zero_le_one.trans hu)).mpr gap)
  refine ⟨u,hu,h2,?_⟩
  rw [sharp_frontier_product A lower hbox hu h2]
  exact mul_lt_mul_of_pos_right hsq (frontier_area_pos A nonempty M N hu h2)

#print axioms sharp_factor_four_on_each_frontier
#print axioms lower_frontier_rectangle_price
#print axioms sharp_frontier_product
#print axioms frontier_nonneg_for_all_iff
#print axioms sum_frontierAtom
#print axioms prescribed_dyadic_rectangle_price
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
