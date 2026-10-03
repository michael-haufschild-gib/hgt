import GaloisForLFunctions.HTGeometry.WordConvolutionBanachAlgebra
import GaloisForLFunctions.HTGeometry.CompleteGradedAlgebraExpLog
import Mathlib.Data.Vector.Basic

/-!
# Formal word series as a complete graded algebra

For a ring `R` and an alphabet `A`, the formal word series `R⟨⟨A⟩⟩ = (A* → R)` with the
concatenation product form a ring; over a field `k` they form a `k`-algebra.  If `R` is itself a
complete graded `k`-algebra, the total grading `deg(w ⊗ r) = |w| + deg r` makes `R⟨⟨A⟩⟩` complete
graded; with `R = k` (concentrated in degree zero) this is the complete free algebra
`k⟨⟨A⟩⟩`, and iterating once gives its completed tensor square.

For a finite alphabet, every family of degree-one elements of a complete graded algebra `B`
extends to a unique graded algebra homomorphism `k⟨⟨A⟩⟩ → B`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

open CompleteGradedAlgebra

/-! ## The ring of word series -/

variable (A : Type*) (R : Type*)

/-- Formal word series `A* → R` with the concatenation product. -/
@[ext]
structure WordSeries where
  /-- The coefficient of a word. -/
  coeff : List A → R

namespace WordSeries

variable {A R}

/-- Word series are their coefficient functions. -/
def coeffEquiv : WordSeries A R ≃ (List A → R) where
  toFun F := F.coeff
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Ring R]

instance : AddCommGroup (WordSeries A R) := coeffEquiv.addCommGroup

instance : Mul (WordSeries A R) := ⟨fun F G => ⟨wordConv (E := R) F.coeff G.coeff⟩⟩

instance : One (WordSeries A R) := ⟨⟨wordUnit (E := R)⟩⟩

theorem mul_coeff (F G : WordSeries A R) (w : List A) :
    (F * G).coeff w = ∑ p ∈ wordSplits w, F.coeff p.1 * G.coeff p.2 := rfl

theorem one_coeff (w : List A) : (1 : WordSeries A R).coeff w = wordUnit w := rfl

@[simp] theorem add_coeff (F G : WordSeries A R) (w : List A) :
    (F + G).coeff w = F.coeff w + G.coeff w := rfl

@[simp] theorem zero_coeff (w : List A) : (0 : WordSeries A R).coeff w = 0 := rfl

@[simp] theorem neg_coeff (F : WordSeries A R) (w : List A) : (-F).coeff w = -F.coeff w := rfl

@[simp] theorem sub_coeff (F G : WordSeries A R) (w : List A) :
    (F - G).coeff w = F.coeff w - G.coeff w := rfl

theorem sum_coeff {ι : Type*} (s : Finset ι) (F : ι → WordSeries A R) (w : List A) :
    (∑ i ∈ s, F i).coeff w = ∑ i ∈ s, (F i).coeff w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, add_coeff, ih]

omit [Ring R] in
theorem coeff_injective : Function.Injective (coeff : WordSeries A R → List A → R) :=
  fun _ _ h => WordSeries.ext h

instance : Ring (WordSeries A R) :=
  { (inferInstance : AddCommGroup (WordSeries A R)) with
    mul_assoc := fun F G K => WordSeries.ext (wordConv_assoc (E := R) F.coeff G.coeff K.coeff)
    one_mul := fun G => WordSeries.ext (wordConv_unit_left (E := R) G.coeff)
    mul_one := fun F => WordSeries.ext (wordConv_unit_right (E := R) F.coeff)
    left_distrib := fun F G K =>
      WordSeries.ext (wordConv_add_right (E := R) F.coeff G.coeff K.coeff)
    right_distrib := fun F G K =>
      WordSeries.ext (wordConv_add_left (E := R) F.coeff G.coeff K.coeff)
    zero_mul := fun G => WordSeries.ext <| funext fun w => by
      change ∑ p ∈ wordSplits w, (0 : R) * G.coeff p.2 = 0
      simp
    mul_zero := fun F => WordSeries.ext <| funext fun w => by
      change ∑ p ∈ wordSplits w, F.coeff p.1 * (0 : R) = 0
      simp }

section Algebra

variable {k : Type*} [Field k] [Algebra k R]

instance : Module k (WordSeries A R) := coeffEquiv.module k

@[simp] theorem smul_coeff (c : k) (F : WordSeries A R) (w : List A) :
    (c • F).coeff w = c • F.coeff w := rfl

instance : Algebra k (WordSeries A R) :=
  Algebra.ofModule
    (fun c F G => WordSeries.ext <| funext fun w => by
      change ∑ p ∈ wordSplits w, (c • F.coeff p.1) * G.coeff p.2 =
        c • ∑ p ∈ wordSplits w, F.coeff p.1 * G.coeff p.2
      rw [smul_sum]
      exact sum_congr rfl fun _ _ => smul_mul_assoc _ _ _)
    (fun c F G => WordSeries.ext <| funext fun w => by
      change ∑ p ∈ wordSplits w, F.coeff p.1 * (c • G.coeff p.2) =
        c • ∑ p ∈ wordSplits w, F.coeff p.1 * G.coeff p.2
      rw [smul_sum]
      exact sum_congr rfl fun _ _ => mul_smul_comm _ _ _)

theorem algebraMap_coeff (c : k) (w : List A) :
    (algebraMap k (WordSeries A R) c).coeff w = c • wordUnit (E := R) w := by
  rw [Algebra.algebraMap_eq_smul_one, smul_coeff, one_coeff]

end Algebra

/-! ## Elementary words -/

section Single

variable [DecidableEq A]

/-- The monomial `r ⊗ w`. -/
def single (w : List A) (r : R) : WordSeries A R := ⟨fun v => if v = w then r else 0⟩

theorem single_coeff (w : List A) (r : R) (v : List A) :
    (single w r).coeff v = if v = w then r else 0 := rfl

theorem single_mul_single (u v : List A) (r s : R) :
    single u r * single v s = single (u ++ v) (r * s) := by
  ext w
  rw [mul_coeff]
  by_cases hw : w = u ++ v
  · subst hw
    rw [sum_eq_single (u, v)]
    · simp [single_coeff]
    · rintro ⟨a, b⟩ hp hne
      rw [mem_wordSplits] at hp
      by_cases ha : a = u
      · subst ha
        have hb : b = v := List.append_cancel_left hp
        exact absurd (by rw [hb]) hne
      · simp [single_coeff, ha]
    · intro h; exact absurd (mem_wordSplits.2 rfl) h
  · rw [single_coeff, if_neg hw]
    refine sum_eq_zero fun p hp => ?_
    rw [mem_wordSplits] at hp
    by_cases ha : p.1 = u
    · by_cases hb : p.2 = v
      · exact absurd (by rw [← hp, ha, hb]) hw
      · simp [single_coeff, hb]
    · simp [single_coeff, ha]

theorem single_nil_one : single ([] : List A) (1 : R) = 1 := by
  ext v
  rw [single_coeff, one_coeff]
  cases v with
  | nil => simp
  | cons _ _ => simp [wordUnit]

theorem single_pow (a : A) (r : R) (m : ℕ) :
    single [a] r ^ m = single (List.replicate m a) (r ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, List.replicate_zero, single_nil_one]
  | succ m ih => rw [pow_succ, ih, single_mul_single, ← pow_succ, List.replicate_succ']

end Single

end WordSeries

/-! ## The total grading -/

namespace CompleteGradedAlgebra

variable {k : Type*} [Field k]

/-- A field as a complete graded algebra concentrated in degree zero. -/
instance trivialGrading : CompleteGradedAlgebra k k where
  comp n := if n = 0 then LinearMap.id else 0
  comp_comp m n x := by
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]
  ext_comp x y h := by simpa using h 0
  glue f _ := f 0
  comp_glue f hf n := by
    by_cases hn : n = 0
    · subst hn; simp
    · have := hf n
      simp only [hn, if_false, LinearMap.zero_apply] at this
      simp [hn, ← this]
  comp_mul n x y := by
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn, LinearMap.zero_apply]
      symm
      refine sum_eq_zero fun i hi => ?_
      by_cases hi0 : i = 0
      · subst hi0; simp [hn]
      · simp [hi0]
  comp_one n := by by_cases hn : n = 0 <;> simp [hn]

theorem proj_field (n : ℕ) (c : k) : proj k n c = if n = 0 then c else 0 := by
  show (if n = 0 then LinearMap.id else 0 : k →ₗ[k] k) c = _
  split_ifs <;> rfl

end CompleteGradedAlgebra

namespace WordSeries

variable {A : Type*} {k : Type*} [Field k] {R : Type*} [Ring R] [Algebra k R]
variable [CompleteGradedAlgebra k R]

/-- Reindexing a split sum by the length of the first factor. -/
theorem sum_shift_eq (p q n : ℕ) (f g : ℕ → R) :
    ∑ i ∈ range (n + 1),
        (if p ≤ i then f (i - p) else 0) * (if q ≤ n - i then g (n - i - q) else 0) =
      if p + q ≤ n then ∑ a ∈ range (n - (p + q) + 1), f a * g (n - (p + q) - a) else 0 := by
  rw [← sum_filter_add_sum_filter_not (range (n + 1)) (fun i => p ≤ i ∧ q ≤ n - i)]
  rw [sum_eq_zero (s := filter (fun i => ¬(p ≤ i ∧ q ≤ n - i)) (range (n + 1))) (fun i hi => by
    rw [mem_filter] at hi
    by_cases h1 : p ≤ i
    · rw [if_pos h1, if_neg (fun h2 => hi.2 ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]), add_zero]
  split_ifs with hpq
  · refine sum_nbij' (fun i => i - p) (fun a => a + p) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_filter, mem_range] at hi
      rw [mem_range]
      omega
    · intro a ha
      rw [mem_range] at ha
      rw [mem_filter, mem_range]
      omega
    · intro i hi
      rw [mem_filter, mem_range] at hi
      omega
    · intro a _; simp
    · intro i hi
      rw [mem_filter, mem_range] at hi
      rw [if_pos hi.2.1, if_pos hi.2.2]
      congr 2
      omega
  · refine sum_eq_zero fun i hi => ?_
    rw [mem_filter, mem_range] at hi
    omega

/-- `π_n` of the total grading: `(π_n F)_w = π_{n-|w|}(F_w)` for `|w| ≤ n`. -/
def totalProj (n : ℕ) : WordSeries A R →ₗ[k] WordSeries A R where
  toFun F := ⟨fun w => if w.length ≤ n then proj k (n - w.length) (F.coeff w) else 0⟩
  map_add' F G := WordSeries.ext <| funext fun w => by
    simp only [add_coeff]
    split_ifs <;> simp
  map_smul' c F := WordSeries.ext <| funext fun w => by
    simp only [smul_coeff, RingHom.id_apply]
    split_ifs <;> simp

theorem totalProj_coeff (n : ℕ) (F : WordSeries A R) (w : List A) :
    (totalProj (k := k) n F).coeff w =
      if w.length ≤ n then proj k (n - w.length) (F.coeff w) else 0 := rfl

instance totalGrading : CompleteGradedAlgebra k (WordSeries A R) where
  comp := totalProj
  comp_comp m n F := by
    ext w
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, totalProj_coeff, totalProj_coeff]
      split_ifs <;> simp [comp_comp_self]
    · rw [if_neg hmn, totalProj_coeff, totalProj_coeff, zero_coeff]
      split_ifs with h1 h2
      · rw [comp_comp_of_ne (by omega)]
      · simp
      · rfl
  ext_comp F G h := by
    ext w
    refine ext_comp (k := k) _ _ fun j => ?_
    have := congrArg (fun F => WordSeries.coeff F w) (h (w.length + j))
    simp only [totalProj_coeff, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at this
    exact this
  glue f hf := ⟨fun w => glue (k := k) (fun j => (f (w.length + j)).coeff w) fun j => by
    have := congrArg (fun F => WordSeries.coeff F w) (hf (w.length + j))
    simp only [totalProj_coeff, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at this
    exact this⟩
  comp_glue f hf n := by
    ext w
    rw [totalProj_coeff]
    split_ifs with h
    · rw [comp_glue, Nat.add_sub_cancel' h]
    · have := congrArg (fun F => WordSeries.coeff F w) (hf n)
      simp only [totalProj_coeff, if_neg h] at this
      exact this
  comp_mul n F G := by
    ext w
    rw [totalProj_coeff, mul_coeff, sum_coeff]
    simp only [mul_coeff, totalProj_coeff]
    rw [sum_comm]
    split_ifs with hw
    · rw [map_sum]
      refine sum_congr rfl fun p hp => ?_
      rw [mem_wordSplits] at hp
      have hl : p.1.length + p.2.length = w.length := by rw [← hp, List.length_append]
      rw [comp_mul, sum_shift_eq p.1.length p.2.length n (fun a => proj k a (F.coeff p.1))
        (fun b => proj k b (G.coeff p.2)), hl, if_pos hw]
    · symm
      refine sum_eq_zero fun p hp => ?_
      rw [mem_wordSplits] at hp
      have hl : p.1.length + p.2.length = w.length := by rw [← hp, List.length_append]
      rw [sum_shift_eq p.1.length p.2.length n (fun a => proj k a (F.coeff p.1))
        (fun b => proj k b (G.coeff p.2)), hl, if_neg hw]
  comp_one n := by
    ext w
    rw [totalProj_coeff, one_coeff]
    cases w with
    | nil =>
      simp only [wordUnit, List.length_nil, zero_le, if_true, Nat.sub_zero, comp_one]
      split_ifs <;> rfl
    | cons a w =>
      simp only [wordUnit, map_zero, ite_self]
      split_ifs <;> rfl

theorem proj_coeff (n : ℕ) (F : WordSeries A R) (w : List A) :
    (proj k n F).coeff w = if w.length ≤ n then proj k (n - w.length) (F.coeff w) else 0 := rfl

/-! ## Homogeneous elements -/

end WordSeries

namespace CompleteGradedAlgebra

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B] [CompleteGradedAlgebra k B]

theorem proj_of_homogeneous {i : ℕ} {x : B} (hx : proj k i x = x) (m : ℕ) :
    proj k m x = if m = i then x else 0 := by
  rw [← hx, comp_comp, hx]

theorem proj_mul_of_homogeneous {i j : ℕ} {x y : B} (hx : proj k i x = x) (hy : proj k j y = y)
    (m : ℕ) : proj k m (x * y) = if m = i + j then x * y else 0 := by
  rw [comp_mul]
  simp_rw [proj_of_homogeneous hx, proj_of_homogeneous hy]
  by_cases h : i ≤ m
  · rw [sum_eq_single i (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun hi => absurd (mem_range.2 (by omega)) hi), if_pos rfl]
    by_cases h' : m = i + j
    · rw [if_pos (by omega), if_pos h']
    · rw [if_neg (by omega), if_neg h', mul_zero]
  · rw [if_neg (by omega)]
    exact sum_eq_zero fun b hb => by
      rw [mem_range] at hb
      rw [if_neg (by omega), zero_mul]

theorem homogeneous_mul {i j : ℕ} {x y : B} (hx : proj k i x = x) (hy : proj k j y = y) :
    proj k (i + j) (x * y) = x * y := by
  rw [proj_mul_of_homogeneous hx hy, if_pos rfl]

end CompleteGradedAlgebra

namespace WordSeries

variable {A : Type*} {k : Type*} [Field k]

/-! ## Words of a given length -/

section Words

variable [Fintype A]

/-- The finite set of words of length `n`. -/
def wordsOfLength (n : ℕ) : Finset (List A) :=
  (Finset.univ : Finset (List.Vector A n)).map ⟨List.Vector.toList, fun _ _ h => Subtype.ext h⟩

theorem mem_wordsOfLength {n : ℕ} {w : List A} : w ∈ wordsOfLength n ↔ w.length = n := by
  constructor
  · intro h
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.1 h
    exact v.2
  · intro h
    exact Finset.mem_map.2 ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩

end Words

/-! ## The universal property of `k⟨⟨A⟩⟩` -/

section Lift

variable [Fintype A] [DecidableEq A]
variable {B : Type*} [Ring B] [Algebra k B] [CompleteGradedAlgebra k B]

/-- The word monomial `t(a₁) ⋯ t(aₙ)`. -/
def tprod (t : A → B) (w : List A) : B := (w.map t).prod

omit [Fintype A] [DecidableEq A] in
theorem tprod_append (t : A → B) (u v : List A) : tprod t (u ++ v) = tprod t u * tprod t v := by
  rw [tprod, List.map_append, List.prod_append]; rfl

omit [Fintype A] [DecidableEq A] in
theorem proj_tprod (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (w : List A) :
    proj k w.length (tprod t w) = tprod t w := by
  induction w with
  | nil => rw [tprod, List.map_nil, List.prod_nil, List.length_nil, comp_one, if_pos rfl]
  | cons a w ih =>
    rw [tprod, List.map_cons, List.prod_cons, List.length_cons, add_comm]
    exact homogeneous_mul (ht a) ih

/-- The homogeneous component `∑_{|w| = n} F_w t^w`. -/
def liftComponent (t : A → B) (F : WordSeries A k) (n : ℕ) : B :=
  ∑ w ∈ wordsOfLength n, F.coeff w • tprod t w

omit [DecidableEq A] in
theorem proj_liftComponent (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (F : WordSeries A k)
    (n m : ℕ) : proj k m (liftComponent t F n) = if m = n then liftComponent t F n else 0 := by
  rw [liftComponent, map_sum]
  split_ifs with h
  · subst h
    refine sum_congr rfl fun w hw => ?_
    rw [map_smul, ← mem_wordsOfLength.1 hw, proj_tprod t ht]
  · refine sum_eq_zero fun w hw => ?_
    rw [map_smul, proj_of_homogeneous (proj_tprod t ht w), if_neg (by
      rw [mem_wordsOfLength.1 hw]; exact h), smul_zero]

/-- The extension of `t : A → B_1` to `k⟨⟨A⟩⟩`. -/
def liftFun (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (F : WordSeries A k) : B :=
  glue (k := k) (liftComponent t F) fun n => by rw [proj_liftComponent t ht, if_pos rfl]

omit [DecidableEq A] in
theorem proj_liftFun (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (F : WordSeries A k) (n : ℕ) :
    proj k n (liftFun t ht F) = liftComponent t F n := comp_glue _ _ n

omit [DecidableEq A] [CompleteGradedAlgebra k B] in
theorem liftComponent_mul (t : A → B) (F G : WordSeries A k) (n : ℕ) :
    liftComponent t (F * G) n =
      ∑ i ∈ range (n + 1), liftComponent t F i * liftComponent t G (n - i) := by
  have hL : liftComponent t (F * G) n = ∑ x ∈ (wordsOfLength n).sigma (fun w => wordSplits w),
      (F.coeff x.2.1 * G.coeff x.2.2) • tprod t x.1 := by
    rw [liftComponent]
    simp_rw [mul_coeff, sum_smul]
    rw [sum_sigma']
  have hR : ∑ i ∈ range (n + 1), liftComponent t F i * liftComponent t G (n - i) =
      ∑ y ∈ (range (n + 1)).sigma (fun i => wordsOfLength i ×ˢ wordsOfLength (n - i)),
        (F.coeff y.2.1 • tprod t y.2.1) * (G.coeff y.2.2 • tprod t y.2.2) := by
    simp_rw [liftComponent, sum_mul_sum, ← sum_product']
    rw [sum_sigma']
  rw [hL, hR]
  refine sum_bij' (fun x _ => ⟨x.2.1.length, (x.2.1, x.2.2)⟩) (fun y _ => ⟨y.2.1 ++ y.2.2, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨w, ⟨u, v⟩⟩ hx
    simp only [mem_sigma, mem_wordsOfLength, mem_wordSplits] at hx
    simp only [mem_sigma, mem_range, mem_product, mem_wordsOfLength]
    have hl : u.length + v.length = n := by rw [← hx.1, ← hx.2, List.length_append]
    exact ⟨by omega, trivial, by omega⟩
  · rintro ⟨i, ⟨u, v⟩⟩ hy
    simp only [mem_sigma, mem_range, mem_product, mem_wordsOfLength] at hy
    obtain ⟨h1, h2, h3⟩ := hy
    simp only [mem_sigma, mem_wordsOfLength, mem_wordSplits, List.length_append, and_true]
    rw [h2, h3]
    omega
  · rintro ⟨w, ⟨u, v⟩⟩ hx
    simp only [mem_sigma, mem_wordsOfLength, mem_wordSplits] at hx
    simp only [hx.2]
  · rintro ⟨i, ⟨u, v⟩⟩ hy
    simp only [mem_sigma, mem_range, mem_product, mem_wordsOfLength] at hy
    simp only [hy.2.1]
  · rintro ⟨w, ⟨u, v⟩⟩ hx
    simp only [mem_sigma, mem_wordsOfLength, mem_wordSplits] at hx
    simp only
    rw [← hx.2, tprod_append, smul_mul_smul]

omit [DecidableEq A] in
theorem liftFun_one (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) : liftFun t ht 1 = 1 := by
  refine ext_comp (k := k) _ _ fun n => ?_
  rw [proj_liftFun, comp_one, liftComponent]
  split_ifs with h
  · subst h
    rw [sum_eq_single []]
    · rw [one_coeff, wordUnit_nil, one_smul, tprod, List.map_nil, List.prod_nil]
    · intro w _ hne
      rw [one_coeff, wordUnit_of_ne_nil hne, zero_smul]
    · intro h; exact (h (mem_wordsOfLength.2 rfl)).elim
  · refine sum_eq_zero fun w hw => ?_
    have : w ≠ [] := fun h' => h (by rw [← mem_wordsOfLength.1 hw, h', List.length_nil])
    rw [one_coeff, wordUnit_of_ne_nil this, zero_smul]

variable (k) in
/-- **Universal property.**  Degree-one elements `t a ∈ B_1` extend to a graded algebra
homomorphism `k⟨⟨A⟩⟩ → B`. -/
def lift (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) : WordSeries A k →ₐ[k] B where
  toFun := liftFun t ht
  map_one' := by
    refine ext_comp (k := k) _ _ fun n => ?_
    rw [proj_liftFun, comp_one, liftComponent]
    split_ifs with h
    · subst h
      rw [sum_eq_single []]
      · rw [one_coeff, wordUnit_nil, one_smul, tprod, List.map_nil, List.prod_nil]
      · intro w _ hne
        rw [one_coeff, wordUnit_of_ne_nil hne, zero_smul]
      · intro h; exact (h (mem_wordsOfLength.2 rfl)).elim
    · refine sum_eq_zero fun w hw => ?_
      have : w ≠ [] := fun h' => h (by rw [← mem_wordsOfLength.1 hw, h', List.length_nil])
      rw [one_coeff, wordUnit_of_ne_nil this, zero_smul]
  map_mul' F G := by
    refine ext_comp (k := k) _ _ fun n => ?_
    change proj k n (liftFun t ht (F * G)) = proj k n (liftFun t ht F * liftFun t ht G)
    rw [proj_liftFun, liftComponent_mul, comp_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [proj_liftFun, proj_liftFun]
  map_zero' := by
    refine ext_comp (k := k) _ _ fun n => ?_
    change proj k n (liftFun t ht 0) = proj k n 0
    rw [proj_liftFun, map_zero, liftComponent]
    exact sum_eq_zero fun w _ => by rw [zero_coeff, zero_smul]
  map_add' F G := by
    refine ext_comp (k := k) _ _ fun n => ?_
    change proj k n (liftFun t ht (F + G)) = proj k n (liftFun t ht F + liftFun t ht G)
    rw [map_add, proj_liftFun, proj_liftFun, proj_liftFun, liftComponent, liftComponent,
      liftComponent, ← sum_add_distrib]
    exact sum_congr rfl fun w _ => by rw [add_coeff, add_smul]
  commutes' c := by
    refine ext_comp (k := k) _ _ fun n => ?_
    change proj k n (liftFun t ht (algebraMap k (WordSeries A k) c)) = _
    rw [proj_liftFun, comp_algebraMap, liftComponent]
    split_ifs with h
    · subst h
      rw [sum_eq_single []]
      · rw [algebraMap_coeff, wordUnit_nil, tprod, List.map_nil, List.prod_nil,
          Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one]
      · intro w _ hne
        rw [algebraMap_coeff, wordUnit_of_ne_nil hne, smul_zero, zero_smul]
      · intro h; exact (h (mem_wordsOfLength.2 rfl)).elim
    · refine sum_eq_zero fun w hw => ?_
      have : w ≠ [] := fun h' => h (by rw [← mem_wordsOfLength.1 hw, h', List.length_nil])
      rw [algebraMap_coeff, wordUnit_of_ne_nil this, smul_zero, zero_smul]

omit [DecidableEq A] in
theorem lift_apply (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (F : WordSeries A k) :
    lift k t ht F = liftFun t ht F := rfl

omit [DecidableEq A] in
theorem proj_lift (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (F : WordSeries A k) (n : ℕ) :
    proj k n (lift k t ht F) = ∑ w ∈ wordsOfLength n, F.coeff w • tprod t w :=
  proj_liftFun t ht F n

/-- The homogeneous component of a word series is the sum of its monomials of that length. -/
theorem proj_eq_sum_single (F : WordSeries A k) (n : ℕ) :
    proj k n F = ∑ w ∈ wordsOfLength n, F.coeff w • single w (1 : k) := by
  ext v
  rw [proj_coeff, sum_coeff]
  simp only [smul_coeff, single_coeff, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hv : v.length = n
  · rw [if_pos (by omega), if_pos (mem_wordsOfLength.2 hv), hv, Nat.sub_self, proj_field,
      if_pos rfl]
  · by_cases hle : v.length ≤ n
    · rw [if_pos hle, if_neg (fun h => hv (mem_wordsOfLength.1 h)), proj_field, if_neg (by omega)]
    · rw [if_neg hle, if_neg (fun h => hv (mem_wordsOfLength.1 h))]

omit [Fintype A] in
theorem single_cons (a : A) (w : List A) :
    single (a :: w) (1 : k) = single [a] 1 * single w 1 := by
  rw [single_mul_single, List.singleton_append, one_mul]

theorem lift_single_singleton (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (a : A) :
    lift k t ht (single [a] 1) = t a := by
  refine ext_comp (k := k) _ _ fun n => ?_
  rw [proj_lift, proj_of_homogeneous (ht a)]
  split_ifs with h
  · subst h
    rw [sum_eq_single [a]]
    · simp [single_coeff, tprod]
    · intro w _ hw; rw [single_coeff, if_neg hw, zero_smul]
    · intro h; exact (h (mem_wordsOfLength.2 rfl)).elim
  · refine sum_eq_zero fun w hw => ?_
    have : w ≠ [a] := fun h' => h (by rw [← mem_wordsOfLength.1 hw, h']; rfl)
    rw [single_coeff, if_neg this, zero_smul]

theorem lift_single (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (w : List A) :
    lift k t ht (single w 1) = tprod t w := by
  induction w with
  | nil => rw [single_nil_one, map_one]; rfl
  | cons a w ih =>
    rw [single_cons, map_mul, lift_single_singleton, ih]
    simp only [tprod, List.map_cons, List.prod_cons]

theorem lift_graded (t : A → B) (ht : ∀ a, proj k 1 (t a) = t a) (n : ℕ) (F : WordSeries A k) :
    proj k n (lift k t ht F) = lift k t ht (proj k n F) := by
  rw [proj_eq_sum_single F n, map_sum, proj_lift]
  exact sum_congr rfl fun w _ => by rw [map_smul, lift_single]

end Lift

end WordSeries

end GaloisForLFunctions.HTGeometry
