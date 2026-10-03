import GaloisForLFunctions.HTGeometry.WordSeriesCompleteGradedAlgebra
import GaloisForLFunctions.HTGeometry.CompleteGradedHopfSignature

/-!
# The complete tensor Hopf algebra on a finite alphabet

On `H = k⟨⟨A⟩⟩` with completed tensor square `T = H⟨⟨A⟩⟩` (coefficient of `u ⊗ v` is
`F_u(v)`), the letters are primitive: the coproduct is the graded algebra map with
`Δ(a) = a ⊗ 1 + 1 ⊗ a`.  The antipode `S(w) = (-1)^{|w|} rev(w)` satisfies `m(S ⊗ id)Δ = ηε`;
the key cancellation is `m(S ⊗ id)(Δ(a) · G) = 0` for every letter `a` and every `G ∈ T`.
This makes `k⟨⟨A⟩⟩` a complete connected graded Hopf structure.

In it:
* exchanging two letters `a ≠ b`, the primitive `a - b` is anti-invariant and `exp(a - b) ≠ 1`
  is a nontrivial twisted-antipode fixed signature;
* negating two letters `x ≠ y`, the fixed signatures `e^x`, `e^y` have a product that is not
  fixed, and the bracket `[x, y]` of two anti-invariant primitives is not anti-invariant.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

open CompleteGradedAlgebra WordSeries

variable {A : Type*} {k : Type*} [Field k]

namespace FreeHopf

/-! ## Homogeneous monomials -/

theorem proj_single [DecidableEq A] (w : List A) (c : k) (n : ℕ) :
    proj k n (single w c) = if n = w.length then single w c else 0 := by
  refine WordSeries.ext (funext fun v => ?_)
  rw [proj_coeff, single_coeff]
  by_cases hv : v = w
  · subst hv
    rw [if_pos rfl]
    by_cases hn : n = v.length
    · rw [if_pos (by omega), hn, Nat.sub_self, proj_field, if_pos rfl, if_pos rfl, single_coeff,
        if_pos rfl]
    · rw [if_neg hn, zero_coeff]
      split_ifs with h
      · rw [proj_field, if_neg (by omega)]
      · rfl
  · rw [if_neg hv, map_zero]
    split_ifs <;> simp [single_coeff, hv]

/-- Coefficients at the own degree: `F_w = (π_{|w|} F)_w`. -/
theorem coeff_eq_proj_coeff (F : WordSeries A k) (w : List A) :
    F.coeff w = (proj k w.length F).coeff w := by
  rw [proj_coeff, if_pos le_rfl, Nat.sub_self, proj_field, if_pos rfl]

theorem coeff_eq_proj_coeff' {R : Type*} [Ring R] [Algebra k R] [CompleteGradedAlgebra k R]
    (F : WordSeries A R) (w : List A) (j : ℕ) :
    proj k j (F.coeff w) = (proj k (w.length + j) F).coeff w := by
  rw [proj_coeff, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-! ## The two tensor embeddings -/

/-- `x ↦ x ⊗ 1`. -/
def leftEmb : WordSeries A k →ₐ[k] WordSeries A (WordSeries A k) where
  toFun F := ⟨fun u => F.coeff u • (1 : WordSeries A k)⟩
  map_one' := WordSeries.ext <| funext fun u => by
    change wordUnit u • (1 : WordSeries A k) = wordUnit (E := WordSeries A k) u
    cases u with
    | nil => simp [wordUnit]
    | cons _ _ => simp [wordUnit]
  map_mul' F G := WordSeries.ext <| funext fun u => by
    change (∑ p ∈ wordSplits u, F.coeff p.1 * G.coeff p.2) • (1 : WordSeries A k) =
      ∑ p ∈ wordSplits u, (F.coeff p.1 • (1 : WordSeries A k)) * (G.coeff p.2 • 1)
    rw [sum_smul]
    exact sum_congr rfl fun p _ => by rw [smul_mul_smul, mul_one]
  map_zero' := WordSeries.ext <| funext fun u => by
    change (0 : k) • (1 : WordSeries A k) = 0
    rw [zero_smul]
  map_add' F G := WordSeries.ext <| funext fun u => by
    change (F.coeff u + G.coeff u) • (1 : WordSeries A k) = _ + _
    rw [add_smul]
    rfl
  commutes' c := WordSeries.ext <| funext fun u => by
    change (algebraMap k (WordSeries A k) c).coeff u • (1 : WordSeries A k) =
      (algebraMap k (WordSeries A (WordSeries A k)) c).coeff u
    rw [algebraMap_coeff, algebraMap_coeff]
    cases u with
    | nil => simp [wordUnit]
    | cons _ _ => simp [wordUnit]

theorem leftEmb_coeff (F : WordSeries A k) (u : List A) :
    (leftEmb F).coeff u = F.coeff u • (1 : WordSeries A k) := rfl

/-- `y ↦ 1 ⊗ y`. -/
def rightEmb : WordSeries A k →ₐ[k] WordSeries A (WordSeries A k) where
  toFun G := ⟨fun u => if u = [] then G else 0⟩
  map_one' := WordSeries.ext <| funext fun u => by
    change (if u = [] then (1 : WordSeries A k) else 0) = wordUnit (E := WordSeries A k) u
    cases u with
    | nil => simp [wordUnit]
    | cons _ _ => simp [wordUnit]
  map_mul' F G := WordSeries.ext <| funext fun u => by
    change (if u = [] then F * G else 0) =
      ∑ p ∈ wordSplits u, (if p.1 = [] then F else 0) * (if p.2 = [] then G else 0)
    cases u with
    | nil => rw [wordSplits_nil, sum_singleton]; simp
    | cons a u =>
      rw [if_neg (List.cons_ne_nil a u)]
      symm
      refine sum_eq_zero fun p hp => ?_
      rw [mem_wordSplits] at hp
      by_cases h1 : p.1 = []
      · have h2 : p.2 ≠ [] := by
          intro h2; rw [h1, h2] at hp; exact List.cons_ne_nil a u hp.symm
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  map_zero' := WordSeries.ext <| funext fun u => by
    change (if u = [] then (0 : WordSeries A k) else 0) = 0
    split_ifs <;> rfl
  map_add' F G := WordSeries.ext <| funext fun u => by
    change (if u = [] then F + G else 0) = (if u = [] then F else 0) + (if u = [] then G else 0)
    split_ifs <;> simp
  commutes' c := WordSeries.ext <| funext fun u => by
    change (if u = [] then algebraMap k (WordSeries A k) c else 0) =
      (algebraMap k (WordSeries A (WordSeries A k)) c).coeff u
    rw [algebraMap_coeff]
    cases u with
    | nil => simp [wordUnit, Algebra.algebraMap_eq_smul_one]
    | cons _ _ => simp [wordUnit]

theorem rightEmb_coeff (G : WordSeries A k) (u : List A) :
    (rightEmb G).coeff u = if u = [] then G else 0 := rfl

theorem leftEmb_mul_rightEmb_coeff (F G : WordSeries A k) (u : List A) :
    (leftEmb F * rightEmb G).coeff u = F.coeff u • G := by
  rw [mul_coeff, sum_eq_single (u, [])]
  · simp [leftEmb_coeff, rightEmb_coeff]
  · rintro ⟨p, q⟩ hpq hne
    rw [mem_wordSplits] at hpq
    by_cases hq : q = []
    · subst hq; exact absurd (by rw [← hpq, List.append_nil]) hne
    · simp [rightEmb_coeff, hq]
  · intro h; exact (h (mem_wordSplits.2 (List.append_nil u))).elim

theorem rightEmb_mul_leftEmb_coeff (F G : WordSeries A k) (u : List A) :
    (rightEmb G * leftEmb F).coeff u = F.coeff u • G := by
  rw [mul_coeff, sum_eq_single ([], u)]
  · simp [leftEmb_coeff, rightEmb_coeff]
  · rintro ⟨p, q⟩ hpq hne
    rw [mem_wordSplits] at hpq
    by_cases hp : p = []
    · subst hp; exact absurd (by rw [← hpq, List.nil_append]) hne
    · simp [rightEmb_coeff, hp]
  · intro h; exact (h (mem_wordSplits.2 (List.nil_append u))).elim

theorem leftEmb_rightEmb_commute (F G : WordSeries A k) :
    Commute (leftEmb F) (rightEmb G) :=
  WordSeries.ext <| funext fun u => by
    rw [leftEmb_mul_rightEmb_coeff, rightEmb_mul_leftEmb_coeff]

theorem leftEmb_graded : IsGradedAlgHom (leftEmb (A := A) (k := k)) := by
  intro n F
  refine WordSeries.ext (funext fun u => ?_)
  rw [proj_coeff, leftEmb_coeff, leftEmb_coeff, proj_coeff, map_smul, comp_one]
  by_cases hu : u.length ≤ n
  · rw [if_pos hu, if_pos hu, proj_field]
    split_ifs <;> simp
  · rw [if_neg hu, if_neg hu, zero_smul]

theorem rightEmb_graded : IsGradedAlgHom (rightEmb (A := A) (k := k)) := by
  intro n G
  refine WordSeries.ext (funext fun u => ?_)
  rw [proj_coeff, rightEmb_coeff, rightEmb_coeff]
  by_cases hu : u = []
  · subst hu; simp
  · rw [if_neg hu, if_neg hu, map_zero]; split_ifs <;> rfl

/-! ## Coproduct, counit, antipode -/

section Hopf

variable [Fintype A] [DecidableEq A]

omit [Fintype A] in
theorem letter_image_homogeneous (a : A) :
    proj k 1 (leftEmb (single [a] (1 : k)) + rightEmb (single [a] 1)) =
      leftEmb (single [a] (1 : k)) + rightEmb (single [a] 1) := by
  rw [map_add, leftEmb_graded, rightEmb_graded, proj_single, if_pos (by simp)]

/-- The coproduct: the graded algebra map with `Δ(a) = a ⊗ 1 + 1 ⊗ a`. -/
def coproduct : WordSeries A k →ₐ[k] WordSeries A (WordSeries A k) :=
  lift k (fun a => leftEmb (single [a] (1 : k)) + rightEmb (single [a] 1)) letter_image_homogeneous

theorem coproduct_graded : IsGradedAlgHom (coproduct (A := A) (k := k)) :=
  fun n F => lift_graded _ _ n F

theorem coproduct_letter (a : A) :
    coproduct (single [a] (1 : k)) = leftEmb (single [a] 1) + rightEmb (single [a] 1) :=
  lift_single_singleton _ _ a

/-- The counit `F ↦ F_∅`. -/
def counit : WordSeries A k →ₗ[k] k where
  toFun F := F.coeff []
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype A] [DecidableEq A] in
theorem proj_zero_eq (F : WordSeries A k) :
    proj k 0 F = algebraMap k (WordSeries A k) (counit F) := by
  refine WordSeries.ext (funext fun v => ?_)
  rw [proj_coeff, algebraMap_coeff]
  cases v with
  | nil => simp [wordUnit, proj_field, counit]
  | cons a v => simp [wordUnit]

/-- The antipode `S(F)_w = (-1)^{|w|} F_{rev w}`. -/
def antipode : WordSeries A k →ₗ[k] WordSeries A k where
  toFun F := ⟨fun w => (-1 : k) ^ w.length * F.coeff w.reverse⟩
  map_add' F G := WordSeries.ext <| funext fun w => by
    change (-1 : k) ^ w.length * (F.coeff w.reverse + G.coeff w.reverse) = _ + _
    rw [mul_add]; rfl
  map_smul' c F := WordSeries.ext <| funext fun w => by
    change (-1 : k) ^ w.length * (c * F.coeff w.reverse) = c * _
    rw [mul_left_comm]; rfl

omit [Fintype A] [DecidableEq A] in
theorem antipode_coeff (F : WordSeries A k) (w : List A) :
    (antipode F).coeff w = (-1 : k) ^ w.length * F.coeff w.reverse := rfl

/-- The contraction `m ∘ (S ⊗ id)`: `(m_S F)_w = ∑_{uv = w} (-1)^{|u|} F_{rev u}(v)`. -/
def contraction : WordSeries A (WordSeries A k) →ₗ[k] WordSeries A k where
  toFun F := ⟨fun w => ∑ p ∈ wordSplits w, (-1 : k) ^ p.1.length * (F.coeff p.1.reverse).coeff p.2⟩
  map_add' F G := WordSeries.ext <| funext fun w => by
    change ∑ p ∈ wordSplits w, (-1 : k) ^ p.1.length * ((F + G).coeff p.1.reverse).coeff p.2 =
      (∑ p ∈ wordSplits w, (-1 : k) ^ p.1.length * (F.coeff p.1.reverse).coeff p.2) +
        ∑ p ∈ wordSplits w, (-1 : k) ^ p.1.length * (G.coeff p.1.reverse).coeff p.2
    rw [← sum_add_distrib]
    exact sum_congr rfl fun p _ => by rw [add_coeff, add_coeff, mul_add]
  map_smul' c F := WordSeries.ext <| funext fun w => by
    change ∑ p ∈ wordSplits w, (-1 : k) ^ p.1.length * ((c • F).coeff p.1.reverse).coeff p.2 =
      c * ∑ p ∈ wordSplits w, (-1 : k) ^ p.1.length * (F.coeff p.1.reverse).coeff p.2
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by rw [smul_coeff, smul_coeff, smul_eq_mul, mul_left_comm]

omit [Fintype A] [DecidableEq A] in
theorem contraction_coeff (F : WordSeries A (WordSeries A k)) (w : List A) :
    (contraction F).coeff w =
      ∑ p ∈ wordSplits w, (-1 : k) ^ p.1.length * (F.coeff p.1.reverse).coeff p.2 := rfl

omit [Fintype A] [DecidableEq A] in
theorem contraction_left_mul_right (x y : WordSeries A k) :
    contraction (leftEmb x * rightEmb y) = antipode x * y := by
  refine WordSeries.ext (funext fun w => ?_)
  rw [contraction_coeff, mul_coeff]
  refine sum_congr rfl fun p _ => ?_
  rw [leftEmb_mul_rightEmb_coeff, smul_coeff, smul_eq_mul, antipode_coeff, mul_assoc]

/-- A letter times a series: `(a · K)_P = K_{P'}` if `P = a P'`, else `0`. -/
def letterShift (a : A) {R : Type*} [Zero R] (K : List A → R) : List A → R
  | [] => 0
  | b :: P => if b = a then K P else 0

omit [Fintype A] in
theorem single_letter_mul_coeff {R : Type*} [Ring R] (a : A) (r : R) (K : WordSeries A R)
    (P : List A) : (single [a] r * K).coeff P = r * letterShift a K.coeff P := by
  rw [mul_coeff]
  cases P with
  | nil =>
    rw [wordSplits_nil, sum_singleton]
    simp [single_coeff, letterShift]
  | cons b P =>
    by_cases hb : b = a
    · subst hb
      rw [sum_eq_single ([b], P)]
      · simp [single_coeff, letterShift]
      · rintro ⟨u, v⟩ huv hne
        rw [single_coeff, if_neg, zero_mul]
        rintro rfl
        rw [mem_wordSplits] at huv
        exact hne (by simp only [List.singleton_append, List.cons.injEq] at huv; rw [huv.2])
      · intro h; exact (h (mem_wordSplits.2 rfl)).elim
    · rw [letterShift, if_neg hb, mul_zero]
      refine sum_eq_zero fun p hp => ?_
      rw [single_coeff, if_neg, zero_mul]
      intro hp1
      rw [mem_wordSplits, hp1, List.singleton_append, List.cons.injEq] at hp
      exact hb hp.1.symm

omit [Fintype A] in
theorem leftEmb_letter_mul_coeff (a : A) (G : WordSeries A (WordSeries A k)) (P : List A) :
    (leftEmb (single [a] (1 : k)) * G).coeff P = letterShift a G.coeff P := by
  rw [show leftEmb (single [a] (1 : k)) = single [a] (1 : WordSeries A k) by
    refine WordSeries.ext (funext fun u => ?_)
    rw [leftEmb_coeff, single_coeff, single_coeff]
    split_ifs <;> simp, single_letter_mul_coeff, one_mul]

omit [Fintype A] in
theorem rightEmb_letter_mul_coeff (a : A) (G : WordSeries A (WordSeries A k)) (P : List A) :
    (rightEmb (single [a] (1 : k)) * G).coeff P = single [a] (1 : k) * G.coeff P := by
  rw [mul_coeff, sum_eq_single ([], P)]
  · simp [rightEmb_coeff]
  · rintro ⟨u, v⟩ huv hne
    rw [mem_wordSplits] at huv
    by_cases hu : u = []
    · subst hu; exact absurd (by rw [← huv, List.nil_append]) hne
    · rw [rightEmb_coeff, if_neg hu, zero_mul]
  · intro h; exact (h (mem_wordSplits.2 (List.nil_append P))).elim

omit [Fintype A] [DecidableEq A] in
/-- Sums over factorizations as sums over the cut position. -/
theorem sum_wordSplits_eq_sum_range {M : Type*} [AddCommMonoid M] (w : List A)
    (f : List A × List A → M) :
    ∑ p ∈ wordSplits w, f p = ∑ i ∈ range (w.length + 1), f (w.take i, w.drop i) := by
  rw [wordSplits, sum_map, ← Fin.sum_univ_eq_sum_range (fun i => f (w.take i, w.drop i))]
  rfl

/-- **The key cancellation**: `m(S ⊗ id)(Δ(a) · G) = 0` for every letter `a`. -/
theorem contraction_coproduct_letter_mul (a : A) (G : WordSeries A (WordSeries A k)) :
    contraction (coproduct (single [a] (1 : k)) * G) = 0 := by
  refine WordSeries.ext (funext fun w => ?_)
  rw [coproduct_letter, add_mul, map_add, add_coeff, contraction_coeff, contraction_coeff,
    zero_coeff, sum_wordSplits_eq_sum_range, sum_wordSplits_eq_sum_range]
  simp_rw [leftEmb_letter_mul_coeff, rightEmb_letter_mul_coeff, single_letter_mul_coeff, one_mul]
  rw [sum_range_succ', sum_range_succ]
  have hL0 : (-1 : k) ^ (w.take 0).length *
      (letterShift a G.coeff (w.take 0).reverse).coeff (w.drop 0) = 0 := by
    simp [letterShift]
  have hRn : (-1 : k) ^ (w.take w.length).length *
      letterShift a (G.coeff (w.take w.length).reverse).coeff (w.drop w.length) = 0 := by
    simp [letterShift]
  rw [hL0, hRn, add_zero, add_zero, ← sum_add_distrib]
  refine sum_eq_zero fun i hi => ?_
  rw [mem_range] at hi
  have hlen : (w.take i).length = i := by rw [List.length_take]; omega
  have htake : w.take (i + 1) = w.take i ++ [w[i]] := List.take_succ_eq_append_getElem (by omega)
  have hdrop : w.drop i = w[i] :: w.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
  rw [htake, hdrop, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.length_append, hlen, List.length_singleton]
  simp only [letterShift]
  split_ifs with h
  · rw [pow_succ]; ring
  · simp

omit [Fintype A] [DecidableEq A] in
theorem contraction_one :
    contraction (1 : WordSeries A (WordSeries A k)) = 1 := by
  refine WordSeries.ext (funext fun w => ?_)
  rw [contraction_coeff, one_coeff, sum_wordSplits_eq_sum_range, sum_range_succ']
  rw [sum_eq_zero (fun i hi => by
    rw [mem_range] at hi
    rw [one_coeff, wordUnit_of_ne_nil (by
      rw [Ne, List.reverse_eq_nil_iff, ← List.length_eq_zero_iff,
        List.length_take]; omega), zero_coeff, mul_zero]), zero_add]
  simp only [List.take_zero, List.length_nil, pow_zero, one_mul, List.reverse_nil, List.drop_zero,
    one_coeff, wordUnit_nil]

theorem contraction_coproduct_single (w : List A) :
    contraction (coproduct (single w (1 : k))) = if w = [] then 1 else 0 := by
  cases w with
  | nil => rw [single_nil_one, map_one, contraction_one, if_pos rfl]
  | cons a w =>
    rw [single_cons, map_mul, contraction_coproduct_letter_mul, if_neg (List.cons_ne_nil a w)]

omit [Fintype A] [DecidableEq A] in
/-- The contraction only sees the bidegree of the target coefficient. -/
theorem contraction_coeff_proj (F : WordSeries A (WordSeries A k)) (w : List A) :
    (contraction F).coeff w = (contraction (proj k w.length F)).coeff w := by
  rw [contraction_coeff, contraction_coeff]
  refine sum_congr rfl fun p hp => ?_
  rw [mem_wordSplits] at hp
  have hl : p.1.length + p.2.length = w.length := by rw [← hp, List.length_append]
  rw [proj_coeff, List.length_reverse, if_pos (by omega),
    show w.length - p.1.length = p.2.length by omega, ← coeff_eq_proj_coeff]

theorem contraction_coproduct (x : WordSeries A k) :
    contraction (coproduct x) = algebraMap k (WordSeries A k) (counit x) := by
  refine WordSeries.ext (funext fun w => ?_)
  rw [contraction_coeff_proj, coproduct_graded, proj_eq_sum_single, map_sum, map_sum, sum_coeff]
  simp_rw [map_smul, smul_coeff, contraction_coproduct_single]
  rw [algebraMap_coeff]
  cases w with
  | nil =>
    rw [sum_eq_single []]
    · rw [if_pos rfl, one_coeff, wordUnit_nil]; rfl
    · intro w' _ hne; rw [if_neg hne, zero_coeff, smul_zero]
    · intro h; exact (h (mem_wordsOfLength.2 rfl)).elim
  | cons a w =>
    rw [sum_eq_zero (fun w' hw' => by
      have : w' ≠ [] := fun h => by
        rw [h, mem_wordsOfLength] at hw'; simp at hw'
      rw [if_neg this, zero_coeff, smul_zero]), wordUnit_of_ne_nil (List.cons_ne_nil a w),
      smul_zero]

variable (A k) in
/-- **The complete tensor Hopf algebra** `k⟨⟨A⟩⟩`. -/
def freeHopf : CompleteHopfStructure k (WordSeries A k) (WordSeries A (WordSeries A k)) where
  left := leftEmb
  right := rightEmb
  coproduct := coproduct
  left_graded := leftEmb_graded
  right_graded := rightEmb_graded
  coproduct_graded := coproduct_graded
  left_right_commute := leftEmb_rightEmb_commute
  counit := counit
  proj_zero := proj_zero_eq
  antipode := antipode
  antipodeContraction := contraction
  contraction_left_mul_right := contraction_left_mul_right
  contraction_coproduct := contraction_coproduct

theorem isPrimitive_letter (a : A) :
    (freeHopf A k).IsPrimitive (single [a] (1 : k)) := by
  refine ⟨?_, coproduct_letter a⟩
  rw [proj_single, if_neg (by simp)]

end Hopf

/-! ## Countermodels -/

section Countermodels

variable [CharZero k]

/-- The letter-relabelling reversal `a ↦ s · σ(a)` as a graded algebra endomorphism. -/
def letterMap [Fintype A] [DecidableEq A] (σ : A → A) (s : k) :
    WordSeries A k →ₐ[k] WordSeries A k :=
  lift k (fun a => single [σ a] s) fun a => by rw [proj_single, if_pos (by simp)]

omit [CharZero k] in
theorem letterMap_graded [Fintype A] [DecidableEq A] (σ : A → A) (s : k) :
    IsGradedAlgHom (letterMap σ s) := fun n F => lift_graded _ _ n F

omit [CharZero k] in
theorem letterMap_letter [Fintype A] [DecidableEq A] (σ : A → A) (s : k) (a : A) :
    letterMap σ s (single [a] 1) = single [σ a] s := lift_single_singleton _ _ a

omit [CharZero k] in
theorem single_smul_letter [DecidableEq A] (a : A) (c : k) :
    single [a] c = c • single [a] (1 : k) := by
  refine WordSeries.ext (funext fun v => ?_)
  rw [single_coeff, smul_coeff, single_coeff]
  split_ifs <;> simp

/-- The coefficient of `exp(a)` on a word: `1/|w|!` on `a^{|w|}`, zero elsewhere. -/
theorem cexp_letter_coeff [Fintype A] [DecidableEq A] (a : A) (w : List A) :
    (cexp k (single [a] (1 : k))).coeff w =
      if w = List.replicate w.length a then PowerSeries.coeff w.length (PowerSeries.exp k)
      else 0 := by
  have hY : single [a] (1 : k) ∈ filtration k (WordSeries A k) 1 := by
    intro j hj
    rw [proj_single, if_neg (by simp; omega)]
  rw [coeff_eq_proj_coeff, cexp, comp_evalSeries, sum_coeff]
  simp_rw [smul_coeff, single_pow, one_pow, proj_single, List.length_replicate]
  rw [sum_eq_single w.length]
  · rw [if_pos rfl, single_coeff, smul_eq_mul]
    split_ifs <;> simp
  · intro m _ hm
    rw [if_neg (Ne.symm hm), zero_coeff, smul_zero]
  · intro h; exact (h (mem_range.2 (Nat.lt_succ_self _))).elim

/-! ### Sheet twist: an anti-invariant primitive gives a nontrivial fixed signature -/

/-- **§10.1** Exchanging two letters `a ≠ b`, the primitive `X = a - b` is anti-invariant, its
exponential `e^{a-b} ≠ 1` is fixed by the twisted antipode, and `θ(e^X) e^X = 1`. -/
theorem sheetTwist_countermodel [Fintype A] [DecidableEq A] {a b : A} (hab : a ≠ b) :
    let θ := letterMap (Equiv.swap a b) (1 : k)
    let X := single [a] (1 : k) - single [b] 1
    (freeHopf A k).IsOddPrimitive θ X ∧ X ≠ 0 ∧
      (freeHopf A k).IsTwistedFixed θ (cexp k X) ∧ cexp k X ≠ 1 ∧
      θ (cexp k X) * cexp k X = 1 := by
  intro θ X
  have hθ : IsGradedAlgHom θ := letterMap_graded _ _
  have hXp : (freeHopf A k).IsPrimitive X := by
    refine ⟨?_, ?_⟩
    · rw [map_sub, (isPrimitive_letter a).1, (isPrimitive_letter b).1, sub_zero]
    · change coproduct X = leftEmb X + rightEmb X
      rw [map_sub, coproduct_letter, coproduct_letter, map_sub, map_sub]
      abel
  have hθX : θ X = -X := by
    simp only [θ, X, map_sub, letterMap_letter, Equiv.swap_apply_left, Equiv.swap_apply_right]
    abel
  have hX0 : X ≠ 0 := by
    intro h
    have := congrArg (fun F : WordSeries A k => F.coeff [a]) h
    simp [X, single_coeff, hab] at this
  have hfix := (freeHopf A k).cexp_isTwistedFixed_ne_one hθ ⟨hXp, hθX⟩ hX0
  refine ⟨⟨hXp, hθX⟩, hX0, hfix.1, hfix.2, ?_⟩
  rw [algHom_cexp _ hθ, hθX]
  exact cexp_neg_mul_cexp hXp.mem

/-! ### Fixed signatures do not form a group -/

/-- **§10.2** Negating two letters `x ≠ y`, both `e^x` and `e^y` are twisted-antipode fixed but
their product is not, and the bracket of the anti-invariant primitives `x, y` is not
anti-invariant. -/
theorem fixedSignatures_not_group_countermodel [Fintype A] [DecidableEq A] {x y : A}
    (hxy : x ≠ y) :
    let θ := letterMap (id : A → A) (-1 : k)
    (freeHopf A k).IsTwistedFixed θ (cexp k (single [x] 1)) ∧
      (freeHopf A k).IsTwistedFixed θ (cexp k (single [y] 1)) ∧
      ¬ (freeHopf A k).IsTwistedFixed θ (cexp k (single [x] 1) * cexp k (single [y] 1)) ∧
      ¬ (freeHopf A k).IsOddPrimitive θ
        (single [x] (1 : k) * single [y] 1 - single [y] 1 * single [x] 1) := by
  intro θ
  have hθ : IsGradedAlgHom θ := letterMap_graded _ _
  have hodd : ∀ a : A, (freeHopf A k).IsOddPrimitive θ (single [a] (1 : k)) := fun a =>
    ⟨isPrimitive_letter a, by
      rw [show θ (single [a] 1) = single [a] (-1 : k) from letterMap_letter _ _ a,
        single_smul_letter, neg_one_smul]⟩
  have hx := ((freeHopf A k).isTwistedFixed_iff hθ).2 ⟨_, hodd x, rfl⟩
  have hy := ((freeHopf A k).isTwistedFixed_iff hθ).2 ⟨_, hodd y, rfl⟩
  refine ⟨hx, hy, ?_, ?_⟩
  · rw [(freeHopf A k).isTwistedFixed_mul_iff hx hy]
    intro h
    have := congrArg (fun F : WordSeries A k => F.coeff [x, y]) h
    simp only [mul_coeff] at this
    rw [show wordSplits [x, y] = {([], [x, y]), ([x], [y]), ([x, y], [])} by
      ext p
      rw [mem_wordSplits]
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hp
        rcases p with ⟨u, v⟩
        rcases u with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, u⟩⟩⟩ <;> simp_all
      · rintro (h | h | h) <;> subst h <;> rfl] at this
    rw [sum_insert (by simp), sum_insert (by simp), sum_singleton,
      sum_insert (by simp), sum_insert (by simp), sum_singleton] at this
    simp only [cexp_letter_coeff, List.length_nil, List.replicate_zero, if_true,
      List.length_cons, List.cons.injEq, hxy, and_true, if_false, mul_zero, zero_mul,
      add_zero, zero_add, List.replicate_succ] at this
    simp [PowerSeries.coeff_exp] at this
  · rintro ⟨-, hθb⟩
    have hb := CompleteHopfStructure.commutator_parity θ
      (show θ (single [x] 1) = (-1 : k) • single [x] 1 by rw [(hodd x).2, neg_one_smul])
      (show θ (single [y] 1) = (-1 : k) • single [y] 1 by rw [(hodd y).2, neg_one_smul])
    rw [hb, show ((-1 : k) * -1) = 1 by norm_num, one_smul] at hθb
    have h2 : (2 : k) • (single [x] (1 : k) * single [y] 1 - single [y] 1 * single [x] 1) = 0 := by
      rw [two_smul]; nth_rewrite 1 [hθb]; exact neg_add_cancel _
    have := congrArg (fun F : WordSeries A k => F.coeff [x, y]) h2
    simp only [smul_coeff, sub_coeff, single_mul_single, single_coeff, List.singleton_append,
      List.cons.injEq, hxy, hxy.symm, and_true, and_false, if_true, if_false, mul_one,
      sub_zero, smul_eq_mul, zero_coeff] at this
    norm_num at this

end Countermodels

end FreeHopf


end GaloisForLFunctions.HTGeometry
