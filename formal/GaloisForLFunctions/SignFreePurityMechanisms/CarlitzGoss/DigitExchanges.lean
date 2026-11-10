import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitCompositions
import Mathlib.GroupTheory.Perm.Basic

/-!
# Digit exchanges and increasing allocations

Exchanging two base-p digit occurrences in the same residue class modulo s
preserves every part's divisibility by `p^s−1`. Moving a larger power from
an earlier part to a later part increases the weight by the position gap
times the value gap, and also increases the reverse-lexicographic vector.

Consequently, greedy and optimal compositions allocate each residue class's
digit powers in increasing order. Every realized residue-content matrix
admits such an increasing allocation, by maximizing weight in its finite fibre.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Relabelling digit occurrences without changing their residue classes preserves content. -/
theorem tokenContent_image_equiv {s : ℕ} {α : Type*} [DecidableEq α]
    (colour : α → ZMod s) (e : Equiv.Perm α) (he : ∀ x, colour (e x) = colour x)
    (S : Finset α) : tokenContent colour (S.image e) = tokenContent colour S := by
  funext h
  have hf : (S.image e).filter (fun x => colour x = h) =
      (S.filter fun x => colour x = h).image e := by
    ext x
    constructor
    · rintro hx
      obtain ⟨hx, hc⟩ := mem_filter.mp hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact mem_image.mpr ⟨y, mem_filter.mpr ⟨hy, (he y).symm.trans hc⟩, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_image.mpr ⟨y, (mem_filter.mp hy).1, rfl⟩,
        (he y).trans (mem_filter.mp hy).2⟩
  simp only [tokenContent, hf, card_image_of_injective _ e.injective]

/-- The change in a finite sum under a transposition is supported at the two exchanged tokens. -/
theorem sum_swap_sub {α : Type*} [DecidableEq α] (f : α → ℤ) (S : Finset α)
    {x y : α} (hxy : x ≠ y) :
    (∑ z ∈ S, f (Equiv.swap x y z)) - ∑ z ∈ S, f z =
      (if x ∈ S then f y - f x else 0) + (if y ∈ S then f x - f y else 0) := by
  have hpoint (z : α) : f (Equiv.swap x y z) - f z =
      (if z = x then f y - f x else 0) + (if z = y then f x - f y else 0) := by
    by_cases hx : z = x
    · subst z
      simp only [Equiv.swap_apply_left, ite_true, if_neg hxy, add_zero]
    · by_cases hy : z = y
      · subst z
        simp only [Equiv.swap_apply_right, if_neg hx, ite_true, zero_add]
      · simp only [Equiv.swap_apply_of_ne_of_ne hx hy, if_neg hx, if_neg hy, sub_self, add_zero]
  rw [← sum_sub_distrib]
  simp only [hpoint, sum_add_distrib, sum_ite_eq']

namespace DigitComposition
variable {p s m : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- Residue-preserving permutations of the digit collection act on its admissible compositions. -/
def relabel (C : DigitComposition p s m S) (hp : 2 ≤ p) (e : Equiv.Perm (Digit p))
    (hS : ∀ x, x ∈ S ↔ e x ∈ S)
    (he : ∀ x, ((e x).1 : ZMod s) = (x.1 : ZMod s)) : DigitComposition p s m S where
  parts := fun i => (C.parts i).image e
  subset := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact (hS y).mp (C.subset i hy)
  disjoint := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨y, hy, heq⟩ := mem_image.mp hxi
    obtain ⟨z, hz, heq'⟩ := mem_image.mp hxj
    have hyz : y = z := e.injective (heq.trans heq'.symm)
    exact disjoint_left.mp (C.disjoint hij) hy (hyz.symm ▸ hz)
  cover := by
    intro x hx
    have hy : e.symm x ∈ S := (hS (e.symm x)).mpr (by simpa only [e.apply_symm_apply] using hx)
    obtain ⟨i, hi⟩ := C.cover (e.symm x) hy
    exact ⟨i, mem_image.mpr ⟨e.symm x, hi, e.apply_symm_apply x⟩⟩
  nonempty := fun i => (C.nonempty i).image e
  divisible := by
    intro i hi
    have hJ := (divisibleContent_tokens_iff (s := s) p hp Prod.fst (C.parts i)).mpr
      ⟨C.nonempty i, C.divisible i hi⟩
    have hc := tokenContent_image_equiv (fun t : Digit p => (t.1 : ZMod s)) e he (C.parts i)
    apply ((divisibleContent_tokens_iff (s := s) p hp Prod.fst ((C.parts i).image e)).mp ?_).2
    rw [hc]
    exact hJ

/-- Exchanging two occurrences with the same residue preserves admissibility. -/
def swapDigits (C : DigitComposition p s m S) (hp : 2 ≤ p) {x y : Digit p}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : (x.1 : ZMod s) = (y.1 : ZMod s)) :
    DigitComposition p s m S :=
  C.relabel hp (Equiv.swap x y)
    (fun z => by
      rw [Equiv.apply_swap_eq_self (v := fun t : Digit p => t ∈ S)
        (propext (iff_of_true hx hy)) z])
    (Equiv.apply_swap_eq_self (v := fun t : Digit p => (t.1 : ZMod s)) hxy)

/-- The residue-content matrix of a digit composition. -/
def content (C : DigitComposition p s m S) : Fin m → ZMod s → ℤ :=
  fun i => tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.parts i)

theorem relabel_content (C : DigitComposition p s m S) (hp : 2 ≤ p)
    (e : Equiv.Perm (Digit p)) (hS : ∀ x, x ∈ S ↔ e x ∈ S)
    (he : ∀ x, ((e x).1 : ZMod s) = (x.1 : ZMod s)) :
    (C.relabel hp e hS he).content = C.content := by
  funext i
  exact tokenContent_image_equiv (fun t : Digit p => (t.1 : ZMod s)) e he (C.parts i)

theorem swapDigits_content (C : DigitComposition p s m S) (hp : 2 ≤ p)
    {x y : Digit p} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : (x.1 : ZMod s) = (y.1 : ZMod s)) :
    (C.swapDigits hp hx hy hxy).content = C.content :=
  C.relabel_content hp _ _ _

/-- Maximal weight among compositions with the same residue-content matrix. -/
def IsContentOptimal (C : DigitComposition p s m S) : Prop :=
  ∀ D : DigitComposition p s m S, D.content = C.content → D.weight ≤ C.weight

theorem swapDigits_value_sub (C : DigitComposition p s m S) (hp : 2 ≤ p)
    {x y : Digit p} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : (x.1 : ZMod s) = (y.1 : ZMod s)) (hne : x ≠ y) (k : Fin m) :
    (C.swapDigits hp hx hy hxy).value k - C.value k =
      (if x ∈ C.parts k then (p : ℤ) ^ y.1 - (p : ℤ) ^ x.1 else 0) +
        (if y ∈ C.parts k then (p : ℤ) ^ x.1 - (p : ℤ) ^ y.1 else 0) := by
  change (∑ z ∈ (C.parts k).image (Equiv.swap x y), (p : ℤ) ^ z.1) -
    ∑ z ∈ C.parts k, (p : ℤ) ^ z.1 = _
  rw [sum_image]
  · exact sum_swap_sub (fun z : Digit p => (p : ℤ) ^ z.1) (C.parts k) hne
  · intro a _ b _ h
    exact (Equiv.swap x y).injective h

omit [NeZero s] in
/-- Membership of an assigned digit detects its unique part. -/
theorem mem_part_iff (C : DigitComposition p s m S) {x : Digit p} {i : Fin m}
    (hx : x ∈ C.parts i) (k : Fin m) : x ∈ C.parts k ↔ k = i := by
  constructor
  · intro hk
    by_contra hki
    exact disjoint_left.mp (C.disjoint hki) hk hx
  · rintro rfl
    exact hx

/-- Swapping earlier and later digits changes the weight by the index gap times the value gap. -/
theorem swapDigits_weight_sub (C : DigitComposition p s m S) (hp : 2 ≤ p)
    {i j : Fin m} (hij : i ≠ j) {x y : Digit p}
    (hx : x ∈ C.parts i) (hy : y ∈ C.parts j)
    (hxy : (x.1 : ZMod s) = (y.1 : ZMod s)) :
    (C.swapDigits hp (C.subset i hx) (C.subset j hy) hxy).weight - C.weight =
      ((j.val : ℤ) - (i.val : ℤ)) * ((p : ℤ) ^ x.1 - (p : ℤ) ^ y.1) := by
  have hne : x ≠ y := by
    intro he
    exact disjoint_left.mp (C.disjoint hij) hx (he.symm ▸ hy)
  simp only [weight, ← sum_sub_distrib, ← mul_sub]
  simp only [C.swapDigits_value_sub hp _ _ hxy hne, C.mem_part_iff hx,
    C.mem_part_iff hy, mul_add, mul_ite, mul_zero, sum_add_distrib,
    sum_ite_eq', mem_univ, ite_true, Nat.cast_add, Nat.cast_one]
  ring

/-- Each residue class's digit powers increase from earlier parts to later parts. -/
def TauMonotone (C : DigitComposition p s m S) : Prop :=
  ∀ i j : Fin m, i < j → ∀ x ∈ C.parts i, ∀ y ∈ C.parts j,
    (x.1 : ZMod s) = (y.1 : ZMod s) → x.1 ≤ y.1

theorem IsContentOptimal.tauMonotone {C : DigitComposition p s m S} (hp : 2 ≤ p)
    (hC : C.IsContentOptimal) : C.TauMonotone := by
  intro i j hij x hx y hy hxy
  by_contra hle
  have hpow : (p : ℤ) ^ y.1 < (p : ℤ) ^ x.1 :=
    pow_lt_pow_right₀ (by exact_mod_cast (show 1 < p by omega)) (lt_of_not_ge hle)
  have hidx : (i.val : ℤ) < (j.val : ℤ) := by
    exact_mod_cast (show i.val < j.val from hij)
  have hpos := mul_pos (sub_pos.mpr hidx) (sub_pos.mpr hpow)
  have he := C.swapDigits_weight_sub hp (ne_of_lt hij) hx hy hxy
  have ho := hC (C.swapDigits hp (C.subset i hx) (C.subset j hy) hxy)
    (C.swapDigits_content hp _ _ hxy)
  linarith only [he, ho, hpos]

theorem IsOptimal.tauMonotone {C : DigitComposition p s m S} (hp : 2 ≤ p)
    (hC : C.IsOptimal) : C.TauMonotone :=
  IsContentOptimal.tauMonotone hp (fun D _ => hC D)

/-- Every realized residue-content matrix has an increasing allocation of its digit powers. -/
theorem exists_tauMonotone_same_content (C : DigitComposition p s m S) (hp : 2 ≤ p) :
    ∃ D : DigitComposition p s m S, D.content = C.content ∧ D.TauMonotone := by
  classical
  letI := Fintype.ofFinite (DigitComposition p s m S)
  let F := univ.filter fun D : DigitComposition p s m S => D.content = C.content
  have hF : F.Nonempty := ⟨C, mem_filter.mpr ⟨mem_univ C, rfl⟩⟩
  obtain ⟨D, hD, hmax⟩ := F.exists_max_image (fun D => D.weight) hF
  have hDc : D.content = C.content := (mem_filter.mp hD).2
  refine ⟨D, hDc, IsContentOptimal.tauMonotone hp ?_⟩
  intro E hE
  exact hmax E (mem_filter.mpr ⟨mem_univ E, hE.trans hDc⟩)

omit [NeZero s] in
/-- A larger value at the last differing position gives a larger reverse-lexicographic vector. -/
theorem reverseValues_lt_of_agree_above {C D : DigitComposition p s m S} {j : Fin m}
    (he : ∀ k, j < k → C.value k = D.value k) (hj : C.value j < D.value j) :
    C.reverseValues < D.reverseValues := by
  change Pi.Lex (· < ·) (· < ·)
    (fun i : Fin m => C.value i.rev) (fun i : Fin m => D.value i.rev)
  refine ⟨j.rev, ?_, ?_⟩
  · intro k hk
    exact he k.rev (Fin.lt_rev_iff.mp hk)
  · simpa only [Fin.rev_rev] using hj

theorem IsGreedy.tauMonotone {C : DigitComposition p s m S} (hp : 2 ≤ p)
    (hC : C.IsGreedy) : C.TauMonotone := by
  intro i j hij x hx y hy hxy
  by_contra hle
  have hne : x ≠ y := by
    intro he
    exact disjoint_left.mp (C.disjoint (ne_of_lt hij)) hx (he.symm ▸ hy)
  have hpow : (p : ℤ) ^ y.1 < (p : ℤ) ^ x.1 :=
    pow_lt_pow_right₀ (by exact_mod_cast (show 1 < p by omega)) (lt_of_not_ge hle)
  let D := C.swapDigits hp (C.subset i hx) (C.subset j hy) hxy
  have hv (k : Fin m) := C.swapDigits_value_sub hp (C.subset i hx) (C.subset j hy) hxy hne k
  have he : ∀ k, j < k → C.value k = D.value k := by
    intro k hk
    have hki : k ≠ i := ne_of_gt (hij.trans hk)
    have hkj : k ≠ j := ne_of_gt hk
    have hh := hv k
    simp only [C.mem_part_iff hx, C.mem_part_iff hy, if_neg hki, if_neg hkj, add_zero] at hh
    exact (sub_eq_zero.mp hh).symm
  have hj : C.value j < D.value j := by
    have hh := hv j
    simp only [C.mem_part_iff hx, C.mem_part_iff hy, if_neg (ne_of_gt hij),
      ite_true, zero_add] at hh
    exact sub_pos.mp (hh.symm ▸ sub_pos.mpr hpow)
  exact (not_lt_of_ge (hC D)) (reverseValues_lt_of_agree_above he hj)

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.tauMonotone
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsGreedy.tauMonotone

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_tauMonotone_same_content
