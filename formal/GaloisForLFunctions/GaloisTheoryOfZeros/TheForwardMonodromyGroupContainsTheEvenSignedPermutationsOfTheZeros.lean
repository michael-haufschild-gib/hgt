import GaloisForLFunctions.GaloisTheoryOfZeros.AFinitaryGroupOfSignedPermutationsWithWindowReflectionsContainsTheEvenOnes
import GaloisForLFunctions.GaloisTheoryOfZeros.OneForwardMonodromyMovesTheZerosOfOneParityOfAWindowDownByOne
import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnAroundAForwardBranchTimeIsANontrivialForwardMonodromy
import GaloisForLFunctions.GaloisTheoryOfZeros.EveryForwardMonodromyMovesFinitelyManyZeros

/-!
# The forward monodromy group contains the even signed permutations of the zeros

For every forward time `b` off the branch times the forward monodromy group `G₊(b)` contains

* the signed 3-cycle `p → q → r → p`, `-p → -q → -r → -p` of any three zeros of `H_b` in distinct
  pairs `{z, -z}`, the identity off the three pairs
  (`exists_mem_forwardMonodromy_signedCycle`),
* the double flip `p ↔ -p`, `q ↔ -q` of any two zeros in distinct pairs, the identity off the
  two pairs (`exists_mem_forwardMonodromy_doubleFlip`).

These generate the group `W⁰` of the signed permutations of finite support that are even on the
zeros and even on the pairs, a subgroup of index four of the group `W` of all signed
permutations of finite support. Every element of `G₊(b)` lies in `W`, so `W⁰ ≤ G₊(b) ≤ W`.

Proof. Number the zeros of `H_{1/8}` in the order of the real line; the pair of the zeros number
`j` and `-1 - j` gets the number `pairNumber j`. One forward monodromy moves the zeros with odd
number of a window down by one, another the zeros with even number; as they commute with
`z ↦ -z`, they act on the pairs of the window as the reflections `m ↦ -m - 1` and `m ↦ -m`. With
the finite supports and the sign flip of one pair, `G₊(1/8)` is a windowed signed group, and such
a group contains the signed 3-cycles and the double flips. The transport along a forward path
carries the structure to every base time.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The number of a pair -/

/-- The number of the pair of the zeros number `j` and `-1 - j`: the values `0, -1, 1, -2, 2, …`
for `j = 0, 1, 2, 3, 4, …`. -/
def pairNumber (j : ℤ) : ℤ := if j % 2 = 0 then j / 2 else -((j + 1) / 2)

theorem pairNumber_eq_iff (j j' : ℤ) : pairNumber j = pairNumber j' ↔ j' = j ∨ j' = -1 - j := by
  unfold pairNumber
  split_ifs <;> constructor <;> intro h <;> omega

theorem pairNumber_neg_one_sub (j : ℤ) : pairNumber (-1 - j) = pairNumber j :=
  ((pairNumber_eq_iff j (-1 - j)).mpr (Or.inr rfl)).symm

theorem pairNumber_sub_one_of_odd {j : ℤ} (h : Odd j) :
    pairNumber (j - 1) = -pairNumber j - 1 := by
  obtain ⟨m, rfl⟩ := h
  unfold pairNumber
  split_ifs <;> omega

theorem pairNumber_sub_one_of_even {j : ℤ} (h : Even j) : pairNumber (j - 1) = -pairNumber j := by
  obtain ⟨m, rfl⟩ := h
  unfold pairNumber
  split_ifs <;> omega

theorem le_of_abs_pairNumber_le {j K : ℤ} (h : |pairNumber j| ≤ K) :
    -(2 * K + 1) ≤ j ∧ j ≤ 2 * K := by
  rw [abs_le] at h
  unfold pairNumber at h
  split_ifs at h <;> omega

theorem odd_or_odd_neg_one_sub (j : ℤ) : Odd j ∨ Odd (-1 - j) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | h
  · exact Or.inr ⟨-m - 1, by omega⟩
  · exact Or.inl h

theorem even_or_even_neg_one_sub (j : ℤ) : Even j ∨ Even (-1 - j) := by
  rcases Int.even_or_odd j with h | ⟨m, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨-m - 1, by omega⟩

/-! ## The pairs of the zeros at `1/8` -/

/-- The pairs `{x, -x}` of the zeros of `H_{1/8}` with their numbers. -/
def eighthPairs : PairCoordinate {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0} where
  flip p := fibreNeg ((1 / 8 : ℝ) : ℂ) p
  pair p := pairNumber (zeroIndex p.1)
  flip_flip x := Subtype.ext (neg_neg _)
  pair_eq_iff x y := by
    show pairNumber (zeroIndex x.1) = pairNumber (zeroIndex y.1) ↔
      y = x ∨ y = fibreNeg ((1 / 8 : ℝ) : ℂ) x
    rw [pairNumber_eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext (eq_of_zeroIndex_eq y.2 x.2 h))
      · refine Or.inr (Subtype.ext
          (eq_of_zeroIndex_eq y.2 (fibreNeg ((1 / 8 : ℝ) : ℂ) x).2 ?_))
        rw [h]
        exact (zeroIndex_neg x.2).symm
    · rintro (h | h)
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr (zeroIndex_neg x.2)

/-- **The action on the pairs of a window.** Let `g` commute with `z ↦ -z` and move the zero
number `k` to the zero number `k - 1` for the `k` of a window in a class `S` that contains one
of `j`, `-1 - j` for every `j`. Then `g` acts on the numbers of the pairs of the window as the
map `f` that describes `j ↦ j - 1` on the class. -/
theorem pairNumber_apply_of_class
    {g : Equiv.Perm {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}}
    (hcomm : ∀ x, g (fibreNeg ((1 / 8 : ℝ) : ℂ) x) = fibreNeg ((1 / 8 : ℝ) : ℂ) (g x))
    {N : ℕ} {S : ℤ → Prop} (f : ℤ → ℤ) (hS : ∀ j, S j ∨ S (-1 - j))
    (hf : ∀ j, S j → pairNumber (j - 1) = f (pairNumber j))
    (hg : ∀ p : {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}, -(N : ℤ) ≤ zeroIndex p.1 →
      zeroIndex p.1 ≤ N → S (zeroIndex p.1) → zeroIndex (g p).1 = zeroIndex p.1 - 1)
    (x : {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}) (h1 : -(N : ℤ) ≤ zeroIndex x.1)
    (h2 : zeroIndex x.1 + 1 ≤ N) :
    pairNumber (zeroIndex (g x).1) = f (pairNumber (zeroIndex x.1)) := by
  rcases hS (zeroIndex x.1) with h | h
  · rw [hg x h1 (by omega) h, hf _ h]
  · -- the partner `-x` is in the class
    have e1 : zeroIndex (fibreNeg ((1 / 8 : ℝ) : ℂ) x).1 = -1 - zeroIndex x.1 :=
      zeroIndex_neg x.2
    have e2 : zeroIndex (fibreNeg ((1 / 8 : ℝ) : ℂ) (g x)).1 = -1 - zeroIndex (g x).1 :=
      zeroIndex_neg (g x).2
    have e3 := hg (fibreNeg ((1 / 8 : ℝ) : ℂ) x) (by rw [e1]; omega) (by rw [e1]; omega)
      (by rw [e1]; exact h)
    rw [hcomm, e2, e1] at e3
    rw [← pairNumber_neg_one_sub (zeroIndex (g x).1), e3, hf _ h, pairNumber_neg_one_sub]

/-- **`G₊(1/8)` is a windowed signed group on the pairs of the zeros.** -/
theorem isWindowedSignedGroup_eighth : IsWindowedSignedGroup eighthPairs
    (forwardMonodromy ((1 / 8 : ℝ) : ℂ) eighth_re_pos eighth_not_mem_branchTimes) := by
  have hcomm : ∀ g ∈ forwardMonodromy ((1 / 8 : ℝ) : ℂ) eighth_re_pos
      eighth_not_mem_branchTimes, ∀ x,
      g (fibreNeg ((1 / 8 : ℝ) : ℂ) x) = fibreNeg ((1 / 8 : ℝ) : ℂ) (g x) := fun g hg x =>
    DFunLike.congr_fun (forwardMonodromy_commute_fibreNeg hg) x
  refine ⟨hcomm, fun g hg => finite_setOf_forwardMonodromy_ne hg, fun K => ?_, ?_⟩
  · by_cases hK : 0 ≤ K
    swap
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, fun x hx =>
        absurd ((abs_nonneg _).trans hx) hK⟩
    obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 2 * K + 1 by omega)
    obtain ⟨a, ha, hodd⟩ := exists_mem_forwardMonodromy_odd_sub_one N
    obtain ⟨b, hb, heven⟩ := exists_mem_forwardMonodromy_even_sub_one N
    refine ⟨a, ha, b, hb, fun x hx => ?_⟩
    obtain ⟨hj1, hj2⟩ :=
      le_of_abs_pairNumber_le (show |pairNumber (zeroIndex x.1)| ≤ K from hx)
    exact ⟨pairNumber_apply_of_class (hcomm a ha) (fun m => -m - 1) odd_or_odd_neg_one_sub
        (fun j hj => pairNumber_sub_one_of_odd hj) hodd x (by omega) (by omega),
      pairNumber_apply_of_class (hcomm b hb) (fun m => -m) even_or_even_neg_one_sub
        (fun j hj => pairNumber_sub_one_of_even hj) heven x (by omega) (by omega)⟩
  · obtain ⟨σ, hσ, p, -, hp⟩ :=
      exists_mem_forwardMonodromy_flip eighth_re_pos eighth_not_mem_branchTimes
    exact ⟨σ, hσ, p, hp⟩

/-! ## Every base time -/

/-- **At every base time `G₊` is a windowed signed group on the pairs of the zeros.** The pairs
`{z, -z}` of the zeros of `H_b` have a numbering by the integers for which `G₊(b)` is a windowed
signed group: the numbering at `1/8` carried along a forward path. -/
theorem exists_pairCoordinate_isWindowedSignedGroup {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) :
    ∃ P : PairCoordinate {z : ℂ // complexHeat b z = 0}, (∀ x, P.flip x = fibreNeg b x) ∧
      IsWindowedSignedGroup P (forwardMonodromy b hb₀ hb) := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ :=
    exists_isForwardPath eighth_re_pos hb₀ eighth_not_mem_branchTimes hb
  obtain ⟨φ, hφ⟩ := hγ.exists_fibreEquiv hγ0 hγ1
  have hflip : ∀ x, φ (eighthPairs.flip x) = fibreNeg b (φ x) := fun x =>
    Subtype.ext (hγ.transports_unique (hφ (fibreNeg ((1 / 8 : ℝ) : ℂ) x)) (hφ x).neg)
  exact ⟨eighthPairs.map φ (fun y => fibreNeg b y) hflip, fun _ => rfl,
    isWindowedSignedGroup_eighth.map φ hflip
      (fun g hg => hγ.permCongr_mem_forwardMonodromy hγ0 hγ1 hφ hg)
      (fun g hg x => DFunLike.congr_fun (forwardMonodromy_commute_fibreNeg hg) x)
      (fun g hg => finite_setOf_forwardMonodromy_ne hg)⟩

section Main

variable {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)

/-- **`G₊` contains every signed 3-cycle.** For zeros `p, q, r` of `H_b` in three distinct pairs
`{z, -z}` some `T ∈ G₊(b)` has `T p = q`, `T q = r`, `T r = p` and is the identity off the three
pairs. As `T` commutes with `z ↦ -z`, it is the signed 3-cycle `(p q r)(-p -q -r)`. -/
theorem exists_mem_forwardMonodromy_signedCycle {p q r : {z : ℂ // complexHeat b z = 0}}
    (hpq : q ≠ p) (hpq' : q ≠ fibreNeg b p) (hqr : r ≠ q) (hqr' : r ≠ fibreNeg b q)
    (hpr : r ≠ p) (hpr' : r ≠ fibreNeg b p) :
    ∃ T ∈ forwardMonodromy b hb₀ hb, T p = q ∧ T q = r ∧ T r = p ∧
      ∀ x, x ≠ p → x ≠ fibreNeg b p → x ≠ q → x ≠ fibreNeg b q → x ≠ r → x ≠ fibreNeg b r →
        T x = x := by
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hb₀ hb
  have hne : ∀ {x y : {z : ℂ // complexHeat b z = 0}}, y ≠ x → y ≠ fibreNeg b x →
      P.pair x ≠ P.pair y := fun {x y} h1 h2 h => by
    rcases (P.pair_eq_iff x y).mp h with h' | h'
    · exact h1 h'
    · exact h2 (h'.trans (hP x))
  obtain ⟨T, hT, h1, h2, h3, h4⟩ :=
    hG.hasSignedCycle (hne hpq hpq') (hne hqr hqr') (hne hpr hpr')
  exact ⟨T, hT, h1, h2, h3, fun x a a' c c' d d' =>
    h4 x (hne a a').symm (hne c c').symm (hne d d').symm⟩

/-- **`G₊` contains every double flip.** For zeros `p, q` of `H_b` in two distinct pairs some
`T ∈ G₊(b)` has `T p = -p`, `T q = -q` and is the identity off the two pairs. -/
theorem exists_mem_forwardMonodromy_doubleFlip {p q : {z : ℂ // complexHeat b z = 0}}
    (hpq : q ≠ p) (hpq' : q ≠ fibreNeg b p) :
    ∃ T ∈ forwardMonodromy b hb₀ hb, T p = fibreNeg b p ∧ T q = fibreNeg b q ∧
      ∀ x, x ≠ p → x ≠ fibreNeg b p → x ≠ q → x ≠ fibreNeg b q → T x = x := by
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hb₀ hb
  have hne : ∀ {x y : {z : ℂ // complexHeat b z = 0}}, y ≠ x → y ≠ fibreNeg b x →
      P.pair x ≠ P.pair y := fun {x y} h1 h2 h => by
    rcases (P.pair_eq_iff x y).mp h with h' | h'
    · exact h1 h'
    · exact h2 (h'.trans (hP x))
  obtain ⟨T, hT, h1, h2, h3⟩ := hG.hasDoubleFlip (hne hpq hpq')
  exact ⟨T, hT, h1.trans (hP p), h2.trans (hP q), fun x a a' c c' =>
    h3 x (hne a a').symm (hne c c').symm⟩

end Main

end

end GaloisForLFunctions.GaloisTheoryOfZeros
