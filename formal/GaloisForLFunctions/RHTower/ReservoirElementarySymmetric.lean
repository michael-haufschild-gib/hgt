import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic

/-!
# The elementary symmetric reciprocal weight of a reservoir pool

The harmonic allocation law weights an ordered reservoir family by the reciprocal of its product.
Its normalizer is the elementary symmetric function of the reciprocals, and the two-sided estimate

`S^m - C(m,2)·S^{m-1}/W ≤ m!·e_m ≤ S^m`

says that normalizer is the naive `S^m/m!` up to a relative error `O(m²/(W S))`, where `W` is a
lower bound for the pool primes.  Both halves come from the two structural identities

`e_{m+1}(P) = e_{m+1}(P \ p) + x_p e_m(P \ p)`,   `∑_p x_p e_m(P \ p) = (m+1) e_{m+1}(P)`,

the second of which counts each `(m+1)`-set once from each of its elements.  The lower bound is
then an induction in which the repeated-index defect is at most `x_p ≤ 1/W` times the previous
level.
-/

namespace RHTower

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric weight of level `m`. -/
noncomputable def esym (x : ι → ℝ) (P : Finset ι) (m : ℕ) : ℝ :=
  ∑ R ∈ P.powersetCard m, ∏ q ∈ R, x q

omit [DecidableEq ι] in
theorem esym_zero (x : ι → ℝ) (P : Finset ι) : esym x P 0 = 1 := by
  simp [esym]

omit [DecidableEq ι] in
theorem esym_nonneg {x : ι → ℝ} {P : Finset ι} (hx : ∀ p ∈ P, 0 ≤ x p) (m : ℕ) :
    0 ≤ esym x P m := by
  refine Finset.sum_nonneg fun R hR => Finset.prod_nonneg fun q hq => ?_
  exact hx q ((Finset.mem_powersetCard.1 hR).1 hq)

omit [DecidableEq ι] in
theorem esym_mono_subset {x : ι → ℝ} {P Q : Finset ι} (hx : ∀ p ∈ P, 0 ≤ x p) (hQ : Q ⊆ P)
    (m : ℕ) : esym x Q m ≤ esym x P m := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.powersetCard_mono hQ) fun R hR _ => ?_
  exact Finset.prod_nonneg fun q hq => hx q ((Finset.mem_powersetCard.1 hR).1 hq)

/-- **The erase split.**  A level-`(m+1)` set either avoids `p` or contains it. -/
theorem esym_erase_split (x : ι → ℝ) {P : Finset ι} {p : ι} (hp : p ∈ P) (m : ℕ) :
    esym x P (m + 1) = esym x (P.erase p) (m + 1) + x p * esym x (P.erase p) m := by
  classical
  have hnot : p ∉ P.erase p := Finset.notMem_erase p P
  have hins : P = insert p (P.erase p) := (Finset.insert_erase hp).symm
  have hsplit : P.powersetCard (m + 1)
      = (P.erase p).powersetCard (m + 1)
        ∪ ((P.erase p).powersetCard m).image (insert p) := by
    conv_lhs => rw [hins]
    exact Finset.powersetCard_succ_insert hnot m
  have hdisj : Disjoint ((P.erase p).powersetCard (m + 1))
      (((P.erase p).powersetCard m).image (insert p)) := by
    refine Finset.disjoint_left.2 fun R hR hR' => ?_
    obtain ⟨R', hR', rfl⟩ := Finset.mem_image.1 hR'
    have hsub := (Finset.mem_powersetCard.1 hR).1
    exact hnot (hsub (Finset.mem_insert_self p R'))
  rw [esym, hsplit, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image, esym, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun R hR => ?_
    have hpR : p ∉ R := fun h => hnot ((Finset.mem_powersetCard.1 hR).1 h)
    rw [Finset.prod_insert hpR]
  · intro R hR R' hR' heq
    have hpR : p ∉ R := fun h => hnot ((Finset.mem_powersetCard.1 hR).1 h)
    have hpR' : p ∉ R' := fun h => hnot ((Finset.mem_powersetCard.1 hR').1 h)
    have := congrArg (fun s => Finset.erase s p) heq
    simpa [Finset.erase_insert hpR, Finset.erase_insert hpR'] using this

/-- **The level count.**  Summing the erased weight over the pool counts every `(m+1)`-set once
from each of its `m+1` elements. -/
theorem sum_mul_esym_erase (x : ι → ℝ) (P : Finset ι) (m : ℕ) :
    ∑ p ∈ P, x p * esym x (P.erase p) m = ((m : ℝ) + 1) * esym x P (m + 1) := by
  classical
  have hsig1 := Finset.sum_sigma' P (fun p => (P.erase p).powersetCard m)
    (fun p R => x p * ∏ r ∈ R, x r)
  have hsig2 := Finset.sum_sigma' (P.powersetCard (m + 1)) (fun T : Finset ι => T)
    (fun T _p => ∏ r ∈ T, x r)
  have hleft : ∑ p ∈ P, x p * esym x (P.erase p) m
      = ∑ q ∈ P.sigma fun p => (P.erase p).powersetCard m, x q.1 * ∏ r ∈ q.2, x r := by
    rw [← hsig1]
    exact Finset.sum_congr rfl fun p _ => by rw [esym, Finset.mul_sum]
  have hright : ((m : ℝ) + 1) * esym x P (m + 1)
      = ∑ q ∈ (P.powersetCard (m + 1)).sigma fun T => T, ∏ r ∈ q.1, x r := by
    rw [← hsig2, esym, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.1 hT).2]
    push_cast
    ring
  rw [hleft, hright]
  refine Finset.sum_nbij' (i := fun q => (⟨insert q.1 q.2, q.1⟩ : (_ : Finset ι) × ι))
    (j := fun q => (⟨q.2, q.1.erase q.2⟩ : (_ : ι) × Finset ι)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, R⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq ⊢
    have hp : p ∈ P := hq.1
    have hR : R ⊆ P.erase p := hq.2.1
    have hcard : R.card = m := hq.2.2
    have hpR : p ∉ R := fun h => (Finset.notMem_erase p P) (hR h)
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self p R⟩
    · intro q hqm
      rcases Finset.mem_insert.1 hqm with rfl | hqm
      · exact hp
      · exact Finset.mem_of_mem_erase (hR hqm)
    · rw [Finset.card_insert_of_notMem hpR, hcard]
  · rintro ⟨T, p⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq ⊢
    have hT : T ⊆ P := hq.1.1
    have hcard : T.card = m + 1 := hq.1.2
    have hp : p ∈ T := hq.2
    refine ⟨hT hp, ?_, ?_⟩
    · intro q hqm
      exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hqm).1, hT (Finset.mem_of_mem_erase hqm)⟩
    · rw [Finset.card_erase_of_mem hp, hcard]
      omega
  · rintro ⟨p, R⟩ hq
    simp only [Finset.mem_sigma] at hq
    have hpR : p ∉ R := fun h =>
      (Finset.notMem_erase p P) ((Finset.mem_powersetCard.1 hq.2).1 h)
    simp [Finset.erase_insert hpR]
  · rintro ⟨T, p⟩ hq
    simp only [Finset.mem_sigma] at hq
    simp [Finset.insert_erase hq.2]
  · rintro ⟨p, R⟩ hq
    simp only [Finset.mem_sigma] at hq
    have hpR : p ∉ R := fun h =>
      (Finset.notMem_erase p P) ((Finset.mem_powersetCard.1 hq.2).1 h)
    rw [Finset.prod_insert hpR]

/-- **The reservoir recursion.**  The pool mass times a level is the next level with multiplicity
plus the repeated-index defect. -/
theorem poolMass_mul_esym (x : ι → ℝ) (P : Finset ι) (m : ℕ) :
    (∑ p ∈ P, x p) * esym x P (m + 1)
      = ((m : ℝ) + 2) * esym x P (m + 2)
        + ∑ p ∈ P, x p ^ 2 * esym x (P.erase p) m := by
  classical
  have hsplit : ∀ p ∈ P, x p * esym x P (m + 1)
      = x p * esym x (P.erase p) (m + 1) + x p ^ 2 * esym x (P.erase p) m := by
    intro p hp
    rw [esym_erase_split x hp m]
    ring
  rw [Finset.sum_mul, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, sum_mul_esym_erase]
  push_cast
  ring

/-! ## The ordered-block identity -/

/-- **Choosing a block first.**  Splitting a level-`(b+s)` set into a `b`-part and the rest counts
each set `C(b+s,b)` times. -/
theorem sum_prod_mul_esym_sdiff (x : ι → ℝ) (P : Finset ι) (b s : ℕ) :
    ∑ R ∈ P.powersetCard b, (∏ p ∈ R, x p) * esym x (P \ R) s
      = (((b + s).choose b : ℕ) : ℝ) * esym x P (b + s) := by
  classical
  have hsig1 := Finset.sum_sigma' (P.powersetCard b) (fun R => (P \ R).powersetCard s)
    (fun R S => (∏ p ∈ R, x p) * ∏ p ∈ S, x p)
  have hsig2 := Finset.sum_sigma' (P.powersetCard (b + s)) (fun T => T.powersetCard b)
    (fun T _R => ∏ p ∈ T, x p)
  have hleft : ∑ R ∈ P.powersetCard b, (∏ p ∈ R, x p) * esym x (P \ R) s
      = ∑ q ∈ (P.powersetCard b).sigma fun R => (P \ R).powersetCard s,
          (∏ p ∈ q.1, x p) * ∏ p ∈ q.2, x p := by
    rw [← hsig1]
    exact Finset.sum_congr rfl fun R _ => by rw [esym, Finset.mul_sum]
  have hright : (((b + s).choose b : ℕ) : ℝ) * esym x P (b + s)
      = ∑ q ∈ (P.powersetCard (b + s)).sigma fun T => T.powersetCard b, ∏ p ∈ q.1, x p := by
    rw [← hsig2, esym, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
      (Finset.mem_powersetCard.1 hT).2]
  rw [hleft, hright]
  refine Finset.sum_nbij' (i := fun q => (⟨q.1 ∪ q.2, q.1⟩ : (_ : Finset ι) × Finset ι))
    (j := fun q => (⟨q.2, q.1 \ q.2⟩ : (_ : Finset ι) × Finset ι)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨R, S⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq ⊢
    have hR : R ⊆ P := hq.1.1
    have hRcard : R.card = b := hq.1.2
    have hS : S ⊆ P \ R := hq.2.1
    have hScard : S.card = s := hq.2.2
    have hdisj : Disjoint R S := by
      refine Finset.disjoint_left.2 fun a haR haS => ?_
      exact (Finset.mem_sdiff.1 (hS haS)).2 haR
    refine ⟨⟨?_, ?_⟩, ?_, hRcard⟩
    · intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · exact hR ha
      · exact (Finset.mem_sdiff.1 (hS ha)).1
    · rw [Finset.card_union_of_disjoint hdisj, hRcard, hScard]
    · exact Finset.subset_union_left
  · rintro ⟨T, R⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq ⊢
    have hT : T ⊆ P := hq.1.1
    have hTcard : T.card = b + s := hq.1.2
    have hR : R ⊆ T := hq.2.1
    have hRcard : R.card = b := hq.2.2
    refine ⟨⟨fun a ha => hT (hR ha), hRcard⟩, ?_, ?_⟩
    · intro a ha
      have haT : a ∈ T := (Finset.mem_sdiff.1 ha).1
      have haR : a ∉ R := (Finset.mem_sdiff.1 ha).2
      exact Finset.mem_sdiff.2 ⟨hT haT, haR⟩
    · rw [Finset.card_sdiff, Finset.inter_eq_left.2 hR, hTcard, hRcard]
      omega
  · rintro ⟨R, S⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq
    have hS : S ⊆ P \ R := hq.2.1
    have hdisj : Disjoint R S := by
      refine Finset.disjoint_left.2 fun a haR haS => ?_
      exact (Finset.mem_sdiff.1 (hS haS)).2 haR
    simp [Finset.union_sdiff_cancel_left hdisj]
  · rintro ⟨T, R⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq
    have hR : R ⊆ T := hq.2.1
    simp [Finset.union_sdiff_of_subset hR]
  · rintro ⟨R, S⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq
    have hS : S ⊆ P \ R := hq.2.1
    have hdisj : Disjoint R S := by
      refine Finset.disjoint_left.2 fun a haR haS => ?_
      exact (Finset.mem_sdiff.1 (hS haS)).2 haR
    rw [Finset.prod_union hdisj]

/-- The ordered-block sum: choose the first block, then the rest from the complement. -/
noncomputable def orderedFamilySum (x : ι → ℝ) : Finset ι → List ℕ → ℝ
  | _, [] => 1
  | P, b :: bs => ∑ R ∈ P.powersetCard b, (∏ p ∈ R, x p) * orderedFamilySum x (P \ R) bs

/-- The ordered-block multiplicity. -/
def blockMultiplicity : List ℕ → ℕ
  | [] => 1
  | b :: bs => (b + bs.sum).choose b * blockMultiplicity bs

/-- **(50) The ordered-block identity.**  Summing over all ordered families of disjoint blocks of
prescribed sizes gives the level of the total size, with the ordered-block multiplicity. -/
theorem orderedFamilySum_eq (x : ι → ℝ) (P : Finset ι) (bs : List ℕ) :
    orderedFamilySum x P bs = ((blockMultiplicity bs : ℕ) : ℝ) * esym x P bs.sum := by
  classical
  induction bs generalizing P with
  | nil => simp [orderedFamilySum, blockMultiplicity, esym_zero]
  | cons b bs ih =>
      simp only [orderedFamilySum, blockMultiplicity, List.sum_cons]
      have hstep : ∑ R ∈ P.powersetCard b, (∏ p ∈ R, x p) * orderedFamilySum x (P \ R) bs
          = ((blockMultiplicity bs : ℕ) : ℝ)
            * ∑ R ∈ P.powersetCard b, (∏ p ∈ R, x p) * esym x (P \ R) bs.sum := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun R _ => ?_
        rw [ih (P \ R)]
        ring
      rw [hstep, sum_prod_mul_esym_sdiff]
      push_cast
      ring

/-- The ordered-block multiplicity is the multinomial coefficient. -/
theorem blockMultiplicity_spec (bs : List ℕ) :
    (bs.map Nat.factorial).prod * blockMultiplicity bs = (bs.sum).factorial := by
  induction bs with
  | nil => simp [blockMultiplicity]
  | cons b bs ih =>
      simp only [blockMultiplicity, List.map_cons, List.prod_cons, List.sum_cons]
      have hchoose : (b + bs.sum).choose b * (b.factorial * (bs.sum).factorial)
          = (b + bs.sum).factorial := by
        rw [mul_comm b.factorial, ← mul_assoc]
        have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right b bs.sum)
        rw [Nat.add_sub_cancel_left] at this
        rw [mul_comm ((b + bs.sum).choose b) (bs.sum).factorial] at *
        calc (bs.sum).factorial * (b + bs.sum).choose b * b.factorial
            = (b + bs.sum).choose b * b.factorial * (bs.sum).factorial := by ring
          _ = (b + bs.sum).factorial := this
      calc b.factorial * (bs.map Nat.factorial).prod
              * ((b + bs.sum).choose b * blockMultiplicity bs)
          = (b + bs.sum).choose b * (b.factorial
              * ((bs.map Nat.factorial).prod * blockMultiplicity bs)) := by ring
        _ = (b + bs.sum).choose b * (b.factorial * (bs.sum).factorial) := by rw [ih]
        _ = (b + bs.sum).factorial := hchoose

/-! ## The two-sided factorial estimate -/

/-- **(47) upper half.**  The factorial-normalized level never exceeds the naive power. -/
theorem factorial_mul_esym_le {x : ι → ℝ} {P : Finset ι} (hx : ∀ p ∈ P, 0 ≤ x p) (m : ℕ) :
    (m.factorial : ℝ) * esym x P m ≤ (∑ p ∈ P, x p) ^ m := by
  classical
  have hS : 0 ≤ ∑ p ∈ P, x p := Finset.sum_nonneg hx
  induction m with
  | zero => simp [esym_zero]
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [esym]
        rw [Finset.powersetCard_one, Finset.sum_map]
        simp
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hrec := poolMass_mul_esym x P j
        have hdefect : 0 ≤ ∑ p ∈ P, x p ^ 2 * esym x (P.erase p) j := by
          refine Finset.sum_nonneg fun p hp => ?_
          refine mul_nonneg (sq_nonneg _) (esym_nonneg ?_ j)
          exact fun q hq => hx q (Finset.mem_of_mem_erase hq)
        have hstep : ((j : ℝ) + 2) * esym x P (j + 2) ≤ (∑ p ∈ P, x p) * esym x P (j + 1) := by
          rw [hrec]
          linarith
        have hmul : (∑ p ∈ P, x p) * (((j + 1).factorial : ℝ) * esym x P (j + 1))
            ≤ (∑ p ∈ P, x p) * (∑ p ∈ P, x p) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left ih hS
        have hfac : ((j + 2).factorial : ℝ) = ((j : ℝ) + 2) * ((j + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hpos : (0 : ℝ) ≤ ((j + 1).factorial : ℝ) := by positivity
        calc ((j + 2).factorial : ℝ) * esym x P (j + 2)
            = ((j + 1).factorial : ℝ) * (((j : ℝ) + 2) * esym x P (j + 2)) := by
              rw [hfac]; ring
          _ ≤ ((j + 1).factorial : ℝ) * ((∑ p ∈ P, x p) * esym x P (j + 1)) :=
              mul_le_mul_of_nonneg_left hstep hpos
          _ = (∑ p ∈ P, x p) * (((j + 1).factorial : ℝ) * esym x P (j + 1)) := by ring
          _ ≤ (∑ p ∈ P, x p) * (∑ p ∈ P, x p) ^ (j + 1) := hmul
          _ = (∑ p ∈ P, x p) ^ (j + 2) := by ring

/-- **(47) lower half.**  The repeated-index defect costs at most `C(m,2)` times the pool bound. -/
theorem pow_le_factorial_mul_esym {x : ι → ℝ} {P : Finset ι} {cW : ℝ}
    (hx : ∀ p ∈ P, 0 ≤ x p) (hcW0 : 0 ≤ cW) (hcW : ∀ p ∈ P, x p ≤ cW) (m : ℕ) :
    (∑ p ∈ P, x p) ^ (m + 1)
      ≤ ((m + 1).factorial : ℝ) * esym x P (m + 1)
        + (((m + 1).choose 2 : ℕ) : ℝ) * cW * (∑ p ∈ P, x p) ^ m := by
  classical
  have hS : 0 ≤ ∑ p ∈ P, x p := Finset.sum_nonneg hx
  induction m with
  | zero =>
      have h1 : esym x P 1 = ∑ p ∈ P, x p := by
        simp only [esym]
        rw [Finset.powersetCard_one, Finset.sum_map]
        simp
      simp [h1]
  | succ k ih =>
      have hrec := poolMass_mul_esym x P k
      have hdefect : ∑ p ∈ P, x p ^ 2 * esym x (P.erase p) k
          ≤ cW * (((k : ℝ) + 1) * esym x P (k + 1)) := by
        have hterm : ∀ p ∈ P, x p ^ 2 * esym x (P.erase p) k
            ≤ cW * (x p * esym x (P.erase p) k) := by
          intro p hp
          have hnn : 0 ≤ esym x (P.erase p) k :=
            esym_nonneg (fun q hq => hx q (Finset.mem_of_mem_erase hq)) k
          have hsq : x p ^ 2 = x p * x p := sq (x p)
          rw [hsq]
          have : x p * x p * esym x (P.erase p) k = (x p * esym x (P.erase p) k) * x p := by ring
          rw [this, mul_comm cW]
          exact mul_le_mul_of_nonneg_left (hcW p hp) (mul_nonneg (hx p hp) hnn)
        calc ∑ p ∈ P, x p ^ 2 * esym x (P.erase p) k
            ≤ ∑ p ∈ P, cW * (x p * esym x (P.erase p) k) := Finset.sum_le_sum hterm
          _ = cW * ∑ p ∈ P, x p * esym x (P.erase p) k := by rw [Finset.mul_sum]
          _ = cW * (((k : ℝ) + 1) * esym x P (k + 1)) := by rw [sum_mul_esym_erase]
      have hup : ((k + 1).factorial : ℝ) * esym x P (k + 1) ≤ (∑ p ∈ P, x p) ^ (k + 1) :=
        factorial_mul_esym_le hx (k + 1)
      have hmul : (∑ p ∈ P, x p) * (∑ p ∈ P, x p) ^ (k + 1)
          ≤ (∑ p ∈ P, x p) * (((k + 1).factorial : ℝ) * esym x P (k + 1)
            + (((k + 1).choose 2 : ℕ) : ℝ) * cW * (∑ p ∈ P, x p) ^ k) :=
        mul_le_mul_of_nonneg_left ih hS
      have hfac : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hchooseNat : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
        simp [Nat.choose_succ_succ]
        omega
      have hchoose : (((k + 2).choose 2 : ℕ) : ℝ)
          = (((k + 1).choose 2 : ℕ) : ℝ) + ((k : ℝ) + 1) := by
        rw [hchooseNat]
        push_cast
        ring
      have hfacnn : (0 : ℝ) ≤ ((k + 1).factorial : ℝ) := by positivity
      have hkey : (∑ p ∈ P, x p) * (((k + 1).factorial : ℝ) * esym x P (k + 1))
          ≤ ((k + 2).factorial : ℝ) * esym x P (k + 2)
            + ((k : ℝ) + 1) * cW * (∑ p ∈ P, x p) ^ (k + 1) := by
        have hexpand : (∑ p ∈ P, x p) * (((k + 1).factorial : ℝ) * esym x P (k + 1))
            = ((k + 1).factorial : ℝ) * ((∑ p ∈ P, x p) * esym x P (k + 1)) := by ring
        rw [hexpand, hrec]
        have hb : ((k + 1).factorial : ℝ) * (((k : ℝ) + 2) * esym x P (k + 2)
              + ∑ p ∈ P, x p ^ 2 * esym x (P.erase p) k)
            ≤ ((k + 1).factorial : ℝ) * (((k : ℝ) + 2) * esym x P (k + 2)
              + cW * (((k : ℝ) + 1) * esym x P (k + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ hfacnn
          linarith
        refine le_trans hb ?_
        have hsplit : ((k + 1).factorial : ℝ) * (((k : ℝ) + 2) * esym x P (k + 2)
              + cW * (((k : ℝ) + 1) * esym x P (k + 1)))
            = ((k + 2).factorial : ℝ) * esym x P (k + 2)
              + ((k : ℝ) + 1) * cW * (((k + 1).factorial : ℝ) * esym x P (k + 1)) := by
          rw [hfac]; ring
        rw [hsplit]
        have hmulnn : (0 : ℝ) ≤ ((k : ℝ) + 1) * cW := by positivity
        have := mul_le_mul_of_nonneg_left hup hmulnn
        linarith
      calc (∑ p ∈ P, x p) ^ (k + 2)
          = (∑ p ∈ P, x p) * (∑ p ∈ P, x p) ^ (k + 1) := by ring
        _ ≤ (∑ p ∈ P, x p) * (((k + 1).factorial : ℝ) * esym x P (k + 1)
              + (((k + 1).choose 2 : ℕ) : ℝ) * cW * (∑ p ∈ P, x p) ^ k) := hmul
        _ = (∑ p ∈ P, x p) * (((k + 1).factorial : ℝ) * esym x P (k + 1))
              + (((k + 1).choose 2 : ℕ) : ℝ) * cW
                * ((∑ p ∈ P, x p) * (∑ p ∈ P, x p) ^ k) := by ring
        _ ≤ (((k + 2).factorial : ℝ) * esym x P (k + 2)
              + ((k : ℝ) + 1) * cW * (∑ p ∈ P, x p) ^ (k + 1))
              + (((k + 1).choose 2 : ℕ) : ℝ) * cW * (∑ p ∈ P, x p) ^ (k + 1) := by
            have hpow : (∑ p ∈ P, x p) * (∑ p ∈ P, x p) ^ k = (∑ p ∈ P, x p) ^ (k + 1) := by ring
            rw [hpow]
            linarith
        _ = ((k + 2).factorial : ℝ) * esym x P (k + 2)
              + (((k + 2).choose 2 : ℕ) : ℝ) * cW * (∑ p ∈ P, x p) ^ (k + 1) := by
            rw [hchoose]; ring

/-- **(48) Source exclusion is invisible.**  Deleting a small set from the pool changes the mass by
at most its cardinality times the pool bound. -/
theorem sub_sum_sdiff_le {x : ι → ℝ} {P O : Finset ι} {cW : ℝ}
    (hx : ∀ p ∈ P, 0 ≤ x p) (hcW0 : 0 ≤ cW) (hcW : ∀ p ∈ P, x p ≤ cW) :
    0 ≤ (∑ p ∈ P, x p) - ∑ p ∈ P \ O, x p
      ∧ (∑ p ∈ P, x p) - ∑ p ∈ P \ O, x p ≤ (O.card : ℝ) * cW := by
  classical
  have hsub : P ∩ O ⊆ P := Finset.inter_subset_left
  have hset : P \ (P ∩ O) = P \ O := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit : (∑ p ∈ P \ O, x p) + ∑ p ∈ P ∩ O, x p = ∑ p ∈ P, x p := by
    have h := Finset.sum_sdiff (f := x) hsub
    rwa [hset] at h
  have hnn : 0 ≤ ∑ p ∈ P ∩ O, x p :=
    Finset.sum_nonneg fun p hp => hx p (Finset.mem_of_mem_inter_left hp)
  refine ⟨by linarith, ?_⟩
  have hle : ∑ p ∈ P ∩ O, x p ≤ (O.card : ℝ) * cW := by
    calc ∑ p ∈ P ∩ O, x p ≤ ∑ _p ∈ P ∩ O, cW :=
          Finset.sum_le_sum fun p hp => hcW p (Finset.mem_of_mem_inter_left hp)
      _ = ((P ∩ O).card : ℝ) * cW := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (O.card : ℝ) * cW := by
          have hcard : ((P ∩ O).card : ℝ) ≤ (O.card : ℝ) := by
            exact_mod_cast Finset.card_le_card Finset.inter_subset_right
          exact mul_le_mul_of_nonneg_right hcard hcW0
  linarith

end RHTower
