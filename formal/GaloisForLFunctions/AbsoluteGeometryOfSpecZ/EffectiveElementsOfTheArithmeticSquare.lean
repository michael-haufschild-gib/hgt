import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRestrictionToTheFrobeniusGraph
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheGoldenCurveIsABeurlingSystem

/-!
# Effective elements of the arithmetic square

An element of the arithmetic square is **effective** if its necklace coordinates are nonnegative
(`IsEffective`): it is the sequence of point counts `N_k = Σ_{d ∣ k} d π_d` of an object with `π_d`
closed points of degree `d`. Every sequence of nonnegative prime counts is realized
(`ofPrimeCounts`, `coord_ofPrimeCounts`). This file reads three criteria of the programme on the
arithmetic square.

* **Curves and their fakes are elements, `Spec ℤ` is the base.** The point counts of a curve over
  `𝔽_q` are an effective element; so are the counts of the golden datum
  (`exists_effective_golden_not_pure`), which has the functional equation and is not pure.
  Effectivity in the square does not imply purity: counts alone are not enough.
* **Geodesic flows on graphs are effective elements with any spectrum**
  (`exists_effective_closedWalks`): the closed-walk counts `tr(Mᵏ)` of every finite relation lie in
  the square with nonnegative coordinates, whether or not the eigenvalues are exceptional. The
  square does not distinguish them by effectivity.
* **The line over `𝔽_q` is the Teichmüller point `[q]`** (`isEffective_teichmuller_natCast`): its
  components are `qᵏ` and its necklace coordinates the numbers of primitive cyclic words in `q`
  letters, the exact count of the carry-free side.
* **The contact sequence of the square is not an element.** The fixed-point counts of the Witt
  Frobenius on the diagonal are `Λ(n)`, and no element of the square has them as components
  (`not_exists_ghostComponent_eq_vonMangoldt`): `Λ(2) = log 2` is not an integer.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- An element of the arithmetic square is effective if all its necklace coordinates are
nonnegative. -/
def IsEffective (x : ghostRing) : Prop := ∀ d : ℕ, 0 ≤ coord x d

/-- The element with prescribed closed-point counts: `N_n = Σ_{d ∣ n} d π_d`. -/
def ofPrimeCounts (π : ℕ → ℤ) : ghostRing :=
  ⟨fun n => ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * π d, isGhost_of_necklace (b := π) fun _ => rfl⟩

theorem ghostComponent_ofPrimeCounts (π : ℕ → ℤ) (n : ℕ+) :
    ghostComponent n (ofPrimeCounts π) = ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * π d := rfl

theorem coord_zero (x : ghostRing) : coord x 0 = 0 := by
  rw [coord, necklace_eq]
  simp

/-- The necklace coordinates of `ofPrimeCounts π` are `π`. -/
theorem coord_ofPrimeCounts (π : ℕ → ℤ) {d : ℕ} (hd : d ≠ 0) :
    coord (ofPrimeCounts π) d = π d := by
  refine necklace_unique (b := coord (ofPrimeCounts π)) (b' := π) (fun n hn => ?_) d hd
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, Nat.pos_of_ne_zero hn⟩, rfl⟩
  rw [← ghostComponent_eq_sum_coord, ghostComponent_ofPrimeCounts]

/-- Nonnegative prime counts give an effective element. -/
theorem isEffective_ofPrimeCounts (π : ℕ → ℕ) : IsEffective (ofPrimeCounts fun d => (π d : ℤ)) := by
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [coord_zero]
  · rw [coord_ofPrimeCounts _ hd.ne']
    exact Int.natCast_nonneg _

/-! ### Criterion: counts alone are not enough -/

/-- **Effectivity does not imply purity.** The point counts of the golden datum over `𝔽₅` are an
effective element of the arithmetic square; the datum has the functional equation and is not
pure. -/
theorem exists_effective_golden_not_pure :
    ∃ x : ghostRing, IsEffective x ∧
      (∀ k : ℕ+, ((ghostComponent k x : ℤ) : ℝ) = goldenDatum.pointCount k) ∧
      (∀ i, goldenDatum.β (goldenDatum.fePerm i) * goldenDatum.β i = 1) ∧
      ¬ ∀ i, ‖goldenDatum.β i‖ = 1 := by
  obtain ⟨⟨π, hπ⟩, -, hfe, hnp⟩ := goldenDatum_beurling_not_pure
  refine ⟨ofPrimeCounts fun d => (π d : ℤ), isEffective_ofPrimeCounts π, fun k => ?_, hfe, hnp⟩
  rw [hπ k k.pos, ghostComponent_ofPrimeCounts]
  push_cast
  rfl

/-! ### Criterion: geodesic flows on graphs -/

section ClosedWalks

open scoped Classical

variable {α : Type*} [Fintype α]

/-- **Closed-walk counts are effective.** For every finite relation `R`, the numbers of admissible
`k`-periodic sequences are the components of an effective element of the arithmetic square: the
orbits of minimal period `d` are free of length `d`. -/
theorem exists_effective_closedWalks (R : α → α → Prop) :
    ∃ x : ghostRing, IsEffective x ∧
      ∀ k : ℕ+, ghostComponent k x = ((perSeqs R k).card : ℤ) := by
  have hempty : ∀ d : ℕ, 0 < d → primSeqs (fun _ _ : α => False) d = ∅ := by
    intro d hd
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    exact ((mem_primSeqs hd).mp hx).1 0
  have hdvd : ∀ d : ℕ, 0 < d → d ∣ (primSeqs R d).card := by
    intro d hd
    have h := dvd_card_primSeqs_sdiff (R := fun _ _ : α => False) (R' := R) hd
    rwa [hempty d hd, Finset.sdiff_empty] at h
  refine ⟨ofPrimeCounts fun d => (((primSeqs R d).card / d : ℕ) : ℤ),
    isEffective_ofPrimeCounts _, fun k => ?_⟩
  rw [ghostComponent_ofPrimeCounts, card_perSeqs_eq_sum k.pos]
  push_cast
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  exact_mod_cast Nat.mul_div_cancel' (hdvd d hd0)

/-- The full shift on a finite alphabet has `(#α)^k` points of period `k`. -/
theorem card_perSeqs_true {k : ℕ} (hk : 0 < k) :
    (perSeqs (fun _ _ : α => True) k).card = Fintype.card α ^ k := by
  have hall : ∀ w ∈ (Finset.univ : Finset (Fin k → α)),
      Admissible (fun _ _ : α => True) (periodize hk w) := fun _ _ _ => trivial
  rw [card_perSeqs hk, Finset.filter_true_of_mem hall, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]

end ClosedWalks

/-- **The Teichmüller point `[q]` is effective.** Its components `qᵏ` count the periodic points of
the full shift on `q` letters, so its necklace coordinates are the numbers of primitive cyclic
words of length `d`: the exact prime count `Σ_{d ∣ k} d π_d = qᵏ` of the line over `𝔽_q`, which has
no carry. -/
theorem isEffective_teichmuller_natCast (q : ℕ) : IsEffective (teichmuller (q : ℤ)) := by
  obtain ⟨x, hx, hcomp⟩ := exists_effective_closedWalks (α := Fin q) (fun _ _ => True)
  have hxq : x = teichmuller (q : ℤ) := ghostRing_ext fun k => by
    rw [hcomp, card_perSeqs_true k.pos, Fintype.card_fin, ghostComponent_teichmuller]
    push_cast
    rfl
  rw [← hxq]
  exact hx

/-! ### The contact sequence is not an element -/

/-- **The fixed-point counts of the square are not the components of an element of the square.** -/
theorem not_exists_ghostComponent_eq_vonMangoldt :
    ¬ ∃ x : ghostRing, ∀ n : ℕ+, ((ghostComponent n x : ℤ) : ℝ) = Λ (n : ℕ) := by
  rintro ⟨x, hx⟩
  have h2 := hx 2
  have hΛ : Λ ((2 : ℕ+) : ℕ) = Real.log 2 := by
    have : ((2 : ℕ+) : ℕ) = 2 := rfl
    rw [this, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [hΛ] at h2
  -- `0 < log 2 < 1` is not an integer
  have hpos : (0 : ℝ) < ((ghostComponent 2 x : ℤ) : ℝ) := by rw [h2]; exact Real.log_pos (by norm_num)
  have hlt : ((ghostComponent 2 x : ℤ) : ℝ) < 1 := by
    rw [h2]
    have := Real.log_two_lt_d9
    linarith
  have h0 : (0 : ℤ) < ghostComponent 2 x := by exact_mod_cast hpos
  have h1 : ghostComponent 2 x < (1 : ℤ) := by exact_mod_cast hlt
  omega

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
