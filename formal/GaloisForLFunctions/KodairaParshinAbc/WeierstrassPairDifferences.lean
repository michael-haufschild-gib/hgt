import GaloisForLFunctions.HTGeometry.LegendreHalfCoordinates

/-!
# Differences of Weierstrass points and the two-torsion

On a hyperelliptic curve of genus `g` with `2g + 2` Weierstrass points, the difference of two
distinct Weierstrass points is a nonzero two-torsion class of the Jacobian, and uniqueness of
reduced divisors makes the map `{P, P'} ↦ P - P'` injective for `g ≥ 2`.  Counting decides when
it is onto `J[2] ∖ 0`:

  `#{pairs} = C(2g+2, 2) = (g+1)(2g+1)`  versus  `#(J[2] ∖ 0) = 4^g - 1`,

and `(g+1)(2g+1) + 1 = 4^g` holds only for `g = 2` (`15 = 16 - 1`).  So an injective pair-difference
map forces `g ≥ 2`, and it is a bijection exactly in genus two: there every nonzero two-torsion
class is the difference of a unique pair of Weierstrass points.

In genus one the map is not injective.  On the Legendre curve `y² = x(x-1)(x-λ)` the four
Weierstrass points form the two-torsion subgroup itself, and each nonzero two-torsion point is
the difference (equivalently the sum) of exactly two of the six pairs.
-/

namespace GaloisForLFunctions.KodairaParshinAbc

open GaloisForLFunctions.HTGeometry

/-! ## Genus numerology -/

theorem choose_two_weierstrass (g : ℕ) : (2 * g + 2).choose 2 = (g + 1) * (2 * g + 1) := by
  rw [Nat.choose_two_right, show 2 * g + 2 - 1 = 2 * g + 1 by omega,
    show (2 * g + 2) * (2 * g + 1) = 2 * ((g + 1) * (2 * g + 1)) by ring]
  omega

/-- For `g ≥ 3` there are strictly fewer Weierstrass pairs than nonzero two-torsion classes. -/
theorem weierstrass_pairs_lt (g : ℕ) (hg : 3 ≤ g) : (g + 1) * (2 * g + 1) + 1 < 4 ^ g := by
  induction g, hg using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

/-- **The genus-two coincidence**: `C(2g+2, 2) + 1 = 4^g` exactly when `g = 2`. -/
theorem weierstrass_pairs_eq_iff (g : ℕ) : (2 * g + 2).choose 2 + 1 = 4 ^ g ↔ g = 2 := by
  rw [choose_two_weierstrass]
  constructor
  · intro h
    by_contra hg
    rcases Nat.lt_or_ge g 3 with hlt | hge
    · interval_cases g <;> simp_all
    · exact (weierstrass_pairs_lt g hge).ne h
  · rintro rfl
    norm_num

/-- An injection of the Weierstrass pairs into the nonzero two-torsion needs `g ≥ 2`. -/
theorem two_le_of_weierstrass_pairs_le (g : ℕ) (h : (2 * g + 2).choose 2 + 1 ≤ 4 ^ g) :
    2 ≤ g := by
  rw [choose_two_weierstrass] at h
  by_contra hg
  interval_cases g <;> simp_all

/-- **Pair differences in genus `g`.**  Let `W` be a set of `2g + 2` points and `V` a finite set of
`4^g` classes with a distinguished `0`.  If `f` maps the two-element subsets of `W` injectively to
nonzero classes, then `g ≥ 2`, and `f` hits every nonzero class exactly when `g = 2`. -/
theorem weierstrass_pairMap {α V : Type*} [DecidableEq α] [Fintype V] [DecidableEq V] [Zero V]
    {g : ℕ} (W : Finset α) (hW : W.card = 2 * g + 2) (hV : Fintype.card V = 4 ^ g)
    (f : Finset α → V) (hf : Set.InjOn f (W.powersetCard 2))
    (hf0 : ∀ s ∈ W.powersetCard 2, f s ≠ 0) :
    2 ≤ g ∧ (Set.SurjOn f (W.powersetCard 2) {v | v ≠ 0} ↔ g = 2) := by
  classical
  set S := W.powersetCard 2 with hS
  set T : Finset V := Finset.univ.erase 0 with hT
  have hcardS : S.card = (2 * g + 2).choose 2 := by rw [hS, Finset.card_powersetCard, hW]
  have hcardT : T.card + 1 = 4 ^ g := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hV]
    have : 0 < 4 ^ g := by positivity
    omega
  have himg_sub : S.image f ⊆ T := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_erase.mpr ⟨hf0 s hs, Finset.mem_univ _⟩
  have hcard_img : (S.image f).card = S.card := Finset.card_image_of_injOn hf
  have hle : S.card ≤ T.card := hcard_img ▸ Finset.card_le_card himg_sub
  refine ⟨two_le_of_weierstrass_pairs_le g (by omega), ?_⟩
  rw [← weierstrass_pairs_eq_iff, ← hcardS]
  constructor
  · intro hsurj
    have : T ⊆ S.image f := by
      intro v hv
      obtain ⟨s, hs, hfs⟩ := hsurj (Finset.mem_erase.mp hv).1
      exact Finset.mem_image.mpr ⟨s, hs, hfs⟩
    have := Finset.card_le_card this
    omega
  · intro heq
    have hEq : S.image f = T :=
      Finset.eq_of_subset_of_card_le himg_sub (by omega)
    intro v hv
    have : v ∈ S.image f := hEq ▸ Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp this
    exact ⟨s, hs, rfl⟩

/-! ## Genus one: the pair-sum map on an elementary abelian two-group -/

section TwoGroup

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- In a finite group `W` of exponent two, each `t ≠ 0` is the sum of exactly `|W| / 2`
two-element subsets `{x, x + t}`. -/
theorem two_mul_card_pairs_sum_eq {W : Finset G} (hadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W)
    (htwo : ∀ x ∈ W, x + x = 0) {t : G} (ht : t ∈ W) (ht0 : t ≠ 0) :
    2 * ((W.powersetCard 2).filter (fun s => ∑ x ∈ s, x = t)).card = W.card := by
  set P := (W.powersetCard 2).filter (fun s => ∑ x ∈ s, x = t) with hP
  have hne : ∀ x : G, x ≠ x + t := fun x h => ht0 (by
    have := congrArg (· - x) h
    simpa using this.symm)
  have hmap : ∀ x ∈ W, ({x, x + t} : Finset G) ∈ P := by
    intro x hx
    rw [hP, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_pair (hne x)⟩, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · rw [Finset.mem_singleton.mp hy]
        exact hadd _ hx _ ht
    · rw [Finset.sum_pair (hne x)]
      calc x + (x + t) = (x + x) + t := by abel
        _ = t := by rw [htwo x hx, zero_add]
  rw [Finset.card_eq_sum_card_fiberwise hmap, Finset.sum_const_nat (m := 2), mul_comm]
  intro s hs
  rw [hP, Finset.mem_filter, Finset.mem_powersetCard] at hs
  obtain ⟨⟨hsW, hs2⟩, hsum⟩ := hs
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hs2
  rw [Finset.sum_pair huv] at hsum
  have hu : u ∈ W := hsW (Finset.mem_insert_self _ _)
  have hv : v ∈ W := hsW (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hut : u + t = v := by
    rw [← hsum]
    calc u + (u + v) = (u + u) + v := by abel
      _ = v := by rw [htwo u hu, zero_add]
  have hvt : v + t = u := by
    rw [← hsum]
    calc v + (u + v) = (v + v) + u := by abel
      _ = u := by rw [htwo v hv, zero_add]
  have hfib : W.filter (fun x => ({x, x + t} : Finset G) = {u, v}) = {u, v} := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, hx⟩
      rw [← hx]
      exact Finset.mem_insert_self _ _
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hu, by rw [hut]⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨hv, by rw [hvt, Finset.pair_comm]⟩
  rw [hfib, Finset.card_pair huv]

end TwoGroup

/-! ## The Legendre curve -/

section Legendre

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

theorem twoTorsion_finite {lam : L} (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) :
    {T : (LegendreDoubling.curve lam).Point | T + T = 0}.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [LegendreDoubling.ncard_twoTorsion hl0 hl1]; norm_num)

/-- **Genus one is not injective.**  On a smooth Legendre curve each nonzero two-torsion point is
the sum (equivalently, the difference) of exactly two of the six pairs of distinct Weierstrass
points `0, (0,0), (1,0), (λ,0)`. -/
theorem legendre_card_weierstrass_pairs {lam : L} (hl0 : lam ≠ 0) (hl1 : lam ≠ 1)
    {t : (LegendreDoubling.curve lam).Point} (ht : t + t = 0) (ht0 : t ≠ 0) :
    (((twoTorsion_finite hl0 hl1).toFinset.powersetCard 2).filter
        (fun s => ∑ x ∈ s, x = t)).card = 2 ∧
      ((twoTorsion_finite hl0 hl1).toFinset.powersetCard 2).card = 6 := by
  classical
  set W := (twoTorsion_finite hl0 hl1).toFinset with hW
  have hmem : ∀ x, x ∈ W ↔ x + x = 0 := fun x => by simp [hW]
  have hcard : W.card = 4 := by
    rw [hW, ← Set.ncard_eq_toFinset_card _ (twoTorsion_finite hl0 hl1),
      LegendreDoubling.ncard_twoTorsion hl0 hl1]
  have hadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W := by
    intro x hx y hy
    rw [hmem] at hx hy ⊢
    calc x + y + (x + y) = (x + x) + (y + y) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  have htwo : ∀ x ∈ W, x + x = 0 := fun x hx => (hmem x).mp hx
  have h2 := two_mul_card_pairs_sum_eq hadd htwo ((hmem t).mpr ht) ht0
  refine ⟨by omega, ?_⟩
  rw [Finset.card_powersetCard, hcard]
  rfl

omit [CharZero L] in
/-- For two-torsion points the difference is the sum. -/
theorem sub_eq_add_of_two_torsion {lam : L} {x y : (LegendreDoubling.curve lam).Point}
    (hy : y + y = 0) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left hy]

end Legendre

end GaloisForLFunctions.KodairaParshinAbc
