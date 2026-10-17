import GaloisForLFunctions.BezoutValuationIncidence.BezoutSelbergDiagonalCoercivityAndHalfDecorrelation

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar V: Chinese Remainder Bézout Periodicity, Sawtooth Defect Calculus, and Master Finite-Prefix Dirichlet Energy Coercivity

This module establishes the exact Chinese Remainder periodicity law for the Bézout successor-incidence
count `bezoutIncidenceCount M d₁ d₂ = #{k ∈ [1, M] : d₁ ∣ k ∧ d₂ ∣ (k + 1)}`, isolates the signed
Bézout sawtooth defect `bezoutSawtoothDefect M d₁ d₂`, and combines the Same-Node and Successor-Node
Selberg decompositions into the **Master Finite-Prefix Dirichlet Energy Coercivity Law**:

* `image_bezoutResidueMap_Icc_eq` & `card_bezoutIntervalSet_period_eq_one`:
  For every shift `A : ℕ` and every coprime pair `d₁, d₂ ≥ 1`, the successor-residue map
  `k ↦ (k % d₁, (k + 1) % d₂)` is a bijection from the contiguous period `[A + 1, A + d₁ * d₂]`
  onto `range d₁ ×ˢ range d₂`, and therefore every contiguous interval `[A + 1, A + d₁ * d₂]` of
  length `d₁ * d₂` contains **exactly one** integer `k` satisfying `d₁ ∣ k ∧ d₂ ∣ (k + 1)`.
* `bezoutIncidenceCount_add_mul`, `bezoutIncidenceCount_eq_div_add_rem`, &
  `div_le_bezoutIncidenceCount_le_div_add_one`:
  For every horizon `M : ℕ` and coprime `d₁, d₂ ≥ 1`:
  `bezoutIncidenceCount M d₁ d₂ = M / (d₁ * d₂) + bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂`,
  with remainder count in `{0, 1}` and sharp floor sandwich
  `M / (d₁ * d₂) ≤ bezoutIncidenceCount M d₁ d₂ ≤ M / (d₁ * d₂) + 1`.
* `abs_bezoutSawtoothDefect_le_one`, `sum_sieveSeq_mul_succ_eq_main_add_sawtooth`, &
  `abs_bezoutSawtoothRemainderForm_le_sq_sum_abs`:
  The Bézout sawtooth defect `δ_Bez(M; d₁, d₂)` lies universally in `[-1, 1]` (and vanishes identically
  when `gcd(d₁, d₂) > 1`), decomposing the successor correlation into the exact Möbius-diagonalized
  main term `M * Q_Bez(N, c)` plus `bezoutSawtoothRemainderForm M N c`.
* `sum_addDiff_sieveSeq_sq_eq_main_sub_defect` &
  `selberg_and_mean_square_le_dirichlet_energy_of_harmonic_eq_zero`:
  Combining the Same-Node Selberg floor-sum identity and the Successor-Node Bézout identity inside
  the discrete Dirichlet energy polarization gives the exact pole-free identity
  `∑_{k=1}^M (s_{N,c}(k+1) - s_{N,c}(k))² = 2 M ∑_{e=2}^N (φ(e) - μ(e)) Y_{N,c}(e)² - 2 R_lcm - 2 R_Bez + s_{N,c}(M+1)² - s_{N,c}(1)²`,
  and on `ker P` (`finiteHarmonicSum N c = 0`), bounds both `M * Q_Sel(N, c)` and
  `∑_{k=1}^M s_{N,c}(k)²` by the additive Dirichlet energy plus the signed sawtooth defects.
-/

/-! ## §1. Sliding-Window Uniqueness and Chinese Remainder Bijection on Contiguous Periods -/

/-- The Bézout successor-incidence set in a general contiguous interval `[A + 1, B]`:
`bezoutIntervalSet A B d₁ d₂ = {k ∈ [A + 1, B] : d₁ ∣ k ∧ d₂ ∣ (k + 1)}`. -/
def bezoutIntervalSet (A B d₁ d₂ : ℕ) : Finset ℕ :=
  (Finset.Icc (A + 1) B).filter (fun k => d₁ ∣ k ∧ d₂ ∣ (k + 1))

@[simp]
theorem mem_bezoutIntervalSet {A B d₁ d₂ k : ℕ} :
    k ∈ bezoutIntervalSet A B d₁ d₂ ↔ (A + 1 ≤ k ∧ k ≤ B) ∧ d₁ ∣ k ∧ d₂ ∣ (k + 1) := by
  simp [bezoutIntervalSet]

@[simp]
theorem mem_bezoutIncidenceSet {M d₁ d₂ k : ℕ} :
    k ∈ bezoutIncidenceSet M d₁ d₂ ↔ (1 ≤ k ∧ k ≤ M) ∧ d₁ ∣ k ∧ d₂ ∣ (k + 1) := by
  simp [bezoutIncidenceSet]

/-- At `A = 0`, `bezoutIntervalSet 0 M d₁ d₂` coincides with `bezoutIncidenceSet M d₁ d₂`. -/
theorem bezoutIntervalSet_zero_eq (M d₁ d₂ : ℕ) :
    bezoutIntervalSet 0 M d₁ d₂ = bezoutIncidenceSet M d₁ d₂ := rfl

/-- If `k₁ < k₂` both satisfy `d₁ ∣ k ∧ d₂ ∣ (k + 1)` with `Nat.Coprime d₁ d₂`, then
`d₁ * d₂ ∣ (k₂ - k₁)` and `k₁ + d₁ * d₂ ≤ k₂`. -/
theorem add_mul_le_of_lt_of_dvd_succ {d₁ d₂ k₁ k₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂)
    (h1 : d₁ ∣ k₁ ∧ d₂ ∣ (k₁ + 1)) (h2 : d₁ ∣ k₂ ∧ d₂ ∣ (k₂ + 1)) (hlt : k₁ < k₂) :
    k₁ + d₁ * d₂ ≤ k₂ := by
  have hdvd1 : d₁ ∣ (k₂ - k₁) := Nat.dvd_sub h2.1 h1.1
  have hdvd2 : d₂ ∣ (k₂ - k₁) := by
    have hsub := Nat.dvd_sub h2.2 h1.2
    have heq : (k₂ + 1) - (k₁ + 1) = k₂ - k₁ := by omega
    rwa [heq] at hsub
  have hdvd : d₁ * d₂ ∣ (k₂ - k₁) := hcop.mul_dvd_of_dvd_of_dvd hdvd1 hdvd2
  have hpos : 0 < k₂ - k₁ := by omega
  have hle : d₁ * d₂ ≤ k₂ - k₁ := Nat.le_of_dvd hpos hdvd
  omega

/-- **Sliding-Window Uniqueness (`card_bezoutIntervalSet_le_one_of_sub_le`):**
For any coprime `d₁, d₂ ≥ 1` and any interval `[A + 1, B]` of length `B - A ≤ d₁ * d₂`,
there is **at most one** integer `k ∈ [A + 1, B]` satisfying `d₁ ∣ k ∧ d₂ ∣ (k + 1)`. -/
theorem card_bezoutIntervalSet_le_one_of_sub_le {A B d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (hlen : B - A ≤ d₁ * d₂) :
    (bezoutIntervalSet A B d₁ d₂).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun k₁ hk₁ k₂ hk₂ => ?_
  rw [mem_bezoutIntervalSet] at hk₁ hk₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsep := add_mul_le_of_lt_of_dvd_succ hcop hk₁.2 hk₂.2 hlt
    omega
  · have hsep := add_mul_le_of_lt_of_dvd_succ hcop hk₂.2 hk₁.2 hgt
    omega

/-- Elementary divisibility of differences from equal remainders: if `a % m = b % m` and `a ≤ b`,
then `m ∣ (b - a)`. -/
theorem dvd_sub_of_mod_eq {m a b : ℕ} (h : a % m = b % m) (hle : a ≤ b) :
    m ∣ (b - a) := by
  have h1 := Nat.div_add_mod a m
  have h2 := Nat.div_add_mod b m
  refine ⟨b / m - a / m, ?_⟩
  rw [Nat.mul_sub]
  omega

/-- The Chinese Remainder successor-residue map `k ↦ (k % d₁, (k + 1) % d₂)`. -/
def bezoutResidueMap (d₁ d₂ k : ℕ) : ℕ × ℕ :=
  (k % d₁, (k + 1) % d₂)

/-- If two naturals `k₁ ≤ k₂` have the same `bezoutResidueMap d₁ d₂` under `Nat.Coprime d₁ d₂`,
then `d₁ * d₂ ∣ (k₂ - k₁)`. -/
theorem mul_dvd_sub_of_bezoutResidueMap_eq {d₁ d₂ k₁ k₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (heq : bezoutResidueMap d₁ d₂ k₁ = bezoutResidueMap d₁ d₂ k₂)
    (hle : k₁ ≤ k₂) :
    d₁ * d₂ ∣ (k₂ - k₁) := by
  unfold bezoutResidueMap at heq
  injection heq with hmod1 hmod2
  have hdvd1 : d₁ ∣ (k₂ - k₁) := dvd_sub_of_mod_eq hmod1 hle
  have hdvd2 : d₂ ∣ (k₂ - k₁) := by
    have hd2 : d₂ ∣ ((k₂ + 1) - (k₁ + 1)) := dvd_sub_of_mod_eq hmod2 (by omega)
    have hsub : (k₂ + 1) - (k₁ + 1) = k₂ - k₁ := by omega
    rwa [hsub] at hd2
  exact hcop.mul_dvd_of_dvd_of_dvd hdvd1 hdvd2

/-- **Injectivity of `bezoutResidueMap` on Any Contiguous Period `[A + 1, A + d₁ * d₂]`:**
For coprime `d₁, d₂ ≥ 1`, `bezoutResidueMap d₁ d₂` is injective on `Finset.Icc (A + 1) (A + d₁ * d₂)`. -/
theorem bezoutResidueMap_injOn_Icc (A : ℕ) {d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) :
    Set.InjOn (bezoutResidueMap d₁ d₂) ↑(Finset.Icc (A + 1) (A + d₁ * d₂)) := by
  intro k₁ hk₁ k₂ hk₂ heq
  rw [Finset.mem_coe, Finset.mem_Icc] at hk₁ hk₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hdvd := mul_dvd_sub_of_bezoutResidueMap_eq hcop heq (le_of_lt hlt)
    have hpos : 0 < k₂ - k₁ := by omega
    have hle := Nat.le_of_dvd hpos hdvd
    omega
  · have hdvd := mul_dvd_sub_of_bezoutResidueMap_eq hcop heq.symm (le_of_lt hgt)
    have hpos : 0 < k₁ - k₂ := by omega
    have hle := Nat.le_of_dvd hpos hdvd
    omega

/-- **Exact Chinese Remainder Bijection on Every Period `[A + 1, A + d₁ * d₂]`:**
The image of `Finset.Icc (A + 1) (A + d₁ * d₂)` under `bezoutResidueMap d₁ d₂` is all of
`(Finset.range d₁) ×ˢ (Finset.range d₂)`. -/
theorem image_bezoutResidueMap_Icc_eq (A : ℕ) {d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    (Finset.Icc (A + 1) (A + d₁ * d₂)).image (bezoutResidueMap d₁ d₂) =
      (Finset.range d₁) ×ˢ (Finset.range d₂) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, _, rfl⟩
    unfold bezoutResidueMap
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩
  · rw [Finset.card_image_of_injOn (bezoutResidueMap_injOn_Icc A hcop),
      Finset.card_product, Finset.card_range, Finset.card_range, Nat.card_Icc]
    omega

/-- **Exact Periodicity Law (`card_bezoutIntervalSet_period_eq_one`):**
For every shift `A : ℕ` and every coprime pair `d₁, d₂ ≥ 1`, the contiguous period
`[A + 1, A + d₁ * d₂]` of length `d₁ * d₂` contains **exactly one** integer `k` satisfying
`d₁ ∣ k ∧ d₂ ∣ (k + 1)`. -/
theorem card_bezoutIntervalSet_period_eq_one (A : ℕ) {d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    (bezoutIntervalSet A (A + d₁ * d₂) d₁ d₂).card = 1 := by
  have hle : (bezoutIntervalSet A (A + d₁ * d₂) d₁ d₂).card ≤ 1 :=
    card_bezoutIntervalSet_le_one_of_sub_le hcop (by omega)
  have hmem : (0, 0) ∈ (Finset.range d₁) ×ˢ (Finset.range d₂) := by
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  rw [← image_bezoutResidueMap_Icc_eq A hcop hd₁ hd₂, Finset.mem_image] at hmem
  rcases hmem with ⟨k, hk, hk0⟩
  unfold bezoutResidueMap at hk0
  injection hk0 with h1 h2
  have hk_mem : k ∈ bezoutIntervalSet A (A + d₁ * d₂) d₁ d₂ := by
    rw [mem_bezoutIntervalSet]
    exact ⟨Finset.mem_Icc.mp hk, Nat.dvd_of_mod_eq_zero h1, Nat.dvd_of_mod_eq_zero h2⟩
  have hpos : 1 ≤ (bezoutIntervalSet A (A + d₁ * d₂) d₁ d₂).card :=
    Finset.card_pos.mpr ⟨k, hk_mem⟩
  omega

/-! ## §2. Exact Division-With-Remainder Formula for `bezoutIncidenceCount` -/

/-- Disjoint union decomposition of `bezoutIncidenceSet (M + d₁ * d₂) d₁ d₂` into the prefix
`[1, M]` and the period `[M + 1, M + d₁ * d₂]`. -/
theorem bezoutIncidenceSet_add_eq_union (M d₁ d₂ : ℕ) :
    bezoutIncidenceSet (M + d₁ * d₂) d₁ d₂ =
      bezoutIncidenceSet M d₁ d₂ ∪ bezoutIntervalSet M (M + d₁ * d₂) d₁ d₂ := by
  ext k
  simp only [mem_bezoutIncidenceSet, Finset.mem_union, mem_bezoutIntervalSet]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd1, hd2⟩
    by_cases hkM : k ≤ M
    · exact Or.inl ⟨⟨h1, hkM⟩, hd1, hd2⟩
    · exact Or.inr ⟨⟨by omega, h2⟩, hd1, hd2⟩
  · rintro (⟨⟨h1, h2⟩, hd1, hd2⟩ | ⟨⟨h1, h2⟩, hd1, hd2⟩)
    · exact ⟨⟨h1, by omega⟩, hd1, hd2⟩
    · exact ⟨⟨by omega, h2⟩, hd1, hd2⟩

/-- **One-Period Step Recurrence (`bezoutIncidenceCount_add_mul`):**
For any `M : ℕ` and coprime `d₁, d₂ ≥ 1`, shifting the horizon `M` by one full Bézout period
`d₁ * d₂` increments `bezoutIncidenceCount` by **exactly `1`**:
`bezoutIncidenceCount (M + d₁ * d₂) d₁ d₂ = bezoutIncidenceCount M d₁ d₂ + 1`. -/
theorem bezoutIncidenceCount_add_mul (M : ℕ) {d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    bezoutIncidenceCount (M + d₁ * d₂) d₁ d₂ = bezoutIncidenceCount M d₁ d₂ + 1 := by
  unfold bezoutIncidenceCount
  rw [bezoutIncidenceSet_add_eq_union]
  have hdisj : Disjoint (bezoutIncidenceSet M d₁ d₂) (bezoutIntervalSet M (M + d₁ * d₂) d₁ d₂) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [mem_bezoutIncidenceSet] at hk1
    rw [mem_bezoutIntervalSet] at hk2
    omega
  rw [Finset.card_union_of_disjoint hdisj, card_bezoutIntervalSet_period_eq_one M hcop hd₁ hd₂]

/-- Multi-period step recurrence: shifting by `q * (d₁ * d₂)` adds `q` to `bezoutIncidenceCount`. -/
theorem bezoutIncidenceCount_add_mul_right (r q : ℕ) {d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    bezoutIncidenceCount (r + d₁ * d₂ * q) d₁ d₂ = bezoutIncidenceCount r d₁ d₂ + q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : r + d₁ * d₂ * (q + 1) = (r + d₁ * d₂ * q) + d₁ * d₂ := by ring
    rw [heq, bezoutIncidenceCount_add_mul _ hcop hd₁ hd₂, ih]
    omega

/-- **Exact Euclidean Division Formula for `bezoutIncidenceCount`
(`bezoutIncidenceCount_eq_div_add_rem`):**
For every horizon `M : ℕ` and every coprime pair `d₁, d₂ ≥ 1`:
`bezoutIncidenceCount M d₁ d₂ = M / (d₁ * d₂) + bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂`,
where the remainder count `bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂` lies in `{0, 1}`! -/
theorem bezoutIncidenceCount_eq_div_add_rem (M : ℕ) {d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    bezoutIncidenceCount M d₁ d₂ =
      M / (d₁ * d₂) + bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂ ∧
    bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂ ≤ 1 := by
  have hdiv : M % (d₁ * d₂) + (d₁ * d₂) * (M / (d₁ * d₂)) = M := Nat.mod_add_div M (d₁ * d₂)
  have hcount : bezoutIncidenceCount M d₁ d₂ =
      bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂ + M / (d₁ * d₂) := by
    conv_lhs => rw [← hdiv]
    exact bezoutIncidenceCount_add_mul_right (M % (d₁ * d₂)) (M / (d₁ * d₂)) hcop hd₁ hd₂
  have hrem_le : M % (d₁ * d₂) ≤ d₁ * d₂ := le_of_lt (Nat.mod_lt M (by positivity))
  have hrem_one : bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂ ≤ 1 :=
    bezoutIncidenceCount_le_one_of_le_mul hrem_le
  exact ⟨by omega, hrem_one⟩

/-- **Sharp Two-Sided Floor Sandwich (`div_le_bezoutIncidenceCount_le_div_add_one`):**
For every `M : ℕ` and every coprime pair `d₁, d₂ ≥ 1`:
`M / (d₁ * d₂) ≤ bezoutIncidenceCount M d₁ d₂ ≤ M / (d₁ * d₂) + 1`. -/
theorem div_le_bezoutIncidenceCount_le_div_add_one (M : ℕ) {d₁ d₂ : ℕ}
    (hcop : Nat.Coprime d₁ d₂) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    M / (d₁ * d₂) ≤ bezoutIncidenceCount M d₁ d₂ ∧
      bezoutIncidenceCount M d₁ d₂ ≤ M / (d₁ * d₂) + 1 := by
  obtain ⟨heq, hrem⟩ := bezoutIncidenceCount_eq_div_add_rem M hcop hd₁ hd₂
  omega

/-! ## §3. The Bézout Sawtooth Defect and Exact Finite-Prefix Decomposition -/

/-- The real-valued Bézout sawtooth defect for `(M, d₁, d₂)`:
`bezoutSawtoothDefect M d₁ d₂ = I_Bez(M; d₁, d₂) - (if gcd(d₁, d₂) = 1 then M / (d₁ d₂) else 0)`. -/
def bezoutSawtoothDefect (M d₁ d₂ : ℕ) : ℝ :=
  (bezoutIncidenceCount M d₁ d₂ : ℝ) -
    if Nat.Coprime d₁ d₂ then (M : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) else 0

/-- For non-coprime `(d₁, d₂)`, `bezoutSawtoothDefect M d₁ d₂ = 0` identically. -/
theorem bezoutSawtoothDefect_eq_zero_of_not_coprime (M : ℕ) {d₁ d₂ : ℕ}
    (hnot : ¬ Nat.Coprime d₁ d₂) :
    bezoutSawtoothDefect M d₁ d₂ = 0 := by
  unfold bezoutSawtoothDefect
  rw [if_neg hnot, (bezoutIncidenceSet_eq_empty_of_not_coprime M hnot).2]
  norm_num

/-- **Universal Unit-Interval Bound on `bezoutSawtoothDefect` (`abs_bezoutSawtoothDefect_le_one`):**
For every `M : ℕ` and every `d₁, d₂ ≥ 1` (whether coprime or not!):
`-1 ≤ bezoutSawtoothDefect M d₁ d₂ ≤ 1` and `|bezoutSawtoothDefect M d₁ d₂| ≤ 1`. -/
theorem abs_bezoutSawtoothDefect_le_one (M : ℕ) {d₁ d₂ : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    -1 ≤ bezoutSawtoothDefect M d₁ d₂ ∧
      bezoutSawtoothDefect M d₁ d₂ ≤ 1 ∧
      |bezoutSawtoothDefect M d₁ d₂| ≤ 1 := by
  by_cases hcop : Nat.Coprime d₁ d₂
  · unfold bezoutSawtoothDefect
    rw [if_pos hcop]
    obtain ⟨heq, hrem⟩ := bezoutIncidenceCount_eq_div_add_rem M hcop hd₁ hd₂
    have hprod_pos : (0 : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by positivity
    have hdiv_mod : (M : ℝ) = ((d₁ : ℝ) * (d₂ : ℝ)) * ((M / (d₁ * d₂) : ℕ) : ℝ) +
        ((M % (d₁ * d₂) : ℕ) : ℝ) := by
      have hnat := (Nat.div_add_mod M (d₁ * d₂)).symm
      exact_mod_cast hnat
    have hmod_lt : ((M % (d₁ * d₂) : ℕ) : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by
      have hlt : M % (d₁ * d₂) < d₁ * d₂ := Nat.mod_lt M (by positivity)
      exact_mod_cast hlt
    have hmod_nonneg : (0 : ℝ) ≤ ((M % (d₁ * d₂) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hfrac_nonneg : 0 ≤ ((M % (d₁ * d₂) : ℕ) : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) :=
      div_nonneg hmod_nonneg (le_of_lt hprod_pos)
    have hfrac_le_one : ((M % (d₁ * d₂) : ℕ) : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) ≤ 1 :=
      (div_le_one hprod_pos).mpr (le_of_lt hmod_lt)
    have hM_div : (M : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) =
        ((M / (d₁ * d₂) : ℕ) : ℝ) + ((M % (d₁ * d₂) : ℕ) : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
      rw [hdiv_mod, add_div, mul_div_cancel_left₀ _ (ne_of_gt hprod_pos)]
    have hcount_real : (bezoutIncidenceCount M d₁ d₂ : ℝ) =
        ((M / (d₁ * d₂) : ℕ) : ℝ) + (bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂ : ℝ) := by
      exact_mod_cast heq
    have hrem_nonneg : (0 : ℝ) ≤ (bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂ : ℝ) :=
      Nat.cast_nonneg _
    have hrem_le_one : (bezoutIncidenceCount (M % (d₁ * d₂)) d₁ d₂ : ℝ) ≤ 1 := by
      exact_mod_cast hrem
    rw [hcount_real, hM_div]
    refine ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · rw [bezoutSawtoothDefect_eq_zero_of_not_coprime M hcop]
    simp

/-- The finite-prefix Bézout sawtooth remainder quadratic form:
`bezoutSawtoothRemainderForm M N c = ∑_{d₁, d₂ ∈ [1, N]} c(d₁) c(d₂) δ_Bez(M; d₁, d₂)`. -/
def bezoutSawtoothRemainderForm (M N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    c p.1 * c p.2 * bezoutSawtoothDefect M p.1 p.2

/-- **Exact Finite-Prefix Bézout–Selberg Decomposition
(`sum_sieveSeq_mul_succ_eq_main_add_sawtooth`):**
For every horizon `M : ℕ`, sieve level `N : ℕ`, and weight `c : ℕ → ℝ`:
`∑_{k=1}^M s_{N,c}(k) s_{N,c}(k+1) = M * Q_Bez(N, c) + bezoutSawtoothRemainderForm M N c`,
where `Q_Bez(N, c) = ∑_{e=1}^N μ(e) Y_{N,c}(e)²` is the exact Möbius-diagonalized form! -/
theorem sum_sieveSeq_mul_succ_eq_main_add_sawtooth (M N : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k * sieveSeq N c (k + 1)) =
      (M : ℝ) * bezoutCoprimeQuadraticForm N c + bezoutSawtoothRemainderForm M N c := by
  rw [sum_sieveSeq_mul_succ_eq_sum_bezoutIncidenceCount, ← Finset.sum_product',
    bezoutCoprimeQuadraticForm, bezoutSawtoothRemainderForm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold bezoutSawtoothDefect
  split_ifs <;> ring

/-- **Unconditional `L¹`-Square Bound on `bezoutSawtoothRemainderForm`
(`abs_bezoutSawtoothRemainderForm_le_sq_sum_abs`):**
Uniformly in all `M : ℕ` (with NO dependence on `M`!):
`|bezoutSawtoothRemainderForm M N c| ≤ (∑_{d=1}^N |c(d)|)²`. -/
theorem abs_bezoutSawtoothRemainderForm_le_sq_sum_abs (M N : ℕ) (c : ℕ → ℝ) :
    |bezoutSawtoothRemainderForm M N c| ≤ (∑ d ∈ Finset.Icc 1 N, |c d|) ^ (2 : ℕ) := by
  unfold bezoutSawtoothRemainderForm
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hle : ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      |c p.1 * c p.2 * bezoutSawtoothDefect M p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), |c p.1| * |c p.2| := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have hd1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
    have hd2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    rw [abs_mul, abs_mul]
    have hdef := (abs_bezoutSawtoothDefect_le_one M hd1 hd2).2.2
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hdef
  refine hle.trans (le_of_eq ?_)
  rw [sq, Finset.sum_mul_sum, Finset.sum_product]

/-! ## §4. Master Finite-Prefix Dirichlet Energy Decomposition & `ker P` Coercivity Law -/

/-- Agreement of `sieveSeq N c` with `sievedDivisorSum N c` on positive integers `k ≥ 1`,
giving the exact Same-Node Selberg decomposition for `sieveSeq N c`:
`∑_{k=1}^M s_{N,c}(k)² = M * selbergTotientDiagonalForm N c - signedLcmFractDefect N M c`. -/
theorem sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect (N M : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k ^ (2 : ℕ)) =
      (M : ℝ) * selbergTotientDiagonalForm N c - signedLcmFractDefect N M c := by
  rw [← sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect N M c]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [sievedDivisorSum_eq_sum_filter_Icc_of_pos N c hk1]
  rfl

/-- **Master Finite-Prefix Dirichlet Energy Decomposition (`sum_addDiff_sieveSeq_sq_eq_main_sub_defect`):**
For every `N ≥ 1`, `M ≥ 1`, and weight `c : ℕ → ℝ`, the additive Dirichlet energy of `sieveSeq N c`
decomposes into the exact pole-free diagonal main term
`2 M ∑_{e=2}^N (φ(e) - μ(e)) Y_{N,c}(e)²`
minus twice the Same-Node and Successor-Node sawtooth defects, plus the boundary telescope
`s_{N,c}(M + 1)² - s_{N,c}(1)²`. -/
theorem sum_addDiff_sieveSeq_sq_eq_main_sub_defect
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) =
      2 * (M : ℝ) *
        (∑ e ∈ Finset.Icc 2 N,
          ((Nat.totient e : ℝ) - moebiusReal e) * (selbergMultiplesCoord N c e) ^ (2 : ℕ)) -
      2 * signedLcmFractDefect N M c -
      2 * bezoutSawtoothRemainderForm M N c +
      sieveSeq N c (M + 1) ^ (2 : ℕ) - sieveSeq N c 1 ^ (2 : ℕ) := by
  have hpol := sum_addDiff_sieveSeq_sq_eq N hM c
  have hsame := sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect N M c
  have hsucc := sum_sieveSeq_mul_succ_eq_main_add_sawtooth M N c
  rw [← selbergSubBezoutQuadraticForm_eq_Icc_two hN c]
  linarith

/-- **Master Finite-Prefix `ker P` Coercivity Law
(`selberg_and_mean_square_le_dirichlet_energy_of_harmonic_eq_zero`):**
For every `N ≥ 1`, `M ≥ 1`, and `ker P` weight `c` (`finiteHarmonicSum N c = 0`), both the
scaled Selberg diagonal `M * Q_Sel(N, c)` and the prefix mean square `∑_{k=1}^M s_{N,c}(k)²` are
bounded unconditionally by the additive Dirichlet energy `∑_{k=1}^M (s_{N,c}(k+1) - s_{N,c}(k))²`
plus the signed Same-Node and Successor-Node sawtooth defects (dropping the non-negative boundary square
`s_{N,c}(M+1)² ≥ 0` in the favorable direction!). -/
theorem selberg_and_mean_square_le_dirichlet_energy_of_harmonic_eq_zero
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0) :
    (M : ℝ) * selbergTotientDiagonalForm N c ≤
      (∑ k ∈ Finset.Icc 1 M, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) +
        2 * signedLcmFractDefect N M c +
        2 * bezoutSawtoothRemainderForm M N c +
        sieveSeq N c 1 ^ (2 : ℕ) ∧
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k ^ (2 : ℕ)) ≤
      (∑ k ∈ Finset.Icc 1 M, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) +
        signedLcmFractDefect N M c +
        2 * bezoutSawtoothRemainderForm M N c +
        sieveSeq N c 1 ^ (2 : ℕ) := by
  have hpol := sum_addDiff_sieveSeq_sq_eq N hM c
  have hsame := sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect N M c
  have hsucc := sum_sieveSeq_mul_succ_eq_main_add_sawtooth M N c
  have hcoerc := (two_mul_bezoutCoprimeQuadraticForm_le_selberg_of_harmonic_eq_zero hN c hker).2
  have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hM_coerc : (M : ℝ) * selbergTotientDiagonalForm N c ≤
      2 * (M : ℝ) * (selbergTotientDiagonalForm N c - bezoutCoprimeQuadraticForm N c) := by
    nlinarith
  have hbd_nonneg : 0 ≤ sieveSeq N c (M + 1) ^ (2 : ℕ) := sq_nonneg _
  constructor <;> linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
