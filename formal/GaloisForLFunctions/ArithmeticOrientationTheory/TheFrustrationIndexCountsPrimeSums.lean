import GaloisForLFunctions.ArithmeticOrientationTheory.TheFrustrationIndexOfThePrimeTriangle

/-!
# The frustration index counts prime sums

When does switching fail to remove any frustration?  For a symmetric coupling `c` and a sign
vector `s` with negative set `S`, switching by `s` trades the anti-aligned overlaps across the cut
`(S, Sᶜ)` for the aligned ones (`misalignedCost_signVector`):

    misaligned(s) = misaligned(1) + 2 (aligned across S − anti-aligned across S),

for the count and for the mass alike.  Hence

* **Cut dominance** (`frustrationIndex_eq_iff_cutDominated`,
  `frustrationMass_eq_iff_massCutDominated`): the frustration index equals the number of positive
  overlaps iff across every cut the aligned overlaps are at least as many as the anti-aligned ones;
  the same for the mass with weights `|c|`.
* **Sparse frustration is rigid** (`cutDominated_of_sparse`): if the positive overlaps lie on a
  symmetric relation of degree `≤ D`, every other overlap is negative, and `4D ≤ n`, then no
  switching helps.

For the odd Weil ledger with a positive archimedean–polar weight the archimedean kernel is
strictly decreasing (`weilKernel_strictAnti`), so every overlap off a prime sum is strictly aligned
(`oddFold_neg_of_not_primeSum`).  Therefore:

* **The frustration index is the prime-sum count** (`frustrationIndex_oddWeilLedger_of_sparse`):
  on a sample whose prime-sum pairs have degree `≤ n/4`, the frustration index is the number of
  anti-aligned prime-sum overlaps.
* **The matched family** (`frustrationIndex_matchedPos`): for a set `Q` of primes `≥ 5`, the
  sample `½ log(3q/2), ½ log(2q/3)` (`q ∈ Q`) has prime sums exactly on the matched pairs, and for
  every small archimedean–polar weight its frustration index is exactly `2|Q|`.  The sample lies in
  `(0, ½ log(3 max Q / 2)]` (`matchedPos_le`), so the frustration index on the aperture `(0, A]`
  is unbounded and reaches twice the number of primes in `[5, ⅔ e^{2A}]`
  (`exists_frustrationIndex_ge`).

The frustration of the odd ledger is thus a count of prime sums of the sample: zero on the lattice
and on generic samples, `2` on the prime triangle, `2|Q|` on matched samples, and never removable by
a switching once the prime sums are sparse.
-/

open Finset ArithmeticFunction Filter Topology

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Switching across a cut -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The misaligned cost of a sign vector with weight `g`: `Σ_{i ≠ j, s_i s_j c_ij > 0} g(c_ij)`. -/
def misalignedCost (s : ι → ℝ) (g : ℝ → ℝ) (c : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ 0 < s i * s j * c i j then g (c i j) else 0

/-- The `g`-weight of the overlaps from `S` to `Sᶜ` whose coupling satisfies `P`. -/
def cutWeight (S : Finset ι) (P : ℝ → Prop) [DecidablePred P] (g : ℝ → ℝ) (c : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, if P (c i j) then g (c i j) else 0

/-- **Cut dominance**: across every cut the aligned overlaps are at least as many as the
anti-aligned ones. -/
def CutDominated (c : ι → ι → ℝ) : Prop :=
  ∀ S : Finset ι, cutWeight S (fun t => 0 < t) (fun _ => 1) c ≤ cutWeight S (fun t => t < 0) (fun _ => 1) c

/-- **Mass cut dominance**: across every cut the aligned mass is at least the anti-aligned mass. -/
def MassCutDominated (c : ι → ι → ℝ) : Prop :=
  ∀ S : Finset ι, cutWeight S (fun t => 0 < t) abs c ≤ cutWeight S (fun t => t < 0) abs c

theorem misalignedCount_eq_cost (s : ι → ℝ) (c : ι → ι → ℝ) :
    (misalignedCount s c : ℝ) = misalignedCost s (fun _ => 1) c := by
  unfold misalignedCount misalignedCost
  rw [card_filter, Nat.cast_sum, ← univ_product_univ, sum_product]
  push_cast
  rfl

theorem misalignedMass_eq_cost (s : ι → ℝ) (c : ι → ι → ℝ) :
    misalignedMass s c = misalignedCost s abs c := rfl

/-- The negative set of a sign vector. -/
def negSet (s : ι → ℝ) : Finset ι := univ.filter fun i => s i < 0

/-- The sign vector switching exactly the points of `S`. -/
def cutSign (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then -1 else 1

omit [Fintype ι] in
theorem isSignVector_cutSign (S : Finset ι) : IsSignVector (cutSign S) := fun i => by
  unfold cutSign; split_ifs <;> norm_num

theorem negSet_cutSign (S : Finset ι) : negSet (cutSign S) = S := by
  ext i
  simp only [negSet, cutSign, mem_filter, mem_univ, true_and]
  split_ifs with h <;> simp [h]

/-- The pointwise switching identity for one ordered pair. -/
theorem switch_term {a b t : ℝ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (g : ℝ → ℝ) (hij : Prop)
    [Decidable hij] :
    (if hij ∧ 0 < a * b * t then g t else 0) =
      (if hij ∧ 0 < 1 * 1 * t then g t else 0) +
      (if hij ∧ a < 0 ∧ ¬ b < 0 then (if t < 0 then g t else 0) - (if 0 < t then g t else 0)
        else 0) +
      (if hij ∧ b < 0 ∧ ¬ a < 0 then (if t < 0 then g t else 0) - (if 0 < t then g t else 0)
        else 0) := by
  by_cases h : hij
  · rcases sq_eq_one_iff.1 ha with rfl | rfl <;> rcases sq_eq_one_iff.1 hb with rfl | rfl <;>
      norm_num [h]
  · simp [h]

/-- **Switching across a cut**: for a symmetric coupling and a sign vector with negative set `S`,
`misaligned(s) = misaligned(1) + 2 (aligned across S − anti-aligned across S)`, for every weight. -/
theorem misalignedCost_signVector {s : ι → ℝ} (hs : IsSignVector s) {c : ι → ι → ℝ}
    (hc : IsSymmetricCoupling c) (g : ℝ → ℝ) :
    misalignedCost s g c = misalignedCost (fun _ => 1) g c +
      2 * (cutWeight (negSet s) (fun t => t < 0) g c - cutWeight (negSet s) (fun t => 0 < t) g c) := by
  set S := negSet s
  have hcut : ∀ P : ℝ → Prop, ∀ [DecidablePred P],
      ∑ i, ∑ j, (if i ≠ j ∧ s i < 0 ∧ ¬ s j < 0 then (if P (c i j) then g (c i j) else 0) else 0) =
        cutWeight S P g c := by
    intro P _
    unfold cutWeight
    rw [show S = univ.filter (fun i => s i < 0) from rfl, compl_filter, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_filter]
    split_ifs with hi
    · refine sum_congr rfl fun j _ => ?_
      by_cases hj : s j < 0
      · simp [hj]
      · have hij : i ≠ j := fun e => hj (e ▸ hi)
        simp [hj, hij, hi]
    · exact sum_eq_zero fun j _ => by simp [hi]
  have hsplit : ∀ i j, (if i ≠ j ∧ 0 < s i * s j * c i j then g (c i j) else 0) =
      (if i ≠ j ∧ 0 < 1 * 1 * c i j then g (c i j) else 0) +
      ((if i ≠ j ∧ s i < 0 ∧ ¬ s j < 0 then (if c i j < 0 then g (c i j) else 0) else 0) -
        (if i ≠ j ∧ s i < 0 ∧ ¬ s j < 0 then (if 0 < c i j then g (c i j) else 0) else 0)) +
      ((if j ≠ i ∧ s j < 0 ∧ ¬ s i < 0 then (if c j i < 0 then g (c j i) else 0) else 0) -
        (if j ≠ i ∧ s j < 0 ∧ ¬ s i < 0 then (if 0 < c j i then g (c j i) else 0) else 0)) := by
    intro i j
    rw [switch_term (hs i) (hs j) g (i ≠ j), hc j i]
    congr 1
    · congr 1
      split_ifs <;> simp
    · have : (j ≠ i ∧ s j < 0 ∧ ¬ s i < 0) ↔ (i ≠ j ∧ s j < 0 ∧ ¬ s i < 0) :=
        ⟨fun h => ⟨Ne.symm h.1, h.2⟩, fun h => ⟨Ne.symm h.1, h.2⟩⟩
      simp only [this]
      split_ifs <;> simp
  unfold misalignedCost
  simp_rw [hsplit, sum_add_distrib, sum_sub_distrib]
  rw [hcut (fun t => t < 0), hcut (fun t => 0 < t), sum_comm (f := fun i j =>
      if j ≠ i ∧ s j < 0 ∧ ¬ s i < 0 then (if c j i < 0 then g (c j i) else 0) else 0),
    sum_comm (f := fun i j =>
      if j ≠ i ∧ s j < 0 ∧ ¬ s i < 0 then (if 0 < c j i then g (c j i) else 0) else 0),
    hcut (fun t => t < 0), hcut (fun t => 0 < t)]
  ring

/-- **The frustration index is the positive-overlap count iff every cut is aligned-dominated.** -/
theorem frustrationIndex_eq_iff_cutDominated {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) :
    frustrationIndex c = misalignedCount (fun _ => 1) c ↔ CutDominated c := by
  constructor
  · intro h S
    have h1 := frustrationIndex_le (isSignVector_cutSign S) c
    rw [h] at h1
    have h2 : (misalignedCount (fun _ => (1 : ℝ)) c : ℝ) ≤ misalignedCount (cutSign S) c := by
      exact_mod_cast h1
    rw [misalignedCount_eq_cost, misalignedCount_eq_cost,
      misalignedCost_signVector (isSignVector_cutSign S) hc, negSet_cutSign] at h2
    linarith
  · intro hd
    refine le_antisymm (frustrationIndex_le isSignVector_one c) ?_
    obtain ⟨s, hs, hseq⟩ := frustrationIndex_mem c
    rw [← hseq]
    have h2 : (misalignedCount (fun _ => (1 : ℝ)) c : ℝ) ≤ misalignedCount s c := by
      rw [misalignedCount_eq_cost, misalignedCount_eq_cost, misalignedCost_signVector hs hc]
      linarith [hd (negSet s)]
    exact_mod_cast h2

/-- **The frustration mass is the positive mass iff every cut is mass-dominated.** -/
theorem frustrationMass_eq_iff_massCutDominated {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) :
    frustrationMass c = misalignedMass (fun _ => 1) c ↔ MassCutDominated c := by
  constructor
  · intro h S
    have h1 := frustrationMass_le (isSignVector_cutSign S) c
    rw [h, misalignedMass_eq_cost, misalignedMass_eq_cost,
      misalignedCost_signVector (isSignVector_cutSign S) hc, negSet_cutSign] at h1
    linarith
  · intro hd
    refine le_antisymm (frustrationMass_le isSignVector_one c) (le_ciInf fun s => ?_)
    rw [misalignedMass_eq_cost, misalignedMass_eq_cost, misalignedCost_signVector s.2 hc]
    linarith [hd (negSet s.1)]

/-- **Sparse frustration is rigid**: if the anti-aligned overlaps lie on a symmetric relation of
degree at most `D`, every other overlap is aligned, and `4D ≤ n`, every cut is aligned-dominated. -/
theorem cutDominated_of_sparse {c : ι → ι → ℝ} {E : ι → ι → Prop} [DecidableRel E]
    (hsymm : ∀ i j, E i j → E j i) (hpos : ∀ i j, i ≠ j → 0 < c i j → E i j)
    (hneg : ∀ i j, i ≠ j → ¬ E i j → c i j < 0) {D : ℕ}
    (hdeg : ∀ i, (univ.filter (E i)).card ≤ D) (hD : 4 * D ≤ Fintype.card ι) :
    CutDominated c := by
  intro S
  set e : ℕ := ∑ i ∈ S, ∑ j ∈ Sᶜ, if E i j then 1 else 0 with he
  have hne : ∀ i ∈ S, ∀ j ∈ Sᶜ, i ≠ j := fun i hi j hj h => (mem_compl.1 hj) (h ▸ hi)
  -- anti-aligned overlaps across the cut lie on `E`
  have hP : cutWeight S (fun t => 0 < t) (fun _ => 1) c ≤ e := by
    unfold cutWeight
    push_cast [he]
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    split_ifs with h1 h2 <;> first | norm_num | exact absurd (hpos i j (hne i hi j hj) h1) h2
  -- aligned overlaps across the cut contain the complement of `E`
  have hN : (S.card * Sᶜ.card : ℝ) - e ≤ cutWeight S (fun t => t < 0) (fun _ => 1) c := by
    unfold cutWeight
    have : (S.card * Sᶜ.card : ℝ) = ∑ i ∈ S, ∑ j ∈ Sᶜ, (1 : ℝ) := by simp
    rw [this]
    push_cast [he]
    rw [← sum_sub_distrib]
    refine sum_le_sum fun i hi => ?_
    rw [← sum_sub_distrib]
    refine sum_le_sum fun j hj => ?_
    split_ifs with h1 h2 <;> first | norm_num | exact absurd (hneg i j (hne i hi j hj) h1) h2
  -- the degree bounds on both sides of the cut
  have hrow : e ≤ S.card * D := by
    rw [he, card_eq_sum_ones, sum_mul]
    refine sum_le_sum fun i _ => ?_
    calc ∑ j ∈ Sᶜ, (if E i j then 1 else 0) ≤ ∑ j, (if E i j then 1 else 0) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
      _ = (univ.filter (E i)).card := by rw [card_filter]
      _ ≤ 1 * D := by rw [one_mul]; exact hdeg i
  have hcol : e ≤ Sᶜ.card * D := by
    rw [he, sum_comm, card_eq_sum_ones, sum_mul]
    refine sum_le_sum fun j _ => ?_
    calc ∑ i ∈ S, (if E i j then 1 else 0) ≤ ∑ i, (if E j i then 1 else 0) :=
          (sum_le_sum fun i _ => by split_ifs with h1 h2 <;> simp_all [hsymm i j]).trans
            (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _)
      _ = (univ.filter (E j)).card := by rw [card_filter]
      _ ≤ 1 * D := by rw [one_mul]; exact hdeg j
  have hn : S.card + Sᶜ.card = Fintype.card ι := by
    rw [← card_union_of_disjoint disjoint_compl_right, union_compl, card_univ]
  have key : 2 * e ≤ S.card * Sᶜ.card := by
    rcases le_total S.card Sᶜ.card with h | h <;> nlinarith
  have key' : (2 * e : ℝ) ≤ S.card * Sᶜ.card := by exact_mod_cast key
  linarith

end General

/-! ### The archimedean kernel is strictly decreasing -/

/-- **The archimedean–polar Weil weight is strictly decreasing on `(0, ∞)`.** -/
theorem weilKernel_strictAnti {u u' : ℝ} (hu : 0 < u) (huu : u < u') :
    RHTower.ArchimedeanKernel.weilKernel u' < RHTower.ArchimedeanKernel.weilKernel u := by
  unfold RHTower.ArchimedeanKernel.weilKernel
  have d1 := RHTower.ArchimedeanKernel.one_sub_exp_neg_two_mul_pos hu
  have d2 : 1 - Real.exp (-2 * u) ≤ 1 - Real.exp (-2 * u') := by
    have := Real.exp_le_exp.2 (by linarith : -2 * u' ≤ -2 * u); linarith
  have n1 : Real.exp (-u' / 2) < Real.exp (-u / 2) := Real.exp_lt_exp.2 (by linarith)
  have hfrac : 2 * Real.exp (-u' / 2) / (1 - Real.exp (-2 * u')) <
      2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) :=
    div_lt_div₀ (by linarith) d2 (by positivity) d1
  have hcosh : Real.cosh (u / 2) < Real.cosh (u' / 2) := by
    rw [Real.cosh_lt_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  linarith

/-! ### The odd Weil ledger -/

section Ledger

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The prime kernel vanishes at a sum that is not the logarithm of a prime power. -/
theorem primeKernel_eq_zero_of_not_primeSum {u : ℝ} (hu : 0 ≤ u)
    (hns : ∀ n : ℕ, Real.exp u = n → Λ n = 0) : primeKernel u = 0 := by
  unfold primeKernel
  rw [abs_of_nonneg hu]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  split_ifs with h
  · rw [hns n h, zero_div]
  · rfl

/-- **Off the prime sums the odd Weil ledger is strictly aligned** when the archimedean–polar
weight is positive. -/
theorem oddFold_neg_of_not_primeSum {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (b : ι → ℝ) {x y : ι}
    (hxy : x ≠ y) (hns : ∀ n : ℕ, Real.exp (p x + p y) = n → Λ n = 0) :
    oddFold p (weilLedgerKernel α β) b x y < 0 := by
  rw [oddFold_weilLedgerKernel hxy, oddFold_offDiag hxy]
  have hx := hp x
  have hy := hp y
  have hd : 0 < |p x - p y| := abs_pos.2 (sub_ne_zero.2 fun e => hxy (hinj e))
  have hs : |p x + p y| = p x + p y := abs_of_pos (by linarith)
  have hds : |p x - p y| < |p x + p y| := by
    rw [hs, abs_lt]; constructor <;> linarith
  have hK := weilKernel_strictAnti hd hds
  have h0 : primeKernel (p x + p y) = 0 := primeKernel_eq_zero_of_not_primeSum (by linarith) hns
  have h1 := primeKernel_nonneg (p x - p y)
  rw [h0]
  nlinarith [mul_lt_mul_of_pos_left hK hα, mul_nonneg hβ h1]

/-- The prime-sum relation of a sample. -/
def IsPrimeSum (p : ι → ℝ) (x y : ι) : Prop := x ≠ y ∧ ∃ n : ℕ, Real.exp (p x + p y) = n ∧ 0 < Λ n

/-- **The frustration index of the odd Weil ledger counts its anti-aligned prime sums**: if every
sample point lies in at most `D` prime-sum pairs and `4D ≤ n`, the frustration index is the number
of ordered prime-sum pairs with anti-aligned overlap, for every positive archimedean–polar weight. -/
theorem frustrationIndex_oddWeilLedger_of_sparse {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (b : ι → ℝ) {D : ℕ}
    (hdeg : ∀ x, (univ.filter (IsPrimeSum p x)).card ≤ D) (hD : 4 * D ≤ Fintype.card ι) :
    frustrationIndex (oddFold p (weilLedgerKernel α β) b) =
      (univ.filter fun q : ι × ι => q.1 ≠ q.2 ∧ 0 < oddFold p (weilLedgerKernel α β) b q.1 q.2).card := by
  classical
  have hsym := oddFold_isSymmetric (p := p) (b := b) (weilLedgerKernel_neg α β)
  rw [(frustrationIndex_eq_iff_cutDominated hsym).2]
  · unfold misalignedCount
    simp only [one_mul]
  refine cutDominated_of_sparse (E := IsPrimeSum p) (fun i j h => ⟨Ne.symm h.1, ?_⟩)
    (fun i j hij hpos => ⟨hij, oddFold_pos_imp_primeSum hp hinj hα.le hβ hij hpos⟩)
    (fun i j hij hE => oddFold_neg_of_not_primeSum hp hinj hα hβ b hij fun n hn => ?_) hdeg hD
  · obtain ⟨n, hn, hΛ⟩ := h.2
    exact ⟨n, by rw [add_comm]; exact hn, hΛ⟩
  · by_contra hΛ
    exact hE ⟨hij, n, hn, lt_of_le_of_ne vonMangoldt_nonneg (Ne.symm hΛ)⟩

end Ledger

end

end GaloisForLFunctions.ArithmeticOrientationTheory
