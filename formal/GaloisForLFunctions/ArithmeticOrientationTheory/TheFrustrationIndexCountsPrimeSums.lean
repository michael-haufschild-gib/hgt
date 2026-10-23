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
    split_ifs with h1 h2 <;> first | exact absurd (hpos i j (hne i hi j hj) h1) h2 | norm_num
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
    by_cases hE : E i j
    · simp only [hE, if_true]; split_ifs <;> norm_num
    · simp [hE, hneg i j (hne i hi j hj) hE]
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

omit [Fintype ι] in
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

open scoped Classical in
/-- **The frustration index of the odd Weil ledger counts its anti-aligned prime sums**: if every
sample point lies in at most `D` prime-sum pairs and `4D ≤ n`, the frustration index is the number
of ordered prime-sum pairs with anti-aligned overlap, for every positive archimedean–polar weight. -/
theorem frustrationIndex_oddWeilLedger_of_sparse {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (b : ι → ℝ) {D : ℕ}
    (hdeg : ∀ x, (univ.filter (IsPrimeSum p x)).card ≤ D) (hD : 4 * D ≤ Fintype.card ι) :
    frustrationIndex (oddFold p (weilLedgerKernel α β) b) =
      (univ.filter fun q : ι × ι => q.1 ≠ q.2 ∧ 0 < oddFold p (weilLedgerKernel α β) b q.1 q.2).card := by
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

/-! ### The matched prime-sum family -/

section Matched

/-- `A n² ≠ B q` for a prime `q` dividing neither `A` nor `B`: `q` would divide `n`, hence `q²`
would divide `B q`. -/
theorem mul_sq_ne_mul_prime {q A B n : ℕ} (hq : q.Prime) (hA : ¬ q ∣ A) (hB : ¬ q ∣ B) :
    A * n ^ 2 ≠ B * q := by
  intro h
  have h1 : q ∣ A * n ^ 2 := h ▸ dvd_mul_left q B
  obtain ⟨m, rfl⟩ := hq.dvd_of_dvd_pow ((hq.dvd_mul.1 h1).resolve_left hA)
  have h3 : A * q * m ^ 2 = B := by
    have : A * (q * m) ^ 2 = (A * q * m ^ 2) * q := by ring
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_right hq.pos h
  exact hB ⟨A * m ^ 2, by rw [← h3]; ring⟩

variable {Q : Finset ℕ}

/-- The ratio of a matched sample point: `3q/2` on the upper and `2q/3` on the lower point. -/
def matchedRatio (x : ↥Q × Bool) : ℝ := if x.2 then 3 * ((x.1 : ℕ) : ℝ) / 2 else 2 * ((x.1 : ℕ) : ℝ) / 3

/-- **The matched sample** of a set of primes: the positions `½ log(3q/2)` and `½ log(2q/3)`,
whose sum is `log q`. -/
def matchedPos (Q : Finset ℕ) (x : ↥Q × Bool) : ℝ := Real.log (matchedRatio x) / 2

/-- The matched partner of a sample point. -/
def matchedPartner (x : ↥Q × Bool) : ↥Q × Bool := (x.1, !x.2)

theorem matchedPartner_ne (x : ↥Q × Bool) : x ≠ matchedPartner x := by
  intro h
  have h2 : x.2 = !x.2 := congrArg Prod.snd h
  cases hb : x.2 <;> rw [hb] at h2 <;> exact absurd h2 (by decide)

section Primes

variable (hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q)
include hQ

theorem five_le_matched (x : ↥Q × Bool) : (5 : ℝ) ≤ ((x.1 : ℕ) : ℝ) := by
  exact_mod_cast (hQ x.1 x.1.2).2

theorem one_lt_matchedRatio (x : ↥Q × Bool) : 1 < matchedRatio x := by
  have h5 := five_le_matched hQ x
  unfold matchedRatio
  split_ifs <;> linarith

theorem matchedPos_pos (x : ↥Q × Bool) : 0 < matchedPos Q x :=
  div_pos (Real.log_pos (one_lt_matchedRatio hQ x)) two_pos

/-- `exp(2(p_x + p_y)) = r_x r_y`. -/
theorem exp_matchedPos_add_sq (x y : ↥Q × Bool) :
    Real.exp (matchedPos Q x + matchedPos Q y) ^ 2 = matchedRatio x * matchedRatio y := by
  have hx := (one_lt_matchedRatio hQ x).le
  have hy := (one_lt_matchedRatio hQ y).le
  rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (matchedPos Q x + matchedPos Q y) =
    Real.log (matchedRatio x) + Real.log (matchedRatio y) by unfold matchedPos; push_cast; ring,
    Real.exp_add, Real.exp_log (by linarith), Real.exp_log (by linarith)]

/-- A prime `≥ 5` of the family divides no square `m²` with `m ≤ 3`. -/
theorem not_dvd_sq_of_matched {q : ℕ} (hq : q ∈ Q) {m : ℕ} (hm1 : 1 ≤ m) (hm3 : m ≤ 3) :
    ¬ q ∣ m ^ 2 := fun h => by
  have := Nat.le_of_dvd (by omega) ((hQ q hq).1.dvd_of_dvd_pow h)
  have := (hQ q hq).2
  omega

/-- A prime `≥ 5` of the family divides no `m² q'` with `m ≤ 3` and `q'` another prime of the
family. -/
theorem not_dvd_sq_mul_of_matched {q q' : ℕ} (hq : q ∈ Q) (hq' : q' ∈ Q) (hne : q ≠ q') {m : ℕ}
    (hm1 : 1 ≤ m) (hm3 : m ≤ 3) : ¬ q ∣ m ^ 2 * q' := fun h => by
  rcases (hQ q hq).1.dvd_mul.1 h with h1 | h1
  · exact not_dvd_sq_of_matched hQ hq hm1 hm3 h1
  · exact hne ((Nat.prime_dvd_prime_iff_eq (hQ q hq).1 (hQ q' hq').1).1 h1)

/-- **Prime sums of the matched sample lie on the matched pairs.** -/
theorem eq_matchedPartner_of_exp_eq {x y : ↥Q × Bool} (hxy : x ≠ y) {n : ℕ}
    (hn : Real.exp (matchedPos Q x + matchedPos Q y) = n) : y = matchedPartner x := by
  have hsq := exp_matchedPos_add_sq hQ x y
  rw [hn] at hsq
  obtain ⟨⟨q, hq⟩, a⟩ := x
  obtain ⟨⟨q', hq'⟩, a'⟩ := y
  have hq5 := (hQ q hq).2
  simp only [matchedRatio] at hsq
  by_cases hqq : q = q'
  · subst hqq
    cases a <;> cases a' <;> simp_all [matchedPartner]
  · exfalso
    have hprime := (hQ q hq).1
    cases a <;> cases a' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hsq
    · have h : (3 ^ 2 * (n : ℝ) ^ 2) = 2 ^ 2 * q' * q := by rw [hsq]; ring
      exact mul_sq_ne_mul_prime hprime (not_dvd_sq_of_matched hQ hq (m := 3) (by norm_num)
        (by norm_num)) (not_dvd_sq_mul_of_matched hQ hq hq' hqq (m := 2) (by norm_num)
        (by norm_num)) (by exact_mod_cast h)
    · have h : (1 ^ 2 * (n : ℝ) ^ 2) = 1 ^ 2 * q' * q := by rw [hsq]; ring
      exact mul_sq_ne_mul_prime hprime (not_dvd_sq_of_matched hQ hq (m := 1) le_rfl
        (by norm_num)) (not_dvd_sq_mul_of_matched hQ hq hq' hqq (m := 1) le_rfl
        (by norm_num)) (by exact_mod_cast h)
    · have h : (1 ^ 2 * (n : ℝ) ^ 2) = 1 ^ 2 * q' * q := by rw [hsq]; ring
      exact mul_sq_ne_mul_prime hprime (not_dvd_sq_of_matched hQ hq (m := 1) le_rfl
        (by norm_num)) (not_dvd_sq_mul_of_matched hQ hq hq' hqq (m := 1) le_rfl
        (by norm_num)) (by exact_mod_cast h)
    · have h : (2 ^ 2 * (n : ℝ) ^ 2) = 3 ^ 2 * q' * q := by rw [hsq]; ring
      exact mul_sq_ne_mul_prime hprime (not_dvd_sq_of_matched hQ hq (m := 2) (by norm_num)
        (by norm_num)) (not_dvd_sq_mul_of_matched hQ hq hq' hqq (m := 3) (by norm_num)
        (by norm_num)) (by exact_mod_cast h)

theorem matchedPos_add_partner (x : ↥Q × Bool) :
    matchedPos Q x + matchedPos Q (matchedPartner x) = Real.log ((x.1 : ℕ) : ℝ) := by
  have h5 := five_le_matched hQ x
  unfold matchedPos matchedRatio matchedPartner
  cases x.2 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
    rw [Real.log_div (by positivity) (by norm_num), Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)] <;>
    ring

theorem abs_matchedPos_sub_partner (x : ↥Q × Bool) :
    |matchedPos Q x - matchedPos Q (matchedPartner x)| = Real.log (3 / 2) := by
  have h5 := five_le_matched hQ x
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  unfold matchedPos matchedRatio matchedPartner
  cases x.2 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
    rw [Real.log_div (by positivity) (by norm_num), Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  · rw [show (Real.log 2 + Real.log ((x.1 : ℕ) : ℝ) - Real.log 3) / 2 -
      (Real.log 3 + Real.log ((x.1 : ℕ) : ℝ) - Real.log 2) / 2 = -(Real.log 3 - Real.log 2) by ring,
      abs_neg, ← h32, abs_of_pos hl]
  · rw [show (Real.log 3 + Real.log ((x.1 : ℕ) : ℝ) - Real.log 2) / 2 -
      (Real.log 2 + Real.log ((x.1 : ℕ) : ℝ) - Real.log 3) / 2 = Real.log 3 - Real.log 2 by ring,
      ← h32, abs_of_pos hl]

theorem matchedPos_injective : Function.Injective (matchedPos Q) := by
  intro x y h
  have hx := one_lt_matchedRatio hQ x
  have hy := one_lt_matchedRatio hQ y
  have hr : matchedRatio x = matchedRatio y := by
    unfold matchedPos at h
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (by linarith)) (Set.mem_Ioi.2 (by linarith))
      (by linarith)
  obtain ⟨⟨q, hq⟩, a⟩ := x
  obtain ⟨⟨q', hq'⟩, a'⟩ := y
  simp only [matchedRatio] at hr
  have h5 := (hQ q hq).2
  have h5' := (hQ q' hq').2
  cases a <;> cases a' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr
  · have : q = q' := by exact_mod_cast (by linarith : (q : ℝ) = q')
    subst this; rfl
  · -- `4 q = 9 q'` is impossible for primes `≥ 5`
    have h' : 4 * q = 9 * q' := by exact_mod_cast (by linarith : (4 * q : ℝ) = 9 * q')
    exfalso
    have hd : q' ∣ 4 * q := ⟨9, by rw [h']; ring⟩
    rcases (hQ q' hq').1.dvd_mul.1 hd with hd | hd
    · have := Nat.le_of_dvd (by norm_num) hd; omega
    · have := (Nat.prime_dvd_prime_iff_eq (hQ q' hq').1 (hQ q hq).1).1 hd; subst this; omega
  · have h' : 9 * q = 4 * q' := by exact_mod_cast (by linarith : (9 * q : ℝ) = 4 * q')
    exfalso
    have hd : q ∣ 4 * q' := ⟨9, by rw [← h']; ring⟩
    rcases (hQ q hq).1.dvd_mul.1 hd with hd | hd
    · have := Nat.le_of_dvd (by norm_num) hd; omega
    · have := (Nat.prime_dvd_prime_iff_eq (hQ q hq).1 (hQ q' hq').1).1 hd; subst this; omega
  · have : q = q' := by exact_mod_cast (by linarith : (q : ℝ) = q')
    subst this; rfl

/-- The matched overlap: `α (K(log q) − K(log 3/2)) + β log q/√q`. -/
theorem oddFold_matchedPartner {α β : ℝ} (b : ↥Q × Bool → ℝ) (x : ↥Q × Bool) :
    oddFold (matchedPos Q) (weilLedgerKernel α β) b x (matchedPartner x) =
      α * (RHTower.ArchimedeanKernel.weilKernel (Real.log ((x.1 : ℕ) : ℝ)) -
        RHTower.ArchimedeanKernel.weilKernel (Real.log (3 / 2))) +
      β * (Real.log ((x.1 : ℕ) : ℝ) / Real.sqrt ((x.1 : ℕ) : ℝ)) := by
  have hne := matchedPartner_ne x
  have h5 := five_le_matched hQ x
  rw [oddFold_weilLedgerKernel hne, oddFold_offDiag hne, matchedPos_add_partner hQ,
    abs_matchedPos_sub_partner hQ, abs_of_pos (Real.log_pos (by linarith)),
    primeKernel_log_prime (hQ x.1 x.1.2).1]
  have h0 : primeKernel (matchedPos Q x - matchedPos Q (matchedPartner x)) = 0 := by
    apply primeKernel_eq_zero
    intro n
    rw [abs_matchedPos_sub_partner hQ, Real.exp_log (by norm_num)]
    exact ne_natCast_of_between (m := 1) (by norm_num) (by norm_num) n
  rw [h0]
  ring

/-- Small archimedean–polar weights keep every matched overlap anti-aligned. -/
theorem exists_weight_matched_pos (hne : Q.Nonempty) {β : ℝ} (hβ : 0 < β) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ → ∀ (b : ↥Q × Bool → ℝ) (x : ↥Q × Bool),
      0 < oddFold (matchedPos Q) (weilLedgerKernel α β) b x (matchedPartner x) := by
  set a : ℕ → ℝ := fun q => RHTower.ArchimedeanKernel.weilKernel (Real.log (3 / 2)) -
    RHTower.ArchimedeanKernel.weilKernel (Real.log q)
  set t : ℕ → ℝ := fun q => β * (Real.log q / Real.sqrt q) / (|a q| + 1)
  have ht : ∀ q ∈ Q, 0 < t q := fun q hq => by
    have h5 : (5 : ℝ) ≤ q := by exact_mod_cast (hQ q hq).2
    have : 0 < Real.log q / Real.sqrt q :=
      div_pos (Real.log_pos (by linarith)) (Real.sqrt_pos.2 (by linarith))
    positivity
  refine ⟨Q.inf' hne t, (lt_inf'_iff hne).2 ht, fun α hα hαt b x => ?_⟩
  rw [oddFold_matchedPartner hQ]
  have hq := x.1.2
  have hle : α < t x.1 := lt_of_lt_of_le hαt (inf'_le t hq)
  have h5 := five_le_matched hQ x
  have hP : 0 < Real.log ((x.1 : ℕ) : ℝ) / Real.sqrt ((x.1 : ℕ) : ℝ) :=
    div_pos (Real.log_pos (by linarith)) (Real.sqrt_pos.2 (by linarith))
  have h1 : α * |a x.1| < β * (Real.log ((x.1 : ℕ) : ℝ) / Real.sqrt ((x.1 : ℕ) : ℝ)) := by
    have h2 : α * (|a x.1| + 1) < β * (Real.log ((x.1 : ℕ) : ℝ) / Real.sqrt ((x.1 : ℕ) : ℝ)) := by
      have := mul_lt_mul_of_pos_right hle (by positivity : (0 : ℝ) < |a x.1| + 1)
      simp only [t] at this
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    nlinarith
  have h3 : -(α * |a x.1|) ≤ α * (RHTower.ArchimedeanKernel.weilKernel (Real.log ((x.1 : ℕ) : ℝ)) -
      RHTower.ArchimedeanKernel.weilKernel (Real.log (3 / 2))) := by
    have : -|a x.1| ≤ -(a x.1) := neg_le_neg (le_abs_self _)
    simp only [a] at this
    nlinarith
  linarith

/-- **The frustration index of the matched sample is `2|Q|`**: for a set `Q` of at least two primes
`≥ 5` and every positive prime weight `β`, all small positive archimedean–polar weights give the odd
Weil ledger on the matched sample frustration index exactly `2|Q|`. -/
theorem frustrationIndex_matchedPos (hcard : 2 ≤ Q.card) {β : ℝ} (hβ : 0 < β) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ → ∀ b : ↥Q × Bool → ℝ,
      frustrationIndex (oddFold (matchedPos Q) (weilLedgerKernel α β) b) = 2 * Q.card := by
  classical
  have hne : Q.Nonempty := card_pos.1 (by omega)
  obtain ⟨α₀, hα₀, hpos⟩ := exists_weight_matched_pos hQ hne hβ
  refine ⟨α₀, hα₀, fun α hα hαt b => ?_⟩
  have hcardι : Fintype.card (↥Q × Bool) = Q.card * 2 := by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool]
  rw [frustrationIndex_oddWeilLedger_of_sparse (matchedPos_pos hQ) (matchedPos_injective hQ) hα
    hβ.le b (D := 1) (fun x => ?_) (by omega)]
  · -- the anti-aligned overlaps are exactly the matched pairs
    have hset : (univ.filter fun q : (↥Q × Bool) × (↥Q × Bool) =>
        q.1 ≠ q.2 ∧ 0 < oddFold (matchedPos Q) (weilLedgerKernel α β) b q.1 q.2) =
        univ.image fun x => (x, matchedPartner x) := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨hxy, hp⟩
        obtain ⟨n, hn, -⟩ := oddFold_pos_imp_primeSum (matchedPos_pos hQ) (matchedPos_injective hQ)
          hα.le hβ.le hxy hp
        exact ⟨x, rfl, (eq_matchedPartner_of_exp_eq hQ hxy hn).symm⟩
      · rintro ⟨z, rfl, rfl⟩
        exact ⟨matchedPartner_ne z, hpos α hα hαt b z⟩
    rw [hset, card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).1), card_univ, hcardι]
    ring
  · -- each point has at most one prime-sum partner
    calc (univ.filter (IsPrimeSum (matchedPos Q) x)).card ≤ ({matchedPartner x} : Finset _).card := by
          refine card_le_card fun y hy => ?_
          simp only [mem_filter, mem_univ, true_and] at hy
          obtain ⟨hxy, n, hn, -⟩ := hy
          rw [mem_singleton]
          exact eq_matchedPartner_of_exp_eq hQ hxy hn
      _ = 1 := card_singleton _

/-- The matched sample lies in `(0, ½ log(3M/2)]` when every prime of `Q` is at most `M`. -/
theorem matchedPos_le {M : ℝ} (hM : ∀ q ∈ Q, (q : ℝ) ≤ M) (x : ↥Q × Bool) :
    matchedPos Q x ≤ Real.log (3 * M / 2) / 2 := by
  have h5 := five_le_matched hQ x
  have hqM := hM x.1 x.1.2
  have h1 := one_lt_matchedRatio hQ x
  unfold matchedPos
  refine div_le_div_of_nonneg_right (Real.log_le_log (by linarith) ?_) (by norm_num)
  unfold matchedRatio
  split_ifs <;> linarith

end Primes

/-- **The frustration index is unbounded**: for every `N` there is a set of `N + 2` primes `≥ 5`
whose matched sample has frustration index `2(N + 2)` for all small archimedean–polar weights. -/
theorem exists_frustrationIndex_ge (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ 5 ≤ q) ∧ Q.card = N + 2 ∧
      ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ → ∀ b : ↥Q × Bool → ℝ,
        frustrationIndex (oddFold (matchedPos Q) (weilLedgerKernel α β) b) = 2 * (N + 2) := by
  have hinf : {q : ℕ | q.Prime ∧ 5 ≤ q}.Infinite := by
    have := Nat.infinite_setOf_prime.sdiff (Set.finite_lt_nat 5)
    refine this.mono fun q hq => ⟨hq.1, ?_⟩
    have h2 : ¬ q < 5 := hq.2
    omega
  obtain ⟨Q, hQs, hQc⟩ := hinf.exists_subset_card_eq (N + 2)
  have hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q := fun q hq => hQs hq
  obtain ⟨α₀, hα₀, h⟩ := frustrationIndex_matchedPos hQ (by omega) hβ
  exact ⟨Q, hQ, hQc, α₀, hα₀, fun α hα hαt b => by rw [h α hα hαt b, hQc]⟩

end Matched

end

end GaloisForLFunctions.ArithmeticOrientationTheory
