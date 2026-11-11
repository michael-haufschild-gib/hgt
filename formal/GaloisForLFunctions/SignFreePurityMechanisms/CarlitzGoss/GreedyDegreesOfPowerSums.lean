import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PowerSumChains
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ZeroRemainderBoundary

/-!
# The degrees of the monic power sums are greedy weights

Let `q = p ^ s` and `S_d(N) = ∑_{a monic, deg a = d} a ^ N` over `𝔽_q`. A digit chain of length
`d` with nonempty remainder is a carry-free composition of `N` into `d + 1` parts; one with empty
remainder is a composition into `d` parts of a total divisible by `q − 1`.

* With a positive remainder available, the greedy `(d + 1)`-part composition `G` dominates every
  chain, and every chain of the same weight has the part values of `G`
  (`top_of_greedy`, using `isOptimal_iff_isGreedy` and `IsGreedy.zeroRemainderWeight_lt`).
* Otherwise all chains have empty remainder and the greedy `d`-part composition plays this role
  (`top_of_greedy_zero`).

Hence `deg S_d(N) = wt(G) − N` with nonzero leading coefficient (`natDegree_gossPoly_of_top`),
and `S_d(N) ≠ 0` exactly when a chain of length `d` exists (`gossPoly_ne_zero_iff`).

**The Newton polygon.** The degrees are strictly concave in `d`
(`natDegree_gossPoly_strictConcave`): on positive remainders this is the strict convexity of
greedy prefix costs (`IsGreedy.prefixCost_strictConvex`); at a zero remainder the last two degrees
coincide and the preceding step is strict because a divisible greedy cost is below its total.
-/

open Finset Polynomial

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-! ### The base-`p` digits of `N` -/

/-- The digit collection of `N`: `N / p ^ e % p` labelled copies of `p ^ e`. -/
def digitsOf (p N : ℕ) : Finset (Digit p) :=
  (range (N + 1) ×ˢ (univ : Finset (Fin (p - 1)))).filter fun x => x.2.val < N / p ^ x.1 % p

theorem digitValueNat_digitsOf {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    digitValueNat p (digitsOf p N) = N := by
  unfold digitValueNat digitsOf
  rw [sum_filter, sum_product]
  have hterm (e : ℕ) : (∑ i : Fin (p - 1), if i.val < N / p ^ e % p then p ^ e else 0) =
      (N / p ^ e % p) * p ^ e := by
    rw [← sum_filter, sum_const, smul_eq_mul, Fin.card_filter_val_lt]
    have : N / p ^ e % p < p := Nat.mod_lt _ (by omega)
    congr 1
    omega
  simp only [hterm]
  have hN : N < p ^ (N + 1) :=
    (Nat.lt_pow_self (by omega : 1 < p)).trans (Nat.pow_lt_pow_right (by omega) (by omega))
  exact sum_digits_eq_of_lt_pow hN

variable {p s d : ℕ} {S : Finset (Digit p)}

namespace DigitChain

theorem mem_remainder {c : DigitChain p s d S} {x : Digit p} :
    x ∈ c.remainder ↔ x ∈ S ∧ ∀ i, x ∉ c.parts i := by
  simp only [remainder, mem_sdiff, mem_biUnion, mem_univ, true_and, not_exists]

theorem pairwise_disjoint_snoc {α : Type*} {f : Fin d → Finset α} {T : Finset α}
    (hT : ∀ i, Disjoint (f i) T) (hf : Pairwise fun i j => Disjoint (f i) (f j)) :
    Pairwise fun i j : Fin (d + 1) =>
      Disjoint ((Fin.snoc f T : Fin (d + 1) → Finset α) i)
        ((Fin.snoc f T : Fin (d + 1) → Finset α) j) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact absurd rfl hij
    | cast j => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using (hT j).symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hT i
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact hf fun h => hij (congrArg Fin.castSucc h)

theorem disjoint_remainder (c : DigitChain p s d S) (i : Fin d) :
    Disjoint (c.parts i) c.remainder :=
  disjoint_left.mpr fun _ hx hR => (mem_remainder.mp hR).2 i hx

/-! ### Chains and compositions -/

/-- A chain with nonempty remainder is a composition whose last part is the remainder. -/
def toComposition (c : DigitChain p s d S) (hR : c.remainder.Nonempty) :
    DigitComposition p s (d + 1) S where
  parts := Fin.snoc c.parts c.remainder
  subset i := by
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact sdiff_subset
    | cast j => simpa only [Fin.snoc_castSucc] using c.subset j
  disjoint := pairwise_disjoint_snoc c.disjoint_remainder c.disjoint
  cover x hx := by
    by_cases h : ∃ i, x ∈ c.parts i
    · obtain ⟨i, hi⟩ := h
      exact ⟨i.castSucc, by simpa only [Fin.snoc_castSucc] using hi⟩
    · push Not at h
      exact ⟨Fin.last d, by simpa only [Fin.snoc_last] using mem_remainder.mpr ⟨hx, h⟩⟩
  nonempty i := by
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hR
    | cast j => simpa only [Fin.snoc_castSucc] using c.nonempty j
  divisible i hi := by
    induction i using Fin.lastCases with
    | last => simp only [Fin.val_last, lt_self_iff_false] at hi
    | cast j => simpa only [Fin.snoc_castSucc] using c.divisible j

theorem toComposition_value_castSucc (c : DigitChain p s d S) (hR : c.remainder.Nonempty)
    (i : Fin d) : (c.toComposition hR).value i.castSucc = c.values i := by
  simp only [DigitComposition.value, toComposition, Fin.snoc_castSucc, values,
    natCast_digitValueNat]

theorem toComposition_weight (c : DigitChain p s d S) (hR : c.remainder.Nonempty) :
    (c.toComposition hR).weight = c.weight := by
  simp only [DigitComposition.weight, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    toComposition_value_castSucc, weight]
  simp only [DigitComposition.value, toComposition, Fin.snoc_last, ← natCast_digitValueNat]
  push_cast
  rfl

/-- The first `d` parts of a `(d + 1)`-part composition form a chain with the last part as
remainder. -/
def ofComposition (C : DigitComposition p s (d + 1) S) : DigitChain p s d S where
  parts i := C.parts i.castSucc
  subset _ := C.subset _
  disjoint _ _ hij := C.disjoint fun h => hij (Fin.castSucc_injective _ h)
  nonempty _ := C.nonempty _
  divisible i := C.divisible i.castSucc (by simp only [Fin.val_castSucc]; omega)

theorem ofComposition_remainder (C : DigitComposition p s (d + 1) S) :
    (ofComposition C).remainder = C.parts (Fin.last d) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hS, hnot⟩ := mem_remainder.mp hx
    obtain ⟨i, hi⟩ := C.cover x hS
    induction i using Fin.lastCases with
    | last => exact hi
    | cast j => exact absurd hi (hnot j)
  · intro hx
    refine mem_remainder.mpr ⟨C.subset _ hx, fun i hi => ?_⟩
    exact disjoint_left.mp (C.disjoint (Fin.castSucc_lt_last i).ne) hi hx

theorem ofComposition_values (C : DigitComposition p s (d + 1) S) (i : Fin d) :
    ((ofComposition C).values i : ℤ) = C.value i.castSucc := by
  simp only [values, ofComposition, natCast_digitValueNat, DigitComposition.value]

theorem ofComposition_weight (C : DigitComposition p s (d + 1) S) :
    ((ofComposition C).weight : ℤ) = C.weight := by
  have hR : (ofComposition C).remainder.Nonempty := by
    rw [ofComposition_remainder]
    exact C.nonempty _
  rw [← toComposition_weight _ hR]
  simp only [DigitComposition.weight, Fin.sum_univ_castSucc, toComposition_value_castSucc,
    ofComposition_values, Fin.val_castSucc, Fin.val_last]
  congr 1
  simp only [DigitComposition.value, toComposition, Fin.snoc_last, ofComposition_remainder]

/-- A chain with empty remainder is a composition with the same parts. -/
def toCompositionZero (c : DigitChain p s (d + 1) S) (hR : c.remainder = ∅) :
    DigitComposition p s (d + 1) S where
  parts := c.parts
  subset := c.subset
  disjoint := c.disjoint
  cover x hx := by
    by_contra h
    push Not at h
    have hmem : x ∈ c.remainder := mem_remainder.mpr ⟨hx, h⟩
    rw [hR] at hmem
    exact Finset.notMem_empty x hmem
  nonempty := c.nonempty
  divisible i _ := c.divisible i

theorem toCompositionZero_weight (c : DigitChain p s (d + 1) S) (hR : c.remainder = ∅) :
    (c.toCompositionZero hR).weight = c.weight := by
  simp only [DigitComposition.weight, weight, hR, digitValueNat, sum_empty, mul_zero, add_zero,
    DigitComposition.value, toCompositionZero, values, ← natCast_digitValueNat]
  push_cast
  rfl

theorem toCompositionZero_value (c : DigitChain p s (d + 1) S) (hR : c.remainder = ∅)
    (i : Fin (d + 1)) : (c.toCompositionZero hR).value i = c.values i := by
  simp only [DigitComposition.value, toCompositionZero, values, natCast_digitValueNat]

/-- A composition of a divisible total is a chain with empty remainder. -/
def ofCompositionDivisible (C : DigitComposition p s (d + 1) S)
    (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) : DigitChain p s (d + 1) S where
  parts := C.parts
  subset := C.subset
  disjoint := C.disjoint
  nonempty := C.nonempty
  divisible := C.all_divisible_of_total hN

theorem ofCompositionDivisible_remainder (C : DigitComposition p s (d + 1) S)
    (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) : (ofCompositionDivisible C hN).remainder = ∅ := by
  simp only [remainder, ofCompositionDivisible, C.biUnion_parts, sdiff_self, bot_eq_empty]

theorem ofCompositionDivisible_weight (C : DigitComposition p s (d + 1) S)
    (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    ((ofCompositionDivisible C hN).weight : ℤ) = C.weight := by
  rw [← toCompositionZero_weight _ (ofCompositionDivisible_remainder C hN)]
  rfl

theorem total_divisible_of_remainder_eq_empty (c : DigitChain p s d S) (hR : c.remainder = ∅) :
    ((p : ℤ) ^ s - 1) ∣ digitValue p S := by
  have h := c.sum_values_add_remainder
  rw [hR, show digitValueNat p ∅ = 0 from sum_empty, add_zero] at h
  rw [← natCast_digitValueNat, ← h]
  push_cast
  exact dvd_sum fun i _ => by
    rw [values, natCast_digitValueNat]
    exact c.divisible i

/-- Forget the last part, which joins the remainder. -/
def dropLast (c : DigitChain p s (d + 1) S) : DigitChain p s d S where
  parts i := c.parts i.castSucc
  subset _ := c.subset _
  disjoint _ _ hij := c.disjoint fun h => hij (Fin.castSucc_injective _ h)
  nonempty _ := c.nonempty _
  divisible _ := c.divisible _

theorem dropLast_remainder_nonempty (c : DigitChain p s (d + 1) S) :
    c.dropLast.remainder.Nonempty := by
  obtain ⟨x, hx⟩ := c.nonempty (Fin.last d)
  refine ⟨x, mem_remainder.mpr ⟨c.subset _ hx, fun i hi => ?_⟩⟩
  exact disjoint_left.mp (c.disjoint (Fin.castSucc_lt_last i).ne) hi hx

/-! ### The top chains -/

variable [NeZero s]

/-- A chain with empty remainder weighs strictly less than a greedy composition with one more
part than it has parts. -/
theorem weight_lt_of_remainder_eq_empty (hp : 2 ≤ p) {G : DigitComposition p s (d + 2) S}
    (hG : G.IsGreedy) (c : DigitChain p s (d + 1) S) (hR : c.remainder = ∅) :
    (c.weight : ℤ) < G.weight := by
  have h := hG.zeroRemainderWeight_lt hp (c.toCompositionZero hR) (fun i => by
    simpa only [DigitComposition.zeroRemainderParts, Fin.snoc_castSucc, toCompositionZero]
      using c.divisible i)
  rwa [DigitComposition.zeroRemainderWeight_eq, toCompositionZero_weight] at h

/-- **The top chain, positive remainder.** A greedy `(d + 1)`-part composition dominates every
chain of length `d`, and chains of its weight have its first `d` part values. -/
theorem top_of_greedy (hp : 2 ≤ p) {G : DigitComposition p s (d + 1) S} (hG : G.IsGreedy) :
    (∀ c : DigitChain p s d S, (c.weight : ℤ) ≤ G.weight) ∧
      ∀ c : DigitChain p s d S, (c.weight : ℤ) = G.weight →
        ∀ i, (c.values i : ℤ) = G.value i.castSucc := by
  have hzero : ∀ c : DigitChain p s d S, c.remainder = ∅ → (c.weight : ℤ) < G.weight := by
    intro c hR
    cases d with
    | zero =>
      exfalso
      obtain ⟨x, hx⟩ := G.nonempty 0
      have hmem : x ∈ c.remainder :=
        mem_remainder.mpr ⟨G.subset 0 hx, fun i => i.elim0⟩
      rw [hR] at hmem
      exact Finset.notMem_empty x hmem
    | succ d => exact weight_lt_of_remainder_eq_empty hp hG c hR
  refine ⟨fun c => ?_, fun c hc i => ?_⟩
  · by_cases hR : c.remainder.Nonempty
    · rw [← toComposition_weight c hR]
      exact hG.isOptimal hp _
    · exact (hzero c (not_nonempty_iff_eq_empty.mp hR)).le
  · by_cases hR : c.remainder.Nonempty
    · have hopt : (c.toComposition hR).IsOptimal := fun D => by
        rw [toComposition_weight, hc]
        exact hG.isOptimal hp D
      rw [← toComposition_value_castSucc c hR i,
        DigitComposition.IsOptimal.values_eq hp hopt (hG.isOptimal hp)]
    · exact absurd hc (hzero c (not_nonempty_iff_eq_empty.mp hR)).ne

/-- **The top chain, zero remainder.** If no chain of length `d + 1` has a nonempty remainder,
a greedy `(d + 1)`-part composition dominates every chain of length `d + 1`. -/
theorem top_of_greedy_zero (hp : 2 ≤ p) (hno : IsEmpty (DigitComposition p s (d + 2) S))
    {G : DigitComposition p s (d + 1) S} (hG : G.IsGreedy) :
    (∀ c : DigitChain p s (d + 1) S, (c.weight : ℤ) ≤ G.weight) ∧
      ∀ c : DigitChain p s (d + 1) S, (c.weight : ℤ) = G.weight →
        ∀ i, (c.values i : ℤ) = G.value i := by
  have hR : ∀ c : DigitChain p s (d + 1) S, c.remainder = ∅ := fun c =>
    not_nonempty_iff_eq_empty.mp fun h => hno.false (c.toComposition h)
  refine ⟨fun c => ?_, fun c hc i => ?_⟩
  · rw [← toCompositionZero_weight c (hR c)]
    exact hG.isOptimal hp _
  · have hopt : (c.toCompositionZero (hR c)).IsOptimal := fun D => by
      rw [toCompositionZero_weight, hc]
      exact hG.isOptimal hp D
    rw [← toCompositionZero_value c (hR c) i,
      DigitComposition.IsOptimal.values_eq hp hopt (hG.isOptimal hp)]

end DigitChain

/-! ### Degrees -/

section Degrees

variable [hp : Fact p.Prime] {F : Type*} [Field F] [CharP F p]

/-- A chain dominating all chains, with unique values at its weight, gives the degree and a
nonzero leading coefficient. -/
theorem natDegree_gossPoly_of_top (c₀ : DigitChain p s d S)
    (hmax : ∀ c : DigitChain p s d S, c.weight ≤ c₀.weight)
    (huniq : ∀ c : DigitChain p s d S, c.weight = c₀.weight → c.values = c₀.values) :
    gossPoly F (p ^ s) d (digitValueNat p S) ≠ 0 ∧
      (gossPoly F (p ^ s) d (digitValueNat p S)).natDegree = c₀.expo := by
  have hne : (gossPoly F (p ^ s) d (digitValueNat p S)).coeff c₀.expo ≠ 0 := by
    refine coeff_gossPoly_ne_zero_of_unique_top d S c₀ (fun c => ?_) (fun c hc => ?_)
    · exact Nat.sub_le_sub_right (hmax c) _
    · refine huniq c ?_
      have h1 := c.le_weight
      have h2 := c₀.le_weight
      simp only [DigitChain.expo] at hc
      omega
  refine ⟨fun h => hne (by rw [h, coeff_zero]), le_antisymm ?_ (le_natDegree_of_ne_zero hne)⟩
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_contra h
  obtain ⟨c, hc⟩ := exists_chain_of_coeff_gossPoly_ne_zero d S n h
  have := Nat.sub_le_sub_right (hmax c) (digitValueNat p S)
  simp only [DigitChain.expo] at hc
  rw [hc] at this
  exact absurd hn (not_lt.mpr this)

variable [NeZero s]

/-- **Degree from the greedy composition.** -/
theorem natDegree_gossPoly_of_greedy {G : DigitComposition p s (d + 1) S} (hG : G.IsGreedy) :
    gossPoly F (p ^ s) d (digitValueNat p S) ≠ 0 ∧
      ((gossPoly F (p ^ s) d (digitValueNat p S)).natDegree : ℤ) =
        G.weight - digitValueNat p S := by
  obtain ⟨hmax, huniq⟩ := DigitChain.top_of_greedy hp.out.two_le hG
  have hw := DigitChain.ofComposition_weight G
  obtain ⟨hne, hdeg⟩ := natDegree_gossPoly_of_top (F := F) (DigitChain.ofComposition G)
    (fun c => by have := hmax c; omega)
    (fun c hc => funext fun i => by
      have := huniq c (by rw [← hw]; exact_mod_cast hc) i
      have h2 := DigitChain.ofComposition_values G i
      omega)
  refine ⟨hne, ?_⟩
  rw [hdeg, DigitChain.expo, Nat.cast_sub (DigitChain.ofComposition G).le_weight, hw]

/-- **Degree from the greedy composition, zero remainder.** -/
theorem natDegree_gossPoly_of_greedy_zero (hno : IsEmpty (DigitComposition p s (d + 2) S))
    (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S)
    {G : DigitComposition p s (d + 1) S} (hG : G.IsGreedy) :
    gossPoly F (p ^ s) (d + 1) (digitValueNat p S) ≠ 0 ∧
      ((gossPoly F (p ^ s) (d + 1) (digitValueNat p S)).natDegree : ℤ) =
        G.weight - digitValueNat p S := by
  obtain ⟨hmax, huniq⟩ := DigitChain.top_of_greedy_zero hp.out.two_le hno hG
  have hw := DigitChain.ofCompositionDivisible_weight G hN
  obtain ⟨hne, hdeg⟩ := natDegree_gossPoly_of_top (F := F) (DigitChain.ofCompositionDivisible G hN)
    (fun c => by have := hmax c; omega)
    (fun c hc => funext fun i => by
      have := huniq c (by rw [← hw]; exact_mod_cast hc) i
      have h2 : ((DigitChain.ofCompositionDivisible G hN).values i : ℤ) = G.value i := by
        simp only [DigitChain.values, DigitChain.ofCompositionDivisible, natCast_digitValueNat,
          DigitComposition.value]
      omega)
  refine ⟨hne, ?_⟩
  rw [hdeg, DigitChain.expo, Nat.cast_sub (DigitChain.ofCompositionDivisible G hN).le_weight, hw]

/-- The power sum `S_d(N)` is nonzero exactly when a chain of length `d` exists. -/
theorem gossPoly_ne_zero_iff :
    gossPoly F (p ^ s) d (digitValueNat p S) ≠ 0 ↔ Nonempty (DigitChain p s d S) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, (gossPoly F (p ^ s) d (digitValueNat p S)).coeff n ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h (Polynomial.ext hcon)
    obtain ⟨c, _⟩ := exists_chain_of_coeff_gossPoly_ne_zero d S n hn
    exact ⟨c⟩
  · rintro ⟨c⟩
    by_cases hpos : Nonempty (DigitComposition p s (d + 1) S)
    · obtain ⟨G, hG⟩ := DigitComposition.exists_greedy hpos
      exact (natDegree_gossPoly_of_greedy hG).1
    · cases d with
      | zero => rw [gossPoly_zero]; exact one_ne_zero
      | succ d =>
        have hR : c.remainder = ∅ := not_nonempty_iff_eq_empty.mp fun h =>
          hpos ⟨(c.toComposition h)⟩
        obtain ⟨G, hG⟩ := DigitComposition.exists_greedy ⟨c.toCompositionZero hR⟩
        exact (natDegree_gossPoly_of_greedy_zero (not_nonempty_iff.mp hpos)
          (c.total_divisible_of_remainder_eq_empty hR) hG).1

/-- **The Newton polygon of the power sums.** The degrees of `S_d(N)` are strictly concave
wherever `S_{d+2}(N) ≠ 0`. -/
theorem natDegree_gossPoly_strictConcave (hc : Nonempty (DigitChain p s (d + 2) S)) :
    (gossPoly F (p ^ s) d (digitValueNat p S)).natDegree +
        (gossPoly F (p ^ s) (d + 2) (digitValueNat p S)).natDegree <
      2 * (gossPoly F (p ^ s) (d + 1) (digitValueNat p S)).natDegree := by
  have hp2 := hp.out.two_le
  obtain ⟨c₂⟩ := hc
  suffices key : ((gossPoly F (p ^ s) d (digitValueNat p S)).natDegree : ℤ) +
      (gossPoly F (p ^ s) (d + 2) (digitValueNat p S)).natDegree <
      2 * ((gossPoly F (p ^ s) (d + 1) (digitValueNat p S)).natDegree : ℤ) by
    exact_mod_cast key
  by_cases hpos : Nonempty (DigitComposition p s (d + 3) S)
  · obtain ⟨G₃, hG₃⟩ := DigitComposition.exists_greedy hpos
    obtain ⟨G₂, hG₂⟩ := DigitComposition.exists_greedy ⟨G₃.mergeLast⟩
    obtain ⟨G₁, hG₁⟩ := DigitComposition.exists_greedy ⟨G₂.mergeLast⟩
    have hconv := hG₂.prefixCost_strictConvex G₁ hp2 hG₃
    simp only [DigitComposition.prefixCost] at hconv
    rw [(natDegree_gossPoly_of_greedy (F := F) hG₁).2, (natDegree_gossPoly_of_greedy (F := F) hG₂).2,
      (natDegree_gossPoly_of_greedy (F := F) hG₃).2]
    push_cast at hconv
    linarith only [hconv]
  · have hR : c₂.remainder = ∅ := not_nonempty_iff_eq_empty.mp fun h =>
      hpos ⟨c₂.toComposition h⟩
    have hN := c₂.total_divisible_of_remainder_eq_empty hR
    obtain ⟨G₂, hG₂⟩ := DigitComposition.exists_greedy ⟨c₂.toCompositionZero hR⟩
    obtain ⟨G₁, hG₁⟩ := DigitComposition.exists_greedy ⟨G₂.mergeLast⟩
    have hcost := hG₂.prefixCost_lt_total hp2 hN
    have hle := G₁.weight_le (by omega : 0 < p)
    simp only [DigitComposition.prefixCost] at hcost
    rw [(natDegree_gossPoly_of_greedy (F := F) hG₁).2, (natDegree_gossPoly_of_greedy (F := F) hG₂).2,
      (natDegree_gossPoly_of_greedy_zero (F := F) (not_nonempty_iff.mp hpos) hN hG₂).2]
    rw [← natCast_digitValueNat] at hcost hle
    push_cast at hcost hle
    linarith only [hcost, hle]

omit hp [NeZero s] in
/-- Chains of length `d + 1` give chains of length `d`. -/
theorem nonempty_chain_of_succ (h : Nonempty (DigitChain p s (d + 1) S)) :
    Nonempty (DigitChain p s d S) :=
  h.map DigitChain.dropLast

end Degrees

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
