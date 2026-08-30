import GaloisForLFunctions.HTGeometry.RittCyclicOrders

/-!
# The cyclic normal form carries no invariant differential

For `h(w) = (A − Bλw^p)/(1 − λw^p)` the homogeneous transport equation `F(h)·(h′)^k = b·F` is
solved by counting.

Away from the origin the order of `F` is constant along the map, and the fibre of `h` over any point
other than the two critical values `A`, `B` consists of `p` distinct points at which the map is
regular and unramified.  So the finite set `S` where the order of `F` does not vanish swallows the
whole fibre over each of its own points outside `{A,B}`.  Writing `T = S \ {A,B}`, disjointness of
fibres gives `p·|T| ≤ |S| ≤ |T| + 2`, while a single fibre already contributes `p − 2` points to `T`,
so a nonempty `T` forces `(p−1)(p−2) ≤ 2`.

For `p ≥ 4` that is impossible.  For `p = 3` it leaves one configuration, in which both critical
values lie in a single fibre; but `h(A) = h(B)` rearranges to `(A−B)(A^p − B^p) = 0`, so it is
excluded as soon as `A^p ≠ B^p`.

With `T` empty the support lies in `{A, B}`, and the two remaining relations finish it: the origin
carries no order, so the ramification identity at the critical point reads `p·ord_A F = −k(p−1)`,
and transporting the order from `A` to `h(A)` forces `ord_A F = 0`, because `h(A) = A` would need
`λA^p(A−B) = 0` and `h(A) = B` would need `A = B`.  Hence `k(p−1) = 0`, contradicting `k ≠ 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

/-! ## Fibres -/

/-- The fibre of the normal form over a point. -/
def cnfFiber [DecidableEq K] (p : ℕ) (A B lam y : K) : Finset K :=
  (cnfNum p A B lam - C y * cnfDen p lam).roots.toFinset

omit [CharZero K] in
theorem mem_cnfFiber_iff [DecidableEq K] {p : ℕ} (hp : 0 < p) {A B lam y : K}
    (hc : (B - y) * lam ≠ 0) (z : K) :
    z ∈ cnfFiber p A B lam y ↔ A - y = (B - y) * lam * z ^ p := by
  rw [cnfFiber, Multiset.mem_toFinset,
    Polynomial.mem_roots (cnfFiberPoly_ne_zero hp hc), cnfFiberPoly_eq]
  simp only [Polynomial.IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

omit [CharZero K] in
/-- A point of a fibre is a point of regularity. -/
theorem cnfFiber_den_ne_zero [DecidableEq K] {p : ℕ} (hp : 0 < p) {A B lam y : K} (hAB : A ≠ B)
    (hc : (B - y) * lam ≠ 0) {z : K} (hz : z ∈ cnfFiber p A B lam y) :
    1 - lam * z ^ p ≠ 0 := by
  rw [mem_cnfFiber_iff hp hc] at hz
  intro h
  exact hAB (by linear_combination hz - (B - y) * h)

omit [CharZero K] in
/-- A point of a fibre is carried to the base point. -/
theorem cnfFiber_value [DecidableEq K] {p : ℕ} (hp : 0 < p) {A B lam y : K} (hAB : A ≠ B)
    (hc : (B - y) * lam ≠ 0) {z : K} (hz : z ∈ cnfFiber p A B lam y) :
    (A - B * lam * z ^ p) / (1 - lam * z ^ p) = y := by
  have hden := cnfFiber_den_ne_zero hp hAB hc hz
  rw [mem_cnfFiber_iff hp hc] at hz
  rw [div_eq_iff hden]
  linear_combination hz

omit [CharZero K] in
/-- Membership of the fibre in the two directions used below. -/
theorem mem_cnfFiber_of_value [DecidableEq K] {p : ℕ} (hp : 0 < p) {A B lam y z : K}
    (hc : (B - y) * lam ≠ 0) (hden : 1 - lam * z ^ p ≠ 0)
    (hval : (A - B * lam * z ^ p) / (1 - lam * z ^ p) = y) : z ∈ cnfFiber p A B lam y := by
  rw [mem_cnfFiber_iff hp hc]
  rw [div_eq_iff hden] at hval
  linear_combination hval

/-- Every fibre over a point other than the two critical values has exactly `p` points. -/
theorem card_cnfFiber [DecidableEq K] [IsAlgClosed K] {p : ℕ} (hp : 0 < p) {A B lam y : K}
    (hlam : lam ≠ 0) (hyA : y ≠ A) (hyB : y ≠ B) :
    (cnfFiber p A B lam y).card = p := by
  have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
  have hd : (A - y) / ((B - y) * lam) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hyA)) hc
  have hEq : cnfNum p A B lam - C y * cnfDen p lam
      = C (-((B - y) * lam)) * (X ^ p - C ((A - y) / ((B - y) * lam))) := by
    have hcc : (C ((B - y) * lam) * C ((A - y) / ((B - y) * lam)) : K[X]) = C (A - y) := by
      rw [← map_mul, mul_div_cancel₀ _ hc]
    rw [cnfFiberPoly_eq, map_neg]
    linear_combination -hcc
  have hsep : (X ^ p - C ((A - y) / ((B - y) * lam)) : K[X]).Separable :=
    Polynomial.separable_X_pow_sub_C _ (Nat.cast_ne_zero.mpr (by omega)) hd
  have hroots : (cnfNum p A B lam - C y * cnfDen p lam).roots
      = (X ^ p - C ((A - y) / ((B - y) * lam)) : K[X]).roots := by
    rw [hEq, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hc)]
  rw [cnfFiber, hroots, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
    Polynomial.natDegree_X_pow_sub_C]

/-! ## Two critical values in one fibre -/

omit [CharZero K] in
/-- If both critical values lie over the same point then `A^p = B^p`. -/
theorem pow_eq_pow_of_same_fiber {p : ℕ} {A B lam : K} (hlam : lam ≠ 0)
    (hA : 1 - lam * A ^ p ≠ 0) (hB : 1 - lam * B ^ p ≠ 0)
    (h : (A - B * lam * A ^ p) / (1 - lam * A ^ p)
        = (A - B * lam * B ^ p) / (1 - lam * B ^ p)) :
    (A - B) * (A ^ p - B ^ p) = 0 := by
  rw [div_eq_div_iff hA hB] at h
  have hkey : lam * ((A - B) * (A ^ p - B ^ p)) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hkey).resolve_left hlam

/-! ## The endgame -/

/-- **With the support inside the two critical values there is no solution.** -/
theorem cnf_no_cocycle_of_support {p : ℕ} (hp : 2 ≤ p) {A B lam : K} (hlam : lam ≠ 0)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (hApole : 1 - lam * A ^ p ≠ 0)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} (hk : k ≠ 0) {b : K} (hb : b ≠ 0) {F : RatFunc K} (hF : F ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k (RatFunc.C b) 0 F)
    (hsupp : ∀ z : K, z ≠ A → z ≠ B → ratOrder F z = 0) : False := by
  have hp0 : 0 < p := by omega
  have h0 : ratOrder F 0 = 0 := hsupp 0 (Ne.symm hA0) (Ne.symm hB0)
  have hAord : ratOrder F A = 0 := by
    by_contra hne
    have hreg := cnf_transport_regular hp0 hlam hAB hb hF heq hA0 hApole
    have hyne : ratOrder F ((A - B * lam * A ^ p) / (1 - lam * A ^ p)) ≠ 0 := by
      rw [hreg]; exact hne
    have hyA : (A - B * lam * A ^ p) / (1 - lam * A ^ p) ≠ A := by
      intro h
      rw [div_eq_iff hApole] at h
      have hz : lam * A ^ p * (A - B) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact (mul_ne_zero hlam (pow_ne_zero _ hA0)) h1
      · exact hAB (by linear_combination h2)
    have hyB : (A - B * lam * A ^ p) / (1 - lam * A ^ p) ≠ B := by
      intro h
      rw [div_eq_iff hApole] at h
      exact hAB (by linear_combination h)
    exact hyne (hsupp _ hyA hyB)
  have hcrit := cnf_transport_critical hp0 hlam hAB hb hF heq
  rw [hAord, h0, zero_mul, zero_add] at hcrit
  have hp1 : ((p : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    omega
  exact hk ((mul_eq_zero.mp hcrit).resolve_right hp1)

/-! ## The counting -/

/-- **The support of a solution lies in the two critical values.** -/
theorem cnf_support_subset [IsAlgClosed K] {p : ℕ} (hp : 3 ≤ p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) (hpow : A ^ p ≠ B ^ p)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b : K} (hb : b ≠ 0) {F : RatFunc K} (hF : F ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k (RatFunc.C b) 0 F)
    (y₀ : K) (hy₀A : y₀ ≠ A) (hy₀B : y₀ ≠ B) : ratOrder F y₀ = 0 := by
  classical
  by_contra hy₀
  have hp0 : 0 < p := by omega
  set S : Finset K := (finite_support_ratOrder hF).toFinset with hS
  have hmemS : ∀ z : K, z ∈ S ↔ ratOrder F z ≠ 0 := by
    intro z; rw [hS, Set.Finite.mem_toFinset]; rfl
  set T : Finset K := (S.erase A).erase B with hT
  have hmemT : ∀ z : K, z ∈ T ↔ (z ≠ B ∧ z ≠ A ∧ ratOrder F z ≠ 0) := by
    intro z
    constructor
    · intro hz
      rw [hT, Finset.mem_erase, Finset.mem_erase] at hz
      exact ⟨hz.1, hz.2.1, (hmemS z).mp hz.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      rw [hT, Finset.mem_erase, Finset.mem_erase]
      exact ⟨h1, h2, (hmemS z).mpr h3⟩
  have hy₀T : y₀ ∈ T := (hmemT y₀).mpr ⟨hy₀B, hy₀A, hy₀⟩
  -- every fibre over a point of `T` lies in the support
  have hfib : ∀ y ∈ T, cnfFiber p A B lam y ⊆ S := by
    intro y hy z hz
    obtain ⟨hyB, hyA, hyord⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hden := cnfFiber_den_ne_zero hp0 hAB hc hz
    have hval := cnfFiber_value hp0 hAB hc hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega : p ≠ 0), mul_zero, mul_zero, sub_zero, sub_zero,
        div_one] at hval
      exact hyA hval.symm
    have hreg := cnf_transport_regular hp0 hlam hAB hb hF heq hz0 hden
    rw [hval] at hreg
    exact (hmemS z).mpr (by rw [← hreg]; exact hyord)
  have hcard : ∀ y ∈ T, (cnfFiber p A B lam y).card = p := by
    intro y hy
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    exact card_cnfFiber hp0 hlam hyA hyB
  have hdisj : (↑T : Set K).PairwiseDisjoint (cnfFiber p A B lam) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    obtain ⟨hyB, -, -⟩ := (hmemT y).mp hy
    obtain ⟨hyB', -, -⟩ := (hmemT y').mp hy'
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hc' : (B - y') * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB')) hlam
    exact hne ((cnfFiber_value hp0 hAB hc hz).symm.trans (cnfFiber_value hp0 hAB hc' hz'))
  have hcount : p * T.card ≤ S.card := by
    have hsub : T.biUnion (cnfFiber p A B lam) ⊆ S := by
      intro z hz
      obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz
      exact hfib y hy hzy
    have hcc : (T.biUnion (cnfFiber p A B lam)).card = p * T.card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
      ring
    rw [← hcc]
    exact Finset.card_le_card hsub
  have hSle : S.card ≤ T.card + 2 := by
    have h1 : (S.erase A).card - 1 ≤ ((S.erase A).erase B).card :=
      Finset.pred_card_le_card_erase
    have h2 : S.card - 1 ≤ (S.erase A).card := Finset.pred_card_le_card_erase
    rw [hT]
    omega
  have hTlow : p - 2 ≤ T.card := by
    have hsub : ((cnfFiber p A B lam y₀).erase A).erase B ⊆ T := by
      rw [hT]
      exact Finset.erase_subset_erase _ (Finset.erase_subset_erase _ (hfib y₀ hy₀T))
    have h1 : ((cnfFiber p A B lam y₀).erase A).card - 1
        ≤ (((cnfFiber p A B lam y₀).erase A).erase B).card := Finset.pred_card_le_card_erase
    have h2 : (cnfFiber p A B lam y₀).card - 1 ≤ ((cnfFiber p A B lam y₀).erase A).card :=
      Finset.pred_card_le_card_erase
    have h3 := Finset.card_le_card hsub
    have h4 := hcard y₀ hy₀T
    omega
  have hT1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨y₀, hy₀T⟩
  -- the count leaves only degree three, with both critical values in one fibre
  have hpeq : p = 3 := by
    rcases Nat.lt_or_ge p 4 with h | h
    · omega
    · exfalso
      have : 4 * T.card ≤ p * T.card := Nat.mul_le_mul h (le_refl T.card)
      omega
  subst hpeq
  have hTcard : T.card = 1 := by omega
  have hScard : S.card = 3 := by omega
  have hAS : A ∈ S := by
    by_contra hmem
    rw [hT, Finset.erase_eq_of_notMem hmem] at hTcard
    have := Finset.pred_card_le_card_erase (s := S) (a := B)
    omega
  have hBS : B ∈ S.erase A := by
    by_contra hmem
    rw [hT, Finset.erase_eq_of_notMem hmem, Finset.card_erase_of_mem hAS] at hTcard
    omega
  have hfibS : cnfFiber 3 A B lam y₀ = S :=
    Finset.eq_of_subset_of_card_le (hfib y₀ hy₀T) (by rw [hcard y₀ hy₀T, hScard])
  have hc : (B - y₀) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hy₀B)) hlam
  have hAfib : A ∈ cnfFiber 3 A B lam y₀ := by rw [hfibS]; exact hAS
  have hBfib : B ∈ cnfFiber 3 A B lam y₀ := by
    rw [hfibS]; exact Finset.mem_of_mem_erase hBS
  have hvA := cnfFiber_value hp0 hAB hc hAfib
  have hvB := cnfFiber_value hp0 hAB hc hBfib
  have hkey := pow_eq_pow_of_same_fiber (p := 3) hlam
    (cnfFiber_den_ne_zero hp0 hAB hc hAfib) (cnfFiber_den_ne_zero hp0 hAB hc hBfib)
    (hvA.trans hvB.symm)
  rcases mul_eq_zero.mp hkey with h | h
  · exact hAB (by linear_combination h)
  · exact hpow (by linear_combination h)

/-- **The cyclic normal form of degree at least three carries no invariant differential.** -/
theorem cnf_no_cocycle [IsAlgClosed K] {p : ℕ} (hp : 3 ≤ p) {A B lam : K} (hlam : lam ≠ 0)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (hpow : A ^ p ≠ B ^ p)
    (hApole : 1 - lam * A ^ p ≠ 0)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} (hk : k ≠ 0) {b : K} (hb : b ≠ 0) {F : RatFunc K} (hF : F ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k (RatFunc.C b) 0 F) : False :=
  cnf_no_cocycle_of_support (by omega) hlam hA0 hB0 hAB hApole hk hb hF heq
    (fun z hzA hzB => cnf_support_subset hp hlam hAB hpow hb hF heq z hzA hzB)

end

end GaloisForLFunctions.HTGeometry
