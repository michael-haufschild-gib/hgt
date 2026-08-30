import GaloisForLFunctions.HTGeometry.RittCyclicNoCocycle

/-!
# Degree two

In degree two the fibre count alone leaves configurations standing, because a fibre has only two
points and the two critical values can absorb both.  What closes the case is that a fibre of
`h(w) = (A − Bλw²)/(1 − λw²)` is stable under `w ↦ −w`, so every fibre over a point of the support
is a pair `{z, −z}`.

If the support has two points outside the critical values, the two fibres over them partition the
support into two such pairs, and the pairs containing `A` and `B` are `{A,−A}` and `{B,−B}`; so the
image of `A` is one of `−A`, `−B`.  If it has one, the fibre over it is `{c, −c}` with `c` a critical
value and `−c` that point, so either `h(A) = −A`, or `h(B) = −B` and then the ramification identity
at the origin forces a nonzero order at `A` whose image again lands on `−B`.

So the two exclusions `h(A) ≠ −A` and `h(A) ≠ −B` — explicit inequalities in `A`, `B`, `λ` — finish
degree two, and the normal form of any degree carries no invariant differential.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

omit [CharZero K] in
/-- A fibre in degree two is stable under the sign change. -/
theorem neg_mem_cnfFiber_two [DecidableEq K] {A B lam y : K} (hc : (B - y) * lam ≠ 0) {z : K}
    (hz : z ∈ cnfFiber 2 A B lam y) : -z ∈ cnfFiber 2 A B lam y := by
  rw [mem_cnfFiber_iff (by norm_num) hc] at hz ⊢
  rw [neg_pow]
  simpa using hz

omit [CharZero K] in
/-- The origin lies over the critical value at the origin. -/
theorem zero_mem_cnfFiber_iff [DecidableEq K] {p : ℕ} (hp : 0 < p) {A B lam y : K}
    (hc : (B - y) * lam ≠ 0) : (0 : K) ∈ cnfFiber p A B lam y ↔ y = A := by
  rw [mem_cnfFiber_iff hp hc, zero_pow (by omega : p ≠ 0), mul_zero]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- **In degree two a fibre over a non-critical value is a sign pair.** -/
theorem cnfFiber_two_eq_pair [DecidableEq K] [IsAlgClosed K] {A B lam y : K} (hlam : lam ≠ 0)
    (hyA : y ≠ A) (hyB : y ≠ B) {z : K} (hz : z ∈ cnfFiber 2 A B lam y) :
    cnfFiber 2 A B lam y = {z, -z} := by
  have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    exact hyA ((zero_mem_cnfFiber_iff (by norm_num) hc).mp hz)
  have hzn : z ≠ -z := by
    intro h
    exact hz0 (by linear_combination h / 2)
  have hsub : ({z, -z} : Finset K) ⊆ cnfFiber 2 A B lam y := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hz
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact neg_mem_cnfFiber_two hc hz
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [card_cnfFiber (by norm_num) hlam hyA hyB,
    Finset.card_insert_of_notMem (by simpa using hzn), Finset.card_singleton]

/-- **The support of a solution in degree two lies in the two critical values.** -/
theorem cnf_support_subset_two [IsAlgClosed K] {A B lam : K} (hlam : lam ≠ 0)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (hpow : A ^ 2 ≠ B ^ 2)
    (hApole : 1 - lam * A ^ 2 ≠ 0)
    (hnegA : (A - B * lam * A ^ 2) / (1 - lam * A ^ 2) ≠ -A)
    (hnegB : (A - B * lam * A ^ 2) / (1 - lam * A ^ 2) ≠ -B)
    {hP : ¬ ∃ c : K, cnf 2 A B lam = RatFunc.C c}
    {k : ℤ} (hk : k ≠ 0) {b : K} (hb : b ≠ 0) {F : RatFunc K} (hF : F ≠ 0)
    (heq : IsRatAffineTransport (cnf 2 A B lam) hP k (RatFunc.C b) 0 F)
    (y₀ : K) (hy₀A : y₀ ≠ A) (hy₀B : y₀ ≠ B) : ratOrder F y₀ = 0 := by
  classical
  by_contra hy₀
  have hp0 : (0 : ℕ) < 2 := by norm_num
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
  have hfib : ∀ y ∈ T, cnfFiber 2 A B lam y ⊆ S := by
    intro y hy z hz
    obtain ⟨hyB, hyA, hyord⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hden := cnfFiber_den_ne_zero hp0 hAB hc hz
    have hval := cnfFiber_value hp0 hAB hc hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      exact hyA ((zero_mem_cnfFiber_iff hp0 hc).mp hz)
    have hreg := cnf_transport_regular hp0 hlam hAB hb hF heq hz0 hden
    rw [hval] at hreg
    exact (hmemS z).mpr (by rw [← hreg]; exact hyord)
  have hcard : ∀ y ∈ T, (cnfFiber 2 A B lam y).card = 2 := by
    intro y hy
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    exact card_cnfFiber hp0 hlam hyA hyB
  have hdisj : (↑T : Set K).PairwiseDisjoint (cnfFiber 2 A B lam) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    obtain ⟨hyB, -, -⟩ := (hmemT y).mp hy
    obtain ⟨hyB', -, -⟩ := (hmemT y').mp hy'
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hc' : (B - y') * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB')) hlam
    exact hne ((cnfFiber_value hp0 hAB hc hz).symm.trans (cnfFiber_value hp0 hAB hc' hz'))
  have hcount : 2 * T.card ≤ S.card := by
    have hsub : T.biUnion (cnfFiber 2 A B lam) ⊆ S := by
      intro z hz
      obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz
      exact hfib y hy hzy
    have hcc : (T.biUnion (cnfFiber 2 A B lam)).card = 2 * T.card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
      ring
    rw [← hcc]
    exact Finset.card_le_card hsub
  have hSle : S.card ≤ T.card + 2 := by
    have h1 : (S.erase A).card - 1 ≤ ((S.erase A).erase B).card := Finset.pred_card_le_card_erase
    have h2 : S.card - 1 ≤ (S.erase A).card := Finset.pred_card_le_card_erase
    rw [hT]; omega
  have hT1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨y₀, hy₀T⟩
  have hT2 : T.card ≤ 2 := by omega
  -- the value of the map at the critical value `A`
  have hAimg : (A - B * lam * A ^ 2) / (1 - lam * A ^ 2) ≠ A := by
    intro h
    rw [div_eq_iff hApole] at h
    have hz : lam * A ^ 2 * (A - B) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (mul_ne_zero hlam (pow_ne_zero _ hA0)) h1
    · exact hAB (by linear_combination h2)
  have hAimgB : (A - B * lam * A ^ 2) / (1 - lam * A ^ 2) ≠ B := by
    intro h
    rw [div_eq_iff hApole] at h
    exact hAB (by linear_combination h)
  have hAimgT : ratOrder F A ≠ 0 → (A - B * lam * A ^ 2) / (1 - lam * A ^ 2) ∈ T := by
    intro hAne
    have hreg := cnf_transport_regular hp0 hlam hAB hb hF heq hA0 hApole
    exact (hmemT _).mpr ⟨hAimgB, hAimg, by rw [hreg]; exact hAne⟩
  interval_cases h : T.card
  · -- one point outside the critical values
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h
    have hyT : y ∈ T := by rw [hy]; exact Finset.mem_singleton_self y
    obtain ⟨hyB, hyA, hyord⟩ := (hmemT y).mp hyT
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    -- the fibre over `y` is a sign pair whose members lie in the support
    obtain ⟨z, hz⟩ : ∃ z : K, z ∈ cnfFiber 2 A B lam y := by
      have := hcard y hyT
      exact Finset.card_pos.mp (by omega)
    have hfibeq := cnfFiber_two_eq_pair hlam hyA hyB hz
    have hzn : -z ∈ cnfFiber 2 A B lam y := neg_mem_cnfFiber_two hc hz
    have hmemcrit : ∀ x ∈ cnfFiber 2 A B lam y, x ≠ A → x ≠ B → x = y := by
      intro x hx hxA hxB
      have hxS : x ∈ S := hfib y hyT hx
      have hxT : x ∈ T := (hmemT x).mpr ⟨hxB, hxA, (hmemS x).mp hxS⟩
      rw [hy, Finset.mem_singleton] at hxT
      exact hxT
    have hz0 : z ≠ 0 := by
      intro hzz
      rw [hzz] at hz
      exact hyA ((zero_mem_cnfFiber_iff hp0 hc).mp hz)
    have hzne : z ≠ -z := fun hh => hz0 (by linear_combination hh / 2)
    -- one of the two fibre points is a critical value
    have hcrit : (z = A ∨ z = B) ∨ (-z = A ∨ -z = B) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
      exact hzne ((hmemcrit z hz h1 h2).trans (hmemcrit (-z) hzn h3 h4).symm)
    -- the other one is `y`
    have hboth : ¬ (A ∈ cnfFiber 2 A B lam y ∧ B ∈ cnfFiber 2 A B lam y) := by
      rintro ⟨hAf, hBf⟩
      have hkey := pow_eq_pow_of_same_fiber (p := 2) hlam
        (cnfFiber_den_ne_zero hp0 hAB hc hAf) (cnfFiber_den_ne_zero hp0 hAB hc hBf)
        ((cnfFiber_value hp0 hAB hc hAf).trans (cnfFiber_value hp0 hAB hc hBf).symm)
      rcases mul_eq_zero.mp hkey with h' | h'
      · exact hAB (by linear_combination h')
      · exact hpow (by linear_combination h')
    have hAcase : A ∈ cnfFiber 2 A B lam y → False := by
      intro hAf
      have hnA : -A ∈ cnfFiber 2 A B lam y := neg_mem_cnfFiber_two hc hAf
      have hnAA : -A ≠ A := fun hh => hA0 (by linear_combination -hh / 2)
      have hnAB : -A ≠ B := by
        intro hh
        exact hpow (by linear_combination (A - B) * hh)
      have hyv : y = -A := (hmemcrit (-A) hnA hnAA hnAB).symm
      exact hnegA (by rw [cnfFiber_value hp0 hAB hc hAf, hyv])
    have hBcase : B ∈ cnfFiber 2 A B lam y → False := by
      intro hBf
      have hnB : -B ∈ cnfFiber 2 A B lam y := neg_mem_cnfFiber_two hc hBf
      have hnBB : -B ≠ B := fun hh => hB0 (by linear_combination -hh / 2)
      have hnBA : -B ≠ A := by
        intro hh
        exact hpow (by linear_combination (A - B) * hh)
      have hyv : y = -B := (hmemcrit (-B) hnB hnBB hnBA).symm
      -- the origin carries no order
      have h0S : (0 : K) ∉ S := by
        intro h0
        have : (0 : K) ∈ T := (hmemT 0).mpr ⟨Ne.symm hB0, Ne.symm hA0, (hmemS 0).mp h0⟩
        rw [hy, Finset.mem_singleton] at this
        rw [hyv] at this
        exact hB0 (by linear_combination -this)
      have h0 : ratOrder F 0 = 0 := by
        by_contra hne
        exact h0S ((hmemS 0).mpr hne)
      have hcrit2 := cnf_transport_critical hp0 hlam hAB hb hF heq
      rw [h0] at hcrit2
      have hAne : ratOrder F A ≠ 0 := by
        intro hz'
        rw [hz'] at hcrit2
        norm_num at hcrit2
        exact hk hcrit2
      have himg := hAimgT hAne
      rw [hy, Finset.mem_singleton, hyv] at himg
      exact hnegB himg
    rcases hcrit with (rfl | rfl) | h'
    · exact hAcase hz
    · exact hBcase hz
    · rcases h' with h' | h'
      · exact hAcase (by rw [← h']; exact hzn)
      · exact hBcase (by rw [← h']; exact hzn)
  · -- two points outside the critical values
    have hS4 : S.card = 4 := by omega
    have hAS : A ∈ S := by
      by_contra hmem
      rw [hT, Finset.erase_eq_of_notMem hmem] at h
      have := Finset.pred_card_le_card_erase (s := S) (a := B)
      omega
    have hBS : B ∈ S := by
      by_contra hmem
      have hBe : (S.erase A).erase B = S.erase A :=
        Finset.erase_eq_of_notMem (fun hh => hmem (Finset.mem_of_mem_erase hh))
      rw [hT, hBe, Finset.card_erase_of_mem hAS] at h
      omega
    have hunion : S = T.biUnion (cnfFiber 2 A B lam) := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro z hz
        obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz
        exact hfib y hy hzy
      · rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul,
          h, hS4]
    obtain ⟨y, hy, hAf⟩ := Finset.mem_biUnion.mp (hunion ▸ hAS)
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hyval : (A - B * lam * A ^ 2) / (1 - lam * A ^ 2) = y :=
      cnfFiber_value hp0 hAB hc hAf
    have hfibeq : cnfFiber 2 A B lam y = {A, -A} := cnfFiber_two_eq_pair hlam hyA hyB hAf
    obtain ⟨y', hy', hBf⟩ := Finset.mem_biUnion.mp (hunion ▸ hBS)
    obtain ⟨hyB', hyA', -⟩ := (hmemT y').mp hy'
    have hfibeq' : cnfFiber 2 A B lam y' = {B, -B} := by
      have hc' : (B - y') * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB')) hlam
      exact cnfFiber_two_eq_pair hlam hyA' hyB' hBf
    -- the two fibres are the sign pairs of the critical values, so `T` is their negatives
    have hyT : y ∈ S := hfib y hy hAf
    have hyU : y ∈ T := hy
    have hymem : y ∈ ({A, -A} : Finset K) ∪ ({B, -B} : Finset K) := by
      have : y ∈ T.biUnion (cnfFiber 2 A B lam) := hunion ▸ hyT
      obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp this
      have hne : u = y ∨ u = y' ∨ (u ≠ y ∧ u ≠ y') := by tauto
      rcases eq_or_ne u y with rfl | hu1
      · exact Finset.mem_union_left _ (hfibeq ▸ hyu)
      · rcases eq_or_ne u y' with rfl | hu2
        · exact Finset.mem_union_right _ (hfibeq' ▸ hyu)
        · exfalso
          have hsub : ({y, y'} : Finset K) ⊆ T := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hy
            · rw [Finset.mem_singleton] at hx; subst hx; exact hy'
          have hyy' : y ≠ y' := by
            intro hh
            rw [hh] at hfibeq
            rw [hfibeq] at hfibeq'
            have hBmem : B ∈ ({A, -A} : Finset K) := hfibeq' ▸ Finset.mem_insert_self B {-B}
            rcases Finset.mem_insert.mp hBmem with hh1 | hh1
            · exact hAB hh1.symm
            · rw [Finset.mem_singleton] at hh1
              exact hpow (by linear_combination (A - B) * hh1)
          have hcard2 : ({y, y'} : Finset K).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simpa using hyy'), Finset.card_singleton]
          have := Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, h])
          have humem : u ∈ ({y, y'} : Finset K) := this ▸ hu
          rcases Finset.mem_insert.mp humem with hh | hh
          · exact hu1 hh
          · rw [Finset.mem_singleton] at hh; exact hu2 hh
    rw [Finset.mem_union] at hymem
    rcases hymem with hm | hm
    · rcases Finset.mem_insert.mp hm with hh | hh
      · exact hyA hh
      · rw [Finset.mem_singleton] at hh
        exact hnegA (by rw [hyval, hh])
    · rcases Finset.mem_insert.mp hm with hh | hh
      · exact hyB hh
      · rw [Finset.mem_singleton] at hh
        exact hnegB (by rw [hyval, hh])

end

end GaloisForLFunctions.HTGeometry
