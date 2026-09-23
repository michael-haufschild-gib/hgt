import GaloisForLFunctions.HTGeometry.RittCyclicOrders
import GaloisForLFunctions.HTGeometry.RittCyclicNoCocycle
import GaloisForLFunctions.HTGeometry.RittCyclicNoCocycleTwo

/-!
# Poles travel backward along the cyclic normal form

The general pole-transport law for a rational map, specialised to `h(w) = (A − Bλw^p)/(1 − λw^p)`.
Away from the origin the derivative of the normal form is a unit and the map is regular, so at any
such point where the coefficient of an affine transport equation is a unit and its inhomogeneity is
regular, a pole of the solution at the image forces a pole at the point itself.

This is the step the inhomogeneous branch of the tower descent needs: unlike the homogeneous case,
which is settled by the order identity, the affine case has to move poles, and it can do so exactly
where the inhomogeneity is regular.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

/-- **A pole travels backward along the cyclic normal form.** -/
theorem cnf_pole_backward {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0) (hAB : A ≠ B)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k b c a)
    {z : K} (hz0 : z ≠ 0) (hz : 1 - lam * z ^ p ≠ 0)
    (hbz : ratOrder b z = 0) (hcz : 0 ≤ ratOrder c z)
    (hpole : ratOrder a ((A - B * lam * z ^ p) / (1 - lam * z ^ p)) < 0) :
    ratOrder a z < 0 := by
  refine ratAffineTransport_pole_backward hP ha hb (ratFuncDeriv_cnf_ne_zero hp hlam hAB) heq
    (denom_cnf_eval_ne_zero A B lam hz)
    (ratOrder_ratFuncDeriv_cnf_ne_zero hp hlam hAB hz0 hz) hbz hcz ?_
  rwa [ratValue_cnf hp A B lam hz]

/-- **A pole on an injective critical-free backward orbit of the normal form is impossible.** -/
theorem cnf_no_pole_of_backward_orbit {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k b c a)
    {w : ℕ → K} (hw0 : ∀ n, w (n + 1) ≠ 0) (hwden : ∀ n, 1 - lam * (w (n + 1)) ^ p ≠ 0)
    (hstep : ∀ n, (A - B * lam * (w (n + 1)) ^ p) / (1 - lam * (w (n + 1)) ^ p) = w n)
    (hbw : ∀ n, ratOrder b (w (n + 1)) = 0) (hcw : ∀ n, 0 ≤ ratOrder c (w (n + 1)))
    (hinj : Function.Injective w) (hpole : ratOrder a (w 0) < 0) : False := by
  have horbit : ∀ n : ℕ, ratOrder a (w n) < 0 := by
    intro n
    induction n with
    | zero => exact hpole
    | succ n ih =>
        exact cnf_pole_backward hp hlam hAB ha hb heq (hw0 n) (hwden n) (hbw n) (hcw n)
          (by rw [hstep n]; exact ih)
  have hsub : Set.range w ⊆ {z : K | ratOrder a z ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    exact ne_of_lt (horbit n)
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder ha).subset hsub)

/-- **The pole count of an affine transport equation.**  Off a finite bad set the fibre over every
pole consists of poles, so the poles outside the two critical values are bounded by the bad set. -/
theorem cnf_pole_count [IsAlgClosed K] [DecidableEq K] {p : ℕ} (hp : 0 < p) {A B lam : K} (hlam : lam ≠ 0)
    (hAB : A ≠ B) {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k b c a)
    (E : Finset K)
    (hE : ∀ z : K, z ∉ E → ratOrder b z = 0 ∧ 0 ≤ ratOrder c z) :
    ∀ P : Finset K, (∀ z : K, z ∈ P ↔ ratOrder a z < 0) →
      (p - 1) * ((P.erase A).erase B).card ≤ E.card + 2 := by
  classical
  intro P hPmem
  set T : Finset K := (P.erase A).erase B with hT
  have hmemT : ∀ z : K, z ∈ T ↔ (z ≠ B ∧ z ≠ A ∧ ratOrder a z < 0) := by
    intro z
    constructor
    · intro hz
      rw [hT, Finset.mem_erase, Finset.mem_erase] at hz
      exact ⟨hz.1, hz.2.1, (hPmem z).mp hz.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      rw [hT, Finset.mem_erase, Finset.mem_erase]
      exact ⟨h1, h2, (hPmem z).mpr h3⟩
  -- every fibre point over a pole is a pole or bad
  have hfib : ∀ y ∈ T, cnfFiber p A B lam y ⊆ P ∪ E := by
    intro y hy z hz
    obtain ⟨hyB, hyA, hyord⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hval := cnfFiber_value hp hAB hc hz
    have hzden : 1 - lam * z ^ p ≠ 0 := cnfFiber_den_ne_zero hp hAB hc hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, mem_cnfFiber_iff hp hc, zero_pow (by omega : p ≠ 0), mul_zero] at hz
      exact hyA (by linear_combination -hz)
    by_cases hzE : z ∈ E
    · exact Finset.mem_union_right _ hzE
    · obtain ⟨hzb, hzc⟩ := hE z hzE
      refine Finset.mem_union_left _ ((hPmem z).mpr ?_)
      refine cnf_pole_backward hp hlam hAB ha hb heq hz0 hzden hzb hzc ?_
      rw [hval]
      exact hyord
  have hcard : ∀ y ∈ T, (cnfFiber p A B lam y).card = p := by
    intro y hy
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    exact card_cnfFiber hp hlam hyA hyB
  have hdisj : (↑T : Set K).PairwiseDisjoint (cnfFiber p A B lam) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    obtain ⟨hyB, -, -⟩ := (hmemT y).mp hy
    obtain ⟨hyB', -, -⟩ := (hmemT y').mp hy'
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hc' : (B - y') * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB')) hlam
    exact hne ((cnfFiber_value hp hAB hc hz).symm.trans (cnfFiber_value hp hAB hc' hz'))
  have hcount : p * T.card ≤ P.card + E.card := by
    have hsub : T.biUnion (cnfFiber p A B lam) ⊆ P ∪ E := by
      intro z hz
      obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz
      exact hfib y hy hzy
    have hcc : (T.biUnion (cnfFiber p A B lam)).card = p * T.card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
      ring
    have hle := Finset.card_le_card hsub
    rw [hcc] at hle
    exact le_trans hle (Finset.card_union_le _ _)
  have hPle : P.card ≤ T.card + 2 := by
    have h1 : (P.erase A).card - 1 ≤ ((P.erase A).erase B).card := Finset.pred_card_le_card_erase
    have h2 : P.card - 1 ≤ (P.erase A).card := Finset.pred_card_le_card_erase
    rw [hT]
    omega
  have hmul : (p - 1) * T.card + T.card = p * T.card := by
    cases p with
    | zero => omega
    | succ n => simp; ring
  omega

/-- **With unit coefficient and regular inhomogeneity there are no poles off the critical values.**
In degree at least four the count leaves no room. -/
theorem cnf_no_pole_of_regular_data [IsAlgClosed K] [DecidableEq K] {p : ℕ} (hp : 4 ≤ p)
    {A B lam : K} (hlam : lam ≠ 0) (hAB : A ≠ B)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k b c a)
    (hbreg : ∀ z : K, ratOrder b z = 0) (hcreg : ∀ z : K, 0 ≤ ratOrder c z)
    {z : K} (hzA : z ≠ A) (hzB : z ≠ B) : 0 ≤ ratOrder a z := by
  classical
  by_contra hpole
  rw [not_le] at hpole
  set P : Finset K := ((finite_support_ratOrder ha).toFinset).filter
    (fun w => ratOrder a w < 0) with hPdef
  have hPmem : ∀ w : K, w ∈ P ↔ ratOrder a w < 0 := by
    intro w
    rw [hPdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨ne_of_lt h, h⟩
  have hcount := cnf_pole_count (by omega : 0 < p) hlam hAB ha hb heq ∅
    (fun w _ => ⟨hbreg w, hcreg w⟩) P hPmem
  rw [Finset.card_empty] at hcount
  have hmem : z ∈ (P.erase A).erase B := by
    rw [Finset.mem_erase, Finset.mem_erase, hPmem]
    exact ⟨hzB, hzA, hpole⟩
  have hpos : 0 < ((P.erase A).erase B).card := Finset.card_pos.mpr ⟨z, hmem⟩
  have hle : (p - 1) * 1 ≤ (p - 1) * ((P.erase A).erase B).card :=
    Nat.mul_le_mul_left _ hpos
  omega

/-- **No poles off the critical values in degree at least three.**  The one configuration the count
leaves in degree three puts both critical values in a single fibre, which forces `A^p = B^p`. -/
theorem cnf_no_pole_of_regular_data_three [IsAlgClosed K] [DecidableEq K] {p : ℕ} (hp : 3 ≤ p)
    {A B lam : K} (hlam : lam ≠ 0) (hAB : A ≠ B) (hpow : A ^ p ≠ B ^ p)
    {hP : ¬ ∃ c : K, cnf p A B lam = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsRatAffineTransport (cnf p A B lam) hP k b c a)
    (hbreg : ∀ z : K, ratOrder b z = 0) (hcreg : ∀ z : K, 0 ≤ ratOrder c z)
    {z : K} (hzA : z ≠ A) (hzB : z ≠ B) : 0 ≤ ratOrder a z := by
  classical
  by_contra hpole
  rw [not_le] at hpole
  have hp0 : 0 < p := by omega
  set P : Finset K := ((finite_support_ratOrder ha).toFinset).filter
    (fun w => ratOrder a w < 0) with hPdef
  have hPmem : ∀ w : K, w ∈ P ↔ ratOrder a w < 0 := by
    intro w
    rw [hPdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  set T : Finset K := (P.erase A).erase B with hT
  have hmemT : ∀ w : K, w ∈ T ↔ (w ≠ B ∧ w ≠ A ∧ ratOrder a w < 0) := by
    intro w
    constructor
    · intro hw
      rw [hT, Finset.mem_erase, Finset.mem_erase] at hw
      exact ⟨hw.1, hw.2.1, (hPmem w).mp hw.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      rw [hT, Finset.mem_erase, Finset.mem_erase]
      exact ⟨h1, h2, (hPmem w).mpr h3⟩
  have hzT : z ∈ T := (hmemT z).mpr ⟨hzB, hzA, hpole⟩
  have hfib : ∀ y ∈ T, cnfFiber p A B lam y ⊆ P := by
    intro y hy w hw
    obtain ⟨hyB, hyA, hyord⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hwden : 1 - lam * w ^ p ≠ 0 := cnfFiber_den_ne_zero hp0 hAB hc hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, mem_cnfFiber_iff hp0 hc, zero_pow (by omega : p ≠ 0), mul_zero] at hw
      exact hyA (by linear_combination -hw)
    refine (hPmem w).mpr (cnf_pole_backward hp0 hlam hAB ha hb heq hw0 hwden (hbreg w)
      (hcreg w) ?_)
    rw [cnfFiber_value hp0 hAB hc hw]
    exact hyord
  have hcard : ∀ y ∈ T, (cnfFiber p A B lam y).card = p := by
    intro y hy
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    exact card_cnfFiber hp0 hlam hyA hyB
  have hdisj : (↑T : Set K).PairwiseDisjoint (cnfFiber p A B lam) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr ?_
    intro w hw hw'
    obtain ⟨hyB, -, -⟩ := (hmemT y).mp hy
    obtain ⟨hyB', -, -⟩ := (hmemT y').mp hy'
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hc' : (B - y') * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB')) hlam
    exact hne ((cnfFiber_value hp0 hAB hc hw).symm.trans (cnfFiber_value hp0 hAB hc' hw'))
  have hcount : p * T.card ≤ P.card := by
    have hsub : T.biUnion (cnfFiber p A B lam) ⊆ P := by
      intro w hw
      obtain ⟨y, hy, hwy⟩ := Finset.mem_biUnion.mp hw
      exact hfib y hy hwy
    have hcc : (T.biUnion (cnfFiber p A B lam)).card = p * T.card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
      ring
    rw [← hcc]
    exact Finset.card_le_card hsub
  have hPle : P.card ≤ T.card + 2 := by
    have h1 : (P.erase A).card - 1 ≤ ((P.erase A).erase B).card := Finset.pred_card_le_card_erase
    have h2 : P.card - 1 ≤ (P.erase A).card := Finset.pred_card_le_card_erase
    rw [hT]; omega
  have hT1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨z, hzT⟩
  have h3t : 3 * T.card ≤ p * T.card := Nat.mul_le_mul hp (le_refl T.card)
  have hTcard : T.card = 1 := by omega
  rw [hTcard, mul_one] at hcount h3t
  rw [hTcard] at hPle
  have hp3 : p = 3 := by omega
  have hPcard3 : P.card = 3 := by omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hTcard
  have hyT : y ∈ T := by rw [hy]; exact Finset.mem_singleton_self y
  obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hyT
  have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
  have hfibP : cnfFiber p A B lam y = P :=
    Finset.eq_of_subset_of_card_le (hfib y hyT) (by rw [hcard y hyT]; omega)
  have hAP : A ∈ P := by
    by_contra hmem
    rw [hT, Finset.erase_eq_of_notMem hmem] at hTcard
    have := Finset.pred_card_le_card_erase (s := P) (a := B)
    omega
  have hBP : B ∈ P := by
    by_contra hmem
    have hBe : (P.erase A).erase B = P.erase A :=
      Finset.erase_eq_of_notMem (fun hh => hmem (Finset.mem_of_mem_erase hh))
    rw [hT, hBe, Finset.card_erase_of_mem hAP] at hTcard
    omega
  have hAf : A ∈ cnfFiber p A B lam y := by rw [hfibP]; exact hAP
  have hBf : B ∈ cnfFiber p A B lam y := by rw [hfibP]; exact hBP
  have hkey := pow_eq_pow_of_same_fiber hlam
    (cnfFiber_den_ne_zero hp0 hAB hc hAf) (cnfFiber_den_ne_zero hp0 hAB hc hBf)
    ((cnfFiber_value hp0 hAB hc hAf).trans (cnfFiber_value hp0 hAB hc hBf).symm)
  rcases mul_eq_zero.mp hkey with h | h
  · exact hAB (by linear_combination h)
  · exact hpow (by linear_combination h)

/-- **No poles off the critical values in degree two.**  The count permits one or two poles; each
configuration is a sign pair containing a critical value, and the three sign exclusions rule them
all out. -/
theorem cnf_no_pole_of_regular_data_two [IsAlgClosed K] [DecidableEq K]
    {A B lam : K} (hlam : lam ≠ 0) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B)
    (hpow : A ^ (2 : ℕ) ≠ B ^ (2 : ℕ))
    (hnegA : (A - B * lam * A ^ (2 : ℕ)) / (1 - lam * A ^ (2 : ℕ)) ≠ -A)
    (hnegA' : (A - B * lam * A ^ (2 : ℕ)) / (1 - lam * A ^ (2 : ℕ)) ≠ -B)
    (hnegB : (A - B * lam * B ^ (2 : ℕ)) / (1 - lam * B ^ (2 : ℕ)) ≠ -B)
    {hP : ¬ ∃ c : K, cnf 2 A B lam = RatFunc.C c}
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsRatAffineTransport (cnf 2 A B lam) hP k b c a)
    (hbreg : ∀ z : K, ratOrder b z = 0) (hcreg : ∀ z : K, 0 ≤ ratOrder c z)
    {z : K} (hzA : z ≠ A) (hzB : z ≠ B) : 0 ≤ ratOrder a z := by
  classical
  by_contra hpole
  rw [not_le] at hpole
  have hp0 : (0 : ℕ) < 2 := by norm_num
  set P : Finset K := ((finite_support_ratOrder ha).toFinset).filter
    (fun w => ratOrder a w < 0) with hPdef
  have hPmem : ∀ w : K, w ∈ P ↔ ratOrder a w < 0 := by
    intro w
    rw [hPdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  set T : Finset K := (P.erase A).erase B with hT
  have hmemT : ∀ w : K, w ∈ T ↔ (w ≠ B ∧ w ≠ A ∧ ratOrder a w < 0) := by
    intro w
    constructor
    · intro hw
      rw [hT, Finset.mem_erase, Finset.mem_erase] at hw
      exact ⟨hw.1, hw.2.1, (hPmem w).mp hw.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      rw [hT, Finset.mem_erase, Finset.mem_erase]
      exact ⟨h1, h2, (hPmem w).mpr h3⟩
  have hzT : z ∈ T := (hmemT z).mpr ⟨hzB, hzA, hpole⟩
  have hfib : ∀ y ∈ T, cnfFiber 2 A B lam y ⊆ P := by
    intro y hy w hw
    obtain ⟨hyB, hyA, hyord⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hwden : 1 - lam * w ^ (2 : ℕ) ≠ 0 := cnfFiber_den_ne_zero hp0 hAB hc hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, mem_cnfFiber_iff hp0 hc, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero] at hw
      exact hyA (by linear_combination -hw)
    refine (hPmem w).mpr (cnf_pole_backward hp0 hlam hAB ha hb heq hw0 hwden (hbreg w)
      (hcreg w) ?_)
    rw [cnfFiber_value hp0 hAB hc hw]
    exact hyord
  have hcard : ∀ y ∈ T, (cnfFiber 2 A B lam y).card = 2 := by
    intro y hy
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    exact card_cnfFiber hp0 hlam hyA hyB
  have hdisj : (↑T : Set K).PairwiseDisjoint (cnfFiber 2 A B lam) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr ?_
    intro w hw hw'
    obtain ⟨hyB, -, -⟩ := (hmemT y).mp hy
    obtain ⟨hyB', -, -⟩ := (hmemT y').mp hy'
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hc' : (B - y') * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB')) hlam
    exact hne ((cnfFiber_value hp0 hAB hc hw).symm.trans (cnfFiber_value hp0 hAB hc' hw'))
  have hcount : 2 * T.card ≤ P.card := by
    have hsub : T.biUnion (cnfFiber 2 A B lam) ⊆ P := by
      intro w hw
      obtain ⟨y, hy, hwy⟩ := Finset.mem_biUnion.mp hw
      exact hfib y hy hwy
    have hcc : (T.biUnion (cnfFiber 2 A B lam)).card = 2 * T.card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
      ring
    rw [← hcc]
    exact Finset.card_le_card hsub
  have hPle : P.card ≤ T.card + 2 := by
    have h1 : (P.erase A).card - 1 ≤ ((P.erase A).erase B).card := Finset.pred_card_le_card_erase
    have h2 : P.card - 1 ≤ (P.erase A).card := Finset.pred_card_le_card_erase
    rw [hT]; omega
  have hT1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨z, hzT⟩
  have hT2 : T.card ≤ 2 := by omega
  -- name a pole outside the critical values and its fibre
  have hpairstep : ∀ y ∈ T, ∃ w : K, w ≠ 0 ∧ cnfFiber 2 A B lam y = {w, -w} := by
    intro y hy
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    obtain ⟨w, hw⟩ : ∃ w : K, w ∈ cnfFiber 2 A B lam y := by
      have := hcard y hy
      exact Finset.card_pos.mp (by omega)
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, mem_cnfFiber_iff hp0 hc, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero] at hw
      exact hyA (by linear_combination -hw)
    exact ⟨w, hw0, cnfFiber_two_eq_pair hlam hyA hyB hw⟩
  have hnAA : -A ≠ A := fun hh => hA0 (by
    have h2 : (2 : K) * A = 0 := by linear_combination -hh
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
  have hnBB : -B ≠ B := fun hh => hB0 (by
    have h2 : (2 : K) * B = 0 := by linear_combination -hh
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
  have hnAB : -A ≠ B := fun hh => hpow (by linear_combination (B - A) * hh)
  have hnBA : -B ≠ A := fun hh => hpow (by linear_combination (B - A) * hh)
  -- both critical values cannot lie over the same point
  have hnotboth : ∀ y ∈ T, ¬ (A ∈ cnfFiber 2 A B lam y ∧ B ∈ cnfFiber 2 A B lam y) := by
    intro y hy hcon
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    obtain ⟨hAf, hBf⟩ := hcon
    have hkey := pow_eq_pow_of_same_fiber hlam
      (cnfFiber_den_ne_zero hp0 hAB hc hAf) (cnfFiber_den_ne_zero hp0 hAB hc hBf)
      ((cnfFiber_value hp0 hAB hc hAf).trans (cnfFiber_value hp0 hAB hc hBf).symm)
    rcases mul_eq_zero.mp hkey with h | h
    · exact hAB (by linear_combination h)
    · exact hpow (by linear_combination h)
  -- a fibre point outside the critical values is itself a pole outside them
  have hmemcrit : ∀ y ∈ T, ∀ x ∈ cnfFiber 2 A B lam y, x ≠ A → x ≠ B → x ∈ T := by
    intro y hy x hx hxA hxB
    exact (hmemT x).mpr ⟨hxB, hxA, (hPmem x).mp (hfib y hy hx)⟩
  interval_cases h : T.card
  · -- a single pole outside the critical values
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h
    have hyT : y ∈ T := by rw [hy]; exact Finset.mem_singleton_self y
    obtain ⟨hyB, hyA, -⟩ := (hmemT y).mp hyT
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    obtain ⟨w, hw0, hpair⟩ := hpairstep y hyT
    have hwmem : w ∈ cnfFiber 2 A B lam y := by
      rw [hpair]; exact Finset.mem_insert_self w {-w}
    have hnwmem : -w ∈ cnfFiber 2 A B lam y := by
      rw [hpair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (-w))
    have hwne : w ≠ -w := fun hh => hw0 (by linear_combination hh / 2)
    have hone : (w = A ∨ w = B) ∨ (-w = A ∨ -w = B) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
      have hwT := hmemcrit y hyT w hwmem h1 h2
      have hnwT := hmemcrit y hyT (-w) hnwmem h3 h4
      rw [hy, Finset.mem_singleton] at hwT hnwT
      exact hwne (hwT.trans hnwT.symm)
    have hfinish : ∀ x : K, x ∈ cnfFiber 2 A B lam y → (x = A ∨ x = B) → False := by
      intro x hx hxc
      have hnx : -x ∈ cnfFiber 2 A B lam y := neg_mem_cnfFiber_two hc hx
      rcases hxc with rfl | rfl
      · have hyv : y = -x := by
          have := hmemcrit y hyT (-x) hnx hnAA hnAB
          rw [hy, Finset.mem_singleton] at this
          exact this.symm
        exact hnegA (by rw [cnfFiber_value hp0 hAB hc hx, hyv])
      · have hyv : y = -x := by
          have := hmemcrit y hyT (-x) hnx hnBA hnBB
          rw [hy, Finset.mem_singleton] at this
          exact this.symm
        exact hnegB (by rw [cnfFiber_value hp0 hAB hc hx, hyv])
    rcases hone with hc1 | hc1
    · exact hfinish w hwmem hc1
    · exact hfinish (-w) hnwmem hc1
  · -- two poles outside the critical values
    have hPcard : P.card = 4 := by omega
    have hunion : P = T.biUnion (cnfFiber 2 A B lam) := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
        exact hfib t ht hxt
      · rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const,
          smul_eq_mul, h, hPcard]
    have hAP : A ∈ P := by
      by_contra hmem
      rw [hT, Finset.erase_eq_of_notMem hmem] at h
      have := Finset.pred_card_le_card_erase (s := P) (a := B)
      omega
    have hBP : B ∈ P := by
      by_contra hmem
      have hBe : (P.erase A).erase B = P.erase A :=
        Finset.erase_eq_of_notMem (fun hh => hmem (Finset.mem_of_mem_erase hh))
      rw [hT, hBe, Finset.card_erase_of_mem hAP] at h
      omega
    have hAu : A ∈ T.biUnion (cnfFiber 2 A B lam) := by rw [← hunion]; exact hAP
    obtain ⟨y, hy, hAf⟩ := Finset.mem_biUnion.mp hAu
    obtain ⟨hyB, hyA, hyord⟩ := (hmemT y).mp hy
    have hc : (B - y) * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB)) hlam
    have hyval : (A - B * lam * A ^ (2 : ℕ)) / (1 - lam * A ^ (2 : ℕ)) = y :=
      cnfFiber_value hp0 hAB hc hAf
    have hfibeq : cnfFiber 2 A B lam y = {A, -A} := cnfFiber_two_eq_pair hlam hyA hyB hAf
    have hBu : B ∈ T.biUnion (cnfFiber 2 A B lam) := by rw [← hunion]; exact hBP
    obtain ⟨y', hy', hBf⟩ := Finset.mem_biUnion.mp hBu
    obtain ⟨hyB', hyA', -⟩ := (hmemT y').mp hy'
    have hfibeq' : cnfFiber 2 A B lam y' = {B, -B} := by
      have hc' : (B - y') * lam ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hyB')) hlam
      exact cnfFiber_two_eq_pair hlam hyA' hyB' hBf
    have hyy' : y ≠ y' := by
      intro hh
      rw [hh, hfibeq'] at hfibeq
      have hBmem : B ∈ ({A, -A} : Finset K) := by
        rw [← hfibeq]
        exact Finset.mem_insert_self B {-B}
      rcases Finset.mem_insert.mp hBmem with hh1 | hh1
      · exact hAB hh1.symm
      · rw [Finset.mem_singleton] at hh1
        exact hpow (by linear_combination (A - B) * hh1)
    have hTeq : ({y, y'} : Finset K) = T := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hy
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact hy'
      · rw [Finset.card_insert_of_notMem (by simpa using hyy'), Finset.card_singleton, h]
    have hyP : y ∈ P := (hPmem y).mpr hyord
    have hyU : y ∈ T.biUnion (cnfFiber 2 A B lam) := by rw [← hunion]; exact hyP
    obtain ⟨t, ht, hyt⟩ := Finset.mem_biUnion.mp hyU
    rw [← hTeq, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · rw [hfibeq, Finset.mem_insert, Finset.mem_singleton] at hyt
      rcases hyt with hh | hh
      · exact hyA hh
      · exact hnegA (hyval.trans hh)
    · rw [hfibeq', Finset.mem_insert, Finset.mem_singleton] at hyt
      rcases hyt with hh | hh
      · exact hyB hh
      · exact hnegA' (hyval.trans hh)

/-! ## Differentiation does not create poles -/

omit [CharZero K] in
/-- A rational function regular at a point has a denominator that does not vanish there. -/
theorem denom_eval_ne_zero_of_ratOrder_nonneg {f : RatFunc K} (hf : f ≠ 0) {z : K}
    (h : 0 ≤ ratOrder f z) : f.denom.eval z ≠ 0 := by
  intro hz
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  have hdvdden : (X - Polynomial.C z : K[X]) ∣ f.denom := dvd_iff_isRoot.mpr hz
  have hmden : 1 ≤ rootMultiplicity z f.denom :=
    (Polynomial.le_rootMultiplicity_iff hden).mpr (by simpa using hdvdden)
  rw [ratOrder] at h
  have hmnum : 1 ≤ rootMultiplicity z f.num := by omega
  have hdvdnum : (X - Polynomial.C z : K[X]) ∣ f.num := by
    have hd := (Polynomial.le_rootMultiplicity_iff hnum).mp hmnum
    simpa using hd
  have hunit := hcop.isUnit_of_dvd' hdvdnum hdvdden
  have hdeg := Polynomial.degree_eq_zero_of_isUnit hunit
  rw [degree_X_sub_C] at hdeg
  exact absurd hdeg (by norm_num)

/-- **Differentiation does not create poles.**  The derivative of a rational function regular at a
point is regular there. -/
theorem ratOrder_ratFuncDeriv_nonneg {f : RatFunc K} (hf : f ≠ 0) {z : K}
    (h : 0 ≤ ratOrder f z) : 0 ≤ ratOrder (ratFuncDeriv f) z := by
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hdz : f.denom.eval z ≠ 0 := denom_eval_ne_zero_of_ratOrder_nonneg hf h
  have hfeq : f = algebraMap K[X] (RatFunc K) f.num
      / algebraMap K[X] (RatFunc K) f.denom := (RatFunc.num_div_denom f).symm
  have hder : ratFuncDeriv f
      = algebraMap K[X] (RatFunc K)
          (derivative f.num * f.denom - f.num * derivative f.denom)
        / algebraMap K[X] (RatFunc K) (f.denom ^ (2 : ℕ)) := by
    conv_lhs => rw [hfeq]
    exact ratFuncDeriv_div hden
  have hd2 : rootMultiplicity z (f.denom ^ (2 : ℕ)) = 0 := by
    rw [rootMultiplicity_pow hden,
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hdz)]
  rcases eq_or_ne (derivative f.num * f.denom - f.num * derivative f.denom) 0 with h0 | h0
  · rw [hder, h0, map_zero, zero_div, ratOrder_zero]
  · rw [hder, ratOrder_algebraMap_div h0 (pow_ne_zero 2 hden), hd2]
    omega

end

end GaloisForLFunctions.HTGeometry
