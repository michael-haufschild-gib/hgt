import GaloisForLFunctions.RHTower.RouteEConditionedSlotDivisors
import GaloisForLFunctions.RHTower.RouteEComponentHistoryShuffle

/-!
# Route E squarefree conditioned-majority obstruction

For singleton component histories with at least five slots, squarefree receivers in one interval,
at most four receiver values per history, and interval width below the inactive baseline, every
history repeats the same receiver in all but at most three slots.  Orienting by that receiver's
Möbius sign gives a lower bound of `card S - 6` for every within-history Möbius sum. Common slot
swaps transfer this to fixed anchors for invariant weights; the uniform literal conditioned cell
needs no separate invariance premise. Existing source power estimates derive both bounded support
and the required interval-width inequality.

This is a rigidity/no-go theorem, not a cancellation estimate: bounded receiver support forces
near-total sign alignment.  A surviving Route E construction must therefore produce growing
receiver diversity and separately preserve literal source weights.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace RHTower.IntegerCubeAperture

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

omit [Fintype C] [DecidableEq C] in
theorem exists_common_inactive_slot
    (h : S → C → Bool)
    (hcard : 3 ≤ Fintype.card S)
    (hsingle : ∀ i r s, h r i = true → h s i = true → r = s)
    (c d : C) :
    ∃ r : S, h r c = false ∧ h r d = false := by
  let A : Finset S := univ.filter fun r => h r c = false
  let B : Finset S := univ.filter fun r => h r d = false
  have hA : Fintype.card S - 1 ≤ A.card := by
    simpa only [A] using inactive_slot_card_lower h hsingle c
  have hB : Fintype.card S - 1 ≤ B.card := by
    simpa only [B] using inactive_slot_card_lower h hsingle d
  have hU : (A ∪ B).card ≤ Fintype.card S := by
    simpa using card_le_card (subset_univ (A ∪ B))
  have hI : 0 < (A ∩ B).card := by
    have hinc := card_union_add_card_inter A B
    omega
  obtain ⟨r, hr⟩ := card_pos.mp hI
  have hr' := mem_inter.mp hr
  exact ⟨r, (mem_filter.mp hr'.1).2, (mem_filter.mp hr'.2).2⟩

theorem inactive_factors_pairwise_coprime
    (a b : C → ℕ) (h : S → C → Bool)
    (hcard : 3 ≤ Fintype.card S)
    (hsingle : ∀ i r s, h r i = true → h s i = true → r = s)
    (hsquarefree : ∀ r, Squarefree
      (boolCorner (fun i z => if z then b i else a i) (h r))) :
    ∀ ⦃c d : C⦄, c ≠ d → (a c).Coprime (a d) := by
  intro c d hcd
  obtain ⟨r, hrc, hrd⟩ := exists_common_inactive_slot h hcard hsingle c d
  let f : C → ℕ := fun i => if h r i then b i else a i
  have hdiv : a c * a d ∣ boolCorner (fun i z => if z then b i else a i) (h r) := by
    have hsub : ({c, d} : Finset C) ⊆ univ := subset_univ _
    have hp := prod_dvd_prod_of_subset ({c, d} : Finset C) univ f hsub
    simpa [f, boolCorner, hrc, hrd, hcd] using hp
  exact Nat.coprime_of_squarefree_mul
    ((hsquarefree r).squarefree_of_dvd hdiv)

omit [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem inactive_factor_dvd_receiver
    (a b : C → ℕ) (h : S → C → Bool) (r : S) (c : C)
    (hrc : h r c = false) :
    a c ∣ boolCorner (fun i z => if z then b i else a i) (h r) := by
  unfold boolCorner
  have hdvd := Finset.dvd_prod_of_mem
    (fun i => if h r i then b i else a i) (Finset.mem_univ c)
  simpa [hrc] using hdvd

theorem baseline_dvd_of_repeated_receiver
    (a b : C → ℕ) (h : S → C → Bool)
    (hcard : 3 ≤ Fintype.card S)
    (hsingle : ∀ i r s, h r i = true → h s i = true → r = s)
    (hsquarefree : ∀ t, Squarefree
      (boolCorner (fun i z => if z then b i else a i) (h t)))
    {r s : S} (hrs : r ≠ s)
    (heq : boolCorner (fun i z => if z then b i else a i) (h r) =
      boolCorner (fun i z => if z then b i else a i) (h s)) :
    (∏ i, a i) ∣ boolCorner (fun i z => if z then b i else a i) (h r) := by
  let receiver : S → ℕ := fun t =>
    boolCorner (fun i z => if z then b i else a i) (h t)
  have hpair := inactive_factors_pairwise_coprime a b h hcard hsingle hsquarefree
  have hdiv : ∀ i, a i ∣ receiver r := by
    intro i
    by_cases hri : h r i = true
    · have hsi : h s i = false := by
        cases hsval : h s i with
        | false => rfl
        | true => exact (hrs (hsingle i r s hri hsval)).elim
      rw [show receiver r = receiver s by exact heq]
      exact inactive_factor_dvd_receiver a b h s i hsi
    · have hri' : h r i = false := by simpa using hri
      exact inactive_factor_dvd_receiver a b h r i hri'
  have hpairInt : Pairwise (fun i j : C => IsCoprime (a i : ℤ) (a j : ℤ)) := by
    intro i j hij
    exact (hpair hij).isCoprime
  have hdivInt : ∀ i, (a i : ℤ) ∣ (receiver r : ℤ) := by
    intro i
    exact_mod_cast hdiv i
  have hprodInt : (∏ i, (a i : ℤ)) ∣ (receiver r : ℤ) :=
    Fintype.prod_dvd_of_coprime hpairInt hdivInt
  exact_mod_cast hprodInt

omit [Fintype C] [DecidableEq C] [DecidableEq S] in
theorem image_card_le_four_of_no_five_distinct
    (f : S → ℕ)
    (hnoFive : ∀ e : Fin 5 → S, ¬ Function.Injective fun r => f (e r)) :
    (univ.image f).card ≤ 4 := by
  by_contra hle
  have hfive : 5 ≤ (univ.image f).card := by omega
  let g : Fin 5 ↪o ℕ := (univ.image f).orderEmbOfCardLe hfive
  have hgmem (i : Fin 5) : g i ∈ univ.image f := by
    exact orderEmbOfCardLe_mem (univ.image f) hfive i
  choose e he using fun i => mem_image.mp (hgmem i)
  apply hnoFive e
  intro r s hrs
  apply g.injective
  exact (he r).2.symm.trans (hrs.trans (he s).2)

omit [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem width_lt_baseline_of_power_separation
    (A L W : ℝ) (hA : 1 ≤ A) (hL : 0 ≤ L)
    (hbase : L ^ (10 : ℕ) ≤ A ^ (11 : ℕ)) (hgap : W ^ (55 : ℕ) < L ^ (30 : ℕ)) :
    W < A := by
  have hLA : L ^ (30 : ℕ) ≤ A ^ (33 : ℕ) := by
    calc
      L ^ (30 : ℕ) = (L ^ (10 : ℕ)) ^ (3 : ℕ) := by ring
      _ ≤ (A ^ (11 : ℕ)) ^ (3 : ℕ) := pow_le_pow_left₀ (pow_nonneg hL 10) hbase 3
      _ = A ^ (33 : ℕ) := by ring
  have hAmono : A ^ (33 : ℕ) ≤ A ^ (55 : ℕ) := pow_le_pow_right₀ hA (by norm_num)
  have hpow : W ^ (55 : ℕ) < A ^ (55 : ℕ) := hgap.trans_le (hLA.trans hAmono)
  exact lt_of_pow_lt_pow_left₀ 55 (by linarith) hpow

omit [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem boolCorner_natCast_eq_routeEComponentSlotReceiver
    {m : ℕ} (a b : C → ℕ)
    (history : RouteEComponentHistory (fun _ : C => Bool) m) (r : Fin m) :
    (boolCorner (fun i z => if z then b i else a i) (history r) : ℝ) =
      routeEComponentSlotReceiver (fun _ : C => Bool)
        (fun i z => if z then (b i : ℝ) else (a i : ℝ)) history r := by
  unfold boolCorner routeEComponentSlotReceiver
  push_cast
  apply prod_congr rfl
  intro i _hi
  cases history r i <;> rfl

omit [Fintype S] [DecidableEq S] in
theorem singleton_history_support_le_four_of_power_activation
    (m K : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ)
    (history : RouteEComponentHistory (fun _ : C => Bool) m)
    (hmem : history ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k)
    (hone : ∀ i, k i true = 1) (ha : ∀ i, 1 ≤ a i)
    (hactivation : ∀ i, b i ≤ a i ^ K) (hm : 10 * (K + 1) ≤ m)
    (L W : ℝ) (hL : 0 ≤ L) (hW : 0 ≤ W) (hgap : W ^ (55 : ℕ) < L ^ (30 : ℕ))
    (hwindow : ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i : ℝ) else (a i : ℝ)) history r ∈ Set.Icc L (L + W)) :
    ((univ : Finset (Fin m)).image fun r =>
      boolCorner (fun i z => if z then b i else a i) (history r)).card ≤ 4 := by
  apply image_card_le_four_of_no_five_distinct
  intro e hinjNat
  apply singleton_history_no_five_of_power_activation m K k a b history hmem hone ha
    hactivation hm L W hL hW hgap hwindow e
  intro r s hrs
  apply hinjNat
  have hrs' :
      (boolCorner (fun i z => if z then b i else a i) (history (e r)) : ℝ) =
        (boolCorner (fun i z => if z then b i else a i) (history (e s)) : ℝ) := by
    simpa only [boolCorner_natCast_eq_routeEComponentSlotReceiver] using hrs
  exact_mod_cast hrs'

/-- Literal singleton histogram cell restricted only by squarefreeness and one physical window. -/
def routeESquarefreeWindowFamily
    (m : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ) (L W : ℝ) :
    Finset (RouteEComponentHistory (fun _ : C => Bool) m) :=
  (routeEComponentHistogramCell (fun _ : C => Bool) m k).filter fun x =>
    ∀ r,
      Squarefree (boolCorner (fun i z => if z then b i else a i) (x r)) ∧
      routeEComponentSlotReceiver (fun _ : C => Bool)
        (fun i z => if z then (b i : ℝ) else (a i : ℝ)) x r ∈ Set.Icc L (L + W)

omit [Fintype S] [DecidableEq S] in
theorem routeESquarefreeWindowFamily_anchorSwap_mem_iff
    (m : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ) (L W : ℝ)
    (anchor r : Fin m) (x : RouteEComponentHistory (fun _ : C => Bool) m) :
    routeEComponentHistoryAnchorSwap (fun _ : C => Bool) anchor r x ∈
        routeESquarefreeWindowFamily m k a b L W ↔
      x ∈ routeESquarefreeWindowFamily m k a b L W := by
  simp only [routeESquarefreeWindowFamily, mem_filter,
    routeEComponentHistoryAnchorSwap_mem_cell_iff]
  constructor
  · rintro ⟨hcell, hphysical⟩
    refine ⟨hcell, ?_⟩
    intro s
    have hs := hphysical (Equiv.swap anchor r s)
    change Squarefree (boolCorner (fun i z => if z then b i else a i)
        (x (Equiv.swap anchor r (Equiv.swap anchor r s)))) ∧
      (∏ i, (if x (Equiv.swap anchor r (Equiv.swap anchor r s)) i
          then (b i : ℝ) else (a i : ℝ))) ∈ Set.Icc L (L + W) at hs
    change Squarefree (boolCorner (fun i z => if z then b i else a i) (x s)) ∧
      (∏ i, (if x s i then (b i : ℝ) else (a i : ℝ))) ∈ Set.Icc L (L + W)
    simpa only [Equiv.swap_apply_self] using hs
  · rintro ⟨hcell, hphysical⟩
    refine ⟨hcell, ?_⟩
    intro s
    have hs := hphysical (Equiv.swap anchor r s)
    change Squarefree (boolCorner (fun i z => if z then b i else a i)
        (x (Equiv.swap anchor r s))) ∧
      (∏ i, (if x (Equiv.swap anchor r s) i then (b i : ℝ) else (a i : ℝ))) ∈
        Set.Icc L (L + W) at hs
    change Squarefree (boolCorner (fun i z => if z then b i else a i)
        (x (Equiv.swap anchor r s))) ∧
      (∏ i, (if x (Equiv.swap anchor r s) i then (b i : ℝ) else (a i : ℝ))) ∈
        Set.Icc L (L + W)
    exact hs

omit [Fintype C] [DecidableEq C] [DecidableEq S] in
theorem exists_repeated_of_image_card_le_four
    (f : S → ℕ)
    (hcard : 5 ≤ Fintype.card S)
    (hsupport : (univ.image f).card ≤ 4) :
    ∃ r s : S, r ≠ s ∧ f r = f s := by
  have hninj : ¬ Function.Injective f := by
    intro hinj
    have himage : (univ.image f).card = Fintype.card S := by
      simpa using card_image_of_injective (univ : Finset S) hinj
    omega
  obtain ⟨r, s, hrs, hne⟩ := Function.not_injective_iff.mp hninj
  exact ⟨r, s, hne, hrs⟩

omit [Fintype C] [DecidableEq C] in
theorem card_exceptions_le_three
    (f : S → ℕ) (nStar : ℕ)
    (hsupport : (univ.image f).card ≤ 4)
    (hnStar : nStar ∈ univ.image f)
    (hrepeat : ∀ {r s : S}, r ≠ s → f r = f s → f r = nStar) :
    (univ.filter fun r => f r ≠ nStar).card ≤ 3 := by
  let E : Finset S := univ.filter fun r => f r ≠ nStar
  have hinj : Set.InjOn f (E : Set S) := by
    intro r hr s hs hrs
    by_contra hne
    have hrStar : f r = nStar := hrepeat hne hrs
    exact (mem_filter.mp hr).2 hrStar
  have himage : (E.image f).card = E.card := card_image_iff.mpr hinj
  have hsubset : E.image f ⊆ (univ.image f).erase nStar := by
    intro n hn
    obtain ⟨r, hrE, rfl⟩ := mem_image.mp hn
    refine mem_erase.mpr ⟨?_, mem_image.mpr ⟨r, mem_univ r, rfl⟩⟩
    exact (mem_filter.mp hrE).2
  have hle : E.card ≤ ((univ.image f).erase nStar).card := by
    rw [← himage]
    exact card_le_card hsubset
  rw [card_erase_of_mem hnStar] at hle
  simpa only [E] using (show E.card ≤ 3 by omega)

variable {H : Type*}

theorem squarefree_singleton_family_common_receiver
    (family : Finset H) (hfamily : family.Nonempty)
    (history : H → S → C → Bool) (a b : C → ℕ) (L W : ℝ)
    (hcard : 5 ≤ Fintype.card S)
    (hsingle : ∀ x ∈ family, ∀ i r s,
      history x r i = true → history x s i = true → r = s)
    (hsquarefree : ∀ x ∈ family, ∀ r, Squarefree
      (boolCorner (fun i z => if z then b i else a i) (history x r)))
    (hwindow : ∀ x ∈ family, ∀ r,
      (boolCorner (fun i z => if z then b i else a i) (history x r) : ℝ) ∈
        Set.Icc L (L + W))
    (hsupport : ∀ x ∈ family,
      ((univ : Finset S).image fun r =>
        boolCorner (fun i z => if z then b i else a i) (history x r)).card ≤ 4)
    (hwidth : W < ((∏ i, a i : ℕ) : ℝ)) :
    ∃ nStar : ℕ,
      Squarefree nStar ∧
      (∏ i, a i) ∣ nStar ∧
      ∀ x ∈ family,
        ((univ : Finset S).filter fun r =>
          boolCorner (fun i z => if z then b i else a i) (history x r) ≠ nStar).card ≤ 3 ∧
        ∀ {r s : S}, r ≠ s →
          boolCorner (fun i z => if z then b i else a i) (history x r) =
            boolCorner (fun i z => if z then b i else a i) (history x s) →
          boolCorner (fun i z => if z then b i else a i) (history x r) = nStar := by
  let receiver : H → S → ℕ := fun x r =>
    boolCorner (fun i z => if z then b i else a i) (history x r)
  let x0 := hfamily.choose
  have hx0 : x0 ∈ family := hfamily.choose_spec
  obtain ⟨r0, s0, hrs0, heq0⟩ :=
    exists_repeated_of_image_card_le_four (receiver x0) hcard (hsupport x0 hx0)
  let nStar : ℕ := receiver x0 r0
  have hbaseStar : (∏ i, a i) ∣ nStar := by
    exact baseline_dvd_of_repeated_receiver a b (history x0) (by omega)
      (hsingle x0 hx0) (hsquarefree x0 hx0) hrs0 heq0
  have hsquarefreeStar : Squarefree nStar := hsquarefree x0 hx0 r0
  have hwindowStar : (nStar : ℝ) ∈ Set.Icc L (L + W) := hwindow x0 hx0 r0
  refine ⟨nStar, hsquarefreeStar, hbaseStar, ?_⟩
  intro x hx
  have hrepeat : ∀ {r s : S}, r ≠ s → receiver x r = receiver x s →
      receiver x r = nStar := by
    intro r s hrs heq
    have hbase : (∏ i, a i) ∣ receiver x r :=
      baseline_dvd_of_repeated_receiver a b (history x) (by omega)
        (hsingle x hx) (hsquarefree x hx) hrs heq
    by_contra hne
    have hle : ((∏ i, a i : ℕ) : ℝ) ≤ W :=
      common_divisor_le_width (∏ i, a i) (receiver x r) nStar L W
        hbase hbaseStar hne (hwindow x hx r) hwindowStar
    exact (not_le_of_gt hwidth) hle
  refine ⟨card_exceptions_le_three (receiver x) nStar (hsupport x hx) ?_ hrepeat, ?_⟩
  · obtain ⟨r, s, hrs, heq⟩ :=
      exists_repeated_of_image_card_le_four (receiver x) hcard (hsupport x hx)
    exact mem_image.mpr ⟨r, mem_univ r, hrepeat hrs heq⟩
  · exact hrepeat

omit [Fintype C] [DecidableEq C] [DecidableEq S] in
theorem mobius_oriented_sum_lower_of_card_exceptions_le_three
    (f : S → ℕ) (nStar : ℕ)
    (hsquarefreeStar : Squarefree nStar)
    (hsquarefree : ∀ r, Squarefree (f r))
    (hexceptions : ((univ : Finset S).filter fun r => f r ≠ nStar).card ≤ 3) :
    (Fintype.card S : ℤ) - 6 ≤
      ArithmeticFunction.moebius nStar * ∑ r, ArithmeticFunction.moebius (f r) := by
  let E : Finset S := univ.filter fun r => f r ≠ nStar
  have hpoint (r : S) :
      (if f r = nStar then (1 : ℤ) else -1) ≤
        ArithmeticFunction.moebius nStar * ArithmeticFunction.moebius (f r) := by
    split_ifs with hr
    · rw [hr, ← pow_two]
      exact le_of_eq
        (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsquarefreeStar).symm
    · have hstar :=
        ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsquarefreeStar
      have hrSq := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsquarefree r)
      nlinarith [sq_nonneg
        (ArithmeticFunction.moebius nStar + ArithmeticFunction.moebius (f r))]
  have hsum :
      ∑ r : S, (if f r = nStar then (1 : ℤ) else -1) =
        (Fintype.card S : ℤ) - 2 * (E.card : ℤ) := by
    let P : Finset S := univ.filter fun r => f r = nStar
    have hP : ∑ r ∈ P, (if f r = nStar then (1 : ℤ) else -1) = (P.card : ℤ) := by
      calc
        _ = ∑ _r ∈ P, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [if_pos (mem_filter.mp hr).2]
        _ = (P.card : ℤ) := by simp
    have hE : ∑ r ∈ E, (if f r = nStar then (1 : ℤ) else -1) = -(E.card : ℤ) := by
      calc
        _ = ∑ _r ∈ E, (-1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [if_neg (mem_filter.mp hr).2]
        _ = -(E.card : ℤ) := by simp
    have hpartition : P.card + E.card = Fintype.card S := by
      simpa only [P, E, card_univ] using
        card_filter_add_card_filter_not
          (s := (univ : Finset S)) (p := fun r => f r = nStar)
    calc
      ∑ r : S, (if f r = nStar then (1 : ℤ) else -1) =
          (∑ r ∈ P, (if f r = nStar then (1 : ℤ) else -1)) +
          ∑ r ∈ E, (if f r = nStar then (1 : ℤ) else -1) := by
            simpa only [P, E] using
              (sum_filter_add_sum_filter_not (s := (univ : Finset S))
                (p := fun r => f r = nStar)
                (f := fun r => if f r = nStar then (1 : ℤ) else -1)).symm
      _ = (P.card : ℤ) - (E.card : ℤ) := by rw [hP, hE]; omega
      _ = (Fintype.card S : ℤ) - 2 * (E.card : ℤ) := by
        have hpartitionInt : (P.card : ℤ) + (E.card : ℤ) = Fintype.card S := by
          exact_mod_cast hpartition
        omega
  calc
    (Fintype.card S : ℤ) - 6 ≤ (Fintype.card S : ℤ) - 2 * (E.card : ℤ) := by
      have : E.card ≤ 3 := by simpa only [E] using hexceptions
      omega
    _ = ∑ r : S, (if f r = nStar then (1 : ℤ) else -1) := hsum.symm
    _ ≤ ∑ r : S,
        ArithmeticFunction.moebius nStar * ArithmeticFunction.moebius (f r) := by
      exact sum_le_sum fun r _ => hpoint r
    _ = ArithmeticFunction.moebius nStar *
        ∑ r, ArithmeticFunction.moebius (f r) := by rw [mul_sum]

theorem squarefree_singleton_family_mobius_majority
    (family : Finset H) (hfamily : family.Nonempty)
    (history : H → S → C → Bool) (a b : C → ℕ) (L W : ℝ)
    (hcard : 5 ≤ Fintype.card S)
    (hsingle : ∀ x ∈ family, ∀ i r s,
      history x r i = true → history x s i = true → r = s)
    (hsquarefree : ∀ x ∈ family, ∀ r, Squarefree
      (boolCorner (fun i z => if z then b i else a i) (history x r)))
    (hwindow : ∀ x ∈ family, ∀ r,
      (boolCorner (fun i z => if z then b i else a i) (history x r) : ℝ) ∈
        Set.Icc L (L + W))
    (hsupport : ∀ x ∈ family,
      ((univ : Finset S).image fun r =>
        boolCorner (fun i z => if z then b i else a i) (history x r)).card ≤ 4)
    (hwidth : W < ((∏ i, a i : ℕ) : ℝ)) :
    ∃ nStar : ℕ,
      Squarefree nStar ∧
      (∏ i, a i) ∣ nStar ∧
      ∀ x ∈ family,
        ((univ : Finset S).filter fun r =>
          boolCorner (fun i z => if z then b i else a i) (history x r) ≠ nStar).card ≤ 3 ∧
        (Fintype.card S : ℤ) - 6 ≤
          ArithmeticFunction.moebius nStar *
            ∑ r, ArithmeticFunction.moebius
              (boolCorner (fun i z => if z then b i else a i) (history x r)) := by
  let receiver : H → S → ℕ := fun x r =>
    boolCorner (fun i z => if z then b i else a i) (history x r)
  obtain ⟨nStar, hsquarefreeStar, hbaseStar, hcommon⟩ :=
    squarefree_singleton_family_common_receiver family hfamily history a b L W hcard
      hsingle hsquarefree hwindow hsupport hwidth
  refine ⟨nStar, hsquarefreeStar, hbaseStar, ?_⟩
  intro x hx
  have hexceptions := (hcommon x hx).1
  refine ⟨hexceptions, ?_⟩
  exact mobius_oriented_sum_lower_of_card_exceptions_le_three
    (receiver x) nStar hsquarefreeStar (hsquarefree x hx) hexceptions

variable {J : C → Type*}

omit [Fintype C] [DecidableEq C] in
theorem routeE_invariant_weighted_anchor_sum_eq
    (m : ℕ) (family : Finset (RouteEComponentHistory J m))
    (weight : RouteEComponentHistory J m → ℝ)
    (value : RouteEComponentHistory J m → Fin m → ℝ)
    (r₀ : Fin m)
    (hswap : ∀ r x,
      routeEComponentHistoryAnchorSwap J r₀ r x ∈ family ↔ x ∈ family)
    (hweight : ∀ r x,
      weight (routeEComponentHistoryAnchorSwap J r₀ r x) = weight x)
    (hvalue : ∀ r x,
      value (routeEComponentHistoryAnchorSwap J r₀ r x) r₀ = value x r)
    (r : Fin m) :
    (∑ x ∈ family, weight x * value x r) =
      ∑ x ∈ family, weight x * value x r₀ := by
  let swapHistory := routeEComponentHistoryAnchorSwap J r₀ r
  have hmem : ∀ x, x ∈ family → swapHistory x ∈ family := by
    intro x hx
    exact (hswap r x).2 hx
  refine Finset.sum_bij' (fun x _ => swapHistory x) (fun x _ => swapHistory x)
    hmem hmem ?_ ?_ ?_
  · intro x _hx
    funext s c
    simp [swapHistory, routeEComponentHistoryAnchorSwap]
  · intro x _hx
    funext s c
    simp [swapHistory, routeEComponentHistoryAnchorSwap]
  · intro x _hx
    rw [show weight (swapHistory x) = weight x by exact hweight r x]
    rw [show value (swapHistory x) r₀ = value x r by exact hvalue r x]

theorem squarefree_singleton_invariant_weight_anchor_majority
    (m : ℕ)
    (family : Finset (RouteEComponentHistory (fun _ : C => Bool) m))
    (hfamily : family.Nonempty)
    (weight : RouteEComponentHistory (fun _ : C => Bool) m → ℝ)
    (hweightNonneg : ∀ x ∈ family, 0 ≤ weight x)
    (anchor : Fin m)
    (hswap : ∀ r x,
      routeEComponentHistoryAnchorSwap (fun _ : C => Bool) anchor r x ∈ family ↔
        x ∈ family)
    (hweightSwap : ∀ r x,
      weight (routeEComponentHistoryAnchorSwap (fun _ : C => Bool) anchor r x) = weight x)
    (a b : C → ℕ) (L W : ℝ)
    (hcard : 5 ≤ m)
    (hsingle : ∀ x ∈ family, ∀ i r s,
      x r i = true → x s i = true → r = s)
    (hsquarefree : ∀ x ∈ family, ∀ r, Squarefree
      (boolCorner (fun i z => if z then b i else a i) (x r)))
    (hwindow : ∀ x ∈ family, ∀ r,
      (boolCorner (fun i z => if z then b i else a i) (x r) : ℝ) ∈
        Set.Icc L (L + W))
    (hsupport : ∀ x ∈ family,
      ((univ : Finset (Fin m)).image fun r =>
        boolCorner (fun i z => if z then b i else a i) (x r)).card ≤ 4)
    (hwidth : W < ((∏ i, a i : ℕ) : ℝ)) :
    ∃ nStar : ℕ,
      Squarefree nStar ∧
      (∏ i, a i) ∣ nStar ∧
      ((m : ℝ) - 6) * ∑ x ∈ family, weight x ≤
        (m : ℝ) * ∑ x ∈ family,
          weight x * ((ArithmeticFunction.moebius nStar : ℝ) *
            ArithmeticFunction.moebius
              (boolCorner (fun i z => if z then b i else a i) (x anchor))) := by
  let receiver : RouteEComponentHistory (fun _ : C => Bool) m → Fin m → ℕ :=
    fun x r => boolCorner (fun i z => if z then b i else a i) (x r)
  obtain ⟨nStar, hsquarefreeStar, hbaseStar, hmajor⟩ :=
    squarefree_singleton_family_mobius_majority family hfamily (fun x => x) a b L W
      (by simpa using hcard) hsingle hsquarefree hwindow hsupport hwidth
  let oriented : RouteEComponentHistory (fun _ : C => Bool) m → Fin m → ℝ :=
    fun x r => (ArithmeticFunction.moebius nStar : ℝ) *
      ArithmeticFunction.moebius (receiver x r)
  have hhistory (x) (hx : x ∈ family) :
      (m : ℝ) - 6 ≤ ∑ r, oriented x r := by
    have hInt := (hmajor x hx).2
    simp only [Fintype.card_fin] at hInt
    have hcast : ((((m : ℤ) - 6 : ℤ)) : ℝ) ≤
        ((ArithmeticFunction.moebius nStar *
          ∑ r, ArithmeticFunction.moebius (receiver x r) : ℤ) : ℝ) := by
      exact_mod_cast hInt
    simpa [oriented, Int.cast_sub, Int.cast_mul, Int.cast_sum, mul_sum] using hcast
  have hslot (r : Fin m) :
      (∑ x ∈ family, weight x * oriented x r) =
        ∑ x ∈ family, weight x * oriented x anchor := by
    apply routeE_invariant_weighted_anchor_sum_eq
      (J := fun _ : C => Bool) m family weight oriented anchor hswap hweightSwap
    intro r x
    change (ArithmeticFunction.moebius nStar : ℝ) *
        ArithmeticFunction.moebius
          (boolCorner (fun i z => if z then b i else a i)
            (x (Equiv.swap anchor r anchor))) =
      (ArithmeticFunction.moebius nStar : ℝ) *
        ArithmeticFunction.moebius
          (boolCorner (fun i z => if z then b i else a i) (x r))
    rw [Equiv.swap_apply_left]
  refine ⟨nStar, hsquarefreeStar, hbaseStar, ?_⟩
  calc
    ((m : ℝ) - 6) * ∑ x ∈ family, weight x =
        ∑ x ∈ family, weight x * ((m : ℝ) - 6) := by
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ ≤ ∑ x ∈ family, weight x * ∑ r, oriented x r := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hhistory x hx) (hweightNonneg x hx)
    _ = ∑ r : Fin m, ∑ x ∈ family, weight x * oriented x r := by
      simp_rw [mul_sum]
      rw [sum_comm]
    _ = ∑ _r : Fin m, ∑ x ∈ family, weight x * oriented x anchor := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact hslot r
    _ = (m : ℝ) * ∑ x ∈ family, weight x * oriented x anchor := by simp

/-- Fixed activation powers and the actual aperture inequalities force a common squarefree
receiver and an overwhelming fixed-anchor Möbius bias for every swap-invariant nonnegative
source weight.  This is an obstruction to bounded-support cancellation, not an RH proof. -/
theorem squarefree_power_bounded_invariant_weight_anchor_majority
    (m K : ℕ) (k : C → Bool → ℕ)
    (family : Finset (RouteEComponentHistory (fun _ : C => Bool) m))
    (hfamily : family.Nonempty)
    (hmem : ∀ x ∈ family,
      x ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k)
    (weight : RouteEComponentHistory (fun _ : C => Bool) m → ℝ)
    (hweightNonneg : ∀ x ∈ family, 0 ≤ weight x)
    (anchor : Fin m)
    (hswap : ∀ r x,
      routeEComponentHistoryAnchorSwap (fun _ : C => Bool) anchor r x ∈ family ↔
        x ∈ family)
    (hweightSwap : ∀ r x,
      weight (routeEComponentHistoryAnchorSwap (fun _ : C => Bool) anchor r x) = weight x)
    (a b : C → ℕ) (L W : ℝ)
    (hone : ∀ i, k i true = 1) (ha : ∀ i, 1 ≤ a i)
    (hactivation : ∀ i, b i ≤ a i ^ K) (hm : 10 * (K + 1) ≤ m)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hgap : W ^ (55 : ℕ) < L ^ (30 : ℕ))
    (hsquarefree : ∀ x ∈ family, ∀ r, Squarefree
      (boolCorner (fun i z => if z then b i else a i) (x r)))
    (hwindow : ∀ x ∈ family, ∀ r,
      routeEComponentSlotReceiver (fun _ : C => Bool)
        (fun i z => if z then (b i : ℝ) else (a i : ℝ)) x r ∈ Set.Icc L (L + W)) :
    ∃ nStar : ℕ,
      Squarefree nStar ∧
      (∏ i, a i) ∣ nStar ∧
      ((m : ℝ) - 6) * ∑ x ∈ family, weight x ≤
        (m : ℝ) * ∑ x ∈ family,
          weight x * ((ArithmeticFunction.moebius nStar : ℝ) *
            ArithmeticFunction.moebius
              (boolCorner (fun i z => if z then b i else a i) (x anchor))) := by
  have hsingle : ∀ x ∈ family, ∀ i r s,
      x r i = true → x s i = true → r = s := by
    intro x hx i r s hr hs
    have hhist := (mem_filter.mp (hmem x hx)).2 i
    have hcount : (univ.filter fun t => x t i = true).card = 1 := by
      simpa only [GaloisForLFunctions.HTGeometry.tupleHistogram, hone i] using
        congrFun hhist true
    have hle : (univ.filter fun t => x t i = true).card ≤ 1 := by omega
    exact (card_le_one.mp hle) r (mem_filter.mpr ⟨mem_univ _, hr⟩)
      s (mem_filter.mpr ⟨mem_univ _, hs⟩)
  have hwindowNat : ∀ x ∈ family, ∀ r,
      (boolCorner (fun i z => if z then b i else a i) (x r) : ℝ) ∈
        Set.Icc L (L + W) := by
    intro x hx r
    rw [boolCorner_natCast_eq_routeEComponentSlotReceiver]
    exact hwindow x hx r
  have hsupport : ∀ x ∈ family,
      ((univ : Finset (Fin m)).image fun r =>
        boolCorner (fun i z => if z then b i else a i) (x r)).card ≤ 4 := by
    intro x hx
    exact singleton_history_support_le_four_of_power_activation m K k a b x
      (hmem x hx) hone ha hactivation hm L W hL hW hgap (hwindow x hx)
  let x0 := hfamily.choose
  have hx0 : x0 ∈ family := hfamily.choose_spec
  have hbase : L ^ (10 : ℕ) ≤ ((∏ i, a i : ℕ) : ℝ) ^ (11 : ℕ) :=
    singleton_history_baseline_tenth_power m K k a b x0 (hmem x0 hx0) hone ha
      hactivation hm L hL (fun r => (hwindow x0 hx0 r).1)
  have hA : 1 ≤ ((∏ i, a i : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.prod_pos fun i _ => ha i)
  have hwidth : W < ((∏ i, a i : ℕ) : ℝ) :=
    width_lt_baseline_of_power_separation _ L W hA hL hbase hgap
  exact squarefree_singleton_invariant_weight_anchor_majority m family hfamily weight
    hweightNonneg anchor hswap hweightSwap a b L W (by omega) hsingle hsquarefree
    hwindowNat hsupport hwidth

/-- Uniform specialization for the literal squarefree, window-conditioned histogram cell.
No anchor-invariance premise remains: common slot swaps preserve this cell by construction. -/
theorem squarefree_power_bounded_uniform_conditioned_anchor_majority
    (m K : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ) (L W : ℝ)
    (hone : ∀ i, k i true = 1) (ha : ∀ i, 1 ≤ a i)
    (hactivation : ∀ i, b i ≤ a i ^ K) (hm : 10 * (K + 1) ≤ m)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hgap : W ^ (55 : ℕ) < L ^ (30 : ℕ))
    (hfamily : (routeESquarefreeWindowFamily m k a b L W).Nonempty)
    (anchor : Fin m) :
    ∃ nStar : ℕ,
      Squarefree nStar ∧
      (∏ i, a i) ∣ nStar ∧
      ((m : ℝ) - 6) * (routeESquarefreeWindowFamily m k a b L W).card ≤
        (m : ℝ) *
          ∑ x ∈ routeESquarefreeWindowFamily m k a b L W,
            (ArithmeticFunction.moebius nStar : ℝ) *
              ArithmeticFunction.moebius
                (boolCorner (fun i z => if z then b i else a i) (x anchor)) := by
  let family := routeESquarefreeWindowFamily m k a b L W
  have hmem : ∀ x ∈ family,
      x ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k := by
    intro x hx
    exact (mem_filter.mp hx).1
  have hsquarefree : ∀ x ∈ family, ∀ r, Squarefree
      (boolCorner (fun i z => if z then b i else a i) (x r)) := by
    intro x hx r
    exact ((mem_filter.mp hx).2 r).1
  have hwindow : ∀ x ∈ family, ∀ r,
      routeEComponentSlotReceiver (fun _ : C => Bool)
        (fun i z => if z then (b i : ℝ) else (a i : ℝ)) x r ∈ Set.Icc L (L + W) := by
    intro x hx r
    exact ((mem_filter.mp hx).2 r).2
  have hmain := squarefree_power_bounded_invariant_weight_anchor_majority
    m K k family (by simpa only [family] using hfamily) hmem (fun _ => 1)
    (by intros; positivity) anchor
    (by
      intro r x
      simpa only [family] using
        routeESquarefreeWindowFamily_anchorSwap_mem_iff m k a b L W anchor r x)
    (by intros; rfl) a b L W hone ha hactivation hm hL hW hgap hsquarefree hwindow
  simpa only [family, one_mul, sum_const, Nat.cast_ofNat, nsmul_eq_mul, mul_one] using hmain

end RHTower.IntegerCubeAperture
