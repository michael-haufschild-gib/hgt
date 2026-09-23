import GaloisForLFunctions.RHTower.MobiusDivisorExhaustiveClockCheckpoints

/-!
# Complete terminal orders retaining the logarithmic clock

Once all square-root primes are processed, a remaining prime has one signed
leaf and its original cost `(1 + log p) * leaf^(2 : ℕ)`. An adaptive insertion
order completes every remaining prime without exceeding the larger actual
endpoint energy. The construction retains the full finite counting weight.

Applying this order to nested prime-exhaustive clock checkpoints controls
all insertion prefixes by the larger of `200*M^(2 : ℕ)` and the completed source
square. That completed square remains explicit and unbounded here; paid
exhaustive continuation and a uniform critical-action bound are not proved.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

private def leafEnergy {α : Type*} [DecidableEq α]
    (a b : α → ℝ) (h : ℝ) (U R : Finset α) : ℝ :=
  (h+∑ p ∈ R,a p)^(2 : ℕ)+∑ p ∈ U \ R,b p

private lemma leaf_safe_first {α : Type*} [DecidableEq α]
    (a b : α → ℝ) (h : ℝ) (U : Finset α)
    (hb : ∀ p ∈ U,(a p)^(2 : ℕ) ≤ b p) (hU : U.Nonempty) :
    ∃ p ∈ U,(h+a p)^(2 : ℕ)+∑ q ∈ U.erase p,b q ≤
      max (h^(2 : ℕ)+∑ q ∈ U,b q) ((h+∑ q ∈ U,a q)^(2 : ℕ)) := by
  by_cases hx : ∃ p ∈ U,2*h*a p+(a p)^(2 : ℕ) ≤ b p
  · obtain ⟨p,hp,hs⟩ := hx
    refine ⟨p,hp,le_trans ?_ (le_max_left _ _)⟩
    have he := sum_erase_add U b hp
    nlinarith only [he,hs]
  · obtain ⟨p,hp⟩ := hU
    have hs : ∀ q ∈ U,b q < 2*h*a q+(a q)^(2 : ℕ) := by
      intro q hq
      exact lt_of_not_ge (fun hn => hx ⟨q,hq,hn⟩)
    have hsign : ∀ q ∈ U,0<h*a q := by
      intro q hq
      have := hs q hq
      have := hb q hq
      nlinarith
    have hsq : (∑ q ∈ U.erase p,(a q)^(2 : ℕ)) ≤ (∑ q ∈ U.erase p,a q)^(2 : ℕ) ∧
        0 ≤ a p * ∑ q ∈ U.erase p,a q := by
      by_cases hh : 0 ≤ h
      · have ha : ∀ q ∈ U,0 ≤ a q := by
          intro q hq
          by_contra hn
          have := mul_nonpos_of_nonneg_of_nonpos hh (le_of_not_ge hn)
          linarith [hsign q hq]
        exact ⟨sum_sq_le_sq_sum_of_nonneg (fun q hq => ha q (mem_of_mem_erase hq)),
          mul_nonneg (ha p hp) (sum_nonneg (fun q hq => ha q (mem_of_mem_erase hq)))⟩
      · have ha : ∀ q ∈ U,a q ≤ 0 := by
          intro q hq
          by_contra hn
          have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hh) (le_of_not_ge hn)
          linarith [hsign q hq]
        have hsq := sum_sq_le_sq_sum_of_nonneg (s:=U.erase p)
          (fun q hq => neg_nonneg.mpr (ha q (mem_of_mem_erase hq)))
        refine ⟨?_,mul_nonneg_of_nonpos_of_nonpos (ha p hp)
          (sum_nonpos (fun q hq => ha q (mem_of_mem_erase hq)))⟩
        simpa only [neg_sq,sum_neg_distrib] using hsq
    have hsum := sum_le_sum (s:=U.erase p) (fun q hq => (hs q (mem_of_mem_erase hq)).le)
    rw [sum_add_distrib,← mul_sum] at hsum
    have htotal := sum_erase_add U a hp
    refine ⟨p,hp,le_trans ?_ (le_max_right _ _)⟩
    rw [← htotal]
    nlinarith only [hsq.1,hsq.2,hsum]

private lemma leaf_insert {α : Type*} [DecidableEq α]
    (a b : α → ℝ) (h : ℝ) (U R : Finset α)
    (p : α) (hpR : p ∉ R) :
    leafEnergy a b h U (insert p R)=leafEnergy a b (h+a p) (U.erase p) R := by
  have he : U \ insert p R=U.erase p \ R := by ext q; simp; tauto
  simp only [leafEnergy,sum_insert hpR,he]
  ring

private lemma exists_leaf_order {α : Type*} [DecidableEq α]
    (a b : α → ℝ) (h : ℝ) (U : Finset α)
    (hb : ∀ p ∈ U,(a p)^(2 : ℕ) ≤ b p) :
    ∃ l : List α,l.Nodup ∧ l.toFinset=U ∧ ∀ k : ℕ,
      leafEnergy a b h U (l.take k).toFinset ≤
        max (h^(2 : ℕ)+∑ p ∈ U,b p) ((h+∑ p ∈ U,a p)^(2 : ℕ)) := by
  revert h
  refine Finset.strongInductionOn U ?_ hb
  intro U ih hb h
  by_cases hU : U.Nonempty
  · obtain ⟨p,hp,hsafe⟩ := leaf_safe_first a b h U hb hU
    obtain ⟨l,hl,hset,hbound⟩ := ih (U.erase p) (erase_ssubset hp)
      (fun q hq => hb q (mem_of_mem_erase hq)) (h+a p)
    have hpL : p ∉ l := by
      intro hpl
      have hm : p ∈ l.toFinset := List.mem_toFinset.mpr hpl
      rw [hset] at hm
      exact notMem_erase p U hm
    have htotal : h+a p+∑ q ∈ U.erase p,a q=h+∑ q ∈ U,a q := by
      have := sum_erase_add U a hp
      linarith
    refine ⟨p::l,List.nodup_cons.mpr ⟨hpL,hl⟩,?_,?_⟩
    · simp [hset,insert_erase hp]
    · intro k
      cases k with
      | zero => simp [leafEnergy]
      | succ k =>
        have hpR : p ∉ (l.take k).toFinset := by
          simp only [List.mem_toFinset]
          exact fun hx => hpL (List.mem_of_mem_take hx)
        simp only [List.take_succ_cons,List.toFinset_cons]
        rw [leaf_insert a b h U _ p hpR]
        refine (hbound k).trans ?_
        rw [htotal]
        exact max_le hsafe (le_max_right _ _)
  · have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    subst U
    exact ⟨[],by simp,by simp,by simp [leafEnergy]⟩

private lemma square_as_fibre (P : Finset ℕ) (M : ℕ) {r : ℕ}
    (hs : Squarefree r) (hd : Disjoint r.primeFactors P) :
    (r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ) =
      (mobiusDivisorSelectionFibre M P r.primeFactors)^(2 : ℕ) := by
  have h := mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hd
  rw [Nat.prod_primeFactors_of_squarefree hs] at h
  have hm : (((ArithmeticFunction.moebius r : ℤ):ℝ))^(2 : ℕ)=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
  rw [h,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg r),hm,mul_one]

private lemma sample_terminal (P : Finset ℕ) (M : ℕ) :
    mobiusDivisorInterpolatedFibre M M P ∅=0 := by
  by_cases hm : M=0
  · subst M
    simp [mobiusDivisorInterpolatedFibre,divisorPrimeClipWeight,
      mobiusDivisorSelectionFibre,mobiusDivisorSelectionIndices,subsetLabelFibre]
  · have h1 : mobiusDivisorSelectionFibre 1 P ∅=0 := by
      simp [mobiusDivisorSelectionFibre,mobiusDivisorSelectionIndices,subsetLabelFibre]
    simp [mobiusDivisorInterpolatedFibre,divisorPrimeClipWeight,
      Nat.div_self (by omega : 0<M),h1]

/-- After all square-root primes are processed, the full clock energy is
the head square plus the literal logarithmically weighted singleton squares. -/
theorem mobiusDivisorFiniteClockEnergy_terminal (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorFiniteClockEnergy 1 M P = (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)+
      ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
        (1+Real.log p)*(mobiusDivisorSelectionFibre M P {p})^(2 : ℕ) := by
  by_cases hm : M=0
  · subst M
    simp [mobiusDivisorFiniteClockEnergy,fixedCoreSquarefreeIndices,
      mobiusDivisorSelectionPrimes,mobiusDivisorSelectionFibre,
      mobiusDivisorSelectionIndices,subsetLabelFibre]
  have hM : 1 ≤ M := by omega
  let U := mobiusDivisorSelectionPrimes M \ P
  let S := fixedCoreSquarefreeIndices P M
  have h1U : 1 ∉ U := by simp [U,mobiusDivisorSelectionPrimes,Nat.not_prime_one]
  have hsub : insert 1 U ⊆ S := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · simp [S,fixedCoreSquarefreeIndices,hM]
    · obtain ⟨hrM,hrP⟩ := mem_sdiff.mp hr
      obtain ⟨hrM,hrprime⟩ := mem_filter.mp hrM
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hrprime.pos,(mem_range.mp hrM).le⟩,
        hrprime.squarefree,by simpa [hrprime.primeFactors] using hrP⟩
  have he : mobiusDivisorFiniteClockEnergy 1 M P =
      ∑ r ∈ S,(1+Real.log r)*(mobiusDivisorSelectionFibre M P r.primeFactors)^(2 : ℕ) := by
    apply sum_congr rfl
    intro r hr
    obtain ⟨_,hs,hd⟩ := mem_filter.mp hr
    rw [mul_assoc,square_as_fibre P M hs hd]
  rw [he]
  have hsum : (∑ r ∈ insert 1 U,
      (1+Real.log r)*(mobiusDivisorSelectionFibre M P r.primeFactors)^(2 : ℕ))=
      ∑ r ∈ S,(1+Real.log r)*(mobiusDivisorSelectionFibre M P r.primeFactors)^(2 : ℕ) := by
    apply sum_subset hsub
    intro r hr hn
    obtain ⟨hr,hs,hd⟩ := mem_filter.mp hr
    obtain ⟨hr1,hrM⟩ := mem_Icc.mp hr
    by_cases heq : r=M
    · subst r
      rw [← square_as_fibre P M hs hd,sample_terminal]
      simp
    · have hlabel := mobiusDivisorSelectionLabel_card_le_one M P hP r
        (mem_filter.mpr ⟨mem_Icc.mpr ⟨hr1,by omega⟩,hs⟩)
      have hdif : r.primeFactors \ P=r.primeFactors := by
        ext p
        simp only [Finset.mem_sdiff]
        exact ⟨And.left,fun hp => ⟨hp,fun hpP => disjoint_left.mp hd hp hpP⟩⟩
      rw [hdif] at hlabel
      have hne : r.primeFactors.Nonempty := by
        apply nonempty_iff_ne_empty.mpr
        intro hzero
        have hp := Nat.prod_primeFactors_of_squarefree hs
        rw [hzero,prod_empty] at hp
        exact hn (hp ▸ mem_insert_self 1 U)
      have hc : r.primeFactors.card=1 := by have := card_pos.mpr hne; omega
      obtain ⟨p,hp⟩ := card_eq_one.mp hc
      have hprod := Nat.prod_primeFactors_of_squarefree hs
      rw [hp,prod_singleton] at hprod
      have hprime := (Nat.mem_primeFactors.mp (hp.symm ▸ mem_singleton_self p)).1
      have hpP : p ∉ P := fun hpP => disjoint_left.mp hd (hp.symm ▸ mem_singleton_self p) hpP
      have hrU : r ∈ U := by
        apply Finset.mem_sdiff.mpr
        refine ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hprod ▸ hprime⟩,hprod ▸ hpP⟩
      exact (hn (mem_insert_of_mem hrU)).elim
  rw [← hsum,sum_insert h1U]
  simp only [Nat.primeFactors_one,Real.log_one,add_zero,one_mul,Nat.cast_one]
  congr 1
  apply sum_congr rfl
  intro p hp
  have hpU : p ∈ mobiusDivisorSelectionPrimes M \ P := hp
  have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpU).1).2
  rw [hprime.primeFactors]

private lemma clock_union_terminal (M : ℕ) (P R : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorFiniteClockEnergy 1 M (P ∪ R)=
      leafEnergy (fun p => mobiusDivisorSelectionFibre M P {p})
        (fun p => (1+Real.log p)*(mobiusDivisorSelectionFibre M P {p})^(2 : ℕ))
        (mobiusDivisorSelectionFibre M P ∅) (mobiusDivisorSelectionPrimes M \ P) R := by
  rw [mobiusDivisorFiniteClockEnergy_terminal M (P ∪ R) (hP.trans subset_union_left),
    mobiusDivisorSelectionHead_union_terminal M P R hP,leafEnergy]
  congr 1
  have he : mobiusDivisorSelectionPrimes M \ (P ∪ R)=
      (mobiusDivisorSelectionPrimes M \ P) \ R := by
    ext p
    simp
    tauto
  rw [he]
  apply sum_congr rfl
  intro p hp
  rw [mobiusDivisorSelectionFibre_singleton_union_terminal M P R hP p,
    if_neg (mem_sdiff.mp hp).2]

/-- The logarithmic cofactor weight permits a complete terminal insertion
order without any peak above the larger actual endpoint energy. -/
theorem exists_mobiusDivisorTerminalClockOrder (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    ∃ l : List ℕ,l.Nodup ∧ l.toFinset=mobiusDivisorSelectionPrimes M \ P ∧ ∀ k : ℕ,
      mobiusDivisorFiniteClockEnergy 1 M (P ∪ (l.take k).toFinset) ≤
        max (mobiusDivisorFiniteClockEnergy 1 M P)
          ((∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d)^(2 : ℕ)) := by
  have hb (p : ℕ) (_hp : p ∈ mobiusDivisorSelectionPrimes M \ P) :
      (mobiusDivisorSelectionFibre M P {p})^(2 : ℕ) ≤
        (1+Real.log p)*(mobiusDivisorSelectionFibre M P {p})^(2 : ℕ) := by
    have := mul_nonneg (Real.log_natCast_nonneg p)
      (sq_nonneg (mobiusDivisorSelectionFibre M P {p}))
    nlinarith only [this]
  obtain ⟨l,hl,hset,hbound⟩ := exists_leaf_order
    (fun p => mobiusDivisorSelectionFibre M P {p})
    (fun p => (1+Real.log p)*(mobiusDivisorSelectionFibre M P {p})^(2 : ℕ))
    (mobiusDivisorSelectionFibre M P ∅) (mobiusDivisorSelectionPrimes M \ P) hb
  refine ⟨l,hl,hset,fun k => ?_⟩
  rw [clock_union_terminal M P _ hP]
  have hk := hbound k
  rw [← mobiusDivisorFiniteClockEnergy_terminal M P hP,
    mobiusDivisorSelectionHead_add_terminal_leaves M P hP] at hk
  exact hk

/-- The canonical square-root prime core admits an endpoint-optimal complete
order for the full logarithmically weighted clock energy. -/
theorem exists_mobiusDivisorSquareRootTerminalClockOrder (M : ℕ) :
    ∃ l : List ℕ,l.Nodup ∧
      l.toFinset=mobiusDivisorSelectionPrimes M \ mobiusDivisorSmallSelectionPrimes M ∧
      ∀ k : ℕ,mobiusDivisorFiniteClockEnergy 1 M
        (mobiusDivisorSmallSelectionPrimes M ∪ (l.take k).toFinset) ≤
        max (mobiusDivisorFiniteClockEnergy 1 M (mobiusDivisorSmallSelectionPrimes M))
          ((∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d)^(2 : ℕ)) := by
  exact exists_mobiusDivisorTerminalClockOrder M (mobiusDivisorSmallSelectionPrimes M) Subset.rfl

private lemma square_root_subset_previous {M : ℕ} (hM : 8 ≤ M) :
    mobiusDivisorSmallSelectionPrimes (8*M) ⊆ mobiusDivisorSelectionPrimes M := by
  intro p hp
  obtain ⟨hp,hsmall⟩ := mem_filter.mp hp
  obtain ⟨_,hprime⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨mem_range.mpr ?_,hprime⟩
  by_contra hn
  have hMp : M ≤ p := by omega
  have hsq : M*M ≤ p*p := Nat.mul_le_mul hMp hMp
  nlinarith

/-- Actual nested prime-exhaustive clock cores admit complete orders at
every checkpoint. Each order preserves the full logarithmic energy and
has no intermediate cost beyond the larger of the uniform initial budget
and the literal completed source square. The completed source square is
retained explicitly; it is not bounded here. -/
theorem exists_mobiusDivisorExhaustiveClockOrders :
    ∃ M : ℕ → ℕ, ∃ P : ℕ → Finset ℕ, ∃ l : ℕ → List ℕ,
      0 < M 0 ∧ (∀ n,M (n+1)=8*M n) ∧ StrictMono M ∧
      (∀ n,P n ⊆ mobiusDivisorSelectionPrimes (M n)) ∧
      (∀ n,mobiusDivisorSelectionPrimes (M n) ⊆ P (n+1)) ∧ Monotone P ∧
      (∀ p : ℕ,p.Prime → ∀ᶠ n : ℕ in atTop,p ∈ P n) ∧
      (∀ n,mobiusDivisorFiniteClockEnergy 1 (M n) (P n) ≤ 200*(M n:ℝ)^(2 : ℕ)) ∧
      ∀ n,(l n).Nodup ∧ (l n).toFinset=mobiusDivisorSelectionPrimes (M n) \ P n ∧
        P n ∪ (l n).toFinset=mobiusDivisorSelectionPrimes (M n) ∧
        ∀ k : ℕ,mobiusDivisorFiniteClockEnergy 1 (M n) (P n ∪ ((l n).take k).toFinset) ≤
          max (200*(M n:ℝ)^(2 : ℕ))
            ((∑ d ∈ Icc 1 (M n),mobiusDivisorDilationChannel (M n) d)^(2 : ℕ)) := by
  obtain ⟨M,P,hpos,hstep,hmono,hsub,hprev,hPmono,hexhaust,henergy,_hcollar⟩ :=
    exists_mobiusDivisorExhaustiveClockCheckpoints
  have hmpos (n : ℕ) : 0<M n := hpos.trans_le (hmono.monotone (Nat.zero_le n))
  have hterminal (n : ℕ) : mobiusDivisorSmallSelectionPrimes (M (n+2)) ⊆ P (n+2) := by
    have hm8 : 8 ≤ M (n+1) := by rw [hstep]; nlinarith [hmpos n]
    have ht := (square_root_subset_previous hm8).trans (hprev (n+1))
    rw [hstep (n+1)]
    exact ht
  have hall (n : ℕ) := exists_mobiusDivisorTerminalClockOrder (M (n+2)) (P (n+2)) (hterminal n)
  choose l hnodup hset hbound using hall
  refine ⟨(fun n => M (n+2)),(fun n => P (n+2)),l,hmpos 2,?_,?_,
    (fun n => hsub (n+2)),?_,?_,?_,(fun n => henergy (n+2)),?_⟩
  · intro n
    exact hstep (n+2)
  · intro n m hnm
    exact hmono (by omega)
  · intro n
    exact hprev (n+2)
  · intro n m hnm
    exact hPmono (by omega)
  · intro p hp
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hexhaust p hp)
    exact eventually_atTop.mpr ⟨N,fun n hn => hN (n+2) (by omega)⟩
  · intro n
    refine ⟨hnodup n,hset n,?_,fun k => (hbound n k).trans ?_⟩
    · rw [hset]
      exact union_sdiff_of_subset (hsub (n+2))
    · exact max_le_max (henergy (n+2)) le_rfl

end RHTower
