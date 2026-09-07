import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergy
import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport
import GaloisForLFunctions.RHTower.MobiusDivisorAbelQuadraticDiagonal
import GaloisForLFunctions.RHTower.MobiusDivisorHeadNeutralization
import GaloisForLFunctions.RHTower.SignedScalarMergeOrder
/-!
# Isolated signed prime batches before the terminal phase

Completing the adjacent quotient core isolates a prime into its retained
singleton. Any such pool admits an endpoint-optimal signed scalar order.
Opposite supplies can be matched so removed singleton squares pay the final
head, giving a complete selected-batch order below its initial energy.
Every partial preparation of the fixed small core has a quadratic bound.
-/

noncomputable section
open Finset
namespace RHTower

private theorem source_primes_mono {a b : ℕ} (hab : a≤b) :
    mobiusDivisorSelectionPrimes a⊆mobiusDivisorSelectionPrimes b := by
  intro q hq
  obtain ⟨hq,hprime⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hq).trans_le hab),hprime⟩

/-- Once the adjacent quotient source is completely processed, a prime has no nonscalar partner. -/
theorem mobiusDivisorSelectionFibre_insertLabel_isolated (M : ℕ) (P R : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (hpR : p∉R)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)⊆P) :
    mobiusDivisorSelectionFibre M P (insert p R)=
      if R=∅ then mobiusDivisorSelectionFibre M P {p} else 0 := by
  by_cases hR : R=∅
  · simp [hR]
  rw [if_neg hR,mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP hpR,
    mobiusDivisorInterpolatedFibre,
    mobiusDivisorSelectionFibre_of_all_source_primes_processed (M/p) P R
      ((source_primes_mono (by omega : M/p≤M/p+1)).trans hcore),
    mobiusDivisorSelectionFibre_of_all_source_primes_processed (M/p+1) P R hcore,
    if_neg hR,if_neg hR]
  ring

private theorem isolated_singleton_union (M : ℕ) (P L : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpP : p∉P) (hpL : p∉L)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)⊆P) :
    mobiusDivisorSelectionFibre M (P∪L) {p}=mobiusDivisorSelectionFibre M P {p} := by
  revert hpL
  induction L using Finset.induction_on with
  | empty => intro _; simp
  | @insert q L hqL ih =>
    intro hpL
    have hpq : p≠q := fun he => hpL (mem_insert.mpr (Or.inl he))
    have hpL' : p∉L := fun h => hpL (mem_insert_of_mem h)
    have hzero : mobiusDivisorSelectionFibre M (P∪L) (insert q {p})=0 := by
      rw [show insert q ({p}:Finset ℕ)=insert p {q} by ext x; simp [or_comm]]
      rw [mobiusDivisorSelectionFibre_insertLabel_isolated M (P∪L) {q} hp
        (by simp [hpP,hpL']) (by simpa using hpq) (hcore.trans subset_union_left)]
      simp
    rw [union_insert,mobiusDivisorSelectionFibre_insert,if_neg (by simpa using Ne.symm hpq),hzero,add_zero]
    exact ih hpL'

/-- An isolated prime changes total energy only through its signed singleton and current head. -/
theorem mobiusDivisorSelectionEnergy_insert_isolated (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpM : p<M) (hpP : p∉P)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)⊆P) :
    mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P=
      2*mobiusDivisorSelectionFibre M P ∅*mobiusDivisorSelectionFibre M P {p} := by
  rw [mobiusDivisorSelectionEnergy_insert_cross hp M P hpM hpP]
  rw [mul_assoc]
  congr 1
  rw [sum_eq_single ∅]
  · simp
  · intro R hR hne
    have hpR : p∉R := by
      intro h
      have := mem_powerset.mp hR h
      simp at this
    rw [mobiusDivisorSelectionFibre_insertLabel_isolated M P R hp hpP hpR hcore,if_neg hne,mul_zero]
  · simp

private theorem isolated_head_union (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ mobiusDivisorSelectionPrimes (M/p+1)⊆P) :
    mobiusDivisorSelectionFibre M (P∪L) ∅=mobiusDivisorSelectionFibre M P ∅+
      ∑ p∈L,mobiusDivisorSelectionFibre M P {p} := by
  revert hL
  induction L using Finset.induction_on with
  | empty => intro _; simp
  | @insert p L hpL ih =>
    intro hL
    obtain ⟨hp,hpM,hpP,hcore⟩ := hL p (mem_insert_self p L)
    have hL' := fun q hq => hL q (mem_insert_of_mem hq)
    rw [union_insert,mobiusDivisorSelectionFibre_insert]
    simp only [notMem_empty,if_false,insert_empty_eq]
    rw [isolated_singleton_union M P L hp hpP hpL hcore,ih hL',sum_insert hpL]
    ring

/-- Exact signed energy for any isolated pool, before or after the global terminal stage. -/
theorem mobiusDivisorSelectionEnergy_union_isolated (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ mobiusDivisorSelectionPrimes (M/p+1)⊆P) :
    mobiusDivisorSelectionEnergy M (P∪L)=mobiusDivisorSelectionEnergy M P+
      2*mobiusDivisorSelectionFibre M P ∅*(∑ p∈L,mobiusDivisorSelectionFibre M P {p})+
      (∑ p∈L,mobiusDivisorSelectionFibre M P {p})^2-
      ∑ p∈L,(mobiusDivisorSelectionFibre M P {p})^2 := by
  revert hL
  induction L using Finset.induction_on with
  | empty => intro _; simp
  | @insert p L hpL ih =>
    intro hL
    obtain ⟨hp,hpM,hpP,hcore⟩ := hL p (mem_insert_self p L)
    have hL' := fun q hq => hL q (mem_insert_of_mem hq)
    have he := mobiusDivisorSelectionEnergy_insert_isolated M (P∪L) hp hpM
      (by simp [hpP,hpL]) (hcore.trans subset_union_left)
    rw [isolated_singleton_union M P L hp hpP hpL hcore,isolated_head_union M P L hL',ih hL'] at he
    rw [union_insert,sum_insert hpL,sum_insert hpL]
    nlinarith only [he]

/-- Every isolated signed pool has a complete order below the larger actual endpoint energy. -/
theorem exists_mobiusDivisorIsolatedPrimeOrder (M : ℕ) (P U : Finset ℕ)
    (hU : ∀ p∈U,p.Prime ∧ p<M ∧ p∉P ∧ mobiusDivisorSelectionPrimes (M/p+1)⊆P) :
    ∃ l : List ℕ,l.Nodup ∧ l.toFinset=U ∧ ∀ k : ℕ,
      mobiusDivisorSelectionEnergy M (P∪(l.take k).toFinset)≤
        max (mobiusDivisorSelectionEnergy M P) (mobiusDivisorSelectionEnergy M (P∪U)) := by
  let c := fun p => mobiusDivisorSelectionFibre M P {p}
  let h := mobiusDivisorSelectionFibre M P ∅
  have hid (L : Finset ℕ) (hLU : L⊆U) :
      mobiusDivisorSelectionEnergy M (P∪L)=
        mobiusDivisorSelectionEnergy M P-h^2-(∑ p∈U,(c p)^2)+
          scalarSubsetMergeEnergy c h U L := by
    rw [mobiusDivisorSelectionEnergy_union_isolated M P L (fun p hp => hU p (hLU hp)),scalarSubsetMergeEnergy]
    have hs := sum_sdiff hLU (f := fun p => (c p)^2)
    dsimp [c,h] at *
    nlinarith only [hs]
  obtain ⟨l,hl,hset,hbound⟩ := exists_scalarSubsetMergeOrder c h U
  refine ⟨l,hl,hset,fun k => ?_⟩
  have htake : (l.take k).toFinset⊆U := by
    rw [← hset]
    intro p hp
    apply List.mem_toFinset.mpr
    exact (List.take_sublist k l).subset (List.mem_toFinset.mp hp)
  have hf := hid U Subset.rfl
  have hk := hid (l.take k).toFinset htake
  have hb := hbound k
  simp [scalarSubsetMergeEnergy] at hf
  rcases le_total (h^2+∑ p∈U,(c p)^2) ((h+∑ p∈U,c p)^2) with he|he
  · rw [max_eq_right he] at hb
    exact (by linarith only [hk,hf,hb] : _≤ mobiusDivisorSelectionEnergy M (P∪U)).trans (le_max_right _ _)
  · rw [max_eq_left he] at hb
    exact (by linarith only [hk,hb] : _≤ mobiusDivisorSelectionEnergy M P).trans (le_max_left _ _)

/-- Processing the fixed core below eight makes every unprocessed prime above one eighth of the cutoff an isolated scalar. -/
theorem mobiusDivisorPrime_isolated_after_eight (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSelectionPrimes 8⊆P) {p : ℕ} (hp : p.Prime) (hlarge : M<8*p) :
    mobiusDivisorSelectionPrimes (M/p+1)⊆P := by
  have hq := (Nat.div_lt_iff_lt_mul hp.pos).mpr hlarge
  exact (source_primes_mono (by omega : M/p+1≤8)).trans hP


/-- A single actual prime merger increases energy by at most a factor of two. -/
theorem mobiusDivisorSelectionEnergy_insert_le_double (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpM : p<M) (hpP : p∉P) :
    mobiusDivisorSelectionEnergy M (insert p P)≤2*mobiusDivisorSelectionEnergy M P := by
  have hg := mobiusDivisorParityGoodEnergy_nonneg M P
  have hd := mobiusDivisorParityDefectEnergy_nonneg M P
  have hgs := Real.sq_sqrt hg
  have hds := Real.sq_sqrt hd
  have hs := mobiusDivisorParityGoodEnergy_add_defect M P
  have he := mobiusDivisorSelectionEnergy_insert_le_parity_geometric M P hp hpM hpP
  have hsq := sq_nonneg (Real.sqrt (mobiusDivisorParityGoodEnergy M P)-
    Real.sqrt (mobiusDivisorParityDefectEnergy M P))
  nlinarith only [hgs,hds,hs,he,hsq]

/-- Processing a finite prime core costs at most one factor of two per processed prime. -/
theorem mobiusDivisorSelectionEnergy_le_pow_card (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime ∧ p<M) :
    mobiusDivisorSelectionEnergy M P≤(2:ℝ)^P.card*mobiusDivisorSelectionEnergy M ∅ := by
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | @insert p P hpP ih =>
    intro hP
    obtain ⟨hp,hpM⟩ := hP p (mem_insert_self p P)
    have hi := ih (fun q hq => hP q (mem_insert_of_mem hq))
    have hm := mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2)
    have he := mobiusDivisorSelectionEnergy_insert_le_double M P hp hpM hpP
    rw [card_insert_of_notMem hpP,pow_succ]
    nlinarith only [hm,he]

/-- Every partial preparation of the fixed core below eight has one uniform quadratic source bound. -/
theorem mobiusDivisorSelectionEnergy_small_core_le (M : ℕ) (hM : 8≤M) (P : Finset ℕ)
    (hP : P⊆mobiusDivisorSelectionPrimes 8) :
    mobiusDivisorSelectionEnergy M P≤(2:ℝ)^8*722*(M:ℝ)^2 := by
  have hprimes : ∀ p∈P,p.Prime ∧ p<M := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp (hP hp)
    exact ⟨hprime,(mem_range.mp hp).trans_le hM⟩
  have he := mobiusDivisorSelectionEnergy_le_pow_card M P hprimes
  have hc : P.card≤8 := (card_le_card hP).trans
    (by simpa only [mobiusDivisorSelectionPrimes,card_range] using
      (card_filter_le (s := range 8) (p := Nat.Prime)))
  have hpow : (2:ℝ)^P.card≤2^8 := by gcongr; norm_num
  have hdiag := sum_mobiusDivisorDilationChannel_sq_le_quadratic M
  rw [mobiusDivisorSelectionEnergy_empty] at he
  have hmult := mul_le_mul_of_nonneg_left hdiag (by positivity : (0:ℝ)≤2^P.card)
  have hlast := mul_le_mul_of_nonneg_right hpow (by positivity : (0:ℝ)≤722*(M:ℝ)^2)
  exact he.trans (hmult.trans (by nlinarith only [hlast]))


private theorem exists_cover_with_removed_square {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α→ℝ) (h : ℝ) (hh : 0≤h)
    (hw : ∀ p∈U,0≤w p) (hcover : h≤∑ p∈U,w p) :
    ∃ L⊆U,h≤∑ p∈L,w p ∧ (h-∑ p∈L,w p)^2≤∑ p∈L,(w p)^2 := by
  obtain ⟨L,hLU,h0,h1,hs⟩ := exists_mass_cover_with_square_reserve U w (∑ p∈U,w p)
    (sum_nonneg hw) h hh (fun p hp => ⟨hw p hp,single_le_sum hw hp⟩) hcover
  exact ⟨L,hLU,by linarith only [h0],by nlinarith only [hs]⟩

/-- Opposite signed finite supplies can be matched while their removed squares pay the entire final head. Both consumed masses reach the smaller available supply minus the initial head magnitude. -/
theorem exists_signedScalarBalancedBatch {α : Type*} [DecidableEq α]
    (c : α→ℝ) (h : ℝ) (A B : Finset α)
    (hA : ∀ p∈A,0≤c p) (hB : ∀ p∈B,c p≤0)
    (hcoverA : |h|≤∑ p∈A,c p) (hcoverB : |h|≤∑ p∈B,-c p) :
    ∃ L⊆A,∃ R⊆B,
      (h+(∑ p∈L,c p)+(∑ p∈R,c p))^2≤
        (∑ p∈L,(c p)^2)+(∑ p∈R,(c p)^2) ∧
      min (∑ p∈A,c p) (∑ p∈B,-c p)-|h|≤∑ p∈L,c p ∧
      min (∑ p∈A,c p) (∑ p∈B,-c p)-|h|≤∑ p∈R,-c p := by
  have hh0 := abs_nonneg h
  have hhi := le_abs_self h
  have hlo := neg_abs_le h
  by_cases hcomp : h+(∑ p∈A,c p)≤∑ p∈B,-c p
  · obtain ⟨R,hRB,hR,hs⟩ := exists_cover_with_removed_square B (fun p => -c p)
      (h+∑ p∈A,c p) (by linarith only [hcoverA,hlo])
      (fun p hp => neg_nonneg.mpr (hB p hp)) hcomp
    refine ⟨A,Subset.rfl,R,hRB,?_,?_,?_⟩
    · simp only [sum_neg_distrib,neg_sq] at hs
      have ha := sum_nonneg (s := A) (fun p _ => sq_nonneg (c p))
      nlinarith only [hs,ha]
    · linarith only [min_le_left (∑ p∈A,c p) (∑ p∈B,-c p),hh0]
    · linarith only [min_le_left (∑ p∈A,c p) (∑ p∈B,-c p),hR,hlo]
  · have htarget : (∑ p∈B,-c p)-h≤∑ p∈A,c p := by linarith only [hcomp]
    obtain ⟨L,hLA,hL,hs⟩ := exists_cover_with_removed_square A c
      ((∑ p∈B,-c p)-h) (by linarith only [hcoverB,hhi]) hA htarget
    refine ⟨L,hLA,B,Subset.rfl,?_,?_,?_⟩
    · simp only [sum_neg_distrib] at hs
      have hb := sum_nonneg (s := B) (fun p _ => sq_nonneg (c p))
      nlinarith only [hs,hb]
    · linarith only [min_le_right (∑ p∈A,c p) (∑ p∈B,-c p),hL,hhi]
    · linarith only [min_le_right (∑ p∈A,c p) (∑ p∈B,-c p),hh0]

/-- Opposite isolated source pools admit a matched batch with complete order under the starting energy, consuming both signs up to the smaller available mass minus the initial head magnitude. -/
theorem exists_mobiusDivisorBalancedIsolatedBatch (M : ℕ) (P A B : Finset ℕ)
    (hAB : Disjoint A B)
    (hU : ∀ p∈A∪B,p.Prime ∧ p<M ∧ p∉P ∧ mobiusDivisorSelectionPrimes (M/p+1)⊆P)
    (hA : ∀ p∈A,0≤ mobiusDivisorSelectionFibre M P {p})
    (hB : ∀ p∈B,mobiusDivisorSelectionFibre M P {p}≤0)
    (hcoverA : |mobiusDivisorSelectionFibre M P ∅|≤∑ p∈A,mobiusDivisorSelectionFibre M P {p})
    (hcoverB : |mobiusDivisorSelectionFibre M P ∅|≤∑ p∈B,-mobiusDivisorSelectionFibre M P {p}) :
    ∃ L⊆A,∃ R⊆B,
      (min (∑ p∈A,mobiusDivisorSelectionFibre M P {p})
        (∑ p∈B,-mobiusDivisorSelectionFibre M P {p})-|mobiusDivisorSelectionFibre M P ∅|≤
          ∑ p∈L,mobiusDivisorSelectionFibre M P {p}) ∧
      (min (∑ p∈A,mobiusDivisorSelectionFibre M P {p})
        (∑ p∈B,-mobiusDivisorSelectionFibre M P {p})-|mobiusDivisorSelectionFibre M P ∅|≤
          ∑ p∈R,-mobiusDivisorSelectionFibre M P {p}) ∧
      ∃ l : List ℕ,l.Nodup ∧ l.toFinset=L∪R ∧ ∀ k : ℕ,
        mobiusDivisorSelectionEnergy M (P∪(l.take k).toFinset)≤ mobiusDivisorSelectionEnergy M P := by
  obtain ⟨L,hLA,R,hRB,hres,hL,hR⟩ := exists_signedScalarBalancedBatch
    (fun p => mobiusDivisorSelectionFibre M P {p}) (mobiusDivisorSelectionFibre M P ∅)
    A B hA hB hcoverA hcoverB
  have hLR : Disjoint L R := hAB.mono hLA hRB
  have hsub : L∪R⊆A∪B := union_subset_union hLA hRB
  have hU' := fun p hp => hU p (hsub hp)
  have he := mobiusDivisorSelectionEnergy_union_isolated M P (L∪R) hU'
  rw [sum_union hLR,sum_union hLR] at he
  have hfinal : mobiusDivisorSelectionEnergy M (P∪(L∪R))≤ mobiusDivisorSelectionEnergy M P := by
    nlinarith only [he,hres,sq_nonneg (mobiusDivisorSelectionFibre M P ∅)]
  obtain ⟨l,hl,hset,hbound⟩ := exists_mobiusDivisorIsolatedPrimeOrder M P (L∪R) hU'
  refine ⟨L,hLA,R,hRB,hL,hR,l,hl,hset,fun k => ?_⟩
  simpa only [max_eq_left hfinal] using hbound k
end RHTower
