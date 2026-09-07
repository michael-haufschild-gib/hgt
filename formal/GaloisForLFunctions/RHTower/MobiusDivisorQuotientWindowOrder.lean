import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergy
import GaloisForLFunctions.RHTower.AffineFieldSubsetOrder

/-!
# Complete actual prime-window orders after arbitrary processed states

Primes in one quotient window above the joint-product threshold carry a fixed
reflected interpolation of the same two retained fields, even after processing
any part of that window. Exact energy marginals retain all signed packet
inner products. The source's transverse sign partitions an arbitrary subpool
into two classes with nonnegative pair overlaps. Each class admits a complete
order under its endpoint energies; concatenation needs only the separating
energy fixed by that source partition in advance.

No retained-sign hypothesis, numerical certificate, or unproved arithmetic
bound is assumed by the complete-window theorem. The three source-defined
endpoint energies still require bounds for a global growing schedule or RH.
-/

noncomputable section
open Finset
namespace RHTower

/-- The literal reflected quotient field carried by an unprocessed prime. -/
def mobiusDivisorPrimePacket (M : ℕ) (P : Finset ℕ) (p : ℕ) (R : Finset ℕ) : ℝ :=
  -Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R

/-- Complete signed inner product of two actual copied prime fields. -/
def mobiusDivisorPrimePacketOverlap (M : ℕ) (P : Finset ℕ) (p q : ℕ) : ℝ :=
  ∑ R∈(mobiusDivisorSelectionPrimes M).powerset,
    mobiusDivisorPrimePacket M P p R*mobiusDivisorPrimePacket M P q R

/-- The complete unprocessed prime pool in one quotient window above the joint-product threshold. -/
def mobiusDivisorQuotientWindowPrimes (M N : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (mobiusDivisorSelectionPrimes M\P).filter (fun p => M/p=N ∧ N+1≤p)

private theorem small_fibre_zero_of_large_label (N : ℕ) (P R : Finset ℕ)
    {p : ℕ} (hp : N≤p) (hpR : p∈R) : mobiusDivisorSelectionFibre N P R=0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have he : d.primeFactors\P≠R := by
    intro he
    have hpd : p∈d.primeFactors := (mem_sdiff.mp (he.symm ▸ hpR)).1
    have hn := mem_Icc.mp (mem_filter.mp hd).1
    have hle := Nat.le_of_mem_primeFactors hpd
    omega
  simp only [if_neg he]

/-- Primes outside the active cutoff do not change any retained source label. -/
theorem mobiusDivisorSelectionFibre_union_inactive (N : ℕ) (P L R : Finset ℕ)
    (hL : ∀ p∈L,N≤p) :
    mobiusDivisorSelectionFibre N (P∪L) R=mobiusDivisorSelectionFibre N P R := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_congr rfl
  intro d hd
  have hnone : ∀ p∈d.primeFactors,p∉L := by
    intro p hp hpL
    have hn := mem_Icc.mp (mem_filter.mp hd).1
    have hle := Nat.le_of_mem_primeFactors hp
    have hge := hL p hpL
    omega
  have he : d.primeFactors\(P∪L)=d.primeFactors\P := by
    ext p
    simp only [mem_sdiff,mem_union,not_or]
    constructor
    · rintro ⟨hpd,hpP,hpL⟩
      exact ⟨hpd,hpP⟩
    · rintro ⟨hpd,hpP⟩
      exact ⟨hpd,hpP,hnone p hpd⟩
  rw [he]

private theorem prime_packet_zero_large_label (M N q : ℕ) (P R : Finset ℕ)
    (hq : M/q=N) {p : ℕ} (hp : N+1≤p) (hpR : p∈R) : mobiusDivisorPrimePacket M P q R=0 := by
  unfold mobiusDivisorPrimePacket mobiusDivisorInterpolatedFibre
  rw [hq,small_fibre_zero_of_large_label N P R (by omega) hpR,
    small_fibre_zero_of_large_label (N+1) P R hp hpR]
  ring

/-- Every copied field in the window remains fixed under processing any part of that window. -/
theorem mobiusDivisorPrimePacket_union_inactive (M N q : ℕ) (P L : Finset ℕ)
    (hq : M/q=N) (hL : ∀ p∈L,N+1≤p) (R : Finset ℕ) :
    mobiusDivisorPrimePacket M (P∪L) q R=mobiusDivisorPrimePacket M P q R := by
  unfold mobiusDivisorPrimePacket mobiusDivisorInterpolatedFibre
  rw [hq,mobiusDivisorSelectionFibre_union_inactive N P L R (fun p hp => by have := hL p hp; omega),
    mobiusDivisorSelectionFibre_union_inactive (N+1) P L R hL]

private theorem prime_packet_eq_partner (M : ℕ) (P R : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpP : p∉P) (hpR : p∉R) :
    mobiusDivisorSelectionFibre M P (insert p R)=mobiusDivisorPrimePacket M P p R :=
  mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP hpR

private theorem window_head_union (M N : ℕ) (P L R : Finset ℕ)
    (hL : ∀ p∈L,p.Prime ∧ p∉P ∧ M/p=N ∧ N+1≤p) (hdis : Disjoint R L) :
    mobiusDivisorSelectionFibre M (P∪L) R=mobiusDivisorSelectionFibre M P R+
      ∑ p∈L,mobiusDivisorPrimePacket M P p R := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert p L hpL ih =>
    obtain ⟨hp,hpP,hquot,hlarge⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q∈L,q.Prime ∧ q∉P ∧ M/q=N ∧ N+1≤q :=
      fun q hq => hL q (mem_insert_of_mem hq)
    have hpR : p∉R := fun h => disjoint_left.mp hdis h (mem_insert_self p L)
    have hdis' : Disjoint R L := disjoint_left.mpr
      (fun q hq hqL => disjoint_left.mp hdis hq (mem_insert_of_mem hqL))
    rw [union_insert,mobiusDivisorSelectionFibre_insert,if_neg hpR,
      prime_packet_eq_partner M (P∪L) R hp (by simp [hpP,hpL]) hpR,
      mobiusDivisorPrimePacket_union_inactive M N p P L hquot (fun q hq => (hL' q hq).2.2.2),
      ih hL' hdis',sum_insert hpL]
    ring

private theorem window_packet_product (M N q : ℕ) (P L R : Finset ℕ)
    (hq : M/q=N) (hL : ∀ p∈L,p.Prime ∧ p∉P ∧ M/p=N ∧ N+1≤p) :
    mobiusDivisorSelectionFibre M (P∪L) R*mobiusDivisorPrimePacket M P q R =
      (mobiusDivisorSelectionFibre M P R+∑ p∈L,mobiusDivisorPrimePacket M P p R)*
        mobiusDivisorPrimePacket M P q R := by
  by_cases hdis : Disjoint R L
  · rw [window_head_union M N P L R hL hdis]
  · have hex : ∃ p∈R,p∈L := by simpa only [disjoint_left,not_forall,not_not,exists_prop] using hdis
    obtain ⟨p,hpR,hpL⟩ := hex
    rw [prime_packet_zero_large_label M N q P R hq (hL p hpL).2.2.2 hpR]
    ring

/-- Exact window merger marginal: the original signed interaction plus every already-consumed packet overlap. -/
theorem mobiusDivisorSelectionEnergy_window_marginal (M N : ℕ) (P L : Finset ℕ) {q : ℕ}
    (hq : q.Prime) (hqM : q<M) (hqP : q∉P) (hqL : q∉L) (hquot : M/q=N) (hlarge : N+1≤q)
    (hL : ∀ p∈L,p.Prime ∧ p∉P ∧ M/p=N ∧ N+1≤p) :
    mobiusDivisorSelectionEnergy M (P∪insert q L)-mobiusDivisorSelectionEnergy M (P∪L) =
      2*(∑ R∈(mobiusDivisorSelectionPrimes M).powerset,
        mobiusDivisorSelectionFibre M P R*mobiusDivisorPrimePacket M P q R)+
      2*(∑ p∈L,mobiusDivisorPrimePacketOverlap M P p q) := by
  rw [union_insert,mobiusDivisorSelectionEnergy_insert_cross hq M (P∪L) hqM (by simp [hqP,hqL])]
  have hRfree {R : Finset ℕ} (hR : R∈((mobiusDivisorSelectionPrimes M).erase q).powerset) : q∉R := by
    intro h
    have hm := mem_powerset.mp hR h
    exact (mem_erase.mp hm).1 rfl
  have he : (∑ R∈((mobiusDivisorSelectionPrimes M).erase q).powerset,
      mobiusDivisorSelectionFibre M (P∪L) R*mobiusDivisorSelectionFibre M (P∪L) (insert q R)) =
      ∑ R∈(mobiusDivisorSelectionPrimes M).powerset,
        mobiusDivisorSelectionFibre M (P∪L) R*mobiusDivisorPrimePacket M P q R := by
    calc
      _ = ∑ R∈((mobiusDivisorSelectionPrimes M).erase q).powerset,
          mobiusDivisorSelectionFibre M (P∪L) R*mobiusDivisorPrimePacket M P q R := by
        apply sum_congr rfl
        intro R hR
        rw [prime_packet_eq_partner M (P∪L) R hq (by simp [hqP,hqL]) (hRfree hR),
          mobiusDivisorPrimePacket_union_inactive M N q P L hquot (fun p hp => (hL p hp).2.2.2)]
      _ = _ := by
        apply sum_subset (powerset_mono.mpr (erase_subset q _))
        intro R hR hnR
        have hqR : q∈R := by
          by_contra hn
          apply hnR
          exact mem_powerset.mpr (fun p hp => mem_erase.mpr ⟨fun he => hn (he ▸ hp),mem_powerset.mp hR hp⟩)
        rw [prime_packet_zero_large_label M N q P R hquot hlarge hqR,mul_zero]
  rw [he]
  simp_rw [window_packet_product M N q P L _ hquot hL,add_mul,sum_mul]
  rw [sum_add_distrib,mul_add]
  congr 1
  rw [sum_comm]
  rfl

/-- The affine quotient field's signed coordinate along its common adjacent-cutoff direction. -/
def mobiusDivisorQuotientTransverse (M N : ℕ) (P : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ R∈(mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre N P R+divisorPrimeClipWeight M p*
      (mobiusDivisorSelectionFibre (N+1) P R-mobiusDivisorSelectionFibre N P R))*
      (mobiusDivisorSelectionFibre (N+1) P R-mobiusDivisorSelectionFibre N P R)

/-- All signed packet overlaps are unchanged while processing the same inactive quotient window. -/
theorem mobiusDivisorPrimePacketOverlap_union_inactive (M N p q : ℕ) (P L : Finset ℕ)
    (hp : M/p=N) (hq : M/q=N) (hL : ∀ r∈L,N+1≤r) :
    mobiusDivisorPrimePacketOverlap M (P∪L) p q=mobiusDivisorPrimePacketOverlap M P p q := by
  unfold mobiusDivisorPrimePacketOverlap
  apply sum_congr rfl
  intro R hR
  rw [mobiusDivisorPrimePacket_union_inactive M N p P L hp hL,
    mobiusDivisorPrimePacket_union_inactive M N q P L hq hL]

/-- Actual same-quotient packets have nonnegative overlap whenever their transverse coordinates have the same sign. -/
theorem mobiusDivisorPrimePacketOverlap_nonneg_of_transverse_product (M N p q : ℕ) (P : Finset ℕ)
    (hp : M/p=N) (hq : M/q=N)
    (ht : 0≤ mobiusDivisorQuotientTransverse M N P p*mobiusDivisorQuotientTransverse M N P q) :
    0 ≤ mobiusDivisorPrimePacketOverlap M P p q := by
  let A := mobiusDivisorSelectionFibre N P
  let D := fun R => mobiusDivisorSelectionFibre (N+1) P R-mobiusDivisorSelectionFibre N P R
  have hpoint (r : ℕ) (hr : M/r=N) (R : Finset ℕ) :
      mobiusDivisorPrimePacket M P r R = -Real.sqrt r*(A R+divisorPrimeClipWeight M r*D R) := by
    unfold mobiusDivisorPrimePacket mobiusDivisorInterpolatedFibre
    rw [hr]
    dsimp [A,D]
    ring
  have hg := affineField_inner_nonneg_of_transverse_product (mobiusDivisorSelectionPrimes M).powerset
    A D (divisorPrimeClipWeight M p) (divisorPrimeClipWeight M q) ht
  have he : mobiusDivisorPrimePacketOverlap M P p q = Real.sqrt p*Real.sqrt q*
      (∑ R∈(mobiusDivisorSelectionPrimes M).powerset,
        (A R+divisorPrimeClipWeight M p*D R)*(A R+divisorPrimeClipWeight M q*D R)) := by
    unfold mobiusDivisorPrimePacketOverlap
    rw [mul_sum]
    apply sum_congr rfl
    intro R hR
    rw [hpoint p hp,hpoint q hq]
    ring
  rw [he]
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hg

/-- A complete actual prime-window block with nonnegative pair overlaps admits the sharp two-endpoint order after any processed state. -/
theorem exists_mobiusDivisorAcuteQuotientWindowOrder (M N : ℕ) (P U : Finset ℕ)
    (hU : ∀ p∈U,p.Prime ∧ p<M ∧ p∉P ∧ M/p=N ∧ N+1≤p)
    (hacute : ∀ p∈U,∀ q∈U,0 ≤ mobiusDivisorPrimePacketOverlap M P p q) :
    ∃ l : List ℕ,l.Nodup ∧ l.toFinset=U ∧ ∀ k : ℕ,
      mobiusDivisorSelectionEnergy M (P∪(l.take k).toFinset) ≤
        max (mobiusDivisorSelectionEnergy M P) (mobiusDivisorSelectionEnergy M (P∪U)) := by
  have hinc : ∀ A B : Finset ℕ,A⊆B → B⊆U → ∀ q∈U,q∉B →
      mobiusDivisorSelectionEnergy M (P∪insert q A)-mobiusDivisorSelectionEnergy M (P∪A) ≤
        mobiusDivisorSelectionEnergy M (P∪insert q B)-mobiusDivisorSelectionEnergy M (P∪B) := by
    intro A B hAB hBU q hq hqB
    obtain ⟨hqprime,hqM,hqP,hquot,hlarge⟩ := hU q hq
    have hB : ∀ p∈B,p.Prime ∧ p∉P ∧ M/p=N ∧ N+1≤p := by
      intro p hp
      obtain ⟨h1,h2,h3,h4,h5⟩ := hU p (hBU hp)
      exact ⟨h1,h3,h4,h5⟩
    rw [mobiusDivisorSelectionEnergy_window_marginal M N P A hqprime hqM hqP
        (fun h => hqB (hAB h)) hquot hlarge (fun p hp => hB p (hAB hp)),
      mobiusDivisorSelectionEnergy_window_marginal M N P B hqprime hqM hqP hqB hquot hlarge hB]
    have hs := sum_le_sum_of_subset_of_nonneg hAB (fun p hp _ => hacute p (hBU hp) q hq)
    linarith only [hs]
  simpa only [union_empty] using exists_increasingMarginalSubsetOrder
    (fun L => mobiusDivisorSelectionEnergy M (P∪L)) U hinc

/-- The separating prime part fixed by the actual transverse source sign before choosing an order. -/
def mobiusDivisorQuotientPositivePart (M N : ℕ) (P U : Finset ℕ) : Finset ℕ :=
  U.filter (fun p => 0 ≤ mobiusDivisorQuotientTransverse M N P p)

/-- Every selected quotient subpool has a complete order controlled by its endpoints and the separating part fixed by the source. -/
theorem exists_mobiusDivisorQuotientSubwindowOrder (M N : ℕ) (P U : Finset ℕ)
    (hWindow : U⊆mobiusDivisorQuotientWindowPrimes M N P) :
    ∃ l : List ℕ,l.Nodup ∧ l.toFinset=U ∧
        ∀ k : ℕ,mobiusDivisorSelectionEnergy M (P∪(l.take k).toFinset) ≤
          max (mobiusDivisorSelectionEnergy M P)
            (max (mobiusDivisorSelectionEnergy M (P∪mobiusDivisorQuotientPositivePart M N P U))
              (mobiusDivisorSelectionEnergy M (P∪U))) := by
  let A := mobiusDivisorQuotientPositivePart M N P U
  let B := U\A
  have hU : ∀ p∈U,p.Prime ∧ p<M ∧ p∉P ∧ M/p=N ∧ N+1≤p := by
    intro p hp
    obtain ⟨hbase,hquot,hlarge⟩ := mem_filter.mp (hWindow hp)
    obtain ⟨hactive,hfree⟩ := mem_sdiff.mp hbase
    obtain ⟨hrange,hprime⟩ := mem_filter.mp hactive
    exact ⟨hprime,mem_range.mp hrange,hfree,hquot,hlarge⟩
  have hAU : A⊆U := filter_subset _ _
  have hBU : B⊆U := sdiff_subset
  have hAB : A∪B=U := union_sdiff_of_subset hAU
  have hdis : Disjoint A B := disjoint_left.mpr (fun p hp hq => (mem_sdiff.mp hq).2 hp)
  have hAlarge : ∀ p∈A,N+1≤p := fun p hp => (hU p (hAU hp)).2.2.2.2
  have hAacute : ∀ p∈A,∀ q∈A,0 ≤ mobiusDivisorPrimePacketOverlap M P p q := by
    intro p hp q hq
    apply mobiusDivisorPrimePacketOverlap_nonneg_of_transverse_product M N p q P
      (hU p (hAU hp)).2.2.2.1 (hU q (hAU hq)).2.2.2.1
    exact mul_nonneg (mem_filter.mp hp).2 (mem_filter.mp hq).2
  have hBtrans : ∀ p∈B,mobiusDivisorQuotientTransverse M N P p≤0 := by
    intro p hp
    have hn : ¬0≤ mobiusDivisorQuotientTransverse M N P p := by
      intro h
      exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨hBU hp,h⟩)
    exact (lt_of_not_ge hn).le
  have hB : ∀ p∈B,p.Prime ∧ p<M ∧ p∉P∪A ∧ M/p=N ∧ N+1≤p := by
    intro p hp
    obtain ⟨hprime,hpM,hpP,hquot,hlarge⟩ := hU p (hBU hp)
    exact ⟨hprime,hpM,by simp [hpP,(mem_sdiff.mp hp).2],hquot,hlarge⟩
  have hBacute : ∀ p∈B,∀ q∈B,0 ≤ mobiusDivisorPrimePacketOverlap M (P∪A) p q := by
    intro p hp q hq
    have hqp := (hU p (hBU hp)).2.2.2.1
    have hqq := (hU q (hBU hq)).2.2.2.1
    rw [mobiusDivisorPrimePacketOverlap_union_inactive M N p q P A hqp hqq hAlarge]
    exact mobiusDivisorPrimePacketOverlap_nonneg_of_transverse_product M N p q P hqp hqq
      (mul_nonneg_of_nonpos_of_nonpos (hBtrans p hp) (hBtrans q hq))
  have ha := exists_mobiusDivisorAcuteQuotientWindowOrder M N P A (fun p hp => hU p (hAU hp)) hAacute
  have hb := exists_mobiusDivisorAcuteQuotientWindowOrder M N (P∪A) B hB hBacute
  have hord := exists_twoBlockSubsetOrder (fun L => mobiusDivisorSelectionEnergy M (P∪L)) A B hdis
    (by simpa only [union_empty] using ha) (by simpa only [union_assoc] using hb)
  rw [hAB] at hord
  simpa only [union_empty] using hord

/-- Unconditionally, every complete actual quotient window admits the three-endpoint order after any processed state. -/
theorem exists_mobiusDivisorQuotientWindowOrder (M N : ℕ) (P : Finset ℕ) :
    ∃ l : List ℕ,l.Nodup ∧ l.toFinset=mobiusDivisorQuotientWindowPrimes M N P ∧
        ∀ k : ℕ,mobiusDivisorSelectionEnergy M (P∪(l.take k).toFinset) ≤
          max (mobiusDivisorSelectionEnergy M P)
            (max (mobiusDivisorSelectionEnergy M (P∪mobiusDivisorQuotientPositivePart M N P
                (mobiusDivisorQuotientWindowPrimes M N P)))
              (mobiusDivisorSelectionEnergy M (P∪mobiusDivisorQuotientWindowPrimes M N P))) :=
  exists_mobiusDivisorQuotientSubwindowOrder M N P (mobiusDivisorQuotientWindowPrimes M N P) (Subset.refl _)

end RHTower
