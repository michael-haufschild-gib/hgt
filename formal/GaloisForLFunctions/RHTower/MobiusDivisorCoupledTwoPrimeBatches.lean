import GaloisForLFunctions.RHTower.MobiusDivisorCoupledTwoSourceCone
import GaloisForLFunctions.RHTower.MobiusDivisorQuotientWindowOrder
import GaloisForLFunctions.RHTower.MobiusDivisorPositivePrimeSupply
import GaloisForLFunctions.RHTower.PartialSubsetEnergyOrder
import GaloisForLFunctions.RHTower.MobiusDivisorSignedPrimeBatches

/-!
# Growing coupled prime batches below a quadratic energy ceiling

A fixed core leaves the head and prime-two coordinates available. The literal
source at child cutoffs two, seven and fourteen gives three independent
clipped descent directions. At the common parent scale, macroscopic prime
windows copy them without changing any child field under partial processing.
Their original retained squares pay the receiving squares exactly.

A safe unused prime is therefore available until one direction pool is
exhausted. Finite selection gives a distinct order of length the smallest
pool cardinality, with every prefix below one fixed quadratic ceiling.
The prime-window theorem makes that length tend to infinity. Other source
primes remain unprocessed: this is not an exhaustive order or SD1.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- Complete prime energy change when only the head and prime-two child coordinates survive. -/
theorem mobiusDivisorSelectionEnergy_insert_two_remaining (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpM : p<M) (hpP : p∉P) (hp2 : p≠2) (hM : 2<M)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P) :
    mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P =
      -2*Real.sqrt p*(mobiusDivisorSelectionFibre M P ∅*mobiusDivisorInterpolatedFibre M p P ∅+
        mobiusDivisorSelectionFibre M P {2}*mobiusDivisorInterpolatedFibre M p P {2}) := by
  rw [mobiusDivisorSelectionEnergy_insert_interpolation hp M P hpM hpP]
  congr 1
  have hs : ({∅,{2}}:Finset (Finset ℕ))⊆((mobiusDivisorSelectionPrimes M).erase p).powerset := by
    intro R hR
    simp only [mem_insert,mem_singleton] at hR
    rcases hR with rfl|rfl
    · simp
    · exact mem_powerset.mpr (singleton_subset_iff.mpr (mem_erase.mpr
        ⟨Ne.symm hp2,mem_filter.mpr ⟨mem_range.mpr hM,Nat.prime_two⟩⟩))
  have hsmall : mobiusDivisorSelectionPrimes (M/p)\{2}⊆P := by
    refine Subset.trans ?_ hcore
    intro q hq
    obtain ⟨hq,hq2⟩ := mem_sdiff.mp hq
    obtain ⟨hq,hprime⟩ := mem_filter.mp hq
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hq; omega),hprime⟩,hq2⟩
  have he := sum_subset hs (f := fun R => mobiusDivisorSelectionFibre M P R*mobiusDivisorInterpolatedFibre M p P R) (by
    intro R hR hn
    have hR0 : R≠∅ := by intro he; simp [he] at hn
    have hR2 : R≠{2} := by intro he; simp [he] at hn
    unfold mobiusDivisorInterpolatedFibre
    rw [mobiusDivisorSelectionFibre_one_remaining_zero (M/p) 2 P R hsmall hR0 hR2,
      mobiusDivisorSelectionFibre_one_remaining_zero (M/p+1) 2 P R hcore hR0 hR2]
    ring)
  rw [← he]
  simp

/-- The prepared core and any child-inactive processed primes copy the same literal two-coordinate profile. -/
theorem mobiusDivisorCoupledTwo_interpolation_union (M K p : ℕ) (L : Finset ℕ)
    (hquot : M/p=K) (hL : ∀ q∈L,K+1≤q) :
    (mobiusDivisorInterpolatedFibre M p (mobiusDivisorCoupledTwoCore∪L) ∅,
      mobiusDivisorInterpolatedFibre M p (mobiusDivisorCoupledTwoCore∪L) {2}) =
      mobiusDivisorCoupledTwoInterpolatedProfile K (divisorPrimeClipWeight M p) := by
  have hlow : ∀ q∈L,K≤q := fun q hq => by have := hL q hq; omega
  have point (R : Finset ℕ) :
      mobiusDivisorInterpolatedFibre M p (mobiusDivisorCoupledTwoCore∪L) R=
        mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore R+divisorPrimeClipWeight M p*
          (mobiusDivisorSelectionFibre (K+1) mobiusDivisorCoupledTwoCore R-
            mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore R) := by
    rw [mobiusDivisorInterpolatedFibre,hquot,
      mobiusDivisorSelectionFibre_union_inactive K _ L _ hlow,
      mobiusDivisorSelectionFibre_union_inactive (K+1) _ L _ hL]
    ring
  exact Prod.ext (point ∅) (point {2})

/-- The literal three-profile source guarantees a nonincreasing full-energy step after any child-inactive selection. -/
theorem exists_mobiusDivisorCoupledTwo_prime_energy_descent :
    ∃ ε : ℝ,0<ε ∧ ∀ (M : ℕ) (L : Finset ℕ),2<M → (∀ q∈L,15≤q) →
      ∀ p q r : ℕ,
      (p.Prime ∧ p<M ∧ 15≤p ∧ p∉L ∧ M/p=2 ∧ divisorPrimeClipWeight M p≤ε) →
      (q.Prime ∧ q<M ∧ 15≤q ∧ q∉L ∧ M/q=7 ∧ divisorPrimeClipWeight M q≤ε) →
      (r.Prime ∧ r<M ∧ 15≤r ∧ r∉L ∧ M/r=14 ∧ divisorPrimeClipWeight M r≤ε) →
      ∃ t∈({p,q,r}:Finset ℕ),
        mobiusDivisorSelectionEnergy M (insert t (mobiusDivisorCoupledTwoCore∪L))≤
          mobiusDivisorSelectionEnergy M (mobiusDivisorCoupledTwoCore∪L) := by
  obtain ⟨ε,c,hε,hc,hmargin⟩ := exists_mobiusDivisorCoupledTwo_clip_margin
  refine ⟨ε,hε,?_⟩
  intro M L hM hL p q r hp hq hr
  let P := mobiusDivisorCoupledTwoCore∪L
  let z : ℝ × ℝ := (mobiusDivisorSelectionFibre M P ∅,mobiusDivisorSelectionFibre M P {2})
  have step (t K : ℕ) (ht : t.Prime ∧ t<M ∧ 15≤t ∧ t∉L ∧ M/t=K)
      (hK : K≤14)
      (hdot : 0≤z.1*(mobiusDivisorCoupledTwoInterpolatedProfile K (divisorPrimeClipWeight M t)).1+
        z.2*(mobiusDivisorCoupledTwoInterpolatedProfile K (divisorPrimeClipWeight M t)).2) :
      mobiusDivisorSelectionEnergy M (insert t P) ≤ mobiusDivisorSelectionEnergy M P := by
    obtain ⟨ht,htM,ht15,htL,hquot⟩ := ht
    have htP : t∉P := by
      intro h
      rcases mem_union.mp h with h|h
      · have hlt := mem_range.mp (mem_filter.mp (mem_erase.mp h).2).1
        omega
      · exact htL h
    have hcore : mobiusDivisorSelectionPrimes (M/t+1)\{2}⊆P :=
      (mobiusDivisorCoupledTwoCore_covers (by omega)).trans subset_union_left
    have he := mobiusDivisorSelectionEnergy_insert_two_remaining M P ht htM htP (by omega) hM hcore
    have hi := mobiusDivisorCoupledTwo_interpolation_union M K t L hquot
      (fun a ha => by have := hL a ha; omega)
    have hi0 := congrArg Prod.fst hi
    have hi2 := congrArg Prod.snd hi
    change mobiusDivisorInterpolatedFibre M t P ∅=_ at hi0
    change mobiusDivisorInterpolatedFibre M t P {2}=_ at hi2
    rw [hi0,hi2] at he
    have hn := mul_nonpos_of_nonpos_of_nonneg
      (show -2*Real.sqrt t≤0 by have := Real.sqrt_nonneg (t:ℝ); linarith) hdot
    change 0 ≤ mobiusDivisorSelectionFibre M P ∅*_+mobiusDivisorSelectionFibre M P {2}*_ at hdot
    dsimp only [z] at hn
    linarith only [he,hn]
  have hm := hmargin (divisorPrimeClipWeight M p) (divisorPrimeClipWeight M q)
    (divisorPrimeClipWeight M r) (divisorPrimeClipWeight_nonneg M p hp.1.pos) hp.2.2.2.2.2
    (divisorPrimeClipWeight_nonneg M q hq.1.pos) hq.2.2.2.2.2
    (divisorPrimeClipWeight_nonneg M r hr.1.pos) hr.2.2.2.2.2 z
  have hn := (mul_nonneg hc.le (norm_nonneg z)).trans hm
  rcases le_max_iff.mp hn with hn|hn
  · exact ⟨p,by simp,step p 2 ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1⟩ (by norm_num) hn⟩
  · rcases le_max_iff.mp hn with hn|hn
    · exact ⟨q,by simp,step q 7 ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2.1⟩ (by norm_num) hn⟩
    · exact ⟨r,by simp,step r 14 ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1⟩ (by norm_num) hn⟩


/-- A fixed multiplicative prime window has its prescribed child quotient. -/
theorem natDiv_fixed_quotient_window {K b N p : ℕ} (hb : K≤b)
    (hlo : b*N<p) (hhi : p≤(b+1)*N) : (K*(b+1)*N)/p=K := by
  have hp : 0<p := by omega
  have hlow : K≤(K*(b+1)*N)/p :=
    (Nat.le_div_iff_mul_le hp).mpr (by
      have h := Nat.mul_le_mul_left K hhi
      nlinarith only [h])
  have hhigh : (K*(b+1)*N)/p<K+1 :=
    (Nat.div_lt_iff_lt_mul hp).mpr (by
      have h₀ : K*(b+1)≤(K+1)*b := by nlinarith only [hb]
      have h₁ := Nat.mul_le_mul_right N h₀
      have h₂ := Nat.mul_lt_mul_of_pos_left hlo (show 0<K+1 by omega)
      nlinarith only [h₁,h₂])
  omega

/-- A uniform analytic clipping estimate for each child cutoff from one through fourteen. -/
theorem divisorPrimeClipWeight_small_quotient_window {K b N p : ℕ}
    (hK : 1≤K) (hK14 : K≤14) (hb : K≤b)
    (hlo : b*N<p) (hhi : p≤(b+1)*N) :
    (b:ℝ)*divisorPrimeClipWeight (K*(b+1)*N) p≤140 := by
  have hp : 0<p := by omega
  have hN : 0<N := by nlinarith
  have hquot := natDiv_fixed_quotient_window hb hlo hhi
  have hw := divisorPrimeClipWeight_nonneg (K*(b+1)*N) p hp
  have hstep := divisorPrimeClipWeight_mul_step (K*(b+1)*N) p hp
  rw [hquot] at hstep
  have hgap : (1/10:ℝ)≤Real.sqrt (K+1:ℕ)-Real.sqrt K := by
    push_cast
    have ha := Real.sq_sqrt (show 0≤(K:ℝ)+1 by positivity)
    have hb' := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) K)
    have hkr : (K:ℝ)≤14 := by exact_mod_cast hK14
    have hdiff : 0≤Real.sqrt ((K:ℝ)+1)-Real.sqrt K :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hsum : Real.sqrt ((K:ℝ)+1)+Real.sqrt K≤8 := by
      have h₀ : Real.sqrt ((K:ℝ)+1)≤4 := by nlinarith [sq_nonneg (Real.sqrt ((K:ℝ)+1)-4)]
      have h₁ : Real.sqrt (K:ℝ)≤4 := by nlinarith [sq_nonneg (Real.sqrt (K:ℝ)-4)]
      linarith
    have hm := mul_nonneg (sub_nonneg.mpr hsum) hdiff
    nlinarith only [ha,hb',hm]
  have hroot : Real.sqrt (p:ℝ)≤Real.sqrt (p*K:ℕ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show p≤p*K by simpa using Nat.mul_le_mul_left p hK)
  have hdiff : 0≤Real.sqrt (K*(b+1)*N:ℕ)-Real.sqrt (p*K:ℕ) := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show p*K≤K*(b+1)*N by
      have h := Nat.mul_le_mul_left K hhi; nlinarith only [h])
  have hsM := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (K*(b+1)*N))
  have hsK := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (p*K))
  have hsp := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have hmul := mul_le_mul_of_nonneg_left
    (show Real.sqrt p≤Real.sqrt (K*(b+1)*N:ℕ)+Real.sqrt (p*K:ℕ) by
      linarith only [hroot,Real.sqrt_nonneg ((K*(b+1)*N:ℕ):ℝ)]) hdiff
  have hNat : ((K*(b+1)*N:ℕ):ℝ)≤(p*K:ℕ)+(K:ℝ)*N := by
    exact_mod_cast (show K*(b+1)*N≤p*K+K*N by
      have h := Nat.mul_le_mul_left K hlo.le; nlinarith only [h])
  have hbound : (Real.sqrt (K*(b+1)*N:ℕ)-Real.sqrt (p*K:ℕ))*Real.sqrt p≤(K:ℝ)*N := by
    nlinarith only [hmul,hsM,hsK,hNat]
  have he := congrArg (fun x : ℝ => x*Real.sqrt p) hstep
  have he' : divisorPrimeClipWeight (K*(b+1)*N) p*(p:ℝ)*
      (Real.sqrt (K+1:ℕ)-Real.sqrt K)≤(K:ℝ)*N := by
    calc
      _ = divisorPrimeClipWeight (K*(b+1)*N) p*(Real.sqrt p)^2*
          (Real.sqrt (K+1:ℕ)-Real.sqrt K) := by rw [hsp]
      _ = divisorPrimeClipWeight (K*(b+1)*N) p*Real.sqrt p*
          (Real.sqrt (K+1:ℕ)-Real.sqrt K)*Real.sqrt p := by ring
      _ = _ := he
      _ ≤ _ := hbound
  have h10 := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg hw (Nat.cast_nonneg (α := ℝ) p))
  have hbn : (b:ℝ)*N≤p := by exact_mod_cast hlo.le
  have hbmul := mul_le_mul_of_nonneg_left hbn hw
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hkr : (K:ℝ)≤14 := by exact_mod_cast hK14
  have hKN := mul_le_mul_of_nonneg_right hkr hNr.le
  nlinarith only [he',h10,hbmul,hNr,hKN]

/-- Every fixed nontrivial integer prime window eventually supplies any prescribed finite number of primes. -/
theorem eventually_fixed_prime_window_card_ge (b n : ℕ) (hb : 1≤b) :
    ∀ᶠ N : ℕ in atTop,n≤(GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N)).card := by
  have hbR : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hratio : (1:ℝ)<((b:ℝ)+1)/b := by rw [lt_div_iff₀ hbR]; linarith
  have hcast : Tendsto (fun N : ℕ => (b:ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hbR
  have hc := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge hratio)
  filter_upwards [hc,eventually_ge_atTop (max 2 ((4*b*n)^2))] with N hc hN
  have harg : (((b:ℝ)+1)/b)*((b:ℝ)*N)=((b+1)*N:ℕ) := by push_cast; field_simp
  have hbN : (b:ℝ)*N=(b*N:ℕ) := by push_cast; rfl
  rw [harg,hbN,Nat.floor_natCast,Nat.floor_natCast,
    ← GaloisForLFunctions.HTGeometry.card_primesInIoc (show b*N≤(b+1)*N by nlinarith)] at hc
  have hr : (((b:ℝ)+1)/b-1)/2=1/(2*b) := by field_simp; ring
  rw [hr] at hc
  have hx1 : (1:ℝ)<(b*N:ℕ) := by exact_mod_cast (show 1<b*N by have := le_max_left 2 ((4*b*n)^2); nlinarith)
  have hx0 : (0:ℝ)<(b*N:ℕ) := by linarith only [hx1]
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
  rw [Real.log_sqrt hx0.le] at hl
  have hs := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg ((b*N:ℕ):ℝ)
  have hd : Real.sqrt (b*N:ℕ)/2≤((b*N:ℕ):ℝ)/Real.log (b*N:ℕ) := by
    rw [le_div_iff₀ (Real.log_pos hx1)]
    have hm := mul_le_mul_of_nonneg_left hl hs0
    nlinarith only [hm,hs,hs0]
  have hroot : 4*(b:ℝ)*n≤Real.sqrt (b*N:ℕ) := by
    have hn : (4*(b:ℝ)*n)^2≤(b*N:ℕ) := by
      exact_mod_cast (show (4*b*n)^2≤b*N by
        have := le_max_right 2 ((4*b*n)^2); nlinarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hnn : (n:ℝ)≤(GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N)).card := calc
    _ = (1/(2*(b:ℝ)))*(4*b*n/2) := by field_simp; ring
    _ ≤ (1/(2*(b:ℝ)))*(Real.sqrt (b*N:ℕ)/2) := by gcongr
    _ ≤ (1/(2*(b:ℝ)))*(((b*N:ℕ):ℝ)/Real.log (b*N:ℕ)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ _ := hc
  exact_mod_cast hnn


/-- One actual prime pool carrying a fixed child quotient at the common parent scale. -/
def mobiusDivisorCoupledTwoWindow (b N K : ℕ) : Finset ℕ :=
  GaloisForLFunctions.HTGeometry.primesInIoc (b*((14/K)*N)) ((b+1)*((14/K)*N))

/-- The three coupled source pools at one parent cutoff. -/
def mobiusDivisorCoupledTwoPool (b N : ℕ) : Finset ℕ :=
  mobiusDivisorCoupledTwoWindow b N 2∪
    (mobiusDivisorCoupledTwoWindow b N 7∪mobiusDivisorCoupledTwoWindow b N 14)

/-- Number of safe steps guaranteed before any one source-direction pool can be exhausted. -/
def mobiusDivisorCoupledTwoCapacity (b N : ℕ) : ℕ :=
  min (mobiusDivisorCoupledTwoWindow b N 2).card
    (min (mobiusDivisorCoupledTwoWindow b N 7).card (mobiusDivisorCoupledTwoWindow b N 14).card)

private theorem window_data {b N K p : ℕ} (hb : 15≤b) (hN : 1≤N)
    (hK : K∈({2,7,14}:Finset ℕ)) (hp : p∈mobiusDivisorCoupledTwoWindow b N K) :
    p.Prime ∧ p<14*(b+1)*N ∧ 15≤p ∧ (14*(b+1)*N)/p=K ∧
      (b:ℝ)*divisorPrimeClipWeight (14*(b+1)*N) p≤140 := by
  obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have hk : K≤14 ∧ 1≤K ∧ 1≤14/K ∧ K*(14/K)=14 := by
    simp only [mem_insert,mem_singleton] at hK
    rcases hK with rfl|rfl|rfl <;> norm_num
  have he : K*(b+1)*((14/K)*N)=14*(b+1)*N := by
    calc
      _ = (K*(14/K))*((b+1)*N) := by ring
      _ = _ := by rw [hk.2.2.2]; ring
  have hquot := natDiv_fixed_quotient_window (show K≤b by omega) hlo hhi
  have hw := divisorPrimeClipWeight_small_quotient_window hk.2.1 hk.1 (show K≤b by omega) hlo hhi
  rw [he] at hquot hw
  refine ⟨hpp,?_,?_,hquot,hw⟩
  · have hK2 : 2≤K := by
      simp only [mem_insert,mem_singleton] at hK
      rcases hK with rfl|rfl|rfl <;> omega
    have hpM : K*p≤14*(b+1)*N := by nlinarith [hhi,he]
    nlinarith [hpp.pos]
  · nlinarith [hk.2.2.1]

private theorem prepared_core_energy (M : ℕ) (hM : 15≤M) :
    mobiusDivisorSelectionEnergy M mobiusDivisorCoupledTwoCore≤(2:ℝ)^15*722*(M:ℝ)^2 := by
  have hprimes : ∀ p∈mobiusDivisorCoupledTwoCore,p.Prime ∧ p<M := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp (mem_erase.mp hp).2
    exact ⟨hprime,(mem_range.mp hp).trans_le hM⟩
  have he := mobiusDivisorSelectionEnergy_le_pow_card M mobiusDivisorCoupledTwoCore hprimes
  have hc : mobiusDivisorCoupledTwoCore.card≤15 := by
    apply (card_le_card (erase_subset 2 (mobiusDivisorSelectionPrimes 15))).trans
    simpa only [mobiusDivisorSelectionPrimes,card_range] using
      (card_filter_le (s := range 15) (p := Nat.Prime))
  have hpow : (2:ℝ)^mobiusDivisorCoupledTwoCore.card≤2^15 := by gcongr; norm_num
  have hdiag := sum_mobiusDivisorDilationChannel_sq_le_quadratic M
  rw [mobiusDivisorSelectionEnergy_empty] at he
  have hmult := mul_le_mul_of_nonneg_left hdiag (by positivity : (0:ℝ)≤2^mobiusDivisorCoupledTwoCore.card)
  have hlast := mul_le_mul_of_nonneg_right hpow (by positivity : (0:ℝ)≤722*(M:ℝ)^2)
  exact he.trans (hmult.trans (by nlinarith only [hlast]))

/-- One fixed set of source windows supplies arbitrarily long coupled batches under a uniform quadratic prefix ceiling. -/
theorem exists_mobiusDivisorCoupledTwo_bounded_batches :
    ∃ b : ℕ,15≤b ∧ ∀ N : ℕ,1≤N →
      ∃ l : List ℕ,l.Nodup ∧ l.length=mobiusDivisorCoupledTwoCapacity b N ∧
        l.toFinset⊆mobiusDivisorCoupledTwoPool b N ∧ ∀ k : ℕ,
        mobiusDivisorSelectionEnergy (14*(b+1)*N)
          (mobiusDivisorCoupledTwoCore∪(l.take k).toFinset)≤
          (2:ℝ)^15*722*(14*(b+1)*N:ℕ)^2 := by
  obtain ⟨ε,hε,hdescent⟩ := exists_mobiusDivisorCoupledTwo_prime_energy_descent
  obtain ⟨b,hbε⟩ := exists_nat_gt (140/ε)
  let B := max 15 b
  have hB : 15≤B := le_max_left _ _
  have hBε : 140≤(B:ℝ)*ε := by
    have hbb : (b:ℝ)≤B := by exact_mod_cast (le_max_right 15 b)
    have hm := (div_lt_iff₀ hε).mp hbε
    nlinarith
  refine ⟨B,hB,?_⟩
  intro N hN
  let M := 14*(B+1)*N
  let U := mobiusDivisorCoupledTwoPool B N
  let n := mobiusDivisorCoupledTwoCapacity B N
  have hM : 15≤M := by dsimp [M]; nlinarith
  have hU (p : ℕ) (hp : p∈U) : p.Prime ∧ p<M ∧ 15≤p := by
    rcases mem_union.mp hp with hp|hp
    · exact (window_data hB hN (by simp) hp).imp_right (fun h => ⟨h.1,h.2.1⟩)
    · rcases mem_union.mp hp with hp|hp
      · exact (window_data hB hN (by simp) hp).imp_right (fun h => ⟨h.1,h.2.1⟩)
      · exact (window_data hB hN (by simp) hp).imp_right (fun h => ⟨h.1,h.2.1⟩)
  obtain ⟨l,hnd,hlen,hsub,hbound⟩ := exists_partialSubsetEnergyOrder
    (fun L => mobiusDivisorSelectionEnergy M (mobiusDivisorCoupledTwoCore∪L)) U n (by
      intro L hLU hcard
      have choose (W : Finset ℕ) (hn : n≤W.card) : ∃ p∈W,p∉L := by
        by_contra hh
        push Not at hh
        have hh' := card_le_card hh
        omega
      obtain ⟨p,hp,hpL⟩ := choose (mobiusDivisorCoupledTwoWindow B N 2) (min_le_left _ _)
      obtain ⟨q,hq,hqL⟩ := choose (mobiusDivisorCoupledTwoWindow B N 7) ((min_le_right _ _).trans (min_le_left _ _))
      obtain ⟨r,hr,hrL⟩ := choose (mobiusDivisorCoupledTwoWindow B N 14) ((min_le_right _ _).trans (min_le_right _ _))
      have data (t K : ℕ) (ht : t∈mobiusDivisorCoupledTwoWindow B N K) (htL : t∉L)
          (hK : K∈({2,7,14}:Finset ℕ)) :
          t.Prime ∧ t<M ∧ 15≤t ∧ t∉L ∧ M/t=K ∧ divisorPrimeClipWeight M t≤ε := by
        obtain ⟨ht,htM,ht15,hquot,hw⟩ := window_data hB hN hK ht
        refine ⟨ht,htM,ht15,htL,hquot,?_⟩
        have hBr : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
        change divisorPrimeClipWeight (14*(B+1)*N) t≤ε
        nlinarith
      obtain ⟨t,ht,hsafe⟩ := hdescent M L (by omega) (fun a ha => (hU a (hLU ha)).2.2) p q r
        (data p 2 hp hpL (by simp)) (data q 7 hq hqL (by simp)) (data r 14 hr hrL (by simp))
      simp only [mem_insert,mem_singleton] at ht
      have hpU : p∈U := mem_union_left _ hp
      have hqU : q∈U := mem_union_right _ (mem_union_left _ hq)
      have hrU : r∈U := mem_union_right _ (mem_union_right _ hr)
      rcases ht with rfl|rfl|rfl
      · exact ⟨t,hpU,hpL,by simpa only [union_insert] using hsafe⟩
      · exact ⟨t,hqU,hqL,by simpa only [union_insert] using hsafe⟩
      · exact ⟨t,hrU,hrL,by simpa only [union_insert] using hsafe⟩)
  refine ⟨l,hnd,hlen,hsub,?_⟩
  intro k
  exact (hbound k).trans (by simpa only [union_empty] using prepared_core_energy M hM)

/-- The guaranteed coupled-batch capacity grows beyond every fixed finite length. -/
theorem eventually_mobiusDivisorCoupledTwoCapacity_ge (b n : ℕ) (hb : 1≤b) :
    ∀ᶠ N : ℕ in atTop,n ≤ mobiusDivisorCoupledTwoCapacity b N := by
  have hbase := eventually_fixed_prime_window_card_ge b n hb
  have h7 : ∀ᶠ N : ℕ in atTop,n≤(mobiusDivisorCoupledTwoWindow b N 2).card := by
    have ht : Tendsto (fun N : ℕ => 7*N) atTop atTop :=
      Filter.Tendsto.const_mul_atTop' (by norm_num : (0:ℕ)<7) tendsto_id
    simpa only [mobiusDivisorCoupledTwoWindow,Nat.reduceDiv] using ht.eventually hbase
  have h2 : ∀ᶠ N : ℕ in atTop,n≤(mobiusDivisorCoupledTwoWindow b N 7).card := by
    have ht : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
      Filter.Tendsto.const_mul_atTop' (by norm_num : (0:ℕ)<2) tendsto_id
    simpa only [mobiusDivisorCoupledTwoWindow,Nat.reduceDiv] using ht.eventually hbase
  filter_upwards [h7,h2,hbase] with N h7 h2 h1
  exact le_min h7 (le_min h2 (by simpa only [mobiusDivisorCoupledTwoWindow,Nat.reduceDiv,one_mul] using h1))

end RHTower
