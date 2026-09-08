import GaloisForLFunctions.RHTower.MobiusDivisorRemainingFrontTransport

import GaloisForLFunctions.RHTower.MobiusDivisorApproximateTwoReserve
import GaloisForLFunctions.RHTower.BoundedPlaneDisplacementBatch
import GaloisForLFunctions.RHTower.MobiusDivisorSquareRootWindowCapacity
import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport

/-! # Prescribed-prime repair from actual source windows -/
noncomputable section
open Finset Filter Topology
namespace RHTower

/-- The two retained child coordinates normalized at the physical square-root scale. -/
def mobiusDivisorTwoPlanePacket (M p : ℕ) (P : Finset ℕ) : ℝ × ℝ :=
  (Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅/Real.sqrt M,
   Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}/Real.sqrt M)

/-- Every available quotient-at-most-fourteen packet has a uniform product-norm bound. -/
theorem norm_mobiusDivisorTwoPlanePacket_le_nine {M p : ℕ} (P : Finset ℕ) (hM : 2< M)
    (hp : p.Prime) (hpP : p∉P) (hp2 : p≠2) (hquot : M/p≤ 14) : ‖mobiusDivisorTwoPlanePacket M p P‖≤ 9 := by
  have hr : 0< Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0< M by omega))
  have hcoord (R : Finset ℕ) (hR : R⊆(mobiusDivisorSelectionPrimes M).erase p) :
      |Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R/Real.sqrt M|≤ 9 := by
    have hpR : p∉R := fun h => (mem_erase.mp (hR h)).1 rfl
    have hs := (single_le_sum (fun S (_ : S∈((mobiusDivisorSelectionPrimes M).erase p).powerset) =>
      abs_nonneg (mobiusDivisorSelectionFibre M P (insert p S))) (mem_powerset.mpr hR)).trans
        (sum_abs_mobiusDivisorPrimeFibre_le_quotient M P hp)
    rw [mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP hpR,neg_mul,abs_neg] at hs
    rw [abs_div,abs_of_pos hr,div_le_iff₀ hr]
    have hq : ((M/p:ℕ):ℝ)≤ 14 := by exact_mod_cast hquot
    nlinarith only [hs,hq,hr]
  rw [Prod.norm_def]
  apply max_le
  · simpa only [mobiusDivisorTwoPlanePacket,Real.norm_eq_abs] using hcoord ∅ (empty_subset _)
  · simpa only [mobiusDivisorTwoPlanePacket,Real.norm_eq_abs] using hcoord {2} (singleton_subset_iff.mpr
      (mem_erase.mpr ⟨Ne.symm hp2,mem_filter.mpr ⟨mem_range.mpr hM,Nat.prime_two⟩⟩))

private lemma core_profile {M p : ℕ} (P : Finset ℕ)
    (hP : mobiusDivisorCoupledTwoCore⊆P) (h2 : 2∉P) (hquot : M/p≤ 14) :
    (mobiusDivisorInterpolatedFibre M p P ∅,mobiusDivisorInterpolatedFibre M p P {2})=
      mobiusDivisorCoupledTwoInterpolatedProfile (M/p) (divisorPrimeClipWeight M p) := by
  have hf (K : ℕ) (hK : K≤ 15) :
      mobiusDivisorSelectionFibre K P ∅=mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore ∅ ∧
      mobiusDivisorSelectionFibre K P {2}=mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore {2} := by
    have ha := mobiusDivisorSelectionFibre_one_remaining K 2 P Nat.prime_two h2
      ((mobiusDivisorCoupledTwoCore_covers hK).trans hP)
    have hb := mobiusDivisorSelectionFibre_one_remaining K 2 mobiusDivisorCoupledTwoCore Nat.prime_two
      (by simp [mobiusDivisorCoupledTwoCore]) (mobiusDivisorCoupledTwoCore_covers hK)
    exact ⟨ha.1.trans hb.1.symm,ha.2.trans hb.2.symm⟩
  obtain ⟨h0,h1⟩ := hf (M/p) (by omega)
  obtain ⟨h0',h1'⟩ := hf (M/p+1) (by omega)
  apply Prod.ext
  all_goals dsimp [mobiusDivisorInterpolatedFibre,mobiusDivisorCoupledTwoInterpolatedProfile,
    mobiusDivisorCoupledTwoProfile]
  · rw [h0,h0']; ring
  · rw [h1,h1']; ring

private lemma window_data {b N K p : ℕ} (hb : 15≤ b) (hN : 1≤ N)
    (hK : K∈({2,7,14}:Finset ℕ)) (hp : p∈mobiusDivisorCoupledTwoWindow b N K) :
    p.Prime ∧ p<14*(b+1)*N ∧ 15≤ p ∧ (14*(b+1)*N)/p=K ∧
      (b:ℝ)*divisorPrimeClipWeight (14*(b+1)*N) p≤ 420 := by
  have hk : 2≤ K ∧ K≤ 14 ∧ K∣14 ∧ 2*(K:ℝ)*(K+1)≤ 420 := by
    simp only [mem_insert,mem_singleton] at hK
    rcases hK with rfl|rfl|rfl <;> norm_num
  obtain ⟨hpr,hM,hb',hquot,hclip⟩ := retainedPrimeWitnessWindow_data hk.1 (by omega)
    (by norm_num : 0<14) hk.2.2.1 hN hp
  exact ⟨hpr,hM,by omega,hquot,hclip.trans hk.2.2.2⟩

private lemma window_subset_pool (b N K : ℕ) (hK : K∈({2,7,14}:Finset ℕ)) :
    mobiusDivisorCoupledTwoWindow b N K⊆mobiusDivisorCoupledTwoPool b N := by
  simp only [mem_insert,mem_singleton] at hK
  rcases hK with rfl|rfl|rfl
  · exact subset_union_left
  · exact subset_trans subset_union_left subset_union_right
  · exact subset_trans subset_union_right subset_union_right

/-- Every actual reserve-window prime retains its exact quotient and clipping bound. -/
theorem mobiusDivisorCoupledTwoPool_data {b N p : ℕ} (hb : 15≤ b) (hN : 1≤ N)
    (hp : p∈mobiusDivisorCoupledTwoPool b N) :
    ∃ K∈({2,7,14}:Finset ℕ),p∈mobiusDivisorCoupledTwoWindow b N K ∧
      p.Prime ∧ p<14*(b+1)*N ∧ 15≤ p ∧ (14*(b+1)*N)/p=K ∧
        (b:ℝ)*divisorPrimeClipWeight (14*(b+1)*N) p≤ 420 := by
  rcases mem_union.mp hp with hp|hp
  · exact ⟨2,by simp,hp,window_data hb hN (by simp) hp⟩
  · rcases mem_union.mp hp with hp|hp
    · exact ⟨7,by simp,hp,window_data hb hN (by simp) hp⟩
    · exact ⟨14,by simp,hp,window_data hb hN (by simp) hp⟩

private lemma packet_scale_lower {M p : ℕ} (hM : 0< M) (hp : 0< p) (hq : M/p≤ 14) :
    (1/4:ℝ)≤ Real.sqrt p/Real.sqrt M ∧ (M:ℝ)≤ 16*(p:ℝ) := by
  have hm : M<15*p := (Nat.div_lt_iff_lt_mul hp).mp (by omega : M/p<15)
  have hmR : (M:ℝ)≤ 16*(p:ℝ) := by exact_mod_cast (show M≤ 16*p by omega)
  have hrM : 0< Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  have hrp := Real.sqrt_nonneg (p:ℝ)
  have hsM := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)
  have hsp := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
  constructor
  · rw [le_div_iff₀ hrM]
    nlinarith only [hmR,hsM,hsp,hrM,hrp]
  · exact hmR

/-- Actual source windows supply a common inward margin, two positive square reserves,
and fresh directions after any depletion smaller than their minimum cardinality. -/
theorem exists_mobiusDivisorTwoPlaneWindowGeometry :
    ∃ b : ℕ,∃ c d : ℝ,15≤ b ∧ 0< c ∧ 0< d ∧
    ∀ N : ℕ,1≤ N → ∀ P : Finset ℕ,mobiusDivisorCoupledTwoCore⊆P → 2∉P →
      (∀ p∈mobiusDivisorCoupledTwoPool b N,p∉P) →
      let M := 14*(b+1)*N
      (∀ p∈mobiusDivisorCoupledTwoPool b N,‖mobiusDivisorTwoPlanePacket M p P‖≤ 9) ∧
      (∀ p∈mobiusDivisorCoupledTwoPool b N,
        d*(M:ℝ)≤ (p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+(mobiusDivisorInterpolatedFibre M p P {2})^2) ∧
        d*(M:ℝ)≤ (p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^2) ∧
      ∀ q : ℕ,∀ L : Finset ℕ,L.card< mobiusDivisorCoupledTwoCapacity b N-1 → ∀ z : ℝ × ℝ,
        ∃ p∈(mobiusDivisorCoupledTwoPool b N).erase q,p∉L ∧
          z.1*(mobiusDivisorTwoPlanePacket M p P).1+z.2*(mobiusDivisorTwoPlanePacket M p P).2≤ -c*‖z‖ := by
  obtain ⟨ε₁,c,hε₁,hc,hmargin⟩ := exists_mobiusDivisorCoupledTwo_clip_margin
  obtain ⟨ε₂,d,hε₂,hd,hreserve⟩ := exists_mobiusDivisorCoupledTwo_clip_square_reserve
  let ε := min ε₁ ε₂
  have hε : 0<ε := lt_min hε₁ hε₂
  obtain ⟨a,ha⟩ := exists_nat_gt (420/ε)
  let b := max 15 a
  have hb : 15≤ b := le_max_left _ _
  have hbR : (0:ℝ)< b := by exact_mod_cast (show 0< b by omega)
  have hclipb : (420:ℝ)≤ (b:ℝ)*ε := by
    have hab : (a:ℝ)≤ b := by exact_mod_cast (le_max_right 15 a)
    have h := (div_lt_iff₀ hε).mp ha
    nlinarith only [h,hab,hε]
  refine ⟨b,c/4,d/16,hb,by positivity,by positivity,?_⟩
  intro N hN P hP h2 hfresh
  let M := 14*(b+1)*N
  have hM : 2< M := by dsimp only [M]; nlinarith
  have window (K p : ℕ) (hK : K∈({2,7,14}:Finset ℕ))
      (hp : p∈mobiusDivisorCoupledTwoWindow b N K) :
      p.Prime ∧ p< M ∧ 15≤ p ∧ M/p=K ∧ 0≤ divisorPrimeClipWeight M p ∧ divisorPrimeClipWeight M p≤ ε := by
    obtain ⟨hpp,hpM,h15,hq,hclip⟩ := window_data hb hN hK hp
    exact ⟨hpp,hpM,h15,hq,divisorPrimeClipWeight_nonneg M p hpp.pos,
      (by nlinarith only [hclip,hclipb,hbR])⟩
  have pdata (p : ℕ) (hp : p∈mobiusDivisorCoupledTwoPool b N) : p.Prime ∧ p< M ∧ 15≤ p ∧ M/p≤ 14 := by
    obtain ⟨K,hK,_,hpr,hpM,h15,hq,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN hp
    have hk : K≤ 14 := by simp only [mem_insert,mem_singleton] at hK; rcases hK with rfl|rfl|rfl <;> omega
    exact ⟨hpr,hpM,h15,by change (14*(b+1)*N)/p≤14; omega⟩
  refine ⟨?_,?_,?_⟩
  · intro p hp
    obtain ⟨hpr,_,h15,hq⟩ := pdata p hp
    exact norm_mobiusDivisorTwoPlanePacket_le_nine P hM hpr (hfresh p hp) (by omega) hq
  · intro p hp
    obtain ⟨K,hK,hpK,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN hp
    obtain ⟨hpr,_,h15,hq,hw0,hw⟩ := window K p hK hpK
    have hk : M/p≤ 14 := by rw [hq]; simp only [mem_insert,mem_singleton] at hK; rcases hK with rfl|rfl|rfl <;> omega
    have hv := hreserve K hK (divisorPrimeClipWeight M p)
      (by rw [abs_of_nonneg hw0]; exact hw.trans (min_le_right _ _))
    have he := core_profile P hP h2 hk
    rw [hq] at he
    rw [← he] at hv
    have hm := (packet_scale_lower (by omega : 0< M) hpr.pos hk).2
    have h0 := mul_le_mul_of_nonneg_left hv.1 (Nat.cast_nonneg (α:=ℝ) p)
    have h1 := mul_le_mul_of_nonneg_left hv.2 (Nat.cast_nonneg (α:=ℝ) p)
    constructor <;> dsimp only at h0 h1 ⊢ <;> nlinarith only [h0,h1,hm,hd]
  · intro q L hL z
    have choose (W : Finset ℕ) (hW : mobiusDivisorCoupledTwoCapacity b N≤ W.card) :
        ∃ p∈W,p∉insert q L := by
      by_contra hn
      push Not at hn
      have hsub : W⊆insert q L := hn
      have hcard := card_le_card hsub
      have hi : (insert q L).card≤ L.card+1 := by by_cases h : q∈L <;> simp [h]
      omega
    obtain ⟨p,hp,hpL⟩ := choose (mobiusDivisorCoupledTwoWindow b N 2) (min_le_left _ _)
    obtain ⟨r,hr,hrL⟩ := choose (mobiusDivisorCoupledTwoWindow b N 7) ((min_le_right _ _).trans (min_le_left _ _))
    obtain ⟨s,hs,hsL⟩ := choose (mobiusDivisorCoupledTwoWindow b N 14) ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hpp,_,_,hpq,hp0,hpε⟩ := window 2 p (by simp) hp
    obtain ⟨hrp,_,_,hrq,hr0,hrε⟩ := window 7 r (by simp) hr
    obtain ⟨hsp,_,_,hsq,hs0,hsε⟩ := window 14 s (by simp) hs
    have hm := hmargin (divisorPrimeClipWeight M p) (divisorPrimeClipWeight M r) (divisorPrimeClipWeight M s)
      hp0 (hpε.trans (min_le_left _ _)) hr0 (hrε.trans (min_le_left _ _)) hs0 (hsε.trans (min_le_left _ _)) (-z)
    simp only [Prod.fst_neg,Prod.snd_neg,norm_neg] at hm
    have finish (t K : ℕ) (ht : t∈mobiusDivisorCoupledTwoWindow b N K) (htL : t∉insert q L)
        (hK : K∈({2,7,14}:Finset ℕ))
        (hz : c*‖z‖≤ -z.1*(mobiusDivisorCoupledTwoInterpolatedProfile K (divisorPrimeClipWeight M t)).1+
          -z.2*(mobiusDivisorCoupledTwoInterpolatedProfile K (divisorPrimeClipWeight M t)).2) :
        ∃ p∈(mobiusDivisorCoupledTwoPool b N).erase q,p∉L ∧
          z.1*(mobiusDivisorTwoPlanePacket M p P).1+z.2*(mobiusDivisorTwoPlanePacket M p P).2≤ -(c/4)*‖z‖ := by
      have htp := window_subset_pool b N K hK ht
      obtain ⟨htpr,_,_,htq⟩ := pdata t htp
      have htK := (window K t hK ht).2.2.2.1
      have he := core_profile P hP h2 htq
      rw [htK] at he
      rw [← he] at hz
      have hscale := (packet_scale_lower (by omega : 0< M) htpr.pos htq).1
      have hρ : 0≤ Real.sqrt t/Real.sqrt M := by positivity
      have hd0 : z.1*mobiusDivisorInterpolatedFibre M t P ∅+z.2*mobiusDivisorInterpolatedFibre M t P {2}≤ -c*‖z‖ := by
        dsimp only at hz
        linarith only [hz]
      have hd1 := mul_le_mul_of_nonneg_left hd0 hρ
      have hd2 := mul_le_mul_of_nonpos_right hscale (show -c*‖z‖≤ 0 by nlinarith only [hc,norm_nonneg z])
      refine ⟨t,mem_erase.mpr ⟨fun h => htL (mem_insert.mpr (Or.inl h)),htp⟩,
        fun h => htL (mem_insert_of_mem h),?_⟩
      dsimp only [mobiusDivisorTwoPlanePacket]
      calc
        _ = (Real.sqrt t/Real.sqrt M)*(z.1*mobiusDivisorInterpolatedFibre M t P ∅+z.2*mobiusDivisorInterpolatedFibre M t P {2}) := by ring
        _ ≤ (1/4)*(-c*‖z‖) := hd1.trans hd2
        _ = _ := by ring
    rcases le_max_iff.mp hm with hm|hm
    · exact finish p 2 hp hpL (by simp) hm
    · rcases le_max_iff.mp hm with hm|hm
      · exact finish r 7 hr hrL (by simp) hm
      · exact finish s 14 hs hsL (by simp) hm


/-- A square-root number of positive square reserves pays the complete receiving error
of a bounded physical displacement under a quadratic envelope budget. -/
theorem mobiusDivisor_two_plane_repair_error_budget (E C H d m n D : ℝ)
    (hC : 0< C) (hH : 0< H) (hd : 0< d) (hm : 1≤ m)
    (hE : E≤ C*m^2) (hD0 : 0≤ D) (hD : D≤ H*Real.sqrt m)
    (hn : (2*Real.sqrt C*H+H^2+1)/d*Real.sqrt m≤ n) :
    2*Real.sqrt E*D+D^2+m≤ d*n*m := by
  have hm0 : 0≤ m := by linarith only [hm]
  have hs : Real.sqrt E≤ Real.sqrt C*m := by
    calc
      _ ≤ Real.sqrt (C*m^2) := Real.sqrt_le_sqrt hE
      _ = _ := by rw [Real.sqrt_mul hC.le,Real.sqrt_sq hm0]
  have hr1 : 1≤ Real.sqrt m := by rw [Real.le_sqrt (by norm_num) hm0]; simpa using hm
  have hquad : D^2≤ (H*Real.sqrt m)^2 := by gcongr
  have hlin : 2*Real.sqrt E*D≤ 2*(Real.sqrt C*m)*(H*Real.sqrt m) := by gcongr
  have hscale := mul_le_mul_of_nonneg_left hr1 (show 0≤ (H^2+1)*m by positivity)
  have hpay := mul_le_mul_of_nonneg_right hn (show 0≤ d*m by positivity)
  have he : ((2*Real.sqrt C*H+H^2+1)/d*Real.sqrt m)*(d*m)=
      (2*Real.sqrt C*H+H^2+1)*m*Real.sqrt m := by field_simp
  rw [he] at hpay
  have hsq := Real.sq_sqrt hm0
  have hquad' : D^2≤ H^2*m := by nlinarith only [hquad,hsq]
  nlinarith only [hlin,hquad',hscale,hpay]

/-- For all sufficiently large fields, actual unused source windows pay for any prescribed
available prime with quotient at most fourteen, using only square-root many primes.
The bound is uniform in the processed core; the endpoint lowers the complete
successor envelope by at least the field cutoff. -/
theorem exists_mobiusDivisor_prescribed_window_repair :
    ∃ b : ℕ,15≤ b ∧ ∀ C : ℝ,0< C → ∃ A : ℝ,0<A ∧ ∀ᶠ N : ℕ in atTop,
      let M := 14*(b+1)*N
      ∀ P : Finset ℕ,∀ q : ℕ,
        mobiusDivisorCoupledTwoCore⊆P → 2∉P →
        (∀ p∈mobiusDivisorCoupledTwoPool b N,p∉P) →
        mobiusDivisorSuccessorEnvelope M P≤ C*(M:ℝ)^2 →
        q.Prime → q∉P → q< M → 15≤ q → M/q≤ 14 →
        ∃ L : Finset ℕ,q∈L ∧ L⊆insert q (mobiusDivisorCoupledTwoPool b N) ∧
          L.card=⌈A*Real.sqrt M⌉₊+1 ∧
          mobiusDivisorSuccessorEnvelope M (P∪L)+(M:ℝ)≤ mobiusDivisorSuccessorEnvelope M P := by
  obtain ⟨b,c,d,hb,hc,hd,hgeometry⟩ := exists_mobiusDivisorTwoPlaneWindowGeometry
  refine ⟨b,hb,?_⟩
  intro C hC
  let H : ℝ := 2*(9^2/c+9)
  have hH : 0< H := by dsimp only [H]; positivity
  let A : ℝ := (2*Real.sqrt C*H+H^2+1)/d
  have hA : 0< A := by dsimp only [A]; positivity
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_mobiusDivisorCoupledTwoCapacity_sub_one_ge_sqrt b (by omega) A hA,
    eventually_ge_atTop (1:ℕ)] with N hn hN
  let M := 14*(b+1)*N
  have hM : 2< M := by dsimp only [M]; nlinarith
  dsimp only
  intro P q hP h2 hfresh hE hqprime hqP hqM hq15 hqquot
  obtain ⟨hv,hreserve,hdir⟩ := hgeometry N hN P hP h2 hfresh
  let U := (mobiusDivisorCoupledTwoPool b N).erase q
  let n := ⌈A*Real.sqrt M⌉₊
  have hncap : n≤ mobiusDivisorCoupledTwoCapacity b N-1 := Nat.ceil_le.mpr hn
  have hnlow : A*Real.sqrt M≤(n:ℝ) := Nat.le_ceil _
  obtain ⟨l,hnd,hlen,hsub,hbound⟩ := exists_bounded_plane_displacement_batch
    (fun p => mobiusDivisorTwoPlanePacket M p P) U n (mobiusDivisorTwoPlanePacket M q P) 9 c (by norm_num) hc
    (norm_mobiusDivisorTwoPlanePacket_le_nine P hM hqprime hqP (by omega) hqquot)
    (fun p hp => hv p (mem_erase.mp hp).2)
    (fun L _ hL z => hdir q L (hL.trans_le hncap) z)
  let S := l.toFinset
  let L := insert q S
  have hSP : S⊆mobiusDivisorCoupledTwoPool b N := fun p hp => (mem_erase.mp (hsub hp)).2
  have hqS : q∉S := fun h => (mem_erase.mp (hsub h)).1 rfl
  have hcard : S.card=n := by dsimp only [S]; rw [List.toFinset_card_of_nodup hnd,hlen]
  have pdata (p : ℕ) (hp : p∈L) : p.Prime ∧ p< M ∧ p∉P ∧ 15≤ p ∧ M/p≤ 14 := by
    rcases mem_insert.mp hp with rfl|hp
    · exact ⟨hqprime,hqM,hqP,hq15,hqquot⟩
    · obtain ⟨K,hK,_,hpp,hpM,hp15,hpquot,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN (hSP hp)
      have hk : K≤ 14 := by simp only [mem_insert,mem_singleton] at hK; rcases hK with rfl|rfl|rfl <;> omega
      exact ⟨hpp,hpM,hfresh p (hSP hp),hp15,by change (14*(b+1)*N)/p ≤ 14; omega⟩
  have hbase := mobiusDivisorSuccessorEnvelope_two_block_reserve_error M P L hM
    (fun p hp => let h := pdata p hp; ⟨h.1,h.2.1,h.2.2.1,by have := h.2.2.2.1; omega⟩)
    (fun p hp => (mobiusDivisorCoupledTwoCore_covers (by have := (pdata p hp).2.2.2.2; omega)).trans hP)
    (fun p hp r hr _ => by have := (pdata p hp).2.2.2.2; have := (pdata r hr).2.2.2.1; omega)
  let X : ℝ := ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅
  let Y : ℝ := ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}
  let R : ℝ := ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+(mobiusDivisorInterpolatedFibre M p P {2})^2)
  let T : ℝ := ∑ p∈L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^2
  change mobiusDivisorSuccessorEnvelope M (P∪L)+min R T≤
    mobiusDivisorSuccessorEnvelope M P+2*Real.sqrt (mobiusDivisorSuccessorEnvelope M P)*(|X|+|Y|)+(|X|+|Y|)^2 at hbase
  let x := (mobiusDivisorTwoPlanePacket M q P).1+∑ p∈S,(mobiusDivisorTwoPlanePacket M p P).1
  let y := (mobiusDivisorTwoPlanePacket M q P).2+∑ p∈S,(mobiusDivisorTwoPlanePacket M p P).2
  have hxy : |x|+|y|≤ H := by
    change x^2+y^2≤ 2*(9^2/c+9)^2 at hbound
    have hx := sq_abs x
    have hy := sq_abs y
    have hh := sq_nonneg (|x|-|y|)
    dsimp only [H]
    have hpos : 0<9^2/c+9 := by positivity
    nlinarith only [hbound,hx,hy,hh,hpos,abs_nonneg x,abs_nonneg y]
  have hr : 0< Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0< M by omega))
  have hsum (R' : Finset ℕ) :
      (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R')=
        Real.sqrt M*(Real.sqrt q*mobiusDivisorInterpolatedFibre M q P R'/Real.sqrt M+
          ∑ p∈S,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R'/Real.sqrt M) := by
    dsimp only [L]
    rw [sum_insert hqS,← sum_div]
    field_simp
  have hX : X=Real.sqrt M*x := hsum ∅
  have hY : Y=Real.sqrt M*y := hsum {2}
  have hD : |X|+|Y|≤ H*Real.sqrt M := by
    rw [hX,hY,abs_mul,abs_mul,abs_of_pos hr]
    nlinarith only [hxy,hr]
  have hRS : d*(n:ℝ)*(M:ℝ)≤ R ∧ d*(n:ℝ)*(M:ℝ)≤ T := by
    have hsum0 := sum_le_sum (fun p hp => (hreserve p (hSP hp)).1)
    have hsum1 := sum_le_sum (fun p hp => (hreserve p (hSP hp)).2)
    have he : (∑ _p∈S,d*(M:ℝ))=d*(n:ℝ)*(M:ℝ) := by simp only [sum_const,nsmul_eq_mul,hcard]; ring
    rw [he] at hsum0 hsum1
    constructor
    · apply hsum0.trans
      exact sum_le_sum_of_subset_of_nonneg (subset_insert q S) (fun p _ _ => by positivity)
    · apply hsum1.trans
      exact sum_le_sum_of_subset_of_nonneg (subset_insert q S) (fun p _ _ => by positivity)
  have hpay := mobiusDivisor_two_plane_repair_error_budget (mobiusDivisorSuccessorEnvelope M P) C H d M n (|X|+|Y|)
    hC hH hd (by exact_mod_cast (show 1≤ M by omega)) hE (by positivity) hD hnlow
  have hmin := le_min hRS.1 hRS.2
  refine ⟨L,mem_insert_self q S,?_,?_,?_⟩
  · exact insert_subset_insert q hSP
  · exact (card_insert_of_notMem hqS).trans (congrArg (fun k => k+1) hcard)
  · linarith only [hbase,hpay,hmin]

end RHTower

namespace RHTower

/-- A prescribed prime two can be paid with square-root many actual source primes
once all other remaining quotients are bounded. Its own quotient is unrestricted. -/
theorem exists_mobiusDivisor_two_bounded_front_repair :
    ∃ b : ℕ,15≤ b ∧ ∀ J : ℕ,∀ C : ℝ,0< C → ∃ A : ℝ,0< A ∧ ∀ᶠ N : ℕ in atTop,
      let M := 14*(b+1)*N
      ∀ P : Finset ℕ,mobiusDivisorCoupledTwoCore⊆P → 2∉P →
        (∀ p∈mobiusDivisorCoupledTwoPool b N,p∉P) →
        mobiusDivisorSuccessorEnvelope M P≤ C*(M:ℝ)^2 →
        (∀ q∈mobiusDivisorSelectionPrimes M\insert 2 P,M/q≤ J) →
        ∃ L : Finset ℕ,2∈L ∧ L⊆insert 2 (mobiusDivisorCoupledTwoPool b N) ∧
          L.card=⌈A*Real.sqrt M⌉₊+1 ∧
          mobiusDivisorSuccessorEnvelope M (P∪L)+(M:ℝ)≤ mobiusDivisorSuccessorEnvelope M P := by
  obtain ⟨b,c,d,hb,hc,hd,hgeometry⟩ := exists_mobiusDivisorTwoPlaneWindowGeometry
  refine ⟨b,hb,?_⟩
  intro J C hC
  let H : ℝ := 2*(9^2/c+9)
  have hH : 0< H := by dsimp only [H]; positivity
  let C' : ℝ := C+2*((J:ℝ)+1)*Real.sqrt C
  have hC' : 0< C' := by dsimp only [C']; positivity
  let B : ℝ := (2*Real.sqrt C'*H+H^2+1)/(d/2)
  let D : ℝ := 4*((J:ℝ)+1)*Real.sqrt C/d
  let A : ℝ := B+D
  have hB : 0< B := by dsimp only [B]; positivity
  have hD : 0< D := by dsimp only [D]; positivity
  have hA : 0< A := add_pos hB hD
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_mobiusDivisorCoupledTwoCapacity_sub_one_ge_sqrt b (by omega) A hA,
    eventually_ge_atTop (1:ℕ)] with N hn hN
  let M := 14*(b+1)*N
  have hM : 2< M := by dsimp only [M]; nlinarith
  have hm0 : (0:ℝ)≤ M := Nat.cast_nonneg M
  have hm1 : (1:ℝ)≤ M := by exact_mod_cast (show 1≤ M by omega)
  have hr : 0< Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0< M by omega))
  have hrM : Real.sqrt M≤ (M:ℝ) := by
    have h := Real.sqrt_le_sqrt (show (M:ℝ)≤ (M:ℝ)^2 by nlinarith only [hm1])
    simpa only [Real.sqrt_sq hm0] using h
  dsimp only
  intro P hP h2 hfresh hE hfront
  let P' := insert 2 P
  let E := mobiusDivisorSuccessorEnvelope M P
  let E' := mobiusDivisorSuccessorEnvelope M P'
  have hsE : Real.sqrt E≤ Real.sqrt C*(M:ℝ) := by
    calc
      _ ≤ Real.sqrt (C*(M:ℝ)^2) := Real.sqrt_le_sqrt hE
      _ = _ := by rw [Real.sqrt_mul hC.le,Real.sqrt_sq hm0]
  have hfront0 := mobiusDivisorSuccessorEnvelope_insert_le_remaining_quotient M J P Nat.prime_two hM h2 hfront
  rw [Real.sqrt_mul hm0] at hfront0
  have hfront' : E'≤ E+2*((J:ℝ)+1)*Real.sqrt C*(M:ℝ)*Real.sqrt M := by
    have hcost : (6/5:ℝ)*(J:ℝ)*(Real.sqrt M*Real.sqrt E)≤ 2*((J:ℝ)+1)*Real.sqrt C*(M:ℝ)*Real.sqrt M := by
      have hh := mul_le_mul_of_nonneg_left hsE (show 0≤ (6/5:ℝ)*(J:ℝ)*Real.sqrt M by positivity)
      have hprod : 0≤ Real.sqrt C*(M:ℝ)*Real.sqrt M := by positivity
      have hjprod := mul_nonneg (Nat.cast_nonneg (α:=ℝ) J) hprod
      nlinarith only [hh,hprod,hjprod]
    norm_num only [Nat.cast_ofNat] at hfront0
    change E'≤ E+(6/5:ℝ)*(J:ℝ)*(Real.sqrt M*Real.sqrt E) at hfront0
    linarith only [hfront0,hcost]
  have hE' : E'≤ C'*(M:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hrM (show 0≤ 2*((J:ℝ)+1)*Real.sqrt C*(M:ℝ) by positivity)
    dsimp only [C']
    nlinarith only [hfront',hE,hh]
  obtain ⟨hv,hreserve,hdir⟩ := hgeometry N hN P hP h2 hfresh
  let U := (mobiusDivisorCoupledTwoPool b N).erase 2
  let n := ⌈A*Real.sqrt M⌉₊
  have hncap : n≤ mobiusDivisorCoupledTwoCapacity b N-1 := Nat.ceil_le.mpr hn
  have hnlow : A*Real.sqrt M≤ (n:ℝ) := Nat.le_ceil _
  obtain ⟨l,hnd,hlen,hsub,hbound⟩ := exists_bounded_plane_displacement_batch
    (fun p => mobiusDivisorTwoPlanePacket M p P) U n (0,0) 9 c (by norm_num) hc (by simp)
    (fun p hp => hv p (mem_erase.mp hp).2)
    (fun L _ hL z => hdir 2 L (hL.trans_le hncap) z)
  let S := l.toFinset
  have hSP : S⊆mobiusDivisorCoupledTwoPool b N := fun p hp => (mem_erase.mp (hsub hp)).2
  have h2S : 2∉S := fun h => (mem_erase.mp (hsub h)).1 rfl
  have hcard : S.card=n := by dsimp only [S]; rw [List.toFinset_card_of_nodup hnd,hlen]
  have pdata (p : ℕ) (hp : p∈S) : p.Prime ∧ p< M ∧ p∉P' ∧ 15≤ p ∧ M/p≤ 14 := by
    obtain ⟨K,hK,_,hpp,hpM,hp15,hpquot,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN (hSP hp)
    have hk : K≤ 14 := by simp only [mem_insert,mem_singleton] at hK; rcases hK with rfl|rfl|rfl <;> omega
    exact ⟨hpp,hpM,by simp only [P',mem_insert,not_or]; exact ⟨by omega,hfresh p (hSP hp)⟩,
      hp15,by change (14*(b+1)*N)/p≤ 14; omega⟩
  have hfold (p : ℕ) : mobiusDivisorInterpolatedFibre M p P' ∅=
      mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2} := by
    simp only [P',mobiusDivisorInterpolatedFibre,mobiusDivisorSelectionFibre_insert,
      notMem_empty,if_false,insert_empty_eq]
    ring
  have hzero (p : ℕ) : mobiusDivisorInterpolatedFibre M p P' {2}=0 := by
    simp [P',mobiusDivisorInterpolatedFibre,mobiusDivisorSelectionFibre_insert]
  have hbase := mobiusDivisorSuccessorEnvelope_two_block_reserve_error M P' S hM
    (fun p hp => let h := pdata p hp; ⟨h.1,h.2.1,h.2.2.1,by have := h.2.2.2.1; omega⟩)
    (fun p hp => ((mobiusDivisorCoupledTwoCore_covers (by have := (pdata p hp).2.2.2.2; omega)).trans hP).trans (subset_insert 2 P))
    (fun p hp r hr _ => by have := (pdata p hp).2.2.2.2; have := (pdata r hr).2.2.2.1; omega)
  let Z : ℝ := ∑ p∈S,Real.sqrt p*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})
  let T : ℝ := ∑ p∈S,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^2
  dsimp only at hbase
  simp only [hfold,hzero,mul_zero,sum_const_zero,abs_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero,min_self] at hbase
  change mobiusDivisorSuccessorEnvelope M (P'∪S)+T≤ E'+2*Real.sqrt E'*|Z|+|Z|^2 at hbase
  let x : ℝ := ∑ p∈S,(mobiusDivisorTwoPlanePacket M p P).1
  let y : ℝ := ∑ p∈S,(mobiusDivisorTwoPlanePacket M p P).2
  have hxy : |x|+|y|≤ H := by
    simp only [zero_add] at hbound
    change x^2+y^2≤ 2*(9^2/c+9)^2 at hbound
    have hpos : 0<9^2/c+9 := by positivity
    dsimp only [H]
    nlinarith only [hbound,sq_abs x,sq_abs y,sq_nonneg (|x|-|y|),hpos,abs_nonneg x,abs_nonneg y]
  have hsum (R : Finset ℕ) :
      (∑ p∈S,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R)=
        Real.sqrt M*(∑ p∈S,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R/Real.sqrt M) := by
    rw [←sum_div]
    field_simp
  have hZ : Z=Real.sqrt M*(x+y) := by
    dsimp only [Z]
    simp only [mul_add,sum_add_distrib]
    rw [hsum ∅,hsum {2}]
    dsimp only [x,y,mobiusDivisorTwoPlanePacket]
  have hZbound : |Z|≤ H*Real.sqrt M := by
    rw [hZ,abs_mul,abs_of_pos hr]
    have hh := (abs_add_le x y).trans hxy
    nlinarith only [hh,hr]
  have hT : d*(n:ℝ)*(M:ℝ)≤ T := by
    have hh := sum_le_sum (fun p hp => (hreserve p (hSP hp)).2)
    have he : (∑ _p∈S,d*(M:ℝ))=d*(n:ℝ)*(M:ℝ) := by simp only [sum_const,nsmul_eq_mul,hcard]; ring
    rwa [he] at hh
  have hnB : B*Real.sqrt M≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hr.le).trans hnlow
  have hnD : D*Real.sqrt M≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB.le) hr.le).trans hnlow
  have hpay := mobiusDivisor_two_plane_repair_error_budget E' C' H (d/2) M n |Z| hC' hH (by positivity)
    hm1 hE' (abs_nonneg _) hZbound hnB
  have hpayFront := mul_le_mul_of_nonneg_right hnD (show 0≤ d/2*(M:ℝ) by positivity)
  have heFront : D*Real.sqrt M*(d/2*(M:ℝ))=2*((J:ℝ)+1)*Real.sqrt C*(M:ℝ)*Real.sqrt M := by
    dsimp only [D]
    field_simp
    norm_num
  rw [heFront] at hpayFront
  have hfinal : mobiusDivisorSuccessorEnvelope M (P'∪S)+(M:ℝ)≤ E := by
    nlinarith only [hbase,hT,hpay,hpayFront,hfront']
  refine ⟨insert 2 S,mem_insert_self 2 S,insert_subset_insert 2 hSP,?_,?_⟩
  · exact (card_insert_of_notMem h2S).trans (congrArg (fun k => k+1) hcard)
  · simpa only [P',union_insert,insert_union] using hfinal
end RHTower
