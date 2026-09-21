import GaloisForLFunctions.RHTower.MobiusDivisorFiniteClockCountingCancellation
import GaloisForLFunctions.HTGeometry.InwardPlaneDisplacementReturn
import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedWindowRepair
import GaloisForLFunctions.RHTower.MobiusDivisorLogarithmicWindowCapacity

/-!
# Quadratic payment from actual primes at the current clock

The complete cofactor weight `1 + log r` survives the source merger.
For children supported in the head/two plane, every packet removes its
copied squares with weights `1 + log p` and `1 + log p + log 2`.
Inward selection in the corresponding weighted receiving metric keeps
every prefix within a linear allowance of the starting clock energy.

Using the actual prime-window capacity, rather than only square-root many
primes, produces a positive quadratic terminal payment. The constants are
uniform over admitted inherited cores. The literal initial core supplies
its own admission bound, giving a closed producer without a payment premise.

This theorem fixes the current cutoff. It neither completes the remaining
prime order nor pays the larger inherited debts requiring increasing child
depth. No RH conclusion or uniform transport between cutoffs is asserted.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
open HTGeometry

private lemma weighted_insert_nat (P : Finset ℕ) (hP : ∀q ∈ P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (M : ℕ) :
    mobiusDivisorFiniteClockEnergy 1 M (insert p P)-mobiusDivisorFiniteClockEnergy 1 M P+
      2*Real.sqrt p*∑r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (1+Real.log r)*(r:ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*
          mobiusDivisorInterpolatedFibre M (p*r) P ∅ =
      -(p:ℝ)*Real.log p*∑r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (r:ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^2 := by
  let Q : Finset Nat.Primes := P.attach.image (fun q => ⟨q.val,hP q.val q.property⟩)
  have he : (Q.erase ⟨p,hp⟩).image (fun q : Nat.Primes => (q:ℕ))=P := by
    ext q
    simp only [mem_image,mem_erase,Q]
    constructor
    · rintro ⟨r,⟨_,⟨s,_,hs⟩⟩,hr⟩
      have hv := congrArg (fun t : Nat.Primes => (t:ℕ)) hs
      change s.val=r.val at hv
      rw [← hr,← hv]
      exact s.property
    · intro hq
      refine ⟨⟨q,hP q hq⟩,⟨?_,⟨⟨q,hq⟩,by simp,rfl⟩⟩,rfl⟩
      intro h
      have hh := congrArg (fun t : Nat.Primes => (t:ℕ)) h
      change q=p at hh
      exact hpP (hh ▸ hq)
  have h := mobiusDivisorFiniteClockEnergy_source_cancellation Q ⟨p,hp⟩ M 1
  dsimp only at h
  rw [he] at h
  exact h

private lemma fibre_sample (P : Finset ℕ) (M : ℕ) {r : ℕ}
    (hs : Squarefree r) (hd : Disjoint r.primeFactors P) :
    mobiusDivisorSelectionFibre M P r.primeFactors =
      Real.sqrt r*((ArithmeticFunction.moebius r : ℤ):ℝ)*mobiusDivisorInterpolatedFibre M r P ∅ := by
  simpa only [Nat.prod_primeFactors_of_squarefree hs] using
    mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
      (fun q hq => (Nat.mem_primeFactors.mp hq).1) hd

private lemma clipped_sample (P : Finset ℕ) (M : ℕ) {p r : ℕ}
    (hp : p.Prime) (hpP : p∉P) (hr : 0<r) (hs : Squarefree r)
    (hd : Disjoint r.primeFactors (insert p P)) :
    mobiusDivisorInterpolatedFibre M p P r.primeFactors =
      Real.sqrt r*((ArithmeticFunction.moebius r : ℤ):ℝ)*mobiusDivisorInterpolatedFibre M (p*r) P ∅ := by
  have hpR : p∉r.primeFactors := fun h => disjoint_left.mp hd h (mem_insert_self _ _)
  have h := mobiusDivisorSelectionFibre_insert_interpolation hp M P r.primeFactors hpP hpR
  rw [fibre_sample (insert p P) M hs hd,
    fibre_sample P M hs (hd.mono_right (subset_insert _ _)),
    mobiusDivisorInterpolatedHead_insert_prime P hp hpP hr hs hd M] at h
  have hp0 : 0<Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  nlinarith only [h,hp0]

private lemma sparse_child (M p : ℕ) (P R : Finset ℕ)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P)
    (h0 : R ≠ ∅) (h2 : R ≠ {2}) : mobiusDivisorInterpolatedFibre M p P R=0 := by
  have hc : mobiusDivisorSelectionPrimes (M/p)\{2} ⊆ P := by
    refine Subset.trans ?_ hcore
    intro q hq
    obtain ⟨hq,hn⟩ := mem_sdiff.mp hq
    obtain ⟨hq,hprime⟩ := mem_filter.mp hq
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hq; omega),hprime⟩,hn⟩
  simp only [mobiusDivisorInterpolatedFibre,
    mobiusDivisorSelectionFibre_one_remaining_zero (M/p) 2 P R hc h0 h2,
    mobiusDivisorSelectionFibre_one_remaining_zero (M/p+1) 2 P R hcore h0 h2]
  ring

private lemma weighted_two_insert (M : ℕ) (P : Finset ℕ) (hP : ∀q ∈ P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (hp2 : p ≠ 2) (h2 : 2∉P) (hM : 2<M)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P) :
    mobiusDivisorFiniteClockEnergy 1 M (insert p P)-mobiusDivisorFiniteClockEnergy 1 M P =
      -2*Real.sqrt p*(mobiusDivisorSelectionFibre M P ∅*mobiusDivisorInterpolatedFibre M p P ∅+
        (1+Real.log 2)*mobiusDivisorSelectionFibre M P {2}*mobiusDivisorInterpolatedFibre M p P {2})-
      (p:ℝ)*Real.log p*((mobiusDivisorInterpolatedFibre M p P ∅)^2+
        (mobiusDivisorInterpolatedFibre M p P {2})^2) := by
  let S := fixedCoreSquarefreeIndices (insert p P) M
  have sub : ({1,2}:Finset ℕ) ⊆ S := by
    intro r hr
    simp only [mem_insert,mem_singleton] at hr
    rcases hr with rfl|rfl
    · apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by simp,?_⟩
      simp
    · apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨by omega,by omega⟩,Nat.prime_two.squarefree,?_⟩
      rw [Nat.prime_two.primeFactors]
      simp [h2,Ne.symm hp2]
  have data (r : ℕ) (hr : r ∈ S) :
      (r:ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*mobiusDivisorInterpolatedFibre M (p*r) P ∅ =
        mobiusDivisorSelectionFibre M P r.primeFactors*mobiusDivisorInterpolatedFibre M p P r.primeFactors  ∧ 
      (r:ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^2 =
        (mobiusDivisorInterpolatedFibre M p P r.primeFactors)^2 := by
    obtain ⟨hr,hs,hd⟩ := mem_filter.mp hr
    have h0 := (mem_Icc.mp hr).1
    rw [clipped_sample P M hp hpP h0 hs hd,
      fibre_sample P M hs (hd.mono_right (subset_insert _ _))]
    have hmu : (((ArithmeticFunction.moebius r:ℤ):ℝ))^2=1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) r)
    constructor
    · calc
        _ = (Real.sqrt r)^2*(((ArithmeticFunction.moebius r:ℤ):ℝ))^2*
            mobiusDivisorInterpolatedFibre M r P ∅*mobiusDivisorInterpolatedFibre M (p*r) P ∅ := by
              rw [hsqrt,hmu]; ring
        _ = _ := by ring
    · simp only [mul_pow,hsqrt,hmu,mul_one]
  have reduce (f : ℕ → ℝ) :
      (∑r ∈ S,f r*mobiusDivisorSelectionFibre M P r.primeFactors*mobiusDivisorInterpolatedFibre M p P r.primeFactors) =
        f 1*mobiusDivisorSelectionFibre M P ∅*mobiusDivisorInterpolatedFibre M p P ∅+
        f 2*mobiusDivisorSelectionFibre M P {2}*mobiusDivisorInterpolatedFibre M p P {2} := by
    have he := sum_subset sub (f:=fun r => f r*mobiusDivisorSelectionFibre M P r.primeFactors*
      mobiusDivisorInterpolatedFibre M p P r.primeFactors) (by
      intro r hr hn
      have hs := (mem_filter.mp hr).2.1
      have h0 : r.primeFactors ≠ ∅ := by
        intro h
        have hh := Nat.prod_primeFactors_of_squarefree hs
        rw [h,prod_empty] at hh
        simp [← hh] at hn
      have htwo : r.primeFactors ≠ {2} := by
        intro h
        have hh := Nat.prod_primeFactors_of_squarefree hs
        rw [h,prod_singleton] at hh
        simp [← hh] at hn
      rw [sparse_child M p P r.primeFactors hcore h0 htwo,mul_zero])
    rw [← he]
    simp [Nat.prime_two.primeFactors]
  have mixed : (∑r ∈ S,(1+Real.log r)*(r:ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*
      mobiusDivisorInterpolatedFibre M (p*r) P ∅)=
      mobiusDivisorSelectionFibre M P ∅*mobiusDivisorInterpolatedFibre M p P ∅+
      (1+Real.log 2)*mobiusDivisorSelectionFibre M P {2}*mobiusDivisorInterpolatedFibre M p P {2} := by
    have hrw := sum_congr (s₁:=S) rfl (fun (r : ℕ) hr => congrArg (fun x : ℝ => (1+Real.log r)*x) (data r hr).1)
    simp only [← mul_assoc] at hrw
    rw [hrw,reduce]
    simp
  have diag : (∑r ∈ S,(r:ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^2)=
      (mobiusDivisorInterpolatedFibre M p P ∅)^2+(mobiusDivisorInterpolatedFibre M p P {2})^2 := by
    rw [sum_congr rfl (fun r hr => (data r hr).2)]
    have he := sum_subset sub (f:=fun r => (mobiusDivisorInterpolatedFibre M p P r.primeFactors)^2) (by
      intro r hr hn
      have hs := (mem_filter.mp hr).2.1
      have hfac := Nat.prod_primeFactors_of_squarefree hs
      have h0 : r.primeFactors ≠ ∅ := by intro h; rw [h,prod_empty] at hfac; simp [← hfac] at hn
      have ht : r.primeFactors ≠ {2} := by intro h; rw [h,prod_singleton] at hfac; simp [← hfac] at hn
      rw [sparse_child M p P r.primeFactors hcore h0 ht,zero_pow (by omega)])
    rw [← he]
    simp [Nat.prime_two.primeFactors]
  have h := weighted_insert_nat P hP hp hpP M
  change _+2*Real.sqrt p*(∑r ∈ S,_)= -(p:ℝ)*Real.log p*(∑r ∈ S,_) at h
  rw [mixed,diag] at h
  linarith only [h]

private def clockPair (M : ℕ) (P : Finset ℕ) : ℝ :=
  (mobiusDivisorSelectionFibre M P ∅)^2+
    (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2

private def clockPacket (M p : ℕ) (P : Finset ℕ) : ℝ :=
  (p:ℝ)*((1+Real.log p)*(mobiusDivisorInterpolatedFibre M p P ∅)^2+
    (1+Real.log p+Real.log 2)*(mobiusDivisorInterpolatedFibre M p P {2})^2)

private lemma clock_pair_nonneg (M : ℕ) (P : Finset ℕ) : 0 ≤ clockPair M P := by
  have hl : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  unfold clockPair
  positivity

private lemma clipped_union (M p : ℕ) (P L R : Finset ℕ)
    (hL : ∀q ∈ L,M/p+1 ≤ q) :
    mobiusDivisorInterpolatedFibre M p (P∪L) R=mobiusDivisorInterpolatedFibre M p P R := by
  rw [mobiusDivisorInterpolatedFibre,
    mobiusDivisorSelectionFibre_union_inactive (M/p) P L R
      (fun q hq => by have := hL q hq; omega),
    mobiusDivisorSelectionFibre_union_inactive (M/p+1) P L R hL]
  rfl

private lemma clock_insert_balance (M : ℕ) (P : Finset ℕ) (hP : ∀q ∈ P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (hp2 : p ≠ 2) (h2 : 2∉P) (hM : 2<M)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P) :
    mobiusDivisorFiniteClockEnergy 1 M (insert p P)+clockPair M P+clockPacket M p P =
      mobiusDivisorFiniteClockEnergy 1 M P+clockPair M (insert p P) := by
  have h := weighted_two_insert M P hP hp hpP hp2 h2 hM hcore
  unfold clockPair clockPacket
  rw [mobiusDivisorSelectionFibre_insert_interpolation hp M P ∅ hpP (by simp),
    mobiusDivisorSelectionFibre_insert_interpolation hp M P {2} hpP (by simpa using hp2)]
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
  linear_combination h-((mobiusDivisorInterpolatedFibre M p P ∅)^2+
    (1+Real.log 2)*(mobiusDivisorInterpolatedFibre M p P {2})^2)*hs

private lemma clock_union_balance (M : ℕ) (P L : Finset ℕ) (hP : ∀q ∈ P,q.Prime)
    (h2 : 2∉P) (hM : 2<M)
    (hL : ∀p ∈ L,p.Prime  ∧  p∉P  ∧  p ≠ 2)
    (hcore : ∀p ∈ L,mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P)
    (hchild : ∀p ∈ L,∀q ∈ L,p ≠ q → M/p+1 ≤ q) :
    mobiusDivisorFiniteClockEnergy 1 M (P∪L)+clockPair M P+
      (∑p ∈ L,clockPacket M p P) =
      mobiusDivisorFiniteClockEnergy 1 M P+clockPair M (P∪L) := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert p L hpL ih =>
    obtain ⟨hp,hpP,hp2⟩ := hL p (mem_insert_self _ _)
    have hL' := fun q hq => hL q (mem_insert_of_mem hq)
    have hc' := fun q hq => hcore q (mem_insert_of_mem hq)
    have hd' := fun q hq r hr hqr => hchild q (mem_insert_of_mem hq) r (mem_insert_of_mem hr) hqr
    have hprime : ∀q ∈ P∪L,q.Prime := by
      intro q hq
      rcases mem_union.mp hq with hq|hq
      · exact hP q hq
      · exact (hL' q hq).1
    have htwo : 2∉P∪L := by
      simp only [mem_union,not_or]
      exact ⟨h2,fun h => (hL' 2 h).2.2 rfl⟩
    have hinactive : ∀q ∈ L,M/p+1 ≤ q := fun q hq =>
      hchild p (mem_insert_self _ _) q (mem_insert_of_mem hq) (fun he => hpL (he.symm ▸ hq))
    have hs := clock_insert_balance M (P∪L) hprime hp (by simp [hpP,hpL]) hp2 htwo hM
      ((hcore p (mem_insert_self _ _)).trans subset_union_left)
    have packet : clockPacket M p (P∪L)=clockPacket M p P := by
      unfold clockPacket
      rw [clipped_union M p P L ∅ hinactive,clipped_union M p P L {2} hinactive]
    rw [packet] at hs
    have hi := ih hL' hc' hd'
    rw [union_insert,sum_insert hpL]
    linarith only [hs,hi]

private lemma scaled_direction {z v : ℝ × ℝ} {s c : ℝ} (hs : 1 ≤ s) (hc : 0<c)
    (h : z.1*v.1+(s*z.2)*v.2  ≤  -c*‖(z.1,s*z.2)‖) :
    z.1*v.1+z.2*(s*v.2)  ≤  -c*‖z‖ := by
  have hn : ‖z‖ ≤ ‖(z.1,s*z.2)‖ := by
    simp only [Prod.norm_def,Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0 ≤ s by linarith)]
    exact max_le_max le_rfl (le_mul_of_one_le_left (abs_nonneg _) hs)
  have hh := mul_le_mul_of_nonpos_left hn (by linarith : -c ≤ 0)
  nlinarith only [h,hh]

private lemma scaled_norm {v : ℝ × ℝ} {s : ℝ} (hs : 1 ≤ s) (hv : ‖v‖ ≤ 9) :
    ‖(v.1,s*v.2)‖ ≤ 9*s := by
  have hf : |v.1| ≤ 9 := (show |v.1| ≤ ‖v‖ by simpa using norm_fst_le v).trans hv
  have hg : |v.2| ≤ 9 := (show |v.2| ≤ ‖v‖ by simpa using norm_snd_le v).trans hv
  simp only [Prod.norm_def,Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0 ≤ s by linarith)]
  apply max_le
  · nlinarith only [hf,hs]
  · nlinarith only [hg,hs]

private lemma weighted_radius (a b s t x y : ℝ) (hs : s ≠ 0) :
    s^2*(planeDisplacementRadius (-a/s+x,-t*b/s+t*y))^2 =
      (a-s*x)^2+t^2*(b-s*y)^2 := by
  rw [planeDisplacementRadius,Real.sq_sqrt (by positivity)]
  field_simp
  ring

private lemma clock_packet_lower (M p : ℕ) (P : Finset ℕ) {d : ℝ}
    (_hd : 0<d) (hlog : Real.log (M:ℝ)/2 ≤ Real.log p)
    (hr : d*(M:ℝ) ≤ (p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+
      (mobiusDivisorInterpolatedFibre M p P {2})^2))
    (hM : 1 ≤ M) : d*(M:ℝ)*Real.log M/2 ≤ clockPacket M p P := by
  have hm : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have htwo : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hr (show 0 ≤ Real.log (M:ℝ)/2 by positivity)
  have hx := sq_nonneg (mobiusDivisorInterpolatedFibre M p P ∅)
  have hy := sq_nonneg (mobiusDivisorInterpolatedFibre M p P {2})
  have hb : 0 ≤ (p:ℝ) := Nat.cast_nonneg _
  unfold clockPacket
  nlinarith [mul_nonneg hb hx,mul_nonneg hb hy,
    mul_nonneg (show 0 ≤ 1+Real.log p-Real.log (M:ℝ)/2 by linarith) (mul_nonneg hb hx),
    mul_nonneg (show 0 ≤ 1+Real.log p+Real.log 2-Real.log (M:ℝ)/2 by linarith) (mul_nonneg hb hy)]

private lemma window_log_lower (M p : ℕ) (hM : 225 ≤ M) (hp : 0<p) (hq : M/p ≤ 14) :
    Real.log (M:ℝ)/2 ≤ Real.log p := by
  have hm : M<15*p := (Nat.div_lt_iff_lt_mul hp).mp (by omega)
  have hMr : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have h := Real.log_le_log hMr (show (M:ℝ) ≤ 15*(p:ℝ) by exact_mod_cast hm.le)
  rw [Real.log_mul (by norm_num : (15:ℝ) ≠ 0) hpR.ne'] at h
  have hsq := Real.log_le_log (by norm_num : (0:ℝ)<(15:ℝ)^2)
    (show (15:ℝ)^2 ≤ (M:ℝ) by exact_mod_cast hM)
  rw [Real.log_pow] at hsq
  norm_num only [Nat.cast_ofNat] at hsq
  linarith

private lemma capacity_clock_payment (b N : ℕ) (hb : 1 ≤ b) (hN : 2 ≤ N)
    (hc : 2 ≤ mobiusDivisorCoupledTwoCapacity b N)
    (hcap : (N:ℝ)/(14*Real.log ((14*b*N:ℕ):ℝ)) ≤ (mobiusDivisorCoupledTwoCapacity b N:ℝ)) :
    (N:ℝ) ≤ 28*((mobiusDivisorCoupledTwoCapacity b N-1:ℕ):ℝ)*Real.log (14*(b+1)*N:ℕ) := by
  have hlog : 0<Real.log ((14*b*N:ℕ):ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<14*b*N by nlinarith))
  have hlog' := Real.log_le_log (by positivity : (0:ℝ)<(14*b*N:ℕ))
    (show ((14*b*N:ℕ):ℝ) ≤ (14*(b+1)*N:ℕ) by exact_mod_cast (show 14*b*N ≤ 14*(b+1)*N by nlinarith))
  have hm := (div_le_iff₀ (show 0<14*Real.log ((14*b*N:ℕ):ℝ) by positivity)).mp hcap
  have hh : (mobiusDivisorCoupledTwoCapacity b N:ℝ) ≤ 
      2*((mobiusDivisorCoupledTwoCapacity b N-1:ℕ):ℝ) := by
    exact_mod_cast (show mobiusDivisorCoupledTwoCapacity b N ≤ 2*(mobiusDivisorCoupledTwoCapacity b N-1) by omega)
  have h1 := mul_le_mul_of_nonneg_right hh (show 0 ≤ 14*Real.log ((14*b*N:ℕ):ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlog'
    (show 0 ≤ 28*((mobiusDivisorCoupledTwoCapacity b N-1:ℕ):ℝ) by positivity)
  nlinarith only [hm,h1,h2]

/-- Actual source batches produce a quadratic payment in the complete
logarithmic clock energy at the current cutoff. Every prefix has only a
linear allowance. Constants are uniform over every admitted inherited core. -/
theorem eventually_exists_mobiusDivisorCurrentClockPayment :
    ∃ b : ℕ,∃ R δ : ℝ,15 ≤ b  ∧  0<R  ∧  0<δ  ∧ 
      ∀ C : ℝ,0<C  →  ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        ∀ P : Finset ℕ,(∀p ∈ P,p.Prime)  →  mobiusDivisorCoupledTwoCore ⊆ P  →  2∉P  → 
          (∀p ∈ mobiusDivisorCoupledTwoPool b N,p∉P)  → 
          (mobiusDivisorSelectionFibre M P ∅)^2+
            (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2 ≤ C*(M:ℝ)^2  → 
          ∃ l : List ℕ,l.Nodup  ∧  l.length=mobiusDivisorCoupledTwoCapacity b N-1  ∧ 
            l.toFinset ⊆ mobiusDivisorCoupledTwoPool b N  ∧ 
            (∀ k : ℕ,mobiusDivisorFiniteClockEnergy 1 M (P∪(l.take k).toFinset) ≤ 
              mobiusDivisorFiniteClockEnergy 1 M P+R^2*M)  ∧ 
            (mobiusDivisorSelectionFibre M (P∪l.toFinset) ∅)^2+
              (1+Real.log 2)*(mobiusDivisorSelectionFibre M (P∪l.toFinset) {2})^2 ≤ R^2*M  ∧ 
            mobiusDivisorFiniteClockEnergy 1 M (P∪l.toFinset)+
              (mobiusDivisorSelectionFibre M P ∅)^2+
              (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2+
              δ*(M:ℝ)^2 ≤ mobiusDivisorFiniteClockEnergy 1 M P := by
  obtain ⟨b,c,d,hb,hc,hd,hgeometry⟩ := exists_mobiusDivisorTwoPlaneWindowGeometry
  let t := Real.sqrt (1+Real.log (2:ℝ))
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have ht : 1 ≤ t := by
    dsimp [t]
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have htsq : t^2=1+Real.log (2:ℝ) := Real.sq_sqrt (by positivity)
  let B := 9*t
  have hB : 0<B := by dsimp [B]; positivity
  let R := 4*B^2/c+2*B+c
  have hR : 0<R := by dsimp [R]; positivity
  let δ := d/(4*28*14*((b:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  refine ⟨b,R,δ,hb,hR,hδ,?_⟩
  intro C hC
  let A := 4*Real.sqrt C/c+4*R^2/(d*Real.log 2)+1
  have hA : 0<A := by dsimp [A]; positivity
  filter_upwards [eventually_mobiusDivisorCoupledTwoCapacity_sub_one_ge_sqrt b (by omega) A hA,
    eventually_mobiusDivisorCoupledTwoCapacity_ge_logarithmic b (by omega),
    eventually_mobiusDivisorCoupledTwoCapacity_ge b 2 (by omega),
    eventually_ge_atTop (225:ℕ)] with N hcap hcount htwo hN
  let M := 14*(b+1)*N
  have hM : 225 ≤ M := by dsimp [M]; nlinarith
  have hMr : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hm1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlogM : Real.log (2:ℝ) ≤ Real.log (M:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ M by omega))
  let s := Real.sqrt (M:ℝ)
  have hs : 0<s := Real.sqrt_pos.mpr hMr
  have hssq : s^2=M := Real.sq_sqrt hMr.le
  have hs1 : 1 ≤ s := by
    dsimp [s]
    rw [Real.le_sqrt (by norm_num) hMr.le]
    simpa using hm1
  let n := mobiusDivisorCoupledTwoCapacity b N-1
  have hn : A*s ≤ (n:ℝ) := hcap
  have hAn : A ≤ (n:ℝ) := (le_mul_of_one_le_right hA.le hs1).trans hn
  dsimp only
  intro P hprime hP h2 hfresh hpair
  obtain ⟨hu,hreserve,hdir⟩ := hgeometry N (by omega) P hP h2 hfresh
  let u := fun p => mobiusDivisorTwoPlanePacket M p P
  let v := fun p => ((u p).1,t*(u p).2)
  let a := mobiusDivisorSelectionFibre M P ∅
  let e := mobiusDivisorSelectionFibre M P {2}
  let z0 : ℝ × ℝ := (-a/s,-t*e/s)
  let z := fun L : Finset ℕ => z0+∑p ∈ L,v p
  have hv : ∀p ∈ mobiusDivisorCoupledTwoPool b N,‖v p‖ ≤ B :=
    fun p hp => scaled_norm ht (hu p hp)
  have hdir' : ∀L ⊆ mobiusDivisorCoupledTwoPool b N,L.card<n  →  ∀w : ℝ × ℝ,
      ∃p ∈ mobiusDivisorCoupledTwoPool b N,p∉L  ∧ 
        w.1*(v p).1+w.2*(v p).2 ≤  -c*‖w‖ := by
    intro L _ hLn w
    obtain ⟨p,hp,hpn,hpd⟩ := hdir 0 L hLn (w.1,t*w.2)
    exact ⟨p,(mem_erase.mp hp).2,hpn,scaled_direction (z:=w) (v:=u p) ht hc hpd⟩
  obtain ⟨l,hnd,hlen,hsub,hradius⟩ := exists_planeDisplacement_return_batch v
    (mobiusDivisorCoupledTwoPool b N) n z0 B c hB hc hv hdir'
  have pdata : ∀p ∈ l.toFinset,p.Prime  ∧  p<M  ∧  p∉P  ∧  15 ≤ p  ∧  M/p ≤ 14 := by
    intro p hp
    obtain ⟨K,hK,_,hpp,hpM,hp15,hpq,_⟩ := mobiusDivisorCoupledTwoPool_data hb (by omega) (hsub hp)
    have hk : K ≤ 14 := by
      simp only [mem_insert,mem_singleton] at hK
      rcases hK with rfl|rfl|rfl <;> omega
    exact ⟨hpp,hpM,hfresh p (hsub hp),hp15,by dsimp [M]; omega⟩
  have coord (L : Finset ℕ) :
      s*(∑p ∈ L,u p).1=∑p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅  ∧ 
      s*(∑p ∈ L,u p).2=∑p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2} := by
    constructor
    · rw [Prod.fst_sum]
      simp only [u,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      change s*(_/s)=_
      field_simp
    · rw [Prod.snd_sum]
      simp only [u,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      change s*(_/s)=_
      field_simp
  have physical (L : Finset ℕ) (hL : L ⊆ l.toFinset) :
      clockPair M (P∪L)=(M:ℝ)*(planeDisplacementRadius (z L))^2 := by
    have hchild : ∀p ∈ L,∀q ∈ L,p ≠ q → M/p+1 ≤ q := by
      intro p hp q hq _
      have := (pdata p (hL hp)).2.2.2.2
      have := (pdata q (hL hq)).2.2.2.1
      omega
    have ha := mobiusDivisorSelectionFibre_union_two_child_inactive M P L ∅
      (fun p hp => ⟨(pdata p (hL hp)).1,(pdata p (hL hp)).2.2.1,by simp⟩) hchild
    have he := mobiusDivisorSelectionFibre_union_two_child_inactive M P L {2}
      (fun p hp => ⟨(pdata p (hL hp)).1,(pdata p (hL hp)).2.2.1,
        by have := (pdata p (hL hp)).2.2.2.1; simp only [mem_singleton]; omega⟩) hchild
    have hz : z L=(-a/s+(∑p ∈ L,u p).1,-t*e/s+t*(∑p ∈ L,u p).2) := by
      ext <;> simp [z,z0,v,Prod.fst_sum,Prod.snd_sum,mul_sum]
    have hr := weighted_radius a e s t (∑p ∈ L,u p).1 (∑p ∈ L,u p).2 hs.ne'
    rw [htsq,hssq,(coord L).1,(coord L).2,← hz] at hr
    unfold clockPair
    rw [ha,he]
    exact hr.symm
  have initial : (M:ℝ)*(planeDisplacementRadius z0)^2=clockPair M P := by
    have hh := physical ∅ (empty_subset _)
    simpa only [union_empty,z,sum_empty,add_zero] using hh.symm
  have hr0 : planeDisplacementRadius z0 ≤ Real.sqrt C*s := by
    have hrE : (planeDisplacementRadius z0)^2 ≤ C*(M:ℝ) := by
      change clockPair M P ≤ C*(M:ℝ)^2 at hpair
      nlinarith only [hpair,initial,hMr]
    have he : (Real.sqrt C*s)^2=C*(M:ℝ) := by
      rw [mul_pow,Real.sq_sqrt hC.le,hssq]
    nlinarith only [hrE,he,mul_nonneg (Real.sqrt_nonneg C) hs.le,
      show 0 ≤ planeDisplacementRadius z0 from Real.sqrt_nonneg _]
  have hdecay : planeDisplacementRadius z0-(n:ℝ)*c/4 ≤ 0 := by
    have hAroot : 4*Real.sqrt C/c ≤ A := by
      have hh : 0 ≤ 4*R^2/(d*Real.log 2)+1 := by positivity
      dsimp [A]
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hAroot hs.le
    have hh' := mul_le_mul_of_nonneg_right (hh.trans hn) hc.le
    have he : (4*Real.sqrt C/c*s)*c=4*(Real.sqrt C*s) := by field_simp
    rw [he] at hh'
    linarith only [hr0,hh']
  have hpay : R^2 ≤ d/4*(n:ℝ)*Real.log M := by
    have hAr : 4*R^2/(d*Real.log 2) ≤ A := by
      have hh : 0 ≤ 4*Real.sqrt C/c+1 := by positivity
      dsimp [A]
      linarith only [hh]
    have hh := (div_le_iff₀ (mul_pos hd hlog2)).mp (hAr.trans hAn)
    have hh' := mul_le_mul_of_nonneg_left hlogM (show 0 ≤ (n:ℝ)*d by positivity)
    nlinarith only [hh,hh']
  have energy (L : Finset ℕ) (hL : L ⊆ l.toFinset) :
      mobiusDivisorFiniteClockEnergy 1 M (P∪L)+clockPair M P+(∑p ∈ L,clockPacket M p P)=
        mobiusDivisorFiniteClockEnergy 1 M P+clockPair M (P∪L) := by
    apply clock_union_balance M P L hprime h2 (by omega)
    · intro p hp
      have hh := pdata p (hL hp)
      exact ⟨hh.1,hh.2.2.1,by omega⟩
    · intro p hp
      exact (mobiusDivisorCoupledTwoCore_covers (by have := (pdata p (hL hp)).2.2.2.2; omega)).trans hP
    · intro p hp q hq _
      have := (pdata p (hL hp)).2.2.2.2
      have := (pdata q (hL hq)).2.2.2.1
      omega
  have reserve (p : ℕ) (hp : p ∈ l.toFinset) :
      d*(M:ℝ)*Real.log M/2 ≤ clockPacket M p P :=
    clock_packet_lower M p P hd
      (window_log_lower M p hM (pdata p hp).1.pos (pdata p hp).2.2.2.2)
      (hreserve p (hsub hp)).1 (by omega)
  have endpoint : clockPair M (P∪l.toFinset) ≤ R^2*M := by
    have hr := hradius n le_rfl
    rw [← hlen,List.take_length,hlen] at hr
    have hrr : planeDisplacementRadius (z l.toFinset) ≤ R :=
      hr.trans (max_le le_rfl (hdecay.trans hR.le))
    rw [physical _ Subset.rfl]
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hrr
    have hh' := mul_le_mul_of_nonneg_left hh hMr.le
    change (M:ℝ)*(planeDisplacementRadius (z l.toFinset))^2 ≤ (M:ℝ)*R^2 at hh'
    linarith only [hh']
  refine ⟨l,hnd,hlen,hsub,?_,endpoint,?_⟩
  · intro k
    let L := (l.take k).toFinset
    have hL : L ⊆ l.toFinset := by
      intro p hp
      exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp))
    have hr : planeDisplacementRadius (z L) ≤ max R (planeDisplacementRadius z0) := by
      by_cases hk : k ≤ n
      · exact (hradius k hk).trans (max_le_max_left _ (sub_le_self _ (by positivity)))
      · have ht : l.take k=l := List.take_of_length_le (by omega)
        have hh := hradius n le_rfl
        rw [← hlen,List.take_length,hlen] at hh
        dsimp [L]
        rw [ht]
        exact hh.trans (max_le_max_left _ (sub_le_self _ (by positivity)))
    have he := energy L hL
    have hres : 0 ≤ ∑p ∈ L,clockPacket M p P := by
      apply sum_nonneg
      intro p hp
      exact (show 0 ≤ d*(M:ℝ)*Real.log M/2 by positivity).trans (reserve p (hL hp))
    change mobiusDivisorFiniteClockEnergy 1 M (P∪L) ≤ mobiusDivisorFiniteClockEnergy 1 M P+R^2*M
    rw [physical L hL] at he
    rcases le_total R (planeDisplacementRadius z0) with hle|hle
    · rw [max_eq_right hle] at hr
      have hh := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr hr) hMr.le
      change (M:ℝ)*(planeDisplacementRadius (z L))^2 ≤
        (M:ℝ)*(planeDisplacementRadius z0)^2 at hh
      nlinarith only [he,hh,initial,hres,sq_nonneg R,hMr]
    · rw [max_eq_left hle] at hr
      have hh := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hr) hMr.le
      change (M:ℝ)*(planeDisplacementRadius (z L))^2 ≤ (M:ℝ)*R^2 at hh
      nlinarith only [he,hh,hres,clock_pair_nonneg M P]
  · have he := energy l.toFinset Subset.rfl
    have hr := sum_le_sum (fun p hp => reserve p hp)
    simp only [sum_const,nsmul_eq_mul,List.toFinset_card_of_nodup hnd,hlen] at hr
    have hp := mul_le_mul_of_nonneg_right hpay hMr.le
    have hcount' := capacity_clock_payment b N (by omega) (by omega) htwo hcount
    change (N:ℝ) ≤ 28*(n:ℝ)*Real.log (M:ℝ) at hcount'
    have hmult := mul_le_mul_of_nonneg_left hcount' (show 0 ≤ d/4*(M:ℝ) by positivity)
    have hδeq : δ*(M:ℝ)^2=d/4*(M:ℝ)*(N:ℝ)/28 := by
      dsimp [δ,M]
      push_cast
      field_simp
    change _+a^2+(1+Real.log 2)*e^2+δ*(M:ℝ)^2 ≤ _
    rw [hδeq]
    dsimp only [clockPair] at he endpoint
    nlinarith only [he,hr,hp,endpoint,hmult]

/-- The fixed literal core supplies its own admission bound. This closed
producer has no source-sign, correlation, or energy-bound premise. -/
theorem eventually_exists_mobiusDivisorInitialClockPayment :
    ∃ b : ℕ,∃ R δ : ℝ,15 ≤ b ∧ 0 < R ∧ 0 < δ ∧
      ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        ∃ l : List ℕ,l.Nodup ∧ l.length=mobiusDivisorCoupledTwoCapacity b N-1 ∧
          l.toFinset ⊆ mobiusDivisorCoupledTwoPool b N ∧
          (∀ k : ℕ,mobiusDivisorFiniteClockEnergy 1 M (P∪(l.take k).toFinset) ≤
            mobiusDivisorFiniteClockEnergy 1 M P+R^2*M) ∧
          (mobiusDivisorSelectionFibre M (P∪l.toFinset) ∅)^2+
            (1+Real.log 2)*(mobiusDivisorSelectionFibre M (P∪l.toFinset) {2})^2 ≤ R^2*M ∧
          mobiusDivisorFiniteClockEnergy 1 M (P∪l.toFinset)+
            (mobiusDivisorSelectionFibre M P ∅)^2+
            (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2+
            δ*(M:ℝ)^2 ≤ mobiusDivisorFiniteClockEnergy 1 M P := by
  obtain ⟨b,R,δ,hb,hR,hδ,hproduce⟩ := eventually_exists_mobiusDivisorCurrentClockPayment
  let P := mobiusDivisorCoupledTwoCore
  let D : ℝ := (3/5:ℝ)*2^(P.card-1)
  have hD : 0<D := by dsimp [D]; positivity
  have hlog : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  let C := (2+Real.log (2:ℝ))*D^2
  have hC : 0<C := by dsimp [C]; positivity
  have hprime : ∀p∈P,p.Prime := fun p hp => (mem_filter.mp (mem_erase.mp hp).2).2
  refine ⟨b,R,δ,hb,hR,hδ,?_⟩
  filter_upwards [hproduce C hC,eventually_ge_atTop (1:ℕ)] with N hprod hN
  let M := 14*(b+1)*N
  have hM : 1≤M := by dsimp [M]; nlinarith
  have hMr : (1:ℝ)≤M := by exact_mod_cast hM
  have amplitude (S : Finset ℕ) (hS : ∀p∈S,p.Prime) :
      (mobiusDivisorSelectionFibre M P S)^2 ≤ D^2*(M:ℝ) := by
    have hh := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P S hprime hS
    change |mobiusDivisorSelectionFibre M P S| ≤ D*Real.sqrt M at hh
    have hh' := (sq_le_sq₀ (abs_nonneg _) (show 0≤D*Real.sqrt M by positivity)).mpr hh
    simpa only [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)] using hh'
  have h0 := amplitude ∅ (by simp)
  have htwo := amplitude {2} (by simpa using Nat.prime_two)
  have hw := mul_le_mul_of_nonneg_left htwo (show 0≤1+Real.log (2:ℝ) by positivity)
  have hpair : (mobiusDivisorSelectionFibre M P ∅)^2+
      (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2 ≤ C*(M:ℝ)^2 := by
    have hsq : (M:ℝ)≤(M:ℝ)^2 := by nlinarith only [hMr]
    have hh := mul_le_mul_of_nonneg_left hsq hC.le
    dsimp [C] at hh ⊢
    nlinarith only [h0,hw,hh]
  exact hprod P hprime Subset.rfl (by simp [P,mobiusDivisorCoupledTwoCore]) (by
    intro p hpW hpP
    obtain ⟨K,hK,_,_,_,hp15,_,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN hpW
    have hpLt := mem_range.mp (mem_filter.mp (mem_erase.mp hpP).2).1
    omega) hpair

end RHTower
