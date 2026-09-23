import GaloisForLFunctions.RHTower.MobiusDivisorPaidCutoffInterval

/-!
# Growing-depth omitted-prime payment at the current clock

The complete logarithmically weighted insertion identity gives reciprocal-prime
control of a prescribed insertion's cost. A current-clock batch of actual
helper primes pays that cost whenever `A * (1 + log M) ≤ q ≤ M / 16`, with
constants and the clock threshold chosen before `q`.

An actual prime in the logarithmic window is produced at every sufficiently
large clock. Its child depth is at least `M / (2*A*(1+log M)) - 1`, a quantity
proved to tend to infinity. The payment retains a positive quadratic reserve
through every original integer cutoff in the fourth-root interval, and the
stronger batch theorem controls all intermediate cores on that interval.

These are unconditional local producers over the literal initial core.
Their extensions at distinct clocks need not be nested. Payment for fixed
omitted primes below the moving logarithmic threshold, uniform control over
accumulated cores, exhaustive continuation, and bounded critical action
remain open. The helper batch itself uses the existing shallow source windows.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

private lemma weighted_insert_nat (P : Finset ℕ) (hP : ∀q ∈ P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (M : ℕ) :
    mobiusDivisorFiniteClockEnergy 1 M (insert p P)-mobiusDivisorFiniteClockEnergy 1 M P+
      2*Real.sqrt p*∑r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (1+Real.log r)*(r:ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*
          mobiusDivisorInterpolatedFibre M (p*r) P ∅ =
      -(p:ℝ)*Real.log p*∑r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (r:ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^(2 : ℕ) := by
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

private lemma sample_vanish (P : Finset ℕ) {M r : ℕ} (hr : 0<r) (hMr : M ≤ r) :
    mobiusDivisorInterpolatedFibre M r P ∅=0 := by
  have h0 : mobiusDivisorSelectionFibre 0 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre,mobiusDivisorSelectionIndices,subsetLabelFibre]
  have h1 : mobiusDivisorSelectionFibre 1 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre,mobiusDivisorSelectionIndices,subsetLabelFibre]
  rcases hMr.eq_or_lt with rfl | hlt
  · have hw : divisorPrimeClipWeight M M=0 := by simp [divisorPrimeClipWeight,Nat.div_self hr]
    simp [mobiusDivisorInterpolatedFibre,Nat.div_self hr,hw,h1]
  · simp [mobiusDivisorInterpolatedFibre,Nat.div_eq_of_lt hlt,h0,h1]

private lemma sample_amplitude (P : Finset ℕ) (hP : ∀p ∈ P,p.Prime)
    (M r : ℕ) (hr : 0 < r) :
    Real.sqrt r*|mobiusDivisorInterpolatedFibre M r P ∅| ≤
      ((3/5:ℝ)*2^(P.card-1))*Real.sqrt M := by
  let D : ℝ := (3/5:ℝ)*2^(P.card-1)
  have h0 := abs_mobiusDivisorSelectionFibre_le_source_amplitude (M/r) P ∅ hP (by simp)
  have h1 := abs_mobiusDivisorSelectionFibre_le_source_amplitude (M/r+1) P ∅ hP (by simp)
  have hw0 := divisorPrimeClipWeight_nonneg M r hr
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M r := by
    have := divisorPrimeClipWeight_lt_one M r hr
    linarith
  have hclock := divisorPrimeClipWeight_mul_step M r hr
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg r)] at hclock
  have hc : Real.sqrt r*((1-divisorPrimeClipWeight M r)*Real.sqrt (M/r:ℕ)+
      divisorPrimeClipWeight M r*Real.sqrt (M/r+1:ℕ))=Real.sqrt M := by
    push_cast
    nlinarith only [hclock]
  calc
    _ ≤ Real.sqrt r*((1-divisorPrimeClipWeight M r)*|mobiusDivisorSelectionFibre (M/r) P ∅|+
        divisorPrimeClipWeight M r*|mobiusDivisorSelectionFibre (M/r+1) P ∅|) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg r)
      unfold mobiusDivisorInterpolatedFibre
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul,abs_of_nonneg hw1,abs_of_nonneg hw0])
    _ ≤ Real.sqrt r*((1-divisorPrimeClipWeight M r)*(D*Real.sqrt (M/r:ℕ))+
        divisorPrimeClipWeight M r*(D*Real.sqrt (M/r+1:ℕ))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left h0 hw1) (mul_le_mul_of_nonneg_left h1 hw0)) (Real.sqrt_nonneg r)
    _ = _ := by
      change _=D*Real.sqrt M
      nlinarith only [congrArg (fun x : ℝ => D*x) hc]

/-- The complete weighted insertion cost has an explicit reciprocal-prime
bound. Both source factors and the logarithmic copied-square payment are
retained before estimating the mixed term. -/
theorem mobiusDivisorFiniteClockEnergy_insert_cost_le
    (P : Finset ℕ) (hP : ∀q ∈ P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P)
    {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorFiniteClockEnergy 1 M (insert p P)-mobiusDivisorFiniteClockEnergy 1 M P ≤
      2*((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)*(M:ℝ)^(2 : ℕ)*(1+Real.log M)/p := by
  let D : ℝ := (3/5:ℝ)*2^(P.card-1)
  let S := fixedCoreSquarefreeIndices (insert p P) M
  let T := fixedCoreSquarefreeIndices (insert p P) (M/p)
  let f := fun r : ℕ => (1+Real.log r)*(r:ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*
    mobiusDivisorInterpolatedFibre M (p*r) P ∅
  have hMp : (0:ℝ) < M := by exact_mod_cast hM
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hlogM : 0 ≤ 1+Real.log (M:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ M by exact_mod_cast hM)
    linarith
  have hsum : ∑r ∈ S,f r=∑r ∈ T,f r := by
    symm
    apply sum_subset
    · intro r hr
      obtain ⟨hr,hs⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨Icc_subset_Icc le_rfl (Nat.div_le_self M p) hr,hs⟩
    · intro r hr hn
      obtain ⟨hr,hs⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      have hsmall : ¬r ≤ M/p := fun h => hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨hr'.1,h⟩,hs⟩)
      have hpr : M ≤ p*r := by
        have hh := (Nat.div_lt_iff_lt_mul hp.pos).mp (lt_of_not_ge hsmall)
        nlinarith
      dsimp [f]
      rw [sample_vanish P (by nlinarith [hp.pos] : 0 < p*r) hpr,mul_zero]
  have he := weighted_insert_nat P hP hp hpP M
  have hn : -(p:ℝ)*Real.log p*∑r ∈ S,(r:ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^(2 : ℕ) ≤ 0 := by
    have hlog := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast hp.one_lt.le)
    have hnon : 0 ≤ ∑r ∈ S,(r:ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^(2 : ℕ) :=
      sum_nonneg (fun r _ => by positivity)
    have hh := mul_nonneg (mul_nonneg hpR.le hlog) hnon
    nlinarith only [hh]
  change _+2*Real.sqrt p*(∑r ∈ S,f r)=_ at he
  have hfirst : mobiusDivisorFiniteClockEnergy 1 M (insert p P)-mobiusDivisorFiniteClockEnergy 1 M P ≤
      ∑r ∈ T,-(2*Real.sqrt p)*f r := by
    rw [← mul_sum,← hsum]
    linarith only [he,hn]
  have hpoint (r : ℕ) (hr : r ∈ T) : -(2*Real.sqrt p)*f r ≤ 2*D^(2 : ℕ)*(M:ℝ)*(1+Real.log M) := by
    have hr' := mem_Icc.mp (mem_filter.mp hr).1
    have hrM : r ≤ M := hr'.2.trans (Nat.div_le_self M p)
    have hrpos : (0:ℝ) < r := by exact_mod_cast hr'.1
    have hw : 0 ≤ 1+Real.log (r:ℝ) := by
      have := Real.log_nonneg (show (1:ℝ) ≤ r by exact_mod_cast hr'.1)
      linarith
    have hwM : 1+Real.log (r:ℝ) ≤ 1+Real.log (M:ℝ) :=
      add_le_add le_rfl (Real.log_le_log hrpos (by exact_mod_cast hrM))
    have ha := sample_amplitude P hP M r hr'.1
    have hb := sample_amplitude P hP M (p*r) (by nlinarith [hp.pos])
    have hab := mul_le_mul ha hb (by positivity) (by positivity)
    have heq : (Real.sqrt r*|mobiusDivisorInterpolatedFibre M r P ∅|)*
        (Real.sqrt (p*r:ℕ)*|mobiusDivisorInterpolatedFibre M (p*r) P ∅|)=
        Real.sqrt p*(r:ℝ)*|mobiusDivisorInterpolatedFibre M r P ∅| *
          |mobiusDivisorInterpolatedFibre M (p*r) P ∅| := by
      rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg p)]
      calc
        _ = Real.sqrt p*(Real.sqrt r)^(2 : ℕ)*|mobiusDivisorInterpolatedFibre M r P ∅| *
            |mobiusDivisorInterpolatedFibre M (p*r) P ∅| := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg r)]
    rw [heq,← pow_two,mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)] at hab
    change _ ≤ D^(2 : ℕ)*(M:ℝ) at hab
    have hab' := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2*(1+Real.log (r:ℝ)) by positivity)
    have habM := mul_le_mul_of_nonneg_left hwM (show 0 ≤ 2*D^(2 : ℕ)*(M:ℝ) by positivity)
    have hneg : -(2*Real.sqrt p)*f r ≤
        2*(1+Real.log r)*Real.sqrt p*(r:ℝ)*
          |mobiusDivisorInterpolatedFibre M r P ∅| *|mobiusDivisorInterpolatedFibre M (p*r) P ∅| := by
      have hh := neg_le_abs (mobiusDivisorInterpolatedFibre M r P ∅*mobiusDivisorInterpolatedFibre M (p*r) P ∅)
      rw [abs_mul] at hh
      have hm := mul_le_mul_of_nonneg_left hh
        (show 0 ≤ 2*(1+Real.log r)*Real.sqrt p*(r:ℝ) by positivity)
      dsimp [f]
      nlinarith only [hm]
    nlinarith only [hneg,hab',habM]
  have hcard : T.card ≤ M/p := by
    simpa [T,fixedCoreSquarefreeIndices] using
      card_le_card (filter_subset (fun r => Squarefree r ∧ Disjoint r.primeFactors (insert p P)) (Icc 1 (M/p)))
  have hquot : ((M/p:ℕ):ℝ) ≤ (M:ℝ)/p := by
    apply (le_div_iff₀ hpR).mpr
    exact_mod_cast Nat.div_mul_le_self M p
  calc
    _ ≤ ∑r ∈ T,2*D^(2 : ℕ)*(M:ℝ)*(1+Real.log M) := hfirst.trans (sum_le_sum hpoint)
    _ ≤ (M/p:ℕ)*(2*D^(2 : ℕ)*(M:ℝ)*(1+Real.log M)) := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ ((M:ℝ)/p)*(2*D^(2 : ℕ)*(M:ℝ)*(1+Real.log M)) :=
      mul_le_mul_of_nonneg_right hquot (by positivity)
    _ = _ := by dsimp [D]; ring


private lemma clock_amplitude_bound (P : Finset ℕ) (hP : ∀p ∈ P,p.Prime)
    {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorFiniteClockEnergy 1 M P ≤
      ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)*(M:ℝ)^(2 : ℕ)*(1+Real.log M) := by
  let D : ℝ := (3/5:ℝ)*2^(P.card-1)
  have hw : 0 ≤ 1+Real.log (M:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ M by exact_mod_cast hM)
    linarith
  have hcard : (fixedCoreSquarefreeIndices P M).card ≤ M := by
    simpa [fixedCoreSquarefreeIndices] using
      card_le_card (filter_subset (fun r => Squarefree r ∧ Disjoint r.primeFactors P) (Icc 1 M))
  unfold mobiusDivisorFiniteClockEnergy
  calc
    _ ≤ ∑r ∈ fixedCoreSquarefreeIndices P M,(1+Real.log M)*D^(2 : ℕ)*(M:ℝ) := by
      apply sum_le_sum
      intro r hr
      have hr' := mem_Icc.mp (mem_filter.mp hr).1
      have ha := sample_amplitude P hP M r hr'.1
      change Real.sqrt r*|mobiusDivisorInterpolatedFibre M r P ∅| ≤ D*Real.sqrt M at ha
      have hs := (sq_le_sq₀ (by positivity) (by positivity)).mpr ha
      simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) r),
        Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M),sq_abs] at hs
      have hw' : 0 ≤ 1+Real.log (r:ℝ) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ r by exact_mod_cast hr'.1)
        linarith
      have hlog : 1+Real.log (r:ℝ) ≤ 1+Real.log (M:ℝ) :=
        add_le_add le_rfl (Real.log_le_log (by exact_mod_cast hr'.1) (by exact_mod_cast hr'.2))
      have hh := mul_le_mul_of_nonneg_left hs hw'
      have hh' := mul_le_mul_of_nonneg_right hlog (show 0 ≤ D^(2 : ℕ)*(M:ℝ) by positivity)
      nlinarith only [hh,hh']
    _ ≤ (M:ℝ)*((1+Real.log M)*D^(2 : ℕ)*(M:ℝ)) := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by dsimp [D]; ring

/-- A prescribed omitted prime may have child depth growing almost linearly
with the current cutoff. Its full insertion debt is paid at that same clock,
then every intermediate core and original cutoff in the fourth-root interval
is controlled. The clock threshold is chosen before the prescribed prime.
No payment, source-sign, or energy-bound premise is assumed. -/
theorem eventually_exists_mobiusDivisorGrowingDepthOmittedPrimePayment :
    ∃ b : ℕ, ∃ R δ A : ℝ, 15 ≤ b ∧ 0 < R ∧ 0 < δ ∧ 16 ≤ A ∧
      ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        ∀ q : ℕ, q.Prime → A*(1+Real.log M) ≤ q → 16*q ≤ M →
          ∃ l : List ℕ, q ∉ P ∧ q ∉ l.toFinset ∧ l.Nodup ∧
            l.length=mobiusDivisorCoupledTwoCapacity b N-1 ∧
            l.toFinset ⊆ mobiusDivisorCoupledTwoPool b N ∧
            (∀ k L : ℕ, M ≤ L → (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M) →
              mobiusDivisorFiniteClockEnergy 1 L ((insert q P)∪(l.take k).toFinset) ≤
                mobiusDivisorFiniteClockEnergy 1 M P+R^(2 : ℕ)*M+δ*(M:ℝ)^(2 : ℕ)) ∧
            (mobiusDivisorSelectionFibre M ((insert q P)∪l.toFinset) ∅)^(2 : ℕ)+
              (1+Real.log 2)*(mobiusDivisorSelectionFibre M ((insert q P)∪l.toFinset) {2})^(2 : ℕ) ≤ R^(2 : ℕ)*M ∧
            ∀ L : ℕ, M ≤ L → (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M) →
              mobiusDivisorFiniteClockEnergy 1 L ((insert q P)∪l.toFinset)+
                (mobiusDivisorSelectionFibre M (insert q P) ∅)^(2 : ℕ)+
                (1+Real.log 2)*(mobiusDivisorSelectionFibre M (insert q P) {2})^(2 : ℕ)+
                δ*(M:ℝ)^(2 : ℕ) ≤ mobiusDivisorFiniteClockEnergy 1 M P := by
  obtain ⟨b,R,δ,hb,hR,hδ,hproduce⟩ := eventually_exists_mobiusDivisorCurrentClockPayment
  let P := mobiusDivisorCoupledTwoCore
  let E : ℝ := (3/5:ℝ)*2^(P.card+1)
  let C : ℝ := (2+Real.log 2)*E^(2 : ℕ)
  let A : ℝ := 16+8*E^(2 : ℕ)/δ
  have hE : 0 < E := by dsimp [E]; positivity
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hA : 16 ≤ A := by
    dsimp [A]
    have := div_nonneg (show 0 ≤ 8*E^(2 : ℕ) by positivity) hδ.le
    linarith
  have hprime : ∀p ∈ P,p.Prime := fun p hp => (mem_filter.mp (mem_erase.mp hp).2).2
  have amplitude_le (Q : Finset ℕ) (hcard : Q.card ≤ P.card+1) :
      (3/5:ℝ)*2^(Q.card-1) ≤ E := by
    dsimp [E]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : Q.card-1 ≤ P.card+1))
      (by norm_num)
  have hclock : Tendsto (fun N : ℕ => 14*(b+1)*N) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro N
    change N ≤ 14*(b+1)*N
    nlinarith
  have htransport := hclock.eventually
    (eventually_mobiusDivisorFiniteClockEnergy_fourth_root_transport (E^(2 : ℕ)+R^(2 : ℕ)) (δ/4)
      (by positivity) (by positivity))
  refine ⟨b,R,δ/2,A,hb,hR,by positivity,hA,?_⟩
  filter_upwards [hproduce C hC,htransport,eventually_ge_atTop (1:ℕ)] with N hprod htrans hN
  let M := 14*(b+1)*N
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hw : 1 ≤ 1+Real.log (M:ℝ) := by
    have := Real.log_nonneg hMr
    linarith
  dsimp only
  intro q hq hqlo hqdepth
  have hq16 : 16 ≤ q := by
    have hh : (16:ℝ) ≤ A*(1+Real.log M) := by nlinarith only [hA,hw]
    exact_mod_cast hh.trans hqlo
  have hqP : q ∉ P := by
    intro h
    have hh := mem_range.mp (mem_filter.mp (mem_erase.mp h).2).1
    omega
  have hq2 : q ≠ 2 := by omega
  let Q := insert q P
  have hQ : ∀p ∈ Q,p.Prime := by simpa [Q] using And.intro hq hprime
  have hQcard : Q.card ≤ P.card+1 := card_insert_le _ _
  have hDQ := amplitude_le Q hQcard
  have hDP := amplitude_le P (by omega)
  have hfresh : ∀p ∈ mobiusDivisorCoupledTwoPool b N,p ∉ Q := by
    intro p hpW hpQ
    obtain ⟨K,hK,_,hp,hpM,hp15,hquot,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN hpW
    rcases mem_insert.mp hpQ with hpq | hpP
    · have hk : K ≤ 14 := by simp only [mem_insert,mem_singleton] at hK; rcases hK with rfl|rfl|rfl <;> omega
      rw [hpq] at hquot
      have hh : 16 ≤ M/q := (Nat.le_div_iff_mul_le hq.pos).mpr hqdepth
      change M/q=K at hquot
      omega
    · have hh := mem_range.mp (mem_filter.mp (mem_erase.mp hpP).2).1
      omega
  have amplitude (S : Finset ℕ) (hS : ∀p ∈ S,p.Prime) :
      (mobiusDivisorSelectionFibre M Q S)^(2 : ℕ) ≤ E^(2 : ℕ)*(M:ℝ) := by
    have ha := (abs_mobiusDivisorSelectionFibre_le_source_amplitude M Q S hQ hS).trans
      (mul_le_mul_of_nonneg_right hDQ (Real.sqrt_nonneg M))
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr ha
    simpa only [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)] using hs
  have hpair : (mobiusDivisorSelectionFibre M Q ∅)^(2 : ℕ)+
      (1+Real.log 2)*(mobiusDivisorSelectionFibre M Q {2})^(2 : ℕ) ≤ C*(M:ℝ)^(2 : ℕ) := by
    have h0 := amplitude ∅ (by simp)
    have h2 := mul_le_mul_of_nonneg_left (amplitude {2} (by simpa using Nat.prime_two))
      (show 0 ≤ 1+Real.log (2:ℝ) by positivity)
    have hsq : (M:ℝ) ≤ (M:ℝ)^(2 : ℕ) := by nlinarith only [hMr]
    have hh := mul_le_mul_of_nonneg_left hsq hC.le
    dsimp [C] at hh ⊢
    nlinarith only [h0,h2,hh]
  obtain ⟨l,hnd,hlen,hpool,hprefix,hendpair,hpay⟩ :=
    hprod Q hQ (subset_insert _ _) (by simp [Q,P,mobiusDivisorCoupledTwoCore,Ne.symm hq2]) hfresh hpair
  have hqnot : q ∉ l.toFinset := fun hh => hfresh q (hpool hh) (mem_insert_self _ _)
  have hcost : mobiusDivisorFiniteClockEnergy 1 M Q ≤
      mobiusDivisorFiniteClockEnergy 1 M P+(δ/4)*(M:ℝ)^(2 : ℕ) := by
    have hc := mobiusDivisorFiniteClockEnergy_insert_cost_le P hprime hq hqP hM
    have hpR : (0:ℝ) < q := by exact_mod_cast hq.pos
    have hcoarse : mobiusDivisorFiniteClockEnergy 1 M Q-mobiusDivisorFiniteClockEnergy 1 M P ≤
        2*E^(2 : ℕ)*(M:ℝ)^(2 : ℕ)*(1+Real.log M)/q := by
      apply hc.trans
      gcongr
    have hAeq : δ*A=16*δ+8*E^(2 : ℕ) := by dsimp [A]; field_simp [hδ.ne']
    have hleft : 8*E^(2 : ℕ)*(1+Real.log M) ≤ δ*(A*(1+Real.log M)) := by
      rw [← mul_assoc,hAeq]
      have hh := mul_nonneg hδ.le (show 0 ≤ 1+Real.log (M:ℝ) by linarith)
      nlinarith only [hh]
    have hright := mul_le_mul_of_nonneg_left hqlo hδ.le
    have hratio : 2*E^(2 : ℕ)*(1+Real.log M)/q ≤ δ/4 := by
      apply (div_le_iff₀ hpR).mpr
      nlinarith only [hleft,hright]
    have hh := mul_le_mul_of_nonneg_right hratio (sq_nonneg (M:ℝ))
    have he : (2*E^(2 : ℕ)*(1+Real.log M)/q)*(M:ℝ)^(2 : ℕ)=
        2*E^(2 : ℕ)*(M:ℝ)^(2 : ℕ)*(1+Real.log M)/q := by ring
    rw [he] at hh
    linarith only [hcoarse,hh]
  have hbase : mobiusDivisorFiniteClockEnergy 1 M Q+R^(2 : ℕ)*M ≤
      (E^(2 : ℕ)+R^(2 : ℕ))*(M:ℝ)^(2 : ℕ)*(1+Real.log M) := by
    have hs := clock_amplitude_bound Q hQ hM
    have hs' : mobiusDivisorFiniteClockEnergy 1 M Q ≤ E^(2 : ℕ)*(M:ℝ)^(2 : ℕ)*(1+Real.log M) := by
      apply hs.trans
      gcongr
    have hscale : (M:ℝ) ≤ (M:ℝ)^(2 : ℕ)*(1+Real.log M) := by nlinarith only [hMr,hw]
    have hh := mul_le_mul_of_nonneg_left hscale (sq_nonneg R)
    nlinarith only [hs',hh]
  refine ⟨l,hqP,hqnot,hnd,hlen,hpool,?_,hendpair,?_⟩
  · intro k L hML hgap
    have ht := htrans (Q∪(l.take k).toFinset) ((hprefix k).trans hbase) L hML hgap
    change mobiusDivisorFiniteClockEnergy 1 L (Q∪(l.take k).toFinset) ≤
      mobiusDivisorFiniteClockEnergy 1 M P+R^(2 : ℕ)*M+(δ/2)*(M:ℝ)^(2 : ℕ)
    change mobiusDivisorFiniteClockEnergy 1 L (Q∪(l.take k).toFinset) ≤
      mobiusDivisorFiniteClockEnergy 1 M (Q∪(l.take k).toFinset)+(δ/4)*(M:ℝ)^(2 : ℕ) at ht
    linarith only [ht,hprefix k,hcost]
  · intro L hML hgap
    have hlog : 0 ≤ 1+Real.log (2:ℝ) := by positivity
    have hpair0 : 0 ≤ (mobiusDivisorSelectionFibre M Q ∅)^(2 : ℕ)+
        (1+Real.log 2)*(mobiusDivisorSelectionFibre M Q {2})^(2 : ℕ) := by positivity
    have hδsq : 0 ≤ δ*(M:ℝ)^(2 : ℕ) := by positivity
    have hpad : 0 ≤ R^(2 : ℕ)*(M:ℝ) := by positivity
    have hW : mobiusDivisorFiniteClockEnergy 1 M (Q∪l.toFinset) ≤
        (E^(2 : ℕ)+R^(2 : ℕ))*(M:ℝ)^(2 : ℕ)*(1+Real.log M) := by
      linarith only [hpay,hpair0,hδsq,hpad,hbase]
    have ht := htrans (Q∪l.toFinset) hW L hML hgap
    change mobiusDivisorFiniteClockEnergy 1 L (Q∪l.toFinset) ≤
      mobiusDivisorFiniteClockEnergy 1 M (Q∪l.toFinset)+(δ/4)*(M:ℝ)^(2 : ℕ) at ht
    change mobiusDivisorFiniteClockEnergy 1 L (Q∪l.toFinset)+
      (mobiusDivisorSelectionFibre M Q ∅)^(2 : ℕ)+
      (1+Real.log 2)*(mobiusDivisorSelectionFibre M Q {2})^(2 : ℕ)+
      (δ/2)*(M:ℝ)^(2 : ℕ) ≤ mobiusDivisorFiniteClockEnergy 1 M P
    linarith only [ht,hpay,hcost]


private lemma eventually_logarithmic_window_small (A : ℝ) :
    ∀ᶠ M : ℕ in atTop, 32*A*(1+Real.log (M:ℝ)) < M := by
  have hn : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun M : ℕ => (1:ℝ)/(M:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp hn
  have hl : Tendsto (fun M : ℕ => Real.log (M:ℝ)/(M:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn
  have ht : Tendsto (fun M : ℕ => 32*A*((1+Real.log (M:ℝ))/(M:ℝ))) atTop (𝓝 0) := by
    simpa only [add_div,mul_zero,zero_add] using (hi.add hl).const_mul (32*A)
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    eventually_ge_atTop (1:ℕ)] with M h hM
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hh : 32*A*(1+Real.log (M:ℝ))/(M:ℝ) < 1 := by simpa only [mul_div_assoc] using h
  exact (div_lt_one hMr).mp hh

/-- The explicit retained-depth lower bound in the producer diverges. -/
theorem tendsto_mobiusDivisorLogarithmicChildDepth (A : ℝ) (hA : 0 < A) :
    Tendsto (fun M : ℕ => (M:ℝ)/(2*A*(1+Real.log M))-1) atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards [eventually_logarithmic_window_small ((K+1)*A/16),
    eventually_ge_atTop (1:ℕ)] with M h hM
  have hw : 0 < 1+Real.log (M:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ M by exact_mod_cast hM)
    linarith
  have hden : 0 < 2*A*(1+Real.log M) := by positivity
  have hh : (K+1)*(2*A*(1+Real.log M)) < (M:ℝ) := by
    nlinarith only [h]
  have hdiv := (lt_div_iff₀ hden).mpr hh
  linarith only [hdiv]

/-- An actual omitted prime at logarithmic size is selected and paid at each
sufficiently large current clock. Its retained child depth has the explicit
lower bound `M/(2*A*(1+log M))-1`, and its complete extension pays every
original cutoff in the fourth-root interval. -/
theorem eventually_exists_mobiusDivisorLogarithmicPrime_paid_extension :
    ∃ b : ℕ, ∃ δ A : ℝ, 15 ≤ b ∧ 0 < δ ∧ 16 ≤ A ∧
      ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        ∃ q : ℕ, ∃ Q : Finset ℕ, (∀p ∈ Q,p.Prime) ∧ P ⊆ Q ∧ q ∈ Q ∧ q ∉ P ∧
          A*(1+Real.log M) < q ∧ (q:ℝ) < 2*A*(1+Real.log M) ∧
          (M:ℝ)/(2*A*(1+Real.log M))-1 ≤ (M/q:ℕ) ∧
          ∀ L : ℕ, M ≤ L → (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M) →
            mobiusDivisorFiniteClockEnergy 1 L Q+δ*(M:ℝ)^(2 : ℕ) ≤
              mobiusDivisorFiniteClockEnergy 1 M P := by
  obtain ⟨b,R,δ,A,hb,hR,hδ,hA,hproduce⟩ :=
    eventually_exists_mobiusDivisorGrowingDepthOmittedPrimePayment
  have hA0 : 0 < A := by linarith
  have hclock : Tendsto (fun N : ℕ => 14*(b+1)*N) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro N
    change N ≤ 14*(b+1)*N
    nlinarith
  have hn : Tendsto (fun N : ℕ => ((14*(b+1)*N:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hclock
  have hl : Tendsto (fun N : ℕ => Real.log ((14*(b+1)*N:ℕ):ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hp : Tendsto (fun N : ℕ => 1+Real.log ((14*(b+1)*N:ℕ):ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) hl
  have hX := hp.const_mul_atTop hA0
  have hprimes := hX.eventually (prime_between (by norm_num : (0:ℝ)<1))
  have hsmall := hclock.eventually (eventually_logarithmic_window_small A)
  refine ⟨b,δ,A,hb,hδ,hA,?_⟩
  filter_upwards [hproduce,hprimes,hsmall,eventually_ge_atTop (1:ℕ)] with N hprod hpr hsm hN
  let M := 14*(b+1)*N
  let P := mobiusDivisorCoupledTwoCore
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨q,hq,hqlo,hqhi⟩ := hpr
  change A*(1+Real.log M) < (q:ℝ) at hqlo
  have hqhi' : (q:ℝ) < 2*A*(1+Real.log M) := by
    change (q:ℝ) < (1+1)*(A*(1+Real.log M)) at hqhi
    nlinarith only [hqhi]
  have hqM : 16*q ≤ M := by
    change 32*A*(1+Real.log M) < (M:ℝ) at hsm
    have hh : 16*(q:ℝ) ≤ (M:ℝ) := by nlinarith only [hqhi',hsm]
    exact_mod_cast hh
  obtain ⟨l,hqP,hqnot,hnd,hlen,hpool,hprefix,hpair,hpaid⟩ := hprod q hq hqlo.le hqM
  let Q := (insert q P)∪l.toFinset
  have hQ : ∀p ∈ Q,p.Prime := by
    intro p hpQ
    rcases mem_union.mp hpQ with hp | hp
    · rcases mem_insert.mp hp with rfl | hp
      · exact hq
      · exact (mem_filter.mp (mem_erase.mp hp).2).2
    · obtain ⟨K,_,_,hp,_,_,_,_⟩ := mobiusDivisorCoupledTwoPool_data hb hN (hpool hp)
      exact hp
  have hdep : (M:ℝ)/(2*A*(1+Real.log M))-1 ≤ (M/q:ℕ) := by
    have hw : 0 < 1+Real.log (M:ℝ) := by
      have := Real.log_nonneg hMr
      linarith
    have hden : 0 < 2*A*(1+Real.log M) := by positivity
    have hdiv : M < (M/q+1)*q :=
      (Nat.div_lt_iff_lt_mul hq.pos).mp (Nat.lt_succ_self (M/q))
    have hdiv' : (M:ℝ) < ((M/q:ℕ)+1:ℝ)*(q:ℝ) := by exact_mod_cast hdiv
    have hh := mul_lt_mul_of_pos_left hqhi' (show (0:ℝ) < ((M/q:ℕ):ℝ)+1 by positivity)
    have hh' : (M:ℝ) < (((M/q:ℕ):ℝ)+1)*(2*A*(1+Real.log M)) := hdiv'.trans hh
    have hx := (div_lt_iff₀ hden).mpr hh'
    linarith only [hx]
  refine ⟨q,Q,hQ,(subset_insert q P).trans subset_union_left,
    mem_union_left _ (mem_insert_self _ _),hqP,hqlo,hqhi',hdep,?_⟩
  intro L hML hgap
  have h := hpaid L hML hgap
  have hlog : 0 ≤ 1+Real.log (2:ℝ) := by
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    linarith
  have hn : 0 ≤ (mobiusDivisorSelectionFibre M (insert q P) ∅)^(2 : ℕ)+
      (1+Real.log 2)*(mobiusDivisorSelectionFibre M (insert q P) {2})^(2 : ℕ) := by positivity
  change mobiusDivisorFiniteClockEnergy 1 L Q+δ*(M:ℝ)^(2 : ℕ) ≤ _
  linarith only [h,hn]

end RHTower
