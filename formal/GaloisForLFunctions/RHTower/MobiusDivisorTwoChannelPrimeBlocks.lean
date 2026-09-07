import GaloisForLFunctions.RHTower.MobiusDivisorLargePrimeOrientation

/-!
# Initial prime blocks with two active cofactor channels

For primes satisfying `2*M <= 5*p`, the cofactor-two expenditure is at most
half the head expenditure. The exact smooth-mean bounds give mutual factor-two
comparison for all parent channels whose quotients exceed a common threshold.
Distinct primes in this sector have no joint active source coefficient. Their
block therefore subtracts literal unsigned expenditures from each surviving
oriented fibre. A head budget controls every fibre, complete energy, nonempty
energy, and every available one-prime extension at every intermediate subset.

These are actual-source statements. The head-budget condition is not supplied
by this leaf; the following prime-supply leaf supplies a nonempty initial block.
A complete growing schedule and RH remain open.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower


private theorem source_first_two_nonneg :
    1/10 ≤ primeFreeDivisorDefect 1 ∧ 0 ≤ primeFreeDivisorDefect 2 := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    norm_num
  norm_num [harmonic,Finset.sum_range_succ,hlog] at h
  have hg : (5768/10000:ℝ) ≤ Real.eulerMascheroniConstant := by
    linarith [Real.log_two_lt_d9]
  constructor <;> norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top] <;>
    linarith [Real.log_two_gt_d9]

private theorem unsigned_zero_of_cutoff {M d : ℕ} (hd : 0<d) (hMd : M≤d) :
    divisorUnsignedDilationChannel M d=0 := by
  simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<d)]

private theorem source_second_block {M p : ℕ} (hp : 0<p) (hlo : 2*p≤M) (hhi : M≤3*p) :
    divisorUnsignedDilationChannel M p =
      Real.sqrt p*(Real.sqrt 2-1)*primeFreeDivisorDefect 1+
        (Real.sqrt M-Real.sqrt (2*p:ℕ))*primeFreeDivisorDefect 2 := by
  have h := divisorUnsignedDilationChannel_mul_add p 2 (M-2*p) 1 hp (by omega)
  have hM : p*2+(M-2*p)=M := by omega
  have hK : divisorUnsignedDilationChannel 2 1=(Real.sqrt 2-1)*primeFreeDivisorDefect 1 := by
    simpa using (divisorUnsignedDilationChannel_eq_first_block (M := 2) (d := 1)
      (by omega) (by omega) (by omega))
  rw [hM] at h
  simpa only [Nat.mul_one,hK,Nat.mul_comm p 2,Nat.div_one,mul_assoc] using h

/-- In the two-fifths sector, the actual cofactor-two expenditure is at most half the head expenditure. -/
theorem divisorUnsignedDilationChannel_double_le_half_of_two_mul_le_five_mul
    {M p : ℕ} (hp : 0<p) (hMp : 2*M≤5*p) :
    2*divisorUnsignedDilationChannel M (2*p) ≤ divisorUnsignedDilationChannel M p := by
  by_cases hlo : M≤2*p
  · rw [unsigned_zero_of_cutoff (by omega : 0<2*p) hlo]
    simpa using divisorUnsignedDilationChannel_nonneg M p
  have h2 : 2*p<M := by omega
  rw [divisorUnsignedDilationChannel_eq_first_block (by omega : 1≤2*p) h2 (by omega),
    source_second_block hp (by omega) (by omega)]
  have hr2lo : (7/5:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr2hi : Real.sqrt 2 ≤ (3/2:ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hMr : (M:ℝ) ≤ (5/2:ℝ)*p := by
    have h : 2*(M:ℝ)≤5*p := by exact_mod_cast hMp
    linarith only [h]
  have hroot : Real.sqrt M ≤ (8/5:ℝ)*Real.sqrt p := by
    have hsM := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)
    have hsp := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
    nlinarith [Real.sqrt_nonneg (M:ℝ),Real.sqrt_nonneg (p:ℝ)]
  have he : Real.sqrt (2*p:ℕ)=Real.sqrt 2*Real.sqrt p := by
    rw [Nat.cast_mul,Real.sqrt_mul (by norm_num)]; norm_num
  have hgap : 2*(Real.sqrt M-Real.sqrt (2*p:ℕ)) ≤ Real.sqrt p*(Real.sqrt 2-1) := by
    have hm := mul_le_mul_of_nonneg_right hr2lo (Real.sqrt_nonneg (p:ℝ))
    rw [he]
    nlinarith only [hroot,hm]
  have hposgap : 0≤Real.sqrt M-Real.sqrt (2*p:ℕ) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast h2.le))
  have hD1 : 0≤primeFreeDivisorDefect 1 := by linarith only [source_first_two_nonneg.1]
  have hbound := mul_le_mul_of_nonneg_right hgap hD1
  have htail := mul_nonneg hposgap source_first_two_nonneg.2
  nlinarith only [hbound,htail]

/-- The entire second quotient block has a positive analytic square-root source floor. -/
theorem divisorUnsignedDilationChannel_second_block_lower {M p : ℕ}
    (hp : 0<p) (hlo : 2*p≤M) (hhi : M≤3*p) :
    Real.sqrt p/40 ≤ divisorUnsignedDilationChannel M p := by
  rw [source_second_block hp hlo hhi]
  have hs2 : (5/4:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hgap : 0≤Real.sqrt M-Real.sqrt (2*p:ℕ) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast hlo))
  have htail := mul_nonneg hgap source_first_two_nonneg.2
  have hroot := Real.sqrt_nonneg (p:ℝ)
  have hw : Real.sqrt p/4≤Real.sqrt p*(Real.sqrt 2-1) := by
    have h := mul_le_mul_of_nonneg_left hs2 hroot
    nlinarith only [h]
  have hD := mul_le_mul_of_nonneg_left source_first_two_nonneg.1
    (show 0≤Real.sqrt p*(Real.sqrt 2-1) by nlinarith only [hw,hroot])
  nlinarith only [htail,hw,hD]

private theorem unsigned_band_transfer (M d T : ℕ) (L U : ℝ) (hd : 0<d)
    (hN : T≤M/d)
    (hT : ∀ N : ℕ,T≤N → L*Real.sqrt N≤divisorUnsignedDilationChannel N 1 ∧
      divisorUnsignedDilationChannel N 1≤U*Real.sqrt N) :
    L*Real.sqrt M≤divisorUnsignedDilationChannel M d ∧
      divisorUnsignedDilationChannel M d≤U*Real.sqrt M := by
  have hw0 := divisorPrimeClipWeight_nonneg M d hd
  have hw1 : 0≤1-divisorPrimeClipWeight M d := by
    have h := divisorPrimeClipWeight_lt_one M d hd; linarith only [h]
  have hA := hT (M/d) hN
  have hB := hT (M/d+1) (by omega)
  have hlo := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA.1 hw1) (mul_le_mul_of_nonneg_left hB.1 hw0))
    (Real.sqrt_nonneg (d:ℝ))
  have hhi := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA.2 hw1) (mul_le_mul_of_nonneg_left hB.2 hw0))
    (Real.sqrt_nonneg (d:ℝ))
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd
  simp only [Nat.mul_one] at hc
  have hw := divisorPrimeClipWeight_mul_step M d hd
  push_cast at hw
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hw
  have hlw := congrArg (fun x : ℝ => L*x) hw
  have huw := congrArg (fun x : ℝ => U*x) hw
  rw [hc]
  push_cast at hlo hhi ⊢
  constructor <;> nlinarith only [hlo,hhi,hlw,huw]

/-- Any two channels with sufficiently large quotients are comparable by a common factor two, including both clipped terminal blocks. -/
theorem exists_divisorUnsignedDilationChannel_mutual_large_quotient_comparison :
    ∃ T : ℕ,1≤T ∧ ∀ M d e : ℕ,0<d → 0<e → T≤M/d → T≤M/e →
      divisorUnsignedDilationChannel M d≤2*divisorUnsignedDilationChannel M e := by
  let a := divisorHyperbolaSmoothMean
  let ε := (a-1/6)/4
  have hε : 0<ε := by dsimp [ε,a]; linarith only [divisorHyperbolaSmoothMean_gt_one_sixth]
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_divisorUnsignedDilationChannel_one_exact_mean_bounds ε hε)
  refine ⟨max T 1,le_max_right _ _,?_⟩
  intro M d e hd he hMd hMe
  have hbD := unsigned_band_transfer M d T (a-5/48-ε) (a-1/24+ε) hd
    ((le_max_left _ _).trans hMd) hT
  have hbE := unsigned_band_transfer M e T (a-5/48-ε) (a-1/24+ε) he
    ((le_max_left _ _).trans hMe) hT
  have hgap : a-1/24+ε≤2*(a-5/48-ε) := by
    dsimp [ε,a]; linarith only [divisorHyperbolaSmoothMean_gt_one_sixth]
  have hm := mul_le_mul_of_nonneg_right hgap (Real.sqrt_nonneg (M:ℝ))
  nlinarith only [hbD.2,hbE.1,hm]

private theorem oriented_zero_of_processed_label (M : ℕ) (P R : Finset ℕ)
    {p : ℕ} (hpP : p∈P) (hpR : p∈R) : mobiusDivisorOrientedFibre M P R=0 := by
  unfold mobiusDivisorOrientedFibre mobiusDivisorSelectionFibre subsetLabelFibre
  have hz : (∑ d ∈ mobiusDivisorSelectionIndices M,
      if d.primeFactors \ P=R then mobiusDivisorDilationChannel M d else 0)=0 := by
    apply sum_eq_zero
    intro d hd
    have he : d.primeFactors \ P≠R := by
      intro he
      exact (mem_sdiff.mp (he.symm ▸ hpR)).2 hpP
    simp only [if_neg he]
  rw [hz,mul_zero]

private theorem oriented_zero_of_nonprime_label (M : ℕ) (P R : Finset ℕ)
    {p : ℕ} (hpR : p∈R) (hp : ¬p.Prime) : mobiusDivisorOrientedFibre M P R=0 := by
  unfold mobiusDivisorOrientedFibre mobiusDivisorSelectionFibre subsetLabelFibre
  have hz : (∑ d ∈ mobiusDivisorSelectionIndices M,
      if d.primeFactors \ P=R then mobiusDivisorDilationChannel M d else 0)=0 := by
    apply sum_eq_zero
    intro d hd
    have he : d.primeFactors \ P≠R := by
      intro he
      exact hp (Nat.prime_of_mem_primeFactors (mem_sdiff.mp (he.symm ▸ hpR)).1)
    simp only [if_neg he]
  rw [hz,mul_zero]

/-- Without active joint prime products, every surviving oriented fibre is its original channel minus the literal block expenditures. -/
theorem mobiusDivisorOrientedFibre_sparse_prime_block (M : ℕ) (P R : Finset ℕ)
    (hP : ∀ p∈P,p.Prime)
    (hpair : ∀ p∈P,∀ q∈P,p≠q → M≤p*q)
    (hR : ∀ r∈R,r.Prime) (hdis : Disjoint R P) :
    mobiusDivisorOrientedFibre M P R = divisorUnsignedDilationChannel M (∏ r∈R,r)-
      ∑ p∈P,divisorUnsignedDilationChannel M (p*(∏ r∈R,r)) := by
  induction P using Finset.induction_on generalizing R with
  | empty => simp only [sum_empty,sub_zero,mobiusDivisorOrientedFibre_empty_eq_unsigned_product R hR]
  | @insert p P hpP ih =>
    have hp := hP p (mem_insert_self p P)
    have hP' : ∀ q∈P,q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hpair' : ∀ q∈P,∀ t∈P,q≠t → M≤q*t :=
      fun q hq t ht hqt => hpair q (mem_insert_of_mem hq) t (mem_insert_of_mem ht) hqt
    have hpR : p∉R := fun h => disjoint_left.mp hdis h (mem_insert_self p P)
    have hdis0 : Disjoint R P := disjoint_left.mpr
      (fun r hr hp => disjoint_left.mp hdis hr (mem_insert_of_mem hp))
    have hdis1 : Disjoint (insert p R) P := by
      apply disjoint_left.mpr
      intro r hr hrP
      rcases mem_insert.mp hr with hr|hr
      · exact hpP (hr ▸ hrP)
      · exact disjoint_left.mp hdis0 hr hrP
    have hd : 0<∏ r∈R,r := prod_pos (fun r hr => (hR r hr).pos)
    have hz : (∑ q∈P,divisorUnsignedDilationChannel M (q*(∏ r∈insert p R,r)))=0 := by
      apply sum_eq_zero
      intro q hq
      rw [prod_insert hpR]
      apply unsigned_zero_of_cutoff (by have := (hP' q hq).pos; have := hp.pos; positivity)
      have hqp : q≠p := fun h => hpP (h ▸ hq)
      have hM := hpair q (mem_insert_of_mem hq) p (mem_insert_self p P) hqp
      have hmul := Nat.mul_le_mul_left (q*p) (show 1≤∏ r∈R,r from hd)
      nlinarith only [hM,hmul]
    rw [mobiusDivisorOrientedFibre_insert M P R p hpR,
      ih R hP' hpair' hR hdis0,
      ih (insert p R) hP' hpair' (by simpa using And.intro hp hR) hdis1,
      hz,sub_zero,prod_insert hpR,sum_insert hpP]
    ring

private theorem two_fifths_pairwise {M : ℕ} (hM : 10≤M) (P : Finset ℕ)
    (hP : ∀ p∈P,2*M≤5*p) : ∀ p∈P,∀ q∈P,p≠q → M≤p*q := by
  intro p hp q hq _
  have hpp := hP p hp
  have hqq := hP q hq
  have hp4 : 4≤p := by omega
  have hqp := Nat.mul_le_mul_left p hqq
  nlinarith only [hpp,hqp,hp4]

private theorem two_channel_parity (M : ℕ) (hM : 10≤M) (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime ∧ 2*M≤5*p)
    (hreserve : divisorUnsignedDilationChannel M 1≤2*divisorUnsignedDilationChannel M 2)
    (hbudget : (∑ p∈P,divisorUnsignedDilationChannel M p)≤divisorUnsignedDilationChannel M 1)
    (R : Finset ℕ) : 0 ≤ mobiusDivisorOrientedFibre M P R := by
  by_cases hdis : Disjoint R P
  · by_cases hR : ∀ r∈R,r.Prime
    · rw [mobiusDivisorOrientedFibre_sparse_prime_block M P R (fun p hp => (hP p hp).1)
        (two_fifths_pairwise hM P (fun p hp => (hP p hp).2)) hR hdis]
      let d := ∏ r∈R,r
      change 0≤divisorUnsignedDilationChannel M d-∑ p∈P,divisorUnsignedDilationChannel M (p*d)
      have hd : 0<d := prod_pos (fun r hr => (hR r hr).pos)
      by_cases hd1 : d=1
      · simpa only [hd1,Nat.mul_one] using sub_nonneg.mpr hbudget
      by_cases hd2 : d=2
      · have hs : 2*(∑ p∈P,divisorUnsignedDilationChannel M (p*2))≤
            ∑ p∈P,divisorUnsignedDilationChannel M p := by
          rw [mul_sum]
          apply sum_le_sum
          intro p hp
          simpa only [Nat.mul_comm p 2] using
            divisorUnsignedDilationChannel_double_le_half_of_two_mul_le_five_mul
              (hP p hp).1.pos (hP p hp).2
        rw [hd2]
        linarith only [hs,hbudget,hreserve]
      · have hz : (∑ p∈P,divisorUnsignedDilationChannel M (p*d))=0 := by
          apply sum_eq_zero
          intro p hp
          have hp0 := (hP p hp).1.pos
          apply unsigned_zero_of_cutoff (by positivity)
          have ht := (hP p hp).2
          have hd3 : 3≤d := by omega
          nlinarith only [ht,hd3,hp0]
        rw [hz,sub_zero]
        exact divisorUnsignedDilationChannel_nonneg M d
    · push Not at hR
      obtain ⟨p,hpR,hp⟩ := hR
      rw [oriented_zero_of_nonprime_label M P R hpR hp]
  · have hex : ∃ p∈R,p∈P := by simpa only [disjoint_left,not_forall,not_not,exists_prop] using hdis
    obtain ⟨p,hpR,hpP⟩ := hex
    rw [oriented_zero_of_processed_label M P R hpP hpR]

private theorem sparse_block_oriented_le (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (hpair : ∀ p∈P,∀ q∈P,p≠q → M≤p*q) (R : Finset ℕ) :
    mobiusDivisorOrientedFibre M P R≤ mobiusDivisorOrientedFibre M ∅ R := by
  by_cases hdis : Disjoint R P
  · by_cases hR : ∀ r∈R,r.Prime
    · rw [mobiusDivisorOrientedFibre_sparse_prime_block M P R hP hpair hR hdis,
        mobiusDivisorOrientedFibre_empty_eq_unsigned_product R hR]
      exact sub_le_self _ (sum_nonneg (fun p _ => divisorUnsignedDilationChannel_nonneg M _))
    · push Not at hR
      obtain ⟨p,hpR,hp⟩ := hR
      rw [oriented_zero_of_nonprime_label M P R hpR hp,oriented_zero_of_nonprime_label M ∅ R hpR hp]
  · have hex : ∃ p∈R,p∈P := by simpa only [disjoint_left,not_forall,not_not,exists_prop] using hdis
    obtain ⟨p,hpR,hpP⟩ := hex
    rw [oriented_zero_of_processed_label M P R hpP hpR]
    exact mobiusDivisorSelectionFibre_empty_parity_nonneg M R

/-- Above one universal cutoff, a head-budgeted two-channel prime block preserves all signs and both energy ceilings at every subset; every available next prime contracts. -/
theorem exists_mobiusDivisorTwoChannelBlockParity :
    ∃ M₀ : ℕ,∀ M : ℕ,M₀≤M → ∀ L : Finset ℕ,
      (∀ p∈L,p.Prime ∧ p<M ∧ 2*M≤5*p) →
      (∑ p∈L,divisorUnsignedDilationChannel M p)≤divisorUnsignedDilationChannel M 1 →
      ∀ P⊆L,
        (∀ R : Finset ℕ,0 ≤ mobiusDivisorOrientedFibre M P R ∧
          mobiusDivisorOrientedFibre M P R≤ mobiusDivisorOrientedFibre M ∅ R) ∧
        mobiusDivisorSelectionEnergy M P≤ mobiusDivisorSelectionEnergy M ∅ ∧
        mobiusDivisorNonemptyEnergy M P≤ mobiusDivisorNonemptyEnergy M ∅ ∧
        ∀ q : ℕ,q.Prime → q<M → q∉P →
          mobiusDivisorSelectionEnergy M (insert q P)≤ mobiusDivisorSelectionEnergy M P := by
  obtain ⟨T,hT,hcomp⟩ := exists_divisorUnsignedDilationChannel_mutual_large_quotient_comparison
  refine ⟨max 10 (2*T),?_⟩
  intro M hM L hL hbudget P hPL
  have hM10 : 10≤M := (le_max_left _ _).trans hM
  have hM2 : 2*T≤M := (le_max_right _ _).trans hM
  have hreserve : divisorUnsignedDilationChannel M 1≤2*divisorUnsignedDilationChannel M 2 :=
    hcomp M 1 2 (by omega) (by omega) (by omega)
      ((Nat.le_div_iff_mul_le (by omega : 0<2)).mpr (by omega))
  have hP : ∀ p∈P,p.Prime ∧ 2*M≤5*p :=
    fun p hp => ⟨(hL p (hPL hp)).1,(hL p (hPL hp)).2.2⟩
  have hsub := sum_le_sum_of_subset_of_nonneg hPL
    (fun p _ _ => divisorUnsignedDilationChannel_nonneg M p)
  have hor : ∀ R : Finset ℕ,0 ≤ mobiusDivisorOrientedFibre M P R ∧
      mobiusDivisorOrientedFibre M P R≤ mobiusDivisorOrientedFibre M ∅ R := by
    intro R
    exact ⟨two_channel_parity M hM10 P hP hreserve (hsub.trans hbudget) R,
      sparse_block_oriented_le M P (fun p hp => (hP p hp).1)
        (two_fifths_pairwise hM10 P (fun p hp => (hP p hp).2)) R⟩
  have hsq (R : Finset ℕ) : (mobiusDivisorSelectionFibre M P R)^2≤
      (mobiusDivisorSelectionFibre M ∅ R)^2 := by
    rw [← mobiusDivisorOrientedFibre_sq,← mobiusDivisorOrientedFibre_sq]
    have ha := (hor R).1
    have hb := (hor R).2
    have hc := mul_nonneg (sub_nonneg.mpr hb) (add_nonneg ha (ha.trans hb))
    nlinarith only [hc]
  refine ⟨hor,?_,?_,?_⟩
  · change (∑ R∈(mobiusDivisorSelectionPrimes M).powerset,(mobiusDivisorSelectionFibre M P R)^2)≤
      ∑ R∈(mobiusDivisorSelectionPrimes M).powerset,(mobiusDivisorSelectionFibre M ∅ R)^2
    exact sum_le_sum (fun R _ => hsq R)
  · rw [mobiusDivisorNonemptyEnergy_eq_sum,mobiusDivisorNonemptyEnergy_eq_sum]
    exact sum_le_sum (fun R _ => hsq R)
  · intro q hq hqM hqP
    exact mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg M P hq hqM hqP
      (fun R => (hor R).1)

end RHTower
