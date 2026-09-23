import GaloisForLFunctions.RHTower.MobiusDivisorFiniteClockCountingCancellation
import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedPrimePairReserve
import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import GaloisForLFunctions.RHTower.MobiusDivisorQuotientWindowOrder

/-!
# Prescribed prime insertions paying a complete finite clock block

At every finite prime core, every sufficiently large prescribed prime can
be included using at most two new primes. The resulting strict source
coefficient reserve pays the actual logarithmically weighted action at
every integer clock wall from `M` to `k*M`, for each fixed positive integer
growth factor and every sufficiently large starting cutoff.

The proof retains the finite counting measure. Its exact clock defect is
`sum_r log(M/r) * r * F_P(M,r)^(2 : ℕ)`; the source amplitude and square-root
telescoping bound this defect by a core-dependent multiple of `M^(2 : ℕ)`.
Strict coefficient release then dominates both this defect and `log k`.

The prescribed-prime threshold depends on the core. The starting cutoff
also depends on the chosen extension and the growth factor. No exhaustive
history, bounded initial action, or global cumulative payment is asserted.

At a given cutoff, arbitrary helper sets with bounded child quotient leave
all but an explicitly counted set of old samples unchanged. This bounds
their possible clock payment without any helper-cardinality assumption.
The complete fixed-core clock has the same leading logarithmic coefficient
as the full unweighted source energy.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma logarithmic_count (M : ℕ) :
    (∑ r ∈ Icc 1 M, (Real.log M-Real.log r)) ≤ 4*(M:ℝ) := by
  rcases M.eq_zero_or_pos with rfl | hM
  · simp
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  calc
    _ ≤ ∑ r ∈ Icc 1 M, (2*Real.sqrt M)*(1/Real.sqrt r) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hr,hrM⟩ := mem_Icc.mp hr
      have hrR : (0:ℝ)<r := by exact_mod_cast hr
      have hx : 0<(M:ℝ)/r := div_pos hMR hrR
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
      rw [Real.log_sqrt hx.le,Real.log_div hMR.ne' hrR.ne'] at h
      have hs := Real.sqrt_div hMR.le (y:=(r:ℝ))
      rw [hs] at h
      simp only [div_eq_mul_inv,one_mul] at h ⊢
      nlinarith
    _ = 2*Real.sqrt M * ∑ r ∈ Icc 1 M, 1/Real.sqrt r := by rw [mul_sum]
    _ ≤ 2*Real.sqrt M*(2*Real.sqrt M) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_le M) (by positivity)
    _ = _ := by nlinarith [Real.sq_sqrt hMR.le]

private lemma source_term_bound (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (M : ℕ) {r : ℕ} (hr : r∈fixedCoreSquarefreeIndices P M) :
    (r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ) ≤
      ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)*(M:ℝ) := by
  obtain ⟨_,hsf,hd⟩ := mem_filter.mp hr
  have he := mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hd
  rw [Nat.prod_primeFactors_of_squarefree hsf] at he
  have hm : (((ArithmeticFunction.moebius r : ℤ):ℝ))^(2 : ℕ)=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  have hs := congrArg (fun x : ℝ => x^(2 : ℕ)) he
  simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg r),hm,mul_one] at hs
  rw [← hs]
  have hb := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P r.primeFactors hP
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg M)
  have hab := abs_nonneg (mobiusDivisorSelectionFibre M P r.primeFactors)
  have ha := sq_abs (mobiusDivisorSelectionFibre M P r.primeFactors)
  nlinarith [sq_nonneg (((3/5:ℝ)*2^(P.card-1))*Real.sqrt M-
    |mobiusDivisorSelectionFibre M P r.primeFactors|)]

private lemma clock_defect (P : Finset ℕ) (hP : ∀p∈P,p.Prime) (M : ℕ) :
    0 ≤ (1+Real.log M)*mobiusDivisorSelectionEnergy M P-
      mobiusDivisorFiniteClockEnergy 1 M P ∧
    (1+Real.log M)*mobiusDivisorSelectionEnergy M P-
      mobiusDivisorFiniteClockEnergy 1 M P ≤
      4*((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)*(M:ℝ)^(2 : ℕ) := by
  let S := fixedCoreSquarefreeIndices P M
  let C : ℝ := ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)
  have he : (1+Real.log M)*mobiusDivisorSelectionEnergy M P-
      mobiusDivisorFiniteClockEnergy 1 M P =
      ∑ r∈S,(Real.log M-Real.log r)*((r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ)) := by
    rw [mobiusDivisorSelectionEnergy_eq_inclusive_squarefree,mobiusDivisorFiniteClockEnergy,
      mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro r hr
    ring
  rw [he]
  have hlo (r : ℕ) (hr : r∈Icc 1 M) : 0≤Real.log M-Real.log r := by
    obtain ⟨hr,hrM⟩ := mem_Icc.mp hr
    exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hr) (by exact_mod_cast hrM))
  have hs : S ⊆ Icc 1 M := filter_subset _ _
  constructor
  · exact sum_nonneg (fun r hr => mul_nonneg (hlo r (hs hr)) (by positivity))
  calc
    _ ≤ ∑ r∈S,(Real.log M-Real.log r)*(C*(M:ℝ)) := by
      apply sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (source_term_bound P hP M hr) (hlo r (hs hr))
    _ = (C*(M:ℝ)) * ∑ r∈S,(Real.log M-Real.log r) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (C*(M:ℝ)) * ∑ r∈Icc 1 M,(Real.log M-Real.log r) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      exact sum_le_sum_of_subset_of_nonneg hs (fun r hr _ => hlo r hr)
    _ ≤ (C*(M:ℝ)) * (4*(M:ℝ)) :=
      mul_le_mul_of_nonneg_left (logarithmic_count M) (by dsimp [C]; positivity)
    _ = _ := by dsimp [C]; ring

private lemma clock_comparison (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    {M : ℕ} (hM : 0<M) :
    (1+Real.log M)*(mobiusDivisorSelectionEnergy M P/(M:ℝ)^(2 : ℕ))-
        4*((3/5:ℝ)*2^(P.card-1))^(2 : ℕ) ≤ mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^(2 : ℕ) ∧
    mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^(2 : ℕ) ≤
      (1+Real.log M)*(mobiusDivisorSelectionEnergy M P/(M:ℝ)^(2 : ℕ)) := by
  obtain ⟨hlo,hhi⟩ := clock_defect P hP M
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  have hp := pow_pos hMR 2
  have hlo' := div_nonneg hlo hp.le
  have hhi' := (div_le_iff₀ hp).mpr hhi
  have he : ((1+Real.log M)*mobiusDivisorSelectionEnergy M P-
      mobiusDivisorFiniteClockEnergy 1 M P)/(M:ℝ)^(2 : ℕ) =
      (1+Real.log M)*(mobiusDivisorSelectionEnergy M P/(M:ℝ)^(2 : ℕ))-
        mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^(2 : ℕ) := by ring
  rw [he] at hlo' hhi'
  constructor <;> linarith

private lemma clock_block_release (P Q : Finset ℕ)
    (hP : ∀p∈P,p.Prime) (hQ : ∀p∈Q,p.Prime)
    (hgap : (∑' n,mobiusDivisorFixedCoreBlockMass Q n) <
      ∑' n,mobiusDivisorFixedCoreBlockMass P n)
    (k : ℕ) (hk : 1≤k) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ M : ℕ in atTop, ∀ L : ℕ, M≤L → L≤k*M →
      mobiusDivisorFiniteClockEnergy 1 L Q/(L:ℝ)^(2 : ℕ)+c*Real.log M ≤
        mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^(2 : ℕ) := by
  let a := ∑' n,mobiusDivisorFixedCoreBlockMass P n
  let b := ∑' n,mobiusDivisorFixedCoreBlockMass Q n
  let d := a-b
  let ε := d/4
  let K := 4*((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)
  have hd : 0<d := sub_pos.mpr hgap
  have hε : 0<ε := by dsimp [ε]; positivity
  have hb : 0≤b := tsum_nonneg (mobiusDivisorFixedCoreBlockMass_nonneg Q hQ)
  have htP := (tendsto_mobiusDivisorSelectionEnergy_div_sq P hP).eventually
    (eventually_gt_nhds (show a-ε<a by linarith))
  have htQ := (tendsto_mobiusDivisorSelectionEnergy_div_sq Q hQ).eventually
    (eventually_lt_nhds (show b<b+ε by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp htQ
  have ht : Tendsto (fun M : ℕ => ε*Real.log M) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
  have htε := (tendsto_atTop.mp ht) (K+(b+ε)*Real.log k)
  refine ⟨ε,hε,?_⟩
  filter_upwards [htP,htε,eventually_ge_atTop (max N 1)] with M hPM hεM hM
  intro L hML hLk
  have hM1 : 1≤M := (le_max_right N 1).trans hM
  have hL1 : 1≤L := hM1.trans hML
  have hQM := (hN L ((le_max_left N 1).trans (hM.trans hML))).le
  have hlogM : 0≤Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have hlogL : 0≤Real.log L := Real.log_nonneg (by exact_mod_cast hL1)
  have hAP := (clock_comparison P hP (by omega : 0<M)).1
  have hAQ := (clock_comparison Q hQ (by omega : 0<L)).2
  have hPmul := mul_le_mul_of_nonneg_left hPM.le (show 0≤1+Real.log M by linarith)
  have hQmul := mul_le_mul_of_nonneg_left hQM (show 0≤1+Real.log L by linarith)
  have hlo : mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^(2 : ℕ) ≥
      (1+Real.log M)*(a-ε)-K := by dsimp [K]; linarith
  have hhi : mobiusDivisorFiniteClockEnergy 1 L Q/(L:ℝ)^(2 : ℕ) ≤
      (1+Real.log L)*(b+ε) := hAQ.trans hQmul
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hMR : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hLR : (0:ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hlog := Real.log_le_log hLR (show (L:ℝ)≤(k:ℝ)*M by exact_mod_cast hLk)
  rw [Real.log_mul hkR.ne' hMR.ne'] at hlog
  have hlogmul := mul_le_mul_of_nonneg_right hlog (show 0≤b+ε by linarith)
  dsimp [ε,d] at *
  nlinarith only [hlo,hhi,hlogmul,hεM,hd,hb]

private lemma prescribed_extension (P : Finset ℕ) (hprime : ∀p∈P,p.Prime) :
    ∃ T : ℕ, ∀ r : ℕ, r.Prime → T≤r → ∃ Q : Finset ℕ,
      (∀q∈Q,q.Prime) ∧ P⊆Q ∧ r∈Q ∧ r∉P ∧ Q.card≤P.card+2 ∧
      (∑' n,mobiusDivisorFixedCoreBlockMass Q n) <
        ∑' n,mobiusDivisorFixedCoreBlockMass P n := by
  by_cases hne : P.Nonempty
  · rcases Nat.even_or_odd P.card with he | ho
    · obtain ⟨c,T,hc,hpair⟩ := exists_mobiusDivisorEvenCore_prescribed_prime_pair_reserve
        P hne hprime he
      refine ⟨⌈T⌉₊,fun r hr hrT => ?_⟩
      have hrT' : T≤(r:ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast hrT)
      obtain ⟨p,hp,hpr,hpP,hrP,_,hpay⟩ := hpair r hr hrT'
      refine ⟨insert p (insert r P),?_,?_,by simp,hrP,?_,?_⟩
      · intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact hp
        rcases mem_insert.mp hq with rfl | hq
        · exact hr
        · exact hprime q hq
      · exact (subset_insert _ _).trans (subset_insert _ _)
      · have h₁ := card_insert_le r P
        have h₂ := card_insert_le p (insert r P)
        omega
      · have hh : 0<c/(r:ℝ) := div_pos hc (by exact_mod_cast hr.pos)
        linarith
    · obtain ⟨N,hN⟩ := eventually_atTop.mp
        (eventually_mobiusDivisorPrimeReleaseCoefficient_oriented_pos P hne hprime)
      refine ⟨max N (P.sup id+1),fun r hr hrT => ?_⟩
      have hrP : r∉P := by
        intro h
        have hsup : r≤P.sup id := le_sup (f:=id) h
        have := (le_max_right N (P.sup id+1)).trans hrT
        omega
      have hpay := hN r ((le_max_left N _).trans hrT) hr hrP
      rw [pow_succ,ho.neg_one_pow] at hpay
      norm_num at hpay
      refine ⟨insert r P,?_,subset_insert _ _,mem_insert_self _ _,hrP,?_,?_⟩
      · intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact hr
        · exact hprime q hq
      · have := card_insert_le r P
        omega
      · linarith
  · have hP : P=∅ := not_nonempty_iff_eq_empty.mp hne
    subst P
    obtain ⟨c,hc,N,_,hfirst⟩ := exists_mobiusDivisorSelectionEnergy_first_prime_reserve
    refine ⟨0,fun r hr _ => ?_⟩
    have hsingle : ∀q∈({r}:Finset ℕ),q.Prime := by simpa using hr
    have hlimit := (tendsto_mobiusDivisorSelectionEnergy_div_sq ∅ (by simp)).sub
      (tendsto_mobiusDivisorSelectionEnergy_div_sq {r} hsingle)
    have hlower : ∀ᶠ M : ℕ in atTop, c/(r:ℝ) ≤
        (mobiusDivisorSelectionEnergy M ∅-mobiusDivisorSelectionEnergy M {r})/(M:ℝ)^(2 : ℕ) := by
      filter_upwards [eventually_ge_atTop (N*r+1)] with M hM
      have hquot : N≤M/r := (Nat.le_div_iff_mul_le hr.pos).mpr (by omega)
      have hMR : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
      apply (le_div_iff₀ (pow_pos hMR 2)).mpr
      calc
        _ = c*(M:ℝ)^(2 : ℕ)/(r:ℝ) := by ring
        _ ≤ _ := hfirst M r hr hquot
    simp only [sub_div] at hlower
    have hh := ge_of_tendsto hlimit hlower
    have hc' : 0<c/(r:ℝ) := div_pos hc (by exact_mod_cast hr.pos)
    refine ⟨{r},hsingle,by simp,by simp,by simp,by simp,?_⟩
    linarith

/-- Include any sufficiently large prescribed prime with at most two fresh
prime insertions, then pay every integer cutoff in any fixed multiplicative
clock block. The positive margin is a literal source reserve, with no
correlation or action-bound premise. -/
theorem exists_mobiusDivisorPrescribedClockBlock (P : Finset Nat.Primes) :
    ∃ T : ℕ, ∀ r : Nat.Primes, T≤(r:ℕ) → ∃ Q : Finset ℕ,
      (∀q∈Q,q.Prime) ∧ P.image (fun p : Nat.Primes => (p:ℕ)) ⊆ Q ∧
      (r:ℕ)∈Q ∧ r∉P ∧ Q.card≤P.card+2 ∧
      ∀ k : ℕ, 1≤k → ∃ c : ℝ, 0<c ∧ ∀ᶠ M : ℕ in atTop,
        ∀ L : ℕ, M≤L → L≤k*M →
          mobiusDivisorFiniteClockEnergy 1 L Q/(L:ℝ)^(2 : ℕ)+c*Real.log M ≤
            mobiusDivisorFiniteClockEnergy 1 M
              (P.image (fun p : Nat.Primes => (p:ℕ)))/(M:ℝ)^(2 : ℕ) := by
  let S := P.image (fun p : Nat.Primes => (p:ℕ))
  have hS : ∀p∈S,p.Prime := by
    intro p hp
    obtain ⟨p,_,rfl⟩ := mem_image.mp hp
    exact p.property
  have hcard : S.card=P.card := card_image_of_injective P Subtype.val_injective
  obtain ⟨T,hT⟩ := prescribed_extension S hS
  refine ⟨T,fun r hrT => ?_⟩
  obtain ⟨Q,hQ,hsub,hrQ,hrS,hcardQ,hgap⟩ := hT r r.property hrT
  refine ⟨Q,hQ,hsub,hrQ,?_,by omega,?_⟩
  · intro hrP
    exact hrS (mem_image.mpr ⟨r,hrP,rfl⟩)
  · intro k hk
    exact clock_block_release S Q hS hQ hgap k hk


private def clockAffectedIndices (M K : ℕ) : Finset ℕ :=
  Icc 1 K ∪ (Nat.primesLE M).biUnion (fun q => (Icc 1 K).image (fun a => q*a))

private lemma clockAffectedIndices_card (M K : ℕ) :
    (clockAffectedIndices M K).card ≤ K*(1+Nat.primeCounting M) := by
  calc
    _ ≤ (Icc 1 K).card+
        ∑ q ∈ Nat.primesLE M,((Icc 1 K).image (fun a => q*a)).card :=
      (card_union_le _ _).trans (Nat.add_le_add_left (card_biUnion_le) _)
    _ ≤ (Icc 1 K).card+∑ _q ∈ Nat.primesLE M,(Icc 1 K).card := by
      apply Nat.add_le_add_left
      exact sum_le_sum (fun q _ => card_image_le (s:=Icc 1 K) (f:=fun a => q*a))
    _ = _ := by simp; ring

private lemma clock_sample_preserved (M K : ℕ) (P S : Finset ℕ)
    (hS : ∀ q∈S,q.Prime ∧ M/q≤K) {r : ℕ}
    (hr : r∈fixedCoreSquarefreeIndices P M) (hgood : r∉clockAffectedIndices M K) :
    r∈fixedCoreSquarefreeIndices (P∪S) M ∧
      mobiusDivisorInterpolatedFibre M r (P∪S) ∅ =
        mobiusDivisorInterpolatedFibre M r P ∅ := by
  obtain ⟨hr,hsf,hd⟩ := mem_filter.mp hr
  obtain ⟨hr0,hrM⟩ := mem_Icc.mp hr
  have hrK : K<r := by
    by_contra hn
    exact hgood (mem_union_left _ (mem_Icc.mpr ⟨hr0,le_of_not_gt hn⟩))
  have hnotdiv : ∀ q∈S,¬q∣r := by
    intro q hq hqr
    have hqp := (hS q hq).1
    have hqM : q≤M := (Nat.le_of_dvd hr0 hqr).trans hrM
    have hprod : q*(r/q)=r := Nat.mul_div_cancel' hqr
    have hdiv0 : 1≤r/q := by nlinarith
    have hdivK : r/q≤K := (Nat.div_le_div_right hrM).trans (hS q hq).2
    apply hgood
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨q,Nat.mem_primesLE.mpr ⟨hqM,hqp⟩,?_⟩
    exact mem_image.mpr ⟨r/q,mem_Icc.mpr ⟨hdiv0,hdivK⟩,hprod⟩
  have hlow : ∀ q∈S,M/r+1≤q := by
    intro q hq
    have hq0 := (hS q hq).1.pos
    have hMq : M<(K+1)*q := (Nat.div_lt_iff_lt_mul hq0).mp (by have := (hS q hq).2; omega)
    have hMr : M<q*r := by nlinarith
    have hdiv := (Nat.div_lt_iff_lt_mul hr0).mpr hMr
    omega
  constructor
  · apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hr0,hrM⟩,hsf,disjoint_left.mpr ?_⟩
    intro q hqr hq
    rcases mem_union.mp hq with hq|hq
    · exact disjoint_left.mp hd hqr hq
    · exact hnotdiv q hq (Nat.mem_primeFactors.mp hqr).2.1
  · rw [mobiusDivisorInterpolatedFibre,
      mobiusDivisorSelectionFibre_union_inactive (M/r) P S ∅
        (fun q hq => by have := hlow q hq; omega),
      mobiusDivisorSelectionFibre_union_inactive (M/r+1) P S ∅ hlow]
    rfl

/-- Processing arbitrary actual primes of bounded current quotient preserves
all but a counted set of old samples. Newly merged squares remain nonnegative,
so the possible clock payment is bounded independently of the helper count. -/
theorem mobiusDivisorFiniteClockEnergy_current_quotient_payment_le
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) (M K : ℕ) (hM : 1≤M)
    (S : Finset ℕ) (hS : ∀q∈S,q.Prime ∧ M/q≤K) :
    mobiusDivisorFiniteClockEnergy 1 M P-
      mobiusDivisorFiniteClockEnergy 1 M (P∪S) ≤
        ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ) * M * (1+Real.log M) *
          (K:ℝ)*(1+Nat.primeCounting M) := by
  let F := fixedCoreSquarefreeIndices P M
  let B := clockAffectedIndices M K
  let f := fun r : ℕ => (1+Real.log r)*(r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ)
  let C : ℝ := ((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)
  let H : ℝ := C*M*(1+Real.log M)
  have hlogM : 0≤Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hH : 0≤H := by dsimp [H,C]; positivity
  have hsplit : mobiusDivisorFiniteClockEnergy 1 M P =
      (∑ r∈F.filter (fun r => r∉B),f r)+(∑ r∈F.filter (fun r => r∈B),f r) := by
    exact (sum_filter_not_add_sum_filter F (fun r => r∈B) f).symm
  have hkept : (∑ r∈F.filter (fun r => r∉B),f r) ≤
      mobiusDivisorFiniteClockEnergy 1 M (P∪S) := by
    have hsub : F.filter (fun r => r∉B) ⊆ fixedCoreSquarefreeIndices (P∪S) M :=
      fun r hr => (clock_sample_preserved M K P S hS (mem_filter.mp hr).1 (mem_filter.mp hr).2).1
    calc
      _ = ∑ r∈F.filter (fun r => r∉B),
          (1+Real.log r)*(r:ℝ)*(mobiusDivisorInterpolatedFibre M r (P∪S) ∅)^(2 : ℕ) := by
        apply sum_congr rfl
        intro r hr
        rw [(clock_sample_preserved M K P S hS (mem_filter.mp hr).1 (mem_filter.mp hr).2).2]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro r hr _
        have hr1 : (1:ℝ)≤r := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hr).1).1
        have := Real.log_nonneg hr1
        positivity
  have hdiscard : (∑ r∈F.filter (fun r => r∈B),f r) ≤
      H*((K:ℝ)*(1+Nat.primeCounting M)) := by
    have hpoint : ∀ r∈F,f r≤H := by
      intro r hr
      have hrN := mem_Icc.mp (mem_filter.mp hr).1
      have hrpos : (0:ℝ)<r := by exact_mod_cast hrN.1
      have hlog := Real.log_le_log hrpos (show (r:ℝ)≤M by exact_mod_cast hrN.2)
      have hs := source_term_bound P hP M hr
      have hh := mul_le_mul (show 1+Real.log r≤1+Real.log M by linarith) hs
        (by positivity) (by linarith : 0≤1+Real.log M)
      simpa only [f,H,C,mul_assoc,mul_left_comm,mul_comm] using hh
    have hcard : (F.filter (fun r => r∈B)).card ≤ K*(1+Nat.primeCounting M) :=
      (card_le_card (fun r hr => (mem_filter.mp hr).2)).trans (clockAffectedIndices_card M K)
    calc
      _ ≤ ∑ _r∈F.filter (fun r => r∈B),H :=
        sum_le_sum (fun r hr => hpoint r (mem_filter.mp hr).1)
      _ = H*((F.filter (fun r => r∈B)).card:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hH
  change _ ≤ H*(K:ℝ)*(1+Nat.primeCounting M)
  linarith only [hsplit,hkept,hdiscard]

/-- The complete finite clock has the same leading logarithmic coefficient
as the full fixed-core energy; the literal counting defect is lower order. -/
theorem tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    Tendsto (fun M : ℕ => mobiusDivisorFiniteClockEnergy 1 M P /
      ((M:ℝ)^(2 : ℕ)*(1+Real.log M))) atTop
      (𝓝 (∑' n,mobiusDivisorFixedCoreBlockMass P n)) := by
  let C : ℝ := 4*((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)
  have he := tendsto_mobiusDivisorSelectionEnergy_div_sq P hP
  have hl : Tendsto (fun M : ℕ => 1+Real.log (M:ℝ)) atTop atTop := by
    have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp ht) (b-1)] with M hM
    change b-1≤Real.log (M:ℝ) at hM
    linarith
  have hc : Tendsto (fun M : ℕ => C/(1+Real.log M)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using hl.inv_tendsto_atTop.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using he.sub hc) he
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
    have hMp : (0:ℝ)<M := by exact_mod_cast hM
    have hu : 0<1+Real.log (M:ℝ) := by
      have := Real.log_nonneg (show (1:ℝ)≤M by exact_mod_cast hM)
      linarith
    have hh := (clock_defect P hP M).2
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hMp) hu)).mpr
    have heq : (mobiusDivisorSelectionEnergy M P/(M:ℝ)^(2 : ℕ)-C/(1+Real.log M))*
        ((M:ℝ)^(2 : ℕ)*(1+Real.log M)) =
        (1+Real.log M)*mobiusDivisorSelectionEnergy M P-C*(M:ℝ)^(2 : ℕ) := by
      field_simp
    rw [heq]
    dsimp [C]
    linarith only [hh]
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
    have hMp : (0:ℝ)<M := by exact_mod_cast hM
    have hu : 0<1+Real.log (M:ℝ) := by
      have := Real.log_nonneg (show (1:ℝ)≤M by exact_mod_cast hM)
      linarith
    have hh := (clock_defect P hP M).1
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hMp) hu)).mpr
    have hcancel : mobiusDivisorSelectionEnergy M P/(M:ℝ)^(2 : ℕ)*((M:ℝ)^(2 : ℕ)*(1+Real.log M)) =
        (1+Real.log M)*mobiusDivisorSelectionEnergy M P := by field_simp
    rw [hcancel]
    linarith only [hh]

end RHTower
