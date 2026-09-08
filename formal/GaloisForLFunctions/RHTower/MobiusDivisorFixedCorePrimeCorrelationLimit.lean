import GaloisForLFunctions.RHTower.MobiusDivisorFixedCorePrimeCorrelation
/-!
# Complete signed fixed-core prime-correlation coefficient

Every quotient block of the literal prime-release correlation is the product
of two square-root-affine head samples. The established squarefree moments
give its explicit signed limit. The complete absolute source tail bounds
all quotient depths and proves absolute summability of the limiting masses.
Their sum is exactly the difference of the two complete energy coefficients.
An explicit finite-prefix error is retained. No reserve sign is assumed.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma mixed_prefix_limit (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (a b c d : ℝ) {t : ℝ} (ht : 0<t) :
    Tendsto (fun N : ℕ => (∑ r ∈ fixedCoreSquarefreeIndices P ⌊t*(N : ℝ)⌋₊,
      (a+b*Real.sqrt ((r : ℝ)/N))*(c+d*Real.sqrt ((r : ℝ)/N)))/(N : ℝ)) atTop
      (𝓝 ((Sieve.squarefreeDensity * ∏ p∈P,(p : ℝ)/(p+1))*
        (a*c*t+(2/3:ℝ)*(a*d+b*c)*t*Real.sqrt t+b*d*t^2/2))) := by
  have h0 := (tendsto_fixedCoreSquarefree_scaled_count P hP ht).const_mul (a*c)
  have h1 := (tendsto_fixedCoreSquarefree_scaled_half_moments P hP 0 ht).const_mul (a*d+b*c)
  have h2 := (tendsto_fixedCoreSquarefree_scaled_half_moments P hP 1 ht).const_mul (b*d)
  have h := (h0.add h1).add h2
  convert h using 1
  · ext N
    have he (r : ℕ) : (a+b*Real.sqrt ((r : ℝ)/N))*(c+d*Real.sqrt ((r : ℝ)/N)) =
        a*c+(a*d+b*c)*Real.sqrt ((r : ℝ)/N)+b*d*(Real.sqrt ((r : ℝ)/N))^2 := by ring
    simp_rw [he]
    simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
      fixedCoreSquarefreeCount, Nat.zero_add, Nat.one_add, pow_one, add_div, mul_div_assoc]
    ring
  · congr 1
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, pow_one]
    rw [Real.sq_sqrt ht.le]
    ring

private lemma quotient_indices (P : Finset ℕ) (M : ℕ) {n : ℕ} (hn : 0<n) :
    (fixedCoreSquarefreeIndices P M).filter (fun r => M/r=n) =
      fixedCoreSquarefreeIndices P (M/n) \ fixedCoreSquarefreeIndices P (M/(n+1)) := by
  ext r
  simp only [fixedCoreSquarefreeIndices,mem_filter,Finset.mem_sdiff,mem_Icc]
  constructor
  · rintro ⟨⟨hr,hsf⟩,he⟩
    have hhi : r≤M/n := (Nat.le_div_iff_mul_le hn).mpr (by
      have h := Nat.div_mul_le_self M r
      rw [he] at h
      simpa [mul_comm] using h)
    have hlo : ¬r≤M/(n+1) := by
      intro hlo
      have hm := (Nat.le_div_iff_mul_le (by omega : 0<n+1)).mp hlo
      have hle : n+1≤M/r := (Nat.le_div_iff_mul_le hr.1).mpr (by simpa [mul_comm] using hm)
      omega
    exact ⟨⟨⟨hr.1,hhi⟩,hsf⟩,fun h => hlo h.1.2⟩
  · rintro ⟨⟨hr,hsf⟩,hlo⟩
    have hrM := hr.2.trans (Nat.div_le_self M n)
    refine ⟨⟨⟨hr.1,hrM⟩,hsf⟩,?_⟩
    have hge : n≤M/r := (Nat.le_div_iff_mul_le hr.1).mpr (by
      have h := (Nat.le_div_iff_mul_le hn).mp hr.2
      simpa [mul_comm] using h)
    have hnot : ¬n+1≤M/r := by
      intro h
      apply hlo
      have hm := (Nat.le_div_iff_mul_le hr.1).mp h
      exact ⟨⟨hr.1,(Nat.le_div_iff_mul_le (by omega : 0<n+1)).mpr
        (by simpa [mul_comm] using hm)⟩,hsf⟩
    omega

private def correlationPolynomial (P : Finset ℕ) (p n : ℕ) (u : ℝ) : ℝ :=
  (mobiusDivisorHeadBlockSlope P n+mobiusDivisorHeadBlockIntercept P n*Real.sqrt u)*
    (mobiusDivisorHeadBlockSlope P (n/p)+
      (Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p))*Real.sqrt u)

/-- Primitive of the exact signed two-head product on quotient n. -/
def mobiusDivisorPrimeCorrelationPrimitive (P : Finset ℕ) (p n : ℕ) (t : ℝ) : ℝ :=
  2*(mobiusDivisorHeadBlockSlope P n*mobiusDivisorHeadBlockSlope P (n/p)*t+
    (2/3:ℝ)*(mobiusDivisorHeadBlockSlope P n*
      (Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p))+
        mobiusDivisorHeadBlockIntercept P n*mobiusDivisorHeadBlockSlope P (n/p))*t*Real.sqrt t+
    mobiusDivisorHeadBlockIntercept P n*(Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p))*t^2/2)

/-- The complete signed prime-release source on one literal quotient block. -/
def mobiusDivisorPrimeCorrelationBlock (P : Finset ℕ) (p M n : ℕ) : ℝ :=
  ∑ r ∈ (fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => M/r=n),
    mobiusDivisorPrimeCorrelationTerm P p M r

private lemma term_polynomial (P : Finset ℕ) {p M r n : ℕ}
    (hp : 0<p) (hM : 0<M) (hr : 0<r) (hn : M/r=n) :
    mobiusDivisorPrimeCorrelationTerm P p M r =
      (M : ℝ)*(2*correlationPolynomial P p n ((r : ℝ)/M)) := by
  have hpr : 0<p*r := Nat.mul_pos hp hr
  have hn' : M/(p*r)=n/p := by
    rw [← hn,Nat.div_div_eq_div_mul,Nat.mul_comm]
  have h0 := mobiusDivisorInterpolatedHead_eq_block_affine P hr hn
  have h1 := mobiusDivisorInterpolatedHead_eq_block_affine P hpr hn'
  have hS : Real.sqrt (M : ℝ) ≠0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hM)
  have he : Real.sqrt (r : ℝ)=Real.sqrt M*Real.sqrt ((r : ℝ)/M) := by
    rw [Real.sqrt_div (Nat.cast_nonneg r)]
    field_simp
  calc
    _ = 2*(Real.sqrt r*mobiusDivisorInterpolatedFibre M r P ∅)*
        (Real.sqrt (p*r : ℕ)*mobiusDivisorInterpolatedFibre M (p*r) P ∅) := by
      rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg p)]
      have hs := Real.sq_sqrt (Nat.cast_nonneg r)
      unfold mobiusDivisorPrimeCorrelationTerm
      nlinarith [congrArg (fun z : ℝ => 2*Real.sqrt p*z*
        mobiusDivisorInterpolatedFibre M r P ∅*mobiusDivisorInterpolatedFibre M (p*r) P ∅) hs]
    _ = 2*(mobiusDivisorHeadBlockSlope P n*Real.sqrt M+
        mobiusDivisorHeadBlockIntercept P n*Real.sqrt r)*
        (mobiusDivisorHeadBlockSlope P (n/p)*Real.sqrt M+
          mobiusDivisorHeadBlockIntercept P (n/p)*Real.sqrt (p*r : ℕ)) := by rw [h0,h1]
    _ = (Real.sqrt (M : ℝ))^2*(2*correlationPolynomial P p n ((r : ℝ)/M)) := by
      rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg p),he]
      unfold correlationPolynomial
      ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg M)]

private lemma block_div_sq (P : Finset ℕ) {p M n : ℕ}
    (hp : 0<p) (hM : 0<M) (hn : 0<n) :
    mobiusDivisorPrimeCorrelationBlock P p M n/(M : ℝ)^2 =
      2*((∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/n),
        correlationPolynomial P p n ((r : ℝ)/M))/(M : ℝ)-
      (∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/(n+1)),
        correlationPolynomial P p n ((r : ℝ)/M))/(M : ℝ)) := by
  have hsub : fixedCoreSquarefreeIndices (insert p P) (M/(n+1)) ⊆
      fixedCoreSquarefreeIndices (insert p P) (M/n) := by
    intro r hr
    obtain ⟨hr,hs⟩ := mem_filter.mp hr
    have hr' := mem_Icc.mp hr
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hr'.1,
      hr'.2.trans (Nat.div_le_div_left (by omega : n≤n+1) hn)⟩,hs⟩
  have he : mobiusDivisorPrimeCorrelationBlock P p M n =
      (M : ℝ)*2*∑ r ∈ (fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => M/r=n),
        correlationPolynomial P p n ((r : ℝ)/M) := by
    unfold mobiusDivisorPrimeCorrelationBlock
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    rw [term_polynomial P hp hM
      (mem_Icc.mp (mem_filter.mp (mem_filter.mp hr).1).1).1 (mem_filter.mp hr).2]
    ring
  rw [he,quotient_indices _ M hn,sum_sdiff_eq_sub hsub]
  have hMR : (M : ℝ)≠0 := by exact_mod_cast hM.ne'
  field_simp

/-- Each actual signed prime-correlation block has an explicit arithmetic
quadratic-scale limit, keeping both adjacent head values at both scales. -/
theorem tendsto_mobiusDivisorPrimeCorrelationBlock_div_sq
    (P : Finset ℕ) (hP : ∀ q∈P,q.Prime) {p n : ℕ} (hp : p.Prime) (hn : 0<n) :
    Tendsto (fun M : ℕ => mobiusDivisorPrimeCorrelationBlock P p M n/(M : ℝ)^2) atTop
      (𝓝 ((Sieve.squarefreeDensity * ∏ q∈insert p P,(q : ℝ)/(q+1))*
        (mobiusDivisorPrimeCorrelationPrimitive P p n (1/(n : ℝ))-
          mobiusDivisorPrimeCorrelationPrimitive P p n (1/((n : ℝ)+1))))) := by
  have hPp : ∀ q∈insert p P,q.Prime := by simpa using And.intro hp hP
  have hnR : 0<(n : ℝ) := by exact_mod_cast hn
  have h0 := mixed_prefix_limit (insert p P) hPp
    (mobiusDivisorHeadBlockSlope P n) (mobiusDivisorHeadBlockIntercept P n)
    (mobiusDivisorHeadBlockSlope P (n/p)) (Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p))
    (show 0<1/(n : ℝ) by positivity)
  have h1 := mixed_prefix_limit (insert p P) hPp
    (mobiusDivisorHeadBlockSlope P n) (mobiusDivisorHeadBlockIntercept P n)
    (mobiusDivisorHeadBlockSlope P (n/p)) (Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p))
    (show 0<1/((n : ℝ)+1) by positivity)
  have h := (h0.sub h1).const_mul 2
  have hc (M d : ℕ) : ⌊(1/(d : ℝ))*(M : ℝ)⌋₊=M/d := by
    rw [one_div,mul_comm,← div_eq_mul_inv,Nat.floor_div_natCast,Nat.floor_natCast]
  have h' : Tendsto (fun M : ℕ => 2*((∑ r∈fixedCoreSquarefreeIndices (insert p P)
      ⌊(1/(n : ℝ))*(M : ℝ)⌋₊,correlationPolynomial P p n ((r : ℝ)/M))/(M : ℝ)-
        (∑ r∈fixedCoreSquarefreeIndices (insert p P) ⌊(1/((n : ℝ)+1))*(M : ℝ)⌋₊,
          correlationPolynomial P p n ((r : ℝ)/M))/(M : ℝ))) atTop
      (𝓝 ((Sieve.squarefreeDensity * ∏ q∈insert p P,(q : ℝ)/(q+1))*
        (mobiusDivisorPrimeCorrelationPrimitive P p n (1/(n : ℝ))-
          mobiusDivisorPrimeCorrelationPrimitive P p n (1/((n : ℝ)+1))))) := by
    convert h using 1
    congr 1
    unfold mobiusDivisorPrimeCorrelationPrimitive
    ring
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  rw [block_div_sq P hp.pos hM hn,hc]
  have hc' : ⌊(1/((n : ℝ)+1))*(M : ℝ)⌋₊=M/(n+1) := by simpa using hc M (n+1)
  rw [hc']

/-- Explicit signed mass of one prime-correlation block; the zero cell is empty. -/
def mobiusDivisorPrimeCorrelationMass (P : Finset ℕ) (p n : ℕ) : ℝ :=
  if n=0 then 0 else
    (Sieve.squarefreeDensity * ∏ q∈insert p P,(q : ℝ)/(q+1))*
      (mobiusDivisorPrimeCorrelationPrimitive P p n (1/(n : ℝ))-
        mobiusDivisorPrimeCorrelationPrimitive P p n (1/((n : ℝ)+1)))

private lemma correlation_block_limit (P : Finset ℕ) (hP : ∀ q∈P,q.Prime)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Tendsto (fun M : ℕ => mobiusDivisorPrimeCorrelationBlock P p M n/(M : ℝ)^2) atTop
      (𝓝 (mobiusDivisorPrimeCorrelationMass P p n)) := by
  by_cases hn : n=0
  · have hz (M : ℕ) : mobiusDivisorPrimeCorrelationBlock P p M 0=0 := by
      unfold mobiusDivisorPrimeCorrelationBlock
      apply sum_eq_zero
      intro r hr
      obtain ⟨hr,he⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp (mem_filter.mp hr).1
      have h : 1≤M/r := (Nat.le_div_iff_mul_le hr'.1).mpr (by simpa using hr'.2)
      omega
    simp [hn,hz,mobiusDivisorPrimeCorrelationMass]
  · simpa only [mobiusDivisorPrimeCorrelationMass,if_neg hn] using
      tendsto_mobiusDivisorPrimeCorrelationBlock_div_sq P hP hp (by omega : 0<n)

private lemma correlation_prefix (P : Finset ℕ) (p M T : ℕ) :
    (∑ n∈range T,mobiusDivisorPrimeCorrelationBlock P p M n) =
      ∑ r∈(fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => M/r<T),
        mobiusDivisorPrimeCorrelationTerm P p M r := by
  simpa only [mobiusDivisorPrimeCorrelationBlock,mem_range] using
    sum_fiberwise_eq_sum_filter (fixedCoreSquarefreeIndices (insert p P) M) (range T)
      (fun r => M/r) (mobiusDivisorPrimeCorrelationTerm P p M)

private lemma correlation_remainder (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpP : p∉P) (M T : ℕ) :
    mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P)-
      (∑ n∈range T,mobiusDivisorPrimeCorrelationBlock P p M n) =
      ∑ r∈(fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => T≤M/r),
        mobiusDivisorPrimeCorrelationTerm P p M r := by
  rw [mobiusDivisorSelectionEnergy_prime_release_eq_correlation P hp hpP M,correlation_prefix]
  have he : 2*Real.sqrt p*(∑ r∈fixedCoreSquarefreeIndices (insert p P) M,
      (r : ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*mobiusDivisorInterpolatedFibre M (p*r) P ∅) =
      ∑ r∈fixedCoreSquarefreeIndices (insert p P) M,mobiusDivisorPrimeCorrelationTerm P p M r := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r _
    unfold mobiusDivisorPrimeCorrelationTerm
    ring
  rw [he]
  have h := sum_filter_add_sum_filter_not (fixedCoreSquarefreeIndices (insert p P) M)
    (fun r => M/r<T) (mobiusDivisorPrimeCorrelationTerm P p M)
  simpa only [not_lt] using (eq_sub_of_add_eq' h).symm

private lemma normalized_remainder_bound (P : Finset ℕ) (hP : ∀ q∈P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (M : ℕ) {T : ℕ} (hT : 0<T) :
    |(mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P))/(M : ℝ)^2-
      (∑ n∈range T,mobiusDivisorPrimeCorrelationBlock P p M n/(M : ℝ)^2)| ≤
        2*((3/5:ℝ)*2^(P.card-1))^2/(T : ℝ) := by
  rw [← sum_div,← sub_div,correlation_remainder P hp hpP M T,
    abs_div,abs_of_nonneg (sq_nonneg (M : ℝ))]
  by_cases hM : M=0
  · simp only [hM,Nat.cast_zero,zero_pow (by omega : 2≠0),div_zero]
    positivity
  · have hMR : 0<(M : ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hM)
    apply (div_le_iff₀ hMR).mpr
    exact (abs_sum_le_sum_abs _ _).trans
      (mobiusDivisorPrimeCorrelation_absolute_tail_le P hP hp hpP M hT)

private lemma absolute_source_bound (P : Finset ℕ) (hP : ∀ q∈P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (M : ℕ) :
    (∑ r∈fixedCoreSquarefreeIndices (insert p P) M, |mobiusDivisorPrimeCorrelationTerm P p M r|) ≤
      (2*((3/5:ℝ)*2^(P.card-1))^2)*(M : ℝ)^2 := by
  have he : (fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => 1≤M/r) =
      fixedCoreSquarefreeIndices (insert p P) M := by
    apply filter_eq_self.mpr
    intro r hr
    have hr' := mem_Icc.mp (mem_filter.mp hr).1
    exact (Nat.le_div_iff_mul_le hr'.1).mpr (by simpa using hr'.2)
  simpa only [he,Nat.cast_one,div_one] using
    mobiusDivisorPrimeCorrelation_absolute_tail_le P hP hp hpP M (show 0<1 by omega)

private lemma absolute_block_prefix_bound (P : Finset ℕ) (hP : ∀ q∈P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (M T : ℕ) :
    (∑ n∈range T,|mobiusDivisorPrimeCorrelationBlock P p M n/(M : ℝ)^2|) ≤
      2*((3/5:ℝ)*2^(P.card-1))^2 := by
  simp_rw [abs_div,abs_of_nonneg (sq_nonneg (M : ℝ))]
  rw [← sum_div]
  by_cases hM : M=0
  · simp only [hM,Nat.cast_zero,zero_pow (by omega : 2≠0),div_zero]
    positivity
  · have hMR : 0<(M : ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hM)
    apply (div_le_iff₀ hMR).mpr
    calc
      _ ≤ ∑ n∈range T,∑ r∈(fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => M/r=n),
          |mobiusDivisorPrimeCorrelationTerm P p M r| :=
        sum_le_sum (fun n _ => abs_sum_le_sum_abs _ _)
      _ = ∑ r∈(fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => M/r<T),
          |mobiusDivisorPrimeCorrelationTerm P p M r| := by
        simpa only [mem_range] using sum_fiberwise_eq_sum_filter
          (fixedCoreSquarefreeIndices (insert p P) M) (range T) (fun r => M/r)
          (fun r => |mobiusDivisorPrimeCorrelationTerm P p M r|)
      _ ≤ ∑ r∈fixedCoreSquarefreeIndices (insert p P) M,
          |mobiusDivisorPrimeCorrelationTerm P p M r| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
      _ ≤ _ := absolute_source_bound P hP hp hpP M

/-- The signed prime-correlation masses are absolutely summable. The
complete absolute source budget controls all quotient depths at once. -/
theorem summable_abs_mobiusDivisorPrimeCorrelationMass
    (P : Finset ℕ) (hP : ∀ q∈P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p∉P) :
    Summable (fun n => |mobiusDivisorPrimeCorrelationMass P p n|) := by
  apply summable_of_sum_range_le (fun _ => abs_nonneg _)
  intro T
  apply le_of_tendsto' (tendsto_finsetSum (range T)
    (fun n _ => (correlation_block_limit P hP hp n).abs))
  exact fun M => absolute_block_prefix_bound P hP hp hpP M T

/-- Finite actual head data approximate the full signed prime-release
coefficient with an explicit rigorous error, uniformly in quotient depth. -/
theorem abs_mobiusDivisorPrimeReleaseCoefficient_sub_prefix_le
    (P : Finset ℕ) (hP : ∀ q∈P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p∉P)
    {T : ℕ} (hT : 0<T) :
    |((∑' n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑' n,mobiusDivisorFixedCoreBlockMass (insert p P) n)-
      ∑ n∈range T,mobiusDivisorPrimeCorrelationMass P p n| ≤
        2*((3/5:ℝ)*2^(P.card-1))^2/(T : ℝ) := by
  have hPp : ∀ q∈insert p P,q.Prime := by simpa using And.intro hp hP
  have hE := (tendsto_mobiusDivisorSelectionEnergy_div_sq P hP).sub
    (tendsto_mobiusDivisorSelectionEnergy_div_sq (insert p P) hPp)
  apply le_of_tendsto' ((hE.sub (tendsto_finsetSum (range T)
    (fun n _ => correlation_block_limit P hP hp n))).abs)
  intro M
  simpa only [sub_div] using normalized_remainder_bound P hP hp hpP M hT

/-- The explicit signed correlation series equals the actual fixed-core
prime-release coefficient. All source blocks and both diagonal cancellations
are retained; no positivity or renewable-reserve hypothesis is introduced. -/
theorem hasSum_mobiusDivisorPrimeCorrelationMass
    (P : Finset ℕ) (hP : ∀ q∈P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p∉P) :
    HasSum (mobiusDivisorPrimeCorrelationMass P p)
      ((∑' n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑' n,mobiusDivisorFixedCoreBlockMass (insert p P) n) := by
  have hs : Summable (mobiusDivisorPrimeCorrelationMass P p) :=
    (summable_abs_iff).mp (summable_abs_mobiusDivisorPrimeCorrelationMass P hP hp hpP)
  have hsmall : Tendsto (fun T : ℕ => 2*((3/5:ℝ)*2^(P.card-1))^2/(T : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop)).const_mul
        (2*((3/5:ℝ)*2^(P.card-1))^2)
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using h
  have hle : |((∑' n,mobiusDivisorFixedCoreBlockMass P n)-
      ∑' n,mobiusDivisorFixedCoreBlockMass (insert p P) n)-
        ∑' n,mobiusDivisorPrimeCorrelationMass P p n| ≤ 0 := by
    apply le_of_tendsto_of_tendsto
      ((tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat).abs) hsmall
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    exact abs_mobiusDivisorPrimeReleaseCoefficient_sub_prefix_le P hP hp hpP hT
  have he := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have he' := sub_eq_zero.mp he
  rw [he']
  exact hs.hasSum

end RHTower
