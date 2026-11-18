import GaloisForLFunctions.ExceptionalLayerTheory.PrimePowerLevelsOfTheCyclicCoverCoefficients
import GaloisForLFunctions.RHTower.SmoothNumberLogSeries

/-!
# Common divisors of the cyclic-cover coefficient vectors

At an odd prime the complete residue periods give the valuation of N!.
The first residual level can be minimized exactly. Possible excess comes
entirely from higher prime powers. The row of residue one excludes two.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Common content of the primitive-character powers of the cyclic-cover coordinate
in degree N, after giving all coordinates the same factorial denominator. -/
def cyclicCoefficientContent (q N : ℕ) : ℕ :=
  ((Icc 1 (q-1)).filter (fun a => a.Coprime q)).gcd (cyclicCoefficientRow q N)

private theorem content_dvd {q a : ℕ} (ha : 0 < a) (haq : a < q) (hunit : a.Coprime q) (N : ℕ) :
    cyclicCoefficientContent q N ∣ cyclicCoefficientRow q N a :=
  gcd_dvd (mem_filter.mpr ⟨mem_Icc.mpr ⟨ha,by omega⟩,hunit⟩)

theorem cyclicCoefficientContent_pos {q : ℕ} (hq : 2≤q) (N : ℕ) :
    0 < cyclicCoefficientContent q N :=
  Nat.pos_of_dvd_of_pos (content_dvd one_pos (by omega : 1 < q) (Nat.coprime_one_left _) N) (cyclicCoefficientRow_pos ..)

private theorem last_label_pos {q p : ℕ} (hq : 2≤q) (hc : p.Coprime q) :
    0 < (p*(q-1))%q := by
  by_contra! h
  have hd := Nat.dvd_of_mod_eq_zero (by omega : (p*(q-1))%q=0)
  have hh : q ∣ q-1 := hc.symm.dvd_of_dvd_mul_left hd
  have := Nat.le_of_dvd (by omega : 0 < q-1) hh
  omega

/-- Above the factorial valuation, odd primes realize every common selected
level, with excess at most the number of levels beyond the first. -/
theorem cyclicCoefficientContent_odd_valuation {j N p : ℕ} (hp : p.Prime) (hodd : p≠2)
    (hX : p ≤ 2^(j+1)*N) :
    N.factorial.factorization p+dyadicCommonCarryLevels j N p ≤
        (cyclicCoefficientContent (2^(j+1)) N).factorization p ∧
      (cyclicCoefficientContent (2^(j+1)) N).factorization p+1 ≤
        N.factorial.factorization p+dyadicCommonCarryLevels j N p+p.log (2^(j+1)*N) := by
  let q := 2^(j+1)
  let X := q*N
  let L := p.log X
  let V := N.factorial.factorization p+dyadicCommonCarryLevels j N p
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  have hq0 : 0 < q := by omega
  have hN : 0 < N := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp only [mul_zero] at hX
    exact (not_le_of_gt hp.pos) hX
  have hL : 1≤L := Nat.le_log_of_pow_le hp.one_lt (by simpa only [pow_one,X,q] using hX)
  have hB : X < p^(L+1) := Nat.lt_pow_succ_log_self hp.one_lt _
  have hNX : N≤X := by simpa only [one_mul] using Nat.mul_le_mul_right N (show 1≤q by omega)
  have hfact := Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow hN.ne' (hNX.trans_lt hB))
  have hc : p.Coprime q := ((Nat.coprime_primes hp Nat.prime_two).mpr hodd).pow_right _
  have hV : V = ∑ e ∈ Icc 1 L, (N/p^e+dyadicQuotientCarry j N (p^e)) := by
    rw [sum_add_distrib]
    dsimp only [V]
    rw [hfact,Ico_add_one_right_eq_Icc]
  have hrow (a : ℕ) : (cyclicCoefficientRow q N a).factorization p =
      ∑ e ∈ Icc 1 L, cyclicCoefficientLevel q N a (p^e) := by
    rw [factorization_cyclicCoefficientRow hp hB,Ico_add_one_right_eq_Icc]
  have hmin (a : ℕ) (ha : 0 < a) (haq : a < q) :
      V ≤ (cyclicCoefficientRow q N a).factorization p := by
    rw [hV,hrow]
    exact sum_le_sum fun e _ => (cyclicCoefficientLevel_bounds (pow_pos hp.pos e) ha haq (hc.pow_left _) N).1
  have hg := (cyclicCoefficientContent_pos hq N).ne'
  constructor
  · apply (hp.pow_dvd_iff_le_factorization hg).mp
    apply Finset.dvd_gcd
    intro a ha
    exact (hp.pow_dvd_iff_le_factorization (cyclicCoefficientRow_pos ..).ne').mpr
      (hmin a (mem_Icc.mp (mem_filter.mp ha).1).1 (by have := (mem_Icc.mp (mem_filter.mp ha).1).2; omega))
  · let a := (p*(q-1))%q
    have ha := last_label_pos hq hc
    have haq := Nat.mod_lt (p*(q-1)) hq0
    have hpred : (q-1).Coprime q := by
      change (q-1).gcd q=1
      rw [← Nat.gcd_sub_self_right (Nat.sub_le q 1),show q-(q-1)=1 by omega,Nat.gcd_one_right]
    have hunit : a.Coprime q := by
      have hr := (hc.mul_left hpred).symm
      change q.gcd (p*(q-1))=1 at hr
      rwa [Nat.gcd_rec q (p*(q-1))] at hr
    have hle := (Nat.factorization_le_iff_dvd hg (cyclicCoefficientRow_pos q N a).ne').mpr
      (content_dvd ha haq hunit N) p
    have hupper (e : ℕ) :
        cyclicCoefficientLevel q N a (p^e)+(if e=1 then 1 else 0) ≤
          N/p^e+dyadicQuotientCarry j N (p^e)+1 := by
      by_cases he : e=1
      · subst e
        simp only [pow_one,if_true,a,cyclicCoefficientLevel_last hq hp.pos hc,dyadicQuotientCarry,q,le_refl]
      · simp only [if_neg he,add_zero]
        have hh : cyclicCoefficientLevel q N a (p^e) ≤ N/p^e+1 :=
          (cyclicCoefficientLevel_bounds (pow_pos hp.pos e) ha haq (hc.pow_left _) N).2
        exact hh.trans (Nat.add_le_add_right (Nat.le_add_right ..) 1)
    have htot := sum_le_sum (s := Icc 1 L) (fun e _ => hupper e)
    simp only [sum_add_distrib,sum_ite_eq',mem_Icc,le_refl,hL,and_self,if_true,sum_const,
      Nat.card_Icc,Nat.add_sub_cancel,smul_eq_mul,mul_one] at htot
    have he := hrow a
    have hvt := hV
    rw [sum_add_distrib] at hvt
    change (cyclicCoefficientContent q N).factorization p+1 ≤ V+L
    omega

/-- No factor of two survives in the common content at a dyadic width. -/
theorem cyclicCoefficientContent_two_valuation (j N : ℕ) :
    (cyclicCoefficientContent (2^(j+1)) N).factorization 2=0 := by
  let q := 2^(j+1)
  have hq : 1 < q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have h := hd.trans (content_dvd one_pos hq (Nat.coprime_one_left _) N)
  rw [cyclicCoefficientRow_eq_prod one_pos hq] at h
  obtain ⟨k,_,hk⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp h
  have he : 2 ∣ q*k := dvd_mul_of_dvd_left (by dsimp only [q]; exact dvd_pow_self 2 (by omega)) _
  have hf : 2 ∣ 1 := (Nat.dvd_add_iff_right he).mpr hk
  omega

private theorem central_two_balance (N : ℕ) :
    (Nat.centralBinom N).factorization 2+N.factorial.factorization 2=N := by
  have hf : N.factorial ≠ 0 := Nat.factorial_ne_zero N
  have hc := (Nat.centralBinom_pos N).ne'
  have he : Nat.centralBinom N*N.factorial*N.factorial=(2*N).factorial := by
    simpa only [Nat.centralBinom,two_mul] using Nat.add_choose_mul_factorial_mul_factorial N N
  have h := congrArg (fun k : ℕ => k.factorization 2) he
  simp only [Nat.factorization_mul (Nat.mul_ne_zero hc hf) hf,Nat.factorization_mul hc hf,
    Finsupp.add_apply,Nat.factorization_factorial_mul Nat.prime_two] at h
  omega

/-- Every dyadic central binomial has the same two-adic valuation. It cancels
the entire digit-sum correction of the ordinary factorial. -/
theorem dyadicBinomialGcd_two_balance (j N : ℕ) :
    (dyadicBinomialGcd j N).factorization 2+N.factorial.factorization 2=N := by
  have hd (k : ℕ) : (Nat.centralBinom (2^k*N)).factorization 2=(Nat.centralBinom N).factorization 2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      let n := 2^k*N
      have h₁ := central_two_balance (2*n)
      have h₂ := central_two_balance n
      rw [Nat.factorization_factorial_mul Nat.prime_two] at h₁
      rw [show 2^(k+1)*N=2*n by dsimp only [n]; ring]
      change (Nat.centralBinom n).factorization 2=_ at ih
      omega
  induction j with
  | zero => exact central_two_balance N
  | succ j ih =>
    rw [dyadicBinomialGcd,Nat.factorization_gcd (dyadicBinomialGcd_pos j N).ne' (Nat.centralBinom_pos _).ne',
      Finsupp.inf_apply,hd]
    have h := central_two_balance N
    omega

private theorem content_primeFactors {q N : ℕ} (hq : 2≤q) :
    (cyclicCoefficientContent q N).primeFactors ⊆ Nat.primesLE (q*N) := by
  intro p hp
  obtain ⟨hpr,hd,_⟩ := Nat.mem_primeFactors.mp hp
  have hrow := hd.trans (content_dvd one_pos (by omega : 1 < q) (Nat.coprime_one_left _) N)
  change p ∣ ∏ k ∈ (Icc 1 (q*N)).filter (fun k => k%q=1), k at hrow
  obtain ⟨k,hk,hdk⟩ := (hpr.prime.dvd_finsetProd_iff _).mp hrow
  have hkI := mem_Icc.mp (mem_filter.mp hk).1
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hkI.1 hdk).trans hkI.2,hpr⟩

/-- The discrepancy between the common content, the factorial, and the dyadic
gcd is bounded by precisely the available higher-prime-power mass. -/
theorem cyclicCoefficientContent_log_error (j N : ℕ) (hN : 0 < N) :
    let q := 2^(j+1)
    |Real.log (cyclicCoefficientContent q N) - Real.log N.factorial -
      Real.log (dyadicBinomialGcd j N)+(N:ℝ)*Real.log 2| ≤
        Chebyshev.psi (q*N:ℕ)-Chebyshev.theta (q*N:ℕ) := by
  let q := 2^(j+1)
  let X := q*N
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  have hNX : N≤X := by simpa only [one_mul] using Nat.mul_le_mul_right N (show 1≤q by omega)
  have h2X : 2≤X := hq.trans (by simpa only [mul_one] using Nat.mul_le_mul_left q (show 1≤N from hN))
  have hF : N.factorial.primeFactors ⊆ Nat.primesLE X := by
    intro p hp
    obtain ⟨hpr,hd,_⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨(hpr.dvd_factorial.mp hd).trans hNX,hpr⟩
  have htwo : (N:ℝ)*Real.log 2 =
      ∑ p ∈ Nat.primesLE X, (if p=2 then (N:ℝ) else 0)*Real.log p := by
    simp only [ite_mul,zero_mul,sum_ite_eq',if_pos (Nat.mem_primesLE.mpr ⟨h2X,Nat.prime_two⟩)]
    rfl
  change |Real.log (cyclicCoefficientContent q N) - Real.log N.factorial -
    Real.log (dyadicBinomialGcd j N)+(N:ℝ)*Real.log 2| ≤ Chebyshev.psi X-Chebyshev.theta X
  rw [_root_.RHTower.SmoothNumbers.log_eq_sum_factorization (content_primeFactors hq),
    _root_.RHTower.SmoothNumbers.log_eq_sum_factorization hF,log_dyadicBinomialGcd_eq_sum_primes,htwo,
    ← sum_sub_distrib,← sum_sub_distrib,← sum_add_distrib,Chebyshev.psi_eq_sum_mul_log_prime,
    Chebyshev.theta_eq_sum_primesLE_log,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  obtain ⟨hpX,hpr⟩ := Nat.mem_primesLE.mp hp
  let L := p.log X
  have hL : 1≤L := Nat.le_log_of_pow_le hpr.one_lt (by simpa only [pow_one] using hpX)
  have hlog : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_le)
  have hval : |((cyclicCoefficientContent q N).factorization p:ℝ) - (N.factorial.factorization p:ℝ) -
      ((dyadicBinomialGcd j N).factorization p:ℝ)+(if p=2 then (N:ℝ) else 0)| ≤ (L:ℝ)-1 := by
    by_cases he : p=2
    · subst p
      have hh := dyadicBinomialGcd_two_balance j N
      have hhR : ((dyadicBinomialGcd j N).factorization 2:ℝ)+(N.factorial.factorization 2:ℝ)=N := by exact_mod_cast hh
      rw [cyclicCoefficientContent_two_valuation,if_pos rfl,Nat.cast_zero,show
        (0:ℝ)-(N.factorial.factorization 2:ℝ)-((dyadicBinomialGcd j N).factorization 2:ℝ)+N=0
        by linarith only [hhR],abs_zero]
      exact sub_nonneg.mpr (by exact_mod_cast hL)
    · obtain ⟨hc₁,hc₂⟩ := cyclicCoefficientContent_odd_valuation hpr he hpX
      change N.factorial.factorization p+dyadicCommonCarryLevels j N p ≤
        (cyclicCoefficientContent q N).factorization p at hc₁
      change (cyclicCoefficientContent q N).factorization p+1 ≤
        N.factorial.factorization p+dyadicCommonCarryLevels j N p+L at hc₂
      obtain ⟨hg₁,hg₂⟩ := dyadicBinomialGcd_carry_bounds j N hpr (by omega : 2≤L+1) (Nat.lt_succ_self L)
      rw [Ico_add_one_right_eq_Icc] at hg₁
      have hf : dyadicQuotientCarry j N p ≤ dyadicCommonCarryLevels j N p := by
        simpa only [pow_one] using (single_le_sum (f := fun e => dyadicQuotientCarry j N (p^e))
          (fun _ _ => Nat.zero_le _) (mem_Icc.mpr ⟨le_rfl,hL⟩))
      change dyadicCommonCarryLevels j N p ≤ _ at hg₁
      rw [if_neg he,add_zero,abs_le]
      constructor
      · have hh : N.factorial.factorization p+(dyadicBinomialGcd j N).factorization p+1 ≤
            (cyclicCoefficientContent q N).factorization p+L := by
          omega
        have hr : (N.factorial.factorization p:ℝ)+((dyadicBinomialGcd j N).factorization p:ℝ)+1 ≤
            ((cyclicCoefficientContent q N).factorization p:ℝ)+L := by exact_mod_cast hh
        linarith only [hr]
      · have hh : (cyclicCoefficientContent q N).factorization p+1 ≤
            N.factorial.factorization p+(dyadicBinomialGcd j N).factorization p+L := by
          omega
        have hr : ((cyclicCoefficientContent q N).factorization p:ℝ)+1 ≤
            (N.factorial.factorization p:ℝ)+((dyadicBinomialGcd j N).factorization p:ℝ)+L := by exact_mod_cast hh
        linarith only [hr]
  rw [← sub_mul,← sub_mul,← add_mul,abs_mul,abs_of_nonneg hlog]
  exact (mul_le_mul_of_nonneg_right hval hlog).trans_eq (by ring)

/-- Logarithmic projective height of the simultaneous primitive-character coefficients.
The row q-1 is the largest archimedean coordinate. -/
def cyclicCoefficientHeight (q N : ℕ) : ℝ :=
  Real.log (cyclicCoefficientRow q N (q-1)) - Real.log (cyclicCoefficientContent q N)

theorem cyclicCoefficientHeight_zero {q : ℕ} (hq : 2≤q) : cyclicCoefficientHeight q 0=0 := by
  have hd := content_dvd one_pos (by omega : 1 < q) (Nat.coprime_one_left _) 0
  simp [cyclicCoefficientRow] at hd
  simp [cyclicCoefficientHeight,cyclicCoefficientRow,hd]

/-- The projective height and logarithmic binomial gcd have complementary linear
main terms. The uniform finite error consists of higher powers and a rounding log. -/
theorem cyclicCoefficientHeight_add_log_gcd (j N : ℕ) (hN : 0 < N) :
    let q := 2^(j+1)
    |cyclicCoefficientHeight q N+Real.log (dyadicBinomialGcd j N)-(N:ℝ)*Real.log (2*q:ℕ)| ≤
      Chebyshev.psi (q*N:ℕ)-Chebyshev.theta (q*N:ℕ)+Real.log ((N:ℝ)+1) := by
  let q := 2^(j+1)
  let P := cyclicCoefficientRow q N (q-1)
  let g := cyclicCoefficientContent q N
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  have hqR : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hP : 0 < (P:ℝ) := by exact_mod_cast cyclicCoefficientRow_pos q N (q-1)
  have hF : 0 < (N.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos N
  obtain ⟨hl,hu⟩ := cyclicCoefficientRow_top_bounds hq N
  have hlo : Real.log P ≤ (N:ℝ)*Real.log q+Real.log N.factorial := by
    have h := Real.log_le_log hP (by exact_mod_cast hl : (P:ℝ) ≤ (q:ℝ)^N*N.factorial)
    rwa [Real.log_mul (pow_pos hqR N).ne' hF.ne',Real.log_pow] at h
  have hup : (N:ℝ)*Real.log q+Real.log N.factorial ≤ Real.log ((N:ℝ)+1)+Real.log P := by
    have h := Real.log_le_log (mul_pos (pow_pos hqR N) hF)
      (by exact_mod_cast hu : (q:ℝ)^N*N.factorial ≤ ((N:ℝ)+1)*P)
    rwa [Real.log_mul (pow_pos hqR N).ne' hF.ne',Real.log_pow,Real.log_mul (by positivity) hP.ne'] at h
  have ht : |Real.log P-((N:ℝ)*Real.log q+Real.log N.factorial)| ≤ Real.log ((N:ℝ)+1) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith only [hup]
  have hc := cyclicCoefficientContent_log_error j N hN
  change |Real.log g-Real.log N.factorial-Real.log (dyadicBinomialGcd j N)+(N:ℝ)*Real.log 2| ≤ _ at hc
  change |Real.log P-Real.log g+Real.log (dyadicBinomialGcd j N)-(N:ℝ)*Real.log (2*q:ℕ)| ≤ _
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ)≠0) hqR.ne']
  have he : Real.log P-Real.log g+Real.log (dyadicBinomialGcd j N)-(N:ℝ)*(Real.log 2+Real.log q) =
      (Real.log P-((N:ℝ)*Real.log q+Real.log N.factorial))-
      (Real.log g-Real.log N.factorial-Real.log (dyadicBinomialGcd j N)+(N:ℝ)*Real.log 2) := by ring
  rw [he]
  exact ((abs_sub _ _).trans (add_le_add ht hc)).trans_eq (add_comm _ _)

#print axioms cyclicCoefficientContent_odd_valuation
#print axioms cyclicCoefficientContent_two_valuation
#print axioms dyadicBinomialGcd_two_balance
#print axioms cyclicCoefficientContent_log_error
#print axioms cyclicCoefficientHeight_add_log_gcd

end GaloisForLFunctions.ExceptionalLayerTheory
