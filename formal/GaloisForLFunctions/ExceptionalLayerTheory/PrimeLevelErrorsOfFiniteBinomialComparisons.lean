import GaloisForLFunctions.ExceptionalLayerTheory.ReflectionOfBinomialCarriesAtAnOrdinaryPrime
import GaloisForLFunctions.ExceptionalLayerTheory.ShiftedDivisorsInADyadicBinomialGcd
import GaloisForLFunctions.RHTower.Sieve.PrimeCountRelativeWindow
import GaloisForLFunctions.RHTower.RVCumulantAverage

/-!
# Prime-level error of binomial comparisons on every large scale

For primes between twice and three times the lower scale, the bases between
six and twelve times the scale contain a complete period of residues.
The sharp per-prime reflection bound and the prime number theorem therefore
force a linear absolute error at some base. All slopes may vary with the prime.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem range_eq_residue_sum {p : ℕ} [NeZero p] (f : ZMod p → ℝ) :
    ∑ r ∈ range p, f r = ∑ x : ZMod p, f x := by
  rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ => f r)]
  apply Eq.trans _ ((ZMod.finEquiv p).sum_comp f)
  refine sum_congr rfl fun r _ => congrArg f ?_
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p =>
    apply ZMod.val_injective
    exact ZMod.val_natCast_of_lt r.isLt

/-- Absolute difference at one ordinary prime between a signed sum of binomial
carries and the last quotient class at the base `L*n`. -/
def binomialPrimeLevelLoss {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (q L p : ℕ) (u v : ι → ZMod p) (n : ℕ) : ℝ :=
  |signedBinomialResidues s w u v n - (if q ∣ q*(L*n)/p+1 then 1 else 0)|

private def residueLoss {ι : Type*} (s : Finset ι) (w : ι → ℝ) {p : ℕ}
    (h : ℕ) (l : ZMod p) (u v : ι → ZMod p) (x : ZMod p) : ℝ :=
  |signedBinomialResidues s w u v x - topResidueWeight p h (l*x).val|

private theorem levelLoss_eq_residueLoss {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    {q p : ℕ} (hq : 0<q) (hp : 0<p) (L : ℕ) (u v : ι → ZMod p) (n : ℕ) :
    binomialPrimeLevelLoss s w q L p u v n = residueLoss s w (p/q) L u v n := by
  rw [binomialPrimeLevelLoss,residueLoss,topResidueWeight,← Nat.cast_mul,ZMod.val_natCast]
  simp only [last_quotient_class_iff_top_residue hq hp]

private theorem period_loss {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    {k h : ℕ} [Fact (2*k+1).Prime] (hh : 2*h≤k)
    {l : ZMod (2*k+1)} (hl : l≠0) (u v : ι → ZMod (2*k+1)) :
    (h:ℝ) ≤ ∑ r ∈ range (2*k+1), residueLoss s w h l u v r := by
  let U := fun i => u i/l
  let V := fun i => v i/l
  let f := fun x : ZMod (2*k+1) => |signedBinomialResidues s w U V x-topResidueWeight (2*k+1) h x.val|
  have hf (x : ZMod (2*k+1)) : f (l*x) = residueLoss s w h l u v x := by
    have he (a : ZMod (2*k+1)) : (a/l)*(l*x)=a*x := by rw [← mul_assoc,div_mul_cancel₀ _ hl]
    simp only [f,residueLoss,signedBinomialResidues,U,V,binomialResidueCarry,he]
  calc
    _ ≤ ∑ n ∈ range (2*k), f (n+1 : ℕ) := by
      apply (signedBinomialResidues_absolute_error hh s w U V).trans_eq
      refine sum_congr rfl fun n hn => ?_
      have hlt : n+1 < 2*k+1 := by have := mem_range.mp hn; omega
      simp only [f,ZMod.val_natCast_of_lt hlt]
    _ ≤ ∑ n ∈ range (2*k+1), f n := by
      rw [sum_range_succ']
      exact le_add_of_nonneg_right (abs_nonneg _)
    _ = ∑ x : ZMod (2*k+1), f x := range_eq_residue_sum f
    _ = ∑ x : ZMod (2*k+1), f (l*x) := (Equiv.sum_comp (Equiv.mulLeft₀ l hl) f).symm
    _ = _ := by simp_rw [hf]; exact (range_eq_residue_sum _).symm

private theorem prime_period_loss {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    {p q L : ℕ} (hp : p.Prime) (hp2 : 2<p) (hq : 4≤q) (hL : 0<L) (hLp : L<p)
    (u v : ι → ZMod p) :
    ((p/q:ℕ):ℝ) ≤ ∑ n ∈ Ico (3*p) (4*p), binomialPrimeLevelLoss s w q L p u v n := by
  have hodd := hp.eq_two_or_odd.resolve_left hp2.ne'
  obtain ⟨k,hpk⟩ : ∃ k : ℕ, p=2*k+1 := ⟨p/2,by omega⟩
  subst p
  letI : Fact (2*k+1).Prime := ⟨hp⟩
  have hl : (L : ZMod (2*k+1)) ≠ 0 := by
    intro e
    have he := congrArg ZMod.val e
    rw [ZMod.val_natCast_of_lt hLp,ZMod.val_zero] at he
    omega
  have hdiv := Nat.div_le_div_left hq (by omega : 0<4) (a := 2*k+1)
  have hh : 2*((2*k+1)/q) ≤ k := by omega
  apply (period_loss s w hh hl u v).trans_eq
  rw [sum_Ico_eq_sum_range,show 4*(2*k+1)-3*(2*k+1)=2*k+1 by omega]
  refine sum_congr rfl fun r _ => ?_
  rw [levelLoss_eq_residueLoss s w (by omega) hp.pos]
  rw [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add]

private abbrev primeBand (M : ℕ) := (Ioc (2*M) (3*M)).filter Nat.Prime

private theorem band_mass : ∀ᶠ M : ℕ in atTop, (M:ℝ)/2 ≤ ∑ p ∈ primeBand M, Real.log p := by
  have h₃ := (_root_.RHTower.tendsto_chebyshevTheta_div (by norm_num : (0:ℝ)<3)).comp
    tendsto_natCast_atTop_atTop
  have h₂ := (_root_.RHTower.tendsto_chebyshevTheta_div (by norm_num : (0:ℝ)<2)).comp
    tendsto_natCast_atTop_atTop
  have ht := (h₃.sub h₂).eventually_const_lt (by norm_num : (1/2:ℝ) < 3-2)
  filter_upwards [ht,eventually_ge_atTop 1] with M h hM
  change 1/2 < Chebyshev.theta (3*M)/M - Chebyshev.theta (2*M)/M at h
  have hM0 : 0<(M:ℝ) := by exact_mod_cast hM
  rw [← sub_div,lt_div_iff₀ hM0] at h
  have he := _root_.RHTower.Sieve.theta_sub_theta_eq_sum_primesIn
    (show ((2*M:ℕ):ℝ) ≤ (3*M:ℕ) by exact_mod_cast (by omega : 2*M≤3*M))
  unfold _root_.RHTower.Sieve.primesIn at he
  rw [Nat.floor_natCast,Nat.floor_natCast] at he
  push_cast at he
  change _ ≤ ∑ p ∈ (Ioc (2*M) (3*M)).filter Nat.Prime, Real.log p
  rw [← he]
  linarith only [h]

/-- At every sufficiently large scale the lower bound holds simultaneously for
every width and base multiplier up to that scale. The number, coefficients and
residue slopes of the binomials may all vary with the scale. -/
theorem uniform_prime_level_error_on_every_scale {ι : Type*} :
    ∀ᶠ M : ℕ in atTop, ∀ (s : Finset ι) (w : ι → ℝ) (q L : ℕ),
      4≤q → q≤M → 0<L → L≤M → ∀ u v : (p : ℕ) → ι → ZMod p,
      ∃ n ∈ Ico (6*M) (12*M), (M:ℝ)/(24*q) ≤
        ∑ p ∈ (Ioc (2*M) (3*M)).filter Nat.Prime,
          Real.log p*binomialPrimeLevelLoss s w q L p (u p) (v p) n := by
  filter_upwards [band_mass] with M hband
  intro s w q L hq hqM hL hLM u v
  let D := fun p n => binomialPrimeLevelLoss s w q L p (u p) (v p) n
  have hq0 : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (by omega : 0<M)
  have hrow (p : ℕ) (hp : p ∈ primeBand M) :
      (M:ℝ)/q ≤ ∑ n ∈ Ico (6*M) (12*M), D p n := by
    obtain ⟨⟨hlo,hhi⟩,hp'⟩ := (show (2*M<p ∧ p≤3*M) ∧ p.Prime by
      simpa only [primeBand,mem_filter,mem_Ioc] using hp)
    have hsplit := Nat.mod_add_div p q
    have hrem := Nat.mod_lt p (by omega : 0<q)
    have hprod : M ≤ (p/q)*q := by rw [mul_comm]; omega
    calc
      _ ≤ ((p/q:ℕ):ℝ) := (div_le_iff₀ hq0).mpr (by exact_mod_cast hprod)
      _ ≤ _ := (prime_period_loss s w hp' (by omega) hq hL (by omega) (u p) (v p)).trans
        (sum_le_sum_of_subset_of_nonneg (fun n hn => by
          simp only [mem_Ico] at hn ⊢; omega) (fun _ _ _ => abs_nonneg _))
  have hsum : ((M:ℝ)/q)*(M/2) ≤
      ∑ n ∈ Ico (6*M) (12*M), ∑ p ∈ primeBand M, Real.log p*D p n := by
    calc
      _ ≤ ((M:ℝ)/q)*∑ p ∈ primeBand M, Real.log p :=
        mul_le_mul_of_nonneg_left hband (by positivity)
      _ ≤ ∑ p ∈ primeBand M, ∑ n ∈ Ico (6*M) (12*M), Real.log p*D p n := by
        rw [mul_sum]
        apply sum_le_sum
        intro p hp
        rw [← mul_sum,mul_comm ((M:ℝ)/q)]
        exact mul_le_mul_of_nonneg_left (hrow p hp)
          (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
      _ = _ := sum_comm
  by_contra! hn
  have hub : (∑ n ∈ Ico (6*M) (12*M), ∑ p ∈ primeBand M, Real.log p*D p n) ≤
      (6*(M:ℝ))*((M:ℝ)/(24*q)) := calc
    _ ≤ ∑ _n ∈ Ico (6*M) (12*M), (M:ℝ)/(24*q) := sum_le_sum fun n hn' => (hn n hn').le
    _ = _ := by rw [sum_const,nsmul_eq_mul,Nat.card_Ico,show 12*M-6*M=6*M by omega,Nat.cast_mul]; norm_num
  have he := hsum.trans hub
  field_simp [hq0.ne'] at he
  nlinarith only [he,sq_pos_of_pos hM0]

/-- On every sufficiently large scale, an ordinary-prime band alone supplies
linear absolute error for any signed combination of binomial carry levels.
The base multiplier is arbitrary, so rational slopes are included on their
common-denominator progression. -/
theorem linear_prime_level_error_on_every_scale {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) {q L : ℕ} (hq : 4≤q) (hL : 0<L)
    (u v : (p : ℕ) → ι → ZMod p) :
    ∀ᶠ M : ℕ in atTop, ∃ n ∈ Ico (6*M) (12*M), (M:ℝ)/(24*q) ≤
      ∑ p ∈ (Ioc (2*M) (3*M)).filter Nat.Prime,
        Real.log p*binomialPrimeLevelLoss s w q L p (u p) (v p) n := by
  filter_upwards [uniform_prime_level_error_on_every_scale (ι := ι),eventually_ge_atTop (max q L)] with M h hM
  exact h s w q L hq ((le_max_left _ _).trans hM) hL ((le_max_right _ _).trans hM) u v

/-- Logarithmic size of a finite weighted family of ordinary binomials. -/
def signedBinomialLog {ι : Type*} (s : Finset ι) (w : ι → ℝ) (a b : ι → ℕ) (n : ℕ) : ℝ :=
  ∑ i ∈ s, w i*Real.log (((a i*n+b i*n).choose (b i*n) : ℕ) : ℝ)

private theorem signedBinomialLog_eq_levels {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a b : ι → ℕ) (n X : ℕ) (hX : ∀ i ∈ s, a i*n+b i*n ≤ X) :
    signedBinomialLog s w a b n = ∑ m ∈ Icc 1 X,
      signedBinomialResidues s w (fun i => (a i : ZMod m)) (fun i => (b i : ZMod m)) n *
        ArithmeticFunction.vonMangoldt m := by
  unfold signedBinomialLog signedBinomialResidues
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [log_choose_eq_sum_mangoldt_carries (hX i hi),mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [binomialResidueCarry_natCast (mem_Icc.mp hm).1,mul_assoc]

private theorem dyadic_prime_mass_long_range (j N X : ℕ) (hX : 2^(j+1)*N≤X) :
    dyadicCommonPrimeMass j N =
      ∑ m ∈ Icc 1 X, (if 2^(j+1) ∣ 2^(j+1)*N/m+1 then (1:ℝ) else 0)*ArithmeticFunction.vonMangoldt m := by
  let q := 2^(j+1)
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  rw [dyadicCommonPrimeMass]
  calc
    _ = ∑ m ∈ Icc 1 (q*N), (if q ∣ q*N/m+1 then (1:ℝ) else 0)*ArithmeticFunction.vonMangoldt m := by
      refine sum_congr rfl fun m _ => ?_
      change ((if q ∣ q*N/m+1 then 1 else 0 : ℕ):ℝ)*_ = _
      split <;> norm_num
    _ = _ := by
      apply sum_subset (fun m hm => mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans hX⟩)
      intro m hm hno
      have hm0 := (mem_Icc.mp hm).1
      have hlt : q*N < m := by by_contra! he; exact hno (mem_Icc.mpr ⟨hm0,he⟩)
      have hnd : ¬ q∣1 := fun hd => (by have := Nat.le_of_dvd one_pos hd; omega)
      change (if q ∣ q*N/m+1 then (1:ℝ) else 0)*_ = 0
      rw [Nat.div_eq_of_lt hlt,zero_add,if_neg hnd,zero_mul]

/-- A finite signed family covering the selected Mangoldt levels exceeds the actual
logarithmic gcd by a positive linear amount somewhere on every large scale. -/
theorem finite_binomial_majorant_exceeds_gcd_linearly {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a b : ι → ℕ) {L j : ℕ} (hL : 0<L) (hj : 1≤j)
    (hcover : ∀ n m : ℕ, 0 < m → 0<ArithmeticFunction.vonMangoldt m →
      (if 2^(j+1) ∣ 2^(j+1)*(L*n)/m+1 then (1:ℝ) else 0) ≤
        signedBinomialResidues s w (fun i => (a i : ZMod m)) (fun i => (b i : ZMod m)) n) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ M : ℕ in atTop, ∃ n ∈ Ico (6*M) (12*M),
      Real.log (dyadicBinomialGcd j (L*n))+c*M ≤ signedBinomialLog s w a b n := by
  let q := 2^(j+1)
  have hq : 4≤q := pow_le_pow_right₀ (by omega : 1≤2) (by omega : 2≤j+1)
  have hq0 : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  obtain ⟨K,hK⟩ := exists_uniform_dyadicBinomialGcd_log_error
  let B := |K| * Real.sqrt ((q*L*12:ℕ):ℝ)
  have hsmall : Tendsto (fun M : ℕ => B/Real.sqrt M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨1/(48*q),by positivity,?_⟩
  filter_upwards [linear_prime_level_error_on_every_scale s w hq hL
      (fun p i => (a i : ZMod p)) (fun p i => (b i : ZMod p)),
    hsmall.eventually_lt_const (by positivity : 0<(1:ℝ)/(48*q)),eventually_ge_atTop 1]
    with M hM hsmallM hM1
  obtain ⟨n,hn,hband⟩ := hM
  refine ⟨n,hn,?_⟩
  let X := q*(L*n)+(∑ i ∈ s, (a i*n+b i*n))+3*M
  let e := fun m : ℕ => signedBinomialResidues s w (fun i => (a i : ZMod m)) (fun i => (b i : ZMod m)) n -
    (if q ∣ q*(L*n)/m+1 then (1:ℝ) else 0)
  have heq : signedBinomialLog s w a b n - dyadicCommonPrimeMass j (L*n) =
      ∑ m ∈ Icc 1 X, e m*ArithmeticFunction.vonMangoldt m := by
    have hall (i : ι) (hi : i∈s) : a i*n+b i*n≤X := by
      have hh := single_le_sum (f := fun i => a i*n+b i*n) (fun _ _ => Nat.zero_le _) hi
      dsimp only [X]; omega
    rw [signedBinomialLog_eq_levels s w a b n X hall,
      dyadic_prime_mass_long_range j (L*n) X (by dsimp only [X,q]; omega),← sum_sub_distrib]
    exact sum_congr rfl fun m _ => (sub_mul ..).symm
  have hcompare : (M:ℝ)/(24*q) ≤ signedBinomialLog s w a b n-dyadicCommonPrimeMass j (L*n) := by
    rw [heq]
    apply hband.trans
    calc
      _ = ∑ p ∈ primeBand M, e p*ArithmeticFunction.vonMangoldt p := by
        refine sum_congr rfl fun p hp => ?_
        have hp' := (mem_filter.mp hp).2
        have he : 0≤e p := sub_nonneg.mpr (hcover n p hp'.pos
          (ArithmeticFunction.vonMangoldt_pos_iff.mpr hp'.isPrimePow))
        change Real.log p * |e p| = _
        rw [abs_of_nonneg he,ArithmeticFunction.vonMangoldt_apply_prime hp',mul_comm]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hh := mem_Ioc.mp (mem_filter.mp hp).1
          exact mem_Icc.mpr ⟨(mem_filter.mp hp).2.pos,hh.2.trans (by dsimp only [X]; omega)⟩
        · intro m hm _
          by_cases hz : ArithmeticFunction.vonMangoldt m=0
          · rw [hz,mul_zero]
          · exact mul_nonneg (sub_nonneg.mpr (hcover n m (mem_Icc.mp hm).1
              (lt_of_le_of_ne ArithmeticFunction.vonMangoldt_nonneg (Ne.symm hz))))
              ArithmeticFunction.vonMangoldt_nonneg
  have hnt : q*(L*n)≤(q*L*12)*M := by
    have hh := Nat.mul_le_mul_left (q*L) (mem_Ico.mp hn).2.le
    simpa only [mul_assoc] using hh
  have hroot := (le_abs_self _).trans (hK j (L*n))
  have hE : Real.log (dyadicBinomialGcd j (L*n))-dyadicCommonPrimeMass j (L*n) ≤ B*Real.sqrt M := by
    apply hroot.trans
    have h := mul_le_mul (le_abs_self K) (Real.sqrt_le_sqrt (by exact_mod_cast hnt :
        ((q*(L*n):ℕ):ℝ) ≤ ((q*L*12*M:ℕ):ℝ))) (Real.sqrt_nonneg _) (abs_nonneg _)
    rw [Nat.cast_mul (q*L*12) M, Real.sqrt_mul (Nat.cast_nonneg _)] at h
    simpa only [B,mul_assoc] using h
  have hM0 : 0<(M:ℝ) := by exact_mod_cast hM1
  have hs := (div_lt_iff₀ (Real.sqrt_pos.mpr hM0)).mp hsmallM
  have hs' := mul_le_mul_of_nonneg_right hs.le (Real.sqrt_nonneg (M:ℝ))
  rw [mul_assoc ((1:ℝ)/(48*q)),Real.mul_self_sqrt hM0.le] at hs'
  have hid : (M:ℝ)/(24*q) = 2*((1/(48*q))*M) := by field_simp; ring
  rw [hid] at hcompare
  linarith only [hcompare,hE,hs']

#print axioms uniform_prime_level_error_on_every_scale
#print axioms linear_prime_level_error_on_every_scale
#print axioms finite_binomial_majorant_exceeds_gcd_linearly

end GaloisForLFunctions.ExceptionalLayerTheory
