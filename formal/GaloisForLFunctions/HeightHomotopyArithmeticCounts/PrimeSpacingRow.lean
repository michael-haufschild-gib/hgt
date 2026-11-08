import GaloisForLFunctions.ArithmeticEffectivityTheory.TheQDeformationOfTheHorizonPeriod
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheSpacingRegulatorRemovesTheAnomaly
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The sharp conductor weight for the mixed prime row

The actual spacing energy at conductors one and a prime is the logarithm of
an elementary cyclotomic value. Its error has no uniform bound on finite
unweighted ℓ² probes. Every positive conductor exponent restores square
summability and convergence of the entire prime row as the regulator vanishes.
-/

noncomputable section
open Finset Polynomial Complex Filter Topology Asymptotics
open scoped ComplexConjugate
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- The orbit at one reads the cyclotomic polynomial at the radius. -/
theorem torsionEnergy_one_cyclotomic (r : ℝ) (hr0 : 0<r) (hr1 : r<1)
    (n : ℕ) (hn : 0<n) :
    torsionEnergy r 1 n = -Real.log ‖eval (r:ℂ) (cyclotomic n ℂ)‖ := by
  rw [torsionEnergy, IsPrimitiveRoot.primitiveRoots_one, sum_singleton]
  simp only [one_mul]
  have hp : eval (r:ℂ) (cyclotomic n ℂ) =
      ∏ w ∈ primitiveRoots n ℂ, ((r:ℂ)-w) := by
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn.ne'), eval_prod]
    simp
  rw [hp, norm_prod, Real.log_prod]
  · rw [sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro w hw
    rw [norm_one_sub_mul_conj (norm_of_mem_primitiveRoots hw)]
  · intro w hw
    apply norm_ne_zero_iff.mpr
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_of_mem_primitiveRoots hw] at he
    exact hr1.ne he

/-- The prime orbit gives the logarithm of a positive geometric sum. -/
theorem torsionEnergy_one_prime (r : ℝ) (hr0 : 0<r) (hr1 : r<1)
    (p : ℕ) (hp : p.Prime) :
    torsionEnergy r 1 p = -Real.log (qInt p r) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [torsionEnergy_one_cyclotomic r hr0 hr1 p hp.pos,
    eval_cyclotomic_complex_ofReal, cyclotomic_prime, eval_finsetSum]
  simp only [eval_pow, eval_X]
  rw [Complex.norm_real]
  change -Real.log ‖qInt p r‖ = _
  rw [Real.norm_of_nonneg (qInt_pos hp.pos hr0).le]

/-- On the unit interval the geometric sum lies between one and its length. -/
theorem qInt_unit_bounds (n : ℕ) (hn : 0<n) (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1) :
    1≤qInt n r ∧ qInt n r≤n := by
  constructor
  · calc 1 = r^0 := (pow_zero r).symm
         _ ≤ qInt n r := single_le_sum (fun i _ => pow_nonneg hr0 i) (mem_range.mpr hn)
  · calc qInt n r ≤ ∑ _i ∈ range n, (1:ℝ) :=
          sum_le_sum fun i _ => pow_le_one₀ hr0 hr1
         _ = n := by simp

/-- The actual mixed spacing error at conductors one and a prime. -/
def primeSpacingError (ε : ℝ) (p : Nat.Primes) : ℝ :=
  twistedEnergy (spacingRadius ε 1 p) 1 p + Real.log p / Real.sqrt p

theorem primeSpacingError_eq (ε : ℝ) (hε : 0<ε) (p : Nat.Primes) :
    primeSpacingError ε p =
      (Real.log p-Real.log (qInt p (spacingRadius ε 1 p)))/Real.sqrt p := by
  rw [primeSpacingError, twistedEnergy, gcdTwist_eq, Nat.gcd_one_left]
  simp only [Nat.cast_one, Nat.totient_one, div_one, one_mul]
  have he := torsionEnergy_one_prime (spacingRadius ε 1 (p:ℕ))
    (show 0<spacingRadius ε 1 (p:ℕ) from Real.exp_pos _)
    (spacingRadius_lt_one hε zero_lt_one) (p:ℕ) p.property
  rw [he]
  ring

theorem primeSpacingError_bounds (ε : ℝ) (hε : 0<ε) (p : Nat.Primes) :
    0≤primeSpacingError ε p ∧ primeSpacingError ε p≤Real.log p/Real.sqrt p := by
  have hb := qInt_unit_bounds p p.property.pos (spacingRadius ε 1 p)
    (Real.exp_pos _).le (spacingRadius_lt_one hε zero_lt_one).le
  have hl0 := Real.log_nonneg hb.1
  have hl1 := Real.log_le_log (lt_of_lt_of_le zero_lt_one hb.1) hb.2
  rw [primeSpacingError_eq ε hε p]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hl1) (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right (sub_le_self _ hl0) (Real.sqrt_nonneg _)


/-- A fixed upper radius bounds every geometric sum independently of its length. -/
theorem qInt_le_geometric_bound (n : ℕ) (r R : ℝ) (hr : 0≤r)
    (hrR : r≤R) (hR : R<1) : qInt n r≤1/(1-R) := by
  have hR0 : 0≤R := hr.trans hrR
  have hgeom := geom_sum_mul R n
  have hpow := pow_nonneg hR0 n
  calc qInt n r ≤ qInt n R := sum_le_sum fun i _ => pow_le_pow_left₀ hr hrR i
       _ ≤ 1/(1-R) := by
         apply (le_div_iff₀ (sub_pos.mpr hR)).mpr
         change (∑ i ∈ range n, R^i)*(1-R)≤1
         nlinarith only [hgeom, hpow]

/-- The prime-row numerator grows at least logarithmically at every fixed regulator. -/
theorem primeSpacingError_lower (ε : ℝ) (hε : 0<ε) (p : Nat.Primes) :
    (Real.log p-Real.log (1/(1-Real.exp (-ε))))/Real.sqrt p ≤
      primeSpacingError ε p := by
  have hrR : spacingRadius ε 1 p≤Real.exp (-ε) := by
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_one, inv_one]
    have hpinv : 0≤((p:ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    nlinarith only [mul_nonneg hε.le hpinv]
  have hR : Real.exp (-ε)<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hε)
  have hq := qInt_le_geometric_bound p (spacingRadius ε 1 p) (Real.exp (-ε))
    (Real.exp_pos _).le hrR hR
  have hlog := Real.log_le_log (qInt_pos p.property.pos (Real.exp_pos _)) hq
  rw [primeSpacingError_eq ε hε p]
  exact div_le_div_of_nonneg_right (sub_le_sub_left hlog _) (Real.sqrt_nonneg _)

/-- For each fixed prime the mixed spacing error vanishes at the arithmetic boundary. -/
theorem tendsto_primeSpacingError (p : Nat.Primes) :
    Filter.Tendsto (fun ε : ℝ => primeSpacingError ε p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hqcont : Continuous (fun ε : ℝ => qInt p (spacingRadius ε 1 p)) := by
    unfold qInt spacingRadius
    fun_prop
  have hq0 : qInt p (spacingRadius 0 1 p)=(p:ℝ) := by
    simp only [spacingRadius, neg_zero, zero_mul, Real.exp_zero, qInt_one]
  have hqne : qInt p (spacingRadius 0 1 p)≠0 := by
    rw [hq0]
    exact_mod_cast p.property.ne_zero
  have hcont : ContinuousAt (fun ε : ℝ =>
      (Real.log p-Real.log (qInt p (spacingRadius ε 1 p)))/Real.sqrt p) 0 :=
    (continuousAt_const.sub (hqcont.continuousAt.log hqne)).div_const (Real.sqrt p)
  have hlim : Filter.Tendsto
      (fun ε : ℝ => (Real.log p-Real.log (qInt p (spacingRadius ε 1 p)))/Real.sqrt p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa only [hq0, sub_self, zero_div] using h
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (primeSpacingError_eq ε hε p).symm

/-- The zero conductor weight fails already on the row indexed by primes. -/
theorem not_summable_primeSpacingError_sq (ε : ℝ) (hε : 0<ε) :
    ¬ Summable (fun p : Nat.Primes => (primeSpacingError ε p)^2) := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  apply hs.of_norm_bounded_eventually
  have hpco : Filter.Tendsto (fun p : Nat.Primes => (p:ℕ)) Filter.cofinite Filter.atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p:ℕ))).tendsto_cofinite
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hpco)
  filter_upwards [hlog.eventually_ge_atTop (Real.log (1/(1-Real.exp (-ε)))+1)] with p hp
  simp only [Function.comp_apply] at hp
  have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
  have hsqrt := Real.sqrt_pos.mpr hp0
  have hlo := primeSpacingError_lower ε hε p
  have hunit : 1/Real.sqrt p≤primeSpacingError ε p := by
    apply le_trans _ hlo
    exact div_le_div_of_nonneg_right (by linarith only [hp]) hsqrt.le
  have he0 := (primeSpacingError_bounds ε hε p).1
  have hsq := mul_le_mul hunit hunit (by positivity) he0
  rw [Real.norm_of_nonneg (div_nonneg zero_le_one hp0.le)]
  calc (1:ℝ)/p = (1/Real.sqrt p)*(1/Real.sqrt p) := by
          rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hp0.le]
       _ ≤ (primeSpacingError ε p)^2 := by simpa only [pow_two] using hsq

/-- A logarithmic square is absorbed by any positive loss in a convergent power series. -/
private theorem summable_log_square_decay (δ : ℝ) (hδ : 0<δ) :
    Summable (fun n : ℕ => (Real.log n)^2*(n:ℝ)^(-(1+δ))) := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (half_pos hδ)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hO : (fun n : ℕ => (Real.log n)^2*(n:ℝ)^(-(1+δ))) =O[Filter.atTop]
      fun n : ℕ => ((n:ℝ)^(1+δ/2))⁻¹ := by
    have h := hlo.isBigO.mul (Asymptotics.isBigO_refl
      (fun n : ℕ => (n:ℝ)^(-(1+δ))) Filter.atTop)
    apply h.congr'
    · filter_upwards with n
      simp [Function.comp]
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn0 : (0:ℝ)<n := by exact_mod_cast hn
      simp only [Function.comp]
      rw [← Real.rpow_add hn0, ← Real.rpow_neg hn0.le]
      congr 1
      ring
  exact summable_of_isBigO_nat
    (Real.summable_nat_rpow_inv.mpr (by linarith only [hδ])) hO

/-- The weighted error is dominated by a logarithmic conductor majorant. -/
theorem primeSpacingError_weighted_bound (ε δ : ℝ) (hε : 0<ε) (p : Nat.Primes) :
    (primeSpacingError ε p)^2*(p:ℝ)^(-δ) ≤
      (Real.log p)^2*(p:ℝ)^(-(1+δ)) := by
  have hb := primeSpacingError_bounds ε hε p
  have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
  have hsq := mul_le_mul hb.2 hb.2 hb.1
    (div_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)) (Real.sqrt_nonneg _))
  calc (primeSpacingError ε p)^2*(p:ℝ)^(-δ) ≤
        (Real.log p/Real.sqrt p)^2*(p:ℝ)^(-δ) := by
          exact mul_le_mul_of_nonneg_right (by simpa only [pow_two] using hsq)
            (Real.rpow_nonneg hp0.le _)
       _ = (Real.log p)^2*(p:ℝ)^(-(1+δ)) := by
          rw [div_pow, Real.sq_sqrt hp0.le, div_eq_mul_inv, ← Real.rpow_neg_one,
            mul_assoc, ← Real.rpow_add hp0]
          congr 2
          ring

/-- Every positive conductor weight restores square summability of the actual prime row. -/
theorem summable_primeSpacingError_weighted (ε δ : ℝ) (hε : 0<ε) (hδ : 0<δ) :
    Summable (fun p : Nat.Primes => (primeSpacingError ε p)^2*(p:ℝ)^(-δ)) := by
  have hs : Summable (fun p : Nat.Primes => (Real.log p)^2*(p:ℝ)^(-(1+δ))) :=
    (summable_log_square_decay δ hδ).comp_injective
      (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p:ℕ)))
  exact hs.of_nonneg_of_le (fun p => mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (primeSpacingError_weighted_bound ε δ hε)

/-- Positive conductor weights are precisely the square-summable regime. -/
theorem summable_primeSpacingError_weighted_iff (ε δ : ℝ) (hε : 0<ε) :
    Summable (fun p : Nat.Primes => (primeSpacingError ε p)^2*(p:ℝ)^(-δ)) ↔ 0<δ := by
  constructor
  · intro hs
    by_contra hδ
    have hδ0 : 0≤-δ := neg_nonneg.mpr (le_of_not_gt hδ)
    apply not_summable_primeSpacingError_sq ε hε
    apply hs.of_nonneg_of_le (fun p => sq_nonneg _)
    intro p
    have h := Real.one_le_rpow (show (1:ℝ)≤p by exact_mod_cast p.property.one_lt.le) hδ0
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (sq_nonneg (primeSpacingError ε p))
  · exact summable_primeSpacingError_weighted ε δ hε

/-- The entire prime row converges in every positively weighted square norm. -/
theorem tendsto_tsum_primeSpacingError_weighted (δ : ℝ) (hδ : 0<δ) :
    Filter.Tendsto (fun ε : ℝ => ∑' p : Nat.Primes,
      (primeSpacingError ε p)^2*(p:ℝ)^(-δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hs : Summable (fun p : Nat.Primes => (Real.log p)^2*(p:ℝ)^(-(1+δ))) :=
    (summable_log_square_decay δ hδ).comp_injective
      (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p:ℕ)))
  have hpoint : ∀ p : Nat.Primes,
      Tendsto (fun ε : ℝ => (primeSpacingError ε p)^2*(p:ℝ)^(-δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0:ℝ)) := by
    intro p
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0), zero_mul] using
      ((tendsto_primeSpacingError p).pow 2).mul_const ((p:ℝ)^(-δ))
  have hbound : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ p : Nat.Primes,
      ‖(primeSpacingError ε p)^2*(p:ℝ)^(-δ)‖ ≤
        (Real.log p)^2*(p:ℝ)^(-(1+δ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε p
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
    exact primeSpacingError_weighted_bound ε δ hε p
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence (β := Nat.Primes) hs hpoint hbound

/-- No finite-support bound controls the unweighted squared row error. -/
theorem primeSpacingError_square_sums_unbounded (ε : ℝ) (hε : 0<ε) (C : ℝ) :
    ∃ S : Finset Nat.Primes, C < ∑ p ∈ S, (primeSpacingError ε p)^2 := by
  by_contra h
  push Not at h
  exact not_summable_primeSpacingError_sq ε hε
    (summable_of_sum_le (fun p => sq_nonneg (primeSpacingError ε p)) h)



/-- The mixed prime row does not define a uniformly bounded functional on finite ℓ² probes. -/
theorem primeSpacingError_no_unweighted_row_bound (ε : ℝ) (hε : 0<ε) :
    ¬ ∃ C : ℝ, ∀ (S : Finset Nat.Primes) (x : Nat.Primes → ℝ),
      |∑ p ∈ S, x p*primeSpacingError ε p| ≤ C*Real.sqrt (∑ p ∈ S, (x p)^2) := by
  rintro ⟨C, hC⟩
  obtain ⟨S, hS⟩ := primeSpacingError_square_sums_unbounded ε hε (C^2+1)
  let A := ∑ p ∈ S, (primeSpacingError ε p)^2
  have hA0 : 0<A := by
    change C^2+1<A at hS
    linarith only [hS, sq_nonneg C]
  have hB := Real.sqrt_pos.mpr hA0
  have h := hC S (primeSpacingError ε)
  simp only [← pow_two] at h
  change |A|≤C*Real.sqrt A at h
  rw [abs_of_pos hA0] at h
  have hmul : Real.sqrt A*Real.sqrt A≤C*Real.sqrt A := by
    rwa [Real.mul_self_sqrt hA0.le]
  have hBC : Real.sqrt A≤C := by nlinarith only [hmul, hB]
  have hsq := mul_le_mul hBC hBC hB.le (hB.le.trans hBC)
  rw [Real.mul_self_sqrt hA0.le] at hsq
  change C^2+1<A at hS
  nlinarith only [hS, hsq]


#print axioms torsionEnergy_one_prime
#print axioms primeSpacingError_bounds
#print axioms primeSpacingError_square_sums_unbounded
#print axioms not_summable_primeSpacingError_sq
#print axioms summable_primeSpacingError_weighted_iff
#print axioms tendsto_tsum_primeSpacingError_weighted
#print axioms primeSpacingError_no_unweighted_row_bound

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
