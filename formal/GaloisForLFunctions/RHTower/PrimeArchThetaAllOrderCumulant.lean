import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# All-order theta-cusp cumulant recurrence

The normalized continued prime--Gamma moment germ `G` satisfies the local differential identity

`XiC' + z G XiC = 0`.

The earlier theta-cusp module expanded this identity separately in derivative orders `1`, `3`,
and `5`.  Here one parity-uniform recurrence replaces those finite calculations.  The Xi jets are
written directly in terms of the raw even moments of the positive theta-cusp source, while the jets
of `z G` are factorial multiples of the normalized prime--archimedean moments.

At odd order `2n+1`, the last summand is

`(2n+1)! * thetaCuspRawEvenMoment 0 * normalizedPrimeArchMoment n`.

Since the zeroth raw theta moment is positive, the recurrence determines the `n`th logarithmic
cumulant from the raw theta moments and the lower cumulants.  Thus the countable source Hankel
criterion is an explicit all-order hierarchy of finite theta-moment inequalities.  This is a
source reduction, not a proof that those inequalities are nonnegative.
-/

open Complex Set Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- The `k`th central Xi jet, expressed using the raw moments of the positive theta-cusp source.
Odd jets vanish; the even jet `2j` is `(-1)^j` times raw moment `j`. -/
def thetaCuspXiJet (k : ℕ) : ℂ :=
  if Even k then
    (((-1 : ℝ) ^ (k / 2) * thetaCuspRawEvenMoment (k / 2) : ℝ) : ℂ)
  else 0

/-- Every central Xi jet is the corresponding parity-coded raw theta-cusp moment. -/
theorem iteratedDeriv_XiC_zero_eq_thetaCuspXiJet (k : ℕ) :
    iteratedDeriv k XiC 0 = thetaCuspXiJet k := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [thetaCuspXiJet, if_pos hk]
    nth_rewrite 1 [← Nat.two_mul_div_two_of_even hk]
    exact iteratedDeriv_XiC_zero_eq_rawEvenMoment (k / 2)
  · rw [thetaCuspXiJet, if_neg (Nat.not_even_iff_odd.mpr hk)]
    exact iteratedDeriv_XiC_odd_zero hk

/-- The `k`th central jet of `z G(z)`, where `G` is the normalized continued prime--Gamma moment
germ.  Even jets vanish; the odd jet `2j+1` is `(2j+1)!` times moment `j`. -/
def thetaCuspPrimeArchProductJet (k : ℕ) : ℂ :=
  if Odd k then
    ((k.factorial : ℕ) : ℂ) * (normalizedPrimeArchMoment ((k - 1) / 2) : ℝ)
  else 0

/-- Exact parity formula for every jet of `z G(z)` at the center. -/
theorem iteratedDeriv_id_mul_normalizedPrimeArchMomentGerm_zero (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 =
      thetaCuspPrimeArchProductJet k := by
  rcases k with _ | m
  · simp [thetaCuspPrimeArchProductJet, iteratedDeriv_zero]
  · have hG : AnalyticAt ℂ normalizedPrimeArchMomentGerm 0 :=
      analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
    rw [iteratedDeriv_id_mul_zero_succ normalizedPrimeArchMomentGerm m hG.contDiffAt]
    by_cases hk : Odd (m + 1)
    · rw [thetaCuspPrimeArchProductJet, if_pos hk]
      have hm : Even m := by
        obtain ⟨r, hr⟩ := hk
        refine ⟨r, ?_⟩
        omega
      have hmrep : 2 * (m / 2) = m := Nat.two_mul_div_two_of_even hm
      have hder := iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul (m / 2)
      rw [hmrep] at hder
      rw [hder]
      simp only [normalizedPrimeArchMoment]
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      ring
    · rw [thetaCuspPrimeArchProductJet, if_neg hk]
      have hkmEven : Even (m + 1) := Nat.not_odd_iff_even.mp hk
      have hmOdd : Odd m := by
        obtain ⟨r, hr⟩ := hkmEven
        by_cases hm0 : m = 0
        · subst m
          omega
        · refine ⟨r - 1, ?_⟩
          omega
      rw [iteratedDeriv_normalizedPrimeArchMomentGerm_odd_zero hmOdd, mul_zero]

/-- **All-order theta-cusp cumulant recurrence.**  This is Leibniz applied at the center to
`XiC' + z G XiC = 0`, with both factors replaced by their explicit parity-coded jet sequences. -/
theorem thetaCusp_allOrderCumulantRecurrence (N : ℕ) :
    thetaCuspXiJet (N + 1) +
      ∑ i ∈ Finset.range (N + 1),
        ((N.choose i : ℕ) : ℂ) * thetaCuspPrimeArchProductJet i *
          thetaCuspXiJet (N - i) = 0 := by
  have h := normalizedPrimeArch_differential_identity.iteratedDeriv_eq N
  have hXi : AnalyticAt ℂ XiC 0 := XiC_analytic 0 (Set.mem_univ 0)
  have hG : AnalyticAt ℂ normalizedPrimeArchMomentGerm 0 :=
    analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
  have hZG : AnalyticAt ℂ (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) 0 :=
    analyticAt_id.mul hG
  change iteratedDeriv N
    (deriv XiC + (fun z : ℂ => z * normalizedPrimeArchMomentGerm z) * XiC) 0 =
      iteratedDeriv N (fun _ : ℂ => 0) 0 at h
  rw [iteratedDeriv_add hXi.deriv.contDiffAt (hZG.mul hXi).contDiffAt,
    iteratedDeriv_mul hZG.contDiffAt hXi.contDiffAt] at h
  have hshift : iteratedDeriv N (deriv XiC) 0 = iteratedDeriv (N + 1) XiC 0 :=
    (congrFun (iteratedDeriv_succ' (f := XiC) (n := N)) 0).symm
  rw [hshift, iteratedDeriv_XiC_zero_eq_thetaCuspXiJet,
    iteratedDeriv_const] at h
  simp only [ite_self] at h
  simpa only [iteratedDeriv_id_mul_normalizedPrimeArchMomentGerm_zero,
    iteratedDeriv_XiC_zero_eq_thetaCuspXiJet] using h

/-- At odd order `2n+1`, isolate the newest cumulant.  The remaining finite sum only contains
product jets of order `< 2n+1`, hence normalized moments of index `< n`. -/
theorem normalizedPrimeArchMoment_recursive (n : ℕ) :
    ((((2 * n + 1).factorial : ℕ) : ℂ) *
        (thetaCuspRawEvenMoment 0 : ℂ) *
        (normalizedPrimeArchMoment n : ℂ)) =
      -thetaCuspXiJet (2 * n + 2) -
        ∑ i ∈ Finset.range (2 * n + 1),
          ((((2 * n + 1).choose i : ℕ) : ℂ) *
            thetaCuspPrimeArchProductJet i *
              thetaCuspXiJet (2 * n + 1 - i)) := by
  have h := thetaCusp_allOrderCumulantRecurrence (2 * n + 1)
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega,
    Finset.sum_range_succ] at h
  have hodd : Odd (2 * n + 1) := ⟨n, by omega⟩
  have hjet0 : thetaCuspXiJet 0 = (thetaCuspRawEvenMoment 0 : ℂ) := by
    simp [thetaCuspXiJet]
  rw [thetaCuspPrimeArchProductJet, if_pos hodd] at h
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
    hjet0] at h
  have hidx : (2 * n + 1 - 1) / 2 = n := by omega
  rw [hidx] at h
  linear_combination h

/-- Exact source-side endpoint: countable integer-polynomial positivity of the recursively
theta-determined cumulant sequence is equivalent to RH. -/
theorem primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis :
    PrimeArchSourceTraceHankelIntNonnegative ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
  · intro hRH p
    rw [← xiCentralTraceHankel_eq_primeArchSourceTraceHankel]
    exact xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH p

end

end RHTower
