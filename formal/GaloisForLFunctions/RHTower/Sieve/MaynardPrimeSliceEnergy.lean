import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceLargeValues
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowBrunTitchmarsh
import GaloisForLFunctions.RHTower.Sieve.MaynardLocalPrimePowerLeakage

/-!
# Prime/proper-prime-power energy split for the physical Route T slice

The observation-cone packet is literally von Mangoldt.  This module splits its finite Dirichlet
polynomial into prime and proper-prime-power parts and retains the exact Brun--Titchmarsh saving in
the prime coefficient energy.  The result audits precisely what prime density can and cannot buy
at the transition seam.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

def routeTPrimeSliceCoeff (A B : ℕ) : Fin B → ℂ := fun m =>
  let n := (m : ℕ) + 1
  if A < n ∧ n.Prime then
    (((vonMangoldt n / (n : ℝ) : ℝ)) : ℂ)
  else 0

def routeTProperPrimePowerSliceCoeff (A B : ℕ) : Fin B → ℂ :=
  routeTVonMangoldtSliceCoeff A B - routeTPrimeSliceCoeff A B

theorem routeTVonMangoldtSliceCoeff_eq_prime_add_properPrimePower
    (A B : ℕ) :
    routeTVonMangoldtSliceCoeff A B =
      routeTPrimeSliceCoeff A B + routeTProperPrimePowerSliceCoeff A B := by
  rw [routeTProperPrimePowerSliceCoeff]
  abel

theorem dirPoly_routeTVonMangoldtSliceCoeff_eq_prime_add_properPrimePower
    (A B : ℕ) (y : ℝ) :
    dirPoly B (routeTVonMangoldtSliceCoeff A B) y =
      dirPoly B (routeTPrimeSliceCoeff A B) y +
        dirPoly B (routeTProperPrimePowerSliceCoeff A B) y := by
  rw [routeTVonMangoldtSliceCoeff_eq_prime_add_properPrimePower]
  simp only [dirPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem norm_routeTPrimeSliceCoeff_le
    {A B : ℕ} (hA : 1 ≤ A) {m : Fin B} :
    ‖routeTPrimeSliceCoeff A B m‖ ≤ Real.log B / A := by
  rw [routeTPrimeSliceCoeff]
  split_ifs with hm
  · have heq :
        (((vonMangoldt ((m : ℕ) + 1) /
          (((m : ℕ) + 1 : ℕ) : ℝ) : ℝ)) : ℂ) =
          routeTVonMangoldtSliceCoeff A B m := by
        rw [routeTVonMangoldtSliceCoeff, if_pos hm.1]
    rw [heq]
    exact norm_routeTVonMangoldtSliceCoeff_le hA
  · simp only [norm_zero]
    have hBpos : 0 < B := lt_of_le_of_lt (Nat.zero_le (m : ℕ)) m.isLt
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hBpos)) (by positivity)

/-- The exact prime count, rather than additive interval length, controls prime-slice energy. -/
theorem sum_normSq_routeTPrimeSliceCoeff_le_card
    {A B : ℕ} (hA : 1 ≤ A) :
    ∑ m : Fin B, ‖routeTPrimeSliceCoeff A B m‖ ^ 2 ≤
      (#{n ∈ Finset.Ioc A B | n.Prime} : ℝ) * (Real.log B / A) ^ 2 := by
  simp only [routeTPrimeSliceCoeff]
  rw [sum_fin_eq_sum_Icc B (fun n =>
    ‖(if A < n ∧ n.Prime then
      (((vonMangoldt n / (n : ℝ) : ℝ)) : ℂ) else 0)‖ ^ 2)]
  have hpoint : ∀ n ∈ Finset.Icc 1 B,
      ‖(if A < n ∧ n.Prime then
        (((vonMangoldt n / (n : ℝ) : ℝ)) : ℂ) else 0)‖ ^ 2 ≤
      if A < n ∧ n.Prime then (Real.log B / A) ^ 2 else 0 := by
    intro n hn
    by_cases hnp : A < n ∧ n.Prime
    · rw [if_pos hnp, if_pos hnp]
      have hnB := (Finset.mem_Icc.mp hn).2
      have hn0 : 0 < n := by omega
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg vonMangoldt_nonneg hnpos.le)]
      have hlog : Real.log n ≤ Real.log B :=
        Real.log_le_log hnpos (by exact_mod_cast hnB)
      have hlogB : 0 ≤ Real.log B :=
        Real.log_nonneg (by exact_mod_cast hA.trans (hnp.1.le.trans hnB))
      have hbound : vonMangoldt n / (n : ℝ) ≤ Real.log B / A := by
        calc
          vonMangoldt n / (n : ℝ) ≤ Real.log n / (n : ℝ) :=
            div_le_div_of_nonneg_right vonMangoldt_le_log hnpos.le
          _ ≤ Real.log B / (n : ℝ) :=
            div_le_div_of_nonneg_right hlog hnpos.le
          _ ≤ Real.log B / A :=
            div_le_div_of_nonneg_left hlogB (by exact_mod_cast hA)
              (by exact_mod_cast hnp.1.le)
      exact pow_le_pow_left₀ (div_nonneg vonMangoldt_nonneg hnpos.le) hbound 2
    · simp [hnp]
  calc
    ∑ n ∈ Finset.Icc 1 B,
        ‖(if A < n ∧ n.Prime then
          (((vonMangoldt n / (n : ℝ) : ℝ)) : ℂ) else 0)‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 B,
        if A < n ∧ n.Prime then (Real.log B / A) ^ 2 else 0 :=
      Finset.sum_le_sum hpoint
    _ = (#{n ∈ Finset.Ioc A B | n.Prime} : ℝ) * (Real.log B / A) ^ 2 := by
      rw [← Finset.sum_filter]
      have hset : {n ∈ Finset.Icc 1 B | A < n ∧ n.Prime} =
          {n ∈ Finset.Ioc A B | n.Prime} := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨_hn1, hnB⟩, hAn, hp⟩
          exact ⟨⟨hAn, hnB⟩, hp⟩
        · rintro ⟨⟨hAn, hnB⟩, hp⟩
          exact ⟨⟨hA.trans hAn.le, hnB⟩, hAn, hp⟩
      rw [hset, Finset.sum_const, nsmul_eq_mul]

/-- Parametric Brun--Titchmarsh energy bound.  Its saving is logarithmic; the free level `z`
retains the exact error term for later optimization. -/
theorem sum_normSq_routeTPrimeSliceCoeff_le_bt
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) {z : ℝ} (hz : 1 < z) :
    ∑ m : Fin B, ‖routeTPrimeSliceCoeff A B m‖ ^ 2 ≤
      (2 * ((B : ℝ) - (A : ℝ)) / Real.log z +
          6 * z * (1 + Real.log z) ^ 3 + 1) *
        (Real.log B / A) ^ 2 := by
  refine (sum_normSq_routeTPrimeSliceCoeff_le_card hA).trans ?_
  exact mul_le_mul_of_nonneg_right (card_prime_Ioc_le_bt hAB hz) (sq_nonneg _)

theorem card_largeValues_routeTPrimeSlice_finset_bt
    {A B : ℕ} (hA : 1 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B)
    {z : ℝ} (hz : 1 < z)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hbig : ∀ r ∈ S,
      V ≤ ‖dirPoly B (routeTPrimeSliceCoeff A B) (lam r)‖) :
    (S.card : ℝ) * V ^ 2 ≤
      (T + 4 * (B : ℝ) * (1 + Real.log B)) *
        (1 / delta + 2 * Real.log B) *
          ((2 * ((B : ℝ) - (A : ℝ)) / Real.log z +
              6 * z * (1 + Real.log z) ^ 3 + 1) *
            (Real.log B / A) ^ 2) := by
  exact (card_largeValues_dirPoly_finset B hB
    (routeTPrimeSliceCoeff A B) hdelta hT hV hgap hband hbig).trans
      (mul_le_mul_of_nonneg_left
        (sum_normSq_routeTPrimeSliceCoeff_le_bt hA hAB hz)
        (mul_nonneg (by positivity) (by positivity)))

theorem routeTProperPrimePowerSliceCoeff_apply
    (A B : ℕ) (m : Fin B) :
    routeTProperPrimePowerSliceCoeff A B m =
      if A < (m : ℕ) + 1 ∧ ¬ Nat.Prime ((m : ℕ) + 1) then
        (((vonMangoldt ((m : ℕ) + 1) /
          (((m : ℕ) + 1 : ℕ) : ℝ) : ℝ)) : ℂ)
      else 0 := by
  rw [routeTProperPrimePowerSliceCoeff, Pi.sub_apply,
    routeTVonMangoldtSliceCoeff, routeTPrimeSliceCoeff]
  by_cases hA : A < (m : ℕ) + 1 <;>
    by_cases hp : Nat.Prime ((m : ℕ) + 1) <;> simp [hA, hp]

/-- Proper prime-power von-Mangoldt mass in an additive slice has square-root width, rather than
full-width, size. -/
theorem sum_nonprime_vonMangoldt_Ioc_le_localPrimePower
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) (hwidth : 1 ≤ B - A) :
    ∑ n ∈ (Finset.Ioc A B).filter (fun n => ¬ n.Prime), vonMangoldt n ≤
      (Real.log B / Real.log 2) *
        (Real.sqrt ((B : ℝ) - A) + 1) * Real.log B := by
  have hpsi : Chebyshev.psi (B : ℝ) - Chebyshev.psi (A : ℝ) =
      ∑ n ∈ Finset.Ioc A B, (vonMangoldt n : ℝ) := by
    unfold Chebyshev.psi
    simp only [Nat.floor_natCast]
    rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => (vonMangoldt n : ℝ))
      (Nat.zero_le A) hAB]
    ring
  have htheta := RHTower.theta_window_eq hAB
  have hprime : Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ) =
      ∑ n ∈ (Finset.Ioc A B).filter Nat.Prime, (vonMangoldt n : ℝ) := by
    rw [htheta]
    apply Finset.sum_congr rfl
    intro n hn
    rw [vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc A B) Nat.Prime (fun n => (vonMangoldt n : ℝ))
  have hproper :
      (∑ n ∈ (Finset.Ioc A B).filter (fun n => ¬ n.Prime), vonMangoldt n) =
        (Chebyshev.psi (B : ℝ) - Chebyshev.psi (A : ℝ)) -
          (Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ)) := by
    rw [hpsi, hprime]
    linarith
  rw [hproper]
  have hwidthR : (1 : ℝ) ≤ (B : ℝ) - (A : ℝ) := by
    have hcast : (1 : ℝ) ≤ ((B - A : ℕ) : ℝ) := by exact_mod_cast hwidth
    rw [Nat.cast_sub hAB] at hcast
    exact hcast
  have hlocal := chebyshevPsi_window_le_theta_window_add_local_primePower
    (show (2 : ℝ) ≤ (A : ℝ) by exact_mod_cast hA)
      (show (A : ℝ) ≤ (B : ℝ) by exact_mod_cast hAB) hwidthR
  linarith

/-- The proper-prime-power coefficient energy retains square-root additive support.  This makes
that component power-negligible at the uncertainty seam; only true primes can remain critical. -/
theorem sum_normSq_routeTProperPrimePowerSliceCoeff_le_local
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) (hwidth : 1 ≤ B - A) :
    ∑ m : Fin B, ‖routeTProperPrimePowerSliceCoeff A B m‖ ^ 2 ≤
      (Real.log B / (A : ℝ) ^ 2) *
        ((Real.log B / Real.log 2) *
          (Real.sqrt ((B : ℝ) - A) + 1) * Real.log B) := by
  simp only [routeTProperPrimePowerSliceCoeff_apply]
  rw [sum_fin_eq_sum_Icc B (fun n =>
    ‖(if A < n ∧ ¬ n.Prime then
      (((vonMangoldt n / (n : ℝ) : ℝ)) : ℂ) else 0)‖ ^ 2)]
  let C : ℝ := Real.log B / (A : ℝ) ^ 2
  have hpoint : ∀ n ∈ Finset.Icc 1 B,
      ‖(if A < n ∧ ¬ n.Prime then
        (((vonMangoldt n / (n : ℝ) : ℝ)) : ℂ) else 0)‖ ^ 2 ≤
      if A < n ∧ ¬ n.Prime then C * vonMangoldt n else 0 := by
    intro n hn
    by_cases hnp : A < n ∧ ¬ n.Prime
    · rw [if_pos hnp, if_pos hnp]
      have hnB := (Finset.mem_Icc.mp hn).2
      have hn0 : 0 < n := by omega
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg vonMangoldt_nonneg hnpos.le)]
      have hlogB : 0 ≤ Real.log B :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
      have hlam : vonMangoldt n / (n : ℝ) ≤ vonMangoldt n / A :=
        div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity)
          (by exact_mod_cast hnp.1.le)
      have hlog : vonMangoldt n / (n : ℝ) ≤ Real.log B / A := by
        have hnlog : Real.log n ≤ Real.log B :=
          Real.log_le_log hnpos (by exact_mod_cast hnB)
        calc
          vonMangoldt n / (n : ℝ) ≤ Real.log n / (n : ℝ) :=
            div_le_div_of_nonneg_right vonMangoldt_le_log hnpos.le
          _ ≤ Real.log B / (n : ℝ) :=
            div_le_div_of_nonneg_right hnlog hnpos.le
          _ ≤ Real.log B / A :=
            div_le_div_of_nonneg_left hlogB (by positivity)
              (by exact_mod_cast hnp.1.le)
      have hmul :
          (vonMangoldt n / (n : ℝ)) * (vonMangoldt n / (n : ℝ)) ≤
            (Real.log B / A) * (vonMangoldt n / A) :=
        mul_le_mul hlog hlam (div_nonneg vonMangoldt_nonneg (by positivity))
          (div_nonneg hlogB (by positivity))
      rw [pow_two]
      calc
        (vonMangoldt n / (n : ℝ)) * (vonMangoldt n / (n : ℝ)) ≤
            (Real.log B / A) * (vonMangoldt n / A) := hmul
        _ = C * vonMangoldt n := by
          dsimp only [C]
          ring
    · simp [hnp]
  calc
    ∑ n ∈ Finset.Icc 1 B,
        ‖(if A < n ∧ ¬ n.Prime then
          (((vonMangoldt n / (n : ℝ) : ℝ)) : ℂ) else 0)‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 B,
        if A < n ∧ ¬ n.Prime then C * vonMangoldt n else 0 :=
      Finset.sum_le_sum hpoint
    _ = C * ∑ n ∈ (Finset.Ioc A B).filter (fun n => ¬ n.Prime),
        vonMangoldt n := by
      rw [← Finset.sum_filter]
      have hset : {n ∈ Finset.Icc 1 B | A < n ∧ ¬ n.Prime} =
          (Finset.Ioc A B).filter (fun n => ¬ n.Prime) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨_hn1, hnB⟩, hAn, hnp⟩
          exact ⟨⟨hAn, hnB⟩, hnp⟩
        · rintro ⟨⟨hAn, hnB⟩, hnp⟩
          exact ⟨⟨(show 1 ≤ A by omega).trans hAn.le, hnB⟩, hAn, hnp⟩
      rw [hset, Finset.mul_sum]
    _ ≤ C * ((Real.log B / Real.log 2) *
          (Real.sqrt ((B : ℝ) - A) + 1) * Real.log B) := by
      apply mul_le_mul_of_nonneg_left
        (sum_nonprime_vonMangoldt_Ioc_le_localPrimePower hA hAB hwidth)
      dsimp only [C]
      exact div_nonneg (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ B by omega))) (sq_nonneg _)

/-- The square-root-width proper-prime-power scale fits Route T's second alternative under the
exact budget `mu * (1/2 - nu) + eta <= 3/2`. -/
theorem routeT_properPrimePowerSlice_power_le_secondAlternative
    {T x mu alpha eta : ℝ} (hT : 1 ≤ T) (hx : x = T ^ mu)
    (hbudget : mu * (1 / 2 - routeTGapMomentNu) + eta ≤ 3 / 2) :
    T ^ eta * (T ^ (-(1 : ℝ) / 2) * x ^ (3 / 2 - 2 * alpha)) ≤
      T * x ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  rw [hx]
  rw [← Real.rpow_mul hT0, ← Real.rpow_mul hT0]
  calc
    T ^ eta * (T ^ (-(1 : ℝ) / 2) *
        T ^ (mu * (3 / 2 - 2 * alpha))) =
      T ^ (eta + (-(1 : ℝ) / 2 + mu * (3 / 2 - 2 * alpha))) := by
        rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
    _ ≤ T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha)) := by
      apply Real.rpow_le_rpow_of_exponent_le hT
      linarith
    _ = T * T ^ (mu * (1 + routeTGapMomentNu - 2 * alpha)) := by
      rw [Real.rpow_add hTpos, Real.rpow_one]

/-- Corpus constants give the proper-prime-power slice a full power of reserve on the complete
Route T range `mu <= 8`. -/
theorem routeT_properPrimePowerSlice_fixed_reserve_full_range
    {mu : ℝ} (hmu : mu ≤ 8) :
    mu * (1 / 2 - routeTGapMomentNu) + 1 ≤ 3 / 2 := by
  have hd : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hhalf : 1 / 2 - routeTGapMomentNu =
      maynardLongGlobalAmplitudeDeficit / 2 := by
    rw [routeTGapMomentNu]
    ring
  rw [hhalf]
  have hd0 : 0 ≤ maynardLongGlobalAmplitudeDeficit / 2 := by
    positivity [maynardLongGlobalAmplitudeDeficit_pos]
  have hmul : mu * (maynardLongGlobalAmplitudeDeficit / 2) ≤
      8 * (1 / 200 : ℝ) := by
    calc
      mu * (maynardLongGlobalAmplitudeDeficit / 2) ≤
          8 * (maynardLongGlobalAmplitudeDeficit / 2) :=
        mul_le_mul_of_nonneg_right hmu hd0
      _ ≤ 8 * (1 / 200 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith
  linarith

end RHTower.Sieve
