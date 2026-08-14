import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalObservationCone
import GaloisForLFunctions.RHTower.Sieve.DirichletFiniteSetLargeValues
import GaloisForLFunctions.RHTower.Sieve.TwistedSeriesAsDirichletPoly
import GaloisForLFunctions.RHTower.Sieve.MaynardTwoAlternativeGapReceiver

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

def routeTVonMangoldtSliceCoeff (A B : ℕ) : Fin B → ℂ := fun m =>
  if A < (m : ℕ) + 1 then
    (((vonMangoldt ((m : ℕ) + 1) / (((m : ℕ) + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
  else 0

/-- Von-Mangoldt sequence restricted to one natural additive slice. -/
def routeTVonMangoldtSliceSequence (A B : ℕ) (n : ℕ) : ℂ :=
  if A < n ∧ n ≤ B then ((vonMangoldt n : ℝ) : ℂ) else 0

@[simp] theorem routeTVonMangoldtSliceSequence_zero (A B : ℕ) :
    routeTVonMangoldtSliceSequence A B 0 = 0 := by
  simp [routeTVonMangoldtSliceSequence]

/-- The explicit `sigma=1` slice coefficients are the standard twisted truncation. -/
theorem routeTVonMangoldtSliceCoeff_eq_twistedTruncCoeff
    (A B : ℕ) :
    routeTVonMangoldtSliceCoeff A B =
      twistedTruncCoeff (routeTVonMangoldtSliceSequence A B) 1 B := by
  funext m
  have hmB : (m : ℕ) + 1 ≤ B := by omega
  rw [routeTVonMangoldtSliceCoeff, twistedTruncCoeff,
    routeTVonMangoldtSliceSequence]
  by_cases hmA : A < (m : ℕ) + 1
  · rw [if_pos hmA, if_pos ⟨hmA, hmB⟩]
    rw [show -(1 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    push_cast
    field_simp
  · rw [if_neg hmA, if_neg (by exact fun h => hmA h.1), zero_mul]

/-- The physical slice is exactly one Dirichlet polynomial on the line `sigma=1`. -/
theorem sum_twisted_routeTVonMangoldtSliceSequence_eq_dirPoly
    (A B : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.range (B + 1),
        twistedSummand (routeTVonMangoldtSliceSequence A B)
          ((1 : ℂ) + (y : ℝ) * I) n =
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) := by
  rw [routeTVonMangoldtSliceCoeff_eq_twistedTruncCoeff]
  exact sum_range_twistedSummand_eq_dirPoly
    (routeTVonMangoldtSliceSequence_zero A B) 1 y B

/-- Removing the zeros outside `(A,B]` gives the literal finite von-Mangoldt slice. -/
theorem sum_Ioc_twisted_vonMangoldt_eq_dirPoly
    (A B : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.Ioc A B,
        twistedSummand (fun n : ℕ => ((vonMangoldt n : ℝ) : ℂ))
          ((1 : ℂ) + (y : ℝ) * I) n =
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) := by
  have hsub : Finset.Ioc A B ⊆ Finset.range (B + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by
      have := (Finset.mem_Ioc.mp hn).2
      omega)
  have hzero : ∀ n ∈ Finset.range (B + 1), n ∉ Finset.Ioc A B →
      twistedSummand (routeTVonMangoldtSliceSequence A B)
        ((1 : ℂ) + (y : ℝ) * I) n = 0 := by
    intro n hnRange hnIoc
    have hz : ¬ (A < n ∧ n ≤ B) := by
      intro h
      exact hnIoc (Finset.mem_Ioc.mpr h)
    simp [twistedSummand, routeTVonMangoldtSliceSequence, hz]
  calc
    ∑ n ∈ Finset.Ioc A B,
        twistedSummand (fun n : ℕ => ((vonMangoldt n : ℝ) : ℂ))
          ((1 : ℂ) + (y : ℝ) * I) n =
      ∑ n ∈ Finset.Ioc A B,
        twistedSummand (routeTVonMangoldtSliceSequence A B)
          ((1 : ℂ) + (y : ℝ) * I) n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnAB := Finset.mem_Ioc.mp hn
      simp [twistedSummand, routeTVonMangoldtSliceSequence, hnAB]
    _ = ∑ n ∈ Finset.range (B + 1),
        twistedSummand (routeTVonMangoldtSliceSequence A B)
          ((1 : ℂ) + (y : ℝ) * I) n :=
      Finset.sum_subset hsub hzero
    _ = dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) :=
      sum_twisted_routeTVonMangoldtSliceSequence_eq_dirPoly A B y

/-- Inside the open physical cone, the observed Heath--Brown slice and the literal von-Mangoldt
Dirichlet polynomial agree pointwise on the critical Perron line. -/
theorem sum_Ioc_twisted_observedPacket_eq_dirPoly
    (L X k A B : ℕ) (hXL : X < (L + 1) ^ k) {T t N R y : ℝ}
    (hT : 1 < T)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T ^ t ≤ N)
    (hNA : N ≤ A) (hBEnd : (B : ℝ) < N + 2 * R)
    (hBX : B ≤ X) :
    ∑ n ∈ Finset.Ioc A B,
        twistedSummand
          (complexCoeff (heathBrownObservedEligiblePacket L X k T t N R))
          ((1 : ℂ) + (y : ℝ) * I) n =
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) := by
  rw [← sum_Ioc_twisted_vonMangoldt_eq_dirPoly A B y]
  apply Finset.sum_congr rfl
  intro n hn
  have hnAB := Finset.mem_Ioc.mp hn
  have hnN : N < (n : ℝ) := lt_of_le_of_lt hNA (by exact_mod_cast hnAB.1)
  have hnEnd : (n : ℝ) < N + 2 * R :=
    (by exact_mod_cast hnAB.2 : (n : ℝ) ≤ B).trans_lt hBEnd
  have hnX : n ≤ X := hnAB.2.trans hBX
  rw [twistedSummand,
    complexCoeff_heathBrownObservedEligiblePacket_eq_vonMangoldt
      L X k hXL hT hscale hnN hnEnd hnX]
  rfl

theorem norm_routeTVonMangoldtSliceCoeff_le
    {A B : ℕ} (hA : 1 ≤ A) {m : Fin B} :
    ‖routeTVonMangoldtSliceCoeff A B m‖ ≤ Real.log B / A := by
  have hBpos : 0 < B := lt_of_le_of_lt (Nat.zero_le (m : ℕ)) m.isLt
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hBpos)
  rw [routeTVonMangoldtSliceCoeff]
  split_ifs with hm
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]
    have hnB : (m : ℕ) + 1 ≤ B := by omega
    have hnpos : (0 : ℝ) < (((m : ℕ) + 1 : ℕ) : ℝ) := by positivity
    have hlog : Real.log (((m : ℕ) + 1 : ℕ) : ℝ) ≤ Real.log B := by
      exact Real.log_le_log hnpos (by exact_mod_cast hnB)
    have hlogB : 0 ≤ Real.log B := hlogB0
    calc
      vonMangoldt ((m : ℕ) + 1) / (((m : ℕ) + 1 : ℕ) : ℝ) ≤
          Real.log (((m : ℕ) + 1 : ℕ) : ℝ) /
            (((m : ℕ) + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right vonMangoldt_le_log hnpos.le
      _ ≤ Real.log B / (((m : ℕ) + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hlog hnpos.le
      _ ≤ Real.log B / A := by
        exact div_le_div_of_nonneg_left hlogB (by exact_mod_cast hA)
          (by exact_mod_cast hm.le)
  · simp only [norm_zero]
    exact div_nonneg hlogB0 (by positivity)

theorem sum_normSq_routeTVonMangoldtSliceCoeff_le
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ m : Fin B, ‖routeTVonMangoldtSliceCoeff A B m‖ ^ 2 ≤
      ((B - A : ℕ) : ℝ) * (Real.log B / A) ^ 2 := by
  simp only [routeTVonMangoldtSliceCoeff]
  rw [sum_fin_eq_sum_Icc B (fun n =>
    ‖(if A < n then (((vonMangoldt n / (n : ℝ)) : ℝ) : ℂ) else 0)‖ ^ 2)]
  have hpoint : ∀ n : ℕ,
      ‖(if A < n then (((vonMangoldt n / (n : ℝ)) : ℝ) : ℂ) else 0)‖ ^ 2 =
        if A < n then ‖(((vonMangoldt n / (n : ℝ)) : ℝ) : ℂ)‖ ^ 2 else 0 := by
    intro n
    by_cases hn : A < n <;> simp [hn]
  simp_rw [hpoint]
  have hset : {n ∈ Finset.Icc 1 B | A < n} = Finset.Ioc A B := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_filter]
  rw [hset]
  calc
    ∑ n ∈ Finset.Ioc A B,
        ‖(((vonMangoldt n / (n : ℝ)) : ℝ) : ℂ)‖ ^ 2 ≤
      ∑ _n ∈ Finset.Ioc A B, (Real.log B / A) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnAB := Finset.mem_Ioc.mp hn
        have hn0 : 0 < n := by omega
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]
        have hbound : vonMangoldt n / (n : ℝ) ≤ Real.log B / A := by
          have hlog : Real.log n ≤ Real.log B :=
            Real.log_le_log hnpos (by exact_mod_cast hnAB.2)
          have hlogB : 0 ≤ Real.log B :=
            Real.log_nonneg (by exact_mod_cast hA.trans hAB)
          calc
            vonMangoldt n / (n : ℝ) ≤ Real.log n / (n : ℝ) :=
              div_le_div_of_nonneg_right vonMangoldt_le_log hnpos.le
            _ ≤ Real.log B / (n : ℝ) :=
              div_le_div_of_nonneg_right hlog hnpos.le
            _ ≤ Real.log B / A := by
              exact div_le_div_of_nonneg_left hlogB (by exact_mod_cast hA)
                (by exact_mod_cast hnAB.1.le)
        exact pow_le_pow_left₀ (div_nonneg vonMangoldt_nonneg hnpos.le) hbound 2
    _ = ((B - A : ℕ) : ℝ) * (Real.log B / A) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]

theorem card_largeValues_routeTVonMangoldtSlice_finset
    {A B : ℕ} (hA : 1 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hbig : ∀ r ∈ S,
      V ≤ ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (lam r)‖) :
    (S.card : ℝ) * V ^ 2 ≤
      (T + 4 * (B : ℝ) * (1 + Real.log B)) *
        (1 / delta + 2 * Real.log B) *
          (((B - A : ℕ) : ℝ) * (Real.log B / A) ^ 2) := by
  exact (card_largeValues_dirPoly_finset B hB
    (routeTVonMangoldtSliceCoeff A B) hdelta hT hV hgap hband hbig).trans
      (mul_le_mul_of_nonneg_left
        (sum_normSq_routeTVonMangoldtSliceCoeff_le hA hAB)
        (mul_nonneg
          (by positivity)
          (by positivity)))

/-- Exact power comparison between the physical-slice mean-square scale and Route T's second
large-value alternative.  It isolates the method's genuine phase boundary:
`mu * (1 - nu) + eta <= 2`. -/
theorem routeT_physicalSlice_power_le_secondAlternative
    {T x mu alpha eta : ℝ} (hT : 1 ≤ T) (hx : x = T ^ mu)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    T ^ eta * (T⁻¹ * x ^ (2 - 2 * alpha)) ≤
      T * x ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  rw [hx]
  rw [← Real.rpow_mul hT0, ← Real.rpow_mul hT0]
  calc
    T ^ eta * (T⁻¹ * T ^ (mu * (2 - 2 * alpha))) =
        T ^ (eta + (-1 + mu * (2 - 2 * alpha))) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
    _ ≤ T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha)) := by
      apply Real.rpow_le_rpow_of_exponent_le hT
      linarith
    _ = T * T ^ (mu * (1 + routeTGapMomentNu - 2 * alpha)) := by
      rw [Real.rpow_add hTpos, Real.rpow_one]

/-- With the corpus's explicit gap-moment exponent, the physical slice has a fixed `1/100`
power reserve throughout `mu <= 39/10`. -/
theorem routeT_physicalSlice_fixed_reserve_below_threePointNine
    {mu : ℝ} (hmu : mu ≤ 39 / 10) :
    mu * (1 - routeTGapMomentNu) + 1 / 100 ≤ 2 := by
  have hd : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hnu : 1 - routeTGapMomentNu < 101 / 200 := by
    dsimp only [routeTGapMomentNu]
    linarith
  have hmul : mu * (1 - routeTGapMomentNu) ≤
      (39 / 10) * (101 / 200) := by
    have hnu0 : 0 ≤ 1 - routeTGapMomentNu := by
      linarith [routeTGapMomentNu_lt_half]
    calc
      mu * (1 - routeTGapMomentNu) ≤
          (39 / 10) * (1 - routeTGapMomentNu) :=
        mul_le_mul_of_nonneg_right hmu hnu0
      _ ≤ (39 / 10) * (101 / 200) := by
        exact mul_le_mul_of_nonneg_left hnu.le (by norm_num)
  linarith

/-- At the nominal `mu = 4` transition the physical-slice method misses Route T's required
second-alternative exponent by exactly twice the corpus's positive gap-moment deficit. -/
theorem routeT_physicalSlice_critical_excess_identity :
    4 * (1 - routeTGapMomentNu) =
      2 + 2 * maynardLongGlobalAmplitudeDeficit := by
  rw [routeTGapMomentNu]
  ring

theorem routeT_physicalSlice_budget_fails_at_four :
    2 < 4 * (1 - routeTGapMomentNu) := by
  rw [routeT_physicalSlice_critical_excess_identity]
  linarith [maynardLongGlobalAmplitudeDeficit_pos]

/-- Any nonnegative reserve compatible with the physical-slice power comparison forces the
height exponent strictly below four.  Consequently logarithmic prime-density savings cannot
extend this receiver to `mu = 4`. -/
theorem routeT_physicalSlice_nonnegative_budget_forces_mu_lt_four
    {mu eta : ℝ} (heta : 0 ≤ eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    mu < 4 := by
  have hfactor : 0 < 1 - routeTGapMomentNu := by
    linarith [routeTGapMomentNu_lt_half]
  by_contra h
  have hmu : 4 ≤ mu := le_of_not_gt h
  have hmul : 4 * (1 - routeTGapMomentNu) ≤
      mu * (1 - routeTGapMomentNu) :=
    mul_le_mul_of_nonneg_right hmu hfactor.le
  linarith [routeT_physicalSlice_budget_fails_at_four]

end RHTower.Sieve
