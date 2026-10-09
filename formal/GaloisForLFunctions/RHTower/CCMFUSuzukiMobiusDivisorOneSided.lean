import GaloisForLFunctions.RHTower.CCMUnitRieszSuzukiRealAperture
import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorAbelProducer

/-!
# One-sided upper barrier for the literal Mobius divisor Abel receiver

The signed cell estimate retains the nonnegative attenuation `N/X`:
`|F(log X) - (N/X) F(log N)| <= log 4 + 5` on `N <= X <= N+1`.
An upper bound at integer logarithms therefore propagates to the real resolvent.
Below `log 2`, the exact finite prime sum vanishes and the resolvent is nonpositive.

The real-aperture Suzuki Green identity and positive inverse then prove RH equivalent
to eventual upper boundedness of `mobiusDivisorSquareRootAbelMoment M / M`.
All polar, lattice, and Euler-constant boundary terms are retained. The finite prefix
is absorbed explicitly. The equivalence is unconditional; its arithmetic upper bound
is not established by this module.
-/

open Set MeasureTheory Topology
noncomputable section

namespace RHTower.UnitRieszOneSided

open GaloisForLFunctions.RHTower

private def halfWeightError (y : ℝ) : ℝ :=
  (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))

private theorem intervalIntegrable_halfWeightError {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable halfWeightError volume a b := by
  have hpsi : IntervalIntegrable (fun y : ℝ => Chebyshev.psi y - y) volume a b :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable (μ := volume) a b)
  have hpow : ContinuousOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Set.uIcc a b) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro y hy
    left
    rw [Set.uIcc_of_le hab] at hy
    exact ne_of_gt (zero_lt_one.trans_le (ha.trans hy.1))
  exact hpsi.mul_continuousOn hpow

private theorem abs_halfWeightError_le {X y : ℝ} (hy : 1 ≤ y) (hyX : y ≤ X) :
    |halfWeightError y| ≤ (Real.log 4 + 5) * X := by
  have hpsi0 := Chebyshev.psi_nonneg y
  have hpsi := Chebyshev.psi_le_const_mul_self (show 0 ≤ y by linarith)
  have hC : 0 ≤ Real.log 4 + 5 := by positivity
  have herr : |Chebyshev.psi y - y| ≤ (Real.log 4 + 5) * y := by
    calc
      |Chebyshev.psi y - y| ≤ |Chebyshev.psi y| + |y| := abs_sub _ _
      _ = Chebyshev.psi y + y := by rw [abs_of_nonneg hpsi0, abs_of_nonneg (by linarith)]
      _ ≤ (Real.log 4 + 4) * y + y := by gcongr
      _ = (Real.log 4 + 5) * y := by ring
  have hpow0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hpow1 : y ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  rw [halfWeightError, abs_mul, abs_of_nonneg hpow0]
  calc
    |Chebyshev.psi y - y| * y ^ (-(1 / 2 : ℝ)) ≤ ((Real.log 4 + 5) * y) * 1 := by gcongr
    _ = (Real.log 4 + 5) * y := by ring
    _ ≤ (Real.log 4 + 5) * X := by gcongr

theorem abs_resolvent_log_sub_nat_mul_le {N : ℕ} {X : ℝ} (hN : 2 ≤ N)
    (hNX : (N : ℝ) ≤ X) (hXN : X ≤ (N : ℝ) + 1) :
    |criticalMellinChebyshevResolventSource (Real.log X) -
      ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N)| ≤ Real.log 4 + 5 := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hXpos : 0 < X := hNpos.trans_le hNX
  have hlogN := Real.log_nonneg hNreal
  have hlogX := Real.log_nonneg (hNreal.trans hNX)
  have hrayN := unitRieszChebyshevRayIntegral_eq_fullResolvent hlogN
  have hrayX := unitRieszChebyshevRayIntegral_eq_fullResolvent hlogX
  rw [Real.exp_log hNpos] at hrayN
  rw [Real.exp_log hXpos] at hrayX
  have hprimeN := unitRieszChebyshevRayIntegral_eq_primeIntegral (Real.log N)
  have hprimeX := unitRieszChebyshevRayIntegral_eq_primeIntegral (Real.log X)
  rw [Real.exp_log hNpos] at hprimeN
  rw [Real.exp_log hXpos] at hprimeX
  have hintN := intervalIntegrable_halfWeightError (a := 1) le_rfl hNreal
  have hintTail := intervalIntegrable_halfWeightError hNreal hNX
  have hsplit : unitRieszChebyshevRayIntegral (Real.log X) =
      unitRieszChebyshevRayIntegral (Real.log N) + ∫ y in (N : ℝ)..X, halfWeightError y := by
    rw [hprimeX, hprimeN]
    change (∫ y in (1 : ℝ)..X, halfWeightError y) = _
    exact (intervalIntegral.integral_add_adjacent_intervals hintN hintTail).symm
  let T : ℝ := ∫ y in (N : ℝ)..X, halfWeightError y
  have hT : |T| ≤ (Real.log 4 + 5) * X := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := halfWeightError) (a := (N : ℝ)) (b := X) (C := (Real.log 4 + 5) * X)
      (fun y hy => by
        have hy' : y ∈ Set.uIcc (N : ℝ) X := Set.uIoc_subset_uIcc hy
        rw [Set.uIcc_of_le hNX] at hy'
        rw [Real.norm_eq_abs]
        exact abs_halfWeightError_le (hNreal.trans hy'.1) hy'.2)
    rw [Real.norm_eq_abs] at hraw
    change |T| ≤ _
    calc
      |T| ≤ (Real.log 4 + 5) * X * |X - (N : ℝ)| := hraw
      _ ≤ (Real.log 4 + 5) * X * 1 := by
        gcongr
        rw [abs_of_nonneg (sub_nonneg.mpr hNX)]
        linarith
      _ = (Real.log 4 + 5) * X := by ring
  have hEq : X * criticalMellinChebyshevResolventSource (Real.log X) =
      (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) + T := by
    change _ = _ + (∫ y in (N : ℝ)..X, halfWeightError y)
    linarith [hrayN, hrayX, hsplit]
  have hformula : criticalMellinChebyshevResolventSource (Real.log X) =
      ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) + T / X := by
    calc
      _ = ((N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) + T) / X := by
        apply (eq_div_iff hXpos.ne').2
        nlinarith [hEq]
      _ = _ := by ring
  have hdiff : criticalMellinChebyshevResolventSource (Real.log X) -
      ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) = T / X := by
    rw [hformula]
    ring
  rw [hdiff, abs_div, abs_of_pos hXpos]
  exact (div_le_iff₀ hXpos).2 hT

theorem resolvent_le_of_logNat_upper {B t : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ N : ℕ, 2 ≤ N → criticalMellinChebyshevResolventSource (Real.log N) ≤ B)
    (ht : Real.log 2 ≤ t) :
    criticalMellinChebyshevResolventSource t ≤ B + (Real.log 4 + 5) := by
  let X := Real.exp t
  let N : ℕ := ⌊X⌋₊
  have hX2 : (2 : ℝ) ≤ X := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
    exact Real.exp_le_exp.mpr ht
  have hXpos : 0 < X := Real.exp_pos t
  have hN : 2 ≤ N := Nat.le_floor hX2
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
  have hcell := (abs_le.mp (abs_resolvent_log_sub_nat_mul_le hN hNX hXN)).2
  have hlogX : Real.log X = t := Real.log_exp t
  rw [hlogX] at hcell
  have hr0 : 0 ≤ (N : ℝ) / X := by positivity
  have hr1 : (N : ℝ) / X ≤ 1 := (div_le_one hXpos).2 hNX
  have hsample := mul_le_mul_of_nonneg_left (hB N hN) hr0
  have hscale := mul_le_mul_of_nonneg_right hr1 hB0
  linarith

theorem resolvent_global_le_of_logNat_upper {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ N : ℕ, 2 ≤ N → criticalMellinChebyshevResolventSource (Real.log N) ≤ B)
    {t : ℝ} :
    criticalMellinChebyshevResolventSource t ≤ B + 2 * (Real.log 4 + 5) := by
  have hC : 0 ≤ Real.log 4 + 5 := by positivity
  by_cases hlog : Real.log 2 ≤ t
  · have h := resolvent_le_of_logNat_upper hB0 hB hlog
    linarith
  · have hexp : Real.exp t < 2 := by
      calc
        _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (lt_of_not_ge hlog)
        _ = 2 := Real.exp_log (by norm_num)
    have hsum : (∑ k ∈ Finset.Icc 0 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / Real.exp t))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkR : (k : ℝ) ≤ Real.exp t :=
        (by exact_mod_cast (Finset.mem_Icc.mp hk).2 : (k : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ)).trans
          (Nat.floor_le (Real.exp_pos t).le)
      have hk2 : k < 2 := by exact_mod_cast hkR.trans_lt hexp
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp
    have hsource := UnitRieszRealAperture.resolvent_log_eq_prime_sum (Real.exp_pos t)
    rw [Real.log_exp, hsum, mul_zero, zero_sub] at hsource
    rw [hsource]
    nlinarith [Real.sqrt_nonneg (Real.exp t)]

end RHTower.UnitRieszOneSided

namespace RHTower

open UnitRieszOneSided GaloisForLFunctions.RHTower

theorem riemannHypothesis_iff_criticalResolvent_logNat_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      criticalMellinChebyshevResolventSource (Real.log N) ≤ B := by
  constructor
  · intro hRH
    obtain ⟨B, _, hB⟩ := exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis hRH
    exact ⟨B, fun N hN => (le_abs_self _).trans (hB N hN)⟩
  · rintro ⟨B, hB⟩
    apply riemannHypothesis_of_criticalResolvent_boundedAbove
    exact fun t _ => resolvent_global_le_of_logNat_upper (t := t) (le_max_left 0 B)
      (fun N hN => (hB N hN).trans (le_max_right 0 B))

theorem resolvent_log_nat_le_mobiusDivisorSquareRootAbel {M : ℕ} (hM : 2 ≤ M) :
    criticalMellinChebyshevResolventSource (Real.log M) ≤
      2 * (mobiusDivisorSquareRootAbelMoment M / M) +
        2 * (|2 * Real.eulerMascheroniConstant| + 1) := by
  have hM1 : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hsqrtSq := Real.sq_sqrt hMR.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt M := by nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hsqrtLe : Real.sqrt M ≤ (M : ℝ) := by nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hgamma : |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      |2 * Real.eulerMascheroniConstant| := by
    rw [abs_div, abs_mul, abs_of_pos hMR, abs_of_nonneg (sub_nonneg.mpr hsqrtOne)]
    apply (div_le_iff₀ hMR).2
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hlattice : |coherentSquareRootPolarLatticeDefect M / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hMR]
    exact (div_le_one hMR).2 ((abs_coherentSquareRootPolarLatticeDefect_le hM1).trans hsqrtLe)
  have hsource := congrArg (fun x : ℝ => x / (M : ℝ))
    (mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary hM1)
  rw [add_div] at hsource
  have hcharge := coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM
  rw [add_div] at hcharge
  have hres := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM
  linarith [(abs_le.mp hgamma).1, (abs_le.mp hlattice).2]

theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorSquareRootAbelMoment M / M ≤ B := by
  constructor
  · intro hRH
    obtain ⟨B, _, hB⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded.mp hRH
    exact ⟨B, fun M hM => (le_abs_self _).trans (hB M hM)⟩
  · rintro ⟨B, hB⟩
    apply riemannHypothesis_iff_criticalResolvent_logNat_boundedAbove.mpr
    refine ⟨2 * B + 2 * (|2 * Real.eulerMascheroniConstant| + 1), fun M hM => ?_⟩
    linarith [resolvent_log_nat_le_mobiusDivisorSquareRootAbel hM, hB M hM]

theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_eventually_boundedAbove :
    RiemannHypothesis ↔ ∃ (B : ℝ) (M₀ : ℕ), ∀ M : ℕ, max 2 M₀ ≤ M →
      mobiusDivisorSquareRootAbelMoment M / M ≤ B := by
  constructor
  · intro hRH
    obtain ⟨B, hB⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove.mp hRH
    exact ⟨B, 2, fun M hM => hB M (by simpa using hM)⟩
  · rintro ⟨B, M₀, hB⟩
    let S := ∑ k ∈ Finset.range M₀, |mobiusDivisorSquareRootAbelMoment k / k|
    have hS : 0 ≤ S := by positivity
    apply riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove.mpr
    refine ⟨|B| + S, fun M hM => ?_⟩
    by_cases hM₀ : M₀ ≤ M
    · have h := hB M (max_le hM hM₀)
      linarith [le_abs_self B]
    · have hMS : |mobiusDivisorSquareRootAbelMoment M / M| ≤ S := by
        exact Finset.single_le_sum
          (fun k _ => abs_nonneg (mobiusDivisorSquareRootAbelMoment k / (k : ℝ)))
          (Finset.mem_range.mpr (lt_of_not_ge hM₀))
      linarith [le_abs_self (mobiusDivisorSquareRootAbelMoment M / M), abs_nonneg B]

end RHTower
