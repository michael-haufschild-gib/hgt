import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauColdBoundaryNoGo
import GaloisForLFunctions.RHTower.PrimePowerCompletionBudget

/-!
# Prime/Gamma Stokes-wall Xi tau explicit cold no-go

The source-defined prime-log Gibbs wall has an explicit cold threshold.  For every aperture
`d ≥ 1`, prime two carries more than `12/25` of normalized mass.  Its diagonal contribution
forces cubic Stokes coherence above `9/40`, hence the scale-free Fredholm logarithmic two-jet
above `9/80`.  Xi's projective two-jet lies strictly below that same rational ceiling, so no
complex scalar rescaling of irregular time can identify the two logarithmic germs on `[1,∞)`.

The proof is unconditional and source-native.  Its only analytic tail input is the explicit
integer bound for `Σ_{n>11} log(n)/n²`; no RH assumption, target zero, numerical computation,
or global coherence-monotonicity claim enters.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower

noncomputable section

local instance routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauExplicitColdNoGoLocalInst1 : MeasurableSpace Nat.Primes := ⊤

private def explicitColdPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

private def explicitColdPrimeThree : Nat.Primes := ⟨3, by norm_num⟩

private def explicitColdPrimeFive : Nat.Primes := ⟨5, by norm_num⟩

private def explicitColdPrimeSeven : Nat.Primes := ⟨7, by norm_num⟩

private def explicitColdPrimeEleven : Nat.Primes := ⟨11, by norm_num⟩

private def natTailEquiv (N : ℕ) : ℕ ≃ Set.Ici N where
  toFun i := ⟨N + i, by
    show N ≤ N + i
    omega⟩
  invFun n := n - N
  left_inv i := by simp
  right_inv n := by
    apply Subtype.ext
    exact Nat.add_sub_of_le (show N ≤ n from n.property)

private theorem tsum_nat_tail_eq (f : ℕ → ℝ) (N : ℕ) :
    (∑' n : Set.Ici N, f n) = ∑' i : ℕ, f (N + i) := by
  simpa [natTailEquiv] using ((natTailEquiv N).tsum_eq
    (fun n : Set.Ici N => f n)).symm

private theorem log_seven_lt_two : Real.log (7 : ℝ) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 6)
  norm_num [Finset.sum_range_succ]

private theorem log_eleven_lt_five_div_two : Real.log (11 : ℝ) < 5 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (5 : ℝ) / 2) 6)
  norm_num [Finset.sum_range_succ]

private theorem prime_log_cube_tail_le :
    (∑' p : Nat.Primes,
      if 11 < (p : ℕ) then Real.log (p : ℝ) / (p : ℝ) ^ 3 else 0) ≤
        (Real.log 11 + 1) / 143 := by
  let f : ℕ → ℝ := fun n => Real.log (n : ℝ) / (n : ℝ) ^ 2
  let H : ℕ → ℝ := (Set.Ici 12).indicator f
  have hf : Summable f := by
    simpa [f] using GaloisForLFunctions.HTGeometry.summable_logLin_div_sq
  have hH : Summable H := by
    simpa [H] using hf.indicator (Set.Ici 12)
  have hHnonneg : ∀ n, 0 ≤ H n := by
    intro n
    by_cases hn : 12 ≤ n
    · rw [show H n = f n by simp [H, hn]]
      dsimp [f]
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (by positivity)
    · rw [show H n = 0 by simp [H, hn]]
  have hHsum : (∑' n : ℕ, H n) ≤ (Real.log 11 + 1) / 11 := by
    have hexp : Real.exp 1 ≤ (11 : ℝ) := by
      nlinarith [Real.exp_one_lt_d9]
    have htail := GaloisForLFunctions.HTGeometry.tsum_logLin_div_sq_le
      (N := (11 : ℝ)) hexp
    have heq : (∑' n : ℕ, H n) =
        ∑' i : ℕ,
          Real.log ((11 : ℝ) + ((i : ℝ) + 1)) /
            ((11 : ℝ) + ((i : ℝ) + 1)) ^ 2 := by
      calc
        (∑' n : ℕ, H n) = ∑' n : Set.Ici 12, f n := by
          exact (tsum_subtype (Set.Ici 12) f).symm
        _ = ∑' i : ℕ, f (12 + i) := tsum_nat_tail_eq f 12
        _ = ∑' i : ℕ,
            Real.log ((11 : ℝ) + ((i : ℝ) + 1)) /
              ((11 : ℝ) + ((i : ℝ) + 1)) ^ 2 := by
          apply tsum_congr
          intro i
          dsimp [f]
          congr 1 <;> push_cast <;> ring
    rw [heq]
    exact htail
  have hrepr :
      (∑' p : Nat.Primes,
        if 11 < (p : ℕ) then Real.log (p : ℝ) / (p : ℝ) ^ 3 else 0) =
      ∑' n : ℕ,
        if Nat.Prime n ∧ 11 < n then Real.log (n : ℝ) / (n : ℝ) ^ 3 else 0 := by
    let g : ℕ → ℝ := fun n =>
      if 11 < n then Real.log (n : ℝ) / (n : ℝ) ^ 3 else 0
    change (∑' p : {p : ℕ // Nat.Prime p}, g p) = _
    calc
      (∑' p : {p : ℕ // Nat.Prime p}, g p) =
          ∑' n : ℕ, ({n : ℕ | Nat.Prime n}).indicator g n :=
        tsum_subtype {n : ℕ | Nat.Prime n} g
      _ = ∑' n : ℕ,
          if Nat.Prime n ∧ 11 < n then Real.log (n : ℝ) / (n : ℝ) ^ 3 else 0 := by
        apply tsum_congr
        intro n
        by_cases hp : Nat.Prime n <;> simp [g, hp]
  rw [hrepr]
  apply Real.tsum_le_of_sum_range_le
  · intro n
    split_ifs with hn
    · exact div_nonneg
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (by positivity)
    · exact le_rfl
  · intro N
    calc
      ∑ n ∈ Finset.range N,
          (if Nat.Prime n ∧ 11 < n then Real.log (n : ℝ) / (n : ℝ) ^ 3 else 0) ≤
          ∑ n ∈ Finset.range N, (1 / 13 : ℝ) * H n := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hp : Nat.Prime n ∧ 11 < n
        · rw [if_pos hp]
          have hn12 : n ≠ 12 := by
            intro h
            subst n
            norm_num at hp
          have hn13 : 13 ≤ n := by omega
          have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 13) hn13)
          have hlog : 0 ≤ Real.log (n : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
          have hrecip : (1 / (n : ℝ)) ≤ (1 / 13 : ℝ) := by
            exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn13)
          rw [show H n = f n by simp [H, (by omega : 12 ≤ n)]]
          dsimp [f]
          calc
            Real.log (n : ℝ) / (n : ℝ) ^ 3 =
                (1 / (n : ℝ)) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
              field_simp
            _ ≤ (1 / 13 : ℝ) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hrecip (div_nonneg hlog (by positivity))
        · rw [if_neg hp]
          exact mul_nonneg (by norm_num) (hHnonneg n)
      _ = (1 / 13 : ℝ) * ∑ n ∈ Finset.range N, H n := by
        rw [Finset.mul_sum]
      _ ≤ (1 / 13 : ℝ) * ∑' n : ℕ, H n := by
        gcongr
        exact hH.sum_le_tsum _ (fun n _ => hHnonneg n)
      _ ≤ (1 / 13 : ℝ) * ((Real.log 11 + 1) / 11) := by
        gcongr
      _ = (Real.log 11 + 1) / 143 := by ring

private theorem xiMassPrimeSquareEulerWeight_one_eq_log_div_cube
    (p : Nat.Primes) :
    xiMassPrimeSquareEulerWeight 1 p = Real.log (p : ℝ) / (p : ℝ) ^ 3 := by
  rw [xiMassPrimeSquareEulerWeight_eq]
  norm_num
  rw [div_eq_mul_inv]
  congr 1

/-- Explicit source-only bound for prime-log cubic mass at cold aperture one. -/
theorem tsum_primeLog_div_cube_lt_twentyFive_mul_log_two_div_ninetySix :
    (∑' p : Nat.Primes, Real.log (p : ℝ) / (p : ℝ) ^ 3) <
      25 * Real.log 2 / 96 := by
  let f : Nat.Primes → ℝ := fun p => Real.log (p : ℝ) / (p : ℝ) ^ 3
  let h2 : Nat.Primes → ℝ := fun p => if (p : ℕ) = 2 then f p else 0
  let h3 : Nat.Primes → ℝ := fun p => if (p : ℕ) = 3 then f p else 0
  let h5 : Nat.Primes → ℝ := fun p => if (p : ℕ) = 5 then f p else 0
  let h7 : Nat.Primes → ℝ := fun p => if (p : ℕ) = 7 then f p else 0
  let h11 : Nat.Primes → ℝ := fun p => if (p : ℕ) = 11 then f p else 0
  let tail : Nat.Primes → ℝ := fun p =>
    if 11 < (p : ℕ) then f p else 0
  have hf : Summable f := by
    apply (summable_xiMassPrimeSquareEulerWeight (by norm_num : (0 : ℝ) < 1)).congr
    intro p
    exact xiMassPrimeSquareEulerWeight_one_eq_log_div_cube p
  have hs2 : Summable h2 := by
    apply (hasSum_ite_eq explicitColdPrimeTwo (f explicitColdPrimeTwo)).summable.congr
    intro p
    by_cases hpeq : p = explicitColdPrimeTwo
    · subst p
      norm_num [h2, explicitColdPrimeTwo]
    · have hp : (p : ℕ) ≠ 2 := fun h => hpeq (Subtype.ext h)
      simp [h2, hp, hpeq]
  have hs3 : Summable h3 := by
    apply (hasSum_ite_eq explicitColdPrimeThree (f explicitColdPrimeThree)).summable.congr
    intro p
    by_cases hpeq : p = explicitColdPrimeThree
    · subst p
      norm_num [h3, explicitColdPrimeThree]
    · have hp : (p : ℕ) ≠ 3 := fun h => hpeq (Subtype.ext h)
      simp [h3, hp, hpeq]
  have hs5 : Summable h5 := by
    apply (hasSum_ite_eq explicitColdPrimeFive (f explicitColdPrimeFive)).summable.congr
    intro p
    by_cases hpeq : p = explicitColdPrimeFive
    · subst p
      norm_num [h5, explicitColdPrimeFive]
    · have hp : (p : ℕ) ≠ 5 := fun h => hpeq (Subtype.ext h)
      simp [h5, hp, hpeq]
  have hs7 : Summable h7 := by
    apply (hasSum_ite_eq explicitColdPrimeSeven (f explicitColdPrimeSeven)).summable.congr
    intro p
    by_cases hpeq : p = explicitColdPrimeSeven
    · subst p
      norm_num [h7, explicitColdPrimeSeven]
    · have hp : (p : ℕ) ≠ 7 := fun h => hpeq (Subtype.ext h)
      simp [h7, hp, hpeq]
  have hs11 : Summable h11 := by
    apply (hasSum_ite_eq explicitColdPrimeEleven (f explicitColdPrimeEleven)).summable.congr
    intro p
    by_cases hpeq : p = explicitColdPrimeEleven
    · subst p
      norm_num [h11, explicitColdPrimeEleven]
    · have hp : (p : ℕ) ≠ 11 := fun h => hpeq (Subtype.ext h)
      simp [h11, hp, hpeq]
  have hstail : Summable tail := by
    have h := hf.indicator {p : Nat.Primes | 11 < (p : ℕ)}
    apply h.congr
    intro p
    simp [tail, Set.indicator_apply]
  have hdecomp : ∀ p : Nat.Primes,
      f p = h2 p + (h3 p + (h5 p + (h7 p + (h11 p + tail p)))) := by
    intro p
    by_cases hgt : 11 < (p : ℕ)
    · have hn2 : (p : ℕ) ≠ 2 := by omega
      have hn3 : (p : ℕ) ≠ 3 := by omega
      have hn5 : (p : ℕ) ≠ 5 := by omega
      have hn7 : (p : ℕ) ≠ 7 := by omega
      have hn11 : (p : ℕ) ≠ 11 := by omega
      simp [h2, h3, h5, h7, h11, tail, hgt, hn2, hn3, hn5, hn7, hn11]
    · have hpprime := p.property
      have hle : (p : ℕ) ≤ 11 := by omega
      interval_cases hpval : (p : ℕ)
      all_goals norm_num at hpprime
      all_goals simp [h2, h3, h5, h7, h11, tail, hpval]
  have hsum : (∑' p : Nat.Primes, f p) =
      f explicitColdPrimeTwo +
        (f explicitColdPrimeThree +
          (f explicitColdPrimeFive +
            (f explicitColdPrimeSeven +
              (f explicitColdPrimeEleven + ∑' p : Nat.Primes, tail p)))) := by
    have ht2 : (∑' p : Nat.Primes, h2 p) = f explicitColdPrimeTwo := by
      rw [tsum_eq_single explicitColdPrimeTwo]
      · simp [h2, explicitColdPrimeTwo]
      · intro p hp
        have hn : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
        simp [h2, hn]
    have ht3 : (∑' p : Nat.Primes, h3 p) = f explicitColdPrimeThree := by
      rw [tsum_eq_single explicitColdPrimeThree]
      · simp [h3, explicitColdPrimeThree]
      · intro p hp
        have hn : (p : ℕ) ≠ 3 := fun h => hp (Subtype.ext h)
        simp [h3, hn]
    have ht5 : (∑' p : Nat.Primes, h5 p) = f explicitColdPrimeFive := by
      rw [tsum_eq_single explicitColdPrimeFive]
      · simp [h5, explicitColdPrimeFive]
      · intro p hp
        have hn : (p : ℕ) ≠ 5 := fun h => hp (Subtype.ext h)
        simp [h5, hn]
    have ht7 : (∑' p : Nat.Primes, h7 p) = f explicitColdPrimeSeven := by
      rw [tsum_eq_single explicitColdPrimeSeven]
      · simp [h7, explicitColdPrimeSeven]
      · intro p hp
        have hn : (p : ℕ) ≠ 7 := fun h => hp (Subtype.ext h)
        simp [h7, hn]
    have ht11 : (∑' p : Nat.Primes, h11 p) = f explicitColdPrimeEleven := by
      rw [tsum_eq_single explicitColdPrimeEleven]
      · simp [h11, explicitColdPrimeEleven]
      · intro p hp
        have hn : (p : ℕ) ≠ 11 := fun h => hp (Subtype.ext h)
        simp [h11, hn]
    calc
      (∑' p : Nat.Primes, f p) =
          ∑' p : Nat.Primes,
            (h2 p + (h3 p + (h5 p + (h7 p + (h11 p + tail p))))) :=
        tsum_congr hdecomp
      _ = (∑' p, h2 p) +
          ((∑' p, h3 p) +
            ((∑' p, h5 p) +
              ((∑' p, h7 p) + ((∑' p, h11 p) + ∑' p, tail p)))) := by
        rw [hs2.tsum_add (hs3.add (hs5.add (hs7.add (hs11.add hstail)))),
          hs3.tsum_add (hs5.add (hs7.add (hs11.add hstail))),
          hs5.tsum_add (hs7.add (hs11.add hstail)),
          hs7.tsum_add (hs11.add hstail), hs11.tsum_add hstail]
      _ = _ := by
        rw [ht2, ht3, ht5, ht7, ht11]
  have htail : (∑' p : Nat.Primes, tail p) ≤ (Real.log 11 + 1) / 143 := by
    simpa [tail, f] using prime_log_cube_tail_le
  have hlog3 : Real.log (3 : ℝ) < 6 / 5 := by
    nlinarith [Real.log_three_lt_d9]
  have hlog5 : Real.log (5 : ℝ) < 17 / 10 := by
    nlinarith [Real.log_five_lt_d9]
  have hrest :
      f explicitColdPrimeThree +
          (f explicitColdPrimeFive +
            (f explicitColdPrimeSeven +
              (f explicitColdPrimeEleven + ∑' p : Nat.Primes, tail p))) <
        (6 / 5 : ℝ) / 27 + (17 / 10 : ℝ) / 125 + (2 : ℝ) / 343 +
          (5 / 2 : ℝ) / 1331 + (7 / 2 : ℝ) / 143 := by
    dsimp [f, explicitColdPrimeThree, explicitColdPrimeFive,
      explicitColdPrimeSeven, explicitColdPrimeEleven]
    norm_num only [Nat.cast_ofNat]
    have htail' : (∑' p : Nat.Primes, tail p) < (7 / 2 : ℝ) / 143 := by
      nlinarith [htail, log_eleven_lt_five_div_two]
    linarith [hlog3, hlog5, log_seven_lt_two, log_eleven_lt_five_div_two]
  have hrat :
      (6 / 5 : ℝ) / 27 + (17 / 10 : ℝ) / 125 + (2 : ℝ) / 343 +
          (5 / 2 : ℝ) / 1331 + (7 / 2 : ℝ) / 143 < 13 / 144 := by
    norm_num
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num) Real.log_two_gt_d9
  rw [show (∑' p : Nat.Primes, Real.log (p : ℝ) / (p : ℝ) ^ 3) =
      ∑' p : Nat.Primes, f p by rfl, hsum]
  dsimp [f, explicitColdPrimeTwo]
  norm_num only [Nat.cast_ofNat]
  nlinarith

private def explicitColdCoefficient (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) * (p : ℝ) ^ (-1 : ℝ)

private def explicitColdEnergy (p : Nat.Primes) : ℝ :=
  2 * Real.log (p : ℝ)

private def explicitColdTerm (d : ℝ) (p : Nat.Primes) : ℝ :=
  lowTemperatureMomentTerm explicitColdCoefficient explicitColdEnergy
    (2 * Real.log 2) 0 d p

private def explicitColdPartition (d : ℝ) : ℝ :=
  ∑' p : Nat.Primes, explicitColdTerm d p

private theorem explicitColdEnergy_bottom (p : Nat.Primes) :
    2 * Real.log 2 ≤ explicitColdEnergy p := by
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (by simpa only [mem_Ioi] using
        (by exact_mod_cast p.property.pos : (0 : ℝ) < (p : ℝ)))
      (by exact_mod_cast p.property.two_le)
  dsimp [explicitColdEnergy]
  linarith

private theorem explicitColdTerm_eq_scaled_weight (d : ℝ) (p : Nat.Primes) :
    explicitColdTerm d p =
      Real.exp (2 * d * Real.log 2) * xiMassPrimeSquareEulerWeight d p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [xiMassPrimeSquareEulerWeight_eq, Real.rpow_def_of_pos hp]
  dsimp [explicitColdTerm, lowTemperatureMomentTerm,
    explicitColdCoefficient, explicitColdEnergy]
  rw [Real.rpow_def_of_pos hp]
  simp only [pow_zero, mul_one]
  calc
    Real.log (p : ℝ) * Real.exp (Real.log (p : ℝ) * -1) *
          Real.exp (-d * (2 * Real.log (p : ℝ) - 2 * Real.log 2)) =
        Real.log (p : ℝ) * Real.exp
          (Real.log (p : ℝ) * -1 +
            -d * (2 * Real.log (p : ℝ) - 2 * Real.log 2)) := by
      rw [Real.exp_add]
      ring
    _ = Real.log (p : ℝ) * Real.exp
          (2 * d * Real.log 2 + Real.log (p : ℝ) * -(1 + 2 * d)) := by
      congr 2
      ring
    _ = Real.exp (2 * d * Real.log 2) *
          (Real.log (p : ℝ) * Real.exp (Real.log (p : ℝ) * -(1 + 2 * d))) := by
      rw [Real.exp_add]
      ring

private theorem explicitColdTerm_two (d : ℝ) :
    explicitColdTerm d explicitColdPrimeTwo = Real.log 2 / 2 := by
  dsimp [explicitColdTerm, lowTemperatureMomentTerm,
    explicitColdCoefficient, explicitColdEnergy, explicitColdPrimeTwo]
  rw [Real.rpow_neg_one]
  norm_num
  ring

private theorem explicitColdTerm_nonneg (d : ℝ) (p : Nat.Primes) :
    0 ≤ explicitColdTerm d p := by
  dsimp [explicitColdTerm, lowTemperatureMomentTerm, explicitColdCoefficient]
  positivity

private theorem explicitColdTerm_le_at_one
    {d : ℝ} (hd : 1 ≤ d) (p : Nat.Primes) :
    explicitColdTerm d p ≤ explicitColdTerm 1 p := by
  have hgap : 0 ≤ explicitColdEnergy p - 2 * Real.log 2 :=
    sub_nonneg.mpr (explicitColdEnergy_bottom p)
  have hexp :
      Real.exp (-d * (explicitColdEnergy p - 2 * Real.log 2)) ≤
        Real.exp (-(explicitColdEnergy p - 2 * Real.log 2)) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hcoeff : 0 ≤ explicitColdCoefficient p := by
    dsimp [explicitColdCoefficient]
    exact mul_nonneg
      (Real.log_nonneg (by exact_mod_cast p.property.one_lt.le))
      (Real.rpow_nonneg (by positivity) _)
  dsimp only [explicitColdTerm, lowTemperatureMomentTerm]
  simp only [pow_zero, mul_one]
  gcongr

private theorem summable_explicitColdTerm {d : ℝ} (hd : 0 < d) :
    Summable (explicitColdTerm d) := by
  have hs := (summable_xiMassPrimeSquareEulerWeight hd).mul_left
    (Real.exp (2 * d * Real.log 2))
  apply hs.congr
  intro p
  exact (explicitColdTerm_eq_scaled_weight d p).symm

private theorem explicitColdTerm_one_eq_four_mul_log_div_cube (p : Nat.Primes) :
    explicitColdTerm 1 p = 4 * (Real.log (p : ℝ) / (p : ℝ) ^ 3) := by
  rw [explicitColdTerm_eq_scaled_weight,
    xiMassPrimeSquareEulerWeight_one_eq_log_div_cube]
  have hlog : 2 * (1 : ℝ) * Real.log 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

private theorem explicitColdPartition_lt_twentyFive_div_twelve_mul_two
    {d : ℝ} (hd : 1 ≤ d) :
    explicitColdPartition d < (25 / 12 : ℝ) * (Real.log 2 / 2) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hsumle : explicitColdPartition d ≤ explicitColdPartition 1 := by
    exact Summable.tsum_le_tsum (explicitColdTerm_le_at_one hd)
      (summable_explicitColdTerm hdpos) (summable_explicitColdTerm (by norm_num))
  have hone : explicitColdPartition 1 =
      4 * ∑' p : Nat.Primes, Real.log (p : ℝ) / (p : ℝ) ^ 3 := by
    have hf : Summable (fun p : Nat.Primes =>
        Real.log (p : ℝ) / (p : ℝ) ^ 3) := by
      apply (summable_xiMassPrimeSquareEulerWeight (by norm_num : (0 : ℝ) < 1)).congr
      intro p
      exact xiMassPrimeSquareEulerWeight_one_eq_log_div_cube p
    rw [explicitColdPartition]
    calc
      (∑' p : Nat.Primes, explicitColdTerm 1 p) =
          ∑' p : Nat.Primes, 4 * (Real.log (p : ℝ) / (p : ℝ) ^ 3) := by
        apply tsum_congr
        intro p
        exact explicitColdTerm_one_eq_four_mul_log_div_cube p
      _ = 4 * ∑' p : Nat.Primes, Real.log (p : ℝ) / (p : ℝ) ^ 3 :=
        hf.tsum_mul_left 4
  rw [hone] at hsumle
  have hprime := tsum_primeLog_div_cube_lt_twentyFive_mul_log_two_div_ninetySix
  nlinarith

private theorem wallNormalizedWeight_eq_weight_div_tsum
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p =
      xiMassPrimeSquareEulerWeight d p /
        ∑' q : Nat.Primes, xiMassPrimeSquareEulerWeight d q := by
  have hcurrent : gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d =
      (8 * d) * ∑' q : Nat.Primes, xiMassPrimeSquareEulerWeight d q := by
    rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent,
      ← (summable_xiMassPrimeSquareEulerWeight hd).tsum_mul_left]
    apply tsum_congr
    intro q
    simp [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, abs_of_pos hd]
  rw [routePPrimitiveGammaJuliaStokesWallNormalizedWeight,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd p,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, abs_of_pos hd, hcurrent]
  field_simp [hd.ne']

private theorem explicitColdPartition_eq_scaled_tsum {d : ℝ} (hd : 0 < d) :
    explicitColdPartition d = Real.exp (2 * d * Real.log 2) *
      ∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight d p := by
  rw [explicitColdPartition,
    ← (summable_xiMassPrimeSquareEulerWeight hd).tsum_mul_left]
  exact tsum_congr (explicitColdTerm_eq_scaled_weight d)

private theorem wallNormalizedWeight_two_eq_explicitColdRatio
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d explicitColdPrimeTwo =
      (Real.log 2 / 2) / explicitColdPartition d := by
  rw [wallNormalizedWeight_eq_weight_div_tsum hd,
    ← explicitColdTerm_two d, explicitColdTerm_eq_scaled_weight,
    explicitColdPartition_eq_scaled_tsum hd]
  field_simp [Real.exp_ne_zero]

/-- At every aperture `d ≥ 1`, prime two carries more than `12/25` of wall mass. -/
theorem twelve_div_twentyFive_lt_wallNormalizedWeight_two_of_one_le
    {d : ℝ} (hd : 1 ≤ d) :
    (12 / 25 : ℝ) <
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d explicitColdPrimeTwo := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hsum := summable_explicitColdTerm hdpos
  have hpartpos : 0 < explicitColdPartition d := by
    have hsingle := hsum.sum_le_tsum {explicitColdPrimeTwo}
      (fun p hp => explicitColdTerm_nonneg d p)
    have hsingle' : explicitColdTerm d explicitColdPrimeTwo ≤ explicitColdPartition d := by
      simpa [explicitColdPartition] using hsingle
    have htwo : 0 < explicitColdTerm d explicitColdPrimeTwo := by
      rw [explicitColdTerm_two]
      positivity
    exact lt_of_lt_of_le htwo hsingle'
  rw [wallNormalizedWeight_two_eq_explicitColdRatio hdpos]
  have hbound := explicitColdPartition_lt_twentyFive_div_twelve_mul_two hd
  apply (lt_div_iff₀ hpartpos).2
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- Explicit cold-half-ray floor for cubic Stokes coherence. -/
theorem nine_div_forty_lt_primeGammaWallCoherenceExpectation_of_one_le
    {d : ℝ} (hd : 1 ≤ d) :
    (9 / 40 : ℝ) <
      routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdiag :
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d explicitColdPrimeTwo ^ 2 ≤
        routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d := by
    exact wallNormalizedWeight_two_sq_le_primeGammaWallCoherenceExpectation hdpos
  have hw := twelve_div_twentyFive_lt_wallNormalizedWeight_two_of_one_le hd
  nlinarith [sq_nonneg
    (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d explicitColdPrimeTwo - 12 / 25)]

/-- Every cold-half-ray wall projective jet lies strictly above Xi's `9/80` ceiling. -/
theorem nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_of_one_le
    {d : ℝ} (hd : 1 ≤ d) :
    (9 / 80 : ℝ) <
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re := by
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_eq_half_coherence
    (lt_of_lt_of_le (by norm_num) hd)]
  norm_num
  linarith [nine_div_forty_lt_primeGammaWallCoherenceExpectation_of_one_le hd]

/-- No scalar irregular-time rescaling identifies Xi with any prime/Gamma wall at aperture
`d ≥ 1`. -/
theorem forall_one_le_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt :
    ∀ d : ℝ, 1 ≤ d →
      ¬ RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt d := by
  intro d hd
  have hgap :=
    nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_of_one_le hd
  rintro ⟨c, hgerm⟩
  have hfirst := hgerm.iteratedDeriv_eq 1
  rw [iteratedDeriv_canonicalXiSeamLog_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_one] at hfirst
  change (normalizedPrimeArchMoment 0 : ℂ) / 2 =
    c * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 at hfirst
  have hca : c * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ≠ 0 := by
    rw [← hfirst]
    exact div_ne_zero
      (Complex.ofReal_ne_zero.mpr normalizedPrimeArchMoment_zero_pos.ne') (by norm_num)
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hca).1
  have ha : routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ≠ 0 :=
    (mul_ne_zero_iff.mp hca).2
  have hprojective :
      routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet canonicalXiSeamLog =
        routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
          (fun z => Complex.log
            (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) := by
    unfold routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
    rw [hgerm.iteratedDeriv_eq 1, hgerm.iteratedDeriv_eq 2]
  rw [routePPrimitiveGammaJuliaStokes_canonicalXiSeamLog_projectiveTwoJet,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_projectiveTwoJet hc ha]
      at hprojective
  have hre : normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 =
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hprojective
  have hlt := normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty
  rw [hre] at hlt
  linarith

end
end RHTower
