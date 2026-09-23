import GaloisForLFunctions.RHTower.RapidExponentialFockLocalEvaluation
import GaloisForLFunctions.RHTower.RapidExponentialFockPrimeWindow
import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume

/-!
# Rapid exponential-Fock critical-prime ball overlap

Literal local balls from the weighted mean estimate fit inside a fixed multiple of the exact rapid
adapted radius at their observation point.  The additive prime-window theorem therefore gives a
uniform finite overlap bound and finite prime heads whose tail overlap tends to zero.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Fixed aperture converting local radii at prime-log centers to the adapted radius at an
observation point. -/
def rapidExponentialFockOverlapFactor (a : ℝ) : ℝ :=
  Real.exp (a / 8) * Real.sqrt (4 * a ^ (2 : ℕ) + 2 * a) / (8 * (a + 1))

theorem rapidExponentialFockOverlapFactor_pos
    {a : ℝ} (ha : 0 < a) :
    0 < rapidExponentialFockOverlapFactor a := by
  unfold rapidExponentialFockOverlapFactor
  positivity

/-- A local prime-log ball is contained in one fixed adapted window at the observation point. -/
theorem abs_primeLog_sub_re_lt_rapidExponentialFockOverlapRadius
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) {z : ℂ}
    (hzre : 1 ≤ z.re)
    (hz : z ∈ Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
      (rapidExponentialFockLocalRadius a (Real.log (p : ℝ)))) :
    |Real.log (p : ℝ) - z.re| <
      rapidExponentialFockOverlapFactor a *
        rapidExponentialFockAdaptedRadius a z.re := by
  let xp : ℝ := Real.log (p : ℝ)
  have hnorm : ‖(xp : ℂ) - z‖ < rapidExponentialFockLocalRadius a xp := by
    rw [norm_sub_rev]
    simpa [xp, Metric.mem_ball, dist_eq_norm] using hz
  have habs : |xp - z.re| ≤ ‖(xp : ℂ) - z‖ := by
    simpa using Complex.abs_re_le_norm ((xp : ℂ) - z)
  have hlocal : |xp - z.re| < rapidExponentialFockLocalRadius a xp :=
    habs.trans_lt hnorm
  have hxp0 : 0 ≤ xp := by
    dsimp [xp]
    exact Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hradius : rapidExponentialFockLocalRadius a xp ≤ 1 / 8 :=
    rapidExponentialFockLocalRadius_le_one_eighth ha hxp0
  have hxpLower : z.re - 1 / 8 < xp := by
    have := (abs_lt.mp (hlocal.trans_le hradius)).1
    linarith
  have hexp : Real.exp (-a * xp) <
      Real.exp (a / 8) * Real.exp (-a * z.re) := by
    have harg : -a * xp < -a * (z.re - 1 / 8) := by
      nlinarith
    calc
      Real.exp (-a * xp) < Real.exp (-a * (z.re - 1 / 8)) :=
        Real.exp_lt_exp.mpr harg
      _ = Real.exp (a / 8) * Real.exp (-a * z.re) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hcoeff : 0 < Real.sqrt (4 * a ^ (2 : ℕ) + 2 * a) := by positivity
  have hadapt := rapidExponentialFockAdaptedRadius_lower ha hzre
  have hscale : rapidExponentialFockLocalRadius a xp <
      rapidExponentialFockOverlapFactor a *
        ((Real.sqrt (4 * a ^ (2 : ℕ) + 2 * a))⁻¹ * Real.exp (-a * z.re)) := by
    unfold rapidExponentialFockLocalRadius rapidExponentialFockOverlapFactor
    calc
      (8 * (a + 1))⁻¹ * Real.exp (-a * xp) <
          (8 * (a + 1))⁻¹ *
            (Real.exp (a / 8) * Real.exp (-a * z.re)) := by gcongr
      _ = (Real.exp (a / 8) * Real.sqrt (4 * a ^ (2 : ℕ) + 2 * a) /
            (8 * (a + 1))) *
          ((Real.sqrt (4 * a ^ (2 : ℕ) + 2 * a))⁻¹ *
            Real.exp (-a * z.re)) := by
        field_simp [hcoeff.ne']
  exact hlocal.trans (hscale.trans_le
    (mul_le_mul_of_nonneg_left hadapt
      (rapidExponentialFockOverlapFactor_pos ha).le))

/-- Finite local-ball mass is bounded by one literal rapid adapted prime window. -/
theorem sum_criticalPrimeSamplingWeight_rapidLocalBalls_le_windowMass
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hzre : 1 ≤ z.re)
    (T : Finset Nat.Primes) :
    (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
      then criticalPrimeSamplingWeight p else 0) ≤
      primeLogWindowMass z.re
        (rapidExponentialFockOverlapFactor a *
          rapidExponentialFockAdaptedRadius a z.re) := by
  classical
  let R : ℝ := rapidExponentialFockOverlapFactor a *
    rapidExponentialFockAdaptedRadius a z.re
  let S : Finset Nat.Primes := T.filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
  have hR : 0 < R := by
    dsimp [R]
    exact mul_pos (rapidExponentialFockOverlapFactor_pos ha)
      (rapidExponentialFockAdaptedRadius_pos ha (zero_lt_one.trans_le hzre))
  have hsub : S.image (fun p : Nat.Primes => (p : ℕ)) ⊆
      Finset.Ioc ⌊Real.exp (z.re - R)⌋₊ ⌊Real.exp (z.re + R)⌋₊ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hpS, rfl⟩ := hn
    have hpball : z ∈ Metric.ball ((Real.log (p : ℝ) : ℝ) : ℂ)
        (rapidExponentialFockLocalRadius a (Real.log (p : ℝ))) := by
      simpa [Metric.mem_ball] using (Finset.mem_filter.mp hpS).2
    apply mem_primeLogWindow_of_abs_log_sub_lt p.prop
    simpa [R] using
      abs_primeLog_sub_re_lt_rapidExponentialFockOverlapRadius ha p hzre hpball
  rw [primeLogWindowMass_eq_sum z.re hR.le]
  rw [← Finset.sum_filter]
  change (∑ p ∈ S, criticalPrimeSamplingWeight p) ≤ _
  calc
    (∑ p ∈ S, criticalPrimeSamplingWeight p) =
        ∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n := by
      symm
      calc
        (∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n) =
            ∑ p ∈ S, primeLogPowWeight 2 (p : ℕ) :=
          Finset.sum_image (fun p _ q _ h => Subtype.ext h)
        _ = ∑ p ∈ S, criticalPrimeSamplingWeight p := by simp
    _ ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp (z.re - R)⌋₊ ⌊Real.exp (z.re + R)⌋₊,
        primeLogPowWeight 2 n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => primeLogPowWeight_two_nonneg n)

/-- A canonical uniform finite-overlap bound for all local prime balls. -/
theorem exists_uniform_criticalPrime_rapidLocalBallMass_bound
    {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p else 0) ≤ B := by
  let c : ℝ := rapidExponentialFockOverlapFactor a
  let W : ℝ → ℝ := fun x =>
    primeLogWindowMass x (c * rapidExponentialFockAdaptedRadius a x)
  have hc : 0 < c := rapidExponentialFockOverlapFactor_pos ha
  have hW : Tendsto W atTop (nhds 0) :=
    tendsto_primeLogWindowMass_rapidExponentialFockAdaptedRadius_zero ha hc
  have hev := hW.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  let Y : ℝ := max 1 X
  let B : ℝ := max 1 (primeLogPowSum 2 (Real.exp (Y + 1)))
  refine ⟨B, (primeLogPowSum_nonneg 2 _).trans (le_max_right _ _), fun z T => ?_⟩
  by_cases hz : 1 ≤ z.re
  · by_cases hY : Y ≤ z.re
    · have hwindow := sum_criticalPrimeSamplingWeight_rapidLocalBalls_le_windowMass
          ha hz T
      have hdist := hX z.re ((le_max_right 1 X).trans hY)
      have habs : |W z.re| < 1 := by simpa [Real.dist_eq] using hdist
      have hnonneg : 0 ≤ W z.re := by
        have hempty := sum_criticalPrimeSamplingWeight_rapidLocalBalls_le_windowMass
          ha hz (∅ : Finset Nat.Primes)
        simpa [W, c] using hempty
      exact hwindow.trans (le_max_of_le_left
        (le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)))
    · have hzY : z.re < Y := lt_of_not_ge hY
      apply le_max_of_le_right
      classical
      let S : Finset Nat.Primes := T.filter fun p =>
        dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
      have hsub : S.image (fun p : Nat.Primes => (p : ℕ)) ⊆
          Finset.Icc 0 ⌊Real.exp (Y + 1)⌋₊ := by
        intro n hn
        rw [Finset.mem_image] at hn
        obtain ⟨p, hpS, rfl⟩ := hn
        have hp0 : 0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
        have hr := rapidExponentialFockLocalRadius_le_one_eighth ha hp0
        have hpdist := (Finset.mem_filter.mp hpS).2
        have habs : |Real.log (p : ℝ) - z.re| <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
          have hre := Complex.abs_re_le_norm
            (((Real.log (p : ℝ) : ℝ) : ℂ) - z)
          have hnorm : ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ <
              rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
            rw [norm_sub_rev]
            simpa [dist_eq_norm] using hpdist
          exact hre.trans_lt hnorm
        have hlog : Real.log (p : ℝ) < Y + 1 := by
          have := (abs_lt.mp (habs.trans_le hr)).2
          linarith
        apply Finset.mem_Icc.mpr
        constructor
        · exact Nat.zero_le _
        · have hpReal : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
          have hpExp : (p : ℝ) ≤ Real.exp (Y + 1) := by
            rw [← Real.exp_log hpReal]
            exact Real.exp_le_exp.mpr hlog.le
          exact Nat.le_floor hpExp
      rw [← Finset.sum_filter]
      change (∑ p ∈ S, criticalPrimeSamplingWeight p) ≤ _
      calc
        (∑ p ∈ S, criticalPrimeSamplingWeight p) =
            ∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)),
              primeLogPowWeight 2 n := by
          symm
          calc
            (∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n) =
                ∑ p ∈ S, primeLogPowWeight 2 (p : ℕ) :=
              Finset.sum_image (fun p _ q _ h => Subtype.ext h)
            _ = ∑ p ∈ S, criticalPrimeSamplingWeight p := by simp
        _ ≤ ∑ n ∈ Finset.Icc 0 ⌊Real.exp (Y + 1)⌋₊,
            primeLogPowWeight 2 n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => primeLogPowWeight_two_nonneg n)
        _ = primeLogPowSum 2 (Real.exp (Y + 1)) := by
          rfl
  · apply le_max_of_le_right
    classical
    let S : Finset Nat.Primes := T.filter fun p =>
      dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
    have hsub : S.image (fun p : Nat.Primes => (p : ℕ)) ⊆
        Finset.Icc 0 ⌊Real.exp (Y + 1)⌋₊ := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨p, hpS, rfl⟩ := hn
      have hp0 : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
      have hr := rapidExponentialFockLocalRadius_le_one_eighth ha hp0
      have hpdist := (Finset.mem_filter.mp hpS).2
      have habs : |Real.log (p : ℝ) - z.re| <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
        have hre := Complex.abs_re_le_norm
          (((Real.log (p : ℝ) : ℝ) : ℂ) - z)
        have hnorm : ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
          rw [norm_sub_rev]
          simpa [dist_eq_norm] using hpdist
        exact hre.trans_lt hnorm
      have hlog : Real.log (p : ℝ) < Y + 1 := by
        have := (abs_lt.mp (habs.trans_le hr)).2
        have hzY : z.re < Y := lt_of_not_ge hz |>.trans_le (le_max_left 1 X)
        linarith
      apply Finset.mem_Icc.mpr
      refine ⟨Nat.zero_le _, ?_⟩
      have hpReal : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
      have hpExp : (p : ℝ) ≤ Real.exp (Y + 1) := by
        rw [← Real.exp_log hpReal]
        exact Real.exp_le_exp.mpr hlog.le
      exact Nat.le_floor hpExp
    rw [← Finset.sum_filter]
    change (∑ p ∈ S, criticalPrimeSamplingWeight p) ≤ _
    calc
      (∑ p ∈ S, criticalPrimeSamplingWeight p) =
          ∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n := by
        symm
        calc
          (∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)), primeLogPowWeight 2 n) =
              ∑ p ∈ S, primeLogPowWeight 2 (p : ℕ) :=
            Finset.sum_image (fun p _ q _ h => Subtype.ext h)
          _ = ∑ p ∈ S, criticalPrimeSamplingWeight p := by simp
      _ ≤ ∑ n ∈ Finset.Icc 0 ⌊Real.exp (Y + 1)⌋₊, primeLogPowWeight 2 n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => primeLogPowWeight_two_nonneg n)
      _ = primeLogPowSum 2 (Real.exp (Y + 1)) := by rfl

/-- Local rapid-ball overlaps admit finite prime heads with quantitative vanishing tails. -/
theorem exists_criticalPrime_rapidLocalBallTail_bound
    {a : ℝ} (ha : 0 < a) :
    ∃ P : ℕ → Finset Nat.Primes, ∀ (n : ℕ) (z : ℂ) (T : Finset Nat.Primes),
      (∑ p ∈ T.filter (· ∉ P n),
        if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) ≤
        ((n : ℝ) + 1)⁻¹ := by
  classical
  let c : ℝ := rapidExponentialFockOverlapFactor a
  let W : ℝ → ℝ := fun x =>
    primeLogWindowMass x (c * rapidExponentialFockAdaptedRadius a x)
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hc : 0 < c := rapidExponentialFockOverlapFactor_pos ha
  have hW : Tendsto W atTop (nhds 0) :=
    tendsto_primeLogWindowMass_rapidExponentialFockAdaptedRadius_zero ha hc
  have hδpos : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  have hexists : ∀ n : ℕ, ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |W x| < δ n := by
    intro n
    have hev := hW.eventually (Metric.ball_mem_nhds (0 : ℝ) (hδpos n))
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    exact ⟨X, fun x hx => by simpa [Real.dist_eq] using hX x hx⟩
  choose X hX using hexists
  let Y : ℕ → ℝ := fun n => max 1 (X n)
  let P : ℕ → Finset Nat.Primes := fun n =>
    GaloisForLFunctions.primesBelowSubtype
      (⌊Real.exp (Y n + 1 / 4)⌋₊ + 1)
  refine ⟨P, fun n z T => ?_⟩
  let S : Finset Nat.Primes := (T.filter (· ∉ P n)).filter fun p =>
    dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
  by_cases hS : S.Nonempty
  · obtain ⟨p, hpS⟩ := hS
    have hpTail : p ∉ P n := (Finset.mem_filter.mp (Finset.mem_filter.mp hpS).1).2
    have hpBall : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) :=
      (Finset.mem_filter.mp hpS).2
    have hpLower : ⌊Real.exp (Y n + 1 / 4)⌋₊ + 1 ≤ (p : ℕ) := by
      have hnotlt : ¬ (p : ℕ) < ⌊Real.exp (Y n + 1 / 4)⌋₊ + 1 := by
        intro hlt
        apply hpTail
        rw [mem_primesBelowSubtype_iff]
        exact hlt
      omega
    have hexplt : Real.exp (Y n + 1 / 4) < (p : ℝ) := by
      apply (Nat.floor_lt' p.prop.ne_zero).mp
      omega
    have hplog : Y n + 1 / 4 < Real.log (p : ℝ) := by
      have hpcastpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
      have hlog := Real.log_lt_log (Real.exp_pos _) hexplt
      simpa using hlog
    have hp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
    have hr := rapidExponentialFockLocalRadius_le_one_eighth ha hp0
    have hnorm : ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
      rw [norm_sub_rev]
      simpa [dist_eq_norm] using hpBall
    have habs : |Real.log (p : ℝ) - z.re| ≤
        ‖((Real.log (p : ℝ) : ℝ) : ℂ) - z‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm
        (((Real.log (p : ℝ) : ℝ) : ℂ) - z)
    have hlocal : |Real.log (p : ℝ) - z.re| <
        rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) :=
      habs.trans_lt hnorm
    have hzY : Y n < z.re := by
      have hright := (abs_lt.mp (hlocal.trans_le hr)).2
      linarith
    have hzre : 1 ≤ z.re := (le_max_left 1 (X n)).trans hzY.le
    have hWX : |W z.re| < δ n := hX n z.re ((le_max_right 1 (X n)).trans hzY.le)
    have hsumWindow := sum_criticalPrimeSamplingWeight_rapidLocalBalls_le_windowMass
      ha hzre (T.filter (· ∉ P n))
    have hWnonneg : 0 ≤ W z.re := by
      have hempty := sum_criticalPrimeSamplingWeight_rapidLocalBalls_le_windowMass
        ha hzre (∅ : Finset Nat.Primes)
      simpa [W, c] using hempty
    calc
      (∑ p ∈ T.filter (· ∉ P n),
          if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
              rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
            then criticalPrimeSamplingWeight p else 0) ≤ W z.re := by
        simpa [W, c] using hsumWindow
      _ ≤ |W z.re| := le_abs_self _
      _ ≤ δ n := hWX.le
      _ = ((n : ℝ) + 1)⁻¹ := rfl
  · have hzero : ∀ p ∈ T.filter (· ∉ P n),
        (if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
            rapidExponentialFockLocalRadius a (Real.log (p : ℝ))
          then criticalPrimeSamplingWeight p else 0) = 0 := by
      intro p hp
      have hpnot : ¬ dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          rapidExponentialFockLocalRadius a (Real.log (p : ℝ)) := by
        intro hpball
        apply hS
        exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpball⟩⟩
      exact if_neg hpnot
    rw [Finset.sum_eq_zero hzero]
    positivity

end

end RHTower
