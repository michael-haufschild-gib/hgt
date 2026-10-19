import GaloisForLFunctions.ArithmeticCriticalityTheory.TwoBumpProfile

/-!
# Markov positivity of far-apart bumps with nonzero exponential moment

Let `g` be even, `C²`, supported in `[−1/4, 1/4]`, with `μ = ∫ g(u) e^{u/2} du ≠ 0`. The odd test
`g(x − a) − g(−x − a)` is `Φ(ω_a u)` for the two-bump profile `u`, and the cross-term representation
gives

    markovEnergy ≥ 2 X_a(u) − 2 ∫_{x>0} u² m_a (C_a − 2 sinh(a/2) sinh(x/2)).

On the window `|x − a| ≤ 1/4` the collar excess `C_a − 2 sinh(a/2) sinh(x/2)` is bounded by a
universal constant (the archimedean collar is at most `1`, the signed prime sum is evaluated by the
harmonic identity, the discarded negative parts are at most `primeKernelSum(x − a)`), and `u² m_a =
g(x−a)²/m_a(x)` is bounded there since `m_a ≥ Φ(1/4) − Φ(7/4)`. The cross energy is the archimedean
term, at most `(3/2) sup|ρ_g|` in absolute value, plus the smoothed log-window sum
`Σ Λ(n) n^{−1/2} ρ_g(log n − 2a)`, which the prime number theorem in log windows evaluates as
`2 μ² cosh a + O(1 + e^{a} e^{−√(2a)/1920000})`. Hence the Markov energy is at least
`μ² e^{a} − K` for all large `a`, and positive.

Together with the general origin failure this locates the hard core of the variation inequality:
profiles with `∫ g e^{u/2} = 0`, for which the pole term vanishes.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilOneSided RHTower.ThetaSourceWard

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The collar excess on the window `|x − a| ≤ 1/4` -/

theorem integral_riemannKernelReal_le_half : (∫ x, riemannKernelReal x) ≤ 1 / 2 := by
  rw [← integral_riemannKernelReal_cosh_half]
  have hint : Integrable fun x : ℝ => riemannKernelReal x * Real.cosh (x / 2) := by
    have h := ((integrable_riemannKernelReal_mul_exp (1 / 2)).add
      (integrable_riemannKernelReal_mul_exp (-(1 / 2)))).const_mul (1 / 2)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [Real.cosh_eq, show x / 2 = 1 / 2 * x by ring, show -(1 / 2 * x) = -(1 / 2) * x by ring]
    ring
  refine integral_mono integrable_riemannKernelReal hint fun x => ?_
  exact le_mul_of_one_le_right (riemannKernelReal_pos x).le (Real.one_le_cosh _)

/-- The archimedean collar is at most `1` on the window. -/
theorem archCollar_le_one {a x : ℝ} (ha : 1 ≤ a) (hx : |x - a| ≤ 1 / 4) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0) ≤ 1 := by
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hint := integrableOn_archLevy_max_shiftDifference ha0 hx0
  have hmaj' : Integrable fun t : ℝ => 2 * riemannKernelReal (t - (x + a)) :=
    (integrable_riemannKernelReal.comp_sub_right (x + a)).const_mul 2
  have hmaj : IntegrableOn (fun t : ℝ => 2 * riemannKernelReal (t - (x + a))) (Ioi 0) :=
    hmaj'.integrableOn
  have hpt : ∀ t ∈ Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0 ≤
      2 * riemannKernelReal (t - (x + a)) := by
    intro t ht
    have hΘ := (riemannKernelReal_pos (t - (x + a))).le
    rcases le_or_gt t x with htx | htx
    · rw [max_eq_right (shiftDifference_nonpos_of_nonpos ha0.le (by linarith)), mul_zero]
      exact mul_nonneg (by norm_num) hΘ
    · have hω : archLevyDensity t ≤ 2 := by
        rcases le_or_gt t 1 with h1 | h1
        · calc archLevyDensity t ≤ 3 / 2 / t := archLevyDensity_le_of_le_one (mem_Ioi.mp ht) h1
            _ ≤ 2 := by
              rw [div_le_iff₀ (mem_Ioi.mp ht)]
              linarith
        · calc archLevyDensity t ≤ 3 / 2 * Real.exp (-t / 2) := archLevyDensity_le_of_one_le h1.le
            _ ≤ 3 / 2 * 1 := mul_le_mul_of_nonneg_left
                (Real.exp_le_one_iff.mpr (by linarith)) (by norm_num)
            _ ≤ 2 := by norm_num
      have hm : max (shiftDifference a (t - x)) 0 ≤ riemannKernelReal (t - (x + a)) := by
        refine max_le ?_ hΘ
        have := shiftDifference_le_kernel a (t - x)
        rwa [show t - x - a = t - (x + a) by ring] at this
      exact mul_le_mul hω hm (le_max_right _ _) (by norm_num)
  calc (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0)
      ≤ ∫ t in Ioi (0 : ℝ), 2 * riemannKernelReal (t - (x + a)) :=
        setIntegral_mono_on hint hmaj measurableSet_Ioi hpt
    _ ≤ ∫ t, 2 * riemannKernelReal (t - (x + a)) :=
        setIntegral_le_integral hmaj' (Eventually.of_forall fun t =>
          mul_nonneg (by norm_num) (riemannKernelReal_pos _).le)
    _ = 2 * ∫ t, riemannKernelReal t := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun t => riemannKernelReal t) (x + a)]
    _ ≤ 2 * (1 / 2) := mul_le_mul_of_nonneg_left integral_riemannKernelReal_le_half (by norm_num)
    _ = 1 := by norm_num

/-- `Q(y) ≤ Σ Λ(n) n^{−1/2} Φ(log n − 1/4)` for `y ≥ −1/4`. -/
theorem rightPrimeShift_le_of_quarter_le {y : ℝ} (hy : -(1 / 4) ≤ y) :
    rightPrimeShift y ≤ leftPrimeShift (1 / 4) := by
  unfold rightPrimeShift leftPrimeShift
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_primeShift_right y)
    (summable_primeShift_left (1 / 4))
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hn]
    simp
  · refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
    have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h14 : (1 / 4 : ℝ) ≤ Real.log n := by linarith [half_lt_log_two]
    rw [show (1 / 4 : ℝ) - Real.log n = -(Real.log n - 1 / 4) by ring, riemannKernelReal_neg']
    exact riemannKernelReal_antitone_of_nonneg (by linarith) (by linarith)

/-- The universal constant bounding the collar excess on the window. -/
def windowCollarConstant : ℝ :=
  1 + 4 * |archConstantReal| * riemannKernelReal 0 + 6 * gammaSourceBoundMass +
    leftPrimeShift (1 / 4) + Real.cosh (1 / 8)

theorem gammaSourceBoundMass_nonneg : 0 ≤ gammaSourceBoundMass :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu =>
    le_trans (abs_nonneg _) (abs_gammaSourceTerm_le_bound 0 (mem_Ioi.mp hu))

theorem leftPrimeShift_nonneg (y : ℝ) : 0 ≤ leftPrimeShift y :=
  tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le

theorem windowCollarConstant_nonneg : 0 ≤ windowCollarConstant := by
  unfold windowCollarConstant
  have := gammaSourceBoundMass_nonneg
  have := leftPrimeShift_nonneg (1 / 4 : ℝ)
  have := (riemannKernelReal_pos 0).le
  have := (Real.cosh_pos (1 / 8 : ℝ)).le
  positivity

/-- **Collar excess on the window.** For `a ≥ 1` and `|x − a| ≤ 1/4`,
`C_a(x) − 2 sinh(a/2) sinh(x/2) ≤ windowCollarConstant`. -/
theorem shiftedCollarMass_sub_le_windowCollarConstant {a x : ℝ} (ha : 1 ≤ a) (hx : |x - a| ≤ 1 / 4) :
    shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2) ≤ windowCollarConstant := by
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hΘ0 := (riemannKernelReal_pos 0).le
  have harch := archCollar_le_one ha hx
  -- prime part
  have hterm : ∀ n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 ≤
      vonMangoldtAtom n * shiftDifference a (Real.log n - x) +
        vonMangoldtAtom n * riemannKernelReal (x - a - Real.log n) := by
    intro n
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
    have hΘ := (riemannKernelReal_pos (x - a - Real.log n)).le
    rcases le_or_gt 0 (shiftDifference a (Real.log n - x)) with h | h
    · rw [max_eq_left h]
      linarith
    · rw [max_eq_right h.le]
      have h1 := shiftDifference_le_kernel a (x - Real.log n)
      have h2 : shiftDifference a (x - Real.log n) = -shiftDifference a (Real.log n - x) := by
        rw [show x - Real.log n = -(Real.log n - x) by ring, shiftDifference_neg]
      rw [show x - Real.log n - a = x - a - Real.log n by ring] at h1
      linarith
  have hsum : (∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0) ≤
      signedPrimeShift a x + leftPrimeShift (x - a) := by
    unfold signedPrimeShift leftPrimeShift
    rw [← (summable_atom_shiftDifference_log_sub a x).tsum_add (summable_primeShift_left (x - a))]
    exact Summable.tsum_le_tsum hterm (summable_atom_max_shiftDifference a x)
      ((summable_atom_shiftDifference_log_sub a x).add (summable_primeShift_left (x - a)))
  -- the signed sum
  have hsigned : signedPrimeShift a x ≤ 2 * Real.sinh (a / 2) * Real.sinh (x / 2) +
      2 * |archConstantReal| * riemannKernelReal 0 + 4 * gammaSourceBoundMass +
        leftPrimeShift (1 / 4) := by
    rw [signedPrimeShift_eq]
    have hP : ∀ y, leftPrimeShift y = primeKernelSum y - rightPrimeShift y := fun y => by
      rw [primeKernelSum_eq_add]
      ring
    rw [hP, hP, theta_harmonic_identity, theta_harmonic_identity]
    have hQ1 := rightPrimeShift_nonneg (x + a)
    have hQ2 := rightPrimeShift_le_of_quarter_le (show -(1 / 4 : ℝ) ≤ x - a by linarith)
    have hA1 := abs_le.mp (abs_integral_symArchTerm_le (x + a))
    have hA2 := abs_le.mp (abs_integral_symArchTerm_le (x - a))
    have hcosh : Real.cosh ((x + a) / 2) - Real.cosh ((x - a) / 2) =
        2 * Real.sinh (a / 2) * Real.sinh (x / 2) := by
      rw [show (x + a) / 2 = x / 2 + a / 2 by ring, show (x - a) / 2 = x / 2 - a / 2 by ring,
        Real.cosh_add, Real.cosh_sub]
      ring
    have hΘ1 := riemannKernelReal_pos (x + a)
    have hΘ2 := riemannKernelReal_pos (x - a)
    have hΘ1' := riemannKernelReal_le_zero_point (x + a)
    have hΘ2' := riemannKernelReal_le_zero_point (x - a)
    have hc : -(2 * archConstantReal * riemannKernelReal (x + a)) +
        2 * archConstantReal * riemannKernelReal (x - a) ≤
        2 * |archConstantReal| * riemannKernelReal 0 := by
      have habs : |2 * archConstantReal * (riemannKernelReal (x - a) - riemannKernelReal (x + a))| ≤
          2 * |archConstantReal| * riemannKernelReal 0 := by
        rw [abs_mul, abs_mul, abs_two]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [abs_sub_le_iff]
        constructor <;> linarith
      have := (abs_le.mp habs).2
      linarith
    linarith [hA1.2, hA2.1, hcosh]
  -- the negative parts
  have hneg : leftPrimeShift (x - a) ≤ Real.cosh (1 / 8) +
      2 * |archConstantReal| * riemannKernelReal 0 + 2 * gammaSourceBoundMass := by
    have h1 : leftPrimeShift (x - a) ≤ primeKernelSum (x - a) := by
      rw [primeKernelSum_eq_add]
      linarith [rightPrimeShift_nonneg (x - a)]
    have h2 := primeKernelSum_le (x - a)
    have h3 : Real.cosh ((x - a) / 2) ≤ Real.cosh (1 / 8) := by
      rw [Real.cosh_le_cosh, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8), abs_le]
      constructor <;> linarith
    linarith
  unfold shiftedCollarMass windowCollarConstant
  linarith

/-! ### The two-bump profile on the window -/

/-- The kernel floor `Φ(1/4) − Φ(7/4)` of `m_a` on the window. -/
def windowKernelFloor : ℝ := riemannKernelReal (1 / 4) - riemannKernelReal (7 / 4)

theorem windowKernelFloor_pos : 0 < windowKernelFloor :=
  sub_pos.mpr (strictAntiOn_riemannKernelReal_Ici (mem_Ici.mpr (by norm_num))
    (mem_Ici.mpr (by norm_num)) (by norm_num))

theorem windowKernelFloor_le_shiftDifference {a x : ℝ} (ha : 1 ≤ a) (hx : |x - a| ≤ 1 / 4) :
    windowKernelFloor ≤ shiftDifference a x := by
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  unfold windowKernelFloor shiftDifference
  have h1 : riemannKernelReal (1 / 4) ≤ riemannKernelReal (x - a) := by
    rw [← riemannKernelReal_abs' (x - a)]
    exact riemannKernelReal_antitone_of_nonneg (abs_nonneg _) hx
  have h2 : riemannKernelReal (x + a) ≤ riemannKernelReal (7 / 4) :=
    riemannKernelReal_antitone_of_nonneg (by norm_num) (by linarith)
  linarith

theorem twoBumpProfile_eq_zero_of_window {g : ℝ → ℝ} (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    {a x : ℝ} (ha : 1 ≤ a) (hx0 : 0 < x) (hx : 1 / 4 < |x - a|) : twoBumpProfile g a x = 0 := by
  unfold twoBumpProfile
  rw [hsupp (x - a) hx, hsupp (-x - a) (by rw [abs_of_neg (by linarith)]; linarith), zero_div,
    zero_div, add_zero]

/-- `u² m_a = g(x−a)²/m_a(x) ≤ M_g²/floor` on the window. -/
theorem sq_twoBumpProfile_mul_shiftDifference_le {g : ℝ → ℝ} (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    {Mg : ℝ} (hMg : ∀ u, |g u| ≤ Mg) {a x : ℝ} (ha : 1 ≤ a) (hx : |x - a| ≤ 1 / 4) :
    twoBumpProfile g a x ^ 2 * shiftDifference a x ≤ Mg ^ 2 / windowKernelFloor := by
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  have hx0 : 0 < x := by linarith
  have hm := windowKernelFloor_le_shiftDifference ha hx
  have hfl := windowKernelFloor_pos
  have hmpos : 0 < shiftDifference a x := lt_of_lt_of_le hfl hm
  have he := shiftDifference_mul_twoBumpProfile hsupp ha hx0
  have hu : twoBumpProfile g a x = g (x - a) / shiftDifference a x := by
    rw [eq_div_iff hmpos.ne', mul_comm]
    exact he
  have hg2 : g (x - a) ^ 2 ≤ Mg ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMg _) 2
  have e : (g (x - a) / shiftDifference a x) ^ 2 * shiftDifference a x =
      g (x - a) ^ 2 / shiftDifference a x := by
    rw [div_pow, div_mul_eq_mul_div, sq (shiftDifference a x),
      mul_div_mul_right _ _ hmpos.ne']
  rw [hu, e]
  exact div_le_div₀ (sq_nonneg _) hg2 hfl hm

theorem integrableOn_sq_mul_collar_excess {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x *
      (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2))) (Ioi 0) := by
  have hI1 := integrableOn_sq_mul_shiftDifference_mul_collarMass ha hu huc
  have hI2 : IntegrableOn (fun x => (2 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2)) *
      u x ^ 2) (Ioi 0) :=
    integrableOn_continuous_mul_sq ((continuous_const.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))) hu huc _
  refine (hI1.sub hI2).congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]
  ring

/-- The remainder term of the two-bump profile is bounded by a constant. -/
theorem integral_sq_twoBump_collar_excess_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {Mg : ℝ}
    (hMg : ∀ u, |g u| ≤ Mg) {a : ℝ} (ha : 1 ≤ a) :
    (∫ x in Ioi (0 : ℝ), twoBumpProfile g a x ^ 2 * shiftDifference a x *
        (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2))) ≤
      windowCollarConstant * (Mg ^ 2 / windowKernelFloor) * (1 / 2) := by
  have ha0 : 0 < a := by linarith
  have hu := (contDiff_twoBumpProfile hg hsupp ha).continuous
  have huc := hasCompactSupport_twoBumpProfile hgc a
  have hint := integrableOn_sq_mul_collar_excess ha0 hu huc
  have hB0 : 0 ≤ windowCollarConstant * (Mg ^ 2 / windowKernelFloor) :=
    mul_nonneg windowCollarConstant_nonneg (div_nonneg (sq_nonneg _) windowKernelFloor_pos.le)
  have hg0 : IntegrableOn (fun _ : ℝ => windowCollarConstant * (Mg ^ 2 / windowKernelFloor))
      (Icc (a - 1 / 4) (a + 1 / 4)) := integrableOn_const measure_Icc_lt_top.ne
  have hmaj : IntegrableOn ((Icc (a - 1 / 4) (a + 1 / 4)).indicator fun _ =>
      windowCollarConstant * (Mg ^ 2 / windowKernelFloor)) (Ioi 0) :=
    (hg0.integrable_indicator measurableSet_Icc).integrableOn
  have hpt : ∀ x ∈ Ioi (0 : ℝ), twoBumpProfile g a x ^ 2 * shiftDifference a x *
      (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2)) ≤
      (Icc (a - 1 / 4) (a + 1 / 4)).indicator
        (fun _ => windowCollarConstant * (Mg ^ 2 / windowKernelFloor)) x := by
    intro x hx
    rw [Set.indicator_apply]
    split_ifs with hmem
    · have hxw : |x - a| ≤ 1 / 4 := by
        rw [abs_le]
        constructor <;> linarith [hmem.1, hmem.2]
      have h1 := shiftedCollarMass_sub_le_windowCollarConstant ha hxw
      have h2 := sq_twoBumpProfile_mul_shiftDifference_le hsupp hMg ha hxw
      have h0 : 0 ≤ twoBumpProfile g a x ^ 2 * shiftDifference a x :=
        mul_nonneg (sq_nonneg _) (shiftDifference_nonneg_of_nonneg ha0.le (mem_Ioi.mp hx).le)
      calc twoBumpProfile g a x ^ 2 * shiftDifference a x *
            (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2))
          ≤ twoBumpProfile g a x ^ 2 * shiftDifference a x * windowCollarConstant :=
            mul_le_mul_of_nonneg_left h1 h0
        _ ≤ Mg ^ 2 / windowKernelFloor * windowCollarConstant :=
            mul_le_mul_of_nonneg_right h2 windowCollarConstant_nonneg
        _ = _ := by ring
    · have hxw : 1 / 4 < |x - a| := by
        rw [mem_Icc, not_and_or] at hmem
        rcases hmem with h | h
        · rw [not_le] at h
          rw [abs_of_neg (by linarith)]
          linarith
        · rw [not_le] at h
          rw [abs_of_pos (by linarith)]
          linarith
      rw [twoBumpProfile_eq_zero_of_window hsupp ha (mem_Ioi.mp hx) hxw]
      simp
  calc (∫ x in Ioi (0 : ℝ), twoBumpProfile g a x ^ 2 * shiftDifference a x *
        (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2)))
      ≤ ∫ x in Ioi (0 : ℝ), (Icc (a - 1 / 4) (a + 1 / 4)).indicator
          (fun _ => windowCollarConstant * (Mg ^ 2 / windowKernelFloor)) x :=
        setIntegral_mono_on hint hmaj measurableSet_Ioi hpt
    _ = windowCollarConstant * (Mg ^ 2 / windowKernelFloor) * (1 / 2) := by
        rw [setIntegral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Set.inter_eq_right.mpr (fun y hy => mem_Ioi.mpr (by linarith [(mem_Icc.mp hy).1])),
          Real.volume_real_Icc, show a + 1 / 4 - (a - 1 / 4) = (1 / 2 : ℝ) by ring,
          max_eq_left (by norm_num), mul_comm]

/-! ### The cross energy of the two-bump profile -/

theorem crossEnergy_twoBumpProfile_eq {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (heven : ∀ u, g (-u) = g u) {a : ℝ} (ha : 1 ≤ a) :
    crossEnergy a (twoBumpProfile g a) =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * autoCorr g (t - 2 * a)) +
        windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (2 * a) := by
  unfold crossEnergy
  rw [← tsum_atom_autoCorr_eq_windowSum hg hgc hsupp ha]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      rw [crossShift_twoBumpProfile hsupp heven ha t]
  · exact tsum_congr fun n => by rw [crossShift_twoBumpProfile hsupp heven ha]

/-- The archimedean cross term is at most `(3/2) sup|ρ_g|` in absolute value. -/
theorem abs_integral_archLevy_autoCorr_le {g : ℝ → ℝ} (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    {Hρ : ℝ} (hH : ∀ x, |autoCorr g x| ≤ Hρ) {a : ℝ} (ha : 1 ≤ a) :
    |∫ t in Ioi (0 : ℝ), archLevyDensity t * autoCorr g (t - 2 * a)| ≤ 3 / 2 * Hρ := by
  have hH0 : 0 ≤ Hρ := le_trans (abs_nonneg _) (hH 0)
  have hg0 : IntegrableOn (fun _ : ℝ => 3 / 2 * Hρ) (Icc (2 * a - 1 / 2) (2 * a + 1 / 2)) :=
    integrableOn_const measure_Icc_lt_top.ne
  have hmaj : Integrable ((Icc (2 * a - 1 / 2) (2 * a + 1 / 2)).indicator fun _ => 3 / 2 * Hρ)
      (volume.restrict (Ioi 0)) :=
    (hg0.integrable_indicator measurableSet_Icc).integrableOn
  have hle : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ‖archLevyDensity t * autoCorr g (t - 2 * a)‖ ≤
      (Icc (2 * a - 1 / 2) (2 * a + 1 / 2)).indicator (fun _ => 3 / 2 * Hρ) t :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      rw [Real.norm_eq_abs, Set.indicator_apply]
      split_ifs with hmem
      · rw [abs_mul, abs_of_pos (archLevyDensity_pos (mem_Ioi.mp ht))]
        have hω : archLevyDensity t ≤ 3 / 2 := by
          calc archLevyDensity t ≤ 3 / 2 * Real.exp (-t / 2) :=
                archLevyDensity_le_of_one_le (by linarith [hmem.1])
            _ ≤ 3 / 2 * 1 := mul_le_mul_of_nonneg_left
                (Real.exp_le_one_iff.mpr (by linarith [hmem.1])) (by norm_num)
            _ = 3 / 2 := by norm_num
        exact mul_le_mul hω (hH _) (abs_nonneg _) (by norm_num)
      · have hfar : 1 / 2 < |t - 2 * a| := by
          rw [mem_Icc, not_and_or] at hmem
          rcases hmem with h | h
          · rw [not_le] at h
            rw [abs_of_neg (by linarith)]
            linarith
          · rw [not_le] at h
            rw [abs_of_pos (by linarith)]
            linarith
        rw [autoCorr_eq_zero hsupp hfar, mul_zero, abs_zero]
  have h := norm_integral_le_of_norm_le hmaj hle
  rw [Real.norm_eq_abs, setIntegral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul] at h
  have hvol : volume.real (Ioi (0 : ℝ) ∩ Icc (2 * a - 1 / 2) (2 * a + 1 / 2)) ≤ 1 := by
    calc volume.real (Ioi (0 : ℝ) ∩ Icc (2 * a - 1 / 2) (2 * a + 1 / 2))
        ≤ volume.real (Icc (2 * a - 1 / 2) (2 * a + 1 / 2)) :=
          measureReal_mono inter_subset_right measure_Icc_lt_top.ne
      _ = 1 := by
          rw [Real.volume_real_Icc, show 2 * a + 1 / 2 - (2 * a - 1 / 2) = (1 : ℝ) by ring]
          norm_num
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_right hvol (by positivity : 0 ≤ 3 / 2 * Hρ)
  linarith

/-! ### The main theorem -/

/-- **Markov positivity of far-apart bumps.** For every even `g ∈ C²_c(ℝ)` supported in
`[−1/4, 1/4]` with `∫ g(u) e^{u/2} du ≠ 0`, there is `a₀` such that for every shift `a ≥ a₀` the
Markov energy of `Φ(ω_a · twoBumpProfile g a)`, the odd test `g(x − a) − g(−x − a)`, is positive. -/
theorem exists_shift_markovEnergy_twoBumpProfile_pos {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (heven : ∀ u, g (-u) = g u)
    (hμ : (∫ u, g u * Real.exp (u / 2)) ≠ 0) :
    ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → 0 < markovEnergy
      (fun x => (phiDoobTest (fun y => shiftedGroundState a y * twoBumpProfile g a y) x : ℂ)) := by
  obtain ⟨C, L₀, hPNT⟩ := exists_abs_windowSum_vonMangoldt_sub_le hg hgc hsupp
  obtain ⟨Kρ, Hρ, hK0, hH0, hK, hH, hcont⟩ := exists_autoCorr_constants hg hgc
  obtain ⟨Mg, hMg'⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hMg : ∀ u, |g u| ≤ Mg := fun u => by simpa [Real.norm_eq_abs] using hMg' u
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = ∫ u, g u * Real.exp (u / 2) := ⟨_, rfl⟩
  have hμ0 : μ ≠ 0 := hμdef ▸ hμ
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hPeq : (∫ u, g u * Real.exp (-u / 2)) = μ := by
    rw [hμdef, ← integral_neg_eq_self (fun u => g u * Real.exp (u / 2))]
    congr 1
    funext u
    show g u * Real.exp (-u / 2) = g (-u) * Real.exp (-u / 2)
    rw [heven]
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := hC' ▸ le_max_right _ _
  have hCC' : C ≤ C' := hC' ▸ le_max_left _ _
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 2 * C' + 3 * Hρ +
      windowCollarConstant * (Mg ^ 2 / windowKernelFloor) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    have := windowCollarConstant_nonneg
    have := windowKernelFloor_pos
    positivity
  -- the error factor tends to zero
  have hε : Tendsto (fun a : ℝ => Real.exp (-(Real.sqrt (2 * a) / 1920000))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun a : ℝ => Real.sqrt (2 * a) / 1920000) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop two_pos)).atTop_div_const
        (by norm_num)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have hev := hε.eventually_lt_const (show (0 : ℝ) < μ ^ 2 / (2 * (C' + 1)) by positivity)
  obtain ⟨a₁, ha₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max a₁ 1) (max (L₀ / 2) (Real.log (K₁ / μ ^ 2 + 1))), fun a ha => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ha)
  have haa₁ : a₁ ≤ a := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ha)
  have haL : L₀ ≤ 2 * a := by
    have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ha)
    linarith
  have halog : Real.log (K₁ / μ ^ 2 + 1) ≤ a :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ha)
  have hexp : K₁ / μ ^ 2 + 1 ≤ Real.exp a := by
    rw [← Real.exp_log (by positivity : 0 < K₁ / μ ^ 2 + 1)]
    exact Real.exp_le_exp.mpr halog
  have ha0 : 0 < a := by linarith
  -- the pieces
  have hu := contDiff_twoBumpProfile hg hsupp ha1
  have huc := hasCompactSupport_twoBumpProfile hgc a
  have hlow := markovEnergy_phiDoob_shiftedGroundState_ge_cross ha0 hu huc (twoBumpProfile_neg g a)
  have hcross := crossEnergy_twoBumpProfile_eq hg hgc hsupp heven ha1
  have harch := abs_le.mp (abs_integral_archLevy_autoCorr_le hsupp hH ha1)
  have hrem := integral_sq_twoBump_collar_excess_le hg hgc hsupp hMg ha1
  have hwin := hPNT (2 * a) haL
  rw [hPeq, ← hμdef, show (2 : ℝ) * a / 2 = a by ring] at hwin
  have hwin' := (abs_le.mp hwin).1
  have hcosh : Real.exp a / 2 ≤ Real.cosh a := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-a)]
  have hεa : Real.exp (-(Real.sqrt (2 * a) / 1920000)) < μ ^ 2 / (2 * (C' + 1)) := ha₁ a haa₁
  have hE0 : 0 ≤ Real.exp a * Real.exp (-(Real.sqrt (2 * a) / 1920000)) := by positivity
  have hC1 : C * (1 + Real.exp a * Real.exp (-(Real.sqrt (2 * a) / 1920000))) ≤
      C' * (1 + Real.exp a * Real.exp (-(Real.sqrt (2 * a) / 1920000))) :=
    mul_le_mul_of_nonneg_right hCC' (by linarith)
  have h1 : 2 * (C' + 1) * (Real.exp a * Real.exp (-(Real.sqrt (2 * a) / 1920000))) <
      μ ^ 2 * Real.exp a := by
    have h1' := mul_lt_mul_of_pos_left hεa (Real.exp_pos a)
    have h1'' := mul_lt_mul_of_pos_left h1' (by positivity : (0 : ℝ) < 2 * (C' + 1))
    have e : 2 * (C' + 1) * (Real.exp a * (μ ^ 2 / (2 * (C' + 1)))) = μ ^ 2 * Real.exp a := by
      field_simp
    linarith
  have h2 : K₁ + μ ^ 2 ≤ μ ^ 2 * Real.exp a := by
    have := mul_le_mul_of_nonneg_left hexp hμ2.le
    have e : μ ^ 2 * (K₁ / μ ^ 2 + 1) = K₁ + μ ^ 2 := by
      field_simp
    linarith
  rw [hcross] at hlow
  rw [hK₁] at h2
  nlinarith [hlow, harch.1, hwin', hcosh, hC1, h1, h2, hrem, hμ2, hC'0]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
