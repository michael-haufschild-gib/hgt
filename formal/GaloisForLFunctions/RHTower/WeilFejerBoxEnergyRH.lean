import GaloisForLFunctions.RHTower.CompletedErrorPrimitiveOneSidedLandau
import GaloisForLFunctions.RHTower.CCMLogarithmicWeilFormTransport

/-!
# Weil energy of the box: one test per aperture decides RH

The Fejér triangle `Δ_U(h) = (U − |h|)₊` is the autocorrelation of the box `1_{[−U/2, U/2]}`.
Its literal finite-aperture Weil functional at aperture `U/2` (`ccmRestrictedWeilFull`) is

  `Ψ_{U/2}(Δ_U) = 2 P(U) − (log 4π + γ) U − A(U)`,

where `P(U) = ∫_0^U E` is the primitive of the completed critical-Mellin error and
`A(U) = ∫_0^U (2e^{h/2}(U − h) − 2U)/(e^h − e^{−h}) dh` (`ccmRestrictedPolarPrimeFull_fejerTriangle`,
`ccmRestrictedArchimedeanFull_fejerTriangle`).
* The pole part `16(cosh(U/2) − 1)` and the prime part `2Σ_{k ≤ e^U} Λ(k)k^{−1/2}(U − log k)` combine
  exactly into `2P(U)`.
* The archimedean integrand is at least `−1`, so `A(U) ≥ −U`.

**Theorem** (`riemannHypothesis_of_fejerBoxWeil_ge`).  If the box energies are eventually bounded
below linearly, `Re Ψ_{U/2}(Δ_U) ≥ −C(1+U)` for all `U ≥ U₀`, then RH holds; in particular eventual
nonnegativity suffices (`riemannHypothesis_of_fejerBoxWeil_nonneg`).  Likewise an eventual linear
upper bound `Re Ψ_{U/2}(Δ_U) ≤ C(1+U)` forces RH (`riemannHypothesis_of_fejerBoxWeil_le`); the
archimedean integrand lies between `−1` and `2U e^{−h/2}`.  Sampling at `U = log n` suffices
(`riemannHypothesis_of_fejerBoxWeil_log_ge`), and in elementary form
`Σ_{k ≤ n} Λ(k) k^{−1/2} log(n/k) ≤ 4√n + C(1 + log n)` for all large `n` forces RH
(`riemannHypothesis_of_weightedLogRiesz_le`).  Either bound gives a one-sided linear
bound on `P`, which forces RH by Landau's theorem
(`riemannHypothesis_of_completedErrorPrimitive_eventually_ge`, `..._le`).

The literal functional `Ψ_a` differs from the global Weil functional by
`H(0)∫_{2a}^∞ dh/sinh h` (`ccmArchimedeanWeilSharpDistribution_eq_restricted_add_tail`), here
`U∫_U^∞ dh/sinh h = O(Ue^{−U})`.  Under RH the global functional of `Δ_U` is
`Σ_γ 4 sin²(γU/2)/γ² ≥ 0`, so the slack form of the hypothesis is the one RH supplies.

So the all-aperture ground-energy sign of the restricted Weil form is decided by the energy of a
single explicit vector per aperture, the flat box.
-/

open Complex Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Fejér triangle `(U − |h|)₊`, the autocorrelation of the box `1_{[−U/2, U/2]}`. -/
def fejerTriangle (U h : ℝ) : ℂ := ((max (U - |h|) 0 : ℝ) : ℂ)

theorem fejerTriangle_add_neg {U h : ℝ} (h0 : 0 ≤ h) (hU : h ≤ U) :
    fejerTriangle U h + fejerTriangle U (-h) = ((2 * (U - h) : ℝ) : ℂ) := by
  simp only [fejerTriangle, abs_neg, abs_of_nonneg h0, max_eq_left (sub_nonneg.mpr hU)]
  push_cast
  ring

/-! ## The prime mass as a sum of steps -/

/-- The weighted von Mangoldt atoms `w_k = k^{−1/2} Λ(k)`; they vanish at `k = 0, 1`. -/
theorem criticalMellinAtomWeight_zero : criticalMellinAtomWeight 0 = 0 := by
  simp [criticalMellinAtomWeight]

theorem criticalMellinAtomWeight_one : criticalMellinAtomWeight 1 = 0 := by
  simp [criticalMellinAtomWeight]

/-- On `0 ≤ h ≤ U` the prime mass is a sum of steps over `k ≤ e^U`. -/
theorem criticalMellinPrimeMass_eq_sum_ite {U h : ℝ} (hhU : h ≤ U) :
    criticalMellinPrimeMass h = ∑ k ∈ Finset.Icc 0 ⌊Real.exp U⌋₊,
      if (k : ℝ) ≤ Real.exp h then criticalMellinAtomWeight k else 0 := by
  rw [criticalMellinPrimeMass, ← Finset.sum_filter]
  have hsub : Finset.Icc 0 ⌊Real.exp h⌋₊ =
      (Finset.Icc 0 ⌊Real.exp U⌋₊).filter (fun k : ℕ => (k : ℝ) ≤ Real.exp h) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter, zero_le, true_and]
    rw [Nat.le_floor_iff (Real.exp_pos h).le, Nat.le_floor_iff (Real.exp_pos U).le]
    constructor
    · intro hk; exact ⟨hk.trans (Real.exp_le_exp.mpr hhU), hk⟩
    · intro hk; exact hk.2
  rw [hsub]
  rfl

/-- `∫_0^U 1_{a ≤ h} c dh = c (U − a)` for `0 ≤ a ≤ U`. -/
theorem integral_step {a U c : ℝ} (ha : 0 ≤ a) (haU : a ≤ U) :
    ∫ h in (0 : ℝ)..U, (if a ≤ h then c else 0) = c * (U - a) := by
  have hmono : ∀ c' : ℝ, 0 ≤ c' → Monotone fun h : ℝ => if a ≤ h then c' else 0 := by
    intro c' hc' x y hxy
    dsimp only
    by_cases hx : a ≤ x
    · rw [if_pos hx, if_pos (hx.trans hxy)]
    · rw [if_neg hx]; split_ifs <;> linarith
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun h : ℝ => if a ≤ h then c else 0) volume x y := by
    intro x y
    rcases le_total 0 c with hc | hc
    · exact (hmono c hc).intervalIntegrable
    · have h' : (fun h : ℝ => if a ≤ h then c else 0) =
          fun h => -(if a ≤ h then -c else 0) := by
        funext h; split_ifs <;> ring
      rw [h']
      exact ((hmono (-c) (by linarith)).intervalIntegrable).neg
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a U)]
  have h1 : ∫ h in (0 : ℝ)..a, (if a ≤ h then c else 0) = 0 := by
    have : ∫ h in (0 : ℝ)..a, (if a ≤ h then c else 0) = ∫ h in (0 : ℝ)..a, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume a] with h hne hmem
      rw [uIoc_of_le ha] at hmem
      rw [if_neg (not_le.mpr (lt_of_le_of_ne hmem.2 hne))]
    rw [this, intervalIntegral.integral_zero]
  have h2 : ∫ h in a..U, (if a ≤ h then c else 0) = c * (U - a) := by
    have : ∫ h in a..U, (if a ≤ h then c else 0) = ∫ h in a..U, c := by
      apply intervalIntegral.integral_congr
      intro h hmem
      rw [uIcc_of_le haU] at hmem
      simp only [if_pos hmem.1]
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h1, h2, zero_add]

/-- `∫_0^U Σ_{k ≤ e^h} w_k dh = Σ_{k ≤ e^U} w_k (U − log k)`. -/
theorem integral_criticalMellinPrimeMass {U : ℝ} (hU : 0 ≤ U) :
    ∫ h in (0 : ℝ)..U, criticalMellinPrimeMass h =
      ∑ k ∈ Finset.Icc 0 ⌊Real.exp U⌋₊, criticalMellinAtomWeight k * (U - Real.log k) := by
  have hcongr : ∫ h in (0 : ℝ)..U, criticalMellinPrimeMass h =
      ∫ h in (0 : ℝ)..U, ∑ k ∈ Finset.Icc 0 ⌊Real.exp U⌋₊,
        (if (k : ℝ) ≤ Real.exp h then criticalMellinAtomWeight k else 0) := by
    apply intervalIntegral.integral_congr
    intro h hmem
    rw [uIcc_of_le hU] at hmem
    exact criticalMellinPrimeMass_eq_sum_ite hmem.2
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [criticalMellinAtomWeight_zero]
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have hkpos : (0 : ℝ) < k := by linarith
      have hkU : (k : ℝ) ≤ Real.exp U := by
        have := (Finset.mem_Icc.mp hk).2
        exact (Nat.le_floor_iff (Real.exp_pos U).le).mp this
      have hiff : ∀ h : ℝ, ((k : ℝ) ≤ Real.exp h ↔ Real.log k ≤ h) := fun h =>
        (Real.log_le_iff_le_exp hkpos).symm
      have hfun : (fun h : ℝ => if (k : ℝ) ≤ Real.exp h then criticalMellinAtomWeight k else 0) =
          fun h => if Real.log k ≤ h then criticalMellinAtomWeight k else 0 := by
        funext h
        simp only [hiff h]
      rw [hfun, integral_step (Real.log_nonneg hk1)
        ((Real.log_le_log hkpos hkU).trans (by rw [Real.log_exp]))]
  · intro k _
    have hmono : Monotone fun h : ℝ =>
        if (k : ℝ) ≤ Real.exp h then criticalMellinAtomWeight k else 0 := by
      intro x y hxy
      dsimp only
      by_cases hx : (k : ℝ) ≤ Real.exp x
      · rw [if_pos hx, if_pos (hx.trans (Real.exp_le_exp.mpr hxy))]
      · rw [if_neg hx]; split_ifs
        · exact criticalMellinAtomWeight_nonneg k
        · exact le_rfl
    exact hmono.intervalIntegrable

/-- `∫_0^U 4 sinh(h/2) dh = 8(cosh(U/2) − 1)`. -/
theorem integral_four_sinh_half (U : ℝ) :
    ∫ h in (0 : ℝ)..U, 4 * Real.sinh (h / 2) = 8 * (Real.cosh (U / 2) - 1) := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) U,
      HasDerivAt (fun h : ℝ => 8 * Real.cosh (h / 2)) (4 * Real.sinh (x / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun h : ℝ => h / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
    have h2 := ((Real.hasDerivAt_cosh (x / 2)).comp x h1).const_mul 8
    exact h2.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun h : ℝ => 4 * Real.sinh (h / 2)).intervalIntegrable 0 U)]
  simp only [zero_div, Real.cosh_zero]
  ring

/-- The primitive of the completed error: `P(U) = 8(cosh(U/2) − 1) − Σ_{k ≤ e^U} w_k (U − log k)`. -/
theorem completedErrorPrimitive_eq {U : ℝ} (hU : 0 ≤ U) :
    completedErrorPrimitive U = 8 * (Real.cosh (U / 2) - 1) -
      ∑ k ∈ Finset.Icc 0 ⌊Real.exp U⌋₊, criticalMellinAtomWeight k * (U - Real.log k) := by
  unfold completedErrorPrimitive
  have h : (fun t => criticalMellinCompletedError t) =
      fun t => 4 * Real.sinh (t / 2) - criticalMellinPrimeMass t :=
    funext criticalMellinCompletedError_eq_polar_sub_primeMass
  rw [h, intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun h : ℝ => 4 * Real.sinh (h / 2)).intervalIntegrable 0 U)
    criticalMellinPrimeMass_mono.intervalIntegrable,
    integral_four_sinh_half, integral_criticalMellinPrimeMass hU]

/-! ## The polar and prime part of the box energy -/

/-- `∫_0^U 4(U − h) cosh(h/2) dh = 16(cosh(U/2) − 1)`. -/
theorem integral_fejer_cosh (U : ℝ) :
    ∫ h in (0 : ℝ)..U, 4 * (U - h) * Real.cosh (h / 2) = 16 * (Real.cosh (U / 2) - 1) := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) U,
      HasDerivAt (fun h : ℝ => 8 * (U - h) * Real.sinh (h / 2) + 16 * Real.cosh (h / 2))
        (4 * (U - x) * Real.cosh (x / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun h : ℝ => h / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
    have hs := (Real.hasDerivAt_sinh (x / 2)).comp x h1
    have hc := (Real.hasDerivAt_cosh (x / 2)).comp x h1
    have hl : HasDerivAt (fun h : ℝ => 8 * (U - h)) (-8) x := by
      simpa using ((hasDerivAt_const x U).sub (hasDerivAt_id x)).const_mul 8
    have := (hl.mul hs).add (hc.const_mul 16)
    exact this.congr_deriv (by simp only [Function.comp_apply]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun h : ℝ => 4 * (U - h) * Real.cosh (h / 2)).intervalIntegrable
      0 U)]
  simp only [zero_div, Real.cosh_zero, Real.sinh_zero, sub_self, sub_zero, mul_zero, zero_mul]
  ring

/-- **The polar and prime part of the box energy is twice the error primitive.** -/
theorem ccmRestrictedPolarPrimeFull_fejerTriangle {U : ℝ} (hU : 0 ≤ U) :
    ccmRestrictedPolarPrimeFull (U / 2) (fejerTriangle U) =
      ((2 * completedErrorPrimitive U : ℝ) : ℂ) := by
  unfold ccmRestrictedPolarPrimeFull
  rw [show 2 * (U / 2) = U by ring]
  have hpole : ∫ h in Ioc (0 : ℝ) U,
      (fejerTriangle U h + fejerTriangle U (-h)) * (2 * Real.cosh (h / 2) : ℂ) =
        ((16 * (Real.cosh (U / 2) - 1) : ℝ) : ℂ) := by
    have hcongr : ∀ h ∈ Ioc (0 : ℝ) U,
        (fejerTriangle U h + fejerTriangle U (-h)) * (2 * Real.cosh (h / 2) : ℂ) =
          ((4 * (U - h) * Real.cosh (h / 2) : ℝ) : ℂ) := by
      intro h hh
      rw [fejerTriangle_add_neg hh.1.le hh.2]
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_complex_ofReal,
      ← intervalIntegral.integral_of_le hU, integral_fejer_cosh]
  have hprime : ∑ k ∈ Finset.Icc 2 ⌊Real.exp U⌋₊,
      (criticalMellinAtomWeight k : ℂ) *
        (fejerTriangle U (Real.log k) + fejerTriangle U (-Real.log k)) =
      ((2 * ∑ k ∈ Finset.Icc 0 ⌊Real.exp U⌋₊,
        criticalMellinAtomWeight k * (U - Real.log k) : ℝ) : ℂ) := by
    have hsub : ∑ k ∈ Finset.Icc 2 ⌊Real.exp U⌋₊,
          criticalMellinAtomWeight k * (U - Real.log k) =
        ∑ k ∈ Finset.Icc 0 ⌊Real.exp U⌋₊, criticalMellinAtomWeight k * (U - Real.log k) := by
      refine Finset.sum_subset (Finset.Icc_subset_Icc (Nat.zero_le 2) le_rfl) fun k hk hk2 => ?_
      have hk1 : k ≤ 1 := by
        simp only [Finset.mem_Icc, not_and, not_le] at hk hk2
        have := hk2
        omega
      interval_cases k
      · simp [criticalMellinAtomWeight_zero]
      · simp [criticalMellinAtomWeight_one]
    rw [← hsub]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by linarith
    have hkU : (k : ℝ) ≤ Real.exp U :=
      (Nat.le_floor_iff (Real.exp_pos U).le).mp (Finset.mem_Icc.mp hk).2
    have hlog0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
    have hlogU : Real.log k ≤ U := (Real.log_le_log hkpos hkU).trans (by rw [Real.log_exp])
    rw [fejerTriangle_add_neg hlog0 hlogU]
    push_cast
    ring
  rw [hpole, hprime, completedErrorPrimitive_eq hU]
  push_cast
  ring

/-! ## The archimedean part -/

/-- The archimedean integrand of the box energy is at least `−1`. -/
theorem fejer_archimedean_integrand_ge {U h : ℝ} (h0 : 0 < h) (hU : h ≤ U) :
    -1 ≤ (Real.exp (h / 2) * (2 * (U - h)) - 2 * U) / (Real.exp h - Real.exp (-h)) := by
  have hsinh : 2 * h ≤ Real.exp h - Real.exp (-h) := by
    have := Real.self_le_sinh_iff.mpr h0.le
    rw [Real.sinh_eq] at this
    linarith
  have hden : 0 < Real.exp h - Real.exp (-h) := by linarith
  rw [le_div_iff₀ hden]
  have he : 1 ≤ Real.exp (h / 2) := Real.one_le_exp (by linarith)
  have hnum : 2 * (U - h) ≤ Real.exp (h / 2) * (2 * (U - h)) :=
    le_mul_of_one_le_left (by linarith) he
  linarith

/-- **The real part of the archimedean box energy is at least `(log 4π + γ − 1) U`.** -/
theorem ccmRestrictedArchimedeanFull_fejerTriangle_re_ge {U : ℝ} (hU : 0 ≤ U) :
    (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant - 1) * U ≤
      (ccmRestrictedArchimedeanFull (U / 2) (fejerTriangle U)).re := by
  unfold ccmRestrictedArchimedeanFull
  rw [show 2 * (U / 2) = U by ring]
  set g : ℝ → ℝ := fun h =>
    (Real.exp (h / 2) * (2 * (U - h)) - 2 * U) / (Real.exp h - Real.exp (-h)) with hg
  have hcongr : ∀ h ∈ Ioc (0 : ℝ) U,
      ((Real.exp (h / 2) : ℂ) * (fejerTriangle U h + fejerTriangle U (-h)) -
          2 * fejerTriangle U 0) / (Real.exp h - Real.exp (-h) : ℝ) = ((g h : ℝ) : ℂ) := by
    intro h hh
    rw [fejerTriangle_add_neg hh.1.le hh.2]
    simp only [fejerTriangle, abs_zero, sub_zero, max_eq_left hU, hg]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_complex_ofReal]
  have h00 : fejerTriangle U 0 = (U : ℂ) := by simp [fejerTriangle, max_eq_left hU]
  rw [h00]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hint : -U ≤ ∫ h in Ioc (0 : ℝ) U, g h := by
    by_cases hi : IntegrableOn g (Ioc 0 U)
    · have hmono : ∫ h in Ioc (0 : ℝ) U, (-1 : ℝ) ≤ ∫ h in Ioc (0 : ℝ) U, g h :=
        setIntegral_mono_on (integrableOn_const (by simp)) hi measurableSet_Ioc
          fun h hh => fejer_archimedean_integrand_ge hh.1 hh.2
      have hc : ∫ h in Ioc (0 : ℝ) U, (-1 : ℝ) = -U := by
        rw [setIntegral_const]
        simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hU]
      linarith
    · rw [integral_undef hi]
      linarith
  simp only [zero_mul, sub_zero]
  linarith

/-- **A box test decides RH.**  If the literal Weil functional of the Fejér triangle `(U − |h|)₊`
at aperture `U/2` is eventually bounded below linearly, `Re Ψ_{U/2}(Δ_U) ≥ −C(1 + U)`, the Riemann
hypothesis holds.  The linear slack absorbs the difference `U ∫_U^∞ dh/sinh h` between the literal
functional and the global Weil functional, which is the one that is nonnegative under RH. -/
theorem riemannHypothesis_of_fejerBoxWeil_ge {U₀ C : ℝ}
    (h : ∀ U : ℝ, U₀ ≤ U → -(C * (1 + U)) ≤ (ccmRestrictedWeilFull (U / 2) (fejerTriangle U)).re) :
    RiemannHypothesis := by
  set c := Real.log (4 * Real.pi) + Real.eulerMascheroniConstant - 1 with hc
  refine riemannHypothesis_of_completedErrorPrimitive_eventually_ge
    (C := (|C| + |c|) / 2) (L := max U₀ 0) fun T hT => ?_
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  have hpos := h T (le_trans (le_max_left _ _) hT)
  rw [ccmRestrictedWeilFull, Complex.sub_re, ccmRestrictedPolarPrimeFull_fejerTriangle hT0,
    Complex.ofReal_re] at hpos
  have harch := ccmRestrictedArchimedeanFull_fejerTriangle_re_ge hT0
  have h1 : C * (1 + T) ≤ |C| * (1 + T) := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have hcT : -(|c| * (1 + T)) ≤ c * T := by
    have h2 : -(|c| * T) ≤ c * T := by nlinarith [neg_abs_le c]
    have h3 : |c| * T ≤ |c| * (1 + T) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    linarith
  nlinarith

/-- The case without slack: eventually nonnegative box energies force RH. -/
theorem riemannHypothesis_of_fejerBoxWeil_nonneg {U₀ : ℝ}
    (h : ∀ U : ℝ, U₀ ≤ U → 0 ≤ (ccmRestrictedWeilFull (U / 2) (fejerTriangle U)).re) :
    RiemannHypothesis :=
  riemannHypothesis_of_fejerBoxWeil_ge (U₀ := U₀) (C := 0) fun U hU => by
    simpa using h U hU

/-- The archimedean integrand of the box energy is at most `2U e^{−h/2}`, from
`e^{h/2} − 1 ≤ 2 e^{−h/2} sinh h`. -/
theorem fejer_archimedean_integrand_le {U h : ℝ} (h0 : 0 < h) (hU : h ≤ U) :
    (Real.exp (h / 2) * (2 * (U - h)) - 2 * U) / (Real.exp h - Real.exp (-h)) ≤
      2 * U * Real.exp (-(h / 2)) := by
  have hsinh : 2 * h ≤ Real.exp h - Real.exp (-h) := by
    have := Real.self_le_sinh_iff.mpr h0.le
    rw [Real.sinh_eq] at this
    linarith
  have hden : 0 < Real.exp h - Real.exp (-h) := by linarith
  rw [div_le_iff₀ hden]
  have hU0 : 0 ≤ U := by linarith
  have he : 0 < Real.exp (h / 2) := Real.exp_pos _
  have hkey : Real.exp (h / 2) - 1 ≤ Real.exp (-(h / 2)) * (Real.exp h - Real.exp (-h)) := by
    have e1 : Real.exp (-(h / 2)) * Real.exp h = Real.exp (h / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(h / 2)) * Real.exp (-h) = Real.exp (-(3 * h / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-(3 * h / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [mul_sub, e1, e2]
    linarith
  have hnum : Real.exp (h / 2) * (2 * (U - h)) - 2 * U ≤ 2 * U * (Real.exp (h / 2) - 1) := by
    nlinarith
  calc Real.exp (h / 2) * (2 * (U - h)) - 2 * U ≤ 2 * U * (Real.exp (h / 2) - 1) := hnum
    _ ≤ 2 * U * (Real.exp (-(h / 2)) * (Real.exp h - Real.exp (-h))) :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
    _ = 2 * U * Real.exp (-(h / 2)) * (Real.exp h - Real.exp (-h)) := by ring

/-- **The real part of the archimedean box energy is at most `(log 4π + γ + 4) U`.** -/
theorem ccmRestrictedArchimedeanFull_fejerTriangle_re_le {U : ℝ} (hU : 0 ≤ U) :
    (ccmRestrictedArchimedeanFull (U / 2) (fejerTriangle U)).re ≤
      (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + 4) * U := by
  unfold ccmRestrictedArchimedeanFull
  rw [show 2 * (U / 2) = U by ring]
  set g : ℝ → ℝ := fun h =>
    (Real.exp (h / 2) * (2 * (U - h)) - 2 * U) / (Real.exp h - Real.exp (-h)) with hg
  have hcongr : ∀ h ∈ Ioc (0 : ℝ) U,
      ((Real.exp (h / 2) : ℂ) * (fejerTriangle U h + fejerTriangle U (-h)) -
          2 * fejerTriangle U 0) / (Real.exp h - Real.exp (-h) : ℝ) = ((g h : ℝ) : ℂ) := by
    intro h hh
    rw [fejerTriangle_add_neg hh.1.le hh.2]
    simp only [fejerTriangle, abs_zero, sub_zero, max_eq_left hU, hg]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_complex_ofReal]
  have h00 : fejerTriangle U 0 = (U : ℂ) := by simp [fejerTriangle, max_eq_left hU]
  rw [h00]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hint : ∫ h in Ioc (0 : ℝ) U, g h ≤ 4 * U := by
    by_cases hi : IntegrableOn g (Ioc 0 U)
    · have hmaj : IntegrableOn (fun h : ℝ => 2 * U * Real.exp (-(h / 2))) (Ioc 0 U) :=
        (by fun_prop : Continuous fun h : ℝ => 2 * U * Real.exp (-(h / 2))).integrableOn_Ioc
      have hmono : ∫ h in Ioc (0 : ℝ) U, g h ≤ ∫ h in Ioc (0 : ℝ) U, 2 * U * Real.exp (-(h / 2)) :=
        setIntegral_mono_on hi hmaj measurableSet_Ioc
          fun h hh => fejer_archimedean_integrand_le hh.1 hh.2
      have hval : ∫ h in Ioc (0 : ℝ) U, 2 * U * Real.exp (-(h / 2)) =
          4 * U * (1 - Real.exp (-(U / 2))) := by
        rw [← intervalIntegral.integral_of_le hU, intervalIntegral.integral_const_mul]
        have hd : ∀ x ∈ uIcc (0 : ℝ) U,
            HasDerivAt (fun h : ℝ => -2 * Real.exp (-(h / 2))) (Real.exp (-(x / 2))) x := by
          intro x _
          have h1 : HasDerivAt (fun h : ℝ => -(h / 2)) (-(1 / 2)) x :=
            ((hasDerivAt_id x).div_const 2).neg
          have := (h1.exp).const_mul (-2)
          exact this.congr_deriv (by ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          ((by fun_prop : Continuous fun h : ℝ => Real.exp (-(h / 2))).intervalIntegrable 0 U)]
        simp only [zero_div, neg_zero, Real.exp_zero]
        ring
      have hpos : 0 ≤ 4 * U * Real.exp (-(U / 2)) := by positivity
      linarith
    · rw [integral_undef hi]
      linarith
  simp only [zero_mul, sub_zero]
  linarith

/-- **An upper box bound also decides RH.**  If `Re Ψ_{U/2}(Δ_U) ≤ C(1 + U)` for all `U ≥ U₀`,
the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_fejerBoxWeil_le {U₀ C : ℝ}
    (h : ∀ U : ℝ, U₀ ≤ U → (ccmRestrictedWeilFull (U / 2) (fejerTriangle U)).re ≤ C * (1 + U)) :
    RiemannHypothesis := by
  set c := Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + 4 with hc
  refine riemannHypothesis_of_completedErrorPrimitive_eventually_le
    (C := (|C| + |c|) / 2) (L := max U₀ 0) fun T hT => ?_
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  have hle := h T (le_trans (le_max_left _ _) hT)
  rw [ccmRestrictedWeilFull, Complex.sub_re, ccmRestrictedPolarPrimeFull_fejerTriangle hT0,
    Complex.ofReal_re] at hle
  have harch := ccmRestrictedArchimedeanFull_fejerTriangle_re_le hT0
  have h1 : C * (1 + T) ≤ |C| * (1 + T) := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have h2 : c * T ≤ |c| * (1 + T) :=
    (mul_le_mul_of_nonneg_right (le_abs_self c) hT0).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c))
  nlinarith

/-! ## Sampling at `log n` -/

/-- Between consecutive logarithms the primitive moves by at most `46`. -/
theorem completedErrorPrimitive_sub_le_of_log {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (h1 : Real.log n ≤ T) (h2 : T ≤ Real.log (n + 1)) :
    |completedErrorPrimitive T - completedErrorPrimitive (Real.log n)| ≤ 46 := by
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hsub : completedErrorPrimitive T - completedErrorPrimitive (Real.log n) =
      ∫ t in Real.log n..T, criticalMellinCompletedError t := by
    unfold completedErrorPrimitive
    rw [intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_criticalMellinCompletedError_any 0 T)
      (intervalIntegrable_criticalMellinCompletedError_any 0 (Real.log n))]
  rw [hsub]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := Real.log n) (b := T)
    (f := criticalMellinCompletedError) (C := 23 * Real.exp (T / 2)) (fun t ht => by
      rw [uIoc_of_le h1] at ht
      rw [Real.norm_eq_abs]
      refine (abs_criticalMellinCompletedError_le_sqrt (hlog0.trans ht.1.le)).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.2])) (by norm_num))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T - Real.log n)] at hb
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hgap : T - Real.log n ≤ 1 / n := by
    have hl : Real.log (n + 1) - Real.log n = Real.log (1 + 1 / n) := by
      rw [← Real.log_div (by positivity) hnpos.ne']
      congr 1
      field_simp
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (n : ℝ) by positivity)
    linarith
  have hexp : Real.exp (T / 2) ≤ Real.sqrt (n + 1) := by
    rw [show Real.sqrt (n + 1) = Real.exp (Real.log (n + 1) / 2) by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
      ring_nf]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.sqrt (n + 1) ≤ 2 * n := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  refine hb.trans ?_
  calc 23 * Real.exp (T / 2) * (T - Real.log n)
      ≤ 23 * (2 * n) * (1 / n) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (hexp.trans hsq) (by norm_num)) hgap
          (by linarith) (by positivity)
    _ = 46 := by field_simp; ring

/-- **Boxes of length `log n` decide RH.**  If `Re Ψ_{(log n)/2}(Δ_{log n}) ≥ −C(1 + log n)` for all
`n ≥ n₀`, the Riemann hypothesis holds: between consecutive logarithms the primitive `P` moves by
at most `46`. -/
theorem riemannHypothesis_of_fejerBoxWeil_log_ge {n₀ : ℕ} {C : ℝ}
    (h : ∀ n : ℕ, n₀ ≤ n → -(C * (1 + Real.log n)) ≤
      (ccmRestrictedWeilFull (Real.log n / 2) (fejerTriangle (Real.log n))).re) :
    RiemannHypothesis := by
  set c := Real.log (4 * Real.pi) + Real.eulerMascheroniConstant - 1 with hc
  refine riemannHypothesis_of_completedErrorPrimitive_eventually_ge
    (C := (|C| + |c|) / 2 + 46) (L := Real.log (max n₀ 1)) fun T hT => ?_
  set n : ℕ := ⌊Real.exp T⌋₊ with hn
  have hmax : (1 : ℝ) ≤ max (n₀ : ℝ) 1 := le_max_right _ _
  have hT0 : 0 ≤ T := le_trans (Real.log_nonneg hmax) hT
  have hexpT : max (n₀ : ℝ) 1 ≤ Real.exp T := by
    have := Real.exp_le_exp.mpr hT
    rwa [Real.exp_log (by positivity)] at this
  have hn1 : 1 ≤ n := by
    rw [hn, Nat.one_le_floor_iff]
    exact le_trans hmax hexpT
  have hn0 : n₀ ≤ n := by
    rw [hn, Nat.le_floor_iff (Real.exp_pos T).le]
    exact le_trans (le_max_left _ _) hexpT
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlo : Real.log n ≤ T := by
    rw [Real.log_le_iff_le_exp hnpos]
    exact Nat.floor_le (Real.exp_pos T).le
  have hhi : T ≤ Real.log (n + 1) := by
    rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
    exact (Nat.lt_floor_add_one (Real.exp T)).le
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hpos := h n hn0
  rw [ccmRestrictedWeilFull, Complex.sub_re, ccmRestrictedPolarPrimeFull_fejerTriangle hlog0,
    Complex.ofReal_re] at hpos
  have harch := ccmRestrictedArchimedeanFull_fejerTriangle_re_ge hlog0
  have hmove := (abs_le.mp (completedErrorPrimitive_sub_le_of_log hn1 hlo hhi)).1
  have h1 : C * (1 + Real.log n) ≤ |C| * (1 + T) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C))
  have hcT : -(|c| * (1 + T)) ≤ c * Real.log n := by
    have h2 : -(|c| * Real.log n) ≤ c * Real.log n := by nlinarith [neg_abs_le c]
    have h3 : |c| * Real.log n ≤ |c| * (1 + T) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    linarith
  nlinarith

/-! ## The arithmetic form -/

/-- At `U = log n` the primitive is `4√n + 4/√n − 8 − Σ_{k ≤ n} Λ(k) k^{−1/2} log(n/k)`. -/
theorem completedErrorPrimitive_log_eq {n : ℕ} (hn : 1 ≤ n) :
    completedErrorPrimitive (Real.log n) = 4 * Real.sqrt n + 4 / Real.sqrt n - 8 -
      ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k / Real.sqrt k * Real.log (n / k) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [completedErrorPrimitive_eq (Real.log_nonneg (by exact_mod_cast hn)),
    Real.exp_log hnpos, Nat.floor_natCast]
  have hcosh : 8 * (Real.cosh (Real.log n / 2) - 1) = 4 * Real.sqrt n + 4 / Real.sqrt n - 8 := by
    rw [Real.cosh_eq, show Real.log n / 2 = Real.log (Real.sqrt n) by
      rw [Real.log_sqrt hnpos.le], Real.exp_log (Real.sqrt_pos.mpr hnpos), Real.exp_neg,
      Real.exp_log (Real.sqrt_pos.mpr hnpos)]
    field_simp
    ring
  have hsum : ∑ k ∈ Finset.Icc 0 n, criticalMellinAtomWeight k * (Real.log n - Real.log k) =
      ∑ k ∈ Finset.Icc 1 n,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k * Real.log (n / k) := by
    have hsub : ∑ k ∈ Finset.Icc 1 n, criticalMellinAtomWeight k * (Real.log n - Real.log k) =
        ∑ k ∈ Finset.Icc 0 n, criticalMellinAtomWeight k * (Real.log n - Real.log k) := by
      refine Finset.sum_subset (Finset.Icc_subset_Icc (Nat.zero_le 1) le_rfl) fun k hk hk1 => ?_
      have : k = 0 := by
        simp only [Finset.mem_Icc, not_and, not_le] at hk hk1
        omega
      subst this
      simp [criticalMellinAtomWeight_zero]
    rw [← hsub]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by linarith
    have hr : (k : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt k)⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hkpos.le, ← Real.sqrt_eq_rpow]
    rw [criticalMellinAtomWeight, Real.log_div hnpos.ne' hkpos.ne', hr, div_eq_mul_inv]
    ring
  rw [hcosh, hsum]

/-- **An elementary form of the criterion.**  If
`Σ_{k ≤ n} Λ(k) k^{−1/2} log(n/k) ≤ 4√n + C(1 + log n)` for all `n ≥ n₀`, the Riemann hypothesis
holds. -/
theorem riemannHypothesis_of_weightedLogRiesz_le {n₀ : ℕ} {C : ℝ}
    (h : ∀ n : ℕ, n₀ ≤ n →
      ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k / Real.sqrt k * Real.log (n / k) ≤
        4 * Real.sqrt n + C * (1 + Real.log n)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_completedErrorPrimitive_eventually_ge
    (C := |C| + 54) (L := Real.log (max (n₀ : ℝ) 1)) fun T hT => ?_
  set n : ℕ := ⌊Real.exp T⌋₊ with hn
  have hmax : (1 : ℝ) ≤ max (n₀ : ℝ) 1 := le_max_right _ _
  have hT0 : 0 ≤ T := le_trans (Real.log_nonneg hmax) hT
  have hexpT : max (n₀ : ℝ) 1 ≤ Real.exp T := by
    have := Real.exp_le_exp.mpr hT
    rwa [Real.exp_log (by positivity)] at this
  have hn1 : 1 ≤ n := by
    rw [hn, Nat.one_le_floor_iff]
    exact le_trans hmax hexpT
  have hn0 : n₀ ≤ n := by
    rw [hn, Nat.le_floor_iff (Real.exp_pos T).le]
    exact le_trans (le_max_left _ _) hexpT
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlo : Real.log n ≤ T := by
    rw [Real.log_le_iff_le_exp hnpos]
    exact Nat.floor_le (Real.exp_pos T).le
  have hhi : T ≤ Real.log (n + 1) := by
    rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
    exact (Nat.lt_floor_add_one (Real.exp T)).le
  have hP := completedErrorPrimitive_log_eq hn1
  have hb := h n hn0
  have hmove := (abs_le.mp (completedErrorPrimitive_sub_le_of_log hn1 hlo hhi)).1
  have hsq : 0 ≤ 4 / Real.sqrt n := by positivity
  have hC : C * (1 + Real.log n) ≤ |C| * (1 + T) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn1)])).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C))
  nlinarith

end

end RHTower
