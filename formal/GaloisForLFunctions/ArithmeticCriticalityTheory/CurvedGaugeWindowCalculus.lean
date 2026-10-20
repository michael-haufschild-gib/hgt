import GaloisForLFunctions.ArithmeticCriticalityTheory.MarkovWindowPastPlasticThreshold

/-!
# The curved-gauge window calculus

For a gauge `M ∈ C²_c` with `0 ≤ M ≤ 1`, vanishing outside `(−R, R)`, and a profile `u ∈ C²_c`, the test
`F = M u` has the ground-state representation with the pole as a mass potential and a negative jump
density (`fullZeroForm_mul_eq_gauge_window`, `2R < log 2`):

    Ẑ(M u) = ∫_0^∞ ω(t) I(t) dt − 2 ∫_0^∞ cosh(t/2) I(t) dt
              + ∫ u² M (−𝒲M) + 2 ∫ u(x)² M(x) ∫ M(y) cosh((x−y)/2) dy dx,
    I(t) = ∫ M(x) M(x+t) (u(x) − u(x+t))² dx.

A plateau gauge, `M = 1` on the support of the test, is the case `u = F` of the Markov window. A curved
gauge moves the potential by the regional jump term of `M`, the part of the archimedean energy that
the flat gauge discards. Where the density `ω − 2cosh(t/2)` is negative its contribution is bounded by
a potential (`integral_mul_gaugeJumpProfile_le`): for every continuous `κ ≥ 0`,

    ∫_0^∞ κ(t) I(t) dt ≤ 2 ∫ u(x)² M(x) (∫_0^∞ κ(t) (M(x+t) + M(x−t)) dt) dx.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The Markov energy of a curved-gauge test -/

/-- **The Markov energy in a curved window gauge.** For a gauge `M ∈ C²_c`, `0 ≤ M ≤ 1`, vanishing
outside `(−R, R)`, and a profile `u ∈ C²_c`: `Q(M u) = J_M(u) + ∫ u² M (−𝒲M)`. -/
theorem markovEnergy_mul_eq_gauge_window {u M : ℝ → ℝ} {R : ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (hMd : ContDiff ℝ 2 M) (hMcs : HasCompactSupport M)
    (hle : ∀ y, M y ≤ 1) (hnn : ∀ y, 0 ≤ M y) (hzero : ∀ y, R ≤ |y| → M y = 0) :
    markovEnergy (fun x => ((M x * u x : ℝ) : ℂ)) =
      signedJumpEnergy M u + ∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x := by
  obtain ⟨K, -, hK⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hLip : ∀ a b, |M a - M b| ≤ K * |a - b| := fun a b => hK b a
  have hdecay : ∀ k : ℝ, 0 ≤ k → ∀ y, |M y| ≤ Real.exp (k * |R|) * Real.exp (-(k * |y|)) := by
    intro k hk y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith [le_abs_self R]))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hdec8 := hdecay 8 (by norm_num)
  set ω : ℝ → ℝ := fun y => M y / riemannKernelReal y with hωdef
  have hΦω : ∀ y, riemannKernelReal y * ω y = M y := fun y =>
    mul_div_cancel₀ _ (riemannKernelReal_pos y).ne'
  have hω : ContDiff ℝ 2 ω := hMd.div contDiff_riemannKernelReal fun y => (riemannKernelReal_pos y).ne'
  have hP' : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * (M (x + Real.log n) + M (x - Real.log n)) :=
    summable_atom_mul_profileShift hdec8
  have hA' : ∀ x, IntegrableOn (profileArchTerm M x) (Ioi 0) :=
    integrableOn_profileArchTerm hMd.continuous hLip
  have hAgen : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x)
      (Ioi 0) := fun x => by
    refine IntegrableOn.congr_fun ((((integrableOn_symArchTerm x).const_mul (M x)).sub
      ((hA' x).const_mul (riemannKernelReal x))).neg) (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.neg_apply, Pi.sub_apply]
    rw [hωdef, twoSidedShiftGenerator_profileGauge]
    unfold symArchTerm profileArchTerm
    ring
  have hPgen : ∀ x, Summable fun n : ℕ =>
      vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x := fun x => by
    refine (((summable_primeKernelSum x).mul_left (M x)).sub
      ((hP' x).mul_left (riemannKernelReal x))).congr fun n => ?_
    rw [hωdef, twoSidedShiftGenerator_profileGauge]
    ring
  have hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * (fun x => -poleFreeWeilOperator M x) x := fun x => by
    rw [hωdef, twoSidedGenerator_profileGauge_sub_potential (hP' x) (hA' x)]
    ring
  have hg : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hLip hdec8).neg
  have hC12 := markovEnergy_phiDoob_mul_eq_signedJump_add_source (C := Real.exp (24 * |R|)) hω
    (by positivity) (fun y => by rw [hΦω]; exact hdecay 24 (by norm_num) y) hAgen hPgen hsrc hg
    hu huc
  have hFeq : phiDoobTest (fun y => ω y * u y) = fun x => M x * u x := funext fun x => by
    unfold phiDoobTest
    rw [← mul_assoc, hΦω]
  have hMeq : (fun y => riemannKernelReal y * ω y) = M := funext hΦω
  rw [hFeq, hMeq] at hC12
  simp only [hΦω] at hC12
  exact hC12

/-! ### The pole product of a curved-gauge test -/

section PoleProduct

variable {u M : ℝ → ℝ} {B : ℝ} (hu : Continuous u) (hM : Continuous M)
  (hMB : ∀ x, M x ≠ 0 → |x| ≤ B)

include hMB in
theorem mul_ne_zero_bound : ∀ x, M x * u x ≠ 0 → |x| ≤ B := fun x hx =>
  hMB x (left_ne_zero_of_mul hx)

include hu hM hMB in
/-- The autocorrelation of `M u` in its own gauge:
`A(t) = ½ ∫ u(x)² M(x) (M(x+t) + M(x−t)) dx − ½ I(t)`. -/
theorem autoCorr_mul_eq_gauge (t : ℝ) :
    autoCorr (fun x => M x * u x) t =
      (1 / 2) * (∫ x, u x ^ 2 * M x * (M (x + t) + M (x - t))) -
        (1 / 2) * gaugeJumpProfile M u t := by
  have hMc : HasCompactSupport M := hasCompactSupport_of_bound hMB
  have hpt : ∀ x, M x * u x * (M (x + t) * u (x + t)) =
      (1 / 2) * (u x ^ 2 * M x * M (x + t) + u (x + t) ^ 2 * M (x + t) * M x) -
        (1 / 2) * signedShiftJump M u t x := fun x => by
    unfold signedShiftJump
    ring
  have hMt : Continuous fun x => M (x + t) := hM.comp (continuous_id.add continuous_const)
  have hut : Continuous fun x => u (x + t) := hu.comp (continuous_id.add continuous_const)
  have i1 : Integrable fun x => u x ^ 2 * M x * M (x + t) :=
    (((hu.pow 2).mul hM).mul hMt).integrable_of_hasCompactSupport hMc.mul_left.mul_right
  have i2 : Integrable fun x => u (x + t) ^ 2 * M (x + t) * M x :=
    (((hut.pow 2).mul hMt).mul hM).integrable_of_hasCompactSupport hMc.mul_left
  have i3 : Integrable fun x => signedShiftJump M u t x := by
    unfold signedShiftJump
    exact ((hM.mul hMt).mul ((hu.sub hut).pow 2)).integrable_of_hasCompactSupport
      hMc.mul_right.mul_right
  have i4 : Integrable fun x => u x ^ 2 * M x * M (x - t) :=
    (((hu.pow 2).mul hM).mul (hM.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hMc.mul_left.mul_right
  have hshift : (∫ x, u (x + t) ^ 2 * M (x + t) * M x) = ∫ x, u x ^ 2 * M x * M (x - t) := by
    rw [← integral_add_right_eq_self (fun x => u x ^ 2 * M x * M (x - t)) t]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right]
  unfold autoCorr gaugeJumpProfile
  calc (∫ x, M x * u x * (M (x + t) * u (x + t)))
      = ∫ x, ((1 / 2) * (u x ^ 2 * M x * M (x + t) + u (x + t) ^ 2 * M (x + t) * M x) -
          (1 / 2) * signedShiftJump M u t x) := integral_congr_ae (Eventually.of_forall hpt)
    _ = (1 / 2) * ((∫ x, u x ^ 2 * M x * M (x + t)) + ∫ x, u (x + t) ^ 2 * M (x + t) * M x) -
          (1 / 2) * ∫ x, signedShiftJump M u t x := by
        have i12 : Integrable fun x => u x ^ 2 * M x * M (x + t) + u (x + t) ^ 2 * M (x + t) * M x :=
          i1.add i2
        rw [integral_sub (i12.const_mul _) (i3.const_mul _), integral_const_mul,
          integral_const_mul, integral_add i1 i2]
    _ = _ := by
        rw [hshift, ← integral_add i1 i4]
        congr 2
        exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

include hu hM hMB in
/-- The curved mass kernel `(t, x) ↦ cosh(t/2) u(x)² M(x) (M(x+t) + M(x−t))` is integrable. -/
theorem integrable_curvedMass_kernel :
    Integrable (fun p : ℝ × ℝ =>
        Real.cosh (p.1 / 2) * (u p.2 ^ 2 * M p.2 * (M (p.2 + p.1) + M (p.2 - p.1))))
      ((volume : Measure ℝ).prod volume) := by
  refine integrable_prod_of_box (B := 2 * |B|) (by fun_prop) fun p hp => ?_
  have h1 : M p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
  have a1 := (hMB _ h1).trans (le_abs_self B)
  have hM' : M (p.2 + p.1) ≠ 0 ∨ M (p.2 - p.1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (by rw [h.1, h.2]; ring)
  refine ⟨?_, by linarith [abs_nonneg B]⟩
  rcases hM' with h2 | h2
  · have a2 := (hMB _ h2).trans (le_abs_self B)
    have h3 : |p.1| ≤ |p.2 + p.1| + |p.2| := by
      have := abs_sub (p.2 + p.1) p.2
      rwa [add_sub_cancel_left] at this
    linarith
  · have a2 := (hMB _ h2).trans (le_abs_self B)
    have h3 : |p.1| ≤ |p.2 - p.1| + |p.2| := by
      have := abs_sub p.2 (p.2 - p.1)
      rw [sub_sub_cancel] at this
      linarith [abs_sub_comm p.2 (p.2 - p.1)]
    linarith

include hu hM hMB in
/-- **The pole product in a curved gauge.** For the test `M u`,
`2E₊E₋ = 2 ∫ u(x)² M(x) ∫ M(y) cosh((x−y)/2) dy dx − 2 ∫_0^∞ cosh(t/2) I(t) dt`. -/
theorem two_mul_expMoments_mul_eq_gauge :
    2 * expHalfMoment (fun x => M x * u x) * expNegHalfMoment (fun x => M x * u x) =
      2 * (∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) -
        2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
  set F : ℝ → ℝ := fun x => M x * u x with hFdef
  have hF : Continuous F := hM.mul hu
  have hFB : ∀ x, F x ≠ 0 → |x| ≤ B := mul_ne_zero_bound hMB
  -- `E₊ E₋ = ∫ cosh(t/2) A(t)`
  have hE : expHalfMoment F * expNegHalfMoment F = ∫ t, Real.cosh (t / 2) * autoCorr F t := by
    rw [← integral_exp_mul_autoCorr_eq_cosh hF hFB]
    have hin : ∀ x, F x * Real.exp (x / 2) * expNegHalfMoment F =
        ∫ t, F x * F (x + t) * Real.exp (-(1 / 2) * t) := fun x => by
      unfold expNegHalfMoment
      rw [← integral_add_left_eq_self (fun y => F y * Real.exp (-(y / 2))) x, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      have e : Real.exp (x / 2) * Real.exp (-((x + t) / 2)) = Real.exp (-(1 / 2) * t) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination (F x * F (x + t)) * e
    unfold expHalfMoment
    rw [← integral_mul_const, integral_congr_ae (Eventually.of_forall hin),
      integral_integral_swap (f := fun x t => F x * F (x + t) * Real.exp (-(1 / 2) * t))
        (integrable_autoCorr_kernel hF hFB (-(1 / 2))).swap]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [autoCorr]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hK1 := integrable_curvedMass_kernel hu hM hMB
  have hK2 := integrable_gaugeJump_kernel hu hM hMB
  have hi1 : Integrable fun t =>
      Real.cosh (t / 2) * ∫ x, u x ^ 2 * M x * (M (x + t) + M (x - t)) :=
    hK1.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only
      rw [integral_const_mul])
  have hi2 : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t :=
    hK2.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [gaugeJumpProfile]
      rw [integral_const_mul])
  have hsplit : (∫ t, Real.cosh (t / 2) * autoCorr F t) =
      (1 / 2) * (∫ t, Real.cosh (t / 2) * ∫ x, u x ^ 2 * M x * (M (x + t) + M (x - t))) -
        (1 / 2) * ∫ t, Real.cosh (t / 2) * gaugeJumpProfile M u t := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi1.const_mul _) (hi2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [hFdef, autoCorr_mul_eq_gauge hu hM hMB]
    ring
  -- the potential part
  have hpot : (∫ t, Real.cosh (t / 2) * ∫ x, u x ^ 2 * M x * (M (x + t) + M (x - t))) =
      2 * ∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have hswap := integral_integral_swap
      (f := fun t x => Real.cosh (t / 2) * (u x ^ 2 * M x * (M (x + t) + M (x - t)))) hK1
    have h1 : (∫ t, Real.cosh (t / 2) * ∫ x, u x ^ 2 * M x * (M (x + t) + M (x - t))) =
        ∫ t, ∫ x, Real.cosh (t / 2) * (u x ^ 2 * M x * (M (x + t) + M (x - t))) :=
      integral_congr_ae (Eventually.of_forall fun t => by simp only; rw [integral_const_mul])
    rw [h1, hswap, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    have hMc : HasCompactSupport M := hasCompactSupport_of_bound hMB
    have ia : Integrable fun t => Real.cosh (t / 2) * M (x + t) :=
      ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul
        (hM.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
        (hMc.comp_homeomorph (Homeomorph.addLeft x)).mul_left
    have ib : Integrable fun t => Real.cosh (t / 2) * M (x - t) :=
      ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul
        (hM.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        ((hMc.comp_homeomorph (Homeomorph.subLeft x))).mul_left
    have e1 : (∫ t, Real.cosh (t / 2) * M (x + t)) = ∫ y, M y * Real.cosh ((x - y) / 2) := by
      rw [← integral_add_left_eq_self (fun y => M y * Real.cosh ((x - y) / 2)) x]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [show (x - (x + t)) / 2 = -(t / 2) by ring, Real.cosh_neg]
      ring
    have e2 : (∫ t, Real.cosh (t / 2) * M (x - t)) = ∫ t, Real.cosh (t / 2) * M (x + t) := by
      rw [← integral_neg_eq_self (fun t => Real.cosh (t / 2) * M (x + t))]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [show -t / 2 = -(t / 2) by ring, Real.cosh_neg, ← sub_eq_add_neg]
    have hsum : (∫ t, Real.cosh (t / 2) * (u x ^ 2 * M x * (M (x + t) + M (x - t)))) =
        u x ^ 2 * M x * ((∫ t, Real.cosh (t / 2) * M (x + t)) +
          ∫ t, Real.cosh (t / 2) * M (x - t)) := by
      rw [← integral_add ia ib, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
    rw [hsum, e2, e1]
    ring
  -- fold the jump part onto the half line
  have hfold : (∫ t, Real.cosh (t / 2) * gaugeJumpProfile M u t) =
      2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
    rw [← integral_add_compl measurableSet_Ioi hi2, compl_Ioi]
    have hneg := integral_comp_neg_Ioi 0 (fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t)
    rw [neg_zero] at hneg
    rw [← hneg]
    have : (∫ t in Ioi (0 : ℝ), Real.cosh (-t / 2) * gaugeJumpProfile M u (-t)) =
        ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        rw [gaugeJumpProfile_neg, show -t / 2 = -(t / 2) by ring, Real.cosh_neg]
    rw [this]
    ring
  rw [mul_assoc, hE, hsplit, hpot, hfold]
  ring

end PoleProduct

/-! ### The full zero form of a curved-gauge test -/

/-- **The curved-gauge representation of the full zero form** on a window below the first prime. -/
theorem fullZeroForm_mul_eq_gauge_window {u M : ℝ → ℝ} {R : ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (hMd : ContDiff ℝ 2 M) (hMcs : HasCompactSupport M)
    (hle : ∀ y, M y ≤ 1) (hnn : ∀ y, 0 ≤ M y) (hzero : ∀ y, R ≤ |y| → M y = 0)
    (hR : 2 * R < Real.log 2) :
    fullZeroForm (fun x => M x * u x) =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
        2 * (∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t) +
        (∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x) +
        2 * ∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) := by
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ R := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hFc : HasCompactSupport fun x => M x * u x := huc.mul_left
  have hQ := markovEnergy_mul_eq_gauge_window hu huc hMd hMcs hle hnn hzero
  have hJ := signedJumpEnergy_eq_arch_of_window (F := u) hzero hR
  have hE := two_mul_expMoments_mul_eq_gauge hu.continuous hMd.continuous hMB
  have hZ := fullZeroForm_eq_markovEnergy_add_expMoments (F := fun x => M x * u x)
    (hMd.continuous.mul hu.continuous) hFc
  rw [hZ, hQ, hJ, hE]
  ring

/-! ### Negative densities are potentials -/

/-- The jump profile is at most `2 ∫ u(x)² M(x) (M(x+t) + M(x−t)) dx` in a nonnegative gauge. -/
theorem gaugeJumpProfile_le_curvedMass {u M : ℝ → ℝ} (hu : Continuous u) (hM : Continuous M)
    (hMcs : HasCompactSupport M) (hnn : ∀ y, 0 ≤ M y) (t : ℝ) :
    gaugeJumpProfile M u t ≤ 2 * ∫ x, u x ^ 2 * M x * (M (x + t) + M (x - t)) := by
  have hMt : Continuous fun x => M (x + t) := hM.comp (continuous_id.add continuous_const)
  have hut : Continuous fun x => u (x + t) := hu.comp (continuous_id.add continuous_const)
  have i1 : Integrable fun x => u x ^ 2 * M x * M (x + t) :=
    (((hu.pow 2).mul hM).mul hMt).integrable_of_hasCompactSupport hMcs.mul_left.mul_right
  have i2 : Integrable fun x => u (x + t) ^ 2 * M (x + t) * M x :=
    (((hut.pow 2).mul hMt).mul hM).integrable_of_hasCompactSupport hMcs.mul_left
  have i3 : Integrable fun x => signedShiftJump M u t x := by
    unfold signedShiftJump
    exact ((hM.mul hMt).mul ((hu.sub hut).pow 2)).integrable_of_hasCompactSupport
      hMcs.mul_right.mul_right
  have i4 : Integrable fun x => u x ^ 2 * M x * M (x - t) :=
    (((hu.pow 2).mul hM).mul (hM.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hMcs.mul_left.mul_right
  have hpt : ∀ x, signedShiftJump M u t x ≤
      2 * (u x ^ 2 * M x * M (x + t)) + 2 * (u (x + t) ^ 2 * M (x + t) * M x) := fun x => by
    unfold signedShiftJump
    have h0 : 0 ≤ M x * M (x + t) := mul_nonneg (hnn x) (hnn _)
    nlinarith [mul_nonneg h0 (sq_nonneg (u x + u (x + t)))]
  have hshift : (∫ x, u (x + t) ^ 2 * M (x + t) * M x) = ∫ x, u x ^ 2 * M x * M (x - t) := by
    rw [← integral_add_right_eq_self (fun x => u x ^ 2 * M x * M (x - t)) t]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right]
  unfold gaugeJumpProfile
  calc (∫ x, signedShiftJump M u t x)
      ≤ ∫ x, (2 * (u x ^ 2 * M x * M (x + t)) + 2 * (u (x + t) ^ 2 * M (x + t) * M x)) :=
        integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) hpt
    _ = 2 * ∫ x, u x ^ 2 * M x * (M (x + t) + M (x - t)) := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul,
          hshift, ← mul_add, ← integral_add i1 i4]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

/-- **A negative density is a potential.** For every continuous `κ ≥ 0`,
`∫_0^∞ κ I ≤ 2 ∫ u(x)² M(x) (∫_0^∞ κ(t)(M(x+t) + M(x−t)) dt) dx`. -/
theorem integral_mul_gaugeJumpProfile_le {u M κ : ℝ → ℝ} {B : ℝ} (hu : Continuous u)
    (hM : Continuous M) (hMB : ∀ x, M x ≠ 0 → |x| ≤ B) (hnn : ∀ y, 0 ≤ M y)
    (hκ : Continuous κ) (hκ0 : ∀ t, 0 ≤ κ t) :
    (∫ t in Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t) ≤
      2 * ∫ x, u x ^ 2 * M x * ∫ t in Ioi (0 : ℝ), κ t * (M (x + t) + M (x - t)) := by
  have hMcs : HasCompactSupport M := hasCompactSupport_of_bound hMB
  -- the kernel on the product
  have hK : Integrable (fun p : ℝ × ℝ => κ p.1 * (u p.2 ^ 2 * M p.2 * (M (p.2 + p.1) + M (p.2 - p.1))))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hfull : Integrable (fun p : ℝ × ℝ =>
        κ p.1 * (u p.2 ^ 2 * M p.2 * (M (p.2 + p.1) + M (p.2 - p.1))))
        ((volume : Measure ℝ).prod volume) := by
      refine integrable_prod_of_box (B := 2 * |B|) (by fun_prop) fun p hp => ?_
      have h1 : M p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
      have a1 := (hMB _ h1).trans (le_abs_self B)
      have hM' : M (p.2 + p.1) ≠ 0 ∨ M (p.2 - p.1) ≠ 0 := by
        by_contra h
        push Not at h
        exact hp (by rw [h.1, h.2]; ring)
      refine ⟨?_, by linarith [abs_nonneg B]⟩
      rcases hM' with h2 | h2
      · have a2 := (hMB _ h2).trans (le_abs_self B)
        have h3 : |p.1| ≤ |p.2 + p.1| + |p.2| := by
          have := abs_sub (p.2 + p.1) p.2
          rwa [add_sub_cancel_left] at this
        linarith
      · have a2 := (hMB _ h2).trans (le_abs_self B)
        have h3 : |p.1| ≤ |p.2 - p.1| + |p.2| := by
          have := abs_sub p.2 (p.2 - p.1)
          rw [sub_sub_cancel] at this
          linarith [abs_sub_comm p.2 (p.2 - p.1)]
        linarith
    have hres : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hres]
    exact hfull.integrableOn
  have hmass : ∀ t, κ t * gaugeJumpProfile M u t ≤
      2 * ∫ x, κ t * (u x ^ 2 * M x * (M (x + t) + M (x - t))) := fun t => by
    rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left (gaugeJumpProfile_le_curvedMass hu hM hMcs hnn t) (hκ0 t)
    linarith
  have hleft : IntegrableOn (fun t => κ t * gaugeJumpProfile M u t) (Ioi 0) := by
    have hjump := integrable_gaugeJump_kernel hu hM hMB
    have hfull : Integrable (fun p : ℝ × ℝ => κ p.1 * signedShiftJump M u p.1 p.2)
        ((volume : Measure ℝ).prod volume) := by
      unfold signedShiftJump
      refine integrable_prod_of_box (B := 2 * |B|) (by fun_prop) fun p hp => ?_
      have h1 : M p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
      have h2 : M (p.2 + p.1) ≠ 0 := fun h => hp (by rw [h]; ring)
      have a1 := (hMB _ h1).trans (le_abs_self B)
      have a2 := (hMB _ h2).trans (le_abs_self B)
      have h3 : |p.1| ≤ |p.2 + p.1| + |p.2| := by
        have := abs_sub (p.2 + p.1) p.2
        rwa [add_sub_cancel_left] at this
      exact ⟨by linarith, by linarith [abs_nonneg B]⟩
    exact (hfull.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [gaugeJumpProfile]
      rw [integral_const_mul])).integrableOn
  have hright : IntegrableOn (fun t => 2 * ∫ x, κ t * (u x ^ 2 * M x * (M (x + t) + M (x - t))))
      (Ioi 0) := hK.integral_prod_left.const_mul 2
  calc (∫ t in Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t)
      ≤ ∫ t in Ioi (0 : ℝ), 2 * ∫ x, κ t * (u x ^ 2 * M x * (M (x + t) + M (x - t))) :=
        setIntegral_mono_on hleft hright measurableSet_Ioi fun t _ => hmass t
    _ = 2 * ∫ x, ∫ t in Ioi (0 : ℝ), κ t * (u x ^ 2 * M x * (M (x + t) + M (x - t))) := by
        rw [integral_const_mul, integral_integral_swap hK]
    _ = 2 * ∫ x, u x ^ 2 * M x * ∫ t in Ioi (0 : ℝ), κ t * (M (x + t) + M (x - t)) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
