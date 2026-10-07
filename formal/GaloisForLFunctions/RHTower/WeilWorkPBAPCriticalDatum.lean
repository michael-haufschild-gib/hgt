import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalResonator
import GaloisForLFunctions.RHTower.WeilWorkPBAPNullRepair

/-!
# Variable gamma and pole coefficients on the smooth null cone

The datum below uses the actual gamma integral, both actual poles, and physical
L2 mass. Algebraic null-cone duality produces coefficients without imposing
their signs, growth, or convergence. The resonator estimate then retains the
exact leading gamma coefficient in its multiplicative Toeplitz bound.

These are intermediate implications in `CRITICAL-SLOPE.md`; they do not assume
or assert existence of a positive completion for the original PBAP datum.
-/

open Complex MeasureTheory Finsupp Zeta23
open scoped Real ComplexConjugate ContDiff

noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided ResonatorProfile

/-- Smooth compact tests, retaining the established full Weil test interface. -/
def SmoothTest : Type := {f : WeilTestFn // ContDiff ℝ ∞ f.1}

/-- Actual gamma contribution of a test. -/
def testGamma (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * π)) * ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * EF.gammaBracket t

/-- Both poles of the actual autocorrelation, with their signs retained. -/
def testPole (f : ℝ → ℂ) : ℝ :=
  (paperFT (EF.weilTest f f) (I / 2) + paperFT (EF.weilTest f f) (-I / 2)).re

/-- Physical squared L2 mass. -/
def testMass (f : ℝ → ℂ) : ℝ := ∫ u : ℝ, ‖f u‖ ^ 2

/-- Gamma coefficient, pole weight, and mass slack. -/
def criticalDatum (a b C : ℝ) (f : ℝ → ℂ) : ℝ :=
  a * testGamma f + b * testPole f + C * testMass f

/-- Literal finite pairing with every symmetric integer-log sample. -/
def testAtoms (lam : ℕ → ℝ) (f : WeilTestFn) : ℝ :=
  linearCombination ℝ (fun j : LogIndex => lam j) (logVector f)

/-- Nonnegativity on actual smooth finite integer-null mixtures. -/
def SmoothNullPositive (a b C : ℝ) : Prop :=
  ∀ c : SmoothTest →₀ ℝ, (∀ f, 0 ≤ c f) →
    linearCombination ℝ (fun f : SmoothTest => logVector f.1) c = 0 →
    0 ≤ linearCombination ℝ (fun f : SmoothTest => criticalDatum a b C f.1.1) c

/-- The coordinate-isolating tests are smooth. -/
def smoothPairTest (j : LogIndex) (s : ℝ) : SmoothTest :=
  ⟨pairTestFn j s, (contDiff_narrowBumpC j).add
    (contDiff_const.mul ((contDiff_narrowBumpC j).comp (contDiff_id.sub contDiff_const)))⟩

/-- Exact algebraic duality, with no analytic premise on the produced coefficients. -/
theorem exists_critical_completion {a b C : ℝ} (h : SmoothNullPositive a b C) :
    ∃ lam : ℕ → ℝ, lam 0 = 0 ∧ lam 1 = 0 ∧
      ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1 := by
  obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
    (fun f : SmoothTest => logVector f.1)
    (fun f : SmoothTest => criticalDatum a b C f.1.1)
    (fun j => ⟨smoothPairTest j (-1), _, pairTest_weight_pos j, by
      change logVector (pairTestFn j (-1)) = _
      rw [logVector_pairTestFn]; congr 1; ring⟩)
    (fun j => ⟨smoothPairTest j 1, _, pairTest_weight_pos j, by
      change logVector (pairTestFn j 1) = _
      rw [logVector_pairTestFn]; congr 1; ring⟩) h
  refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0, by simp, by simp, ?_⟩
  intro f
  have heq : (fun j : LogIndex => if hn : 2 ≤ (j : ℕ) then lam ⟨j, hn⟩ else 0) = lam := by
    funext j
    simp only [dif_pos j.2]
  change linearCombination ℝ _ (logVector f.1) ≤ _
  rw [heq]
  exact hlam f

/-- An actual smooth polar resonator in the full test space. -/
def smoothResonator (N : ℕ) (c : ℕ → ℂ) : SmoothTest :=
  ⟨⟨resonator N c (1 / ((N : ℝ) + 1)), contDiff_resonator N c _ 2,
    hasCompactSupport_resonator c (by positivity)⟩, contDiff_resonator_infty N c _⟩

theorem testPole_resonator (N : ℕ) (c : ℕ → ℂ) :
    testPole (smoothResonator N c).1.1 = 0 := by
  have hp := resonator_poles N c
  have hf := (smoothResonator N c).1.2
  unfold testPole
  rw [EF.paperFT_weilTest hf.1.continuous hf.1.continuous hf.2 hf.2,
    EF.paperFT_weilTest hf.1.continuous hf.1.continuous hf.2 hf.2]
  change (paperFT (resonator N c _) (I / 2) * _ +
    paperFT (resonator N c _) (-I / 2) * _).re = 0
  rw [hp.1, show (-I / 2 : ℂ) = -(I / 2) by ring, hp.2]
  simp

/-- Exact atom pairing of the smooth polar resonator. -/
theorem testAtoms_resonator (lam : ℕ → ℝ) (N : ℕ) (c : ℕ → ℂ)
    (hc : ∀ m, N < m → c m = 0) :
    testAtoms lam (smoothResonator N c).1 =
      2 * resonatorMass N * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re := by
  classical
  let f := (smoothResonator N c).1
  have hval (n : ℕ) (hn : 2 ≤ n) : logValue f.1 n =
      2 * resonatorMass N *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re / Real.sqrt n := by
    exact congrArg (fun t : ℝ => t / Real.sqrt n) (resonator_log_sample N c hc n (by omega))
  have hzero (n : ℕ) (hn : N < n) :
      (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [hc (n * m) (by nlinarith), zero_mul]
  have hsum : testAtoms lam f =
      ∑ j ∈ (Finset.Icc 2 N).subtype (fun n => 2 ≤ n), logValue f.1 j * lam j := by
    rw [testAtoms, linearCombination_apply]
    refine (Finsupp.sum_of_support_subset (s := (Finset.Icc 2 N).subtype (fun n => 2 ≤ n))
      (logVector f) (fun j hj => ?_)
      (fun j t => t • lam j) (fun _ _ => zero_smul _ _)).trans ?_
    · rw [Finsupp.mem_support_iff, logVector_apply] at hj
      rw [Finset.mem_subtype, Finset.mem_Icc]
      refine ⟨j.2, ?_⟩
      by_contra hn
      apply hj
      rw [hval j j.2, hzero j (by omega)]
      simp
    · exact Finset.sum_congr rfl fun j _ => by rw [logVector_apply, smul_eq_mul]
  rw [hsum, Finset.sum_subtype_eq_sum_filter (fun n => logValue f.1 n * lam n),
    Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn2 := (Finset.mem_Icc.mp hn).1
  rw [if_pos hn2, hval n hn2]
  ring

/-- Any actual modified completion has Toeplitz slope equal to its gamma coefficient.
No growth or sign hypothesis on `lam` is used. -/
theorem critical_multiplicativeToeplitz_bound {a b C : ℝ} (ha : 0 ≤ a)
    {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ) (hc : ∀ m, N < m → c m = 0) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
      (a * Real.log N + (a * resonatorGammaConstant + C)) *
        ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  have hh := h (smoothResonator N c)
  rw [testAtoms_resonator lam N c hc, criticalDatum, testPole_resonator, mul_zero,
    add_zero] at hh
  have hm := resonator_mass hN c hc
  change testMass (smoothResonator N c).1.1 = _ at hm
  rw [hm] at hh
  have hg := mul_le_mul_of_nonneg_left (resonator_gamma_bound hN c hc) ha
  change a * testGamma (smoothResonator N c).1.1 ≤ _ at hg
  have hprod : resonatorMass N *
      (2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re) ≤
      resonatorMass N * ((a * Real.log N + (a * resonatorGammaConstant + C)) *
        ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2) := by
    nlinarith
  exact le_of_mul_le_mul_left hprod (resonatorMass_pos N)

end RHTower.WeilWorkPBAP
