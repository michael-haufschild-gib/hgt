/-
# Jensen zero counts for completed Dirichlet L-functions

This module provides the analytic counting layer needed before a genuine
Dirichlet-family zero-density estimate can be attempted.  A nonprincipal
character is recorded as certified data at the positive modulus `n + 1`.
The theorem below chooses its own nonzero anchor from the proved real-ray
result and derives an `O(r log r)` divisor count from the proved order-one
envelope.  No RH, GRH, Siegel-zero, density, or external growth assumption is
used.
-/
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne
import GaloisForLFunctions.RHTower.DirichletLZeroExistence
import Mathlib.Analysis.Complex.JensenFormula

noncomputable section

open Complex Metric

namespace RHTower

/-- A complex Dirichlet character at the concrete positive modulus `n + 1`,
certified not to be the principal character. -/
abbrev NonprincipalDirichletCharacter (n : ℕ) :=
  {χ : DirichletCharacter ℂ (n + 1) // χ ≠ 1}

/-- A nonprincipal completed Dirichlet L-function is analytic on the full plane. -/
theorem completedLFunction_analyticOnNhd
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.1) Set.univ :=
  (DirichletCharacter.differentiable_completedLFunction χ.2).differentiableOn.analyticOnNhd
    isOpen_univ

/-- The completed L-function of every certified nonprincipal character is nonzero at the common
right-half-plane anchor `s = 2`. -/
theorem completedLFunction_two_ne_zero
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    DirichletCharacter.completedLFunction χ.1 (2 : ℂ) ≠ 0 := by
  intro hzero
  apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.1 (s := (2 : ℂ))
    (Or.inl χ.2) (by norm_num)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.1 (2 : ℂ)
    (Or.inl (by norm_num)), hzero, zero_div]

/-- Jensen's bound for a nonprincipal completed Dirichlet L-function in a pair of concentric discs.
All analytic premises in this local form are standard boundary data; the global theorem below
constructs them from proved facts. -/
theorem completedLFunction_zeroCount_disc_le
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    {c : ℂ} {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc : DirichletCharacter.completedLFunction χ.1 c ≠ 0)
    (hbound : ∀ z ∈ sphere c |R|, ‖DirichletCharacter.completedLFunction χ.1 z‖ ≤ M) :
    (↑(∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
      (closedBall c |r|)) u) : ℝ)
      ≤ Real.log (M / ‖DirichletCharacter.completedLFunction χ.1 c‖) / Real.log (R / r) :=
  ((completedLFunction_analyticOnNhd n χ).mono (Set.subset_univ _)).sum_divisor_le
    hr hrR hM hc hbound

/-- Every nonprincipal completed Dirichlet L-function has a self-contained local anchor and an
order-one Jensen divisor-count bound.  The bound counts zero multiplicity in `closedBall c r`.
The constants and anchor are obtained inside the proof, not supplied as mathematical assumptions. -/
theorem completedLFunction_zeroCount_growth
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    ∃ c : ℂ, ∃ C : ℝ, 0 < C ∧
      DirichletCharacter.completedLFunction χ.1 c ≠ 0 ∧
      ∀ r : ℝ, 1 ≤ r →
        (↑(∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
          (Metric.closedBall c r)) u) : ℝ)
          ≤ C * (1 + r) * Real.log (2 + r) := by
  obtain ⟨σ, hσ, hσne⟩ := exists_completedLFunction_ne_zero_ray (χ := χ.1)
  obtain ⟨C₀, hC₀, hgrow⟩ := completedLFunction_orderOneEnvelope χ.2
  let c : ℂ := (σ : ℂ)
  have hc : DirichletCharacter.completedLFunction χ.1 c ≠ 0 := by
    simpa only [c] using hσne
  have hL2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := 5 + ‖c‖
  set L : ℝ := Real.log (2 + ‖c‖)
  have hLnn : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith [norm_nonneg c])
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hLpluspos : 0 < 1 + L := by linarith
  refine ⟨c, (C₀ * A * (1 + L) + |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖|
    + Real.log 2) / Real.log 2, ?_, hc, ?_⟩
  · apply div_pos
    · have hmain : 0 < C₀ * A * (1 + L) :=
        mul_pos (mul_pos hC₀ hApos) hLpluspos
      linarith [abs_nonneg (Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖)]
    · exact hL2pos
  intro r hr1
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrabs : |r| = r := abs_of_pos hr0
  set R : ℝ := 2 * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRabs : |R| = R := abs_of_pos hRpos
  set M : ℝ := Real.exp (C₀ * (1 + (‖c‖ + 2 * r)) * Real.log (2 + (‖c‖ + 2 * r))) with hMdef
  have hMnn : 0 ≤ C₀ * (1 + (‖c‖ + 2 * r)) * Real.log (2 + (‖c‖ + 2 * r)) := by
    apply mul_nonneg (mul_nonneg hC₀.le (by linarith [norm_nonneg c]))
    exact Real.log_nonneg (by linarith [norm_nonneg c])
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Real.one_le_exp hMnn
  have hbound : ∀ z ∈ sphere c |R|, ‖DirichletCharacter.completedLFunction χ.1 z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hznorm : ‖z‖ ≤ ‖c‖ + 2 * r := by
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        have h := norm_add_le (z - c) c
        simpa using h
      rw [hz, hRabs, hRdef] at htri
      simpa only [add_comm] using htri
    have hznn : 0 ≤ ‖z‖ := norm_nonneg z
    refine le_trans (hgrow z) ?_
    rw [GaloisForLFunctions.HTGeometry.orderOneWeight, hMdef]
    apply Real.exp_le_exp.mpr
    have hfac1 : C₀ * (1 + ‖z‖) ≤ C₀ * (1 + (‖c‖ + 2 * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have hfac2 : Real.log (2 + ‖z‖) ≤ Real.log (2 + (‖c‖ + 2 * r)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlognn : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
    exact mul_le_mul hfac1 hfac2 hlognn (by positivity)
  have hrR : r < R := by rw [hRdef]; linarith
  have hcount := completedLFunction_zeroCount_disc_le n χ
    (c := c) (r := r) (R := R) (M := M)
    (by rwa [abs_of_pos hr0])
    (by rwa [abs_of_pos hr0, abs_of_pos hRpos]) hM1 hc hbound
  rw [hrabs] at hcount
  have hRr : R / r = 2 := by rw [hRdef]; field_simp
  rw [hRr, hMdef,
    Real.log_div (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hc), Real.log_exp] at hcount
  set P : ℝ := (1 + r) * Real.log (2 + r)
  have hlog1 : (1 : ℝ) ≤ Real.log (2 + r) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    nlinarith [Real.exp_one_lt_d9, hr1]
  have hP : (1 : ℝ) ≤ P := by
    dsimp only [P]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (1 + r) * Real.log (2 + r) :=
        mul_le_mul (by linarith) hlog1 zero_le_one (by linarith)
  have hfac : 1 + ‖c‖ + 2 * r ≤ A * (1 + r) := by
    dsimp [A]
    nlinarith [norm_nonneg c, hr1]
  have hlog : Real.log (2 + (‖c‖ + 2 * r)) ≤ (1 + L) * Real.log (2 + r) := by
    have harg : 2 + (‖c‖ + 2 * r) ≤ (2 + ‖c‖) * (2 + r) := by
      nlinarith [norm_nonneg c, hr1]
    have hfirst : Real.log (2 + (‖c‖ + 2 * r)) ≤ Real.log ((2 + ‖c‖) * (2 + r)) :=
      Real.log_le_log (by linarith [norm_nonneg c]) harg
    rw [Real.log_mul (by linarith [norm_nonneg c]) (by linarith)] at hfirst
    dsimp [L]
    nlinarith [hfirst, hlog1, hLnn]
  have hQ : C₀ * (1 + (‖c‖ + 2 * r)) * Real.log (2 + (‖c‖ + 2 * r))
      ≤ C₀ * A * (1 + L) * P := by
    have hshape : (1 + (‖c‖ + 2 * r)) * Real.log (2 + (‖c‖ + 2 * r))
        ≤ (A * (1 + r)) * ((1 + L) * Real.log (2 + r)) := by
      have hshape' := mul_le_mul hfac hlog
        (Real.log_nonneg (by linarith [norm_nonneg c])) (by positivity : 0 ≤ A * (1 + r))
      simpa only [add_assoc] using hshape'
    dsimp only [P]
    nlinarith [mul_le_mul_of_nonneg_left hshape hC₀.le]
  have habs : -Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖ ≤
      |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖| * P := by
    calc -Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖
        ≤ |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖| := neg_le_abs _
      _ = |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖| * 1 := by ring
      _ ≤ |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖| * P :=
        mul_le_mul_of_nonneg_left hP (abs_nonneg _)
  have hslack : 0 ≤ Real.log 2 * P :=
    mul_nonneg hL2pos.le (le_trans zero_le_one hP)
  have hcountmul :
      (↑(∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
        (closedBall c r)) u) : ℝ) * Real.log 2
        ≤ C₀ * (1 + (‖c‖ + 2 * r)) * Real.log (2 + (‖c‖ + 2 * r))
          - Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖ :=
    (le_div_iff₀ hL2pos).mp hcount
  have htarget :
      (C₀ * A * (1 + L) + |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖|
        + Real.log 2) * P
        = C₀ * A * (1 + L) * P
          + |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖| * P + Real.log 2 * P := by
    ring
  calc
    _ ≤ (C₀ * A * (1 + L) + |Real.log ‖DirichletCharacter.completedLFunction χ.1 c‖|
        + Real.log 2) / Real.log 2 * P := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hL2pos]
      rw [htarget]
      linarith [hcountmul, hQ, habs, hslack]
    _ = _ := by
      dsimp only [P]
      ring

/-- Fixed-anchor form of the completed Dirichlet L-function zero-count bound.  Every certified
nonprincipal character uses the common anchor `2`; only the proved order-one constant varies with
the character.  This is the form needed for a later finite character-family aggregation. -/
theorem completedLFunction_zeroCount_growth_at_two
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      (↑(∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
        (Metric.closedBall (2 : ℂ) r)) u) : ℝ)
        ≤ C * (1 + r) * Real.log (2 + r) := by
  obtain ⟨C₀, hC₀, hgrow⟩ := completedLFunction_orderOneEnvelope χ.2
  have hL2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(6 * C₀ + |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| + Real.log 2)
    / Real.log 2, by positivity, ?_⟩
  intro r hr1
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrabs : |r| = r := abs_of_pos hr0
  set R : ℝ := 2 * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRabs : |R| = R := abs_of_pos hRpos
  set M : ℝ := Real.exp (C₀ * (1 + (2 + 2 * r)) * Real.log (2 + (2 + 2 * r))) with hMdef
  have hMnn : 0 ≤ C₀ * (1 + (2 + 2 * r)) * Real.log (2 + (2 + 2 * r)) := by
    apply mul_nonneg (mul_nonneg hC₀.le (by linarith))
    exact Real.log_nonneg (by linarith)
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Real.one_le_exp hMnn
  have hbound : ∀ z ∈ sphere (2 : ℂ) |R|,
      ‖DirichletCharacter.completedLFunction χ.1 z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hznorm : ‖z‖ ≤ 2 + 2 * r := by
      have htri : ‖z‖ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := by
        have h := norm_add_le (z - 2) 2
        simpa using h
      rw [hz, hRabs, hRdef] at htri
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2] at htri
      linarith
    have hznn : 0 ≤ ‖z‖ := norm_nonneg z
    refine le_trans (hgrow z) ?_
    rw [GaloisForLFunctions.HTGeometry.orderOneWeight, hMdef]
    apply Real.exp_le_exp.mpr
    have hfac1 : C₀ * (1 + ‖z‖) ≤ C₀ * (1 + (2 + 2 * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have hfac2 : Real.log (2 + ‖z‖) ≤ Real.log (2 + (2 + 2 * r)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlognn : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
    exact mul_le_mul hfac1 hfac2 hlognn (by positivity)
  have hrR : r < R := by rw [hRdef]; linarith
  have hcount := completedLFunction_zeroCount_disc_le n χ
    (c := (2 : ℂ)) (r := r) (R := R) (M := M)
    (by rwa [abs_of_pos hr0])
    (by rwa [abs_of_pos hr0, abs_of_pos hRpos]) hM1 (completedLFunction_two_ne_zero n χ) hbound
  rw [hrabs] at hcount
  have hRr : R / r = 2 := by rw [hRdef]; field_simp
  have h1eq : (1 : ℝ) + (2 + 2 * r) = 3 + 2 * r := by ring
  have h2eq : (2 : ℝ) + (2 + 2 * r) = 4 + 2 * r := by ring
  rw [hRr, hMdef,
    Real.log_div (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (completedLFunction_two_ne_zero n χ)),
    Real.log_exp, h1eq, h2eq] at hcount
  set P : ℝ := (1 + r) * Real.log (2 + r)
  have hP : (1 : ℝ) ≤ P := by
    have hlog1 : (1 : ℝ) ≤ Real.log (2 + r) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      nlinarith [Real.exp_one_lt_d9, hr1]
    dsimp only [P]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (1 + r) * Real.log (2 + r) :=
        mul_le_mul (by linarith) hlog1 zero_le_one (by linarith)
  have hQ : (3 + 2 * r) * Real.log (4 + 2 * r) ≤ 6 * P := by
    have hlog4 : Real.log (4 + 2 * r) ≤ 2 * Real.log (2 + r) := by
      have he : (4 : ℝ) + 2 * r = 2 * (2 + r) := by ring
      rw [he, Real.log_mul (by norm_num) (by linarith)]
      have : Real.log 2 ≤ Real.log (2 + r) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    have h3 : (3 : ℝ) + 2 * r ≤ 3 * (1 + r) := by linarith
    have hlognn : 0 ≤ Real.log (4 + 2 * r) := Real.log_nonneg (by linarith)
    calc (3 + 2 * r) * Real.log (4 + 2 * r)
        ≤ (3 * (1 + r)) * (2 * Real.log (2 + r)) := by
          apply mul_le_mul h3 hlog4 hlognn (by linarith)
      _ = 6 * P := by
        dsimp only [P]
        ring
  have habs : -Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖ ≤
      |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| * P := by
    calc -Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖
        ≤ |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| := neg_le_abs _
      _ = |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| * 1 := by ring
      _ ≤ |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| * P :=
        mul_le_mul_of_nonneg_left hP (abs_nonneg _)
  have hslack : 0 ≤ Real.log 2 * P :=
    mul_nonneg hL2pos.le (le_trans zero_le_one hP)
  have hcountmul :
      (↑(∑ᶠ u, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
        (closedBall (2 : ℂ) r)) u) : ℝ) * Real.log 2
        ≤ C₀ * (3 + 2 * r) * Real.log (4 + 2 * r)
          - Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖ :=
    (le_div_iff₀ hL2pos).mp hcount
  have htarget :
      (6 * C₀ + |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| + Real.log 2) * P
        = 6 * C₀ * P + |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| * P
          + Real.log 2 * P := by ring
  calc
    _ ≤ (6 * C₀ + |Real.log ‖DirichletCharacter.completedLFunction χ.1 2‖| + Real.log 2)
        / Real.log 2 * P := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hL2pos, htarget]
      linarith [hcountmul, mul_le_mul_of_nonneg_left hQ hC₀.le, habs, hslack]
    _ = _ := by
      dsimp only [P]
      ring

end RHTower
