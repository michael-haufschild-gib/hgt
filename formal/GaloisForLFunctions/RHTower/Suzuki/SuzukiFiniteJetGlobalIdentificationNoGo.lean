import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteApertureHermiteBiehler

/-!
# Finite Suzuki jets do not identify a global Schur carrier

Every finite collection of anchor derivatives is shared by distinct strict disk carriers, even
when the first derivative is nonzero.  Therefore strict Schur control plus finite source-jet
calibration alone cannot identify the cofinal Suzuki carrier.  A successful convergence argument
must use additional source-faithful information; in the literal Suzuki route, the candidate is
the global shell--metric Wronskian.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower

def suzukiFiniteJetLinearCarrier (kappa : ℝ) (w : ℂ) : ℂ :=
  (kappa : ℂ) * w

def suzukiFiniteJetPerturbedCarrier (kappa : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  (kappa : ℂ) * w + (((1 - kappa) / 2 : ℝ) : ℂ) * w ^ (n + 1)

theorem norm_suzukiFiniteJetLinearCarrier_lt_one
    {kappa : ℝ} (hk0 : 0 < kappa) (hk1 : kappa < 1) {w : ℂ}
    (hw : ‖w‖ < 1) :
    ‖suzukiFiniteJetLinearCarrier kappa w‖ < 1 := by
  rw [suzukiFiniteJetLinearCarrier, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hk0]
  nlinarith [norm_nonneg w]

theorem norm_suzukiFiniteJetPerturbedCarrier_lt_one
    {kappa : ℝ} (hk0 : 0 < kappa) (hk1 : kappa < 1) {n : ℕ} {w : ℂ}
    (hw : ‖w‖ < 1) :
    ‖suzukiFiniteJetPerturbedCarrier kappa n w‖ < 1 := by
  rw [suzukiFiniteJetPerturbedCarrier]
  calc
    ‖(kappa : ℂ) * w + (((1 - kappa) / 2 : ℝ) : ℂ) * w ^ (n + 1)‖ ≤
        ‖(kappa : ℂ) * w‖ + ‖(((1 - kappa) / 2 : ℝ) : ℂ) * w ^ (n + 1)‖ :=
      norm_add_le _ _
    _ = kappa * ‖w‖ + ((1 - kappa) / 2) * ‖w‖ ^ (n + 1) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), norm_pow]
    _ < kappa + (1 - kappa) / 2 := by
      have hpow : ‖w‖ ^ (n + 1) ≤ 1 := by
        exact pow_le_one₀ (norm_nonneg _) hw.le
      have hleft : kappa * ‖w‖ < kappa := by
        nlinarith
      have hright : (1 - kappa) / 2 * ‖w‖ ^ (n + 1) ≤ (1 - kappa) / 2 := by
        calc
          (1 - kappa) / 2 * ‖w‖ ^ (n + 1) ≤ (1 - kappa) / 2 * 1 :=
            mul_le_mul_of_nonneg_left hpow (by linarith)
          _ = (1 - kappa) / 2 := by ring
      linarith
    _ < 1 := by linarith

theorem suzukiFiniteJetCarriers_same_through
    {kappa : ℝ} {n j : ℕ} (hj : j ≤ n) :
    iteratedDeriv j (suzukiFiniteJetPerturbedCarrier kappa n) 0 =
      iteratedDeriv j (suzukiFiniteJetLinearCarrier kappa) 0 := by
  change iteratedDeriv j ((fun w : ℂ => (kappa : ℂ) * w) +
      fun w : ℂ => (((1 - kappa) / 2 : ℝ) : ℂ) * w ^ (n + 1)) 0 =
    iteratedDeriv j (fun w : ℂ => (kappa : ℂ) * w) 0
  have hlinear : ContDiffAt ℂ j (fun w : ℂ => (kappa : ℂ) * w) 0 := by fun_prop
  have hpower : ContDiffAt ℂ j (fun w : ℂ => (((1 - kappa) / 2 : ℝ) : ℂ) *
      w ^ (n + 1)) 0 := by fun_prop
  have hne : j ≠ n + 1 := by omega
  have hvanishes : iteratedDeriv j (fun w : ℂ => (((1 - kappa) / 2 : ℝ) : ℂ) *
      w ^ (n + 1)) 0 = 0 := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    simp [hne]
  rw [iteratedDeriv_add hlinear hpower, hvanishes, add_zero]

theorem suzukiFiniteJetPerturbedCarrier_ne_linearCarrier
    {kappa : ℝ} (hk1 : kappa < 1) (n : ℕ) :
    suzukiFiniteJetPerturbedCarrier kappa n ≠
      suzukiFiniteJetLinearCarrier kappa := by
  intro h
  have hhalf := congrFun h ((1 / 2 : ℝ) : ℂ)
  rw [suzukiFiniteJetPerturbedCarrier, suzukiFiniteJetLinearCarrier] at hhalf
  have hcoef : (((1 - kappa) / 2 : ℝ) : ℂ) ≠ 0 := by
    have hreal : (1 - kappa) / 2 ≠ 0 := by linarith
    exact_mod_cast hreal
  have hpow : (((1 / 2 : ℝ) : ℂ) ^ (n + 1)) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hzero :
      (((1 - kappa) / 2 : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ (n + 1)) = 0 := by
    linear_combination hhalf
  exact (mul_ne_zero hcoef hpow) hzero

theorem iteratedDeriv_one_suzukiFiniteJetLinearCarrier
    (kappa : ℝ) :
    iteratedDeriv 1 (suzukiFiniteJetLinearCarrier kappa) 0 = (kappa : ℂ) := by
  change iteratedDeriv 1 (fun w : ℂ => (kappa : ℂ) * w) 0 = (kappa : ℂ)
  rw [iteratedDeriv_one, deriv_const_mul_id]

/-- No finite anchor jet, even one with nonzero first defect, identifies a strict Schur carrier.
Additional literal-source constraints are not represented in this abstract obstruction. -/
theorem exists_suzukiFiniteJetBlindStrictSchurPair (n : ℕ) (hn : 1 ≤ n) :
    ∃ f g : ℂ → ℂ,
      (∀ w, ‖w‖ < 1 → ‖f w‖ < 1) ∧
      (∀ w, ‖w‖ < 1 → ‖g w‖ < 1) ∧
      (∀ j, j ≤ n → iteratedDeriv j f 0 = iteratedDeriv j g 0) ∧
      (iteratedDeriv 1 f 0 = iteratedDeriv 1 g 0 ∧ iteratedDeriv 1 f 0 ≠ 0) ∧ f ≠ g := by
  refine ⟨suzukiFiniteJetLinearCarrier (1 / 2),
    suzukiFiniteJetPerturbedCarrier (1 / 2) n, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact norm_suzukiFiniteJetLinearCarrier_lt_one (by norm_num) (by norm_num) hw
  · intro w hw
    exact norm_suzukiFiniteJetPerturbedCarrier_lt_one (by norm_num) (by norm_num) hw
  · intro j hj
    exact (suzukiFiniteJetCarriers_same_through hj).symm
  · constructor
    · exact (suzukiFiniteJetCarriers_same_through hn).symm
    · rw [iteratedDeriv_one_suzukiFiniteJetLinearCarrier]
      norm_num
  · exact (suzukiFiniteJetPerturbedCarrier_ne_linearCarrier (by norm_num) n).symm

end RHTower

end
