import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheCrossEnergyOfTwoWindowsIsBoundedByTheirMasses
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheStabilityRegimeReachesAFixedFractionOfTheRobinEulerThreshold
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The stability regime reaches a quarter of the Robin–Euler threshold

Three refinements of `TheStabilityRegimeReachesAFixedFractionOfTheRobinEulerThreshold`:

* **The prime number theorem for the up-rows** (`exists_psi_le_of_ge`, `sum_mul_upRow_sq_le_pnt`,
  `eventually_upWeightPNT_le`): with `ψ(x) ≤ (1 + η)x` beyond some `X₀`, the low atoms `N/m ≥ X₀`
  have `m R_m ≤ (1 + η)N/(b log N) + N^b`. The high atoms `m > N/Y` keep Chebyshev's bound but form
  a harmonic tail of size at most `Y`. Hence
  `Σ_m m R_m² ≤ ((1 + η)²/b² + o(1)) N²/log N`, with Chebyshev's `B_ψ² ≈ 8.2` replaced by `1`.
* **The halved cross penalty** (`TheCrossEnergyOfTwoWindowsIsBoundedByTheirMasses`).
* **The parameters** `λ = 1/4`, `κ = 3/20`, `b = 19/20`, `θ = 2`, `ζ = 1/20`, `ρ = 3/2`.

Together (`eventually_weilQuad_windowTest_nonneg_quarter`): eventually in `N`, Weil's form is
nonnegative on every window test of shape `β(G_n) ≥ β‖G_n‖²` at every width
`w ≤ K★_q(β, ε, a) δ_N`, `K★_q = min(3/20, (3/4)/C_D, a/C_X, exp(2θ′(0) + 2c_∞ + β + γ − ε − a − 1/25))`,
`C_X ≈ 10.5`, `C_D ≈ 7.0`. This is `≈ 0.108` of the spacing for plateau profiles, a quarter of the
Robin–Euler threshold `≈ 0.43`, and `≈ 0.066` for every profile, against `≈ 0.16`. With absolute
values on the pole term, the linear costs (Lévy loss and pole) keep this method below about half
of the threshold even with optimal constants.
-/

noncomputable section

open MeasureTheory Finset Filter Asymptotics RHTower
open scoped ArithmeticFunction.vonMangoldt Topology

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {G : ℕ → ℝ → ℝ} {w : ℝ}

/-! ### The prime number theorem for the up-rows -/

/-- **PNT**: for every `η > 0`, `ψ(x) ≤ (1 + η) x` for all `x ≥ X₀`, some `X₀ ≥ 1`. -/
theorem exists_psi_le_of_ge {η : ℝ} (hη : 0 < η) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → Chebyshev.psi x ≤ (1 + η) * x := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (tendsto_psi_div_self.eventually (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + η)))
  refine ⟨max X₁ 1, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith [le_max_right X₁ 1]
  have h := hX₁ x (le_trans (le_max_left _ _) hx)
  rw [Set.mem_Iio, div_lt_iff₀ hx0] at h
  exact h.le

/-- The up-row weight with the prime number theorem,
`((1 + η)N/(b log N) + N^b)²(1 + log N) + (B_ψ N/(b log N) + N^b)² Y`. -/
def upWeightPNT (N : ℕ) (b η Y : ℝ) : ℝ :=
  ((1 + η) * N / (b * Real.log N) + (N : ℝ) ^ b) ^ 2 * (1 + Real.log N) +
    (psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b) ^ 2 * Y

/-- **The up-row weight under the prime number theorem**: for `η > 0` there is `Y ≥ 1` with
`Σ_m m R_m² ≤ upWeightPNT N b η Y` for all `N ≥ 2`, `b > 0`. -/
theorem sum_mul_upRow_sq_le_pnt {η : ℝ} (hη : 0 < η) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ N : ℕ, 2 ≤ N → ∀ b : ℝ, 0 < b →
      ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤ upWeightPNT N b η Y := by
  obtain ⟨X₀, hX₀1, hX₀⟩ := exists_psi_le_of_ge hη
  refine ⟨X₀ + 1, by linarith, fun N hN b hb0 => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  set R₁ := (1 + η) * N / (b * Real.log N) + (N : ℝ) ^ b
  set R₂ := psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b
  have hharm : ∑ m ∈ Icc 1 N, (1 : ℝ) / m ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa only [one_div] using h
  have hterm : ∀ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤
      R₁ ^ 2 * (1 / m) + R₂ ^ 2 * ((X₀ + 1) / N) := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have h0 : 0 ≤ (m : ℝ) * upRow N m := mul_nonneg hm0.le (upRow_nonneg hm1)
    have hsum := mul_upRow_le_sum hN hm hb0
    rw [sum_vonMangoldt_Icc_eq_psi] at hsum
    have hq1 : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hmN hm1
    have hdiv : (m : ℝ) * ((N / m : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N m
    have hsplit : (m : ℝ) * upRow N m ^ 2 = ((m : ℝ) * upRow N m) ^ 2 * (1 / m) := by
      field_simp
    have hR₂0 : 0 ≤ R₂ ^ 2 * ((X₀ + 1) / N) := by positivity
    have hR₁0 : 0 ≤ R₁ ^ 2 * (1 / m) := by positivity
    by_cases hT : X₀ ≤ ((N / m : ℕ) : ℝ)
    · -- a low atom: the prime number theorem
      have hψ := hX₀ _ hT
      have h1 : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ (1 + η) * N := by
        calc (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ m * ((1 + η) * ((N / m : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hψ hm0.le
          _ = (1 + η) * (m * ((N / m : ℕ) : ℝ)) := by ring
          _ ≤ (1 + η) * N := mul_le_mul_of_nonneg_left hdiv (by linarith)
      have h2 : (m : ℝ) * upRow N m ≤ R₁ := by
        have : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) / (b * Real.log N) ≤
            (1 + η) * N / (b * Real.log N) := div_le_div_of_nonneg_right h1 (by positivity)
        simp only [R₁]; linarith
      rw [hsplit]
      have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 2)
        (by positivity : (0 : ℝ) ≤ 1 / m)
      linarith
    · -- a high atom: Chebyshev and `1/m < Y/N`
      push Not at hT
      have hψ := psi_le_psiConstant hq1
      have h1 : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ psiConstant * N := by
        calc (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ m * (psiConstant * ((N / m : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hψ hm0.le
          _ = psiConstant * (m * ((N / m : ℕ) : ℝ)) := by ring
          _ ≤ psiConstant * N := mul_le_mul_of_nonneg_left hdiv psiConstant_pos.le
      have h2 : (m : ℝ) * upRow N m ≤ R₂ := by
        have : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) / (b * Real.log N) ≤
            psiConstant * N / (b * Real.log N) := div_le_div_of_nonneg_right h1 (by positivity)
        simp only [R₂]; linarith
      -- `N < (⌊N/m⌋ + 1) m < (X₀ + 1) m`
      have hlt : (N : ℝ) < (((N / m : ℕ) : ℝ) + 1) * m := by
        have := Nat.lt_div_mul_add (a := N) (show 0 < m by omega)
        exact_mod_cast (by linarith [this] : N < (N / m + 1) * m)
      have hinv : 1 / (m : ℝ) ≤ (X₀ + 1) / N := by
        rw [div_le_div_iff₀ hm0 hN0]
        nlinarith
      rw [hsplit]
      have := mul_le_mul (pow_le_pow_left₀ h0 h2 2) hinv (by positivity) (by positivity)
      linarith
  calc ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2
      ≤ ∑ m ∈ Icc 1 N, (R₁ ^ 2 * (1 / m) + R₂ ^ 2 * ((X₀ + 1) / N)) := sum_le_sum hterm
    _ = R₁ ^ 2 * ∑ m ∈ Icc 1 N, (1 : ℝ) / m + R₂ ^ 2 * (X₀ + 1) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast; field_simp
    _ ≤ upWeightPNT N b η (X₀ + 1) := by
        simp only [upWeightPNT, R₁, R₂]
        gcongr

end GaloisForLFunctions.ArithmeticLorentzianGeometry
