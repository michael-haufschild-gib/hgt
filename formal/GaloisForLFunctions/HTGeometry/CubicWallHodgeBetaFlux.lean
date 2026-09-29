import GaloisForLFunctions.HTGeometry.CubicWallJetEnergies
import GaloisForLFunctions.RHTower.EulerPrimitivePolarizedHodgeBetaTransgression

/-!
# The double Hellinger law of the nuclear homotopy jets

The factorially normalized homotopy energies of the cubic wall,

`m_n = ‖K_n‖²_HS/((2n)! ‖A‖²_HS) = 105/((2n+3)(2n+5)(2n+7))`,

are the moments `m_n = E[Λⁿ]` of the `Beta(3/2, 3)` Cayley contrast, and factor through the
source-forced Euler odd-Hodge column `h(s) = -Γ(s + 1/2) Γ(3/2)/Γ(s + 2)`:

`m_n = h(n + 1) h(n + 5/2)/(h(1) h(5/2))`,  `m_{n+1}/m_n = q(n + 1) q(n + 5/2)`,

with the coface coefficient `q(s) = (s + 1/2)/(s + 2)`, `h(s + 1) = q(s) h(s)`.  The adjacent
flux `w_n = m_n - m_{n+1} = 630/((2n+3)(2n+5)(2n+7)(2n+9)) = E[(1 - Λ) Λⁿ]` is positive, sums to
one, and reconstructs every jet as its tail, `m_n = ∑_{k ≥ n} w_k`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance factTwoNeTopHodgeBeta : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

local instance isProbabilityMeasure_expMeasure_one_hodgeBeta :
    IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-! ## The homotopy energies -/

/-- **(DHNJ.2).**  `m_n = ‖K_n‖²_HS/((2n)! ‖A‖²_HS)`. -/
def homotopyEnergy (n : ℕ) : ℝ :=
  ContinuousLinearMap.hsNormSq (jetKernel n).op /
    ((2 * n).factorial * ContinuousLinearMap.hsNormSq wallOperator)

/-- **(DHNJ.3).**  `m_n = 105/((2n+3)(2n+5)(2n+7))`. -/
theorem homotopyEnergy_eq (n : ℕ) :
    homotopyEnergy n = 105 / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7)) := by
  rw [homotopyEnergy, hsNormSq_jetKernel, hsNormSq_wallOperator]
  have hf : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  field_simp
  ring

theorem homotopyEnergy_zero : homotopyEnergy 0 = 1 := by
  rw [homotopyEnergy_eq]
  norm_num

theorem homotopyEnergy_pos (n : ℕ) : 0 < homotopyEnergy n := by
  rw [homotopyEnergy_eq]
  positivity

/-- **(DHNJ.3).**  `m_{n+1}/m_n = (n + 3/2)/(n + 9/2)`. -/
theorem homotopyEnergy_succ_div (n : ℕ) :
    homotopyEnergy (n + 1) / homotopyEnergy n = (n + 3 / 2) / (n + 9 / 2) := by
  rw [homotopyEnergy_eq, homotopyEnergy_eq]
  push_cast
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  have h9 : (2 * (n : ℝ) + 9) ≠ 0 := by positivity
  have h92 : ((n : ℝ) + 9 / 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **(DHNJ.1) via the phase jet.**  `‖K_n‖²_HS = (2n)!/n! · (-1)ⁿ F⁽ⁿ⁾(0)`. -/
theorem hsNormSq_jetKernel_eq_phaseJet (n : ℕ) :
    ContinuousLinearMap.hsNormSq (jetKernel n).op
      = (2 * n).factorial / n.factorial * ((-1) ^ n * iteratedDeriv n phaseResponse 0) := by
  rw [hsNormSq_jetKernel, phaseResponse_jet_zero]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-! ## The Hodge–Beta factorization -/

/-- The Hellinger–Beta coface coefficient `q(s) = (s + 1/2)/(s + 2)`. -/
def hodgeCoface (s : ℝ) : ℝ := (s + 1 / 2) / (s + 2)

/-- The Beta function `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`. -/
def gammaBeta (a b : ℝ) : ℝ := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

/-- **The Beta multiplication identity** `B(a, b) B(a + b, c) = B(a, b + c) B(b, c)`. -/
theorem gammaBeta_mul_gammaBeta {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    gammaBeta a b * gammaBeta (a + b) c = gammaBeta a (b + c) * gammaBeta b c := by
  have hab := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hbc := (Real.Gamma_pos_of_pos (add_pos hb hc)).ne'
  have habc := (Real.Gamma_pos_of_pos (add_pos (add_pos ha hb) hc)).ne'
  rw [gammaBeta, gammaBeta, gammaBeta, gammaBeta, show a + (b + c) = a + b + c by ring]
  field_simp

/-- **(DHNJ.4).**  The Euler odd-Hodge column is `h(s) = -B(s + 1/2, 3/2)`. -/
theorem hodgeBetaColumn_eq_neg_gammaBeta {s : ℝ} (hs : -(1 / 2 : ℝ) < s) :
    eulerPrimitiveBoundaryHodgeBetaColumn s = -gammaBeta (s + 1 / 2) (3 / 2) := by
  rw [eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio hs, gammaBeta,
    show s + 1 / 2 + 3 / 2 = s + 2 by ring]

theorem gamma_add_three {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 3) = (x + 2) * (x + 1) * x * Real.Gamma x := by
  rw [show x + 3 = (x + 2) + 1 by ring, Real.Gamma_add_one (by linarith),
    show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
    Real.Gamma_add_one hx.ne']
  ring

/-- `h(s + 1) = q(s) h(s)` for the Euler odd-Hodge column. -/
theorem hodgeBetaColumn_succ {s : ℝ} (hs : -(1 / 2 : ℝ) < s) :
    eulerPrimitiveBoundaryHodgeBetaColumn (s + 1)
      = hodgeCoface s * eulerPrimitiveBoundaryHodgeBetaColumn s := by
  rw [eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio (by linarith),
    eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio hs, hodgeCoface,
    show s + 1 + 1 / 2 = (s + 1 / 2) + 1 by ring, show s + 1 + 2 = (s + 2) + 1 by ring,
    Real.Gamma_add_one (by linarith), Real.Gamma_add_one (by linarith)]
  have h2 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < s + 2 by linarith)).ne'
  have hs2 : s + 2 ≠ 0 := by linarith
  field_simp

theorem hodgeBetaColumn_product (n : ℕ) :
    eulerPrimitiveBoundaryHodgeBetaColumn (n + 1) *
        eulerPrimitiveBoundaryHodgeBetaColumn (n + 5 / 2)
      = Real.Gamma (n + 3 / 2) * Real.Gamma (3 / 2) ^ 2 / Real.Gamma (n + 9 / 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio (by linarith),
    eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio (by linarith),
    show (n : ℝ) + 1 + 1 / 2 = n + 3 / 2 by ring, show (n : ℝ) + 5 / 2 + 1 / 2 = n + 1 + 2 by ring,
    show (n : ℝ) + 5 / 2 + 2 = n + 9 / 2 by ring]
  have h3 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 1 + 2 by linarith)).ne'
  have h9 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 9 / 2 by linarith)).ne'
  field_simp

/-- **(DHNJ.5).**  `m_n = h(n + 1) h(n + 5/2)/(h(1) h(5/2))`. -/
theorem homotopyEnergy_eq_hodgeBeta (n : ℕ) :
    homotopyEnergy n
      = eulerPrimitiveBoundaryHodgeBetaColumn (n + 1) *
          eulerPrimitiveBoundaryHodgeBetaColumn (n + 5 / 2)
        / (eulerPrimitiveBoundaryHodgeBetaColumn 1 *
          eulerPrimitiveBoundaryHodgeBetaColumn (5 / 2)) := by
  have h0 := hodgeBetaColumn_product 0
  simp only [Nat.cast_zero, zero_add] at h0
  rw [hodgeBetaColumn_product, h0, homotopyEnergy_eq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg : Real.Gamma ((n : ℝ) + 9 / 2) = (n + 7 / 2) * (n + 5 / 2) * (n + 3 / 2) *
      Real.Gamma (n + 3 / 2) := by
    rw [show (n : ℝ) + 9 / 2 = (n + 3 / 2) + 3 by ring, gamma_add_three (by linarith)]
    ring
  have hg0 : Real.Gamma (9 / 2) = (7 / 2) * (5 / 2) * (3 / 2) * Real.Gamma (3 / 2) := by
    rw [show (9 / 2 : ℝ) = 3 / 2 + 3 by norm_num, gamma_add_three (by norm_num)]
    ring
  have hp := (Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 3 / 2 by linarith)).ne'
  have hp0 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)).ne'
  rw [hg, hg0]
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  have h3' : ((n : ℝ) + 3 / 2) ≠ 0 := by positivity
  have h5' : ((n : ℝ) + 5 / 2) ≠ 0 := by positivity
  have h7' : ((n : ℝ) + 7 / 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `m_n = B(n + 3/2, 3)/B(3/2, 3)`. -/
theorem homotopyEnergy_eq_gammaBeta (n : ℕ) :
    homotopyEnergy n = gammaBeta (n + 3 / 2) 3 / gammaBeta (3 / 2) 3 := by
  rw [homotopyEnergy_eq, gammaBeta, gammaBeta, show (n : ℝ) + 3 / 2 + 3 = n + 9 / 2 by ring,
    show (3 / 2 : ℝ) + 3 = 9 / 2 by norm_num]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg : Real.Gamma ((n : ℝ) + 9 / 2) = (n + 7 / 2) * (n + 5 / 2) * (n + 3 / 2) *
      Real.Gamma (n + 3 / 2) := by
    rw [show (n : ℝ) + 9 / 2 = (n + 3 / 2) + 3 by ring, gamma_add_three (by linarith)]
    ring
  have hg0 : Real.Gamma (9 / 2) = (7 / 2) * (5 / 2) * (3 / 2) * Real.Gamma (3 / 2) := by
    rw [show (9 / 2 : ℝ) = 3 / 2 + 3 by norm_num, gamma_add_three (by norm_num)]
    ring
  have hp := (Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 3 / 2 by linarith)).ne'
  have hp0 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)).ne'
  have hg3 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 by norm_num)).ne'
  rw [hg, hg0]
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  have h3' : ((n : ℝ) + 3 / 2) ≠ 0 := by positivity
  have h5' : ((n : ℝ) + 5 / 2) ≠ 0 := by positivity
  have h7' : ((n : ℝ) + 7 / 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **(DHNJ.6).**  `m_{n+1}/m_n = q(n + 1) q(n + 5/2)`. -/
theorem homotopyEnergy_succ_div_eq_coface (n : ℕ) :
    homotopyEnergy (n + 1) / homotopyEnergy n = hodgeCoface (n + 1) * hodgeCoface (n + 5 / 2) := by
  rw [homotopyEnergy_succ_div, hodgeCoface, hodgeCoface]
  have h3 : ((n : ℝ) + 1 + 2) ≠ 0 := by positivity
  have h9 : ((n : ℝ) + 5 / 2 + 2) ≠ 0 := by positivity
  have h92 : ((n : ℝ) + 9 / 2) ≠ 0 := by positivity
  field_simp
  ring

/-! ## The positive history flux -/

/-- **(DHNJ.7).**  The adjacent homotopy flux `w_n = m_n - m_{n+1}`. -/
def homotopyFlux (n : ℕ) : ℝ := homotopyEnergy n - homotopyEnergy (n + 1)

theorem homotopyFlux_eq (n : ℕ) :
    homotopyFlux n = 630 / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7) * (2 * n + 9)) := by
  rw [homotopyFlux, homotopyEnergy_eq, homotopyEnergy_eq]
  push_cast
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  have h9 : (2 * (n : ℝ) + 9) ≠ 0 := by positivity
  field_simp
  ring

theorem homotopyFlux_pos (n : ℕ) : 0 < homotopyFlux n := by
  rw [homotopyFlux_eq]
  positivity

theorem tendsto_homotopyEnergy : Tendsto homotopyEnergy atTop (𝓝 0) := by
  rw [show homotopyEnergy = fun n : ℕ => 105 / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7)) from
    funext homotopyEnergy_eq]
  refine tendsto_const_nhds.div_atTop ?_
  refine tendsto_atTop_mono (fun n : ℕ => ?_) tendsto_natCast_atTop_atTop
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn hn, mul_nonneg (mul_nonneg hn hn) hn]

/-- **(DHNJ.8).**  `m_n = ∑_{k ≥ n} w_k`. -/
theorem hasSum_homotopyFlux_tail (n : ℕ) :
    HasSum (fun k => homotopyFlux (n + k)) (homotopyEnergy n) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (homotopyFlux_pos _).le)]
  have hsum : ∀ N, ∑ k ∈ Finset.range N, homotopyFlux (n + k)
      = homotopyEnergy n - homotopyEnergy (n + N) := fun N => by
    simp only [homotopyFlux, add_assoc]
    rw [Finset.sum_range_sub' (fun k => homotopyEnergy (n + k)) N, add_zero]
  simp_rw [hsum]
  have h := (tendsto_homotopyEnergy.comp (tendsto_add_atTop_iff_nat n |>.mpr tendsto_id)).const_sub
    (homotopyEnergy n)
  simpa [Function.comp_def, add_comm] using h

/-- **(DHNJ.8).**  `w_n > 0`, `∑ w_n = 1`. -/
theorem hasSum_homotopyFlux : HasSum homotopyFlux 1 := by
  have h := hasSum_homotopyFlux_tail 0
  simp only [zero_add, homotopyEnergy_zero] at h
  exact h

/-! ## The Beta moment law -/

/-- `∫₀¹ √λ P(λ) dλ = 2 ∫₀¹ v² P(v²) dv`. -/
theorem integral_sqrt_mul_eq {P : ℝ → ℝ} (hP : Continuous P) :
    ∫ s in (0 : ℝ)..1, Real.sqrt s * P s = 2 * ∫ v in (0 : ℝ)..1, v ^ 2 * P (v ^ 2) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := 1)
    (f := fun v : ℝ => v ^ 2) (f' := fun v => 2 * v) (g := fun s : ℝ => Real.sqrt s * P s)
    (fun v _ => by simpa using hasDerivAt_pow 2 v) (by fun_prop)
    ((Real.continuous_sqrt.mul hP).continuousOn)
  simp only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le zero_le_one] at hv
  simp only [Function.comp_apply, Real.sqrt_sq hv.1]
  ring

/-- **The moment law.**  `m_n = E[Λⁿ]` for `Λ ~ Beta(3/2, 3)`. -/
theorem homotopyEnergy_eq_beta_moment (n : ℕ) :
    homotopyEnergy n = ∫ s, s ^ n ∂phaseBetaLaw := by
  rw [integral_phaseBetaLaw]
  simp only [phaseBetaDensity]
  have hP : Continuous fun s : ℝ => (1 - s) ^ 2 * s ^ n := by fun_prop
  have hrw : ∀ s : ℝ, 105 / 16 * (Real.sqrt s * (1 - s) ^ 2) * s ^ n
      = 105 / 16 * (Real.sqrt s * ((1 - s) ^ 2 * s ^ n)) := fun s => by ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_mul_eq hP]
  have hm := phaseResponseMoment_zero n
  have hpt : ∀ v : ℝ, v ^ 2 * ((1 - v ^ 2) ^ 2 * (v ^ 2) ^ n)
      = v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + 0 * v ^ 2) ^ (n + 1) := fun v => by ring
  simp_rw [hpt]
  rw [← phaseResponseMoment, hm, homotopyEnergy_eq]
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  field_simp
  ring

/-- **(DHNJ.9).**  `w_n = E[(1 - Λ) Λⁿ]`: the history lifetime is geometric given `Λ`. -/
theorem homotopyFlux_eq_beta (n : ℕ) :
    homotopyFlux n = ∫ s, (1 - s) * s ^ n ∂phaseBetaLaw := by
  rw [integral_phaseBetaLaw]
  simp only [phaseBetaDensity]
  have hP : Continuous fun s : ℝ => (1 - s) ^ 3 * s ^ n := by fun_prop
  have hrw : ∀ s : ℝ, 105 / 16 * (Real.sqrt s * (1 - s) ^ 2) * ((1 - s) * s ^ n)
      = 105 / 16 * (Real.sqrt s * ((1 - s) ^ 3 * s ^ n)) := fun s => by ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_mul_eq hP]
  have hpt : ∀ v : ℝ, v ^ 2 * ((1 - v ^ 2) ^ 3 * (v ^ 2) ^ n)
      = v ^ (2 * (n + 1)) * (1 - v ^ 2) ^ 3 := fun v => by ring
  simp_rw [hpt]
  rw [integral_pow_mul_one_sub_sq_cube, homotopyFlux_eq]
  push_cast
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  have h9 : (2 * (n : ℝ) + 9) ≠ 0 := by positivity
  field_simp
  ring

/-- **The double Hellinger law.**  The normalized homotopy energies are the Beta moments, factor
through the Euler odd-Hodge column at grades `n + 1` and `n + 5/2`, and are the tails of a positive
unit flux. -/
theorem double_hellinger_homotopy_law :
    (∀ n, ContinuousLinearMap.hsNormSq (jetKernel n).op
        = 48 * (2 * n).factorial / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7))) ∧
      (∀ n, homotopyEnergy n = 105 / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7))) ∧
      homotopyEnergy 0 = 1 ∧
      (∀ n : ℕ, homotopyEnergy (n + 1) / homotopyEnergy n = (n + 3 / 2) / (n + 9 / 2)) ∧
      (∀ n : ℕ, homotopyEnergy n
        = eulerPrimitiveBoundaryHodgeBetaColumn (n + 1) *
            eulerPrimitiveBoundaryHodgeBetaColumn (n + 5 / 2) /
          (eulerPrimitiveBoundaryHodgeBetaColumn 1 *
            eulerPrimitiveBoundaryHodgeBetaColumn (5 / 2))) ∧
      (∀ n : ℕ, homotopyEnergy (n + 1) / homotopyEnergy n
        = hodgeCoface (n + 1) * hodgeCoface (n + 5 / 2)) ∧
      (∀ n, homotopyFlux n = 630 / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7) * (2 * n + 9))) ∧
      (∀ n, 0 < homotopyFlux n) ∧ HasSum homotopyFlux 1 ∧
      (∀ n, HasSum (fun k => homotopyFlux (n + k)) (homotopyEnergy n)) ∧
      (∀ n, homotopyFlux n = ∫ s, (1 - s) * s ^ n ∂phaseBetaLaw) :=
  ⟨hsNormSq_jetKernel, homotopyEnergy_eq, homotopyEnergy_zero, homotopyEnergy_succ_div,
    homotopyEnergy_eq_hodgeBeta, homotopyEnergy_succ_div_eq_coface, homotopyFlux_eq,
    homotopyFlux_pos, hasSum_homotopyFlux, hasSum_homotopyFlux_tail, homotopyFlux_eq_beta⟩

end GaloisForLFunctions.HTGeometry
