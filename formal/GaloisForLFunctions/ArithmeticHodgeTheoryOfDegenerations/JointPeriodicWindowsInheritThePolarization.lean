import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.JointPeriodicWindowMass
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCharacterWindowsAreGradedByParity
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheShortWindowsInheritThePolarization
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CompleteWeilCriticalMultipleAndWindowCorollaries

/-!
# Joint periodic windows inherit the polarization

Periodic cancellation controls the low-frequency and pole transforms of every
joint linear combination. A single window above the grid pays its full discrete
mass. The residue-averaged mass Gram matrix supplies a uniform positive floor.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry

private theorem paperFT_centredAtomicTest_riemann {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (x : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    paperFT (cx (centredAtomicTest φ x c N)) (gammaOf s) =
      ((Real.sqrt N : ℝ) : ℂ) * ((c / N : ℝ) : ℂ) *
        paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf s) *
          (((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N x (gammaOf s)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : Real.sqrt N = Real.exp (Real.log N / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN0]
    congr 1
    ring
  have he : Complex.exp (-(Complex.I * gammaOf s * (Real.log N : ℂ))) =
      ((Real.sqrt N : ℝ) : ℂ) * ((N : ℝ) : ℂ) ^ (-s) := by
    rw [hsqrt, Complex.ofReal_exp, RHTower.cpow_ofReal_eq_exp hN0, ← Complex.exp_add]
    congr 1
    rw [gammaOf]
    push_cast
    field_simp
    ring
  rw [paperFT_centredAtomicTest hφ hφc x hc hN, he]
  ring

/-- Uniform low-frequency cancellation bounds the only possibly negative part of the form. -/
private theorem exists_joint_lowFrequency_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ N →
      ∀ x : ℕ → ℝ,
        (∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n = 0) →
      ∀ D : ℝ, 0 ≤ D →
        (∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 + archHorizon (A + 1) →
          ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N x (gammaOf s)‖ ≤ D / N) →
      ∀ U : ℝ, archHorizon (A + 1) ≤ U →
        -(C * D ^ 2) / (N : ℝ) ^ 2 +
          (c * (c / N * ∫ u, φ u ^ 2))⁻¹ *
            ∫ τ in U..(2 * U),
              ‖paperFT (cx (centredAtomicTest φ x c N)) τ‖ ^ 2 *
                nuSymbol (Real.exp (2 * (A + 1))) τ ≤
        c⁻¹ * (weilQuad (atomicTest N x (atomDilate φ (c / N))) /
          ∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hφs
  obtain ⟨Bν, hBν, hQ⟩ := exists_weilQuad_ge_of_lowFrequency (A + 1)
  obtain ⟨Φ, hΦ, hFT⟩ := exists_norm_paperFT_le hφ.continuous hφc (archHorizon (A + 1) + 1)
  refine ⟨(2 + Bν) * Φ ^ 2 / (∫ u, φ u ^ 2), by positivity, ?_⟩
  intro N hN c hc hcN x hx D hD0 hD U hU
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  have hτ0 := archHorizon_nonneg (A + 1)
  let B : ℝ := Real.sqrt N * (c / N) * Φ * (D / N)
  have hB : 0 ≤ B := by positivity
  have hbound (s : ℂ) (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2)
      (hs : ‖s - 1‖ ≤ 1 + archHorizon (A + 1))
      (hz : ‖gammaOf s‖ ≤ archHorizon (A + 1) + 1) :
      ‖paperFT (cx (centredAtomicTest φ x c N)) (gammaOf s)‖ ≤ B := by
    rw [paperFT_centredAtomicTest_riemann hφ.continuous hφc x hc hN,
      norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hw.le]
    have hFT' := hFT (((c / N : ℝ) : ℂ) * gammaOf s) (by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
      exact (mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)).trans (by simpa only [one_mul] using hz))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hFT' (by positivity))
      (hD s hs0 hs2 hs) (norm_nonneg _) (by positivity)
  have hlow : ∀ τ : ℝ, |τ| ≤ archHorizon (A + 1) →
      ‖paperFT (cx (centredAtomicTest φ x c N)) τ‖ ^ 2 ≤ B ^ 2 := by
    intro τ hτ
    have hs : ‖(1 / 2 + Complex.I * τ : ℂ) - 1‖ ≤ 1 + archHorizon (A + 1) := by
      rw [show (1 / 2 + Complex.I * τ - 1 : ℂ) = -(1 / 2) + Complex.I * τ by ring]
      refine (norm_add_le _ _).trans ?_
      simp only [norm_neg, norm_div, norm_one, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs]
      norm_num
      linarith only [hτ]
    have hh := hbound (1 / 2 + Complex.I * τ)
      (by simp) (by simp; norm_num) hs (by
        rw [gammaOf_half_add, Complex.norm_real, Real.norm_eq_abs]
        linarith only [hτ])
    rw [gammaOf_half_add] at hh
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hzero := hbound 0 (by simp) (by simp) (by simpa using (by linarith only [hτ0] : (1 : ℝ) ≤ 1 + archHorizon (A + 1)))
    (by rw [gammaOf_zero]; simp; linarith only [hτ0])
  have hone := hbound 1 (by simp) (by simp) (by simpa using (by linarith only [hτ0] : (0 : ℝ) ≤ 1 + archHorizon (A + 1)))
    (by rw [gammaOf_one]; simp; linarith only [hτ0])
  rw [gammaOf_zero] at hzero
  rw [gammaOf_one] at hone
  have hpole : ‖paperFT (cx (centredAtomicTest φ x c N)) (Complex.I / 2)‖ *
      ‖paperFT (cx (centredAtomicTest φ x c N)) (-Complex.I / 2)‖ ≤ B ^ 2 := by
    simpa only [sq] using mul_le_mul hzero hone (norm_nonneg _) hB
  have hts : tsupport (centredAtomicTest φ x c N) ⊆ Set.Icc (-(A + 1)) (A + 1) :=
    (tsupport_centredAtomicTest_subset hφs hx hc hN).trans
      (Set.Icc_subset_Icc (by linarith only) (by linarith only [hw1, hA]))
  have hform := hQ _ (contDiff_centredAtomicTest hφ x c N) hts (B ^ 2)
    (sq_nonneg _) hlow U hU
  rw [weilQuad_centredAtomicTest] at hform
  have hform' : -((2 + Bν) * B ^ 2) +
      (∫ τ in U..(2 * U), ‖paperFT (cx (centredAtomicTest φ x c N)) τ‖ ^ 2 *
        nuSymbol (Real.exp (2 * (A + 1))) τ) ≤
      weilQuad (atomicTest N x (atomDilate φ (c / N))) := by
    linarith only [hform, hpole]
  have hden : 0 < c * (c / N * ∫ u, φ u ^ 2) := by positivity
  have hdiv := div_le_div_of_nonneg_right hform' hden.le
  have hBnorm : ((2 + Bν) * B ^ 2) / (c * (c / N * ∫ u, φ u ^ 2)) =
      ((2 + Bν) * Φ ^ 2 / (∫ u, φ u ^ 2) * D ^ 2) / (N : ℝ) ^ 2 := by
    dsimp only [B]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hN0.le]
    field_simp
  rw [add_div, neg_div, hBnorm] at hdiv
  rw [integral_atomDilate_sq φ hw]
  simpa only [neg_div, div_eq_mul_inv, mul_inv, inv_inv, neg_mul, mul_neg,
    mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- One fixed dyadic window pays the mass of every packet with the prescribed low-frequency bound. -/
private theorem exists_joint_packet_coercivity {A : ℝ} (hA : 0 ≤ A) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → c ≤ N → ∀ x : ℕ → ℝ,
        (∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n = 0) →
      ∀ D : ℝ, 0 ≤ D →
        (∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 + archHorizon (A + 1) →
          ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N x (gammaOf s)‖ ≤ D / N) →
      a * Real.log N / c ^ (8 : ℝ) * (∑ n ∈ Icc 1 N, x n ^ 2) - C * D ^ 2 / (N : ℝ) ^ 2 ≤
        c⁻¹ * (weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2) := by
  let W₀ : ℝ := Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (9 + 1 : ℕ) * Real.exp (-0)) ^ 8)⁻¹
  let I₀ : ℝ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₀ : 0 < I₀ := integral_tiltedUnitSpline_sq_pos
  have hW₀ : 0 < W₀ := by
    have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
    dsimp only [W₀]
    positivity
  obtain ⟨C, hC, hlow⟩ := exists_joint_lowFrequency_bound contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hA
  refine ⟨W₀ * (1 / (4 * Real.pi)) * 256 / I₀, C, by positivity, hC, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (2 * (0 + 12 + 2 * Real.exp (2 * (A + 1)) ^ 2))
  have harch := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (archHorizon (A + 1))
  filter_upwards [eventually_ge_atTop 1, hlog, harch] with N hN hlogN harchN
  intro c hc1 hcN x hx D hD0 hD
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hc8 : 0 < c ^ (8 : ℝ) := Real.rpow_pos_of_pos hc _
  let U : ℝ := 2 ^ (9 : ℕ) * ((N : ℝ) * Real.exp (-0))
  have hU0 : 0 < U := by positivity
  have hUarch : archHorizon (A + 1) ≤ U := by
    dsimp only [U]
    norm_num
    linarith only [harchN, hN0]
  let S : ℝ := ∑ n ∈ Icc 1 N, x n ^ 2
  have hS : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg _
  let D₂ : ℝ := ∫ τ in U..(2 * U), ‖dirichletPoly N x τ‖ ^ 2
  have hD₂ : 256 * S ≤ D₂ / N := by
    rw [le_div_iff₀ hN0]
    have hMV := integral_window_ge N x U
    have hweighted : (∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2) ≤ (N : ℝ) * S := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun n hn => mul_le_mul_of_nonneg_right
        (by exact_mod_cast (mem_Icc.mp hn).2) (sq_nonneg _)
    change U * S - 208 * (∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2) ≤ D₂ at hMV
    rw [show U = 512 * (N : ℝ) by dsimp only [U]; norm_num] at hMV
    nlinarith only [hMV, hweighted, mul_nonneg hN0.le hS]
  have hfc : HasCompactSupport (centredAtomicTest tiltedUnitSpline x c N) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (tsupport_centredAtomicTest_subset tiltedUnitSpline_support hx hc hN)
  let νm : ℝ := (Real.log (1 + U / 4) - 10) / (2 * Real.pi) -
    Real.exp (2 * (A + 1)) ^ 2 / Real.pi
  have hν : Real.log N / (4 * Real.pi) ≤ νm :=
    nuMin_ge (A := 0) (X := Real.exp (2 * (A + 1))) hN 9 hlogN
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hν0 : 0 ≤ νm := (div_nonneg hlog0 (by positivity)).trans hν
  let Wm : ℝ := Real.sinh 1 ^ 8 / 64 * ((1 + 2 * (c / N) * U) ^ 8)⁻¹
  have hWm0 : 0 ≤ Wm := by positivity
  have hWm : W₀ * (c ^ (8 : ℝ))⁻¹ ≤ Wm := windowWeight_ge hc1 hN 0 9
  let I : ℝ := ∫ τ in U..(2 * U),
    ‖paperFT (cx (centredAtomicTest tiltedUnitSpline x c N)) τ‖ ^ 2 *
      nuSymbol (Real.exp (2 * (A + 1))) τ
  have hI := integral_window_centred_ge hc hN x hfc (2 * (A + 1)) hU0 hν0
  change (c / N) ^ 2 * Wm * νm * D₂ ≤ I at hI
  have hchain : (W₀ * (1 / (4 * Real.pi)) * 256 / I₀) * Real.log N /
      c ^ (8 : ℝ) * S ≤ (c * (c / N * I₀))⁻¹ * I := by
    have he : (c * (c / N * I₀))⁻¹ * ((c / N) ^ 2 * Wm * νm * D₂) =
        Wm * νm * (D₂ / N) / I₀ := by field_simp
    calc (W₀ * (1 / (4 * Real.pi)) * 256 / I₀) * Real.log N / c ^ (8 : ℝ) * S
        = (W₀ * (c ^ (8 : ℝ))⁻¹) * (Real.log N / (4 * Real.pi)) * (256 * S) / I₀ := by ring
      _ ≤ Wm * νm * (D₂ / N) / I₀ := by
        apply div_le_div_of_nonneg_right _ hI₀.le
        exact mul_le_mul (mul_le_mul hWm hν (div_nonneg hlog0 (by positivity)) hWm0)
          hD₂ (mul_nonneg (by norm_num) hS) (mul_nonneg hWm0 hν0)
      _ = (c * (c / N * I₀))⁻¹ * ((c / N) ^ 2 * Wm * νm * D₂) := he.symm
      _ ≤ (c * (c / N * I₀))⁻¹ * I :=
        mul_le_mul_of_nonneg_left hI (by positivity)
  have hform := hlow N hN c hc hcN x hx D hD0 hD U hUarch
  change -(C * D ^ 2) / (N : ℝ) ^ 2 + (c * (c / N * I₀))⁻¹ * I ≤ _ at hform
  dsimp only [S] at hchain
  exact (sub_le_sub_right hchain (C * D ^ 2 / (N : ℝ) ^ 2)).trans
    (by simpa only [neg_div, sub_eq_add_neg, add_comm] using hform)

variable {d : ℕ}

/-- The literal joint packet, retaining every spatial profile and periodic twist. -/
def jointTwistedWeights (g : Fin d → ℝ → ℝ) (χ : Fin d → ℕ → ℝ)
    (N : ℕ) (a : Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ i, a i * twistedWeights (g i) (χ i) N n

private theorem dirichletPoly_jointTwistedWeights (g : Fin d → ℝ → ℝ)
    (χ : Fin d → ℕ → ℝ) (N : ℕ) (a : Fin d → ℝ) (s : ℂ) :
    dirichletPoly N (jointTwistedWeights g χ N a) s =
      ∑ i, (a i : ℂ) * dirichletPoly N (twistedWeights (g i) (χ i) N) s := by
  simp only [dirichletPoly, jointTwistedWeights, Complex.ofReal_sum, Complex.ofReal_mul,
    sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun n _ => by ring

private theorem jointTwistedWeights_eq_zero {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    (χ : Fin d → ℕ → ℝ) (N : ℕ) (a : Fin d → ℝ) :
    ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 →
      jointTwistedWeights g χ N a n = 0 := by
  intro n hn hy
  simp only [jointTwistedWeights, twistedWeights_eq_zero (hgs _) _ N n hn hy,
    mul_zero, sum_const_zero]

private theorem exists_joint_riemann_bound {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hA : 0 ≤ A)
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    {χ : Fin d → ℕ → ℝ} {m : Fin d → ℕ} (hχ : ∀ i, MeanZeroTwist (χ i) (m i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ a : Fin d → ℝ,
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 + archHorizon (A + 1) →
        ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (jointTwistedWeights g χ N a) (gammaOf s)‖ ≤
          C * (∑ i, |a i|) / N := by
  have hp : ∀ i, ∃ B : ℝ, ∃ L : NNReal,
      0 ≤ B ∧ (∀ y, |g i y| ≤ B) ∧ LipschitzWith L (g i) := by
    intro i
    obtain ⟨B, -, hB, -⟩ := exists_bound_lipschitz (hg i) (hgs i)
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
      (hasCompactSupport_of_window (hgs i)) (hg i) (by norm_num)
    exact ⟨B, L, (abs_nonneg _).trans (hB 0), hB, hL⟩
  choose B L hB0 hB hL using hp
  let C₀ (i : Fin d) := 2 * (∑ r ∈ range (m i), |χ i r|) *
    (((L i : NNReal) : ℝ) + (1 + archHorizon (A + 1)) * B i) * Real.exp (2 * A)
  have hC₀ (i : Fin d) : 0 ≤ C₀ i := by
    have hBi := hB0 i
    have hτ := archHorizon_nonneg (A + 1)
    dsimp only [C₀]
    positivity
  refine ⟨∑ i, C₀ i, sum_nonneg fun i _ => hC₀ i, ?_⟩
  intro N hN a s hs0 hs2 hs
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hb (i : Fin d) :
      ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (twistedWeights (g i) (χ i) N) (gammaOf s)‖ ≤
        (∑ j, C₀ j) / N := by
    have hBi := hB0 i
    have hbase := norm_twistedRiemannSum_le (hg i) hA (hgs i) (hB i) (hL i)
      (hχ i) hs0 hs2 hN
    have hstep : 2 * (∑ r ∈ range (m i), |χ i r|) *
        ((((L i : NNReal) : ℝ) + ‖s - 1‖ * B i) * Real.exp (2 * A)) ≤ C₀ i := by
      dsimp only [C₀]
      calc _ ≤ 2 * (∑ r ∈ range (m i), |χ i r|) *
          ((((L i : NNReal) : ℝ) + (1 + archHorizon (A + 1)) * B i) * Real.exp (2 * A)) := by
            gcongr
        _ = _ := by ring
    exact hbase.trans ((div_le_div_of_nonneg_right hstep hN0.le).trans
      (div_le_div_of_nonneg_right (single_le_sum (fun j _ => hC₀ j) (mem_univ i)) hN0.le))
  have he : ((N : ℝ) : ℂ) ^ (-s) *
      dirichletPoly N (jointTwistedWeights g χ N a) (gammaOf s) =
      ∑ i, (a i : ℂ) * (((N : ℝ) : ℂ) ^ (-s) *
        dirichletPoly N (twistedWeights (g i) (χ i) N) (gammaOf s)) := by
    rw [dirichletPoly_jointTwistedWeights, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [he]
  calc ‖∑ i, (a i : ℂ) * (((N : ℝ) : ℂ) ^ (-s) *
        dirichletPoly N (twistedWeights (g i) (χ i) N) (gammaOf s))‖
      ≤ ∑ i, |a i| * ((∑ j, C₀ j) / N) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    _ = (∑ j, C₀ j) * (∑ i, |a i|) / N := by rw [← sum_mul]; ring

/-- Every independent joint periodic family has a coefficient-uniform positive floor
at each positive critical multiple of the tilted-spline scale. -/
theorem jointPeriodic_windows_coercive_at_criticalCurve {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hA : 0 ≤ A)
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    {χ : Fin d → ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hχ : ∀ i, MeanZeroTwist (χ i) M)
    (hlin : LinearIndependent ℝ (jointPeriodicFeature g χ M))
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (8 : ℝ) / Real.log N) atTop (𝓝 K)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop, ∀ v : Fin d → ℝ,
      η * (∑ i, v i ^ 2) ≤
        (c N)⁻¹ * (weilQuad (atomicTest N (jointTwistedWeights g χ N v)
          (atomDilate tiltedUnitSpline (c N / N))) /
            ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  obtain ⟨μ, hμ, hmass⟩ := eventually_jointPeriodic_mass_coercive hg hA hgs hM hχ hlin
  obtain ⟨a, C, ha, hC, hpacket⟩ := exists_joint_packet_coercivity hA
  obtain ⟨B, hB, hRiemann⟩ := exists_joint_riemann_bound hg hA hgs hχ
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc1 N)
  have hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    have hsmall := (criticalCurve_facts_rpow hc1 (by norm_num : (1 : ℝ) ≤ 8) hK hcrit).2.2
    filter_upwards [hsmall.eventually (ge_mem_nhds zero_lt_one), eventually_ge_atTop 1]
      with N hN hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hp : c N ≤ c N ^ ((8 : ℝ) + 1) := by
      calc c N = c N ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hc1 N) (by norm_num)
    exact hp.trans ((div_le_one hN0).mp hN)
  have hgain : Tendsto (fun N : ℕ => (a * μ) * Real.log N / c N ^ (8 : ℝ))
      atTop (𝓝 ((a * μ) / K)) := by
    have h := (hcrit.inv₀ hK.ne').const_mul (a * μ)
    rw [div_eq_mul_inv (a * μ) K]
    refine h.congr fun N => ?_
    rw [inv_div]
    ring
  have hloss : Tendsto (fun N : ℕ => (C * B ^ 2 * (d : ℝ)) / (N : ℝ) ^ 2)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hpos : 0 < (a * μ) / K := div_pos (mul_pos ha hμ) hK
  have hcoef := (hgain.sub hloss).eventually
    (le_mem_nhds (show (a * μ) / K / 2 < (a * μ) / K - 0 by linarith only [hpos]))
  refine ⟨(a * μ) / K / 2, half_pos hpos, ?_⟩
  filter_upwards [hpacket, hmass, hcle, hcoef, eventually_ge_atTop 1]
    with N hN hmassN hcleN hcoefN hN1
  intro v
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hS : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hD : 0 ≤ B * ∑ i, |v i| := mul_nonneg hB (sum_nonneg fun i _ => abs_nonneg _)
  have hQ := hN (c N) (hc1 N) hcleN (jointTwistedWeights g χ N v)
    (jointTwistedWeights_eq_zero hgs χ N v) (B * ∑ i, |v i|) hD
    (hRiemann N hN1 v)
  have hL1 : (∑ i, |v i|) ^ 2 ≤ (d : ℝ) * ∑ i, v i ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin d))
      (fun _ => (1 : ℝ)) (fun i => |v i|)
    simpa only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] using hh
  have hcost : C * (B * ∑ i, |v i|) ^ 2 / (N : ℝ) ^ 2 ≤
      (C * B ^ 2 * (d : ℝ) / (N : ℝ) ^ 2) * ∑ i, v i ^ 2 := by
    calc C * (B * ∑ i, |v i|) ^ 2 / (N : ℝ) ^ 2
        = (C * B ^ 2) * (∑ i, |v i|) ^ 2 / (N : ℝ) ^ 2 := by ring
      _ ≤ (C * B ^ 2) * ((d : ℝ) * ∑ i, v i ^ 2) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL1 (by positivity)) (by positivity)
      _ = _ := by ring
  have hweight : 0 ≤ a * Real.log N / c N ^ (8 : ℝ) :=
    div_nonneg (mul_nonneg ha.le (Real.log_nonneg (by exact_mod_cast hN1)))
      (Real.rpow_pos_of_pos (hc0 N) _).le
  have hpay := mul_le_mul_of_nonneg_left (hmassN v) hweight
  have hη := mul_le_mul_of_nonneg_right hcoefN hS
  dsimp only [jointTwistedWeights] at hQ
  have hid : a * Real.log N / c N ^ (8 : ℝ) * (μ * ∑ i, v i ^ 2) =
      ((a * μ) * Real.log N / c N ^ (8 : ℝ)) * ∑ i, v i ^ 2 := by ring
  rw [hid] at hpay
  linarith only [hQ, hcost, hpay, hη]

/-- The complete Weil Gram matrix on a family with independently varying windows and twists. -/
def jointTwistedGram (g : Fin d → ℝ → ℝ) (χ : Fin d → ℕ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) fun i =>
    cx (atomicTest N (twistedWeights (g i) (χ i) N) (atomDilate tiltedUnitSpline (c / N)))

private theorem jointTwistedGram_real (g : Fin d → ℝ → ℝ) (χ : Fin d → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (i j : Fin d) :
    (jointTwistedGram g χ c N i j).im = 0 := by
  unfold jointTwistedGram weilGram
  rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq
    (contDiff_atomicTest_dilate contDiff_tiltedUnitSpline N _ c)
    (hasCompactSupport_atomicTest_dilate tiltedUnitSpline_support N _ hc hN)
    (contDiff_atomicTest_dilate contDiff_tiltedUnitSpline N _ c)
    (hasCompactSupport_atomicTest_dilate tiltedUnitSpline_support N _ hc hN), Complex.ofReal_im]

private theorem jointTwistedGram_quadratic_real (g : Fin d → ℝ → ℝ) (χ : Fin d → ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (a : Fin d → ℝ) :
    hermQuad (jointTwistedGram g χ c N) (fun i => (a i : ℂ)) =
      weilQuad (atomicTest N (jointTwistedWeights g χ N a) (atomDilate tiltedUnitSpline (c / N))) := by
  have hFi (i : Fin d) := contDiff_atomicTest_dilate contDiff_tiltedUnitSpline N
    (twistedWeights (g i) (χ i) N) c
  have hFic (i : Fin d) := hasCompactSupport_atomicTest_dilate tiltedUnitSpline_support N
    (twistedWeights (g i) (χ i) N) hc hN
  have hlin : (fun u => ∑ i, a i * atomicTest N (twistedWeights (g i) (χ i) N)
      (atomDilate tiltedUnitSpline (c / N)) u) =
      atomicTest N (jointTwistedWeights g χ N a) (atomDilate tiltedUnitSpline (c / N)) := by
    funext u
    simp only [atomicTest, jointTwistedWeights, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun n _ => sum_congr rfl fun i _ => by ring
  have hS : (∑ i, conj (a i : ℂ) • cx (atomicTest N (twistedWeights (g i) (χ i) N)
      (atomDilate tiltedUnitSpline (c / N)))) =
      cx (atomicTest N (jointTwistedWeights g χ N a) (atomDilate tiltedUnitSpline (c / N))) := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.conj_ofReal, cx,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    exact congrArg Complex.ofReal (congrFun hlin u)
  unfold jointTwistedGram
  have hci (i : Fin d) : ContDiff ℝ 2 (cx (atomicTest N
      (twistedWeights (g i) (χ i) N) (atomDilate tiltedUnitSpline (c / N)))) :=
    Complex.ofRealCLM.contDiff.comp (hFi i)
  have hcic (i : Fin d) : HasCompactSupport (cx (atomicTest N
      (twistedWeights (g i) (χ i) N) (atomDilate tiltedUnitSpline (c / N)))) :=
    (hFic i).comp_left Complex.ofReal_zero
  rw [hermQuad_weilGram _ _ hci hcic, hS]
  have hF := contDiff_atomicTest_dilate contDiff_tiltedUnitSpline N (jointTwistedWeights g χ N a) c
  have hFc := hasCompactSupport_atomicTest_dilate tiltedUnitSpline_support N
    (jointTwistedWeights g χ N a) hc hN
  rw [LogCells.weilQuad_eq_zetaW hF hFc]
  exact congrArg Complex.re (RHTower.zeta_W_eq_weilFullFunctional
    (Complex.ofRealCLM.contDiff.comp hF) (hFc.comp_left Complex.ofReal_zero)).symm

/-- The full complex coefficient space inherits a uniform positive floor. -/
theorem jointPeriodic_Gram_coercive_at_criticalCurve {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hA : 0 ≤ A)
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    {χ : Fin d → ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hχ : ∀ i, MeanZeroTwist (χ i) M)
    (hlin : LinearIndependent ℝ (jointPeriodicFeature g χ M))
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (8 : ℝ) / Real.log N) atTop (𝓝 K)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop, ∀ z : Fin d → ℂ,
      η * (∑ i, ‖z i‖ ^ 2) ≤
        ((c N)⁻¹ / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) *
          hermQuad (jointTwistedGram g χ (c N) N) z := by
  obtain ⟨η, hη, hfloor⟩ := jointPeriodic_windows_coercive_at_criticalCurve
    hg hA hgs hM hχ hlin hc1 hK hcrit
  refine ⟨η, hη, ?_⟩
  filter_upwards [hfloor, eventually_ge_atTop 1] with N hfloorN hN
  intro z
  have hc : 0 < c N := zero_lt_one.trans_le (hc1 N)
  have hre := hfloorN (fun i => (z i).re)
  have him := hfloorN (fun i => (z i).im)
  rw [hermQuad_eq_re_add_im (jointTwistedGram_real g χ hc hN),
    jointTwistedGram_quadratic_real g χ hc hN, jointTwistedGram_quadratic_real g χ hc hN]
  have hsplit : (∑ i, ‖z i‖ ^ 2) = (∑ i, (z i).re ^ 2) + ∑ i, (z i).im ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hsplit, mul_add]
  simpa only [mul_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using add_le_add hre him

private theorem jointPeriodicFeature_independent_of_global {g : Fin d → ℝ → ℝ}
    {χ : Fin d → ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hχ : ∀ i, MeanZeroTwist (χ i) M)
    (hlin : LinearIndependent ℝ (fun i (p : ℝ × ℕ) => g i p.1 * χ i p.2)) :
    LinearIndependent ℝ (jointPeriodicFeature g χ M) := by
  rw [Fintype.linearIndependent_iff] at hlin ⊢
  intro a ha
  apply hlin a
  funext p
  have hmod (i : Fin d) : χ i p.2 = χ i (p.2 % M) := by
    have h := (hχ i).apply_add_mul (p.2 % M) (p.2 / M)
    simpa only [Nat.mul_comm, Nat.mod_add_div] using h
  have h := congrFun ha (p.1, ⟨p.2 % M, Nat.mod_lt _ hM⟩)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    jointPeriodicFeature, hmod] using h

/-- Joint periodic families of arbitrary moduli are eventually positive at every canonical
critical multiple. All analytic inputs come from the literal tilted-spline complete Weil form. -/
theorem joint_periodic_windows_inherit_at_every_multiple {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hA : 0 ≤ A)
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    {χ : Fin d → ℕ → ℝ} {m : Fin d → ℕ} (hχ : ∀ i, MeanZeroTwist (χ i) (m i))
    (hlin : LinearIndependent ℝ (fun i (p : ℝ × ℕ) => g i p.1 * χ i p.2))
    {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, (jointTwistedGram g χ (canonicalCriticalCurve K N) N).PosDef := by
  let M := ∏ i, m i
  have hM : 0 < M := prod_pos fun i _ => (hχ i).pos
  have hχM (i : Fin d) : MeanZeroTwist (χ i) M :=
    (hχ i).of_dvd hM (dvd_prod_of_mem m (mem_univ i))
  have hlinM := jointPeriodicFeature_independent_of_global hM hχM hlin
  have hc1 := one_le_canonicalCriticalCurve K
  have hcrit : Tendsto (fun N : ℕ => canonicalCriticalCurve K N ^ (8 : ℝ) / Real.log N)
      atTop (𝓝 K) := by
    refine (tendsto_canonicalCriticalCurve_pow_eight hK).congr fun N => ?_
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  obtain ⟨η, hη, hfloor⟩ := jointPeriodic_Gram_coercive_at_criticalCurve hg hA hgs
    hM hχM hlinM hc1 hK hcrit
  filter_upwards [hfloor, eventually_ge_atTop 1] with N hfloorN hN
  apply posDef_of_hermQuad_pos (weilGram_isHermitian _ _)
  intro z hz
  have hsum : 0 < ∑ i, ‖z i‖ ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hz (funext hn)
    exact (sq_pos_of_pos (norm_pos_iff.mpr hi)).trans_le
      (single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => sq_nonneg _) (mem_univ i))
  have hc : 0 < canonicalCriticalCurve K N := zero_lt_one.trans_le (hc1 N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 < (canonicalCriticalCurve K N)⁻¹ /
      ∫ u, atomDilate tiltedUnitSpline (canonicalCriticalCurve K N / N) u ^ 2 := by
    rw [integral_atomDilate_sq tiltedUnitSpline (div_pos hc hN0)]
    exact div_pos (inv_pos.mpr hc)
      (mul_pos (div_pos hc hN0) integral_tiltedUnitSpline_sq_pos)
  exact pos_of_mul_pos_right ((mul_pos hη hsum).trans_le (hfloorN z)) hscale.le

/-- Character windows of arbitrary nonzero moduli inherit positivity without a parity
restriction. Joint independence is the only nondegeneracy requirement. -/
theorem joint_character_windows_inherit_at_every_multiple {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hA : 0 ≤ A)
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    {q : Fin d → ℕ} [∀ i, NeZero (q i)]
    (z : Fin d → ℂ) (ψ : ∀ i, DirichletCharacter ℂ (q i)) (hψ : ∀ i, ψ i ≠ 1)
    (hlin : LinearIndependent ℝ (fun i (p : ℝ × ℕ) =>
      g i p.1 * charTwist (z i) (ψ i) p.2)) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      (jointTwistedGram g (fun i => charTwist (z i) (ψ i)) (canonicalCriticalCurve K N) N).PosDef :=
  joint_periodic_windows_inherit_at_every_multiple hg hA hgs
    (fun i => meanZeroTwist_charTwist (z i) (hψ i)) hlin hK

/-- Positive definiteness at a single resolution forces independence of the joint
spatial-periodic functions: every relation gives an identically zero atomic test. -/
theorem jointTwistedGram_posDef_implies_joint_independent
    {g : Fin d → ℝ → ℝ} {χ : Fin d → ℕ → ℝ}
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hG : (jointTwistedGram g χ c N).PosDef) :
    LinearIndependent ℝ (fun i (p : ℝ × ℕ) => g i p.1 * χ i p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have ha0 : a = 0 := by
    by_contra hane
    have haz : (fun i => (a i : ℂ)) ≠ 0 := by
      intro hz
      apply hane
      funext i
      exact Complex.ofReal_injective (congrFun hz i)
    have hpos : 0 < hermQuad (jointTwistedGram g χ c N) (fun i => (a i : ℂ)) := by
      have hh := (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 haz
      simpa only [hermQuad, Complex.zero_re] using (Complex.lt_def.mp hh).1
    have hx : jointTwistedWeights g χ N a = 0 := by
      funext n
      have hr := congrFun ha (Real.log n - Real.log N, n)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hr
      calc jointTwistedWeights g χ N a n
          = (∑ i, a i * (g i (Real.log n - Real.log N) * χ i n)) / Real.sqrt n := by
              simp only [jointTwistedWeights, twistedWeights, horizonWeights, sum_div]
              exact sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hr, zero_div]
    have ht : atomicTest N (jointTwistedWeights g χ N a)
        (atomDilate tiltedUnitSpline (c / N)) = (0 : ℝ → ℝ) := by
      funext u
      simp only [hx, atomicTest, Pi.zero_apply, zero_mul, sum_const_zero]
    have hQ0 : weilQuad (0 : ℝ → ℝ) = 0 := by
      change weilPair 0 0 = 0
      have h := weilPair_smul_left 0 (0 : ℝ → ℝ) (0 : ℝ → ℝ)
      simpa only [zero_smul, zero_mul] using h
    rw [jointTwistedGram_quadratic_real g χ hc hN, ht, hQ0] at hpos
    exact (lt_irrefl 0) hpos
  exact fun i => congrFun ha0 i

/-- For arbitrary finite mean-zero periodic families, eventual positivity at any
positive critical multiple is equivalent to joint functional independence. -/
theorem joint_periodic_windows_eventually_posDef_iff {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hA : 0 ≤ A)
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    {χ : Fin d → ℕ → ℝ} {m : Fin d → ℕ} (hχ : ∀ i, MeanZeroTwist (χ i) (m i))
    {K : ℝ} (hK : 0 < K) :
    (∀ᶠ N : ℕ in atTop, (jointTwistedGram g χ (canonicalCriticalCurve K N) N).PosDef) ↔
      LinearIndependent ℝ (fun i (p : ℝ × ℕ) => g i p.1 * χ i p.2) := by
  constructor
  · intro hpos
    obtain ⟨N, hN, hG⟩ := (eventually_ge_atTop 1 |>.and hpos).exists
    exact jointTwistedGram_posDef_implies_joint_independent
      (zero_lt_one.trans_le (one_le_canonicalCriticalCurve K N)) hN hG
  · intro hlin
    exact joint_periodic_windows_inherit_at_every_multiple hg hA hgs hχ hlin hK


#print axioms jointPeriodic_windows_coercive_at_criticalCurve
#print axioms jointPeriodic_Gram_coercive_at_criticalCurve
#print axioms joint_periodic_windows_inherit_at_every_multiple
#print axioms joint_character_windows_inherit_at_every_multiple

#print axioms jointTwistedGram_posDef_implies_joint_independent
#print axioms joint_periodic_windows_eventually_posDef_iff

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
