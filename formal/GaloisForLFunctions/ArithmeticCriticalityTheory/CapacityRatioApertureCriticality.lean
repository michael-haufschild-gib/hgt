import GaloisForLFunctions.ArithmeticCriticalityTheory.ZeroFormJumpKernelGaugeFreedom
import GaloisForLFunctions.RHTower.WeilMarkovPoleCapacity
import GaloisForLFunctions.RHTower.EulerMaclaurinCountertermQuadratureAndOneSidedPBAP

/-!
# The odd-sector capacity ratio is asymptotically critical in the aperture

In the finite-aperture Weil–Markov–pole splitting `W(g) = M_N(g) + C(g)²/2 − S(g)²/2`
(`RHTower.WeilMarkovPole.weil_eq_markovForm_add_pole`, `S(g) = ∫ 2 sinh(u/2) g`), the Markov part at
any prime aperture beyond the autocorrelation support is the Markov energy
(`markovForm_eq_markovEnergy`). On odd tests RH is the **capacity inequality**
`S(g)² ≤ 2 M(g)` (`riemannHypothesis_iff_forall_odd_capacity_le`), the zero form of the theory.

**Theorem** (`tendsto_capacityRatio_spanPlateau`). For every finite superposition of shifted ground
states with pole coefficient `σ ≠ 0`, the plateau truncations `g_L = M u_L` have

    S(g_L)² / (2 M(g_L))  →  1,

both numerator and denominator converging at rate `e^{−8L}` (`S → 2σ`, `M → 2σ²`). Hence the capacity
ratio over odd tests of aperture `R` tends to the critical value one as `R → ∞`
(`exists_odd_capacityRatio_gt`): the capacity inequality has no uniform margin at large aperture, at
every admissible prime aperture `N` (`exists_odd_capacityRatio_markovForm_gt`). The extremal directions
are the plateau truncations of positive odd gauges, whose capacity defect is the zero form
`J_M + V_μ → 0`; this is the criticality of the odd form read in the capacity normalisation.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The Markov part of the Weil splitting is the Markov energy -/

theorem sinhPairing_eq_two_mul_oddPoleMoment (g : ℝ → ℝ) :
    RHTower.WeilMarkovPole.sinhPairing g = 2 * oddPoleMoment g := by
  unfold RHTower.WeilMarkovPole.sinhPairing oddPoleMoment
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

theorem coshPairing_eq_two_mul_evenPoleMoment (g : ℝ → ℝ) :
    RHTower.WeilMarkovPole.coshPairing g = 2 * evenPoleMoment g := by
  unfold RHTower.WeilMarkovPole.coshPairing evenPoleMoment
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

/-- **Bridge.** At every prime aperture `N` beyond the autocorrelation support, the Markov part
`M_N(g) = V_N ‖g‖² + J_Lévy(g) + J_prime,N(g)` of the Weil splitting is the Markov energy. -/
theorem markovForm_eq_markovEnergy {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {N : ℕ} (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    RHTower.WeilMarkovPole.markovForm N g = markovEnergy (fun u => (g u : ℂ)) := by
  have h1 := RHTower.WeilMarkovPole.weil_eq_markovForm_add_pole hg hgc hN
  have h2 := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hg.continuous hgc
  have hc := coshPairing_eq_two_mul_evenPoleMoment g
  have hs := sinhPairing_eq_two_mul_oddPoleMoment g
  have hcm : coshHalfMoment g = evenPoleMoment g := rfl
  have hsm : sinhHalfMoment g = oddPoleMoment g := rfl
  unfold markovEnergy
  rw [Complex.sub_re, h1, h2, hc, hs, hcm, hsm]
  ring

/-! ### The capacity inequality is RH -/

/-- **RH is the odd capacity inequality** `S(Φv)² ≤ 2 M(Φv)` for every odd `v ∈ C²_c`. -/
theorem riemannHypothesis_iff_forall_odd_capacity_le :
    RiemannHypothesis ↔ ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
      RHTower.WeilMarkovPole.sinhPairing (phiDoobTest v) ^ 2 ≤
        2 * markovEnergy (fun x => (phiDoobTest v x : ℂ)) := by
  rw [riemannHypothesis_iff_forall_odd_zeroForm_nonneg]
  refine forall_congr' fun v => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [sinhPairing_eq_two_mul_oddPoleMoment]
  unfold zeroForm
  constructor <;> intro h <;> nlinarith

/-! ### Asymptotic criticality of the capacity ratio -/

theorem spanPlateauProfile_odd {ι : Type*} (s : Finset ι) (c a : ι → ℝ) (L x : ℝ) :
    spanPlateauProfile s c a L (-x) = -spanPlateauProfile s c a L x := by
  unfold spanPlateauProfile spanGroundState
  rw [smoothPlateau_neg, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftedGroundState_neg]
  ring

/-- **The capacity ratio of plateau truncations tends to one.** For a superposition of shifted
ground states with `σ ≠ 0`, `S(M u_L)²/(2 M(M u_L)) → 1`. -/
theorem tendsto_capacityRatio_spanPlateau {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    (hσ : spanSourceCoefficient s c a ≠ 0) :
    Tendsto (fun L => RHTower.WeilMarkovPole.sinhPairing (phiDoobTest (spanPlateauProfile s c a L)) ^ 2 /
      (2 * markovEnergy (fun x => (phiDoobTest (spanPlateauProfile s c a L) x : ℂ)))) atTop (𝓝 1) := by
  set σ := spanSourceCoefficient s c a
  have hQ := tendsto_markovEnergy_spanPlateauProfile s c a
  obtain ⟨K, -, hK⟩ := abs_oddPoleMoment_spanPlateau_sub_le s c a
  have hP : Tendsto (fun L => oddPoleMoment (phiDoobTest (spanPlateauProfile s c a L))) atTop
      (𝓝 σ) := by
    refine tendsto_of_abs_sub_le (K := K) (Eventually.of_forall fun L => ?_)
    have e : phiDoobTest (spanPlateauProfile s c a L) =
        fun x => spanShiftDifference s c a x * smoothPlateau L x :=
      funext (phiDoobTest_spanPlateauProfile s c a L)
    rw [e]
    exact hK L
  have hS : Tendsto (fun L => RHTower.WeilMarkovPole.sinhPairing
      (phiDoobTest (spanPlateauProfile s c a L)) ^ 2) atTop (𝓝 ((2 * σ) ^ 2)) := by
    simp only [sinhPairing_eq_two_mul_oddPoleMoment]
    exact (hP.const_mul 2).pow 2
  have hlim := hS.div (hQ.const_mul 2) (by positivity)
  have hval : (2 * σ) ^ 2 / (2 * (2 * σ ^ 2)) = 1 := by field_simp
  rwa [hval] at hlim

/-- **No uniform capacity margin at large aperture.** For every `ε > 0` there is `R₀` such that for
every `R ≥ R₀` some odd `v ∈ C²_c`, vanishing outside `[−R, R]`, has `M(Φv) > 0` and
`S(Φv)² > (1 − ε) · 2 M(Φv)`. -/
theorem exists_odd_capacityRatio_gt {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
      (∀ x, v (-x) = -v x) ∧ (∀ x, R < |x| → v x = 0) ∧
      0 < markovEnergy (fun x => (phiDoobTest v x : ℂ)) ∧
      (1 - ε) * (2 * markovEnergy (fun x => (phiDoobTest v x : ℂ))) <
        RHTower.WeilMarkovPole.sinhPairing (phiDoobTest v) ^ 2 := by
  set s : Finset (Fin 1) := Finset.univ
  set c : Fin 1 → ℝ := fun _ => 1
  set a : Fin 1 → ℝ := fun _ => 1
  have hσ : spanSourceCoefficient s c a = Real.sinh (1 / 2) := by
    simp [s, c, a, spanSourceCoefficient]
  have hσ0 : spanSourceCoefficient s c a ≠ 0 := by
    rw [hσ]; exact (Real.sinh_pos_iff.mpr (by norm_num)).ne'
  have hR := tendsto_capacityRatio_spanPlateau s c a hσ0
  have hQ := tendsto_markovEnergy_spanPlateauProfile s c a
  have hQpos : (0 : ℝ) < 2 * spanSourceCoefficient s c a ^ 2 := by positivity
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp
    ((hR.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and (hQ.eventually (lt_mem_nhds hQpos)))
  refine ⟨L₁ + 1, fun R hR => ⟨spanPlateauProfile s c a (R - 1),
    contDiff_spanPlateauProfile s c a (R - 1), hasCompactSupport_spanPlateauProfile s c a (R - 1),
    spanPlateauProfile_odd s c a (R - 1), fun x hx => ?_, ?_⟩⟩
  · unfold spanPlateauProfile
    rw [smoothPlateau_eq_zero (by linarith), mul_zero]
  · obtain ⟨hcap, hpos⟩ := hL₁ (R - 1) (by linarith)
    refine ⟨hpos, ?_⟩
    rwa [lt_div_iff₀ (by linarith)] at hcap

/-- **The same at every admissible prime aperture.** For every `ε > 0` there is `R₀` such that for
every `R ≥ R₀` some odd `v ∈ C²_c` supported in `[−R, R]` has
`S(Φv)² > (1 − ε) · 2 M_N(Φv)` for every prime aperture `N ≥ e^{2R}`. -/
theorem exists_odd_capacityRatio_markovForm_gt {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
      (∀ x, v (-x) = -v x) ∧ (∀ x, R < |x| → v x = 0) ∧ ∀ N : ℕ, Real.exp (2 * R) ≤ N →
        0 < RHTower.WeilMarkovPole.markovForm N (phiDoobTest v) ∧
        (1 - ε) * (2 * RHTower.WeilMarkovPole.markovForm N (phiDoobTest v)) <
          RHTower.WeilMarkovPole.sinhPairing (phiDoobTest v) ^ 2 := by
  obtain ⟨R₀, hR₀⟩ := exists_odd_capacityRatio_gt hε
  refine ⟨max R₀ 0, fun R hR => ?_⟩
  obtain ⟨v, hv, hvc, hodd, hsupp, hpos, hcap⟩ := hR₀ R (le_trans (le_max_left _ _) hR)
  refine ⟨v, hv, hvc, hodd, hsupp, fun N hN => ?_⟩
  have hR0 : 0 ≤ R := le_trans (le_max_right _ _) hR
  have hg : ContDiff ℝ 2 (phiDoobTest v) := contDiff_riemannKernelReal.mul hv
  have hgc : HasCompactSupport (phiDoobTest v) := hvc.mul_left
  have hbeyond : ∀ n : ℕ, N < n → ∀ u, phiDoobTest v u * phiDoobTest v (u + Real.log n) = 0 := by
    intro n hn u
    by_cases hu : |u| ≤ R
    · have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg N) (by exact_mod_cast hn)
      have hlog : 2 * R < Real.log n := by
        rw [Real.lt_log_iff_exp_lt hn0]
        exact lt_of_le_of_lt hN (by exact_mod_cast hn)
      have hfar : R < |u + Real.log n| := by
        rw [abs_of_pos (by linarith [neg_abs_le u])]
        linarith [neg_abs_le u]
      unfold phiDoobTest
      rw [hsupp _ hfar, mul_zero, mul_zero]
    · unfold phiDoobTest
      rw [hsupp u (not_le.mp hu), mul_zero, zero_mul]
  rw [markovForm_eq_markovEnergy hg hgc hbeyond]
  exact ⟨hpos, hcap⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
