import GaloisForLFunctions.RHTower.CCM.CCMFiniteExponentialFormLift
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFiniteNeumannSource

open Filter Finset
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem source_div_shift_le (a : SuzukiPositiveAperture) (W : ℝ) (hW : 0 ≤ W) :
    W / boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) ≤
      2 * W * Real.exp (-a.1) := by
  have hc := boundedPerturbedFormShift_pos (suzukiWeilIntervalBoundedRemainder a)
  apply (div_le_iff₀ hc).2
  have h := mul_le_mul_of_nonneg_left (exp_aperture_le_twice_suzukiWeilIntervalShift a)
    (mul_nonneg hW (Real.exp_pos (-a.1)).le)
  have he : Real.exp (-a.1) * Real.exp a.1 = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = (W * Real.exp (-a.1)) * Real.exp a.1 := by rw [mul_assoc, he, mul_one]
    _ ≤ (W * Real.exp (-a.1)) *
        (2 * boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)) := h
    _ = _ := by ring

private theorem neumann_budget_band (a : SuzukiPositiveAperture) (W : ℝ) (hW : 0 ≤ W) :
    let C := 2 * (‖ccmArchimedeanRemainderScalar‖ + 46)
    let K := 2 * Real.log C + 10
    let V := C ^ ⌈a.1⌉₊ * W /
      boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
    V ^ 2 / Real.exp (K * a.1) ≤ 4 * C ^ 2 * W ^ 2 * Real.exp (-2 * a.1) := by
  let C := 2 * (‖ccmArchimedeanRemainderScalar‖ + 46)
  let K := 2 * Real.log C + 10
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  let V := C ^ ⌈a.1⌉₊ * W / c
  have hC : 2 ≤ C := by dsimp [C]; linarith [norm_nonneg ccmArchimedeanRemainderScalar]
  have hCp : 0 < C := by linarith
  have hlog : 0 ≤ Real.log C := Real.log_nonneg (by linarith)
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hn : (⌈a.1⌉₊ : ℝ) ≤ a.1 + 1 := (Nat.ceil_lt_add_one a.2.le).le
  have hCN : C ^ ⌈a.1⌉₊ ≤ C * Real.exp (Real.log C * a.1) := by
    calc
      _ = Real.exp ((⌈a.1⌉₊ : ℝ) * Real.log C) := by
        rw [Real.exp_nat_mul, Real.exp_log hCp]
      _ ≤ Real.exp ((a.1 + 1) * Real.log C) := Real.exp_le_exp.mpr (by nlinarith)
      _ = C * Real.exp (Real.log C * a.1) := by
        rw [show (a.1 + 1) * Real.log C = Real.log C + Real.log C * a.1 by ring,
          Real.exp_add, Real.exp_log hCp]
  have hV : V ≤ 2 * C * W * Real.exp ((Real.log C - 1) * a.1) := by
    calc
      _ = C ^ ⌈a.1⌉₊ * (W / c) := by ring
      _ ≤ C ^ ⌈a.1⌉₊ * (2 * W * Real.exp (-a.1)) :=
        mul_le_mul_of_nonneg_left (source_div_shift_le a W hW) (pow_nonneg hCp.le _)
      _ ≤ (C * Real.exp (Real.log C * a.1)) * (2 * W * Real.exp (-a.1)) :=
        mul_le_mul_of_nonneg_right hCN (by positivity)
      _ = _ := by
        rw [show C * Real.exp (Real.log C * a.1) * (2 * W * Real.exp (-a.1)) =
          2 * C * W * (Real.exp (Real.log C * a.1) * Real.exp (-a.1)) by ring,
          ← Real.exp_add]
        congr 2
        ring
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hs : V ^ 2 ≤ (2 * C * W * Real.exp ((Real.log C - 1) * a.1)) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hV0 hV
  have he : (Real.exp ((Real.log C - 1) * a.1)) ^ 2 / Real.exp (K * a.1) =
      Real.exp (-12 * a.1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    dsimp [K]
    ring
  change V ^ 2 / Real.exp (K * a.1) ≤ _
  calc
    _ ≤ (2 * C * W * Real.exp ((Real.log C - 1) * a.1)) ^ 2 / Real.exp (K * a.1) :=
      div_le_div_of_nonneg_right hs (Real.exp_pos _).le
    _ = 4 * C ^ 2 * W ^ 2 * ((Real.exp ((Real.log C - 1) * a.1)) ^ 2 /
        Real.exp (K * a.1)) := by ring
    _ = 4 * C ^ 2 * W ^ 2 * Real.exp (-12 * a.1) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [a.2]))
      (by positivity)

/-- Uniform actual Gamma admission of the finite inverse vector, retaining
its source amplitude for mixed-aperture applications. -/
theorem eventually_ccmFiniteExponentialSource_form_decay :
    ∃ D E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ W : ℝ,
        ‖p‖ ≤ W → CCMFiniteExponentialBudget p.1 W →
        ∃ g : CCMArchimedeanFormDomain ⟨a, ha⟩,
          ccmArchimedeanFormToAperture ⟨a, ha⟩ g = ccmFiniteNeumannVector ⟨a, ha⟩ p ⌈a⌉₊ ∧
          ‖g‖ ^ 2 ≤ D * a * W ^ 2 * Real.exp (-2 * a) ∧
          ‖p - ccmShiftedBoundedWeil ⟨a, ha⟩ (ccmArchimedeanFormToAperture ⟨a, ha⟩ g)‖ ≤
            E * W * Real.exp (-4 * a) := by
  obtain ⟨M, E, hM, hE, happ⟩ := eventually_ccmFiniteExponentialSource_neumann_decay
  let C := 2 * (‖ccmArchimedeanRemainderScalar‖ + 46)
  let K := 2 * Real.log C + 10
  let D := ccmArchimedeanLogComparisonConstant *
    (4 * M ^ 2 * (K + 1) + (2 / Real.pi ^ 2) * (K + 2) * (4 * C ^ 2))
  have hC : 2 ≤ C := by dsimp [C]; linarith [norm_nonneg ccmArchimedeanRemainderScalar]
  have hCp : 0 < C := by linarith
  have hK : 0 < K := by
    have hlog := Real.log_nonneg (show 1 ≤ C by linarith)
    dsimp [K]
    linarith
  have harch : 0 < ccmArchimedeanLogComparisonConstant :=
    zero_lt_one.trans_le one_le_ccmArchimedeanLogComparisonConstant
  refine ⟨D, E, by dsimp [D]; positivity, hE, ?_⟩
  filter_upwards [happ, eventually_ge_atTop (1 : ℝ)] with a haApp haOne
  intro ha p W hpNorm hpBudget
  have hW : 0 ≤ W := hpBudget.nonneg
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let u := ccmFiniteNeumannVector ap p ⌈a⌉₊
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
  let V := C ^ ⌈a⌉₊ * W / c
  let R := Real.exp (K * a)
  have hR : 1 ≤ R := Real.one_le_exp (mul_nonneg hK.le ha.le)
  have hlogR : Real.log R = K * a := Real.log_exp _
  obtain ⟨g, hg, hbound⟩ := (ccmFiniteNeumannVector_budget ap p hpBudget ⌈a⌉₊).exists_ccmFormLift
  refine ⟨g, hg, ?_, ?_⟩
  · have hu : ‖u‖ ≤ 2 * M * W * Real.exp (-a) := by
      calc
        _ ≤ M * W / c := (haApp ha p W hpNorm hpBudget).1
        _ = M * (W / c) := by ring
        _ ≤ M * (2 * W * Real.exp (-a)) :=
          mul_le_mul_of_nonneg_left (source_div_shift_le ap W hW) hM.le
        _ = _ := by ring
    have hu2 : ‖u‖ ^ 2 ≤ 4 * M ^ 2 * W ^ 2 * Real.exp (-2 * a) := by
      have hs : ‖u‖ ^ 2 ≤ (2 * M * W * Real.exp (-a)) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg u) hu
      have hexp : (Real.exp (-a)) ^ 2 = Real.exp (-2 * a) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      exact hs.trans_eq (by rw [mul_pow, hexp]; ring)
    have hV : V ^ 2 / R ≤ 4 * C ^ 2 * W ^ 2 * Real.exp (-2 * a) := neumann_budget_band ap W hW
    have hlow : (1 + Real.log R) * ‖u‖ ^ 2 ≤
        (K + 1) * a * (4 * M ^ 2 * W ^ 2 * Real.exp (-2 * a)) := by
      rw [hlogR]
      apply mul_le_mul (by nlinarith) hu2 (sq_nonneg _) (by positivity)
    have htail : 2 * V ^ 2 * (Real.log R + 2) / (Real.pi ^ 2 * R) ≤
        (2 / Real.pi ^ 2) * ((K + 2) * a) * (4 * C ^ 2 * W ^ 2 * Real.exp (-2 * a)) := by
      rw [hlogR]
      calc
        _ = (2 / Real.pi ^ 2) * (K * a + 2) * (V ^ 2 / R) := by ring
        _ ≤ _ := mul_le_mul
          (mul_le_mul_of_nonneg_left (by nlinarith : K * a + 2 ≤ (K + 2) * a)
            (by positivity)) hV (by positivity) (by positivity)
    calc
      _ ≤ ccmArchimedeanLogComparisonConstant *
          ((1 + Real.log R) * ‖u‖ ^ 2 + 2 * V ^ 2 * (Real.log R + 2) / (Real.pi ^ 2 * R)) :=
        hbound R hR
      _ ≤ ccmArchimedeanLogComparisonConstant *
          ((K + 1) * a * (4 * M ^ 2 * W ^ 2 * Real.exp (-2 * a)) +
            (2 / Real.pi ^ 2) * ((K + 2) * a) * (4 * C ^ 2 * W ^ 2 * Real.exp (-2 * a))) :=
        mul_le_mul_of_nonneg_left (add_le_add hlow htail) harch.le
      _ = _ := by dsimp [D]; ring
  · rw [hg]
    exact (haApp ha p W hpNorm hpBudget).2

/-- The literal finite Neumann approximation has vanishing actual Gamma
energy and an exponentially decaying residual. No response regularity or
form-domain admission is assumed. -/
theorem eventually_ccmMatchedOddNeumannVector_form_decay :
    ∃ D E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
        ∃ g : CCMArchimedeanFormDomain ⟨a, ha⟩,
          ccmArchimedeanFormToAperture ⟨a, ha⟩ g =
            ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊ ∧
          ‖g‖ ^ 2 ≤ D * a * Real.exp (-a) ∧
          ‖ccmMatchedOddPoleSource ⟨a, ha⟩ - ccmShiftedBoundedWeil ⟨a, ha⟩
            (ccmArchimedeanFormToAperture ⟨a, ha⟩ g)‖ ≤ E * Real.exp (-7 * a / 2) := by
  obtain ⟨D, E, hD, hE, hform⟩ := eventually_ccmFiniteExponentialSource_form_decay
  refine ⟨D, E, hD, hE, ?_⟩
  filter_upwards [hform] with a haForm
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  have hp : CCMFiniteExponentialBudget (ccmMatchedOddPoleSource ap : SoninL2)
      (Real.exp (a / 2)) := by
    simpa only [ccmMatchedOddPoleSource, Function.iterate_zero, id_eq, pow_zero, one_mul] using
      ccmNormalizedWeilRemainder_odd_iterate_budget ap 0
  obtain ⟨g, hg, hgNorm, hrNorm⟩ := haForm ha (ccmMatchedOddPoleSource ap)
    (Real.exp (a / 2)) (norm_ccmMatchedOddPoleSource_le ap) hp
  refine ⟨g, hg, ?_, ?_⟩
  · have he : (Real.exp (a / 2)) ^ 2 * Real.exp (-2 * a) = Real.exp (-a) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ D * a * (Real.exp (a / 2)) ^ 2 * Real.exp (-2 * a) := hgNorm
      _ = (D * a) * ((Real.exp (a / 2)) ^ 2 * Real.exp (-2 * a)) := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ E * Real.exp (a / 2) * Real.exp (-4 * a) := hrNorm
      _ = E * Real.exp (-7 * a / 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

end RHTower
end
