import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilGroundEnergyBoundsBoundedPackets
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFlowNeverStalls

/-!
# Step packets retain the aperture mass floor

The flat packets of consecutive unit intervals are orthogonal and each
has unit squared mass. Their full Weil forms therefore have a uniform
positive coefficient-mass floor at every fixed ratio under RH.
-/

noncomputable section

open Finset MeasureTheory Set Zeta23

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart

private theorem flatPacket_mul_eq_zero_of_le {a b c d : ℕ} (hb : 1 ≤ b) (hbc : b ≤ c)
    (u : ℝ) : flatPacket (a : ℝ) b u * flatPacket (c : ℝ) d u = 0 := by
  by_cases h₁ : u ∈ Ioc (Real.log a) (Real.log b)
  · have h₂ : u ∉ Ioc (Real.log c) (Real.log d) := by
      intro h₂
      have hlog : Real.log b ≤ Real.log c :=
        Real.log_le_log (by exact_mod_cast hb) (by exact_mod_cast hbc)
      exact (not_lt_of_ge (h₁.2.trans hlog)) h₂.1
    simp only [flatPacket, indicator_of_notMem h₂, mul_zero]
  · simp only [flatPacket, indicator_of_notMem h₁, zero_mul]

/-- Consecutive logarithmic blocks have exactly unit mass per coefficient. -/
theorem packetAutocorr_stepPacket_zero {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    packetAutocorr (stepPacket R J σ) 0 = ∑ j ∈ range J, σ j ^ 2 := by
  let f : ℕ → ℝ → ℝ := fun j =>
    flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)
  have horth : ∀ i j, i ≠ j → ∀ u, f i u * f j u = 0 := by
    intro i j hij u
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact flatPacket_mul_eq_zero_of_le (by omega) (by omega) u
    · rw [mul_comm]
      exact flatPacket_mul_eq_zero_of_le (by omega) (by omega) u
  have hpoint : ∀ u, stepPacket R J σ u * stepPacket R J σ u =
      ∑ j ∈ range J, σ j ^ 2 * (f j u * f j u) := by
    intro u
    change (∑ j ∈ range J, σ j * f j u) * (∑ j ∈ range J, σ j * f j u) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum, Finset.sum_eq_single j]
    · ring
    · intro i _ hij
      calc (σ j * f j u) * (σ i * f i u) = (σ j * σ i) * (f j u * f i u) := by ring
        _ = 0 := by rw [horth j i hij.symm u, mul_zero]
    · exact fun h => False.elim (h hj)
  have hint : ∀ j ∈ range J, Integrable (fun u => σ j ^ 2 * (f j u * f j u)) := by
    intro j _
    have h := integrable_flatPacket_mul_flatPacket
      ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)
      ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) 0
    simpa only [add_zero, f] using h.const_mul (σ j ^ 2)
  simp only [packetAutocorr, add_zero, hpoint]
  rw [integral_finset_sum _ hint]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  have hm : packetAutocorr (f j) 0 = 1 := by
    have h := packetAutocorr_flatPacket_log_div_exp (a := R + j) (b := R + (j + 1))
      (k := 1) (by omega) (by omega) (by omega)
    simpa [f, Nat.cast_add] using h
  simp only [packetAutocorr, add_zero] at hm
  rw [hm, mul_one]

theorem groundEnergy_mul_nested_mass_le_packetForm
    {ι : Type*} {s : Finset ι} {x : ι → ℕ} {x₀ X Q : ℕ}
    (hx₀ : 1 ≤ x₀) (hQ₀ : 1 ≤ Q) (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X)
    (hQ : X ≤ Q * x₀) (τ : ι → ℝ) {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : Real.log Q < 2 * A.1) :
    _root_.RHTower.ccmRestrictedWeilGroundEnergy A *
        packetAutocorr (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) 0 ≤
      packetForm Q (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) := by
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ₀
  apply groundEnergy_mul_packetAutocorr_le_packetForm
    (M := ∑ j ∈ s, |τ j| * Real.exp (Real.log (x j) / 2))
    (l := Real.log x₀) (r := Real.log x₀ + Real.log Q)
  · exact Finset.measurable_sum _ fun j _ => (measurable_flatPacket _ _).const_mul (τ j)
  · intro u
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_flatPacket_le _ _ _) (abs_nonneg _)
  · intro u hu
    obtain ⟨j, hj, hne⟩ : ∃ j ∈ s, τ j * flatPacket x₀ (x j) u ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hu (Finset.sum_eq_zero hcon)
    have hfp : flatPacket (x₀ : ℝ) (x j) u ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    have hmem : u ∈ Ioc (Real.log x₀) (Real.log (x j)) := by
      by_contra hnot
      exact hfp (by simp only [flatPacket]; exact indicator_of_notMem hnot _)
    have hxj : (x j : ℝ) ≤ (Q : ℝ) * x₀ := by exact_mod_cast (hx j hj).2.trans hQ
    have hxj0 : (0 : ℝ) < x j := hx₀'.trans_le (by exact_mod_cast (hx j hj).1)
    have hlog : Real.log (x j) ≤ Real.log x₀ + Real.log Q := by
      rw [add_comm, ← Real.log_mul hQ'.ne' hx₀'.ne']
      exact Real.log_le_log hxj0 hxj
    exact ⟨hmem.1.le, hmem.2.trans hlog⟩
  · simpa only [add_sub_cancel_left] using hA
  · rw [add_sub_cancel_left]
    exact Real.log_lt_log hQ' (by linarith)
  · exact integrableOn_levyJump_step hx₀ (fun j hj => (hx j hj).1) τ

/-- At a fixed ratio, RH gives one strictly positive floor for every step
packet, independent of its number of blocks. -/
theorem exists_uniform_stepPacket_mass_floor_of_riemannHypothesis
    (hRH : RiemannHypothesis) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R J : ℕ, 1 ≤ R → R + J ≤ Q * R → ∀ σ : ℕ → ℝ,
      δ * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ) := by
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  let A : _root_.RHTower.SuzukiPositiveAperture := ⟨Real.log Q + 1, by positivity⟩
  have hδ :=
    ArithmeticContinuationAndCriticalEnergy.riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos.mp hRH A
  refine ⟨_root_.RHTower.ccmRestrictedWeilGroundEnergy A, hδ, ?_⟩
  intro R J hR hRJ σ
  rw [← packetAutocorr_stepPacket_zero hR J σ]
  simp only [stepPacket_eq_nested hR J σ]
  exact groundEnergy_mul_nested_mass_le_packetForm hR hQ (nested_bounds R J) hRJ
    (nestedCoeff J σ) (by dsimp [A]; linarith only [hlog])

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
