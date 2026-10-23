import GaloisForLFunctions.RHTower.SoninScaledPacketFourier

/-!
# Splitting the packet into its two lobes

The profile is the sum of one lobe and its reflection, so the packet is too, and the transform of a
reflected function is the transform at the reflected frequency.  The packet's spectral magnitude is
therefore controlled by one lobe's, read at `±ξ`.

A lobe is a single translate of the reference bump, so its spectral magnitude does not see the
interference between the two lobes — which is where the dependence on the annulus centre sits.

The transform of the packet is therefore the sum of the lobe's transform at `ξ` and at `-ξ`, and its
magnitude is bounded by the two lobe magnitudes.
-/

noncomputable section


namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- One lobe of the annulus profile. -/
def soninOneSidedBump (m δ : ℝ) : ℝ → ℝ := fun x => soninUnitBumpData ((x - m) / δ)

theorem soninScaledAnnulusBump_eq_oneSided_add (m δ : ℝ) (x : ℝ) :
    soninScaledAnnulusBump m δ x = soninOneSidedBump m δ x + soninOneSidedBump m δ (-x) := by
  rw [soninScaledAnnulusBump, soninOneSidedBump, soninOneSidedBump]

/-- One lobe of the modulated packet. -/
def soninOneSidedPacket (m δ κ : ℝ) : ℝ → ℝ := fun x =>
  soninOneSidedBump m δ x * (Real.cos (κ * x) - soninScaledPacketMean m δ κ)

theorem soninScaledPacket_eq_oneSided_add (m δ κ : ℝ) (x : ℝ) :
    soninScaledPacket m δ κ x =
      soninOneSidedPacket m δ κ x + soninOneSidedPacket m δ κ (-x) := by
  rw [soninScaledPacket, soninScaledAnnulusBump_eq_oneSided_add m δ x, soninOneSidedPacket,
    soninOneSidedPacket, show κ * -x = -(κ * x) by ring, Real.cos_neg]
  ring

/-- **Reflection rule for the Fourier integral.** -/
theorem fourier_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (ξ : ℝ) : 𝓕 (fun x : ℝ => f (-x)) ξ = 𝓕 f (-ξ) := by
  rw [← Real.fourierInv_eq_fourier_comp_neg f]
  exact Real.fourierInv_eq_fourier_neg f ξ

/-- A lobe of the packet is integrable. -/
theorem integrable_soninOneSidedPacket (m δ κ : ℝ) (hδ : 0 < δ) :
    Integrable (soninOneSidedPacket m δ κ) := by
  have hcont : Continuous (soninOneSidedPacket m δ κ) := by
    refine Continuous.mul ?_ ?_
    · exact soninUnitBumpData.continuous.comp ((continuous_id.sub continuous_const).div_const δ)
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub continuous_const
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := m - δ) (b := m + δ)) ?_
  intro x hx
  have hbump : soninUnitBumpData ((x - m) / δ) ≠ 0 := by
    intro hzero
    exact hx (by simp [soninOneSidedPacket, soninOneSidedBump, hzero])
  have hball : |(x - m) / δ| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hbump (soninUnitBumpData_eq_zero_of_one_le hcon)
  rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at hball
  rw [Set.mem_Icc]
  rcases abs_lt.mp hball with ⟨h1, h2⟩
  constructor <;> linarith

/-- **The packet's transform is the lobe's transform read at both signs.** -/
theorem fourier_soninScaledPacket_eq_oneSided (m δ κ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) ξ =
      𝓕 (fun x : ℝ => (soninOneSidedPacket m δ κ x : ℂ)) ξ +
        𝓕 (fun x : ℝ => (soninOneSidedPacket m δ κ x : ℂ)) (-ξ) := by
  have hint : Integrable fun x : ℝ => (soninOneSidedPacket m δ κ x : ℂ) :=
    (integrable_soninOneSidedPacket m δ κ hδ).ofReal
  have hrefl : Integrable fun x : ℝ => (fun y : ℝ => (soninOneSidedPacket m δ κ y : ℂ)) (-x) :=
    hint.comp_neg
  have hsplit : (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) =
      fun x : ℝ => (soninOneSidedPacket m δ κ x : ℂ) +
        (fun y : ℝ => (soninOneSidedPacket m δ κ y : ℂ)) (-x) := by
    funext x
    rw [soninScaledPacket_eq_oneSided_add m δ κ x]
    push_cast
    ring
  rw [hsplit, GaloisForLFunctions.HTGeometry.fourierIntegral_add hint hrefl ξ]
  congr 1
  exact fourier_comp_neg (fun y : ℝ => (soninOneSidedPacket m δ κ y : ℂ)) ξ

/-- **The packet's spectrum is dominated by one lobe's.** -/
theorem norm_fourier_soninScaledPacket_le_oneSided (m δ κ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) ξ‖ ≤
      ‖𝓕 (fun x : ℝ => (soninOneSidedPacket m δ κ x : ℂ)) ξ‖ +
        ‖𝓕 (fun x : ℝ => (soninOneSidedPacket m δ κ x : ℂ)) (-ξ)‖ := by
  rw [fourier_soninScaledPacket_eq_oneSided m δ κ hδ ξ]
  exact norm_add_le _ _

end RHTower
