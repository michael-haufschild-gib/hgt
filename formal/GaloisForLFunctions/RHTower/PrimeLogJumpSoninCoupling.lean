import GaloisForLFunctions.RHTower.SoninAmplitudeCoupling
import GaloisForLFunctions.RHTower.PrimeLogJumpPacket

/-!
# The prime-log jump shell as a Sonin carrier

The two-prime jump shell is an annulus amplitude: even, measurable, bounded by one, supported in the
strict annulus `A < |x| < B`, of mass `2 (B − A)`.  So the whole cofinal coupling architecture
applies to it, and the discontinuous essential-phase packet reaches the Sonin boundary partial
unitary exactly as the smooth one does.

Away from the zero frequency the amplitude's packet is literally the jump packet, so the boundary
limits and the Mellin boundary trace are statements about one and the same family.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Filter
open scoped Topology
open _root_.RHTower

variable {A B : ℝ}

/-- The prime-log jump shell, as an annulus amplitude. -/
def jumpAmplitude (A B : ℝ) (hA : 0 < A) (hAB : A < B) : AnnulusAmplitude A B where
  toFun := jumpShell A B
  measurable' := Measurable.indicator measurable_const (measurableSet_jumpShellSet A B)
  even' := fun x => jumpShell_neg hA x
  nonneg' := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  bound := 1
  le_bound' := by
    intro x
    classical
    by_cases hx : x ∈ jumpShellSet A B <;> simp [jumpShell, hx]
  support' := by
    intro x hx
    refine (mem_jumpShellSet_iff hA x).mp ?_
    by_contra hmem
    exact hx (by simp [jumpShell, Set.indicator_of_notMem hmem])
  mass_pos' := by
    rw [integral_jumpShell hA hAB]
    linarith

@[simp] theorem jumpAmplitude_toFun (hA : 0 < A) (hAB : A < B) :
    (jumpAmplitude A B hA hAB).toFun = jumpShell A B := rfl

/-- Away from zero frequency the amplitude's mean is the jump mean. -/
theorem jumpAmplitude_ampPacketMean (hA : 0 < A) (hAB : A < B) {κ : ℝ} (hκ : κ ≠ 0) :
    (jumpAmplitude A B hA hAB).ampPacketMean κ = jumpMean A B κ := by
  have hD : (B - A) ≠ 0 := by
    intro h
    exact absurd (by linarith [sub_eq_zero.mp h] : A = B) (ne_of_lt hAB)
  rw [AnnulusAmplitude.ampPacketMean, jumpAmplitude_toFun, integral_jumpShell hA hAB,
    integral_jumpShell_mul_cos hA hAB hκ, jumpMean]
  field_simp

/-- Away from zero frequency the amplitude's packet is the jump packet. -/
theorem jumpAmplitude_ampPacket (hA : 0 < A) (hAB : A < B) {κ : ℝ} (hκ : κ ≠ 0) :
    (jumpAmplitude A B hA hAB).ampPacket κ = jumpPacket A B κ := by
  funext x
  rw [AnnulusAmplitude.ampPacket, jumpAmplitude_toFun,
    jumpAmplitude_ampPacketMean hA hAB hκ, jumpPacket]

/-- **`(12)`.**  Along every cofinal clock crossing the aperture flag, the Sonin successive-layer
coupling carries the jump packet to its inverse dilate. -/
theorem tendsto_norm_soninApertureCoupling_jumpPacket_sub
    (hA : 0 < A) (hAB : A < B) (a : ℝ) (ha : 0 < a) (haA : a < A) (q : ℝ)
    (haq : a < q) (hqA : q < A)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, B ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a A B (r n) (hrgt n)
            ((jumpAmplitude A B hA hAB).ampPacketEven (2 * Real.pi * (r n * q))) -
          (jumpAmplitude A B hA hAB).ampDilatedPacket
            (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖) atTop (𝓝 0) :=
  (jumpAmplitude A B hA hAB).tendsto_norm_soninApertureCoupling_ampPacketEven_sub a ha hA haA
    hAB q haq hqA r hrpos hrgt hcr hr

/-- **`(13)`.**  The adjoint coupling carries the dilated jump packet back to the jump packet. -/
theorem tendsto_norm_adjoint_soninApertureCoupling_jumpDilatedPacket_sub
    (hA : 0 < A) (hAB : A < B) (a : ℝ) (ha : 0 < a) (q : ℝ)
    (haq : a < q) (hqA : q < A)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ (2 : ℕ)) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖ContinuousLinearMap.adjoint
            (evenSoninApertureSuccessiveLayerTransition a A B (r n) (hrgt n))
            ((jumpAmplitude A B hA hAB).ampDilatedPacket
              (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          (jumpAmplitude A B hA hAB).ampPacketEven (2 * Real.pi * (r n * q))‖) atTop (𝓝 0) :=
  (jumpAmplitude A B hA hAB).tendsto_norm_adjoint_soninApertureCoupling_ampDilatedPacket_sub
    a ha hA hAB q haq hqA r hrpos hrgt hsq hr

end GaloisForLFunctions.RHTower
