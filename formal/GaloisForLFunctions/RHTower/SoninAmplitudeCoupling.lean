import GaloisForLFunctions.RHTower.SoninAmplitudeFourier
import GaloisForLFunctions.RHTower.SoninCouplingAdjointLimit
import GaloisForLFunctions.RHTower.SoninCouplingPacketLimit
import GaloisForLFunctions.RHTower.SoninCouplingDilateDistance

/-!
# The Sonin coupling on an arbitrary annulus amplitude

The two-branch estimate and the reversed-product adjoint identity are operator statements: they see
the packet only through two physical cutoffs.  The three vanishing inputs they need — the compact
projection correction, the central Fourier band, and the aperture layer's defect on the dilate —
were all established for a general annulus amplitude.

So the cofinal boundary partial unitary holds verbatim for a discontinuous amplitude.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

namespace AnnulusAmplitude

variable {b c : ℝ} (A : AnnulusAmplitude b c)

/-! ### The dilated packet -/

/-- The inverse dilate of the packet. -/
def ampDilatedPacket (κ r : ℝ) (hr : 0 < r) : evenSubspace :=
  evenDilationCLM r⁻¹ (inv_pos.mpr hr) (A.ampPacketEven κ)

theorem norm_ampDilatedPacket (κ r : ℝ) (hr : 0 < r) :
    ‖A.ampDilatedPacket κ r hr‖ = ‖A.ampPacketEven κ‖ :=
  norm_evenDilationCLM_apply r⁻¹ (inv_pos.mpr hr) (A.ampPacketEven κ)

theorem norm_ampDilatedPacket_le (κ r : ℝ) (hr : 0 < r) :
    ‖A.ampDilatedPacket κ r hr‖ ≤ 2 * ‖A.ampL2‖ := by
  rw [A.norm_ampDilatedPacket κ r hr]
  exact A.norm_ampPacketEven_le κ

theorem evenIndicatorCutoff_ampDilatedPacket_eq_zero (κ r : ℝ) (hr : 0 < r) :
    evenIndicatorCutoff (r * b) (A.ampDilatedPacket κ r hr) = 0 :=
  A.evenIndicatorCutoff_evenDilationCLM_inv_ampPacketEven_eq_zero κ r hr (r * b) le_rfl

/-! ### Band limits in gap form -/

/-- **Low band escape, gap form.** -/
theorem tendsto_norm_evenFourierCutoff_ampPacketEven_gap (t a : ℕ → ℝ)
    (hgap : Tendsto (fun n : ℕ => |a n| - t n) atTop atTop)
    (ha : Tendsto (fun n : ℕ => 2 * Real.pi * a n) atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff (t n)
        (A.ampPacketEven (2 * Real.pi * a n))‖) atTop (𝓝 0) := by
  have hTail := A.tendsto_integral_indicator_outer_ampSpectralDensity
    (fun n : ℕ => |a n| - t n) hgap
  have hMean : Tendsto (fun n : ℕ => A.ampPacketMean (2 * Real.pi * a n)) atTop (𝓝 0) :=
    A.tendsto_ampPacketMean_atTop.comp ha
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | |a n| - t n ≤ |η|}.indicator
              A.ampSpectralDensity η) +
        (A.ampPacketMean (2 * Real.pi * a n)) ^ (2 : ℕ) *
          ∫ η : ℝ, A.ampSpectralDensity η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | |a n| - t n ≤ |η|}.indicator A.ampSpectralDensity η)
        atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ => (A.ampPacketMean (2 * Real.pi * a n)) ^ (2 : ℕ) *
        ∫ η : ℝ, A.ampSpectralDensity η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, A.ampSpectralDensity η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  have hsq : Tendsto (fun n : ℕ => ‖evenFourierCutoff (t n)
      (A.ampPacketEven (2 * Real.pi * a n))‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    exact A.norm_sq_evenFourierCutoff_ampPacketEven_le (t n) (a n)
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **High band capture, gap form.** -/
theorem tendsto_norm_sub_evenFourierCutoff_ampPacketEven_gap (t a : ℕ → ℝ)
    (hgap : Tendsto (fun n : ℕ => t n - |a n|) atTop atTop)
    (ha : Tendsto (fun n : ℕ => 2 * Real.pi * a n) atTop atTop) :
    Tendsto (fun n : ℕ => ‖A.ampPacketEven (2 * Real.pi * a n) -
        evenFourierCutoff (t n) (A.ampPacketEven (2 * Real.pi * a n))‖) atTop (𝓝 0) := by
  have hTail := A.tendsto_integral_indicator_outer_ampSpectralDensity
    (fun n : ℕ => t n - |a n|) hgap
  have hMean : Tendsto (fun n : ℕ => A.ampPacketMean (2 * Real.pi * a n)) atTop (𝓝 0) :=
    A.tendsto_ampPacketMean_atTop.comp ha
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | t n - |a n| ≤ |η|}.indicator
              A.ampSpectralDensity η) +
        (A.ampPacketMean (2 * Real.pi * a n)) ^ (2 : ℕ) *
          ∫ η : ℝ, A.ampSpectralDensity η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | t n - |a n| ≤ |η|}.indicator A.ampSpectralDensity η)
        atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ => (A.ampPacketMean (2 * Real.pi * a n)) ^ (2 : ℕ) *
        ∫ η : ℝ, A.ampSpectralDensity η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, A.ampSpectralDensity η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  have hsq : Tendsto (fun n : ℕ => ‖A.ampPacketEven (2 * Real.pi * a n) -
      evenFourierCutoff (t n) (A.ampPacketEven (2 * Real.pi * a n))‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    exact A.norm_sq_sub_evenFourierCutoff_ampPacketEven_le (t n) (a n)
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-! ### The dilated packet's spectrum -/

/-- The dilated packet has no energy below a fixed aperture. -/
theorem tendsto_norm_evenFourierCutoff_ampDilatedPacket (q a₀ : ℝ) (ha₀ : 0 < a₀) (hq : a₀ < q)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff a₀
        (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n))‖) atTop (𝓝 0) := by
  have hbase := A.tendsto_norm_evenFourierCutoff_ampPacketEven_scaled q a₀ ha₀ hq r hrpos hr
  refine hbase.congr fun n => ?_
  exact (norm_evenFourierCutoff_evenDilationCLM_inv a₀ (r n) (hrpos n)
    (A.ampPacketEven (2 * Real.pi * (r n * q)))).symm

/-- The dilated packet loses no energy above a fixed aperture. -/
theorem tendsto_norm_sub_evenFourierCutoff_ampDilatedPacket (q b₀ : ℝ) (hq : 0 < q)
    (hqb : q < b₀) (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n) -
          evenFourierCutoff b₀
            (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n))‖) atTop (𝓝 0) := by
  have hbase := A.tendsto_norm_sub_evenFourierCutoff_ampPacketEven_scaled q b₀ hq hqb r hrpos hr
  refine hbase.congr fun n => ?_
  exact (norm_sub_evenFourierCutoff_evenDilationCLM_inv b₀ (r n) (hrpos n)
    (A.ampPacketEven (2 * Real.pi * (r n * q)))).symm

/-- Every compact operator dies on the dilated packet family. -/
theorem tendsto_norm_compactOperator_apply_ampDilatedPacket
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (K : evenSubspace →L[ℂ] F) (hK : IsCompactOperator K)
    (κ : ℕ → ℝ) (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop)
    (hb : 0 < b) :
    Tendsto (fun n : ℕ => ‖K (A.ampDilatedPacket (κ n) (r n) (hrpos n))‖) atTop (𝓝 0) :=
  tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero K hK
    (fun n => A.ampDilatedPacket (κ n) (r n) (hrpos n)) (2 * ‖A.ampL2‖)
    (fun n => A.norm_ampDilatedPacket_le (κ n) (r n) (hrpos n))
    (fun n : ℕ => r n * b) (Filter.Tendsto.atTop_mul_const hb hr)
    (fun n => A.evenIndicatorCutoff_ampDilatedPacket_eq_zero (κ n) (r n) (hrpos n))

/-- The exact Sonin projection correction vanishes along the dilated packet family. -/
theorem tendsto_norm_evenSoninProjectionCorrection_apply_ampDilatedPacket
    (t : ℝ) (ht : 0 < t) (hb : 0 < b)
    (κ : ℕ → ℝ) (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninProjectionCorrection t (A.ampDilatedPacket (κ n) (r n) (hrpos n))‖)
      atTop (𝓝 0) :=
  A.tendsto_norm_compactOperator_apply_ampDilatedPacket (evenSoninProjectionCorrection t)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection t ht)) κ r hrpos hr hb

/-! ### The aperture layer on the dilated packet -/

/-- **The aperture layer fixes the dilated packet in the limit.** -/
theorem tendsto_norm_evenSoninApertureLayer_ampDilatedPacket_sub
    (hb : 0 < b) (q a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (haq : a₀ < q) (hqb : q < b₀)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureLayer a₀ b₀
            (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖) atTop (𝓝 0) := by
  have hq : 0 < q := ha₀.trans haq
  have hb₀ : 0 < b₀ := hq.trans hqb
  set v : ℕ → evenSubspace := fun n =>
    A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  have hphysEv : ∀ᶠ n : ℕ in atTop,
      (evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) = 0 := by
    have hrb : Tendsto (fun n : ℕ => r n * b) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hb hr
    filter_upwards [hrb.eventually_ge_atTop b₀] with n hn
    have h1 : evenIndicatorCutoff b₀ (v n) = 0 :=
      A.evenIndicatorCutoff_evenDilationCLM_inv_ampPacketEven_eq_zero
        (2 * Real.pi * (r n * q)) (r n) (hrpos n) b₀ hn
    have h2 : evenIndicatorCutoff a₀ (v n) = 0 :=
      A.evenIndicatorCutoff_evenDilationCLM_inv_ampPacketEven_eq_zero
        (2 * Real.pi * (r n * q)) (r n) (hrpos n) a₀ (by linarith)
    rw [sub_apply, h1, h2, sub_zero]
  have hphys : Tendsto (fun n : ℕ =>
      ‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n)‖) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hphysEv] with n hn
    rw [hn, norm_zero]
  have hlow := A.tendsto_norm_evenFourierCutoff_ampDilatedPacket q a₀ ha₀ haq r hrpos hr
  have hhigh := A.tendsto_norm_sub_evenFourierCutoff_ampDilatedPacket q b₀ hq hqb r hrpos hr
  have hfour : Tendsto (fun n : ℕ =>
      ‖(evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n‖) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖v n - evenFourierCutoff b₀ (v n)‖ + ‖evenFourierCutoff a₀ (v n)‖) atTop (𝓝 0) := by
      simpa using hhigh.add hlow
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    have hsplit : (evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n =
        -(v n - evenFourierCutoff b₀ (v n)) - evenFourierCutoff a₀ (v n) := by
      rw [sub_apply]
      abel
    rw [hsplit]
    calc ‖-(v n - evenFourierCutoff b₀ (v n)) - evenFourierCutoff a₀ (v n)‖
        ≤ ‖-(v n - evenFourierCutoff b₀ (v n))‖ + ‖evenFourierCutoff a₀ (v n)‖ :=
          norm_sub_le _ _
      _ = ‖v n - evenFourierCutoff b₀ (v n)‖ + ‖evenFourierCutoff a₀ (v n)‖ := by
          rw [norm_neg]
  have hcorrA := A.tendsto_norm_evenSoninProjectionCorrection_apply_ampDilatedPacket a₀ ha₀ hb
    (fun n : ℕ => 2 * Real.pi * (r n * q)) r hrpos hr
  have hcorrB := A.tendsto_norm_evenSoninProjectionCorrection_apply_ampDilatedPacket b₀ hb₀ hb
    (fun n : ℕ => 2 * Real.pi * (r n * q)) r hrpos hr
  have hcorr : Tendsto (fun n : ℕ =>
      ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖)
      atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖evenSoninProjectionCorrection a₀ (v n)‖ +
          ‖evenSoninProjectionCorrection b₀ (v n)‖) atTop (𝓝 0) := by
      simpa using hcorrA.add hcorrB
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [sub_apply]
    exact norm_sub_le _ _
  have hgtot : Tendsto (fun n : ℕ =>
      (‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n)‖ +
        ‖(evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n‖) +
        ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖)
      atTop (𝓝 0) := by
    simpa using (hphys.add hfour).add hcorr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgtot
  have hdecomp : evenSoninApertureLayer a₀ b₀ (v n) - v n =
      (evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) +
        ((evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n) +
        (evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n) := by
    rw [evenSoninApertureLayer_eq_shell_add_correctionDiff a₀ b₀]
    simp only [add_apply]
    abel
  rw [hdecomp]
  calc ‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) +
          ((evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n) +
          (evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖
      ≤ ‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) +
            ((evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n)‖ +
          ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖ :=
        norm_add_le _ _
    _ ≤ (‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n)‖ +
            ‖(evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n‖) +
          ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖ := by
        gcongr
        exact norm_add_le _ _

/-- **The outer aperture layer fixes the packet in the limit.** -/
theorem tendsto_norm_evenSoninApertureLayer_ampPacketEven_sub (hb : 0 < b)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureLayer b c (A.ampPacketEven (κ n)) - A.ampPacketEven (κ n)‖)
      atTop (𝓝 0) := by
  have hBand := A.tendsto_norm_evenFourierCutoff_ampPacketEven b κ hκ
  have hCorr := A.tendsto_norm_evenSoninProjectionCorrection_apply_ampPacketEven b hb κ hκ
  have hmaj : Tendsto (fun n : ℕ =>
      ‖evenFourierCutoff b (A.ampPacketEven (κ n))‖ +
        ‖evenSoninProjectionCorrection b (A.ampPacketEven (κ n))‖) atTop (𝓝 0) := by
    simpa using hBand.add hCorr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := A.ampPacketEven (κ n) with hw
  have hhigh : evenIndicatorCutoff c w = w := A.evenIndicatorCutoff_ampPacketEven_eq_self (κ n)
  have hlow : evenIndicatorCutoff b w = 0 := A.evenIndicatorCutoff_ampPacketEven_eq_zero (κ n)
  rw [evenSoninApertureLayer_eq_of_indicatorCutoff_eq_self b c hhigh,
    evenCentralSoninProjection_apply_sub b w, hlow]
  calc ‖-(0 : evenSubspace) - evenFourierCutoff b w + evenSoninProjectionCorrection b w‖
      = ‖-evenFourierCutoff b w + evenSoninProjectionCorrection b w‖ := by
        rw [neg_zero, zero_sub]
    _ ≤ ‖-evenFourierCutoff b w‖ + ‖evenSoninProjectionCorrection b w‖ := norm_add_le _ _
    _ = ‖evenFourierCutoff b w‖ + ‖evenSoninProjectionCorrection b w‖ := by rw [norm_neg]

/-! ### The doubly contracted packet -/

/-- **The outer aperture layer annihilates the doubly contracted packet.** -/
theorem tendsto_norm_evenSoninApertureLayer_ampDoublyContracted
    (hb : 0 < b) (hbc : b < c) (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ) (hsq : ∀ n, 0 < r n ^ (2 : ℕ)) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureLayer b c
          (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))‖) atTop (𝓝 0) := by
  have hc : 0 < c := hb.trans hbc
  set z : ℕ → evenSubspace := fun n =>
    A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n) with hz
  have hA : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hphysEv : ∀ᶠ n : ℕ in atTop,
      (evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) = 0 := by
    filter_upwards [(tendsto_sq_mul_atTop hr hb).eventually_ge_atTop c] with n hn
    have h1 : evenIndicatorCutoff c (z n) = 0 :=
      A.evenIndicatorCutoff_evenDilationCLM_inv_ampPacketEven_eq_zero
        (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n) c hn
    have h2 : evenIndicatorCutoff b (z n) = 0 :=
      A.evenIndicatorCutoff_evenDilationCLM_inv_ampPacketEven_eq_zero
        (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n) b (by linarith)
    rw [sub_apply, h1, h2, sub_zero]
  have hphys : Tendsto (fun n : ℕ =>
      ‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n)‖) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hphysEv] with n hn
    rw [hn, norm_zero]
  have hcap : ∀ t : ℝ, 0 < t → Tendsto (fun n : ℕ => ‖z n - evenFourierCutoff t (z n)‖)
      atTop (𝓝 0) := by
    intro t ht
    have hgapT := tendsto_sq_gap_atTop hr hq ht
    have hbase := A.tendsto_norm_sub_evenFourierCutoff_ampPacketEven_gap
      (fun n : ℕ => r n ^ (2 : ℕ) * t) (fun n : ℕ => r n * q) hgapT hA
    refine hbase.congr fun n => ?_
    exact (norm_sub_evenFourierCutoff_evenDilationCLM_inv t (r n ^ (2 : ℕ)) (hsq n)
      (A.ampPacketEven (2 * Real.pi * (r n * q)))).symm
  have hfour : Tendsto (fun n : ℕ =>
      ‖(evenFourierCutoff c - evenFourierCutoff b) (z n)‖) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖z n - evenFourierCutoff c (z n)‖ + ‖z n - evenFourierCutoff b (z n)‖)
        atTop (𝓝 0) := by
      simpa using (hcap c hc).add (hcap b hb)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    have hsplit : (evenFourierCutoff c - evenFourierCutoff b) (z n) =
        (z n - evenFourierCutoff b (z n)) - (z n - evenFourierCutoff c (z n)) := by
      rw [sub_apply]
      abel
    rw [hsplit]
    calc ‖(z n - evenFourierCutoff b (z n)) - (z n - evenFourierCutoff c (z n))‖
        ≤ ‖z n - evenFourierCutoff b (z n)‖ + ‖z n - evenFourierCutoff c (z n)‖ :=
          norm_sub_le _ _
      _ = ‖z n - evenFourierCutoff c (z n)‖ + ‖z n - evenFourierCutoff b (z n)‖ :=
          add_comm _ _
  have hcorrB := tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero
    (evenSoninProjectionCorrection b)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection b hb)) z (2 * ‖A.ampL2‖)
    (fun n => A.norm_ampDilatedPacket_le (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
    (fun n : ℕ => r n ^ (2 : ℕ) * b) (tendsto_sq_mul_atTop hr hb)
    (fun n => A.evenIndicatorCutoff_ampDilatedPacket_eq_zero
      (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
  have hcorrC := tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero
    (evenSoninProjectionCorrection c)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection c hc)) z (2 * ‖A.ampL2‖)
    (fun n => A.norm_ampDilatedPacket_le (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
    (fun n : ℕ => r n ^ (2 : ℕ) * b) (tendsto_sq_mul_atTop hr hb)
    (fun n => A.evenIndicatorCutoff_ampDilatedPacket_eq_zero
      (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
  have hcorr : Tendsto (fun n : ℕ =>
      ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖)
      atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖evenSoninProjectionCorrection b (z n)‖ +
          ‖evenSoninProjectionCorrection c (z n)‖) atTop (𝓝 0) := by
      simpa using hcorrB.add hcorrC
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [sub_apply]
    exact norm_sub_le _ _
  have hgtot : Tendsto (fun n : ℕ =>
      (‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n)‖ +
        ‖(evenFourierCutoff c - evenFourierCutoff b) (z n)‖) +
        ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖)
      atTop (𝓝 0) := by
    simpa using (hphys.add hfour).add hcorr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgtot
  have hdecomp : evenSoninApertureLayer b c (z n) =
      (evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) +
        (evenFourierCutoff c - evenFourierCutoff b) (z n) +
        (evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n) := by
    rw [evenSoninApertureLayer_eq_shell_add_correctionDiff b c]
    simp only [add_apply]
  rw [hdecomp]
  calc ‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) +
          (evenFourierCutoff c - evenFourierCutoff b) (z n) +
          (evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖
      ≤ ‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) +
            (evenFourierCutoff c - evenFourierCutoff b) (z n)‖ +
          ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖ :=
        norm_add_le _ _
    _ ≤ (‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n)‖ +
            ‖(evenFourierCutoff c - evenFourierCutoff b) (z n)‖) +
          ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖ := by
        gcongr
        exact norm_add_le _ _

/-! ### The cofinal boundary partial unitary -/

/-- **`(12)`.**  Along every clock exceeding the crossing threshold, the coupling carries the
packet to its inverse dilate. -/
theorem tendsto_norm_soninApertureCoupling_ampPacketEven_sub
    (a : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (A.ampPacketEven (2 * Real.pi * (r n * q))) -
          A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖) atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hLayer := A.tendsto_norm_evenSoninApertureLayer_ampDilatedPacket_sub hb q a b
    ha haq hqb r hrpos hr
  have hBand := A.tendsto_norm_evenFourierCutoff_ampPacketEven b
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hCorr := A.tendsto_norm_evenSoninProjectionCorrection_apply_ampPacketEven b hb
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hmaj : Tendsto (fun n : ℕ =>
      2 * ‖evenSoninProjectionCorrection b (A.ampPacketEven (2 * Real.pi * (r n * q)))‖ +
        (‖evenSoninApertureLayer a b
              (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
            A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖ +
          ‖evenFourierCutoff b (A.ampPacketEven (2 * Real.pi * (r n * q)))‖))
      atTop (𝓝 0) := by
    simpa using (hCorr.const_mul (2 : ℝ)).add (hLayer.add hBand)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := A.ampPacketEven (2 * Real.pi * (r n * q)) with hw
  set v : evenSubspace := A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  have hvdef : v = evenDilationCLM (r n)⁻¹ (inv_pos.mpr (hrpos n)) w := rfl
  have hlow : evenIndicatorCutoff b w = 0 :=
    A.evenIndicatorCutoff_ampPacketEven_eq_zero (2 * Real.pi * (r n * q))
  have hhigh : evenIndicatorCutoff c w = w :=
    A.evenIndicatorCutoff_ampPacketEven_eq_self (2 * Real.pi * (r n * q))
  exact norm_soninApertureCoupling_sub_dilate_le hab.le hbc.le (hrgt n) (hcr n) hlow hhigh

/-- **`(13)`.**  The adjoint coupling carries the dilated packet back to the packet. -/
theorem tendsto_norm_adjoint_soninApertureCoupling_ampDilatedPacket_sub
    (a : ℝ) (ha : 0 < a) (hb : 0 < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ (2 : ℕ)) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖ContinuousLinearMap.adjoint
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
            (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          A.ampPacketEven (2 * Real.pi * (r n * q))‖) atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hA : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hInner := A.tendsto_norm_evenSoninApertureLayer_ampDilatedPacket_sub hb q a b
    ha haq hqb r hrpos hr
  have hOuter := A.tendsto_norm_evenSoninApertureLayer_ampPacketEven_sub hb
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hA
  have hDouble := A.tendsto_norm_evenSoninApertureLayer_ampDoublyContracted hb hbc q hq r hsq hr
  have hmaj : Tendsto (fun n : ℕ =>
      2 * ‖evenSoninApertureLayer a b
            (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖ +
        (‖evenSoninApertureLayer b c (A.ampPacketEven (2 * Real.pi * (r n * q))) -
            A.ampPacketEven (2 * Real.pi * (r n * q))‖ +
          ‖evenSoninApertureLayer b c
            (A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))‖))
      atTop (𝓝 0) := by
    simpa using (hInner.const_mul (2 : ℝ)).add (hOuter.add hDouble)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := A.ampPacketEven (2 * Real.pi * (r n * q)) with hw
  set v : evenSubspace := A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  set z : evenSubspace := A.ampDilatedPacket (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n) with hz
  set e : evenSubspace := evenSoninApertureLayer a b v - v with he
  have hadj : ContinuousLinearMap.adjoint
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)) v =
      evenSoninApertureLayer b c
        (evenDilationSum (r n) (hrgt n) (evenSoninApertureLayer a b v)) := by
    rw [adjoint_evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n),
      mul_apply_eq_comp, mul_apply_eq_comp]
  have hDv : evenDilationSum (r n) (hrgt n) v = w + z := by
    rw [hv, hz]
    exact evenDilationSum_evenDilationCLM_inv_apply (r n) (hrgt n) (inv_pos.mpr (hsq n)) w
  have hstep : ContinuousLinearMap.adjoint
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)) v - w =
      evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e) +
        ((evenSoninApertureLayer b c w - w) + evenSoninApertureLayer b c z) := by
    rw [hadj]
    have hlin : evenSoninApertureLayer a b v = v + e := by
      rw [he]; abel
    rw [hlin, map_add, map_add, hDv, map_add]
    abel
  rw [hstep]
  calc ‖evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e) +
          ((evenSoninApertureLayer b c w - w) + evenSoninApertureLayer b c z)‖
      ≤ ‖evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e)‖ +
          ‖(evenSoninApertureLayer b c w - w) + evenSoninApertureLayer b c z‖ :=
        norm_add_le _ _
    _ ≤ 2 * ‖e‖ + (‖evenSoninApertureLayer b c w - w‖ + ‖evenSoninApertureLayer b c z‖) := by
        gcongr
        · calc ‖evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e)‖
              ≤ ‖evenDilationSum (r n) (hrgt n) e‖ :=
                norm_evenSoninApertureLayer_apply_le hbc.le _
            _ ≤ 2 * ‖e‖ := norm_evenDilationSum_apply_le (r n) (hrgt n) e
        · exact norm_add_le _ _

end AnnulusAmplitude

end RHTower

