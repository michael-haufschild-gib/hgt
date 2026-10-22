import GaloisForLFunctions.RHTower.WallBlockRayTotals
import GaloisForLFunctions.RHTower.WallBlockThreshold
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWallWindowEstimate

/-!
# The one-block estimate

For a profile supported on a single unit block `[m,m+1]` of the position variable, the forced
solution satisfies

`‖u‖₂ ≤ C_{σ,T}(‖c‖ + e^{max(0,−m)}‖g‖₂)`.

The frequency line is cut at the block's threshold `X_m = max(C₀,2)e^{max(0,−m)}` into a window and
two rays.  On the window nothing decays and the estimate costs one power of the window length; on
each ray the profile is the propagated datum plus the four block averages of the two-fold expansion,
and every one of them lands on at most one power of `X_m` squared.

The threshold is where the block's position is absorbed: `max(0,−m) + m = max(m,0) ≥ 0`, so past
`X_m` the logarithmic floor `log(2+|x|)` of the symbol exceeds `1 − m` and the resolvent of the
shifted generator is bounded by one, uniformly over the block.  That exact cancellation is why the
block weight is `e^{max(0,−m)}` and not a higher power of it — and hence why the block series of
Theorem 2 converges.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The composition constant of the window estimate, as a single real. -/
theorem ofReal_window_combination {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (4 : ℝ≥0∞) * (ENNReal.ofReal a + ENNReal.ofReal b) = ENNReal.ofReal (4 * (a + b)) := by
  rw [← ENNReal.ofReal_add ha hb, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **The forced profile on the frequency window.**  Both contributions cost at most one power of
the window length squared. -/
theorem exists_bound_lintegral_sq_forcedProfile_window
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 1 ≤ Y → ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∫⁻ x in Ioo (-Y) Y, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + Y ^ 2 * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨Cl, hCl, hline⟩ := exists_bound_lintegral_sq_line_stripPropagator (T := T) hT hE hσ0 hσ1
  obtain ⟨M, hM, hwinpart⟩ := exists_bound_lintegral_sq_forcedWindowPart (T := T) hT hE hσ0 hσ1
  refine ⟨4 * (Cl + M ^ 2 * (4 * (Real.pi / 2))), by positivity, ?_⟩
  intro Y hY g c m hg2 hsupp
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  set N : ℝ := ∫ L : ℝ, ‖g L‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  have h1 : (∫⁻ x in Ioo (-Y) Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2)
      ≤ ENNReal.ofReal (Cl * ‖c‖ ^ 2) :=
    (setLIntegral_le_lintegral _ _).trans (hline c)
  have hmeasb : AEMeasurable (fun t : ℝ => ‖blockSource g m t‖ₑ)
      (volume.restrict (Ioo (-Y) Y)) :=
    ((aestronglyMeasurable_blockSource hg2 hsupp).restrict).enorm
  have h3 : (∫⁻ t in Ioo (-Y) Y, ‖blockSource g m t‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((Real.pi / 2) * N) :=
    (setLIntegral_le_lintegral _ _).trans
      (le_of_eq (lintegral_enorm_sq_blockSource hg2 hsupp))
  have h2 : (∫⁻ x in Ioo (-Y) Y, ‖forcedWindowPart E T (blockSource g m) σ x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (M ^ 2 * (4 * (Real.pi / 2)) * (Y ^ 2 * N)) := by
    refine (hwinpart Y hY0.le (blockSource g m) hmeasb).trans ?_
    refine le_trans (mul_le_mul' le_rfl h3) (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  refine (lintegral_sq_forcedProfile_window_le hEdiff hE hEne hσ0 hσ1 (b := blockSource g m)
    (Y := Y) c).trans ?_
  refine le_trans (mul_le_mul' le_rfl (add_le_add h1 h2)) ?_
  rw [ofReal_window_combination (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have t1 : (0 : ℝ) ≤ Cl * (Y ^ 2 * N) := by positivity
  have t2 : (0 : ℝ) ≤ M ^ 2 * Real.pi * ‖c‖ ^ 2 := by positivity
  nlinarith [t1, t2]

/-- **The forced profile on the whole frequency line**, cut at a threshold that opens the floor. -/
theorem exists_bound_lintegral_sq_forcedProfile_block
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 1 < Y → ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → StronglyMeasurable g →
      (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∀ t : ℝ, Y ≤ |t| → ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ t + L) →
      (∫⁻ x : ℝ, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + Y ^ 2 * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨Cw, hCw, hwin⟩ :=
    exists_bound_lintegral_sq_forcedProfile_window hEdiff hE hEne hT hσ0 hσ1
  obtain ⟨Cn, hCn, hneg⟩ :=
    exists_bound_lintegral_sq_forcedProfile_negRay hEdiff hE hEne hT hσ0 hσ1
  obtain ⟨Cp, hCp, hpos⟩ :=
    exists_bound_lintegral_sq_forcedProfile_ray hEdiff hE hEne hT hσ0 hσ1
  refine ⟨Cw + Cn + Cp, by positivity, ?_⟩
  intro Y hY1 g c m hg2 hgm hsupp hfloor
  set N : ℝ := ∫ L : ℝ, ‖g L‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  have hS0 : (0 : ℝ) ≤ ‖c‖ ^ 2 + Y ^ 2 * N := by positivity
  refine (lintegral_sq_of_window_and_rays
    (hwin Y hY1.le g c m hg2 hsupp)
    (hneg Y hY1 g c m hg2 hgm hsupp hfloor)
    (hpos Y hY1 g c m hg2 hgm hsupp hfloor)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- **`(11)`: the one-block estimate.** -/
theorem exists_bound_lintegral_sq_forcedProfile_oneBlock
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → StronglyMeasurable g →
      (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∫⁻ x : ℝ, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
        ≤ ENNReal.ofReal
            (C * (‖c‖ ^ 2 + Real.exp (2 * max 0 (-m)) * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨C, hC, hblock⟩ := exists_bound_lintegral_sq_forcedProfile_block hEdiff hE hEne hT hσ0 hσ1
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_threshold_wallFloor T σ 1
  refine ⟨C * (1 + max C₀ 2 ^ 2), by positivity, ?_⟩
  intro g c m hg2 hgm hsupp
  set N : ℝ := ∫ L : ℝ, ‖g L‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  have hbase := hblock (blockThreshold C₀ m) (one_lt_blockThreshold C₀ m) g c m hg2 hgm hsupp
    (fun t ht L hL => blockThreshold_floor (T := T) (σ := σ) hC₀ t ht L hL)
  refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [sq_blockThreshold, ← hNdef]
  have hexp : (0 : ℝ) < Real.exp (2 * max 0 (-m)) := Real.exp_pos _
  have t1 : (0 : ℝ) ≤ C * (Real.exp (2 * max 0 (-m)) * N) := by positivity
  have t2 : (0 : ℝ) ≤ C * (max C₀ 2 ^ 2 * ‖c‖ ^ 2) := by positivity
  nlinarith [t1, t2]

end GaloisForLFunctions.RHTower
