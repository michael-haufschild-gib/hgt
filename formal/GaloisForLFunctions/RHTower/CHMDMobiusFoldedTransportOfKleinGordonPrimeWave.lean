import GaloisForLFunctions.RHTower.CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection

/-!
# The Klein–Gordon prime transport as a folded Möbius–kernel pairing

Let `T(y) = Σ_n (Λ(n)/√n) K_y(log n) − ∫_0^∞ K_y(s) e^{s/2} ds` be the Klein–Gordon transport of
the Chebyshev discrepancy measure, `f_y = e^{−s/2}K_y` the conjugated kernel and
`S(u) = e^u H(⌊e^u⌋) − ⌊e^u⌋ − Σ_{k ≤ e^u} log k (u − log k)` the elementary dilation source of the
integrated Chebyshev deficit, so that `D(s) = Σ_{m ≤ e^s} μ(m) S(s − log m)`.

Folding the Möbius reconstruction into the conjugated transport identity gives the exact,
absolutely convergent Möbius series

`T(y) = K_y(0) − Σ_m μ(m) Φ_y(log m)`,  `Φ_y(v) = ∫_0^∞ S(u) f_y''(u + v) du`,

in which the von Mangoldt weights no longer appear.  Splitting
`S(u) = (γ+1)(e^u − 1) − (log 2π/2) u + R(u)` with the uniformly bounded centered remainder
`|R| ≤ 7/2`, the fold is

`Φ_y(v) = (γ + 1 − log(2π)/2) f_y(v) + (γ+1) e^{−v} ∫_v^∞ K_y(s) e^{s/2} ds + ∫_0^∞ R(u) f_y''(u+v) du`,

so the transport is `K_y(0)` minus a constant times the Möbius Klein–Gordon wave
`Σ_m μ(m) m^{−1/2} K_y(log m)`, minus `(γ+1)` times the pairing of `K_y e^{s/2}` with the Mertens
sum `Σ_{m ≤ e^s} μ(m)/m`, minus the remainder fold series.  The pole wave has cancelled on every
divisor fibre; the remainder fold is bounded by `7 C e^{−v/2}` uniformly in the time `y`.  The
Riemann hypothesis is equivalent to a one-sided bound on the sum of the three Möbius pieces.  No
such bound is produced.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Section 1: the elementary dilation source on the forward half-line -/

/-- The elementary dilation source vanishes at the origin. -/
theorem ccmPrimeDeficitDilationSource_zero : ccmPrimeDeficitDilationSource 0 = 0 := by
  unfold ccmPrimeDeficitDilationSource
  simp

/-- The constant `7/2 + 5/3 + log(2π)/2` dominating `e^{−u} S(u)` on the forward half-line. -/
def sourceBound : ℝ := 7 / 2 + 5 / 3 + Real.log (2 * π) / 2

theorem log_two_pi_nonneg : 0 ≤ Real.log (2 * π) :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

theorem sourceBound_nonneg : 0 ≤ sourceBound := by
  unfold sourceBound
  linarith [log_two_pi_nonneg]

/-- The elementary source is the explicit pole/Stirling part plus the centered remainder. -/
theorem ccmPrimeDeficitDilationSource_eq (u : ℝ) :
    ccmPrimeDeficitDilationSource u =
      (Real.eulerMascheroniConstant + 1) * (Real.exp u - 1) - Real.log (2 * π) / 2 * u +
        ccmPrimeDeficitDilationRemainder u := by
  unfold ccmPrimeDeficitDilationRemainder
  ring

/-- `|S(u)| ≤ sourceBound · e^u` for `u ≥ 0`. -/
theorem abs_ccmPrimeDeficitDilationSource_le {u : ℝ} (hu : 0 ≤ u) :
    |ccmPrimeDeficitDilationSource u| ≤ sourceBound * Real.exp u := by
  rw [ccmPrimeDeficitDilationSource_eq]
  have hR := abs_ccmPrimeDeficitDilationRemainder_le_uniform hu
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ' := Real.one_half_lt_eulerMascheroniConstant
  have he1 : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hue : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hl := log_two_pi_nonneg
  unfold sourceBound
  rw [abs_le]
  obtain ⟨hRa, hRb⟩ := abs_le.mp hR
  constructor <;> nlinarith [mul_nonneg hl hu, mul_le_mul_of_nonneg_left hue (by positivity : (0:ℝ) ≤ Real.log (2 * π) / 2)]

theorem measurable_ccmPrimeDeficitDilationSource_shift (ℓ : ℝ) :
    Measurable fun s : ℝ => ccmPrimeDeficitDilationSource (s - ℓ) :=
  measurable_ccmPrimeDeficitDilationSource.comp (measurable_id.sub measurable_const)

/-! ## Section 2: translation of half-line integrals -/

/-- `∫_ℓ^∞ g(s) ds = ∫_0^∞ g(u + ℓ) du`. -/
theorem setIntegral_Ioi_shift (g : ℝ → ℝ) (ℓ : ℝ) :
    ∫ s in Ioi ℓ, g s = ∫ u in Ioi (0 : ℝ), g (u + ℓ) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun s => (Ioi ℓ).indicator g s) ℓ]
  congr 1
  funext u
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases h : 0 < u
  · rw [if_pos (by linarith), if_pos h]
  · rw [if_neg (by linarith), if_neg h]

/-! ## Section 3: the folded Möbius kernel -/

/-- The folded Möbius kernel `Φ_y(v) = ∫_0^∞ S(u) f_y''(u + v) du`. -/
def mobiusFold (y v : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), ccmPrimeDeficitDilationSource u * conjugatedLaplacian y (u + v)

/-- The remainder fold `∫_0^∞ R(u) f_y''(u + v) du`. -/
def remainderFold (y v : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), ccmPrimeDeficitDilationRemainder u * conjugatedLaplacian y (u + v)

theorem pi_sub_half_pos : (0 : ℝ) < π - 1 / 2 := by linarith [Real.pi_gt_three]
theorem pi_sub_three_half_pos : (0 : ℝ) < π - 3 / 2 := by linarith [Real.pi_gt_three]

/-- The shifted source paired with the conjugated Laplacian is integrable beyond the shift. -/
theorem integrableOn_source_shift_mul_conjugatedLaplacian (y : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    IntegrableOn (fun s => ccmPrimeDeficitDilationSource (s - ℓ) * conjugatedLaplacian y s)
      (Ioi ℓ) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hdom : IntegrableOn
      (fun s : ℝ => sourceBound * Real.exp (-ℓ) * C * Real.exp (-(π - 3 / 2) * s)) (Ioi ℓ) :=
    (exp_neg_integrableOn_Ioi ℓ pi_sub_three_half_pos).const_mul _
  refine hdom.mono' ((measurable_ccmPrimeDeficitDilationSource_shift ℓ).mul
    (continuous_conjugatedLaplacian y).measurable).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hsl : ℓ < s := hs
  have hs0 : 0 ≤ s := hℓ.trans hsl.le
  rw [Real.norm_eq_abs, abs_mul]
  calc |ccmPrimeDeficitDilationSource (s - ℓ)| * |conjugatedLaplacian y s|
      ≤ sourceBound * Real.exp (s - ℓ) * (C * Real.exp (-((π - 1 / 2) * s))) :=
        mul_le_mul (abs_ccmPrimeDeficitDilationSource_le (sub_nonneg.mpr hsl.le)) (hC s hs0)
          (abs_nonneg _) (mul_nonneg sourceBound_nonneg (Real.exp_pos _).le)
    _ = sourceBound * Real.exp (-ℓ) * C * Real.exp (-(π - 3 / 2) * s) := by
        rw [Real.exp_sub, show sourceBound * (Real.exp s / Real.exp ℓ) *
          (C * Real.exp (-((π - 1 / 2) * s))) = sourceBound * (Real.exp ℓ)⁻¹ * C *
          (Real.exp s * Real.exp (-((π - 1 / 2) * s))) by ring, ← Real.exp_add, Real.exp_neg]
        congr 2
        ring

theorem integrableOn_mobiusFold_integrand (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    IntegrableOn (fun u => ccmPrimeDeficitDilationSource u * conjugatedLaplacian y (u + v))
      (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hdom : IntegrableOn (fun u : ℝ => sourceBound * C * Real.exp (-(π - 3 / 2) * u))
      (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 pi_sub_three_half_pos).const_mul _
  refine hdom.mono' (measurable_ccmPrimeDeficitDilationSource.mul
    ((continuous_conjugatedLaplacian y).comp (continuous_id.add continuous_const)).measurable).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.norm_eq_abs, abs_mul]
  have hb := hC (u + v) (by linarith)
  calc |ccmPrimeDeficitDilationSource u| * |conjugatedLaplacian y (u + v)|
      ≤ sourceBound * Real.exp u * (C * Real.exp (-((π - 1 / 2) * (u + v)))) :=
        mul_le_mul (abs_ccmPrimeDeficitDilationSource_le hu0) hb (abs_nonneg _)
          (mul_nonneg sourceBound_nonneg (Real.exp_pos _).le)
    _ ≤ sourceBound * Real.exp u * (C * Real.exp (-((π - 1 / 2) * u))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ?_) hC0) (mul_nonneg sourceBound_nonneg (Real.exp_pos _).le)
        nlinarith [pi_sub_half_pos]
    _ = sourceBound * C * Real.exp (-(π - 3 / 2) * u) := by
        rw [show sourceBound * Real.exp u * (C * Real.exp (-((π - 1 / 2) * u))) =
          sourceBound * C * (Real.exp u * Real.exp (-((π - 1 / 2) * u))) by ring, ← Real.exp_add]
        congr 2
        ring

/-- The fold at the shift `ℓ ≥ 0` is the translated half-line integral. -/
theorem mobiusFold_eq_setIntegral (y : ℝ) (ℓ : ℝ) :
    mobiusFold y ℓ =
      ∫ s in Ioi ℓ, ccmPrimeDeficitDilationSource (s - ℓ) * conjugatedLaplacian y s := by
  unfold mobiusFold
  rw [setIntegral_Ioi_shift (fun s => ccmPrimeDeficitDilationSource (s - ℓ) * conjugatedLaplacian y s) ℓ]
  simp only [add_sub_cancel_right]

/-- Exponential decay of the fold in the shift, for fixed time. -/
theorem exists_abs_mobiusFold_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 ≤ v → |mobiusFold y v| ≤ C * Real.exp (-((π - 1 / 2) * v)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  refine ⟨sourceBound * C * (π - 3 / 2)⁻¹,
    mul_nonneg (mul_nonneg sourceBound_nonneg hC0) (inv_nonneg.mpr pi_sub_three_half_pos.le),
    fun v hv => ?_⟩
  rw [mobiusFold_eq_setIntegral]
  have hdom : IntegrableOn
      (fun s : ℝ => sourceBound * Real.exp (-v) * C * Real.exp (-((π - 3 / 2) * s))) (Ioi v) := by
    have h : IntegrableOn (fun s : ℝ => sourceBound * Real.exp (-v) * C *
        Real.exp (-(π - 3 / 2) * s)) (Ioi v) :=
      (exp_neg_integrableOn_Ioi v pi_sub_three_half_pos).const_mul _
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi v))
    (f := fun s => ccmPrimeDeficitDilationSource (s - v) * conjugatedLaplacian y s) hdom
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => by
      have hsl : v < s := hs
      have hs0 : 0 ≤ s := hv.trans hsl.le
      rw [Real.norm_eq_abs, abs_mul]
      calc |ccmPrimeDeficitDilationSource (s - v)| * |conjugatedLaplacian y s|
          ≤ sourceBound * Real.exp (s - v) * (C * Real.exp (-((π - 1 / 2) * s))) :=
            mul_le_mul (abs_ccmPrimeDeficitDilationSource_le (sub_nonneg.mpr hsl.le)) (hC s hs0)
              (abs_nonneg _) (mul_nonneg sourceBound_nonneg (Real.exp_pos _).le)
        _ = sourceBound * Real.exp (-v) * C * Real.exp (-((π - 3 / 2) * s)) := by
            rw [Real.exp_sub, show sourceBound * (Real.exp s / Real.exp v) *
              (C * Real.exp (-((π - 1 / 2) * s))) = sourceBound * (Real.exp v)⁻¹ * C *
              (Real.exp s * Real.exp (-((π - 1 / 2) * s))) by ring, ← Real.exp_add, Real.exp_neg]
            congr 2
            ring))
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_exp_neg_mul' pi_sub_three_half_pos] at h
  refine h.trans (le_of_eq ?_)
  rw [show sourceBound * Real.exp (-v) * C * ((π - 3 / 2)⁻¹ * Real.exp (-((π - 3 / 2) * v))) =
    sourceBound * C * (π - 3 / 2)⁻¹ * (Real.exp (-v) * Real.exp (-((π - 3 / 2) * v))) by ring,
    ← Real.exp_add]
  congr 2
  ring

/-! ## Section 4: the folded Möbius series for the deficit pairing -/

/-- Summability of `|μ(m)| C e^{−c log m}` for `c > 1`. -/
theorem summable_moebius_mul_exp_neg_log {c : ℝ} (hc : 1 < c) (C : ℝ) :
    Summable fun m : ℕ => |moebiusCoeff m| * (C * Real.exp (-(c * Real.log m))) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => |C| * ((m : ℝ) ^ c)⁻¹)
    ((Real.summable_nat_rpow_inv.mpr hc).mul_left |C|) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [moebiusCoeff, Real.zero_rpow (by linarith : c ≠ 0)]
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have he : Real.exp (-(c * Real.log m)) = ((m : ℝ) ^ c)⁻¹ := by
      rw [Real.rpow_def_of_pos hm', ← Real.exp_neg]
      congr 1
      ring
    rw [he]
    have h1 := abs_moebiusCoeff_le_one m
    calc |moebiusCoeff m| * (|C| * ((m : ℝ) ^ c)⁻¹) ≤ 1 * (|C| * ((m : ℝ) ^ c)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := one_mul _

/-- **The deficit pairing is the folded Möbius series**:
`∫_0^∞ D(s) f_y''(s) ds = Σ_m μ(m) Φ_y(log m)`. -/
theorem integral_deficitPrimitive_mul_conjugatedLaplacian_eq_tsum_mobiusFold (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s =
      ∑' m : ℕ, moebiusCoeff m * mobiusFold y (Real.log m) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  set F : ℕ → ℝ → ℝ := fun m s =>
    (Ioi (Real.log m)).indicator
      (fun s => moebiusCoeff m * (ccmPrimeDeficitDilationSource (s - Real.log m) *
        conjugatedLaplacian y s)) s with hF
  have hFint : ∀ m, Integrable (F m) := by
    intro m
    have h : IntegrableOn (fun s => moebiusCoeff m * (ccmPrimeDeficitDilationSource (s - Real.log m) *
        conjugatedLaplacian y s)) (Ioi (Real.log m)) :=
      (integrableOn_source_shift_mul_conjugatedLaplacian y (Real.log_natCast_nonneg m)).const_mul _
    exact h.integrable_indicator measurableSet_Ioi
  have hFval : ∀ m, ∫ s, F m s = moebiusCoeff m * mobiusFold y (Real.log m) := by
    intro m
    simp only [hF]
    rw [integral_indicator measurableSet_Ioi, integral_const_mul, mobiusFold_eq_setIntegral]
  -- norms
  have hFnorm : ∀ m, ∫ s, ‖F m s‖ ≤ |moebiusCoeff m| *
      (sourceBound * C * (π - 3 / 2)⁻¹ * Real.exp (-((π - 1 / 2) * Real.log m))) := by
    intro m
    have hln := Real.log_natCast_nonneg m
    set ℓ := Real.log m with hℓ
    have hbound : ∀ s, ‖F m s‖ ≤ (Ioi ℓ).indicator
        (fun s => |moebiusCoeff m| * (sourceBound * Real.exp (-ℓ) * C *
          Real.exp (-((π - 3 / 2) * s)))) s := by
      intro s
      simp only [hF]
      by_cases hs : s ∈ Ioi ℓ
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs, abs_mul, abs_mul]
        have hsl : ℓ < s := hs
        have hs0 : 0 ≤ s := hln.trans hsl.le
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc |ccmPrimeDeficitDilationSource (s - ℓ)| * |conjugatedLaplacian y s|
            ≤ sourceBound * Real.exp (s - ℓ) * (C * Real.exp (-((π - 1 / 2) * s))) :=
              mul_le_mul (abs_ccmPrimeDeficitDilationSource_le (sub_nonneg.mpr hsl.le)) (hC s hs0)
                (abs_nonneg _) (mul_nonneg sourceBound_nonneg (Real.exp_pos _).le)
          _ = sourceBound * Real.exp (-ℓ) * C * Real.exp (-((π - 3 / 2) * s)) := by
              rw [Real.exp_sub, show sourceBound * (Real.exp s / Real.exp ℓ) *
                (C * Real.exp (-((π - 1 / 2) * s))) = sourceBound * (Real.exp ℓ)⁻¹ * C *
                (Real.exp s * Real.exp (-((π - 1 / 2) * s))) by ring, ← Real.exp_add, Real.exp_neg]
              congr 2
              ring
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]
    have hint : Integrable fun s => (Ioi ℓ).indicator
        (fun s => |moebiusCoeff m| * (sourceBound * Real.exp (-ℓ) * C *
          Real.exp (-((π - 3 / 2) * s)))) s := by
      refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioi
      have h : IntegrableOn (fun x : ℝ => |moebiusCoeff m| * (sourceBound * Real.exp (-ℓ) * C) *
          Real.exp (-(π - 3 / 2) * x)) (Ioi ℓ) :=
        (exp_neg_integrableOn_Ioi ℓ pi_sub_three_half_pos).const_mul _
      refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
      simp only [neg_mul]
      ring
    have hmono := integral_mono_of_nonneg (μ := volume) (f := fun s => ‖F m s‖)
      (g := fun s => (Ioi ℓ).indicator
        (fun s => |moebiusCoeff m| * (sourceBound * Real.exp (-ℓ) * C *
          Real.exp (-((π - 3 / 2) * s)))) s)
      (Eventually.of_forall fun s => norm_nonneg _) hint (Eventually.of_forall hbound)
    refine hmono.trans (le_of_eq ?_)
    rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_const_mul,
      integral_Ioi_exp_neg_mul' pi_sub_three_half_pos]
    rw [show |moebiusCoeff m| * (sourceBound * Real.exp (-ℓ) * C *
      ((π - 3 / 2)⁻¹ * Real.exp (-((π - 3 / 2) * ℓ)))) = |moebiusCoeff m| *
      (sourceBound * C * (π - 3 / 2)⁻¹ * (Real.exp (-ℓ) * Real.exp (-((π - 3 / 2) * ℓ)))) by ring,
      ← Real.exp_add]
    congr 3
    ring
  have hFsum : Summable fun m => ∫ s, ‖F m s‖ :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg fun s => norm_nonneg _) hFnorm
      (summable_moebius_mul_exp_neg_log (by linarith [Real.pi_gt_three]) _)
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  simp_rw [hFval] at hswap
  -- pointwise identification on the forward half-line
  have hpt : ∀ s ∈ Ioi (0 : ℝ), (∑' m, F m s) =
      ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    rw [ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation hs0, Finset.sum_mul]
    have hts : (∑' m, F m s) = ∑ m ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, F m s := by
      refine tsum_eq_sum fun m hm => ?_
      simp only [hF]
      rw [Finset.mem_Icc, not_and_or] at hm
      rcases hm with hm | hm
      · have h0 : m = 0 := by omega
        subst h0
        simp [moebiusCoeff]
      · have hm' : ⌊Real.exp s⌋₊ < m := by omega
        have hexp : Real.exp s < m := (Nat.floor_lt (Real.exp_pos s).le).mp hm'
        have hmpos : (0 : ℝ) < m := (Real.exp_pos s).trans hexp
        have hlog : s < Real.log m := (Real.lt_log_iff_exp_lt hmpos).mpr hexp
        rw [Set.indicator_of_notMem (by simpa [Set.mem_Ioi, not_lt] using hlog.le)]
    rw [hts]
    refine Finset.sum_congr rfl fun m hm => ?_
    · simp only [hF]
      obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
      have hle : Real.log m ≤ s := (Real.log_le_iff_le_exp hmpos).mpr
        ((Nat.le_floor_iff (Real.exp_pos s).le).mp hmN)
      rcases lt_or_eq_of_le hle with hlt | heq
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hlt), moebiusCoeff]
        ring
      · rw [Set.indicator_of_notMem (by simp [Set.mem_Ioi, heq]), heq, sub_self,
          ccmPrimeDeficitDilationSource_zero]
        simp
  have hzero : ∀ s ∉ Ioi (0 : ℝ), (∑' m, F m s) = 0 := by
    intro s hs
    have hs0 : s ≤ 0 := by simpa [Set.mem_Ioi, not_lt] using hs
    have : (fun m : ℕ => F m s) = fun _ => 0 := by
      funext m
      simp only [hF]
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ioi, not_lt]
      exact hs0.trans (Real.log_natCast_nonneg m)
    rw [this, tsum_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_congr_fun measurableSet_Ioi hpt] at hswap
  exact hswap.symm

/-- **The transport as a folded Möbius series**: `T(y) = K_y(0) − Σ_m μ(m) Φ_y(log m)`. -/
theorem chebyshevDiscrepancyTransport_eq_sub_tsum_mobiusFold (y : ℝ) :
    chebyshevDiscrepancyTransport y =
      chmdPrimeKernel y 0 - ∑' m : ℕ, moebiusCoeff m * mobiusFold y (Real.log m) := by
  have h1 := integral_deficitPrimitive_mul_conjugatedLaplacian y
  have h2 := integral_deficitPrimitive_mul_conjugatedLaplacian_eq_tsum_mobiusFold y
  linarith

/-! ## Section 5: the explicit decomposition of the fold -/

/-- Pole-density integration by parts from an arbitrary base point `v ≥ 0`:
`∫_v^∞ (e^s − e^v) f_y''(s) ds = e^v f_y(v) + ∫_v^∞ e^s f_y(s) ds`. -/
theorem integral_Ioi_exp_sub_mul_conjugatedLaplacian (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ∫ s in Ioi v, (Real.exp s - Real.exp v) * conjugatedLaplacian y s =
      Real.exp v * conjugatedKernel y v + ∫ s in Ioi v, Real.exp s * conjugatedKernel y s := by
  set g : ℝ → ℝ := fun s => (Real.exp s - Real.exp v) * conjugatedKernelDeriv y s -
    Real.exp s * conjugatedKernel y s with hg
  have hgd : ∀ x, HasDerivAt g
      ((Real.exp x - Real.exp v) * conjugatedLaplacian y x - Real.exp x * conjugatedKernel y x) x := by
    intro x
    have h := (((Real.hasDerivAt_exp x).sub_const (Real.exp v)).mul
      (hasDerivAt_conjugatedKernelDeriv y x)).sub
      ((Real.hasDerivAt_exp x).mul (hasDerivAt_conjugatedKernel y x))
    refine h.congr_deriv ?_
    unfold conjugatedKernelDeriv conjugatedKernel conjugatedLaplacian
    ring
  have hcont : Continuous g :=
    ((Real.continuous_exp.sub continuous_const).mul (continuous_conjugatedKernelDeriv y)).sub
      (Real.continuous_exp.mul (continuous_conjugatedKernel y))
  have hpi : (1 : ℝ) < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have htend : Tendsto g atTop (𝓝 0) := by
    obtain ⟨C₁, _, hC₁⟩ := exists_abs_conjugatedKernelDeriv_le y
    obtain ⟨C₀, _, hC₀⟩ := exists_abs_conjugatedKernel_le y
    have h1 := tendsto_exp_mul_of_abs_le (a := 1) hpi hC₁
    have h1' := tendsto_exp_mul_of_abs_le (a := 0) (by linarith) hC₁
    have h0 := tendsto_exp_mul_of_abs_le (a := 1) hpi hC₀
    simp only [one_mul, zero_mul, Real.exp_zero] at h1 h1' h0
    have := (h1.sub (h1'.const_mul (Real.exp v))).sub h0
    rw [mul_zero, sub_zero, sub_zero] at this
    refine this.congr fun s => ?_
    simp only [hg]
    ring
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hint1 : IntegrableOn (fun s => (Real.exp s - Real.exp v) * conjugatedLaplacian y s) (Ioi v) := by
    have hdom : IntegrableOn (fun s : ℝ => C * Real.exp (-(π - 3 / 2) * s)) (Ioi v) :=
      (exp_neg_integrableOn_Ioi v pi_sub_three_half_pos).const_mul C
    refine hdom.mono' ((Real.continuous_exp.sub continuous_const).mul
      (continuous_conjugatedLaplacian y)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hsv : v < s := hs
    have hs0 : 0 ≤ s := hv.trans hsv.le
    have he : 0 ≤ Real.exp s - Real.exp v := sub_nonneg.mpr (Real.exp_le_exp.mpr hsv.le)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he]
    calc (Real.exp s - Real.exp v) * |conjugatedLaplacian y s|
        ≤ Real.exp s * (C * Real.exp (-((π - 1 / 2) * s))) :=
          mul_le_mul (by linarith [Real.exp_pos v]) (hC s hs0) (abs_nonneg _) (Real.exp_pos _).le
      _ = C * Real.exp (-(π - 3 / 2) * s) := by
          rw [show Real.exp s * (C * Real.exp (-((π - 1 / 2) * s))) =
            C * (Real.exp s * Real.exp (-((π - 1 / 2) * s))) by ring, ← Real.exp_add]
          congr 2
          ring
  have hint2 : IntegrableOn (fun s => Real.exp s * conjugatedKernel y s) (Ioi v) := by
    refine ((integrable_chmdPrimeKernel_mul_exp_half y).integrableOn.congr_fun ?_ measurableSet_Ioi)
    intro s _
    exact (exp_mul_conjugatedKernel y s).symm
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := v) (m := 0) hcont.continuousWithinAt
    (fun x _ => hgd x) (hint1.sub hint2) htend
  rw [integral_sub hint1 hint2] at h
  have h0 : g v = -(Real.exp v * conjugatedKernel y v) := by
    simp [hg]
  rw [h0] at h
  linarith

/-- The fold of the explicit pole part: `∫_0^∞ (e^u − 1) f_y''(u+v) du = f_y(v) + e^{−v}∫_v^∞ K_y e^{s/2}`. -/
theorem integral_exp_sub_one_mul_conjugatedLaplacian_shift (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ∫ u in Ioi (0 : ℝ), (Real.exp u - 1) * conjugatedLaplacian y (u + v) =
      conjugatedKernel y v +
        Real.exp (-v) * ∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2) := by
  have hshift := setIntegral_Ioi_shift
    (fun s => Real.exp (-v) * ((Real.exp s - Real.exp v) * conjugatedLaplacian y s)) v
  have heq : ∀ u : ℝ, Real.exp (-v) * ((Real.exp (u + v) - Real.exp v) * conjugatedLaplacian y (u + v)) =
      (Real.exp u - 1) * conjugatedLaplacian y (u + v) := by
    intro u
    rw [Real.exp_add, Real.exp_neg]
    field_simp
  simp only [heq] at hshift
  rw [← hshift, integral_const_mul, integral_Ioi_exp_sub_mul_conjugatedLaplacian y hv]
  have hK : ∫ s in Ioi v, Real.exp s * conjugatedKernel y s =
      ∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => exp_mul_conjugatedKernel y s
  rw [hK, mul_add, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- The fold of the linear part: `∫_0^∞ u f_y''(u+v) du = f_y(v)`. -/
theorem integral_id_mul_conjugatedLaplacian_shift (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ∫ u in Ioi (0 : ℝ), u * conjugatedLaplacian y (u + v) = conjugatedKernel y v := by
  have hshift := setIntegral_Ioi_shift (fun s => (s - v) * conjugatedLaplacian y s) v
  simp only [add_sub_cancel_right] at hshift
  rw [← hshift]
  exact integral_Ioi_sub_mul_conjugatedLaplacian y hv

theorem integrableOn_exp_sub_one_mul_conjugatedLaplacian_shift (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    IntegrableOn (fun u => (Real.exp u - 1) * conjugatedLaplacian y (u + v)) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hdom : IntegrableOn (fun u : ℝ => C * Real.exp (-(π - 3 / 2) * u)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 pi_sub_three_half_pos).const_mul C
  refine hdom.mono' ((Real.continuous_exp.sub continuous_const).mul
    ((continuous_conjugatedLaplacian y).comp (continuous_id.add continuous_const))).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  have he : 0 ≤ Real.exp u - 1 := by linarith [Real.one_le_exp_iff.mpr hu0]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he]
  have hb := hC (u + v) (by linarith)
  calc (Real.exp u - 1) * |conjugatedLaplacian y (u + v)|
      ≤ Real.exp u * (C * Real.exp (-((π - 1 / 2) * (u + v)))) :=
        mul_le_mul (by linarith) hb (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp u * (C * Real.exp (-((π - 1 / 2) * u))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ?_) hC0) (Real.exp_pos _).le
        nlinarith [pi_sub_half_pos]
    _ = C * Real.exp (-(π - 3 / 2) * u) := by
        rw [show Real.exp u * (C * Real.exp (-((π - 1 / 2) * u))) =
          C * (Real.exp u * Real.exp (-((π - 1 / 2) * u))) by ring, ← Real.exp_add]
        congr 2
        ring

theorem integrableOn_id_mul_conjugatedLaplacian_shift (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    IntegrableOn (fun u => u * conjugatedLaplacian y (u + v)) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hdom : IntegrableOn (fun u : ℝ => 2 * C * Real.exp (-(π - 1) * u)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith [Real.pi_gt_three])).const_mul _
  refine hdom.mono' (continuous_id.mul
    ((continuous_conjugatedLaplacian y).comp (continuous_id.add continuous_const))).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0]
  have hb := hC (u + v) (by linarith)
  calc u * |conjugatedLaplacian y (u + v)|
      ≤ 2 * Real.exp (u / 2) * (C * Real.exp (-((π - 1 / 2) * (u + v)))) :=
        mul_le_mul (le_two_mul_exp_half u) hb (abs_nonneg _) (by positivity)
    _ ≤ 2 * Real.exp (u / 2) * (C * Real.exp (-((π - 1 / 2) * u))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ?_) hC0) (by positivity)
        nlinarith [pi_sub_half_pos]
    _ = 2 * C * Real.exp (-(π - 1) * u) := by
        rw [show 2 * Real.exp (u / 2) * (C * Real.exp (-((π - 1 / 2) * u))) =
          2 * C * (Real.exp (u / 2) * Real.exp (-((π - 1 / 2) * u))) by ring, ← Real.exp_add]
        congr 2
        ring

theorem integrableOn_remainderFold_integrand (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    IntegrableOn (fun u => ccmPrimeDeficitDilationRemainder u * conjugatedLaplacian y (u + v))
      (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hdom : IntegrableOn (fun u : ℝ => 7 / 2 * C * Real.exp (-(π - 1 / 2) * u)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 pi_sub_half_pos).const_mul _
  refine hdom.mono' (measurable_ccmPrimeDeficitDilationRemainder.mul
    ((continuous_conjugatedLaplacian y).comp (continuous_id.add continuous_const)).measurable).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.norm_eq_abs, abs_mul]
  have hb := hC (u + v) (by linarith)
  calc |ccmPrimeDeficitDilationRemainder u| * |conjugatedLaplacian y (u + v)|
      ≤ 7 / 2 * (C * Real.exp (-((π - 1 / 2) * (u + v)))) :=
        mul_le_mul (abs_ccmPrimeDeficitDilationRemainder_le_uniform hu0) hb (abs_nonneg _)
          (by norm_num)
    _ ≤ 7 / 2 * (C * Real.exp (-((π - 1 / 2) * u))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ?_) hC0) (by norm_num)
        nlinarith [pi_sub_half_pos]
    _ = 7 / 2 * C * Real.exp (-(π - 1 / 2) * u) := by
        rw [neg_mul]; ring

/-- The constant `γ + 1 − log(2π)/2` multiplying the Möbius Klein–Gordon wave. -/
def mobiusWaveConstant : ℝ := Real.eulerMascheroniConstant + 1 - Real.log (2 * π) / 2

/-- **Explicit decomposition of the fold** for `v ≥ 0`:
`Φ_y(v) = (γ + 1 − log(2π)/2) f_y(v) + (γ+1) e^{−v} ∫_v^∞ K_y e^{s/2} + ∫_0^∞ R(u) f_y''(u+v) du`. -/
theorem mobiusFold_eq (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    mobiusFold y v =
      mobiusWaveConstant * conjugatedKernel y v +
        (Real.eulerMascheroniConstant + 1) *
          (Real.exp (-v) * ∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2)) +
        remainderFold y v := by
  unfold mobiusFold remainderFold mobiusWaveConstant
  have hS : ∀ u, ccmPrimeDeficitDilationSource u * conjugatedLaplacian y (u + v) =
      (Real.eulerMascheroniConstant + 1) * ((Real.exp u - 1) * conjugatedLaplacian y (u + v)) -
        Real.log (2 * π) / 2 * (u * conjugatedLaplacian y (u + v)) +
        ccmPrimeDeficitDilationRemainder u * conjugatedLaplacian y (u + v) := by
    intro u
    rw [ccmPrimeDeficitDilationSource_eq]
    ring
  simp_rw [hS]
  have hA : IntegrableOn (fun u => (Real.eulerMascheroniConstant + 1) *
      ((Real.exp u - 1) * conjugatedLaplacian y (u + v))) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_sub_one_mul_conjugatedLaplacian_shift y hv).const_mul _
  have hB : IntegrableOn (fun u => Real.log (2 * π) / 2 * (u * conjugatedLaplacian y (u + v)))
      (Ioi (0 : ℝ)) :=
    (integrableOn_id_mul_conjugatedLaplacian_shift y hv).const_mul _
  have hAB : IntegrableOn (fun u => (Real.eulerMascheroniConstant + 1) *
      ((Real.exp u - 1) * conjugatedLaplacian y (u + v)) -
        Real.log (2 * π) / 2 * (u * conjugatedLaplacian y (u + v))) (Ioi (0 : ℝ)) := hA.sub hB
  rw [integral_add hAB (integrableOn_remainderFold_integrand y hv), integral_sub hA hB,
    integral_const_mul, integral_const_mul,
    integral_exp_sub_one_mul_conjugatedLaplacian_shift y hv,
    integral_id_mul_conjugatedLaplacian_shift y hv]
  ring

/-- The remainder fold is bounded by `7 C e^{−v/2}` uniformly in the time `y`. -/
theorem abs_remainderFold_le (y v : ℝ) :
    |remainderFold y v| ≤ 7 * laplacianBound * Real.exp (-(v / 2)) := by
  unfold remainderFold
  have hdom : IntegrableOn (fun u : ℝ => 7 / 2 * laplacianBound * Real.exp (-(v / 2)) *
      Real.exp (-(1 / 2 * u))) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun u : ℝ => 7 / 2 * laplacianBound * Real.exp (-(v / 2)) *
        Real.exp (-(1 / 2) * u)) (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (by norm_num)).const_mul _
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun u => ccmPrimeDeficitDilationRemainder u * conjugatedLaplacian y (u + v)) hdom
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
      have hu0 : 0 ≤ u := le_of_lt hu
      rw [Real.norm_eq_abs, abs_mul]
      calc |ccmPrimeDeficitDilationRemainder u| * |conjugatedLaplacian y (u + v)|
          ≤ 7 / 2 * (laplacianBound * Real.exp (-((u + v) / 2))) :=
            mul_le_mul (abs_ccmPrimeDeficitDilationRemainder_le_uniform hu0)
              (abs_conjugatedLaplacian_le y (u + v)) (abs_nonneg _) (by norm_num)
        _ = 7 / 2 * laplacianBound * Real.exp (-(v / 2)) * Real.exp (-(1 / 2 * u)) := by
            rw [show -((u + v) / 2) = -(v / 2) + -(1 / 2 * u) by ring, Real.exp_add]
            ring))
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_exp_neg_mul' (by norm_num : (0:ℝ) < 1 / 2)] at h
  refine h.trans (le_of_eq ?_)
  rw [mul_zero, neg_zero, Real.exp_zero]
  ring

/-! ## Section 6: the three Möbius pieces of the transport -/

/-- The Möbius Klein–Gordon wave `Σ_m μ(m) m^{−1/2} K_y(log m)`. -/
def mobiusWave (y : ℝ) : ℝ := ∑' m : ℕ, moebiusCoeff m * conjugatedKernel y (Real.log m)

/-- The Möbius tail pairing `Σ_m (μ(m)/m) ∫_{log m}^∞ K_y(s) e^{s/2} ds`. -/
def mobiusTailPairing (y : ℝ) : ℝ :=
  ∑' m : ℕ, moebiusCoeff m *
    (Real.exp (-Real.log m) * ∫ s in Ioi (Real.log m), chmdPrimeKernel y s * Real.exp (s / 2))

/-- The remainder fold series `Σ_m μ(m) ∫_0^∞ R(u) f_y''(u + log m) du`. -/
def remainderFoldSeries (y : ℝ) : ℝ := ∑' m : ℕ, moebiusCoeff m * remainderFold y (Real.log m)

theorem summable_mobiusWave_term (y : ℝ) :
    Summable fun m : ℕ => moebiusCoeff m * conjugatedKernel y (Real.log m) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedKernel_le y
  refine Summable.of_norm_bounded
    (g := fun m : ℕ => |moebiusCoeff m| * (C * Real.exp (-((π - 1 / 2) * Real.log m))))
    (summable_moebius_mul_exp_neg_log (by linarith [Real.pi_gt_three]) C) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC _ (Real.log_natCast_nonneg m)) (abs_nonneg _)

theorem abs_exp_neg_mul_integral_tail_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 ≤ v →
      |Real.exp (-v) * ∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2)| ≤
        C * Real.exp (-((π - 1 / 2) * v)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_chmdPrimeKernel_le y
  refine ⟨C * (π - 3 / 2)⁻¹, mul_nonneg hC0 (inv_nonneg.mpr pi_sub_three_half_pos.le),
    fun v hv => ?_⟩
  have hdom : IntegrableOn (fun s : ℝ => C * Real.exp (-((π - 3 / 2) * s))) (Ioi v) := by
    have h : IntegrableOn (fun s : ℝ => C * Real.exp (-(π - 3 / 2) * s)) (Ioi v) :=
      (exp_neg_integrableOn_Ioi v pi_sub_three_half_pos).const_mul C
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi v))
    (f := fun s => chmdPrimeKernel y s * Real.exp (s / 2)) hdom
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => by
      have hsv : v < s := hs
      have hs0 : 0 ≤ s := hv.trans hsv.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hb := hC s
      rw [abs_of_nonneg hs0] at hb
      calc |chmdPrimeKernel y s| * Real.exp (s / 2)
          ≤ C * Real.exp (-((π - 1) * s)) * Real.exp (s / 2) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = C * Real.exp (-((π - 3 / 2) * s)) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring))
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_exp_neg_mul' pi_sub_three_half_pos] at h
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-v) * |∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2)|
      ≤ Real.exp (-v) * (C * ((π - 3 / 2)⁻¹ * Real.exp (-((π - 3 / 2) * v)))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = C * (π - 3 / 2)⁻¹ * Real.exp (-((π - 1 / 2) * v)) := by
        rw [show Real.exp (-v) * (C * ((π - 3 / 2)⁻¹ * Real.exp (-((π - 3 / 2) * v)))) =
          C * (π - 3 / 2)⁻¹ * (Real.exp (-v) * Real.exp (-((π - 3 / 2) * v))) by ring,
          ← Real.exp_add]
        congr 2
        ring

theorem summable_mobiusTailPairing_term (y : ℝ) :
    Summable fun m : ℕ => moebiusCoeff m *
      (Real.exp (-Real.log m) * ∫ s in Ioi (Real.log m), chmdPrimeKernel y s * Real.exp (s / 2)) := by
  obtain ⟨C, hC0, hC⟩ := abs_exp_neg_mul_integral_tail_le y
  refine Summable.of_norm_bounded
    (g := fun m : ℕ => |moebiusCoeff m| * (C * Real.exp (-((π - 1 / 2) * Real.log m))))
    (summable_moebius_mul_exp_neg_log (by linarith [Real.pi_gt_three]) C) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC _ (Real.log_natCast_nonneg m)) (abs_nonneg _)

theorem exists_abs_remainderFold_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 ≤ v → |remainderFold y v| ≤ C * Real.exp (-((π - 1 / 2) * v)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  refine ⟨7 / 2 * C * (π - 1 / 2)⁻¹,
    mul_nonneg (mul_nonneg (by norm_num) hC0) (inv_nonneg.mpr pi_sub_half_pos.le), fun v hv => ?_⟩
  unfold remainderFold
  have hdom : IntegrableOn (fun u : ℝ => 7 / 2 * C * Real.exp (-((π - 1 / 2) * v)) *
      Real.exp (-((π - 1 / 2) * u))) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun u : ℝ => 7 / 2 * C * Real.exp (-((π - 1 / 2) * v)) *
        Real.exp (-(π - 1 / 2) * u)) (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 pi_sub_half_pos).const_mul _
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun u => ccmPrimeDeficitDilationRemainder u * conjugatedLaplacian y (u + v)) hdom
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
      have hu0 : 0 ≤ u := le_of_lt hu
      rw [Real.norm_eq_abs, abs_mul]
      calc |ccmPrimeDeficitDilationRemainder u| * |conjugatedLaplacian y (u + v)|
          ≤ 7 / 2 * (C * Real.exp (-((π - 1 / 2) * (u + v)))) :=
            mul_le_mul (abs_ccmPrimeDeficitDilationRemainder_le_uniform hu0)
              (hC (u + v) (by linarith)) (abs_nonneg _) (by norm_num)
        _ = 7 / 2 * C * Real.exp (-((π - 1 / 2) * v)) * Real.exp (-((π - 1 / 2) * u)) := by
            rw [show -((π - 1 / 2) * (u + v)) = -((π - 1 / 2) * v) + -((π - 1 / 2) * u) by ring,
              Real.exp_add]
            ring))
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_exp_neg_mul' pi_sub_half_pos] at h
  refine h.trans (le_of_eq ?_)
  rw [mul_zero, neg_zero, Real.exp_zero]
  ring

theorem summable_remainderFoldSeries_term (y : ℝ) :
    Summable fun m : ℕ => moebiusCoeff m * remainderFold y (Real.log m) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_remainderFold_le y
  refine Summable.of_norm_bounded
    (g := fun m : ℕ => |moebiusCoeff m| * (C * Real.exp (-((π - 1 / 2) * Real.log m))))
    (summable_moebius_mul_exp_neg_log (by linarith [Real.pi_gt_three]) C) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC _ (Real.log_natCast_nonneg m)) (abs_nonneg _)

/-- **The Klein–Gordon transport in Möbius pieces**: with `c₀ = γ + 1 − log(2π)/2`,
`T(y) = K_y(0) − c₀ Σ_m μ(m) m^{−1/2} K_y(log m) − (γ+1) Σ_m (μ(m)/m)∫_{log m}^∞ K_y e^{s/2}
  − Σ_m μ(m) ∫_0^∞ R(u) f_y''(u + log m) du`. -/
theorem chebyshevDiscrepancyTransport_eq_mobius_pieces (y : ℝ) :
    chebyshevDiscrepancyTransport y =
      chmdPrimeKernel y 0 - (mobiusWaveConstant * mobiusWave y +
        (Real.eulerMascheroniConstant + 1) * mobiusTailPairing y + remainderFoldSeries y) := by
  rw [chebyshevDiscrepancyTransport_eq_sub_tsum_mobiusFold]
  congr 1
  unfold mobiusWave mobiusTailPairing remainderFoldSeries
  rw [← (summable_mobiusWave_term y).tsum_mul_left, ← (summable_mobiusTailPairing_term y).tsum_mul_left,
    ← ((summable_mobiusWave_term y).mul_left _).tsum_add ((summable_mobiusTailPairing_term y).mul_left _),
    ← (((summable_mobiusWave_term y).mul_left _).add ((summable_mobiusTailPairing_term y).mul_left _)).tsum_add
      (summable_remainderFoldSeries_term y)]
  refine tsum_congr fun m => ?_
  rw [mobiusFold_eq y (Real.log_natCast_nonneg m)]
  ring

/-- **Riemann hypothesis through the Möbius pieces (upper form)**: RH iff the sum of the three
Möbius pieces is bounded above on `[0,∞)`. -/
theorem riemannHypothesis_iff_mobius_pieces_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      mobiusWaveConstant * mobiusWave y + (Real.eulerMascheroniConstant + 1) * mobiusTailPairing y +
        remainderFoldSeries y ≤ M := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chmdPrimeKernel_le y 0)
    have h3 := chebyshevDiscrepancyTransport_eq_mobius_pieces y
    linarith [h2.2]
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chmdPrimeKernel_le y 0)
    have h3 := chebyshevDiscrepancyTransport_eq_mobius_pieces y
    linarith [h2.1]

/-- **Riemann hypothesis through the Möbius pieces (lower form).** -/
theorem riemannHypothesis_iff_mobius_pieces_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      -M ≤ mobiusWaveConstant * mobiusWave y + (Real.eulerMascheroniConstant + 1) * mobiusTailPairing y +
        remainderFoldSeries y := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddAbove]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chmdPrimeKernel_le y 0)
    have h3 := chebyshevDiscrepancyTransport_eq_mobius_pieces y
    linarith [h2.1]
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chmdPrimeKernel_le y 0)
    have h3 := chebyshevDiscrepancyTransport_eq_mobius_pieces y
    linarith [h2.2]

end

end RHTower.CHMDChebyshevTransport
