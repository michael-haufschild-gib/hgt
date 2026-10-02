import GaloisForLFunctions.RHTower.ChiDualSpatialExterior

/-!
# Complete physical-height mean-square dual-block profile

The literal Gaussian dual block has a scalar step profile on its stationary
height interval. Interior and exterior decay hold outside two explicit bands;
the complete all-height bound controls both bands. Their physical lengths
are integrated in full. The result derives source measurability and integrability
and proves normalized mean-square error O(m^-2) at N=m^10, uniformly on each
fixed right-strip disc. It does not supply a full-AFE self-return estimate.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The literal complete dual integer block at physical zero phase. -/
def chiDualIntegerBlock (s : ℂ) (N : ℝ) (A B : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t

/-- The scalar Gaussian profile on the complete stationary-height interval. -/
def chiDualSpatialStepProfile (N : ℝ) (A B : ℕ) : ℝ → ℂ :=
  (Icc (2 * Real.pi * ((A : ℝ) - 1 / 2)) (2 * Real.pi * ((B : ℝ) + 1 / 2))).indicator
    (fun t => smoothAFECutoff ((t / (2 * Real.pi)) / N))

/-- A physical-height transition band corresponding to spatial margin h. -/
def chiDualSpatialBand (b h : ℝ) : Set ℝ :=
  Icc (2 * Real.pi * (b - h)) (2 * Real.pi * (b + h))

private theorem mem_chiDualSpatialBand (t b h : ℝ) :
    t ∈ chiDualSpatialBand b h ↔ b - h ≤ t / (2 * Real.pi) ∧ t / (2 * Real.pi) ≤ b + h := by
  have hp : 0 < 2 * Real.pi := by positivity
  simp only [chiDualSpatialBand, mem_Icc, le_div_iff₀ hp, div_le_iff₀ hp]
  simp only [mul_comm (b - h), mul_comm (b + h)]

private theorem chiDualSpatialStepProfile_eq (N : ℝ) (A B : ℕ) (t : ℝ) :
    chiDualSpatialStepProfile N A B t =
      if (A : ℝ) - 1 / 2 ≤ t / (2 * Real.pi) ∧ t / (2 * Real.pi) ≤ (B : ℝ) + 1 / 2
      then smoothAFECutoff ((t / (2 * Real.pi)) / N) else 0 := by
  have hp : 0 < 2 * Real.pi := by positivity
  simp only [chiDualSpatialStepProfile, Set.indicator, mem_Icc, le_div_iff₀ hp, div_le_iff₀ hp]
  simp only [mul_comm ((A : ℝ) - 1 / 2), mul_comm ((B : ℝ) + 1 / 2)]

private theorem continuous_chiDualIntegerBlock {s : ℂ} (hs : s.re < 1)
    (N : ℝ) (A B : ℕ) : Continuous (chiDualIntegerBlock s N A B) := by
  have hchi : Continuous (fun t : ℝ => zetaChi (s + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hG : Gammaℝ (1 - (s + (t : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simpa using sub_pos.mpr hs
    have hpath : Continuous (fun u : ℝ => s + (u : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => s + (u : ℂ) * I) (x := t)
      (zetaChi_analyticAt hG).continuousAt hpath.continuousAt
  unfold chiDualIntegerBlock
  apply continuous_finsetSum
  intro n hn
  unfold zetaChiDualInteriorAtom bourgainOscillation
  exact continuous_const.mul ((hchi.mul continuous_const).mul (by fun_prop))

private theorem aestronglyMeasurable_chiDualSpatialStepProfile {N : ℝ} (hN : 0 < N)
    (A B : ℕ) : AEStronglyMeasurable (chiDualSpatialStepProfile N A B)
      (volume.restrict (Icc N (2 * N))) := by
  have hc : ContinuousOn (fun t : ℝ => smoothAFECutoff ((t / (2 * Real.pi)) / N))
      (Icc N (2 * N)) := by
    intro t ht
    have ht0 : 0 < (t / (2 * Real.pi)) / N :=
      div_pos (div_pos (hN.trans_le ht.1) (by positivity)) hN
    have hd := (hasDerivAt_smoothAFECutoff ht0).continuousAt
    exact (ContinuousAt.comp (f := fun u : ℝ => (u / (2 * Real.pi)) / N) (x := t)
      hd (by fun_prop)).continuousWithinAt
  exact (hc.aestronglyMeasurable measurableSet_Icc).indicator measurableSet_Icc

/-- A single all-height bound retains both transition bands explicitly.
Outside them it uses the actual interior/exterior decay, uniformly on the disc. -/
theorem exists_chiDual_integer_block_profile_majorant
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ E M : ℝ, 0 < E ∧ 0 < M ∧ ∀ᶠ m : ℕ in atTop,
      ∀ s ∈ Metric.closedBall c r, ∀ A B : ℕ,
      (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      ∀ t ∈ Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10),
      ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
        chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2 ≤
        (E / m) ^ 2 +
          (chiDualSpatialBand ((A : ℝ) - 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2) t +
          (chiDualSpatialBand ((B : ℝ) + 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2) t := by
  obtain ⟨Cᵢ, hCᵢ, hi⟩ := exists_chiDual_integer_block_interior_profile_decay c hr hc0 hc1
  obtain ⟨Cₑ, hCₑ, he⟩ := exists_chiDual_integer_block_exterior_decay c hr hc0 hc1
  obtain ⟨Cᵦ, hCᵦ, hb⟩ := exists_chiDual_integer_block_disc_bound c hr hc0 hc1
  refine ⟨Cᵢ + Cₑ, Cᵦ + 1, add_pos hCᵢ hCₑ, by positivity, ?_⟩
  have hp : Tendsto (fun m : ℕ => m ^ 10) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hi, he, hp.eventually hb, eventually_ge_atTop (1 : ℕ)] with m hi he hb hm
  norm_num only [Nat.cast_pow] at hb
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hN0 : (0 : ℝ) < (m : ℝ) ^ 10 := by positivity
  have hh : (0 : ℝ) < (m : ℝ) ^ 6 := by positivity
  intro s hs A B hA hB hAB t ht
  let a : ℝ := t / (2 * Real.pi)
  have ha : 0 < a := div_pos (hN0.trans_le ht.1) (by positivity)
  have hta : 2 * Real.pi * a = t := mul_div_cancel₀ t (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hat : (m : ℝ) ^ 10 ≤ 2 * Real.pi * a ∧ 2 * Real.pi * a ≤ 2 * (m : ℝ) ^ 10 := by rwa [hta]
  let V := smoothAFECutoff (a / (m : ℝ) ^ 10)
  have hV : ‖V‖ ≤ 1 := norm_smoothAFECutoff_le_one (div_pos ha hN0)
  let F := chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t - chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t
  have hP : ‖chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ≤ 1 := by
    rw [chiDualSpatialStepProfile_eq]
    split_ifs
    · exact hV
    · simp
  have hF : ‖F‖ ≤ Cᵦ + 1 := (norm_sub_le _ _).trans (add_le_add (hb t ht s hs A B hA hB hAB) hP)
  have hF2 : ‖F‖ ^ 2 ≤ (Cᵦ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
  have hi₀ : 0 ≤ (chiDualSpatialBand ((A : ℝ) - 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => (Cᵦ + 1) ^ 2) t :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hi₁ : 0 ≤ (chiDualSpatialBand ((B : ℝ) + 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => (Cᵦ + 1) ^ 2) t :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  change ‖F‖ ^ 2 ≤ _
  by_cases hleft : t ∈ chiDualSpatialBand ((A : ℝ) - 1 / 2) ((m : ℝ) ^ 6)
  · rw [Set.indicator_of_mem hleft]
    linarith only [hF2, hi₁, sq_nonneg ((Cᵢ + Cₑ) / (m : ℝ))]
  by_cases hright : t ∈ chiDualSpatialBand ((B : ℝ) + 1 / 2) ((m : ℝ) ^ 6)
  · rw [Set.indicator_of_mem hright]
    linarith only [hF2, hi₀, sq_nonneg ((Cᵢ + Cₑ) / (m : ℝ))]
  rw [Set.indicator_of_notMem hleft, Set.indicator_of_notMem hright, add_zero, add_zero]
  have hl : ¬ ((A : ℝ) - 1 / 2 - (m : ℝ) ^ 6 ≤ a ∧ a ≤ (A : ℝ) - 1 / 2 + (m : ℝ) ^ 6) :=
    (mem_chiDualSpatialBand t _ _).not.mp hleft
  have hu : ¬ ((B : ℝ) + 1 / 2 - (m : ℝ) ^ 6 ≤ a ∧ a ≤ (B : ℝ) + 1 / 2 + (m : ℝ) ^ 6) :=
    (mem_chiDualSpatialBand t _ _).not.mp hright
  have hsmall : ‖F‖ ≤ (Cᵢ + Cₑ) / m := by
    by_cases hin : (A : ℝ) - 1 / 2 ≤ a ∧ a ≤ (B : ℝ) + 1 / 2
    · have hil : (A : ℝ) - 1 / 2 ≤ a - (m : ℝ) ^ 6 := by
        by_contra h
        exact hl ⟨by linarith only [hin.1, hh], by linarith only [h]⟩
      have hiu : a + (m : ℝ) ^ 6 ≤ (B : ℝ) + 1 / 2 := by
        by_contra h
        exact hu ⟨by linarith only [h], by linarith only [hin.2, hh]⟩
      have hv := hi s hs a ha hat A B hA hB hAB hil hiu
      rw [hta] at hv
      have heq : F = chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t - V := by
        dsimp only [F]
        rw [chiDualSpatialStepProfile_eq, if_pos hin]
      rw [heq]
      exact hv.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hCₑ.le) hm0.le)
    · have hside : (B : ℝ) + 1 / 2 ≤ a - (m : ℝ) ^ 6 ∨ a + (m : ℝ) ^ 6 ≤ (A : ℝ) - 1 / 2 := by
        by_cases hal : (A : ℝ) - 1 / 2 ≤ a
        · have hau : (B : ℝ) + 1 / 2 < a := lt_of_not_ge (fun h => hin ⟨hal, h⟩)
          left
          by_contra h
          exact hu ⟨by linarith only [hau, hh], by linarith only [h]⟩
        · right
          by_contra h
          exact hl ⟨by linarith only [h], by linarith only [hal, hh]⟩
      have hv := he s hs a ha hat A B hA hB hAB hside
      rw [hta] at hv
      have heq : F = chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t := by
        dsimp only [F]
        rw [chiDualSpatialStepProfile_eq, if_neg hin, sub_zero]
      rw [heq]
      exact hv.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hCᵢ.le) hm0.le)
  exact pow_le_pow_left₀ (norm_nonneg _) hsmall 2

private theorem integrable_chiDualSpatialBand (b h M : ℝ) :
    Integrable ((chiDualSpatialBand b h).indicator (fun _ => M ^ 2)) volume := by
  exact (integrableOn_const (by simp [chiDualSpatialBand]) :
    IntegrableOn (fun _ : ℝ => M ^ 2) (chiDualSpatialBand b h) volume).integrable_indicator measurableSet_Icc

private theorem integral_chiDualSpatialBand_le (b : ℝ) {h : ℝ} (hh : 0 ≤ h) (M N : ℝ) :
    (∫ t in Icc N (2 * N), (chiDualSpatialBand b h).indicator (fun _ => M ^ 2) t) ≤
      4 * Real.pi * h * M ^ 2 := by
  have hi := integrable_chiDualSpatialBand b h M
  have hb := setIntegral_le_integral (s := Icc N (2 * N)) hi
    (Filter.Eventually.of_forall (fun t => Set.indicator_nonneg (fun _ _ => sq_nonneg M) t))
  apply hb.trans_eq
  rw [integral_indicator_const (μ := volume) (s := chiDualSpatialBand b h)
    (M ^ 2) (show MeasurableSet (chiDualSpatialBand b h) from measurableSet_Icc)]
  have hab : 2 * Real.pi * (b - h) ≤ 2 * Real.pi * (b + h) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hh]
  rw [show chiDualSpatialBand b h = Icc (2 * Real.pi * (b - h)) (2 * Real.pi * (b + h)) from rfl,
    Real.volume_real_Icc_of_le hab, smul_eq_mul]
  ring

/-- The Gaussian step profile approximates the complete literal dual block
in mean square over the entire physical height window, including transitions.
Measurability and integrability are consequences of the actual source formulas. -/
theorem exists_chiDual_integer_block_mean_square_profile
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      IntegrableOn (fun t => ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
        chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2)
          (Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)) volume ∧
      ((∫ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10),
        ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
          chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2) / (m : ℝ) ^ 10) ≤ C / (m : ℝ) ^ 2 := by
  obtain ⟨E, M, hE, hM, hmajor⟩ := exists_chiDual_integer_block_profile_majorant c hr hc0 hc1
  refine ⟨E ^ 2 + 8 * Real.pi * M ^ 2, by positivity, ?_⟩
  filter_upwards [hmajor, eventually_ge_atTop (1 : ℕ)] with m hmajor hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hN0 : (0 : ℝ) < (m : ℝ) ^ 10 := by positivity
  intro s hs A B hA hB hAB
  have hdist : dist s c ≤ r := Metric.mem_closedBall.mp hs
  have hre : |s.re - c.re| ≤ dist s c := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
  have hs1 : s.re < 1 := by
    have hl := (abs_le.mp (hre.trans hdist)).2
    linarith only [hl, hc1]
  let F : ℝ → ℝ := fun t => ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
    chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2
  let J₀ : ℝ → ℝ := (chiDualSpatialBand ((A : ℝ) - 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2)
  let J₁ : ℝ → ℝ := (chiDualSpatialBand ((B : ℝ) + 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2)
  let G : ℝ → ℝ := fun t => (E / m) ^ 2 + J₀ t + J₁ t
  let W := Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)
  have hJ₀ : Integrable J₀ volume := integrable_chiDualSpatialBand _ _ M
  have hJ₁ : Integrable J₁ volume := integrable_chiDualSpatialBand _ _ M
  have hc : IntegrableOn (fun _ : ℝ => (E / m) ^ 2) W volume := integrableOn_const (by simp [W])
  have hG : IntegrableOn G W volume := (hc.add hJ₀.integrableOn).add hJ₁.integrableOn
  have hfmeas : AEStronglyMeasurable F (volume.restrict W) := by
    have hS := (continuous_chiDualIntegerBlock hs1 ((m : ℝ) ^ 10) A B).continuousOn.aestronglyMeasurable
      (μ := volume) (s := W) measurableSet_Icc
    have hP := aestronglyMeasurable_chiDualSpatialStepProfile hN0 A B
    exact ((hS.sub hP).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hpoint : ∀ t ∈ W, F t ≤ G t := hmajor s hs A B hA hB hAB
  have hF : IntegrableOn F W volume := by
    apply hG.mono' hfmeas
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint t ht)
  refine ⟨hF, ?_⟩
  have hint := setIntegral_mono_on hF hG measurableSet_Icc hpoint
  have hsum : (∫ t in W, G t) ≤
      (E / m) ^ 2 * (m : ℝ) ^ 10 + 8 * Real.pi * (m : ℝ) ^ 6 * M ^ 2 := by
    have hsplit : (∫ t in W, G t) =
        ((∫ t in W, (E / m) ^ 2) + ∫ t in W, J₀ t) + ∫ t in W, J₁ t := by
      calc
        _ = (∫ t in W, (E / m) ^ 2 + J₀ t) + ∫ t in W, J₁ t :=
          integral_add (Integrable.fun_add hc hJ₀.integrableOn) hJ₁.integrableOn
        _ = _ := congrArg (fun x : ℝ => x + ∫ t in W, J₁ t)
          (integral_add hc hJ₀.integrableOn)
    rw [hsplit, setIntegral_const]
    change ((volume.real (Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10))) • (E / m) ^ 2 +
      ∫ t in W, J₀ t) + ∫ t in W, J₁ t ≤ _
    rw [Real.volume_real_Icc_of_le (by linarith only [hN0]), smul_eq_mul]
    have hj0 := integral_chiDualSpatialBand_le ((A : ℝ) - 1 / 2) (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 6) M ((m : ℝ) ^ 10)
    have hj1 := integral_chiDualSpatialBand_le ((B : ℝ) + 1 / 2) (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 6) M ((m : ℝ) ^ 10)
    change (2 * (m : ℝ) ^ 10 - (m : ℝ) ^ 10) * (E / m) ^ 2 +
      (∫ t in W, J₀ t) + (∫ t in W, J₁ t) ≤ _
    linarith only [hj0, hj1]
  have hraw := div_le_div_of_nonneg_right (hint.trans hsum) hN0.le
  change (∫ t in W, F t) / (m : ℝ) ^ 10 ≤ _
  apply hraw.trans
  have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by
    have h2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm1
    nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg (m : ℝ))]
  calc
    _ = E ^ 2 / (m : ℝ) ^ 2 + (8 * Real.pi * M ^ 2) / (m : ℝ) ^ 4 := by field_simp
    _ ≤ E ^ 2 / (m : ℝ) ^ 2 + (8 * Real.pi * M ^ 2) / (m : ℝ) ^ 2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
    _ = _ := by ring

end RHTower
