import GaloisForLFunctions.RHTower.AutocorrelationBlindInterpolationObstruction
import GaloisForLFunctions.RHTower.EvenSectorSmoothTraceCorrection

/-!
# Failure of positive interior interpolation within smooth real EWU

Replace the rectangular pulses by the corpus's smooth even polar profile and
center the train. The exact overlap counts survive, so the counterexamples
belong to `RealSmoothEvenPolarTestFn` itself.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ContDiff

noncomputable section

namespace RHTower.EvenSector.SmoothBlindInterpolation

open ArchimedeanAnomaly AutocorrelationKrein WeilOneSided SeparatedBump

def packet : ℝ → ℝ := evenPolarProfile 20

theorem packet_smooth : ContDiff ℝ ∞ packet := contDiff_evenPolarProfile_infty 20

theorem packet_compact : HasCompactSupport packet := by
  change HasCompactSupport (evenPolarProfile 20)
  exact SeparatedBump.hasCompactSupport_of_abs_gt (R := 6 * (nodeBump 20).rOut / 2)
    (fun u hu => evenPolarProfile_eq_zero 20 hu)

theorem packet_diameter_lt : 6 * (nodeBump 20).rOut < pulseWidth := by
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  rw [nodeBump_rOut]
  unfold pulseWidth
  norm_num at hlog ⊢
  linarith

def packetMass : ℝ := autocorr packet 0

theorem packetMass_pos : 0 < packetMass := by
  rw [packetMass, AutocorrelationKrein.autocorr_zero_eq]
  exact lt_of_lt_of_le
    (mul_pos (inv_pos.mpr (nodeScale_pos 20)) (integral_narrowBump_sq_pos 0))
    (le_integral_evenPolarProfile_sq 20)

theorem packet_autocorr_zero {x : ℝ} (hx : pulseWidth ≤ |x|) : autocorr packet x = 0 := by
  unfold autocorr
  have hpt (u : ℝ) : packet u * packet (u + x) = 0 := by
    have h := mul_translate_eq_zero (fun u hu => evenPolarProfile_eq_zero 20 hu)
      (p := 0) (q := -x) (by simpa using packet_diameter_lt.trans_le hx) u
    simpa only [packet, sub_zero, sub_neg_eq_add] using h
  simp_rw [hpt]
  exact integral_zero _ _

def center (N i : ℕ) : ℝ := i * pulseSpacing - N * pulseSpacing / 2

def translate (N i : ℕ) (u : ℝ) : ℝ := packet (u - center N i)

def train (N : ℕ) (u : ℝ) : ℝ := ∑ i ∈ Finset.range (N + 1), translate N i u

theorem train_smooth (N : ℕ) : ContDiff ℝ ∞ (train N) := by
  apply ContDiff.sum
  intro i _
  exact packet_smooth.comp (contDiff_id.sub contDiff_const)

theorem train_compact (N : ℕ) : HasCompactSupport (train N) := by
  have h (i : ℕ) : HasCompactSupport (translate N i) :=
    packet_compact.comp_homeomorph (Homeomorph.subRight (center N i))
  convert! HasCompactSupport.finset_sum (s := Finset.range (N + 1))
    (f := translate N) (fun i _ => h i) using 1
  funext u
  simp [train]

theorem train_even (N : ℕ) (u : ℝ) : train N (-u) = train N u := by
  have he (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
      translate N i (-u) = translate N (N - i) u := by
    have hiN : i ≤ N := by simpa using Finset.mem_range.mp hi
    unfold translate center
    rw [Nat.cast_sub hiN]
    have ha : -u - (i * pulseSpacing - N * pulseSpacing / 2) =
        -(u - ((N - (i : ℝ)) * pulseSpacing - N * pulseSpacing / 2)) := by ring
    rw [ha]
    exact evenPolarProfile_neg 20 _
  unfold train
  rw [Finset.sum_congr rfl he]
  simpa only [Nat.add_sub_cancel] using
    Finset.sum_range_reflect (fun i => translate N i u) (N + 1)

theorem train_polar (N : ℕ) : paperFT (fun u => (train N u : ℂ)) (I / 2) = 0 := by
  have he : (fun u => (train N u : ℂ)) =
      fun u => ∑ i ∈ Finset.range (N + 1), (1 : ℂ) *
        (fun v => (packet v : ℂ)) (u - center N i) := by
    funext u
    simp [train, translate]
  rw [he]
  change paperFT (fun u => ∑ i ∈ Finset.range (N + 1), (1 : ℂ) *
    (evenPolarProfile 20 (u - center N i) : ℂ)) (I / 2) = 0
  rw [paperFT_sum_translate _ _ _ (continuous_evenPolarProfileC 20)
    (hasCompactSupport_evenPolarProfileC 20), paperFT_evenPolarProfile_I_div_two, mul_zero]

theorem train_complex_smooth (N : ℕ) : ContDiff ℝ ∞ (fun u => (train N u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (train_smooth N)

theorem train_complex_contDiff_two (N : ℕ) : ContDiff ℝ 2 (fun u => (train N u : ℂ)) :=
  (train_complex_smooth N).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

theorem train_complex_compact (N : ℕ) : HasCompactSupport (fun u => (train N u : ℂ)) :=
  HasCompactSupport.comp_left (f := train N) (g := Complex.ofReal)
    (train_compact N) Complex.ofReal_zero

/-- The counterexample is packaged in the precise real smooth EWU domain. -/
def test (N : ℕ) : RealSmoothEvenPolarTestFn :=
  ⟨⟨⟨⟨fun u => (train N u : ℂ),
      train_complex_contDiff_two N,
      train_complex_compact N⟩,
      (fun u => congrArg Complex.ofReal (train_even N u)), train_polar N⟩,
      train_complex_smooth N⟩,
      fun _ => Complex.ofReal_im _⟩

theorem translate_overlap (N i j : ℕ) (x : ℝ) :
    (∫ u, translate N i (u + x) * translate N j u) =
      autocorr packet (x - (i * pulseSpacing - j * pulseSpacing)) := by
  calc
    _ = ∫ u, packet (u - center N j) *
        packet ((u - center N j) + (x - (i * pulseSpacing - j * pulseSpacing))) := by
      congr 1
      funext u
      unfold translate center
      rw [show u - (j * pulseSpacing - N * pulseSpacing / 2) +
        (x - (i * pulseSpacing - j * pulseSpacing)) =
        u + x - (i * pulseSpacing - N * pulseSpacing / 2) by ring]
      ring
    _ = _ := integral_sub_right_eq_self (μ := volume)
      (fun u => packet u * packet (u + (x - (i * pulseSpacing - j * pulseSpacing))))
      (center N j)

/-- Reuse the previously proved separation of the rectangular pulse centers. -/
theorem translate_overlap_zero_of_pulse_overlap_zero (N i j : ℕ) (x : ℝ)
    (h : (∫ u, pulse i (u + x) * pulse j u) = 0) :
    (∫ u, translate N i (u + x) * translate N j u) = 0 := by
  rw [translate_overlap]
  apply packet_autocorr_zero
  rw [pulse_overlap] at h
  have hle := le_max_right (0 : ℝ)
    (pulseWidth - |x - (i * pulseSpacing - j * pulseSpacing)|)
  rw [h] at hle
  linarith

theorem translate_overlap_zero (N i j : ℕ) :
    (∫ u, translate N i u * translate N j u) = if i = j then packetMass else 0 := by
  by_cases hij : i = j
  · subst j
    have h := translate_overlap N i i 0
    simpa only [sub_self, add_zero, ite_true, packetMass] using h
  · rw [if_neg hij]
    have h := translate_overlap_zero_of_pulse_overlap_zero N i j 0
      (by simp only [add_zero, pulse_overlap_zero, if_neg hij])
    simpa only [add_zero] using h

theorem translate_overlap_spacing (N i j : ℕ) :
    (∫ u, translate N i (u + pulseSpacing) * translate N j u) =
      if i = j + 1 then packetMass else 0 := by
  by_cases hij : i = j + 1
  · rw [if_pos hij, translate_overlap, hij, Nat.cast_add, Nat.cast_one]
    rw [show pulseSpacing - ((j + 1) * pulseSpacing - j * pulseSpacing) = 0 by ring]
    rfl
  · rw [if_neg hij]
    exact translate_overlap_zero_of_pulse_overlap_zero N i j pulseSpacing
      (by rw [pulse_overlap_spacing, if_neg hij])

theorem translate_overlap_blind (N i j : ℕ) :
    (∫ u, translate N i (u + Real.log 2) * translate N j u) = 0 :=
  translate_overlap_zero_of_pulse_overlap_zero N i j (Real.log 2) (pulse_overlap_blind i j)

theorem train_autocorr (N : ℕ) (x : ℝ) :
    autocorr (train N) x =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ∫ u, translate N i (u + x) * translate N j u := by
  have hi (i j : ℕ) : Integrable (fun u => translate N i (u + x) * translate N j u) :=
    (((packet_smooth.continuous.comp (continuous_id.sub continuous_const)).comp
      (continuous_id.add continuous_const)).mul
      (packet_smooth.continuous.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
        (((packet_compact.comp_homeomorph (Homeomorph.subRight (center N i))).comp_homeomorph
          (Homeomorph.addRight x)).mul_right)
  unfold autocorr train
  have he : (fun u => (∑ i ∈ Finset.range (N + 1), translate N i u) *
      (∑ i ∈ Finset.range (N + 1), translate N i (u + x))) =
      fun u => ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        translate N i (u + x) * translate N j u := by
    funext u
    rw [mul_comm]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (fun j _ => hi i j)

theorem train_autocorr_zero (N : ℕ) : autocorr (train N) 0 = (N + 1) * packetMass := by
  rw [train_autocorr]
  simp only [add_zero, translate_overlap_zero, Finset.sum_ite_eq, Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
  simp

theorem train_autocorr_spacing (N : ℕ) : autocorr (train N) pulseSpacing = N * packetMass := by
  rw [train_autocorr, Finset.sum_comm]
  simp_rw [translate_overlap_spacing]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.add_lt_add_iff_right]
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))]
  simp

theorem train_autocorr_blind (N : ℕ) : autocorr (train N) (Real.log 2) = 0 := by
  simp [train_autocorr, translate_overlap_blind]

theorem test_weilTest (N : ℕ) (x : ℝ) :
    EF.weilTest (test N).1.1.1.1 (test N).1.1.1.1 x = (autocorr (train N) x : ℂ) :=
  AutocorrelationKrein.weilTest_eq _ _

/-- Even in the precise smooth real polar domain, a single prime-2 blind shift
cannot force a positive universal deficit at every interior point. -/
theorem exists_smooth_polar_blind_small_interior_deficit (ε : Set.Ioi (0 : ℝ)) :
    ∃ g : RealSmoothEvenPolarTestFn,
      0 < (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re ∧
      EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log 2) = 0 ∧
      (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
        (EF.weilTest g.1.1.1.1 g.1.1.1.1 pulseSpacing).re <
          ε * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε.1)
  refine ⟨test N, ?_, ?_, ?_⟩
  · rw [test_weilTest, Complex.ofReal_re, train_autocorr_zero]
    exact mul_pos (by positivity) packetMass_pos
  · rw [test_weilTest, train_autocorr_blind, Complex.ofReal_zero]
  · simp only [test_weilTest, Complex.ofReal_re, train_autocorr_zero, train_autocorr_spacing]
    have hN' : 1 < (N : ℝ) * ε.1 := (div_lt_iff₀ ε.2).mp hN
    have h := mul_lt_mul_of_pos_right (show 1 < ε.1 * (N + 1) by nlinarith [ε.2]) packetMass_pos
    nlinarith

/-- There is no positive universal interior deficit constant, even on smooth real EWU. -/
theorem not_exists_positive_uniform_smooth_polar_interior_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ g : RealSmoothEvenPolarTestFn,
      0 < (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re →
      EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log 2) = 0 →
      c * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re ≤
        (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
          (EF.weilTest g.1.1.1.1 g.1.1.1.1 pulseSpacing).re := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨g, hpos, hblind, hlt⟩ := exists_smooth_polar_blind_small_interior_deficit ⟨c, hc⟩
  exact (not_lt_of_ge (hbound g hpos hblind)) hlt

end RHTower.EvenSector.SmoothBlindInterpolation
