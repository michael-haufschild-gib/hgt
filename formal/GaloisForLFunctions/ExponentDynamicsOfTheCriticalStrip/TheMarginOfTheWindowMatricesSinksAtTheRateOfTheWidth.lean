import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.StepPacketMassAndGroundEnergy
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize

/-!
# The margin of the window matrices sinks at the rate of the width

The margin of a window is the depth of the second negative square of its neutral matrix. A margin
that sinks at a rate `θ < ½` in the ratio confines the zeros to `|Re ρ − ½| ≤ θ`. This module
proves the converse rate law, for all packets and with no hypothesis on the zeros.

* **All packets** (`neg_packetLogEnergy_le_packetForm`): for a bounded packet `g` supported in an
  interval of length below `2A`, Weil's form satisfies
  `𝔚(g) ≥ −160 · L(A, w) (E(g) + ∫ g²)`, where `w` is the zero width,
  `L(A, w) = 4 (2A + 2 + 2π) e^{2π} e^{w(2A+3)}` and
  `E(g) = ∫₀¹ ‖g(· + t) − g‖² dt/t` is the logarithmic energy. Smoothing lowers the energy at
  every displacement, so the floor of the smooth sources passes to the limit.
* **Step packets** (`neg_windowMarginDepth_le_packetForm_stepPacket`): a step packet on the unit
  cells of `(R, R + J]` has `E ≤ 12 log(1 + R + J) Σ σ_j²`: a cell moves by at most
  `3 (R + J) t` of its mass under a displacement `t`, and at each point at most two cells
  contribute to a difference. Hence `𝔚 ≥ −D Σ σ_j²` with
  `D ≤ C (1 + log Q) Q^{w} (1 + log(R + J))` for a window of ratio `Q`.
* **Window matrices** (`exists_neutralWindow_marginDepth`): for `θ ≥ w` and every window
  `(R, (3K + 1)R]`, the neutral matrix plus `C (1 + log K)² K^θ (1 + log R)` has at most one
  negative square. With the seed `w ≤ 3/8` this is a statement about finite matrices with no
  hypothesis (`exists_neutralWindow_marginDepth_three_eighths`).
* **Polynomial block size** (`exists_neutralWindow_marginRate_of_blockSize_le_pow`): on the
  windows with `R ≤ K^A` the shift `C K^{θ+ε}` suffices, the shape of the receiver.

The factor `1 + log R` is the number of zeros in a unit window at the height that a packet of
block size `R` resolves. It is absent in the mass normalisation exactly when the zeros off the
line do not cluster.
-/

open Finset Filter Topology MeasureTheory Matrix
open scoped Real
open Zeta23
open GaloisForLFunctions.HTGeometry (hermQuad hermNegIndex)
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_le_three_eighths)
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-! ### 1. Bounded packets -/

section Packet

variable {g : ℝ → ℝ} {M l r : ℝ}

/-- Products of a bounded packet with its translates are integrable. -/
theorem integrable_packet_mul_shift (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M)
    (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) (x : ℝ) : Integrable fun u => g u * g (u + x) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgb 0)
  refine integrable_of_bounded_of_support (C := M * M) (l := l) (r := r)
    (hgm.mul (hgm.comp (measurable_id.add_const x))) (fun u => ?_) fun u hu => ?_
  · rw [abs_mul]
    exact mul_le_mul (hgb _) (hgb _) (abs_nonneg _) hM0
  · exact hsupp u (left_ne_zero_of_mul hu)

theorem integrable_packet_sq (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M)
    (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) : Integrable fun u => g u ^ 2 := by
  have h := integrable_packet_mul_shift hgm hgb hsupp 0
  simp only [add_zero] at h
  exact h.congr (Eventually.of_forall fun u => (sq (g u)).symm)

/-- `2 (h(0) − h(x)) = ∫ (g(u + x) − g(u))² du` for a bounded packet with autocorrelation `h`. -/
theorem two_mul_packetAutocorr_drop (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M)
    (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) (x : ℝ) :
    2 * (packetAutocorr g 0 - packetAutocorr g x) = ∫ u, (g (u + x) - g u) ^ 2 :=
  two_mul_packetAutocorr_zero_sub (integrable_packet_sq hgm hgb hsupp)
    (integrable_packet_mul_shift hgm hgb hsupp x)

theorem packetAutocorr_drop_nonneg (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M)
    (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) (x : ℝ) :
    0 ≤ 2 * (packetAutocorr g 0 - packetAutocorr g x) := by
  rw [two_mul_packetAutocorr_drop hgm hgb hsupp x]
  exact integral_nonneg fun u => sq_nonneg _

theorem integrable_packet_shift_sub_sq (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M)
    (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) (x : ℝ) :
    Integrable fun u => (g (u + x) - g u) ^ 2 := by
  have e : (fun u => (g (u + x) - g u) ^ 2) =
      fun u => g (u + x) ^ 2 - 2 * (g u * g (u + x)) + g u ^ 2 := by
    funext u
    ring
  rw [e]
  exact (((integrable_packet_sq hgm hgb hsupp).comp_add_right x).sub
    ((integrable_packet_mul_shift hgm hgb hsupp x).const_mul 2)).add
    (integrable_packet_sq hgm hgb hsupp)

/-- The energy at displacement `t` of the complex translate of a bounded real packet. -/
theorem integral_norm_sq_translate_sub (hgm : Measurable g) (hgb : ∀ u, |g u| ≤ M)
    (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) (c t : ℝ) :
    ∫ u, ‖((g (u + t - c) : ℝ) : ℂ) - ((g (u - c) : ℝ) : ℂ)‖ ^ 2 =
      2 * (packetAutocorr g 0 - packetAutocorr g t) := by
  rw [two_mul_packetAutocorr_drop hgm hgb hsupp t,
    ← integral_sub_right_eq_self (fun u => (g (u + t) - g u) ^ 2) c]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show ‖((g (u + t - c) : ℝ) : ℂ) - ((g (u - c) : ℝ) : ℂ)‖ ^ 2 =
    (g (u - c + t) - g (u - c)) ^ 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    show u + t - c = u - c + t by ring]

/-- The logarithmic energy of a real packet in the coordinate of its autocorrelation `h`:
`∫₀¹ 2 (h(0) − h(t)) dt/t = ∫₀¹ ‖g(· + t) − g‖² dt/t`. -/
def packetLogEnergy (g : ℝ → ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, 2 * (packetAutocorr g 0 - packetAutocorr g t) / t

end Packet

/-! ### 2. The floor on all packets -/

theorem hasCompactSupport_of_support_le {G : ℝ → ℝ} {l r : ℝ}
    (hGs : ∀ u, G u ≠ 0 → l ≤ u ∧ u ≤ r) : HasCompactSupport G :=
  HasCompactSupport.intro (isCompact_Icc (a := l) (b := r)) fun u hu => by
    by_contra hne
    exact hu (hGs u hne)

/-- A smooth real packet supported in `[l, r]` with `r − l < 2A`, centred at the origin, as a
smooth source of aperture `A`. -/
def centredSource {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {l r : ℝ}
    (hGs : ∀ u, G u ≠ 0 → l ≤ u ∧ u ≤ r) {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : r - l < 2 * A.1) : _root_.RHTower.CCMComplexSmoothInteriorSource A where
  toFun := fun u => ((G (u - -((l + r) / 2)) : ℝ) : ℂ)
  smooth := by
    have h : ContDiff ℝ (⊤ : ℕ∞) fun u => G (u - -((l + r) / 2)) :=
      hG.comp (contDiff_id.sub contDiff_const)
    exact Complex.ofRealCLM.contDiff.comp h
  hasCompactSupport := by
    have h : HasCompactSupport fun u => G (u - -((l + r) / 2)) :=
      (hasCompactSupport_of_support_le hGs).comp_homeomorph
        (Homeomorph.subRight (-((l + r) / 2)))
    exact h.comp_left Complex.ofReal_zero
  tsupport_subset := by
    refine (closure_minimal (fun u hu => ?_) isClosed_Icc).trans
      (Set.Icc_subset_Ioo (a₁ := -((r - l) / 2)) (b₁ := (r - l) / 2) (by linarith) (by linarith))
    have hn : G (u - -((l + r) / 2)) ≠ 0 := fun hz =>
      hu (by simp only [hz, Complex.ofReal_zero])
    obtain ⟨h1, h2⟩ := hGs _ hn
    constructor <;> linarith

/-- **The floor on a smooth real packet**, with the logarithmic energy in the coordinate of the
autocorrelation; its density is integrable. -/
theorem neg_packetLogEnergy_le_zeroSum_of_smooth {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {M l r : ℝ} (hGb : ∀ u, |G u| ≤ M) (hGs : ∀ u, G u ≠ 0 → l ≤ u ∧ u ≤ r)
    {A : _root_.RHTower.SuzukiPositiveAperture} (hA : r - l < 2 * A.1) :
    IntervalIntegrable (fun t => 2 * (packetAutocorr G 0 - packetAutocorr G t) / t) volume 0 1 ∧
      -(160 * (logSamplingConst A.1 zetaZeroWidth * (packetLogEnergy G + packetAutocorr G 0))) ≤
        zeroSum G := by
  have hGm : Measurable G := hG.continuous.measurable
  have hfun : (fun t => (∫ x, ‖centredSource hG hGs hA (x + t) - centredSource hG hGs hA x‖ ^ 2) / t) =
      fun t => 2 * (packetAutocorr G 0 - packetAutocorr G t) / t := by
    funext t
    rw [← integral_norm_sq_translate_sub hGm hGb hGs (-((l + r) / 2)) t]
    rfl
  have hint : IntervalIntegrable
      (fun t => 2 * (packetAutocorr G 0 - packetAutocorr G t) / t) volume 0 1 := by
    have hs2 : ContDiff ℝ 2 (centredSource hG hGs hA : ℝ → ℂ) :=
      (centredSource hG hGs hA).smooth.of_le (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨K, hK⟩ := hs2.lipschitzWith_of_hasCompactSupport
      (centredSource hG hGs hA).hasCompactSupport (by norm_num)
    have h := intervalIntegrable_logEnergy_of_lipschitz A.2.le
      (_root_.RHTower.CCMParityQuartet.smoothSource_intervalSource (centredSource hG hGs hA)) hK
    rwa [hfun] at h
  refine ⟨hint, ?_⟩
  have hLE : logEnergy (centredSource hG hGs hA) = packetLogEnergy G := by
    unfold logEnergy packetLogEnergy
    rw [hfun]
  have hmass : (∫ x, ‖centredSource hG hGs hA x‖ ^ 2) = packetAutocorr G 0 := by
    show (∫ x, ‖((G (x - -((l + r) / 2)) : ℝ) : ℂ)‖ ^ 2) = packetAutocorr G 0
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [integral_sub_right_eq_self (fun u => G u ^ 2) (-((l + r) / 2))]
    simp only [packetAutocorr, add_zero, pow_two]
  have hW : (zetaZeroConfig.W (centredSource hG hGs hA) (centredSource hG hGs hA)).re =
      zeroSum G :=
    zeroSum_translate (hG.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
      (hasCompactSupport_of_support_le hGs) (-((l + r) / 2))
  have h := zetaZeroConfig_re_W_ge_neg_logEnergy (centredSource hG hGs hA)
  rwa [hLE, hmass, hW] at h

/-- **The converse rate law on all packets.** For a bounded packet `g` supported in an interval
of length below `2A`, with integrable jump density and integrable density of the logarithmic
energy, `𝔚_Q(g) ≥ −160 · L(A, w) (E(g) + ∫ g²)` with `w` the zero width. Smoothing lowers
`h(0) − h(t)` at every `t`, so the floor of the smoothed packets passes to the limit. -/
theorem neg_packetLogEnergy_le_packetForm {g : ℝ → ℝ} (hgm : Measurable g) {M l r : ℝ}
    (hgb : ∀ u, |g u| ≤ M) (hsupp : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r)
    {A : _root_.RHTower.SuzukiPositiveAperture} (hA : r - l < 2 * A.1)
    {Q : ℕ} (hQ : r - l < Real.log ((Q : ℝ) + 1))
    (hJ : IntegrableOn (levyJump g) (Set.Ioi 0))
    (hE : IntervalIntegrable
      (fun t => 2 * (packetAutocorr g 0 - packetAutocorr g t) / t) volume 0 1) :
    -(160 * (logSamplingConst A.1 zetaZeroWidth * (packetLogEnergy g + packetAutocorr g 0))) ≤
      packetForm Q g := by
  have hL := logSamplingConst_nonneg (σ := zetaZeroWidth) A.2.le
  have hradius : ∀ᶠ i : ℕ in atTop, (shrinkingBump i).rOut ≤ (A.1 - (r - l) / 2) / 2 := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iic_mem_nhds (by linarith only [hA]))
  have hbound : ∀ᶠ i : ℕ in atTop,
      -(160 * (logSamplingConst A.1 zetaZeroWidth *
        (packetLogEnergy g + packetAutocorr (mollify (shrinkingBump i) g) 0))) ≤
      zeroSum (mollify (shrinkingBump i) g) := by
    filter_upwards [hradius] with i hi
    have hGs : ∀ u, mollify (shrinkingBump i) g u ≠ 0 →
        l - (shrinkingBump i).rOut ≤ u ∧ u ≤ r + (shrinkingBump i).rOut := fun u hu =>
      ⟨(mollify_ne_zero (shrinkingBump i) hsupp u hu).1.le,
        (mollify_ne_zero (shrinkingBump i) hsupp u hu).2.le⟩
    obtain ⟨hint, hfloor⟩ := neg_packetLogEnergy_le_zeroSum_of_smooth
      (contDiff_top_mollify (shrinkingBump i) hgm hgb hsupp)
      (abs_mollify_le (shrinkingBump i) hgb) hGs (A := A) (by linarith only [hA, hi])
    have hmono : packetLogEnergy (mollify (shrinkingBump i) g) ≤ packetLogEnergy g := by
      unfold packetLogEnergy
      exact intervalIntegral.integral_mono_on zero_le_one hint hE fun t ht =>
        div_le_div_of_nonneg_right (by
          linarith only [packetAutocorr_mollify_sub_le (shrinkingBump i) hgm hgb hsupp t]) ht.1
    refine le_trans (neg_le_neg ?_) hfloor
    have := mul_le_mul_of_nonneg_left
      (add_le_add_right hmono (packetAutocorr (mollify (shrinkingBump i) g) 0)) hL
    linarith
  exact le_of_tendsto_of_tendsto
    (((((tendsto_packetAutocorr_mollify hgm hgb hsupp 0).const_add
      (packetLogEnergy g)).const_mul _).const_mul 160).neg)
    (tendsto_zeroSum_mollify hgm hgb hsupp hQ hJ) hbound

/-! ### 3. Flat packets -/

theorem flatPacket_nonneg (a b u : ℝ) : 0 ≤ flatPacket a b u := by
  unfold flatPacket
  exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u

theorem mem_of_flatPacket_ne_zero {a b u : ℝ} (h : flatPacket a b u ≠ 0) :
    u ∈ Set.Ioc (Real.log a) (Real.log b) := by
  by_contra hu
  exact h (by unfold flatPacket; exact Set.indicator_of_notMem hu _)

theorem flatPacket_support {a b u : ℝ} (h : flatPacket a b u ≠ 0) :
    Real.log a ≤ u ∧ u ≤ Real.log b :=
  ⟨(mem_of_flatPacket_ne_zero h).1.le, (mem_of_flatPacket_ne_zero h).2⟩

theorem packetAutocorr_flatPacket_nonneg (a b t : ℝ) : 0 ≤ packetAutocorr (flatPacket a b) t :=
  integral_nonneg fun u => mul_nonneg (flatPacket_nonneg a b u) (flatPacket_nonneg a b _)

/-- **The autocorrelation of a flat packet drops at most linearly**: `h(0) − h(t) ≤ (3/2) b t`
for the window `(a, b]` and `0 ≤ t ≤ 1`. -/
theorem packetAutocorr_flatPacket_drop_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    packetAutocorr (flatPacket a b) 0 - packetAutocorr (flatPacket a b) t ≤ 3 / 2 * b * t := by
  have hb : 0 < b := ha.trans_le hab
  rw [packetAutocorr_flatPacket_zero ha hb hab]
  rcases le_total t (Real.log b - Real.log a) with h | h
  · rw [packetAutocorr_flatPacket_of_le ha hb ht0 h]
    have h1 : 1 - t / 2 ≤ Real.exp (-t / 2) := by
      have := Real.add_one_le_exp (-t / 2)
      linarith
    have h2 : Real.exp (t / 2) ≤ 1 + t := by
      have hE : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
        rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
      have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (t / 2)).le
      rw [hE] at h3
      by_contra hcon
      have h4 := mul_pos (sub_pos.mpr (not_le.mp hcon)) (by linarith : (0 : ℝ) < 1 - t / 2)
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hb.le, mul_le_mul_of_nonneg_left h2 ha.le,
      mul_nonneg (sub_nonneg.mpr hab) ht0]
  · rw [packetAutocorr_flatPacket_of_ge ht0 h, sub_zero]
    have hlog : 1 - a / b ≤ Real.log b - Real.log a := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
      rwa [inv_div, Real.log_div hb.ne' ha.ne'] at this
    have h4 : b * (a / b) = a := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hb.ne']
    have h5 := mul_le_mul_of_nonneg_left (hlog.trans h) hb.le
    nlinarith [mul_nonneg hb.le ht0]

/-! ### 4. Step packets -/

/-- For two families with at most one nonzero member each, the square of the difference of two
combinations is at most twice the sum of the squares of the differences of the members. -/
theorem sq_sum_sub_sum_le {ι : Type*} (s : Finset ι) (σ p q : ι → ℝ)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i = 0 ∨ p j = 0)
    (hq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → q i = 0 ∨ q j = 0) :
    (∑ j ∈ s, σ j * p j - ∑ j ∈ s, σ j * q j) ^ 2 ≤
      2 * ∑ j ∈ s, σ j ^ 2 * (p j - q j) ^ 2 := by
  classical
  have hnn : ∀ j ∈ s, 0 ≤ σ j ^ 2 * (p j - q j) ^ 2 := fun j _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- one index carries each family
  have hone : ∀ f : ι → ℝ, (∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i = 0 ∨ f j = 0) → s.Nonempty →
      ∃ k ∈ s, ∀ j ∈ s, j ≠ k → f j = 0 := by
    intro f hf hs
    by_cases h : ∃ k ∈ s, f k ≠ 0
    · obtain ⟨k, hk, hfk⟩ := h
      exact ⟨k, hk, fun j hj hjk => (hf j hj k hk hjk).resolve_right hfk⟩
    · obtain ⟨k, hk⟩ := hs
      exact ⟨k, hk, fun j hj _ => by_contra fun hne => h ⟨j, hj, hne⟩⟩
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨k₁, hk₁, hpz⟩ := hone p hp hs
  obtain ⟨k₂, hk₂, hqz⟩ := hone q hq hs
  have hP : ∑ j ∈ s, σ j * p j = σ k₁ * p k₁ :=
    Finset.sum_eq_single_of_mem k₁ hk₁ fun j hj hne => by rw [hpz j hj hne, mul_zero]
  have hQ : ∑ j ∈ s, σ j * q j = σ k₂ * q k₂ :=
    Finset.sum_eq_single_of_mem k₂ hk₂ fun j hj hne => by rw [hqz j hj hne, mul_zero]
  rw [hP, hQ]
  by_cases hk : k₁ = k₂
  · rw [← hk]
    have h1 := Finset.single_le_sum hnn hk₁
    nlinarith [hnn k₁ hk₁]
  · have h0 := Finset.sum_pair (f := fun j => σ j ^ 2 * (p j - q j) ^ 2) hk
    have h1 : σ k₁ ^ 2 * (p k₁ - q k₁) ^ 2 + σ k₂ ^ 2 * (p k₂ - q k₂) ^ 2 ≤
        ∑ j ∈ s, σ j ^ 2 * (p j - q j) ^ 2 := by
      refine (le_of_eq h0.symm).trans (Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_)
        fun j hj _ => hnn j hj)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hk₁
      · rw [Finset.mem_singleton.mp hj]
        exact hk₂
    rw [hqz k₁ hk₁ hk, hpz k₂ hk₂ (Ne.symm hk)] at h1
    nlinarith [sq_nonneg (σ k₁ * p k₁ + σ k₂ * q k₂)]

/-- Two different unit cells do not meet. -/
theorem flatPacket_cell_eq_zero_or {R i j : ℕ} (hR : 1 ≤ R) (hij : i ≠ j) (x : ℝ) :
    flatPacket ((R + i : ℕ) : ℝ) ((R + (i + 1) : ℕ) : ℝ) x = 0 ∨
      flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) x = 0 := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have m1 := mem_of_flatPacket_ne_zero h1
  have m2 := mem_of_flatPacket_ne_zero h2
  rcases lt_or_gt_of_ne hij with h | h
  · have hlog : Real.log ((R + (i + 1) : ℕ) : ℝ) ≤ Real.log ((R + j : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < R + (i + 1)))
        (by exact_mod_cast (by omega : R + (i + 1) ≤ R + j))
    linarith [m1.2, m2.1]
  · have hlog : Real.log ((R + (j + 1) : ℕ) : ℝ) ≤ Real.log ((R + i : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < R + (j + 1)))
        (by exact_mod_cast (by omega : R + (j + 1) ≤ R + i))
    linarith [m2.2, m1.1]

theorem measurable_stepPacket (R J : ℕ) (σ : ℕ → ℝ) : Measurable (stepPacket R J σ) := by
  unfold stepPacket
  exact Finset.measurable_sum _ fun j _ => (measurable_flatPacket _ _).const_mul (σ j)

theorem abs_stepPacket_le (R J : ℕ) (σ : ℕ → ℝ) (u : ℝ) :
    |stepPacket R J σ u| ≤
      ∑ j ∈ range J, |σ j| * Real.exp (Real.log ((R + (j + 1) : ℕ) : ℝ) / 2) := by
  unfold stepPacket
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_flatPacket_le _ _ _) (abs_nonneg _)

/-- A step packet on the cells of `(R, R + J]` is supported in `[log R, log(R + J)]`. -/
theorem stepPacket_ne_zero {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) {u : ℝ}
    (hu : stepPacket R J σ u ≠ 0) :
    Real.log R ≤ u ∧ u ≤ Real.log ((R + J : ℕ) : ℝ) := by
  obtain ⟨j, hj, hne⟩ : ∃ j ∈ range J,
      σ j * flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hu (Finset.sum_eq_zero hcon)
  have hm := mem_of_flatPacket_ne_zero (right_ne_zero_of_mul hne)
  have hj' := Finset.mem_range.mp hj
  have h1 : Real.log (R : ℝ) ≤ Real.log ((R + j : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hR) (by exact_mod_cast (by omega : R ≤ R + j))
  have h2 : Real.log ((R + (j + 1) : ℕ) : ℝ) ≤ Real.log ((R + J : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < R + (j + 1)))
      (by exact_mod_cast (by omega : R + (j + 1) ≤ R + J))
  exact ⟨h1.trans hm.1.le, hm.2.trans h2⟩

theorem integrableOn_levyJump_stepPacket {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    IntegrableOn (levyJump (stepPacket R J σ)) (Set.Ioi 0) := by
  rw [stepPacket_eq_nested hR J σ]
  exact integrableOn_levyJump_step (x := fun j => R + j) hR
    (fun j hj => (nested_bounds R J j hj).1) (nestedCoeff J σ)

/-- **The energy of a step packet at a displacement is at most twice the sum of the energies of
its cells**: at each point at most two cells contribute to the difference. -/
theorem stepPacket_drop_le_sum {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) (t : ℝ) :
    2 * (packetAutocorr (stepPacket R J σ) 0 - packetAutocorr (stepPacket R J σ) t) ≤
      2 * ∑ j ∈ range J, σ j ^ 2 *
        (2 * (packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) 0 -
          packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) t)) := by
  have hcell : ∀ j : ℕ,
      2 * (packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) 0 -
        packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) t) =
      ∫ u, (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) (u + t) -
        flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u) ^ 2 := fun j =>
    two_mul_packetAutocorr_drop (measurable_flatPacket _ _) (abs_flatPacket_le _ _)
      (fun u hu => flatPacket_support hu) t
  have hd : ∀ j : ℕ, Integrable fun u =>
      (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) (u + t) -
        flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u) ^ 2 := fun j =>
    integrable_packet_shift_sub_sq (measurable_flatPacket _ _) (abs_flatPacket_le _ _)
      (fun u hu => flatPacket_support hu) t
  have hgi := integrable_packet_shift_sub_sq (measurable_stepPacket R J σ)
    (abs_stepPacket_le R J σ) (fun u hu => stepPacket_ne_zero hR J σ hu) t
  have hpoint : ∀ u, (stepPacket R J σ (u + t) - stepPacket R J σ u) ^ 2 ≤
      2 * ∑ j ∈ range J, σ j ^ 2 *
        (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) (u + t) -
          flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u) ^ 2 := fun u =>
    sq_sum_sub_sum_le (range J) σ
      (fun j => flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) (u + t))
      (fun j => flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u)
      (fun i _ j _ hij => flatPacket_cell_eq_zero_or hR hij _)
      (fun i _ j _ hij => flatPacket_cell_eq_zero_or hR hij _)
  rw [two_mul_packetAutocorr_drop (measurable_stepPacket R J σ) (abs_stepPacket_le R J σ)
    (fun u hu => stepPacket_ne_zero hR J σ hu) t]
  calc ∫ u, (stepPacket R J σ (u + t) - stepPacket R J σ u) ^ 2
      ≤ ∫ u, 2 * ∑ j ∈ range J, σ j ^ 2 *
          (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) (u + t) -
            flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u) ^ 2 :=
        integral_mono hgi
          ((integrable_finsetSum _ fun j _ => (hd j).const_mul (σ j ^ 2)).const_mul 2) hpoint
    _ = 2 * ∑ j ∈ range J, σ j ^ 2 *
          ∫ u, (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) (u + t) -
            flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ => (hd j).const_mul (σ j ^ 2)]
        simp only [integral_const_mul]
    _ = _ := by simp only [hcell]

/-- **The modulus of a step packet**: `‖g(· + t) − g‖² ≤ min(4, 6 (R + J) t) Σ σ_j²` for
`0 ≤ t ≤ 1`. -/
theorem stepPacket_drop_le {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * (packetAutocorr (stepPacket R J σ) 0 - packetAutocorr (stepPacket R J σ) t) ≤
        4 * ∑ j ∈ range J, σ j ^ 2 ∧
      2 * (packetAutocorr (stepPacket R J σ) 0 - packetAutocorr (stepPacket R J σ) t) ≤
        6 * ((R + J : ℕ) : ℝ) * t * ∑ j ∈ range J, σ j ^ 2 := by
  have hsum := stepPacket_drop_le_sum hR J σ t
  have hcell : ∀ j ∈ range J,
      packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) 0 -
          packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) t ≤ 1 ∧
        packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) 0 -
          packetAutocorr (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ)) t ≤
            3 / 2 * ((R + J : ℕ) : ℝ) * t := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have ha : (0 : ℝ) < ((R + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + j)
    have hab : ((R + j : ℕ) : ℝ) ≤ ((R + (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : R + j ≤ R + (j + 1))
    have hb : (0 : ℝ) < ((R + (j + 1) : ℕ) : ℝ) := ha.trans_le hab
    have hbN : ((R + (j + 1) : ℕ) : ℝ) ≤ ((R + J : ℕ) : ℝ) := by
      exact_mod_cast (by omega : R + (j + 1) ≤ R + J)
    have h0 := packetAutocorr_flatPacket_zero ha hb hab
    have hba : ((R + (j + 1) : ℕ) : ℝ) - ((R + j : ℕ) : ℝ) = 1 := by
      push_cast
      ring
    have hnn := packetAutocorr_flatPacket_nonneg ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) t
    have hdrop := packetAutocorr_flatPacket_drop_le ha hab ht0 ht1
    refine ⟨by linarith, hdrop.trans ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hbN ht0]
  constructor
  · refine hsum.trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    nlinarith [mul_le_mul_of_nonneg_left (hcell j hj).1 (sq_nonneg (σ j))]
  · refine hsum.trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    nlinarith [mul_le_mul_of_nonneg_left (hcell j hj).2 (sq_nonneg (σ j))]

/-- The density of the logarithmic energy of a step packet is at most
`12 Σ σ_j² · N/(1 + N t)` with `N = R + J`. -/
theorem stepPacket_drop_div_le {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * (packetAutocorr (stepPacket R J σ) 0 - packetAutocorr (stepPacket R J σ) t) / t ≤
      12 * (∑ j ∈ range J, σ j ^ 2) *
        (((R + J : ℕ) : ℝ) / (1 + ((R + J : ℕ) : ℝ) * t)) := by
  obtain ⟨h4, h6⟩ := stepPacket_drop_le hR J σ ht0 ht1
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((R + J : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j ∈ range J, σ j ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D =
      2 * (packetAutocorr (stepPacket R J σ) 0 - packetAutocorr (stepPacket R J σ) t) :=
    ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact Nat.cast_nonneg _
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← hD, ← hS] at h4
  rw [← hD, ← hS, ← hN] at h6
  rw [← hD, ← hS, ← hN]
  have hpos : 0 < 1 + N * t := by nlinarith [mul_nonneg hN0 ht0]
  rcases eq_or_lt_of_le ht0 with h0 | ht
  · have hz : D / t = 0 := by rw [← h0, div_zero]
    rw [hz]
    exact mul_nonneg (mul_nonneg (by norm_num) hS0) (div_nonneg hN0 hpos.le)
  · rw [div_le_iff₀ ht,
      show 12 * S * (N / (1 + N * t)) * t = 12 * S * N * t / (1 + N * t) by ring,
      le_div_iff₀ hpos]
    rcases le_total (N * t) 1 with h | h
    · nlinarith [mul_le_mul_of_nonneg_right h6 hpos.le,
        mul_nonneg (mul_nonneg (mul_nonneg hN0 ht0) hS0) (sub_nonneg.mpr h)]
    · nlinarith [mul_le_mul_of_nonneg_right h4 hpos.le, mul_nonneg hS0 (sub_nonneg.mpr h)]

theorem intervalIntegrable_div_one_add_mul {N : ℝ} (hN : 0 ≤ N) :
    IntervalIntegrable (fun t => N / (1 + N * t)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable (ContinuousOn.div continuousOn_const
    (Continuous.continuousOn (by fun_prop)) fun t ht => ?_)
  rw [Set.uIcc_of_le zero_le_one] at ht
  have := mul_nonneg hN ht.1
  exact ne_of_gt (by linarith)

/-- `∫₀¹ N/(1 + N t) dt = log(1 + N)`. -/
theorem integral_div_one_add_mul {N : ℝ} (hN : 0 ≤ N) :
    ∫ t in (0:ℝ)..1, N / (1 + N * t) = Real.log (1 + N) := by
  have hpos : ∀ t ∈ Set.uIcc (0:ℝ) 1, 0 < 1 + N * t := fun t ht => by
    rw [Set.uIcc_of_le zero_le_one] at ht
    have := mul_nonneg hN ht.1
    linarith
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t => Real.log (1 + N * t)) (N / (1 + N * t)) t := fun t ht => by
    have h := (((hasDerivAt_id' t).const_mul N).const_add 1).log (hpos t ht).ne'
    rwa [mul_one] at h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_div_one_add_mul hN)]
  simp

/-- The density of the logarithmic energy of a step packet is integrable. -/
theorem intervalIntegrable_stepPacket_drop {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    IntervalIntegrable (fun t =>
      2 * (packetAutocorr (stepPacket R J σ) 0 - packetAutocorr (stepPacket R J σ) t) / t)
      volume 0 1 := by
  refine ((intervalIntegrable_div_one_add_mul (N := ((R + J : ℕ) : ℝ))
    (Nat.cast_nonneg _)).const_mul (12 * ∑ j ∈ range J, σ j ^ 2)).mono_fun' ?_ ?_
  · exact (((measurable_const.sub (measurable_packetAutocorr_of_measurable
      (measurable_stepPacket R J σ))).const_mul 2).div measurable_id).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    show ‖2 * (packetAutocorr (stepPacket R J σ) 0 - packetAutocorr (stepPacket R J σ) t) / t‖ ≤
      12 * (∑ j ∈ range J, σ j ^ 2) * (((R + J : ℕ) : ℝ) / (1 + ((R + J : ℕ) : ℝ) * t))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (packetAutocorr_drop_nonneg
      (measurable_stepPacket R J σ) (abs_stepPacket_le R J σ)
      (fun u hu => stepPacket_ne_zero hR J σ hu) t) ht.1.le)]
    exact stepPacket_drop_div_le hR J σ ht.1.le ht.2

/-- **The logarithmic energy of a step packet** on the cells of `(R, R + J]` is at most
`12 log(1 + R + J)` times its mass. -/
theorem packetLogEnergy_stepPacket_le {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    packetLogEnergy (stepPacket R J σ) ≤
      12 * Real.log (1 + ((R + J : ℕ) : ℝ)) * ∑ j ∈ range J, σ j ^ 2 := by
  have hN : (0 : ℝ) ≤ ((R + J : ℕ) : ℝ) := Nat.cast_nonneg _
  calc packetLogEnergy (stepPacket R J σ)
      ≤ ∫ t in (0:ℝ)..1, 12 * (∑ j ∈ range J, σ j ^ 2) *
          (((R + J : ℕ) : ℝ) / (1 + ((R + J : ℕ) : ℝ) * t)) := by
        unfold packetLogEnergy
        exact intervalIntegral.integral_mono_on zero_le_one
          (intervalIntegrable_stepPacket_drop hR J σ)
          ((intervalIntegrable_div_one_add_mul hN).const_mul _)
          fun t ht => stepPacket_drop_div_le hR J σ ht.1 ht.2
    _ = 12 * Real.log (1 + ((R + J : ℕ) : ℝ)) * ∑ j ∈ range J, σ j ^ 2 := by
        rw [intervalIntegral.integral_const_mul, integral_div_one_add_mul hN]
        ring

/-! ### 5. The floor on step packets -/

/-- The depth allowed to the margin of a window of ratio `Q` on the integers up to `N`:
`160 · L((log Q + 1)/2, w) (12 log(1 + N) + 1)`. -/
def windowMarginDepth (Q N : ℕ) : ℝ :=
  160 * (logSamplingConst ((Real.log Q + 1) / 2) zetaZeroWidth *
    (12 * Real.log (1 + (N : ℝ)) + 1))

/-- **The floor on step packets**: on the cells of a window `(R, R + J]` of ratio at most `Q`,
Weil's form is at least `−D Σ σ_j²` with `D` the depth of the window. -/
theorem neg_windowMarginDepth_le_packetForm_stepPacket {R : ℕ} (hR : 1 ≤ R) {Q : ℕ}
    (hQ₀ : 1 ≤ Q) {J : ℕ} (hRJ : R + J ≤ Q * R) (σ : ℕ → ℝ) :
    -(windowMarginDepth Q (R + J) * ∑ j ∈ range J, σ j ^ 2) ≤
      packetForm Q (stepPacket R J σ) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ₀
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ₀)
  obtain ⟨A, hA⟩ : ∃ A : _root_.RHTower.SuzukiPositiveAperture, A.1 = (Real.log Q + 1) / 2 :=
    ⟨⟨(Real.log Q + 1) / 2, by positivity⟩, rfl⟩
  have hfloor := neg_packetLogEnergy_le_packetForm (g := stepPacket R J σ)
    (measurable_stepPacket R J σ) (abs_stepPacket_le R J σ)
    (l := Real.log R) (r := Real.log R + Real.log Q)
    (fun u hu => by
      obtain ⟨h1, h2⟩ := stepPacket_ne_zero hR J σ hu
      have hmul : Real.log ((Q : ℝ) * R) = Real.log Q + Real.log R :=
        Real.log_mul hQ'.ne' hR'.ne'
      have hle : Real.log ((R + J : ℕ) : ℝ) ≤ Real.log ((Q : ℝ) * R) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < R + J)) (by exact_mod_cast hRJ)
      exact ⟨h1, by linarith⟩)
    (A := A) (by rw [hA]; linarith) (Q := Q)
    (by rw [add_sub_cancel_left]; exact Real.log_lt_log hQ' (by linarith))
    (integrableOn_levyJump_stepPacket hR J σ) (intervalIntegrable_stepPacket_drop hR J σ)
  rw [hA, packetAutocorr_stepPacket_zero hR J σ] at hfloor
  refine le_trans (neg_le_neg ?_) hfloor
  have hE := packetLogEnergy_stepPacket_le hR J σ
  have hL := logSamplingConst_nonneg (σ := zetaZeroWidth) (a := (Real.log Q + 1) / 2)
    (by positivity)
  have h := mul_le_mul_of_nonneg_left (add_le_add_right hE (∑ j ∈ range J, σ j ^ 2)) hL
  unfold windowMarginDepth
  linarith

/-- The constant of the rate of the depth. -/
def windowRateConst (θ : ℝ) : ℝ := 8320 * (3 + 2 * π) * Real.exp (2 * π) * Real.exp (4 * θ)

theorem windowRateConst_nonneg (θ : ℝ) : 0 ≤ windowRateConst θ := by
  unfold windowRateConst
  have := Real.pi_pos
  positivity

/-- **The depth sinks at the rate of the width**: for `θ ≥ w`,
`D(Q, N) ≤ C_θ (1 + log Q) Q^θ (1 + log N)`. -/
theorem windowMarginDepth_le {θ : ℝ} (hθ : zetaZeroWidth ≤ θ) {Q N : ℕ} (hQ : 1 ≤ Q)
    (hN : 1 ≤ N) :
    windowMarginDepth Q N ≤
      windowRateConst θ * ((1 + Real.log Q) * (Q : ℝ) ^ θ * (1 + Real.log N)) := by
  have hπ := Real.pi_pos
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hq : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hn : 0 ≤ Real.log N := Real.log_nonneg hN'
  -- the exponential factor
  have hexp : Real.exp (zetaZeroWidth * (2 * ((Real.log Q + 1) / 2) + 3)) ≤
      Real.exp (4 * θ) * (Q : ℝ) ^ θ := by
    rw [Real.rpow_def_of_pos hQ', ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_right hθ (by linarith : (0 : ℝ) ≤ Real.log Q + 4)])
  -- the aperture factor
  have h1 : 2 * ((Real.log Q + 1) / 2) + 2 + 2 * π ≤ (3 + 2 * π) * (1 + Real.log Q) := by
    nlinarith [mul_nonneg hπ.le hq]
  -- the factor of the block size
  have h2 : 12 * Real.log (1 + (N : ℝ)) + 1 ≤ 13 * (1 + Real.log N) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) hNpos.ne'
    have h3 : Real.log (1 + (N : ℝ)) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have h20 : 0 ≤ 12 * Real.log (1 + (N : ℝ)) + 1 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + N)
    linarith
  have hX : 4 * (2 * ((Real.log Q + 1) / 2) + 2 + 2 * π) * Real.exp (2 * π) *
        Real.exp (zetaZeroWidth * (2 * ((Real.log Q + 1) / 2) + 3)) ≤
      4 * ((3 + 2 * π) * (1 + Real.log Q)) * Real.exp (2 * π) *
        (Real.exp (4 * θ) * (Q : ℝ) ^ θ) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num))
      (Real.exp_pos _).le) hexp (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith)))
        (Real.exp_pos _).le)
  have hY := mul_le_mul hX h2 h20
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith)))
      (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hQ'.le θ)))
  unfold windowMarginDepth logSamplingConst windowRateConst
  linarith

/-- The floor on step packets in terms of the rate. -/
theorem neg_rate_le_packetForm_stepPacket {θ : ℝ} (hθ : zetaZeroWidth ≤ θ) {R : ℕ} (hR : 1 ≤ R)
    {Q : ℕ} (hQ₀ : 1 ≤ Q) {J : ℕ} (hRJ : R + J ≤ Q * R) (σ : ℕ → ℝ) :
    -(windowRateConst θ * ((1 + Real.log Q) * (Q : ℝ) ^ θ *
        (1 + Real.log ((R + J : ℕ) : ℝ))) * ∑ j ∈ range J, σ j ^ 2) ≤
      packetForm Q (stepPacket R J σ) := by
  refine le_trans (neg_le_neg ?_) (neg_windowMarginDepth_le_packetForm_stepPacket hR hQ₀ hRJ σ)
  exact mul_le_mul_of_nonneg_right (windowMarginDepth_le hθ hQ₀ (by omega))
    (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-! ### 6. Window matrices -/

theorem dotProduct_const_diagonal_mulVec {J : ℕ} (c : ℝ) (y : Fin J → ℝ) :
    y ⬝ᵥ ((Matrix.diagonal fun _ => c : Matrix (Fin J) (Fin J) ℝ) *ᵥ y) = c * ∑ i, y i ^ 2 := by
  rw [dotProduct_mulVec_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i
    (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero])
    (fun h => absurd (Finset.mem_univ i) h), Matrix.diagonal_apply_eq]
  ring

/-- The form of a real matrix shifted by a multiple of the identity. -/
theorem hermQuad_add_diagonal {J : ℕ} (B : Matrix (Fin J) (Fin J) ℝ) (c : ℝ) (x : Fin J → ℂ) :
    hermQuad ((B + Matrix.diagonal fun _ => c).map (↑) : Matrix (Fin J) (Fin J) ℂ) x =
      hermQuad (B.map (↑) : Matrix (Fin J) (Fin J) ℂ) x +
        c * (∑ i, (x i).re ^ 2 + ∑ i, (x i).im ^ 2) := by
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, HeckeKreinToeplitz.hermQuad_map_ofReal,
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    dotProduct_const_diagonal_mulVec, dotProduct_const_diagonal_mulVec]
  ring

/-- **A floor of the block matrix bounds the index of the shifted neutral part**: if the block
matrix plus `c` is nonnegative, the neutral part plus `c` has at most one negative square. The
two agree where the first charge vanishes. -/
theorem hermNegIndex_neutralWindow_add_diagonal_le_one {Q R J : ℕ} {c : ℝ}
    (h : ∀ σ : ℕ → ℝ, 0 ≤ ∑ j ∈ range J, ∑ l ∈ range J,
      σ j * σ l * blockMatrix Q (R + j) (R + l) + c * ∑ j ∈ range J, σ j ^ 2) :
    hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => c).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  have h0 : hermNegIndex ((blockWindow Q R J + Matrix.diagonal fun _ => c).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) = 0 := by
    refine ArithmeticCastelnuovoSeveri.negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
    have hreal : ∀ y : Fin J → ℝ,
        0 ≤ y ⬝ᵥ (blockWindow Q R J *ᵥ y) + c * ∑ i, y i ^ 2 := fun y => by
      have hsq : ∑ i, y i ^ 2 = ∑ j ∈ range J, extendFin y j ^ 2 := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => extendFin y j ^ 2) J]
        exact Finset.sum_congr rfl fun i _ => by rw [extendFin_coe]
      rw [dotProduct_mulVec_eq_sum, blockWindow, sum_fin_windowMatrix_eq, hsq]
      exact h (extendFin y)
    rw [hermQuad_add_diagonal, HeckeKreinToeplitz.hermQuad_map_ofReal]
    have h1 := hreal fun i => (x i).re
    have h2 := hreal fun i => (x i).im
    linarith
  have h1 := HeckeKreinToeplitz.hermNegIndex_le_add_one_of_eq_on_ker
    ((neutralWindow Q R J + Matrix.diagonal fun _ => c).map (↑) : Matrix (Fin J) (Fin J) ℂ)
    ((blockWindow Q R J + Matrix.diagonal fun _ => c).map (↑) : Matrix (Fin J) (Fin J) ℂ)
    (coordSum J) fun x hx => by
      rw [hermQuad_add_diagonal, hermQuad_add_diagonal,
        hermQuad_neutralWindow_eq_blockWindow Q R hx]
  rwa [h0, zero_add] at h1

/-- **The neutral part of every window, shifted by its depth, has at most one negative
square.** -/
theorem hermNegIndex_neutralWindow_add_depth_le_one {Q R J : ℕ} (hR : 1 ≤ R) (hQ₀ : 1 ≤ Q)
    (hRJ : R + J ≤ Q * R) {c : ℝ} (hc : windowMarginDepth Q (R + J) ≤ c) :
    hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => c).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  refine hermNegIndex_neutralWindow_add_diagonal_le_one fun σ => ?_
  have h1 := neg_windowMarginDepth_le_packetForm_stepPacket hR hQ₀ hRJ σ
  rw [packetForm_stepPacket_eq_sum_blockMatrix hR Q J σ] at h1
  have h2 : windowMarginDepth Q (R + J) * ∑ j ∈ range J, σ j ^ 2 ≤
      c * ∑ j ∈ range J, σ j ^ 2 :=
    mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun j _ => sq_nonneg (σ j))
  linarith

/-! ### 7. The rate on the windows of ratio `3K + 1` -/

/-- The depth of the window `(R, (3K + 1)R]` in terms of `K` and `R`. -/
theorem windowMarginDepth_ratio_le {θ : ℝ} (hθ : zetaZeroWidth ≤ θ) {K R : ℕ} (hK : 1 ≤ K)
    (hR : 1 ≤ R) :
    windowMarginDepth (3 * K + 1) (R + 3 * K * R) ≤
      windowRateConst θ * (16 * (4 : ℝ) ^ θ *
        ((1 + Real.log K) ^ 2 * (K : ℝ) ^ θ * (1 + Real.log R))) := by
  have hθ0 : 0 ≤ θ := zetaZeroWidth_nonneg.trans hθ
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hK0 : (K : ℝ) ≠ 0 := by linarith
  have hR0 : (R : ℝ) ≠ 0 := by linarith
  have hk : 0 ≤ Real.log K := Real.log_nonneg hK'
  have hρ : 0 ≤ Real.log R := Real.log_nonneg hR'
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hQle : ((3 * K + 1 : ℕ) : ℝ) ≤ 4 * K := by
    push_cast
    linarith
  have hQ1 : (1 : ℝ) ≤ ((3 * K + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hNle : ((R + 3 * K * R : ℕ) : ℝ) ≤ 4 * K * R := by
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hK') (by linarith : (0 : ℝ) ≤ R)]
  have hN1 : (1 : ℝ) ≤ ((R + 3 * K * R : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * K) (by linarith : (0 : ℝ) ≤ R)]
  have hlq : Real.log ((3 * K + 1 : ℕ) : ℝ) ≤ 3 + Real.log K := by
    have h := Real.log_le_log (by linarith) hQle
    have hm : Real.log (4 * (K : ℝ)) = Real.log 4 + Real.log K :=
      Real.log_mul (by norm_num) hK0
    linarith
  have hln : Real.log ((R + 3 * K * R : ℕ) : ℝ) ≤ 3 + Real.log K + Real.log R := by
    have h := Real.log_le_log (by linarith) hNle
    have hm : Real.log (4 * (K : ℝ) * R) = Real.log 4 + Real.log K + Real.log R := by
      rw [Real.log_mul (mul_ne_zero (by norm_num) hK0) hR0, Real.log_mul (by norm_num) hK0]
    linarith
  have hmul : ((4 : ℝ) * K) ^ θ = (4 : ℝ) ^ θ * (K : ℝ) ^ θ :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hpow : ((3 * K + 1 : ℕ) : ℝ) ^ θ ≤ (4 : ℝ) ^ θ * (K : ℝ) ^ θ := by
    rw [← hmul]
    exact Real.rpow_le_rpow (by linarith) hQle hθ0
  have h4θ : 0 ≤ (4 : ℝ) ^ θ := Real.rpow_nonneg (by norm_num) θ
  have hKθ : 0 ≤ (K : ℝ) ^ θ := Real.rpow_nonneg (by linarith) θ
  have hlq0 : 0 ≤ Real.log ((3 * K + 1 : ℕ) : ℝ) := Real.log_nonneg hQ1
  have hln0 : 0 ≤ Real.log ((R + 3 * K * R : ℕ) : ℝ) := Real.log_nonneg hN1
  have hA1 : 1 + Real.log ((3 * K + 1 : ℕ) : ℝ) ≤ 4 * (1 + Real.log K) := by linarith
  have hA2 : 1 + Real.log ((R + 3 * K * R : ℕ) : ℝ) ≤
      4 * ((1 + Real.log K) * (1 + Real.log R)) := by
    nlinarith [mul_nonneg hk hρ]
  have hB := mul_le_mul (mul_le_mul hA1 hpow (Real.rpow_nonneg (by linarith) θ) (by linarith))
    hA2 (by linarith) (mul_nonneg (by linarith) (mul_nonneg h4θ hKθ))
  refine (windowMarginDepth_le hθ (Q := 3 * K + 1) (N := R + 3 * K * R) (by omega)
    (by omega)).trans (mul_le_mul_of_nonneg_left ?_ (windowRateConst_nonneg θ))
  calc (1 + Real.log ((3 * K + 1 : ℕ) : ℝ)) * ((3 * K + 1 : ℕ) : ℝ) ^ θ *
        (1 + Real.log ((R + 3 * K * R : ℕ) : ℝ))
      ≤ 4 * (1 + Real.log K) * ((4 : ℝ) ^ θ * (K : ℝ) ^ θ) *
          (4 * ((1 + Real.log K) * (1 + Real.log R))) := hB
    _ = 16 * (4 : ℝ) ^ θ * ((1 + Real.log K) ^ 2 * (K : ℝ) ^ θ * (1 + Real.log R)) := by ring

/-- **The margin of the window matrices sinks at the rate of the width.** For `θ` at least the
zero width there is `C` such that for every window `(R, (3K + 1)R]` the neutral part plus
`C (1 + log K)² K^θ (1 + log R)` has at most one negative square. -/
theorem exists_neutralWindow_marginDepth {θ : ℝ} (hθ : zetaZeroWidth ≤ θ) :
    ∃ C : ℝ, ∀ K R : ℕ, 1 ≤ K → 1 ≤ R →
      hermNegIndex ((neutralWindow (3 * K + 1) R (3 * K * R) + Matrix.diagonal fun _ =>
        C * ((1 + Real.log K) ^ 2 * (K : ℝ) ^ θ * (1 + Real.log R))).map (↑) :
          Matrix (Fin (3 * K * R)) (Fin (3 * K * R)) ℂ) ≤ 1 := by
  refine ⟨windowRateConst θ * (16 * (4 : ℝ) ^ θ), fun K R hK hR => ?_⟩
  exact hermNegIndex_neutralWindow_add_depth_le_one hR (by omega) (le_of_eq (by ring))
    ((windowMarginDepth_ratio_le hθ hK hR).trans (le_of_eq (by ring)))

/-- **With no hypothesis**: every neutral window of ratio `3K + 1` and block size `R` has at
most one eigenvalue below `−C (1 + log K)² K^{3/8} (1 + log R)`. -/
theorem exists_neutralWindow_marginDepth_three_eighths :
    ∃ C : ℝ, ∀ K R : ℕ, 1 ≤ K → 1 ≤ R →
      hermNegIndex ((neutralWindow (3 * K + 1) R (3 * K * R) + Matrix.diagonal fun _ =>
        C * ((1 + Real.log K) ^ 2 * (K : ℝ) ^ (3 / 8 : ℝ) * (1 + Real.log R))).map (↑) :
          Matrix (Fin (3 * K * R)) (Fin (3 * K * R)) ℂ) ≤ 1 :=
  exists_neutralWindow_marginDepth zetaZeroWidth_le_three_eighths

/-- **At block sizes polynomial in the ratio the margin exponent is at most the width**: for
`θ ≥ w`, `ε > 0` and `A` there is `C` such that on the windows with `R ≤ K^A` the neutral part
plus `C K^{θ+ε}` has at most one negative square. -/
theorem exists_neutralWindow_marginRate_of_blockSize_le_pow {θ ε : ℝ} (hθ : zetaZeroWidth ≤ θ)
    (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, ∀ K R : ℕ, 1 ≤ K → 1 ≤ R → R ≤ K ^ A →
      hermNegIndex ((neutralWindow (3 * K + 1) R (3 * K * R) + Matrix.diagonal fun _ =>
        C * (K : ℝ) ^ (θ + ε)).map (↑) :
          Matrix (Fin (3 * K * R)) (Fin (3 * K * R)) ℂ) ≤ 1 := by
  refine ⟨windowRateConst θ * (16 * (4 : ℝ) ^ θ) * ((1 + A) * (1 + 3 / ε) ^ 3),
    fun K R hK hR hRA => ?_⟩
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hk : 0 ≤ Real.log K := Real.log_nonneg hK'
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hKθ : 0 ≤ (K : ℝ) ^ θ := Real.rpow_nonneg hK0.le θ
  -- the block size
  have hlogR : Real.log R ≤ A * Real.log K := by
    have h := Real.log_le_log (by linarith) (show (R : ℝ) ≤ (K : ℝ) ^ A by exact_mod_cast hRA)
    rwa [Real.log_pow] at h
  have h1ρ : 1 + Real.log R ≤ (1 + A) * (1 + Real.log K) := by
    nlinarith [mul_nonneg hA0 hk]
  -- the logarithm against a power
  have hδ : 0 < ε / 3 := by positivity
  have hKδ : 1 ≤ (K : ℝ) ^ (ε / 3) := Real.one_le_rpow hK' hδ.le
  have hlogK : 1 + Real.log K ≤ (1 + 3 / ε) * (K : ℝ) ^ (ε / 3) := by
    have h := Real.log_le_rpow_div hK0.le hδ
    rw [div_div_eq_mul_div] at h
    have e : (K : ℝ) ^ (ε / 3) * 3 / ε = 3 / ε * (K : ℝ) ^ (ε / 3) := by ring
    rw [e] at h
    linarith
  have hcube : (1 + Real.log K) ^ 3 ≤ (1 + 3 / ε) ^ 3 * (K : ℝ) ^ ε := by
    have h := pow_le_pow_left₀ (by linarith) hlogK 3
    rw [mul_pow, ← Real.rpow_natCast ((K : ℝ) ^ (ε / 3)) 3, ← Real.rpow_mul hK0.le] at h
    rwa [show ε / 3 * ((3 : ℕ) : ℝ) = ε by push_cast; ring] at h
  have hmain : (1 + Real.log K) ^ 2 * (K : ℝ) ^ θ * (1 + Real.log R) ≤
      (1 + A) * (1 + 3 / ε) ^ 3 * (K : ℝ) ^ (θ + ε) := by
    rw [Real.rpow_add hK0]
    calc (1 + Real.log K) ^ 2 * (K : ℝ) ^ θ * (1 + Real.log R)
        ≤ (1 + Real.log K) ^ 2 * (K : ℝ) ^ θ * ((1 + A) * (1 + Real.log K)) :=
          mul_le_mul_of_nonneg_left h1ρ (mul_nonneg (sq_nonneg _) hKθ)
      _ = (1 + A) * (K : ℝ) ^ θ * (1 + Real.log K) ^ 3 := by ring
      _ ≤ (1 + A) * (K : ℝ) ^ θ * ((1 + 3 / ε) ^ 3 * (K : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hcube (mul_nonneg (by linarith) hKθ)
      _ = (1 + A) * (1 + 3 / ε) ^ 3 * ((K : ℝ) ^ θ * (K : ℝ) ^ ε) := by ring
  have hC : 0 ≤ windowRateConst θ * (16 * (4 : ℝ) ^ θ) :=
    mul_nonneg (windowRateConst_nonneg θ)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) θ))
  exact hermNegIndex_neutralWindow_add_depth_le_one hR (by omega) (le_of_eq (by ring))
    ((windowMarginDepth_ratio_le hθ hK hR).trans ((le_of_eq (by ring)).trans
      ((mul_le_mul_of_nonneg_left hmain hC).trans (le_of_eq (by ring)))))

/-- With no hypothesis: at block sizes polynomial in the ratio the shift `C K^{3/8+ε}`
suffices. -/
theorem exists_neutralWindow_marginRate_three_eighths_of_blockSize_le_pow {ε : ℝ} (hε : 0 < ε)
    (A : ℕ) :
    ∃ C : ℝ, ∀ K R : ℕ, 1 ≤ K → 1 ≤ R → R ≤ K ^ A →
      hermNegIndex ((neutralWindow (3 * K + 1) R (3 * K * R) + Matrix.diagonal fun _ =>
        C * (K : ℝ) ^ ((3 / 8 : ℝ) + ε)).map (↑) :
          Matrix (Fin (3 * K * R)) (Fin (3 * K * R)) ℂ) ≤ 1 :=
  exists_neutralWindow_marginRate_of_blockSize_le_pow zetaZeroWidth_le_three_eighths hε A

#print axioms neg_packetLogEnergy_le_packetForm
#print axioms exists_neutralWindow_marginDepth_three_eighths
#print axioms exists_neutralWindow_marginRate_three_eighths_of_blockSize_le_pow

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
