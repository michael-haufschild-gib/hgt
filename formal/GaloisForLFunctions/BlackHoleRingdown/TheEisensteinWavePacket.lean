import GaloisForLFunctions.BlackHoleRingdown.TheNormalizedEisensteinFunction
import GaloisForLFunctions.BlackHoleRingdown.TheExactLiftOfTheModularWave

/-!
# The Eisenstein wave packet

For a Gaussian amplitude `a(ξ) = exp(-ε(ξ-ξ₀)²)` the packet

`𝓕(τ, z) = ∫ a(ξ) E(z, ½+iξ) e^{iξτ} dξ`

is an exact solution of the modular wave equation `𝓕_ττ = Y²(𝓕_xx + 𝓕_YY) + 𝓕/4`, invariant under
`SL₂(ℤ)`, with no restriction on `ε > 0`. Its horocycle mean is

`∫₀¹ 𝓕 dx = Y^{½} (g(τ + log Y) + 𝒮(τ - log Y))`,

where `g` is the incoming pulse and `𝒮(T) = ∫ a(ξ) φ(½+iξ) e^{iξT} dξ` is the reflected signal.

The exact lift turns the packet into exact solutions of the conformally coupled wave equation on the
massless topological AdS black hole with modular horizon, with Neumann or Dirichlet data at the AdS
boundary.
-/

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### The Gaussian amplitude -/

/-- The amplitude `a(w) = exp(-ε(w-ξ₀)²)`. -/
def gaussianAmplitude (ε ξ₀ : ℝ) (w : ℂ) : ℂ := Complex.exp (-(ε : ℂ) * (w - (ξ₀ : ℂ)) ^ 2)

theorem continuous_gaussianAmplitude_real (ε ξ₀ : ℝ) :
    Continuous fun ξ : ℝ => gaussianAmplitude ε ξ₀ (ξ : ℂ) := by
  unfold gaussianAmplitude
  fun_prop

theorem norm_gaussianAmplitude_real_le {ε : ℝ} (hε : 0 < ε) (ξ₀ ξ : ℝ) :
    ‖gaussianAmplitude ε ξ₀ (ξ : ℂ)‖ ≤ Real.exp (ε * ξ₀ ^ 2) * Real.exp (-(ε / 2) * ξ ^ 2) := by
  rw [gaussianAmplitude, Complex.norm_exp, ← Real.exp_add]
  refine Real.exp_le_exp.mpr (le_of_eq_of_le ?_ ?_)
  · exact -ε * (ξ - ξ₀) ^ 2
  · have : (-(ε : ℂ) * ((ξ : ℂ) - (ξ₀ : ℂ)) ^ 2) = ((-ε * (ξ - ξ₀) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.ofReal_re]
  · nlinarith [mul_nonneg hε.le (sq_nonneg (ξ - 2 * ξ₀))]

/-! ### The packet transform -/

/-- The transform `J ↦ ∫ a(ξ) J(ξ) e^{iξτ} dξ`. -/
def packet (ε ξ₀ : ℝ) (J : ℝ → ℂ) (τ : ℝ) : ℂ :=
  ∫ ξ : ℝ, gaussianAmplitude ε ξ₀ (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (τ : ℂ))

/-- The class of symbols the packet transform accepts. -/
structure PacketSymbol (ε : ℝ) (J : ℝ → ℂ) : Prop where
  measurable : Measurable J
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖J ξ‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2)

theorem norm_exp_I_mul (ξ τ : ℝ) : ‖Complex.exp (I * (ξ : ℂ) * (τ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem measurable_packet_integrand (ε ξ₀ : ℝ) {J : ℝ → ℂ} (hJ : Measurable J) (τ : ℝ) :
    Measurable fun ξ : ℝ =>
      gaussianAmplitude ε ξ₀ (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
  have h : Continuous fun ξ : ℝ => Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by fun_prop
  exact ((continuous_gaussianAmplitude_real ε ξ₀).measurable.mul hJ).mul h.measurable

/-- The dominating Gaussian of a symbol. -/
theorem norm_packet_integrand_le {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {J : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ ξ : ℝ, ‖J ξ‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2)) (τ ξ : ℝ) :
    ‖gaussianAmplitude ε ξ₀ (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (τ : ℂ))‖ ≤
      Real.exp (ε * ξ₀ ^ 2) * C * Real.exp (-(ε / 4) * ξ ^ 2) := by
  rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
  have hprod : Real.exp (-(ε / 2) * ξ ^ 2) * Real.exp (ε / 4 * ξ ^ 2) = Real.exp (-(ε / 4) * ξ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc ‖gaussianAmplitude ε ξ₀ (ξ : ℂ)‖ * ‖J ξ‖
      ≤ (Real.exp (ε * ξ₀ ^ 2) * Real.exp (-(ε / 2) * ξ ^ 2)) * (C * Real.exp (ε / 4 * ξ ^ 2)) :=
        mul_le_mul (norm_gaussianAmplitude_real_le hε ξ₀ ξ) (hJ ξ) (norm_nonneg _) (by positivity)
    _ = Real.exp (ε * ξ₀ ^ 2) * C * (Real.exp (-(ε / 2) * ξ ^ 2) * Real.exp (ε / 4 * ξ ^ 2)) := by ring
    _ = _ := by rw [hprod]

theorem integrable_gaussian_quarter {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    Integrable fun ξ : ℝ => K * Real.exp (-(ε / 4) * ξ ^ 2) :=
  (integrable_exp_neg_mul_sq (by positivity : 0 < ε / 4)).const_mul K

theorem PacketSymbol.integrable {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {J : ℝ → ℂ} (hJ : PacketSymbol ε J)
    (τ : ℝ) :
    Integrable fun ξ : ℝ =>
      gaussianAmplitude ε ξ₀ (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
  obtain ⟨C, hC, hb⟩ := hJ.bound
  refine (integrable_gaussian_quarter hε (Real.exp (ε * ξ₀ ^ 2) * C)).mono'
    (measurable_packet_integrand ε ξ₀ hJ.measurable τ).aestronglyMeasurable
    (Eventually.of_forall fun ξ => norm_packet_integrand_le hε ξ₀ hC hb τ ξ)

theorem packet_add {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {J₁ J₂ : ℝ → ℂ} (h₁ : PacketSymbol ε J₁)
    (h₂ : PacketSymbol ε J₂) (τ : ℝ) :
    packet ε ξ₀ (fun ξ => J₁ ξ + J₂ ξ) τ = packet ε ξ₀ J₁ τ + packet ε ξ₀ J₂ τ := by
  simp only [packet]
  rw [← integral_add (h₁.integrable hε ξ₀ τ) (h₂.integrable hε ξ₀ τ)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  ring

theorem packet_const_mul (ε ξ₀ : ℝ) (c : ℂ) (J : ℝ → ℂ) (τ : ℝ) :
    packet ε ξ₀ (fun ξ => c * J ξ) τ = c * packet ε ξ₀ J τ := by
  simp only [packet]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  ring

/-- **Time derivative of a packet.**  Differentiation multiplies the symbol by `iξ`. -/
theorem hasDerivAt_packet_time {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {J : ℝ → ℂ} (hJ : PacketSymbol ε J)
    (τ : ℝ) :
    HasDerivAt (packet ε ξ₀ J) (packet ε ξ₀ (fun ξ => J ξ * (I * (ξ : ℂ))) τ) τ := by
  obtain ⟨C, hC, hb⟩ := hJ.bound
  obtain ⟨C₁, hC₁, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian 1 (b := 0) (c := ε / 8)
    (by positivity)
  set G : ℝ → ℝ := fun ξ => Real.exp (ε * ξ₀ ^ 2) * C * C₁ * Real.exp (-(ε / 8) * ξ ^ 2) with hG
  have hGint : Integrable G := (integrable_exp_neg_mul_sq (by positivity : 0 < ε / 8)).const_mul _
  have hline : Continuous fun ξ : ℝ => I * (ξ : ℂ) := by fun_prop
  have hderivMeas : Measurable fun ξ : ℝ => J ξ * (I * (ξ : ℂ)) :=
    hJ.measurable.mul hline.measurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ξ => gaussianAmplitude ε ξ₀ (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (s : ℂ)))
    (F' := fun s ξ => gaussianAmplitude ε ξ₀ (ξ : ℂ) * (J ξ * (I * (ξ : ℂ))) *
      Complex.exp (I * (ξ : ℂ) * (s : ℂ)))
    (x₀ := τ) (s := Set.univ) (bound := G) univ_mem
    (Eventually.of_forall fun s => (measurable_packet_integrand ε ξ₀ hJ.measurable s).aestronglyMeasurable)
    (hJ.integrable hε ξ₀ τ)
    (measurable_packet_integrand ε ξ₀ hderivMeas τ).aestronglyMeasurable
    (Eventually.of_forall fun ξ s _ => ?_) hGint
    (Eventually.of_forall fun ξ s _ => ?_)).2
  · have h1 : ‖J ξ * (I * (ξ : ℂ))‖ ≤ C * C₁ * Real.exp (ε / 4 * ξ ^ 2 - ε / 8 * ξ ^ 2 + ε / 8 * ξ ^ 2) := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hp := hcmp |ξ| (abs_nonneg ξ)
      simp only [zero_mul, Real.exp_zero, mul_one, sq_abs, pow_one] at hp
      have hexp : Real.exp (ε / 4 * ξ ^ 2 - ε / 8 * ξ ^ 2 + ε / 8 * ξ ^ 2) =
          Real.exp (ε / 4 * ξ ^ 2) * Real.exp (ε / 8 * ξ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      calc ‖J ξ‖ * |ξ| ≤ (C * Real.exp (ε / 4 * ξ ^ 2)) * (C₁ * Real.exp (ε / 8 * ξ ^ 2)) :=
            mul_le_mul (hb ξ) (by linarith) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
    have hprod : Real.exp (-(ε / 2) * ξ ^ 2) * Real.exp (ε / 4 * ξ ^ 2 - ε / 8 * ξ ^ 2 + ε / 8 * ξ ^ 2) =
        Real.exp (-(ε / 8) * ξ ^ 2) * Real.exp (-(ε / 8) * ξ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hE1 : Real.exp (-(ε / 8) * ξ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg ξ]
    rw [hG]
    calc ‖gaussianAmplitude ε ξ₀ (ξ : ℂ)‖ * ‖J ξ * (I * (ξ : ℂ))‖
        ≤ (Real.exp (ε * ξ₀ ^ 2) * Real.exp (-(ε / 2) * ξ ^ 2)) *
            (C * C₁ * Real.exp (ε / 4 * ξ ^ 2 - ε / 8 * ξ ^ 2 + ε / 8 * ξ ^ 2)) :=
          mul_le_mul (norm_gaussianAmplitude_real_le hε ξ₀ ξ) h1 (norm_nonneg _) (by positivity)
      _ = Real.exp (ε * ξ₀ ^ 2) * C * C₁ * (Real.exp (-(ε / 2) * ξ ^ 2) *
            Real.exp (ε / 4 * ξ ^ 2 - ε / 8 * ξ ^ 2 + ε / 8 * ξ ^ 2)) := by ring
      _ = Real.exp (ε * ξ₀ ^ 2) * C * C₁ * (Real.exp (-(ε / 8) * ξ ^ 2) *
            Real.exp (-(ε / 8) * ξ ^ 2)) := by rw [hprod]
      _ ≤ Real.exp (ε * ξ₀ ^ 2) * C * C₁ * (Real.exp (-(ε / 8) * ξ ^ 2) * 1) := by
          gcongr
      _ = _ := by ring
  · have hs : HasDerivAt (fun r : ℝ => Complex.exp (I * (ξ : ℂ) * (r : ℂ)))
        (Complex.exp (I * (ξ : ℂ) * (s : ℂ)) * (I * (ξ : ℂ))) s := by
      have h := ((hasDerivAt_id s).ofReal_comp.const_mul (I * (ξ : ℂ))).cexp
      simpa using h
    have h := hs.const_mul (gaussianAmplitude ε ξ₀ (ξ : ℂ) * J ξ)
    refine h.congr_deriv ?_
    ring

/-- **Parameter derivative of a packet.** -/
theorem hasDerivAt_packet_param {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {J K : ℝ → ℝ → ℂ} {v₀ : ℝ}
    {s : Set ℝ} (hs : s ∈ 𝓝 v₀) (hJmeas : ∀ᶠ v in 𝓝 v₀, Measurable (J v))
    (hJ₀ : PacketSymbol ε (J v₀)) (hKmeas : Measurable (K v₀)) {C : ℝ} (hC : 0 ≤ C)
    (hKb : ∀ v ∈ s, ∀ ξ : ℝ, ‖K v ξ‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2))
    (hdiff : ∀ v ∈ s, ∀ ξ : ℝ, HasDerivAt (fun w => J w ξ) (K v ξ) v) (τ : ℝ) :
    HasDerivAt (fun v => packet ε ξ₀ (J v) τ) (packet ε ξ₀ (K v₀) τ) v₀ := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v ξ => gaussianAmplitude ε ξ₀ (ξ : ℂ) * J v ξ * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)))
    (F' := fun v ξ => gaussianAmplitude ε ξ₀ (ξ : ℂ) * K v ξ * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)))
    (x₀ := v₀) (s := s) (bound := fun ξ => Real.exp (ε * ξ₀ ^ 2) * C * Real.exp (-(ε / 4) * ξ ^ 2)) hs
    (hJmeas.mono fun v hv => (measurable_packet_integrand ε ξ₀ hv τ).aestronglyMeasurable)
    (hJ₀.integrable hε ξ₀ τ)
    (measurable_packet_integrand ε ξ₀ hKmeas τ).aestronglyMeasurable
    (Eventually.of_forall fun ξ v hv => ?_) (integrable_gaussian_quarter hε _)
    (Eventually.of_forall fun ξ v hv => ?_)).2
  · exact norm_packet_integrand_le hε ξ₀ hC (fun η => hKb v hv η) τ ξ
  · exact ((hdiff v hv ξ).const_mul _).mul_const _

/-! ### The symbols of the Eisenstein function -/

section Symbols

variable {ε : ℝ}

/-- Every jet of `E` is a packet symbol. -/
theorem exists_jets_le_quarter (hε : 0 < ε) {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ x Y : ℝ), Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖normalizedEisenstein ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2) ∧
      ‖eisensteinX ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2) ∧
      ‖eisensteinXX ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2) ∧
      ‖eisensteinY ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2) ∧
      ‖eisensteinYY ((ξ : ℂ) * I) x Y‖ ≤ C * Real.exp (ε / 4 * ξ ^ 2) :=
  exists_eisenstein_jets_le_gaussian hY₀ (by positivity)

theorem packetSymbol_eisenstein (hε : 0 < ε) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    PacketSymbol ε fun ξ => normalizedEisenstein ((ξ : ℂ) * I) x Y := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  exact ⟨measurable_normalizedEisenstein_line hY x, C, hC, fun ξ =>
    (h ξ x Y (mem_window_self hY)).1⟩

theorem packetSymbol_eisensteinX (hε : 0 < ε) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    PacketSymbol ε fun ξ => eisensteinX ((ξ : ℂ) * I) x Y := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  exact ⟨measurable_eisensteinX_line hY x, C, hC, fun ξ =>
    (h ξ x Y (mem_window_self hY)).2.1⟩

theorem packetSymbol_eisensteinXX (hε : 0 < ε) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    PacketSymbol ε fun ξ => eisensteinXX ((ξ : ℂ) * I) x Y := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  exact ⟨measurable_eisensteinXX_line hY x, C, hC, fun ξ =>
    (h ξ x Y (mem_window_self hY)).2.2.1⟩

theorem packetSymbol_eisensteinY (hε : 0 < ε) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    PacketSymbol ε fun ξ => eisensteinY ((ξ : ℂ) * I) x Y := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  exact ⟨measurable_eisensteinY_line hY x, C, hC, fun ξ =>
    (h ξ x Y (mem_window_self hY)).2.2.2.1⟩

theorem packetSymbol_eisensteinYY (hε : 0 < ε) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    PacketSymbol ε fun ξ => eisensteinYY ((ξ : ℂ) * I) x Y := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  exact ⟨measurable_eisensteinYY_line hY x, C, hC, fun ξ =>
    (h ξ x Y (mem_window_self hY)).2.2.2.2⟩

/-- Multiplying a symbol of rate `ε/8` by `iξ`, or by `(iξ)²`, stays a packet symbol. -/
theorem packetSymbol_eisenstein_mul (hε : 0 < ε) (x : ℝ) {Y : ℝ} (hY : 0 < Y) (k : ℕ) :
    PacketSymbol ε fun ξ => normalizedEisenstein ((ξ : ℂ) * I) x Y * (I * (ξ : ℂ)) ^ k := by
  obtain ⟨C, hC, h⟩ := exists_eisenstein_jets_le_gaussian hY (c := ε / 8) (by positivity)
  obtain ⟨C₁, hC₁, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian k (b := 0) (c := ε / 8)
    (by positivity)
  have hline : Continuous fun ξ : ℝ => (I * (ξ : ℂ)) ^ k := by fun_prop
  refine ⟨(measurable_normalizedEisenstein_line hY x).mul hline.measurable, C * C₁, by positivity,
    fun ξ => ?_⟩
  have hp := hcmp |ξ| (abs_nonneg ξ)
  simp only [zero_mul, Real.exp_zero, mul_one, sq_abs] at hp
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hpow : |ξ| ^ k ≤ (1 + |ξ|) ^ k :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) k
  have hE := (h ξ x Y (mem_window_self hY)).1
  have hprod : Real.exp (ε / 8 * ξ ^ 2) * Real.exp (ε / 8 * ξ ^ 2) = Real.exp (ε / 4 * ξ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc ‖normalizedEisenstein ((ξ : ℂ) * I) x Y‖ * |ξ| ^ k
      ≤ (C * Real.exp (ε / 8 * ξ ^ 2)) * (C₁ * Real.exp (ε / 8 * ξ ^ 2)) :=
        mul_le_mul hE (hpow.trans hp) (by positivity) (by positivity)
    _ = C * C₁ * Real.exp (ε / 4 * ξ ^ 2) := by
        rw [← hprod]
        ring

end Symbols

/-! ### The wave packet -/

/-- The Eisenstein wave packet `𝓕(τ, x + iY)`. -/
def wavePacket (ε ξ₀ τ x Y : ℝ) : ℂ :=
  packet ε ξ₀ (fun ξ => normalizedEisenstein ((ξ : ℂ) * I) x Y) τ

/-- The two time jets of the packet. -/
def wavePacketT (ε ξ₀ τ x Y : ℝ) : ℂ :=
  packet ε ξ₀ (fun ξ => normalizedEisenstein ((ξ : ℂ) * I) x Y * (I * (ξ : ℂ)) ^ 1) τ
def wavePacketTT (ε ξ₀ τ x Y : ℝ) : ℂ :=
  packet ε ξ₀ (fun ξ => normalizedEisenstein ((ξ : ℂ) * I) x Y * (I * (ξ : ℂ)) ^ 2) τ

/-- The horizontal and vertical jets of the packet. -/
def wavePacketX (ε ξ₀ τ x Y : ℝ) : ℂ := packet ε ξ₀ (fun ξ => eisensteinX ((ξ : ℂ) * I) x Y) τ
def wavePacketXX (ε ξ₀ τ x Y : ℝ) : ℂ := packet ε ξ₀ (fun ξ => eisensteinXX ((ξ : ℂ) * I) x Y) τ
def wavePacketY (ε ξ₀ τ x Y : ℝ) : ℂ := packet ε ξ₀ (fun ξ => eisensteinY ((ξ : ℂ) * I) x Y) τ
def wavePacketYY (ε ξ₀ τ x Y : ℝ) : ℂ := packet ε ξ₀ (fun ξ => eisensteinYY ((ξ : ℂ) * I) x Y) τ

section Field

variable {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) (τ x : ℝ) {Y : ℝ} (hY : 0 < Y)

include hε hY

theorem hasDerivAt_wavePacket_time :
    HasDerivAt (fun s => wavePacket ε ξ₀ s x Y) (wavePacketT ε ξ₀ τ x Y) τ := by
  have h := hasDerivAt_packet_time hε ξ₀ (packetSymbol_eisenstein hε x hY) τ
  refine h.congr_deriv ?_
  simp only [wavePacketT, pow_one]

theorem hasDerivAt_wavePacketT_time :
    HasDerivAt (fun s => wavePacketT ε ξ₀ s x Y) (wavePacketTT ε ξ₀ τ x Y) τ := by
  have h := hasDerivAt_packet_time hε ξ₀ (packetSymbol_eisenstein_mul hε x hY 1) τ
  refine h.congr_deriv ?_
  simp only [wavePacketTT]
  congr 1
  funext ξ
  ring

theorem hasDerivAt_wavePacket_x :
    HasDerivAt (fun q => wavePacket ε ξ₀ τ q Y) (wavePacketX ε ξ₀ τ x Y) x := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  exact hasDerivAt_packet_param hε ξ₀ (J := fun q ξ => normalizedEisenstein ((ξ : ℂ) * I) q Y)
    (K := fun q ξ => eisensteinX ((ξ : ℂ) * I) q Y) (s := Set.univ) univ_mem
    (Eventually.of_forall fun q => measurable_normalizedEisenstein_line hY q)
    (packetSymbol_eisenstein hε x hY) (measurable_eisensteinX_line hY x) hC
    (fun q _ ξ => (h ξ q Y (mem_window_self hY)).2.1)
    (fun q _ ξ => hasDerivAt_eisenstein_x _ q hY) τ

theorem hasDerivAt_wavePacketX_x :
    HasDerivAt (fun q => wavePacketX ε ξ₀ τ q Y) (wavePacketXX ε ξ₀ τ x Y) x := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  exact hasDerivAt_packet_param hε ξ₀ (J := fun q ξ => eisensteinX ((ξ : ℂ) * I) q Y)
    (K := fun q ξ => eisensteinXX ((ξ : ℂ) * I) q Y) (s := Set.univ) univ_mem
    (Eventually.of_forall fun q => measurable_eisensteinX_line hY q)
    (packetSymbol_eisensteinX hε x hY) (measurable_eisensteinXX_line hY x) hC
    (fun q _ ξ => (h ξ q Y (mem_window_self hY)).2.2.1)
    (fun q _ ξ => hasDerivAt_eisensteinX_x _ q hY) τ

theorem hasDerivAt_wavePacket_y :
    HasDerivAt (fun q => wavePacket ε ξ₀ τ x q) (wavePacketY ε ξ₀ τ x Y) Y := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  have hmem : Ioo (Y / 2) (2 * Y) ∈ 𝓝 Y := Ioo_mem_nhds (by linarith) (by linarith)
  exact hasDerivAt_packet_param hε ξ₀ (J := fun q ξ => normalizedEisenstein ((ξ : ℂ) * I) x q)
    (K := fun q ξ => eisensteinY ((ξ : ℂ) * I) x q) hmem
    ((lt_mem_nhds hY).mono fun q hq => measurable_normalizedEisenstein_line hq x)
    (packetSymbol_eisenstein hε x hY) (measurable_eisensteinY_line hY x) hC
    (fun q hq ξ => (h ξ x q (Ioo_subset_Icc_self hq)).2.2.2.1)
    (fun q hq ξ => hasDerivAt_eisenstein_y _ x (by linarith [hq.1])) τ

theorem hasDerivAt_wavePacketY_y :
    HasDerivAt (fun q => wavePacketY ε ξ₀ τ x q) (wavePacketYY ε ξ₀ τ x Y) Y := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  have hmem : Ioo (Y / 2) (2 * Y) ∈ 𝓝 Y := Ioo_mem_nhds (by linarith) (by linarith)
  exact hasDerivAt_packet_param hε ξ₀ (J := fun q ξ => eisensteinY ((ξ : ℂ) * I) x q)
    (K := fun q ξ => eisensteinYY ((ξ : ℂ) * I) x q) hmem
    ((lt_mem_nhds hY).mono fun q hq => measurable_eisensteinY_line hq x)
    (packetSymbol_eisensteinY hε x hY) (measurable_eisensteinYY_line hY x) hC
    (fun q hq ξ => (h ξ x q (Ioo_subset_Icc_self hq)).2.2.2.2)
    (fun q hq ξ => hasDerivAt_eisensteinY_y _ x (by linarith [hq.1])) τ

/-- **The modular wave equation.**  `𝓕_ττ = Y²(𝓕_xx + 𝓕_YY) + 𝓕/4`. -/
theorem wavePacket_wave :
    wavePacketTT ε ξ₀ τ x Y =
      (Y : ℂ) ^ 2 * (wavePacketXX ε ξ₀ τ x Y + wavePacketYY ε ξ₀ τ x Y) + wavePacket ε ξ₀ τ x Y / 4 := by
  have hadd := packet_add hε ξ₀ (packetSymbol_eisensteinXX hε x hY)
    (packetSymbol_eisensteinYY hε x hY) τ
  have hmul := packet_const_mul ε ξ₀ ((Y : ℂ) ^ 2)
    (fun ξ => eisensteinXX ((ξ : ℂ) * I) x Y + eisensteinYY ((ξ : ℂ) * I) x Y) τ
  have hpoint : (fun ξ : ℝ => (Y : ℂ) ^ 2 *
      (eisensteinXX ((ξ : ℂ) * I) x Y + eisensteinYY ((ξ : ℂ) * I) x Y)) =
      fun ξ : ℝ => normalizedEisenstein ((ξ : ℂ) * I) x Y * (I * (ξ : ℂ)) ^ 2 +
        (-(1 / 4) : ℂ) * normalizedEisenstein ((ξ : ℂ) * I) x Y := by
    funext ξ
    rw [eisenstein_eigen _ x hY]
    ring
  rw [hpoint] at hmul
  have hsplit := packet_add hε ξ₀ (packetSymbol_eisenstein_mul hε x hY 2)
    (J₂ := fun ξ => (-(1 / 4) : ℂ) * normalizedEisenstein ((ξ : ℂ) * I) x Y)
    (by
      obtain ⟨C, hC, hb⟩ := (packetSymbol_eisenstein hε x hY).bound
      refine ⟨(packetSymbol_eisenstein hε x hY).measurable.const_mul _, C / 4, by positivity,
        fun ξ => ?_⟩
      rw [norm_mul]
      have hq : ‖(-(1 / 4) : ℂ)‖ = 1 / 4 := by simp
      rw [hq]
      have := hb ξ
      nlinarith) τ
  have hquarter := packet_const_mul ε ξ₀ (-(1 / 4) : ℂ)
    (fun ξ => normalizedEisenstein ((ξ : ℂ) * I) x Y) τ
  simp only [wavePacketTT, wavePacketXX, wavePacketYY, wavePacket]
  rw [← hadd, ← hmul, hsplit, hquarter]
  ring

/-- **Modular invariance of the packet.** -/
theorem wavePacket_smul (γ : SL(2, ℤ)) (z : ℍ) :
    wavePacket ε ξ₀ τ (γ • z : ℍ).re (γ • z : ℍ).im = wavePacket ε ξ₀ τ z.re z.im := by
  have hae : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by
    have : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr (by simp)
    exact this
  simp only [wavePacket, packet]
  refine integral_congr_ae (hae.mono fun ξ hξ => ?_)
  simp only
  rw [normalizedEisenstein_smul hξ γ z]

end Field

/-! ### The horocycle mean -/

/-- The incoming pulse `g(T) = ∫ a(ξ) e^{iξT} dξ`. -/
def incomingPulse (ε ξ₀ T : ℝ) : ℂ := packet ε ξ₀ (fun _ => 1) T

/-- The reflected signal `𝒮(T) = ∫ a(ξ) φ(½+iξ) e^{iξT} dξ`. -/
def reflectedSignal (ε ξ₀ T : ℝ) : ℂ := packet ε ξ₀ (fun ξ => scatteringPhase ((ξ : ℂ) * I)) T

theorem measurable_tail_pair {Y : ℝ} (hY : 0 < Y) (negative : Bool) :
    Measurable fun p : ℝ × ℝ => weightedTail ((p.1 : ℂ) * I) negative p.2 Y := by
  refine Measurable.tsum fun N => ?_
  have hline : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ) * I) := by fun_prop
  have h1 : Continuous fun p : ℝ × ℝ => modeCoefficient ((p.1 : ℂ) * I) N :=
    (continuous_modeCoefficient N).comp hline
  have hphase : Continuous fun x : ℝ => d4BMCompletedEisensteinFourierPhase negative N x :=
    continuous_fourierPhase negative N
  have hmode : Continuous fun p : ℝ × ℝ =>
      d4BMSignedWhittakerMode negative N ((p.1 : ℂ) * I) p.2 Y := by
    unfold d4BMSignedWhittakerMode d4BMWhittakerP0
    exact (hphase.comp continuous_snd).mul
      (continuous_const.mul ((continuous_bessel_order hY N).comp hline))
  exact (h1.mul hmode).measurable

theorem measurable_normalizedEisenstein_pair {Y : ℝ} (hY : 0 < Y) :
    Measurable fun p : ℝ × ℝ => normalizedEisenstein ((p.1 : ℂ) * I) p.2 Y := by
  have h1 : Continuous fun p : ℝ × ℝ => (Y : ℂ) ^ (1 / 2 + ((p.1 : ℂ) * I)) := by
    refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
    exact_mod_cast hY.ne'
  have h2 : Continuous fun p : ℝ × ℝ => (Y : ℂ) ^ (1 / 2 - ((p.1 : ℂ) * I)) := by
    refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
    exact_mod_cast hY.ne'
  unfold normalizedEisenstein
  exact (h1.measurable.add
    ((continuous_scatteringPhase_line.comp continuous_fst).mul h2).measurable).add
    ((continuous_tailWeight_line.comp continuous_fst).measurable.mul
      ((measurable_tail_pair hY false).add (measurable_tail_pair hY true)))

/-- **The horocycle mean of the packet** is the incoming pulse plus the reflected signal. -/
theorem setIntegral_wavePacket {ε : ℝ} (hε : 0 < ε) (ξ₀ τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioc (0 : ℝ) 1, wavePacket ε ξ₀ τ x Y =
      ((Real.sqrt Y : ℝ) : ℂ) * (incomingPulse ε ξ₀ (τ + Real.log Y) +
        reflectedSignal ε ξ₀ (τ - Real.log Y)) := by
  obtain ⟨C, hC, h⟩ := exists_jets_le_quarter hε hY
  set F : ℝ → ℝ → ℂ := fun x ξ => gaussianAmplitude ε ξ₀ (ξ : ℂ) *
    normalizedEisenstein ((ξ : ℂ) * I) x Y * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) with hF
  have hmeasF : Measurable (Function.uncurry F) := by
    have hg : Continuous fun p : ℝ × ℝ => gaussianAmplitude ε ξ₀ ((p.2 : ℝ) : ℂ) :=
      (continuous_gaussianAmplitude_real ε ξ₀).comp continuous_snd
    have he : Continuous fun p : ℝ × ℝ => Complex.exp (I * ((p.2 : ℝ) : ℂ) * (τ : ℂ)) := by
      fun_prop
    have hE := (measurable_normalizedEisenstein_pair hY).comp (measurable_swap (α := ℝ) (β := ℝ))
    exact (hg.measurable.mul hE).mul he.measurable
  have hfin : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simpa using hfin.lt_top⟩
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    have hG : Integrable (fun p : ℝ × ℝ => Real.exp (ε * ξ₀ ^ 2) * C * Real.exp (-(ε / 4) * p.2 ^ 2))
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) :=
      (integrable_gaussian_quarter hε (Real.exp (ε * ξ₀ ^ 2) * C)).comp_snd _
    refine hG.mono' hmeasF.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    exact norm_packet_integrand_le hε ξ₀ hC (fun ξ => (h ξ p.1 Y (mem_window_self hY)).1) τ p.2
  have hswap := integral_integral_swap (f := F) hint
  simp only [wavePacket, packet]
  rw [hswap]
  have hinner : ∀ ξ : ℝ, (∫ x in Ioc (0 : ℝ) 1, F x ξ) =
      gaussianAmplitude ε ξ₀ (ξ : ℂ) * ((Y : ℂ) ^ (1 / 2 + (ξ : ℂ) * I) +
        scatteringPhase ((ξ : ℂ) * I) * (Y : ℂ) ^ (1 / 2 - (ξ : ℂ) * I)) *
          Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
    intro ξ
    simp only [hF]
    rw [integral_mul_const, integral_const_mul, setIntegral_normalizedEisenstein _ hY]
  simp_rw [hinner]
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpower : ∀ w : ℂ, (Y : ℂ) ^ (1 / 2 + w) =
      ((Real.sqrt Y : ℝ) : ℂ) * Complex.exp (w * (Real.log Y : ℂ)) := by
    intro w
    rw [Complex.cpow_add _ _ hYC]
    congr 1
    · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hY.le]
      norm_num
    · rw [Complex.cpow_def_of_ne_zero hYC, ← Complex.ofReal_log hY.le, mul_comm]
  have hphaseInt : Integrable fun ξ : ℝ =>
      gaussianAmplitude ε ξ₀ (ξ : ℂ) * (1 : ℂ) * Complex.exp (I * (ξ : ℂ) * ((τ + Real.log Y : ℝ) : ℂ)) := by
    refine PacketSymbol.integrable hε ξ₀ ⟨measurable_const, 1, zero_le_one, fun ξ => ?_⟩ _
    simp only [norm_one, one_mul]
    exact Real.one_le_exp (by positivity)
  have hphaseInt₂ : Integrable fun ξ : ℝ =>
      gaussianAmplitude ε ξ₀ (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I) *
        Complex.exp (I * (ξ : ℂ) * ((τ - Real.log Y : ℝ) : ℂ)) := by
    refine PacketSymbol.integrable hε ξ₀ ⟨continuous_scatteringPhase_line.measurable, 1, zero_le_one,
      fun ξ => ?_⟩ _
    rw [norm_scatteringPhase_line, one_mul]
    exact Real.one_le_exp (by positivity)
  simp only [incomingPulse, reflectedSignal, packet]
  rw [← integral_add hphaseInt hphaseInt₂, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [hpower, show (1 / 2 - (ξ : ℂ) * I) = 1 / 2 + (-((ξ : ℂ) * I)) by ring, hpower]
  have hexp1 : Complex.exp (I * (ξ : ℂ) * ((τ + Real.log Y : ℝ) : ℂ)) =
      Complex.exp ((ξ : ℂ) * I * (Real.log Y : ℂ)) * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexp2 : Complex.exp (I * (ξ : ℂ) * ((τ - Real.log Y : ℝ) : ℂ)) =
      Complex.exp (-((ξ : ℂ) * I) * (Real.log Y : ℂ)) * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp1, hexp2]
  ring

/-! ### The black hole field -/

/-- The Neumann radial profile of the packet. -/
def neumannProfile (ε ξ₀ t X x Y : ℝ) : ℂ := neumannLift (fun τ => wavePacket ε ξ₀ τ x Y) t X

/-- The Dirichlet radial profile of the packet. -/
def dirichletProfile (ε ξ₀ t X x Y : ℝ) : ℂ := dirichletLift (fun τ => wavePacket ε ξ₀ τ x Y) t X

section BlackHole

variable {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {t r x y : ℝ} (hr : 1 < r) (hy : 0 < y)

include hε hy

theorem deriv_deriv_packet_x (τ : ℝ) :
    deriv (deriv fun q => wavePacket ε ξ₀ τ q y) x = wavePacketXX ε ξ₀ τ x y := by
  have h : (deriv fun q => wavePacket ε ξ₀ τ q y) = fun q => wavePacketX ε ξ₀ τ q y :=
    funext fun q => (hasDerivAt_wavePacket_x hε ξ₀ τ q hy).deriv
  rw [h]
  exact (hasDerivAt_wavePacketX_x hε ξ₀ τ x hy).deriv

theorem deriv_deriv_packet_y (τ : ℝ) :
    deriv (deriv fun q => wavePacket ε ξ₀ τ x q) y = wavePacketYY ε ξ₀ τ x y := by
  have h : (deriv fun q => wavePacket ε ξ₀ τ x q) =ᶠ[𝓝 y] fun q => wavePacketY ε ξ₀ τ x q := by
    filter_upwards [lt_mem_nhds hy] with q hq
    exact (hasDerivAt_wavePacket_y hε ξ₀ τ x hq).deriv
  rw [h.deriv_eq]
  exact (hasDerivAt_wavePacketY_y hε ξ₀ τ x hy).deriv

include hr

/-- **The conformal scalar with Neumann data solves the wave equation on the black hole.** -/
theorem neumannField_wave :
    blackHoleWaveOperator (conformalScalar (neumannProfile ε ξ₀)) t r x y +
      2 * conformalScalar (neumannProfile ε ξ₀) t r x y = 0 := by
  have hf := fun τ => hasDerivAt_wavePacket_time hε ξ₀ τ x hy
  have hf₁ := fun τ => hasDerivAt_wavePacketT_time hε ξ₀ τ x hy
  have hwave := fun τ => wavePacket_wave hε ξ₀ τ x hy
  rw [blackHoleWaveOperator_conformalScalar _ hr hy
    (Eventually.of_forall fun X => differentiableAt_neumannLift_space hf t X)
    (differentiableAt_deriv_neumannLift_space hf hf₁ t _)]
  set X := tortoise r with hX
  have hmain := neumannLift_modular_wave hf hf₁ (L := fun τ => (y : ℂ) ^ 2 *
    (wavePacketXX ε ξ₀ τ x y + wavePacketYY ε ξ₀ τ x y)) hwave t X
  have hsx : (fun ξ => neumannProfile ε ξ₀ t X ξ y) = fun ξ =>
      Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
        wavePacket ε ξ₀ (hyperboloidalTime t X) ξ y := rfl
  have hsy : (fun η => neumannProfile ε ξ₀ t X x η) = fun η =>
      Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
        wavePacket ε ξ₀ (hyperboloidalTime t X) x η := rfl
  have hdx : deriv (deriv fun ξ => neumannProfile ε ξ₀ t X ξ y) x =
      Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
        wavePacketXX ε ξ₀ (hyperboloidalTime t X) x y := by
    rw [hsx]
    have h1 : (deriv fun ξ => Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
        wavePacket ε ξ₀ (hyperboloidalTime t X) ξ y) = fun ξ =>
        Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
          deriv (fun q => wavePacket ε ξ₀ (hyperboloidalTime t X) q y) ξ :=
      funext fun ξ => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field, deriv_deriv_packet_x hε ξ₀ hy]
  have hdy : deriv (deriv fun η => neumannProfile ε ξ₀ t X x η) y =
      Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
        wavePacketYY ε ξ₀ (hyperboloidalTime t X) x y := by
    rw [hsy]
    have h1 : (deriv fun η => Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
        wavePacket ε ξ₀ (hyperboloidalTime t X) x η) = fun η =>
        Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) *
          deriv (fun q => wavePacket ε ξ₀ (hyperboloidalTime t X) x q) η :=
      funext fun η => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field, deriv_deriv_packet_y hε ξ₀ hy]
  rw [hdx, hdy]
  have hX1 : (deriv (deriv fun X' => neumannProfile ε ξ₀ t X' x y) X) =
      deriv (deriv (neumannLift (fun τ => wavePacket ε ξ₀ τ x y) t)) X := rfl
  have hT1 : (deriv (deriv fun s => neumannProfile ε ξ₀ s X x y) t) =
      deriv (deriv fun s => neumannLift (fun τ => wavePacket ε ξ₀ τ x y) s X) t := rfl
  rw [hX1, hT1]
  have hcancel : deriv (deriv (neumannLift (fun τ => wavePacket ε ξ₀ τ x y) t)) X -
      deriv (deriv fun s => neumannLift (fun τ => wavePacket ε ξ₀ τ x y) s X) t =
      -((1 - (Real.tanh X : ℂ) ^ 2) * neumannLift (fun τ => (y : ℂ) ^ 2 *
        (wavePacketXX ε ξ₀ τ x y + wavePacketYY ε ξ₀ τ x y)) t X) := by
    rw [← hmain]
    ring
  rw [hcancel]
  simp only [neumannLift, dampedProfile]
  push_cast
  ring

/-- **The conformal scalar with Dirichlet data solves the wave equation on the black hole.** -/
theorem dirichletField_wave :
    blackHoleWaveOperator (conformalScalar (dirichletProfile ε ξ₀)) t r x y +
      2 * conformalScalar (dirichletProfile ε ξ₀) t r x y = 0 := by
  have hf := fun τ => hasDerivAt_wavePacket_time hε ξ₀ τ x hy
  have hf₁ := fun τ => hasDerivAt_wavePacketT_time hε ξ₀ τ x hy
  have hwave := fun τ => wavePacket_wave hε ξ₀ τ x hy
  rw [blackHoleWaveOperator_conformalScalar _ hr hy
    (Eventually.of_forall fun X => differentiableAt_dirichletLift_space hf t X)
    (differentiableAt_deriv_dirichletLift_space hf hf₁ t _)]
  set X := tortoise r with hX
  have hmain := dirichletLift_modular_wave hf hf₁ (L := fun τ => (y : ℂ) ^ 2 *
    (wavePacketXX ε ξ₀ τ x y + wavePacketYY ε ξ₀ τ x y)) hwave t X
  set A : ℂ := (Real.tanh X : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (hyperboloidalTime t X : ℂ)) with hA
  have hsx : (fun ξ => dirichletProfile ε ξ₀ t X ξ y) = fun ξ =>
      A * wavePacket ε ξ₀ (hyperboloidalTime t X) ξ y := by
    funext ξ
    simp only [dirichletProfile, dirichletLift, dampedProfile, hA]
    ring
  have hsy : (fun η => dirichletProfile ε ξ₀ t X x η) = fun η =>
      A * wavePacket ε ξ₀ (hyperboloidalTime t X) x η := by
    funext η
    simp only [dirichletProfile, dirichletLift, dampedProfile, hA]
    ring
  have hdx : deriv (deriv fun ξ => dirichletProfile ε ξ₀ t X ξ y) x =
      A * wavePacketXX ε ξ₀ (hyperboloidalTime t X) x y := by
    rw [hsx]
    have h1 : (deriv fun ξ => A * wavePacket ε ξ₀ (hyperboloidalTime t X) ξ y) = fun ξ =>
        A * deriv (fun q => wavePacket ε ξ₀ (hyperboloidalTime t X) q y) ξ :=
      funext fun ξ => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field, deriv_deriv_packet_x hε ξ₀ hy]
  have hdy : deriv (deriv fun η => dirichletProfile ε ξ₀ t X x η) y =
      A * wavePacketYY ε ξ₀ (hyperboloidalTime t X) x y := by
    rw [hsy]
    have h1 : (deriv fun η => A * wavePacket ε ξ₀ (hyperboloidalTime t X) x η) = fun η =>
        A * deriv (fun q => wavePacket ε ξ₀ (hyperboloidalTime t X) x q) η :=
      funext fun η => deriv_const_mul_field _
    rw [h1, deriv_const_mul_field, deriv_deriv_packet_y hε ξ₀ hy]
  rw [hdx, hdy]
  have hX1 : (deriv (deriv fun X' => dirichletProfile ε ξ₀ t X' x y) X) =
      deriv (deriv (dirichletLift (fun τ => wavePacket ε ξ₀ τ x y) t)) X := rfl
  have hT1 : (deriv (deriv fun s => dirichletProfile ε ξ₀ s X x y) t) =
      deriv (deriv fun s => dirichletLift (fun τ => wavePacket ε ξ₀ τ x y) s X) t := rfl
  rw [hX1, hT1]
  have hcancel : deriv (deriv (dirichletLift (fun τ => wavePacket ε ξ₀ τ x y) t)) X -
      deriv (deriv fun s => dirichletLift (fun τ => wavePacket ε ξ₀ τ x y) s X) t =
      -((1 - (Real.tanh X : ℂ) ^ 2) * dirichletLift (fun τ => (y : ℂ) ^ 2 *
        (wavePacketXX ε ξ₀ τ x y + wavePacketYY ε ξ₀ τ x y)) t X) := by
    rw [← hmain]
    ring
  rw [hcancel]
  simp only [dirichletLift, dampedProfile, hA]
  push_cast
  ring

end BlackHole

end GaloisForLFunctions.BlackHoleRingdown

end
