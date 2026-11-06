import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinWavePacket
import GaloisForLFunctions.RHTower.XiSignedFactorZeroSeparation

/-!
# The ringdown expansion of the Eisenstein wave packet

The Eisenstein function is a quotient `E(u; x, Y) = N(u; x, Y)/ξ(1+2u)`, whose numerator

`N(u; x, Y) = Y^{½+u} ξ(1+2u) + ((1+2u)/(2u-1)) ξ(2u) Y^{½-u} + (1+2u)(2u) T(u; x, Y)`

is analytic on `Re u < ½`. Multiplying by the Gaussian amplitude and by `e^{uτ}` gives a numerator of
Gaussian decay on every strip `-A ≤ Re u ≤ 0`, so the contour theorem moves the packet off the line
`Re u = 0`. The field is then the limit over good heights of `2π` times the residues at the points
`(ρ-1)/2`, plus a remainder. The remainder is independent of `A`, because the residues are, so it decays
faster than every exponential as `τ → +∞`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### The numerator of the Eisenstein function -/

/-- The numerator `N(u; x, Y) = ξ(1+2u) E(u; x, Y)`. -/
def eisensteinNumerator (u : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
    (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u) +
    (1 + 2 * u) * (2 * u) * eisTail u x Y

theorem normalizedEisenstein_eq_numerator_div {u : ℂ} (h : xi (1 + 2 * u) ≠ 0) (x Y : ℝ) :
    normalizedEisenstein u x Y = eisensteinNumerator u x Y / xi (1 + 2 * u) := by
  rw [eq_div_iff h]
  simp only [normalizedEisenstein, scatteringPhase, tailWeight, eisensteinNumerator]
  have hX := mul_inv_cancel₀ h
  generalize xi (1 + 2 * u) = X at hX ⊢
  generalize (1 + 2 * u) / (2 * u - 1) = b
  generalize (Y : ℂ) ^ (1 / 2 - u) = B
  generalize (Y : ℂ) ^ (1 / 2 + u) = A
  simp only [div_eq_mul_inv]
  linear_combination (b * xi (2 * u) * B + (1 + 2 * u) * (2 * u) * eisTail u x Y) * hX

theorem differentiableAt_eisTail (x : ℝ) {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    DifferentiableAt ℂ (fun v => eisTail v x Y) u := by
  simp only [eisTail, weightedTail_eq_signedSqrtWhittakerTail]
  exact (differentiableAt_signedSqrtWhittakerTail false x hY u).add
    (differentiableAt_signedSqrtWhittakerTail true x hY u)

theorem differentiableAt_eisensteinNumerator (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ}
    (hu : u.re < 1 / 2) : DifferentiableAt ℂ (fun v => eisensteinNumerator v x Y) u := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 + v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 + v) u).const_cpow (Or.inl hYC)
  have h2 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 - v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 - v) u).const_cpow (Or.inl hYC)
  have hx1 : DifferentiableAt ℂ (fun v : ℂ => xi (1 + 2 * v)) u := differentiable_xi_shift u
  have hx2 : DifferentiableAt ℂ (fun v : ℂ => xi (2 * v)) u :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) u
  have hne : 2 * u - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hq : DifferentiableAt ℂ (fun v : ℂ => (1 + 2 * v) / (2 * v - 1)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) u).div (by fun_prop) hne
  have hp : DifferentiableAt ℂ (fun v : ℂ => (1 + 2 * v) * (2 * v)) u := by fun_prop
  exact ((h1.mul hx1).add ((hq.mul hx2).mul h2)).add (hp.mul (differentiableAt_eisTail x hY u))

theorem analyticAt_eisensteinNumerator (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ} (hu : u.re ≤ 0) :
    AnalyticAt ℂ (fun v => eisensteinNumerator v x Y) u := by
  have hopen : IsOpen {v : ℂ | v.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  have hd : DifferentiableOn ℂ (fun v => eisensteinNumerator v x Y) {v : ℂ | v.re < 1 / 2} :=
    fun v hv => (differentiableAt_eisensteinNumerator x hY hv).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds (show u.re < 1 / 2 by linarith))

/-! ### Bounds on strips -/

/-- `ξ` is bounded on vertical strips: its positive kernel gives `‖ξ(s)‖ ≤ ξ(Re s)`. -/
theorem exists_norm_xi_strip_le (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖xi z‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ => xi (t : ℂ)) (Icc a b) :=
    (xi_differentiable.continuous.comp Complex.continuous_ofReal).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun z hza hzb => ?_⟩
  exact (_root_.RHTower.XiGlobalKummer.norm_xi_le_real_axis z).trans
    ((Complex.re_le_norm _).trans ((hC z.re ⟨hza, hzb⟩).trans (le_max_left _ _)))

theorem norm_cpow_strip_le {Y A : ℝ} (hY : 0 < Y) (w : ℂ) (h1 : 1 / 2 - A ≤ w.re)
    (h2 : w.re ≤ 1 / 2 + A) : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (1 / 2 + A) + Y ^ (1 / 2 - A) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have ha : 0 ≤ Y ^ (1 / 2 + A) := by positivity
  have hb : 0 ≤ Y ^ (1 / 2 - A) := by positivity
  rcases le_total 1 Y with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hY h h1
    linarith

/-- On the left half plane `|1+2u| ≤ |2u-1|`. -/
theorem norm_div_le_one_of_re_nonpos {u : ℂ} (hu : u.re ≤ 0) :
    ‖(1 + 2 * u) / (2 * u - 1)‖ ≤ 1 := by
  rw [norm_div]
  refine div_le_one_of_le₀ ?_ (norm_nonneg _)
  rw [← abs_of_nonneg (norm_nonneg (1 + 2 * u)), ← abs_of_nonneg (norm_nonneg (2 * u - 1)),
    ← sq_le_sq, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.add_im, Complex.one_im, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  nlinarith

/-- The numerator grows at most quadratically on `-A ≤ Re u ≤ 0`, uniformly in `x`. -/
theorem exists_norm_eisensteinNumerator_le {Y A : ℝ} (hY : 0 < Y) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : ℂ) (x : ℝ), -A ≤ u.re → u.re ≤ 0 →
      ‖eisensteinNumerator u x Y‖ ≤ K * (1 + |u.im|) ^ 2 := by
  obtain ⟨C₁, hC₁, hxi⟩ := exists_norm_xi_strip_le (-2 * A) 1
  obtain ⟨C₀, hC₀, htail⟩ := exists_weightedTail_jets_le hY hA
  set M := Y ^ (1 / 2 + A) + Y ^ (1 / 2 - A) with hM
  have hMnn : 0 ≤ M := by positivity
  refine ⟨2 * (M * C₁) + 8 * (1 + A) ^ 2 * C₀, by positivity, fun u x h1 h2 => ?_⟩
  have hyn := abs_nonneg u.im
  have hp1 : 1 ≤ (1 + |u.im|) ^ 2 := one_le_pow₀ (by linarith)
  have habs : |u.re| ≤ A := abs_le.mpr ⟨h1, h2.trans hA⟩
  have hsre1 : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  have hsre2 : (2 * u).re = 2 * u.re := by simp
  have hre1 : (1 / 2 + u).re = 1 / 2 + u.re := by simp
  have hre2 : (1 / 2 - u).re = 1 / 2 - u.re := by simp
  have hP1 : ‖(Y : ℂ) ^ (1 / 2 + u)‖ ≤ M :=
    norm_cpow_strip_le hY _ (by rw [hre1]; linarith) (by rw [hre1]; linarith)
  have hP2 : ‖(Y : ℂ) ^ (1 / 2 - u)‖ ≤ M :=
    norm_cpow_strip_le hY _ (by rw [hre2]; linarith) (by rw [hre2]; linarith)
  have hX1 : ‖xi (1 + 2 * u)‖ ≤ C₁ := hxi _ (by rw [hsre1]; linarith) (by rw [hsre1]; linarith)
  have hX2 : ‖xi (2 * u)‖ ≤ C₁ := hxi _ (by rw [hsre2]; linarith) (by rw [hsre2]; linarith)
  have hT : ‖eisTail u x Y‖ ≤ 2 * C₀ := by
    refine (norm_add_le _ _).trans ?_
    have h₁ := (htail u false x Y habs (mem_window_self hY)).1
    have h₂ := (htail u true x Y habs (mem_window_self hY)).1
    linarith
  have hnorm : ‖u‖ ≤ A + |u.im| := (Complex.norm_le_abs_re_add_abs_im u).trans (by linarith)
  have hF : 1 + 2 * ‖u‖ ≤ 2 * (1 + A) * (1 + |u.im|) := by nlinarith [mul_nonneg hA hyn]
  have hF1 : ‖1 + 2 * u‖ ≤ 2 * (1 + A) * (1 + |u.im|) := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_one, norm_mul, Complex.norm_ofNat]
    exact hF
  have hF2 : ‖2 * u‖ ≤ 2 * (1 + A) * (1 + |u.im|) := by
    simp only [norm_mul, Complex.norm_ofNat]
    linarith
  have hT1 : ‖(Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u)‖ ≤ M * C₁ := by
    rw [norm_mul]
    exact mul_le_mul hP1 hX1 (norm_nonneg _) hMnn
  have hT2 : ‖(1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)‖ ≤ M * C₁ := by
    rw [norm_mul, norm_mul, mul_comm M]
    have hq := norm_div_le_one_of_re_nonpos h2
    calc ‖(1 + 2 * u) / (2 * u - 1)‖ * ‖xi (2 * u)‖ * ‖(Y : ℂ) ^ (1 / 2 - u)‖
        ≤ (1 * C₁) * M :=
          mul_le_mul (mul_le_mul hq hX2 (norm_nonneg _) zero_le_one) hP2 (norm_nonneg _)
            (by positivity)
      _ = C₁ * M := by ring
  have hT3 : ‖(1 + 2 * u) * (2 * u) * eisTail u x Y‖ ≤
      8 * (1 + A) ^ 2 * C₀ * (1 + |u.im|) ^ 2 := by
    rw [norm_mul, norm_mul]
    calc ‖1 + 2 * u‖ * ‖2 * u‖ * ‖eisTail u x Y‖
        ≤ ((2 * (1 + A) * (1 + |u.im|)) * (2 * (1 + A) * (1 + |u.im|))) * (2 * C₀) :=
          mul_le_mul (mul_le_mul hF1 hF2 (norm_nonneg _) (by positivity)) hT (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hconst : M * C₁ ≤ M * C₁ * (1 + |u.im|) ^ 2 :=
    le_mul_of_one_le_right (by positivity) hp1
  rw [eisensteinNumerator]
  refine (norm_add₃_le).trans ?_
  nlinarith

/-- The amplitude off the real axis: `‖a(-iu)‖ = exp(-ε(Im u - ξ₀)² + ε(Re u)²)`. -/
theorem norm_gaussianAmplitude_rotated (ε ξ₀ : ℝ) (u : ℂ) :
    ‖gaussianAmplitude ε ξ₀ (-I * u)‖ = Real.exp (-ε * (u.im - ξ₀) ^ 2 + ε * u.re ^ 2) := by
  rw [gaussianAmplitude, Complex.norm_exp]
  congr 1
  rw [pow_two]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring

/-! ### The numerator of the packet -/

/-- The numerator `a(-iu) e^{uτ} N(u; x, Y)` of the packet. -/
def packetNumerator (ε ξ₀ τ x Y : ℝ) (u : ℂ) : ℂ :=
  gaussianAmplitude ε ξ₀ (-I * u) * Complex.exp (u * (τ : ℂ)) * eisensteinNumerator u x Y

theorem analyticAt_gaussianAmplitude_rotated (ε ξ₀ : ℝ) (u : ℂ) :
    AnalyticAt ℂ (fun v => gaussianAmplitude ε ξ₀ (-I * v)) u := by
  unfold gaussianAmplitude
  fun_prop

/-- The numerator of the packet has Gaussian decay on every strip. -/
theorem gaussianNumerator_packet {ε : ℝ} (hε : 0 < ε) (ξ₀ τ x : ℝ) {Y A : ℝ} (hY : 0 < Y)
    (hA : 0 ≤ A) : GaussianNumerator A (packetNumerator ε ξ₀ τ x Y) where
  analytic := fun u _ h2 => by
    have h1 : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v * (τ : ℂ))) u := by fun_prop
    exact ((analyticAt_gaussianAmplitude_rotated ε ξ₀ u).mul h1).mul
      (analyticAt_eisensteinNumerator x hY h2)
  decay := by
    obtain ⟨K, hK, hN⟩ := exists_norm_eisensteinNumerator_le hY hA
    obtain ⟨C₁, hC₁, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian 2 (b := 0) (c := ε / 4)
      (by positivity)
    refine ⟨Real.exp (ε * A ^ 2 + ε * ξ₀ ^ 2) * Real.exp (A * |τ|) * K * C₁, ε / 4, by positivity,
      by positivity, fun u h1 h2 => ?_⟩
    have habs : |u.re| ≤ A := abs_le.mpr ⟨h1, h2.trans hA⟩
    have hsq : u.re ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hamp : ‖gaussianAmplitude ε ξ₀ (-I * u)‖ ≤
        Real.exp (ε * A ^ 2 + ε * ξ₀ ^ 2) * Real.exp (-(ε / 2) * u.im ^ 2) := by
      rw [norm_gaussianAmplitude_rotated, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_nonneg hε.le (sq_nonneg (u.im - 2 * ξ₀)), mul_le_mul_of_nonneg_left hsq hε.le]
    have hexp : ‖Complex.exp (u * (τ : ℂ))‖ ≤ Real.exp (A * |τ|) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have hre : (u * (τ : ℂ)).re = u.re * τ := by simp
      rw [hre]
      calc u.re * τ ≤ |u.re * τ| := le_abs_self _
        _ = |u.re| * |τ| := abs_mul _ _
        _ ≤ A * |τ| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    have hpoly := hcmp |u.im| (abs_nonneg _)
    simp only [zero_mul, Real.exp_zero, mul_one, sq_abs] at hpoly
    have hgauss : Real.exp (-(ε / 2) * u.im ^ 2) * Real.exp (ε / 4 * u.im ^ 2) =
        Real.exp (-(ε / 4) * u.im ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [packetNumerator, norm_mul, norm_mul]
    calc ‖gaussianAmplitude ε ξ₀ (-I * u)‖ * ‖Complex.exp (u * (τ : ℂ))‖ *
          ‖eisensteinNumerator u x Y‖
        ≤ (Real.exp (ε * A ^ 2 + ε * ξ₀ ^ 2) * Real.exp (-(ε / 2) * u.im ^ 2)) *
            Real.exp (A * |τ|) * (K * (C₁ * Real.exp (ε / 4 * u.im ^ 2))) :=
          mul_le_mul (mul_le_mul hamp hexp (norm_nonneg _) (by positivity))
            ((hN u x h1 h2).trans (mul_le_mul_of_nonneg_left hpoly hK)) (norm_nonneg _)
            (by positivity)
      _ = Real.exp (ε * A ^ 2 + ε * ξ₀ ^ 2) * Real.exp (A * |τ|) * K * C₁ *
            (Real.exp (-(ε / 2) * u.im ^ 2) * Real.exp (ε / 4 * u.im ^ 2)) := by ring
      _ = _ := by rw [hgauss]

/-- On the line `Re u = 0` the quotient is the integrand of the packet. -/
theorem inverseXiQuotient_packet_line (ε ξ₀ τ x Y y : ℝ) :
    inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) ((y : ℂ) * I) =
      gaussianAmplitude ε ξ₀ (y : ℂ) * normalizedEisenstein ((y : ℂ) * I) x Y *
        Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
  have h : -I * ((y : ℂ) * I) = y := by linear_combination (-(y : ℂ)) * I_sq
  have he : Complex.exp ((y : ℂ) * I * (τ : ℂ)) = Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
    congr 1
    ring
  rw [inverseXiQuotient, packetNumerator, h, he,
    normalizedEisenstein_eq_numerator_div (xi_line_ne_zero y)]
  ring

theorem wavePacket_eq_lineIntegral (ε ξ₀ τ x Y : ℝ) :
    wavePacket ε ξ₀ τ x Y = ∫ y : ℝ, inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) ((y : ℂ) * I) := by
  simp only [wavePacket, packet, inverseXiQuotient_packet_line]

/-- The time dependence of the quotient is the factor `e^{uτ}`. -/
theorem inverseXiQuotient_packet_time (ε ξ₀ τ x Y : ℝ) (u : ℂ) :
    inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) u =
      Complex.exp (u * (τ : ℂ)) * inverseXiQuotient (packetNumerator ε ξ₀ 0 x Y) u := by
  simp only [inverseXiQuotient, packetNumerator, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-! ### The expansion -/

/-- The remainder on the line `Re u = -A`. -/
def ringdownRemainder (A ε ξ₀ τ x Y : ℝ) : ℂ :=
  ∫ y : ℝ, inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I)

/-- `2π` times the residues at the zeros up to the `k`-th good height. -/
def ringdownPartialSum (ε ξ₀ τ x Y : ℝ) (k : ℕ) : ℂ :=
  2 * Real.pi * ∑ p ∈ ringdownPoles (goodHeight k),
    laurentCoeff (inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)) p (-1)

section Expansion

variable {ε : ℝ} (hε : 0 < ε) (ξ₀ x : ℝ) {Y : ℝ} (hY : 0 < Y)

include hε hY

/-- The contour theorem for the packet, at any depth `A ≥ 1`. -/
theorem tendsto_ringdownPartialSum (τ : ℝ) {A : ℝ} (hA : 1 ≤ A) :
    Tendsto (ringdownPartialSum ε ξ₀ τ x Y) atTop
      (𝓝 (wavePacket ε ξ₀ τ x Y - ringdownRemainder A ε ξ₀ τ x Y)) := by
  have h := (tendsto_sum_laurentCoeff_inverseXiQuotient hA
    (gaussianNumerator_packet hε ξ₀ τ x hY (by linarith))).const_mul (2 * Real.pi : ℂ)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [mul_inv_cancel_left₀ hpi, ← wavePacket_eq_lineIntegral] at h
  exact h

/-- The remainder does not depend on the depth of the contour. -/
theorem ringdownRemainder_eq (τ : ℝ) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ringdownRemainder A ε ξ₀ τ x Y = ringdownRemainder B ε ξ₀ τ x Y := by
  have h := tendsto_nhds_unique (tendsto_ringdownPartialSum hε ξ₀ x hY τ hA)
    (tendsto_ringdownPartialSum hε ξ₀ x hY τ hB)
  exact sub_right_injective h

/-- At depth `A` the remainder is `O(e^{-Aτ})`, uniformly in `τ`. -/
theorem exists_norm_ringdownRemainder_le {A : ℝ} (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ,
      ‖ringdownRemainder A ε ξ₀ τ x Y‖ ≤ C * Real.exp (-A * τ) := by
  have hint := integrable_inverseXiQuotient_left hA
    (gaussianNumerator_packet hε ξ₀ 0 x hY (by linarith))
  refine ⟨∫ y : ℝ, ‖inverseXiQuotient (packetNumerator ε ξ₀ 0 x Y)
    (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖, integral_nonneg fun _ => norm_nonneg _, fun τ => ?_⟩
  have hpoint : ∀ y : ℝ,
      ‖inverseXiQuotient (packetNumerator ε ξ₀ τ x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ =
        Real.exp (-A * τ) * ‖inverseXiQuotient (packetNumerator ε ξ₀ 0 x Y)
          (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
    intro y
    rw [inverseXiQuotient_packet_time, norm_mul, Complex.norm_exp]
    congr 2
    simp
  calc ‖ringdownRemainder A ε ξ₀ τ x Y‖
      ≤ ∫ y : ℝ, ‖inverseXiQuotient (packetNumerator ε ξ₀ τ x Y)
          (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ := norm_integral_le_integral_norm _
    _ = Real.exp (-A * τ) * ∫ y : ℝ, ‖inverseXiQuotient (packetNumerator ε ξ₀ 0 x Y)
          (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
        simp_rw [hpoint]
        exact integral_const_mul _ _
    _ = _ := mul_comm _ _

/-- **The ringdown expansion.**  The packet is the limit over good heights of `2π` times the residues
at the points `(ρ-1)/2`, up to a remainder that decays faster than every exponential as `τ → +∞`. -/
theorem ringdown_expansion :
    ∃ R : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖R τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ τ : ℝ, Tendsto (ringdownPartialSum ε ξ₀ τ x Y) atTop
        (𝓝 (wavePacket ε ξ₀ τ x Y - R τ)) := by
  refine ⟨fun τ => ringdownRemainder 1 ε ξ₀ τ x Y, fun A hA => ?_, fun τ =>
    tendsto_ringdownPartialSum hε ξ₀ x hY τ le_rfl⟩
  obtain ⟨C, hC, hb⟩ := exists_norm_ringdownRemainder_le hε ξ₀ x hY hA
  refine ⟨C, hC, fun τ => ?_⟩
  simp only
  rw [ringdownRemainder_eq hε ξ₀ x hY τ le_rfl hA]
  exact hb τ

end Expansion

end GaloisForLFunctions.BlackHoleRingdown

end
