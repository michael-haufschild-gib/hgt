import GaloisForLFunctions.RHTower.ThetaCompactStripZeroEngineering
import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum
import GaloisForLFunctions.HTGeometry.WaveTracePoleTransform
import GaloisForLFunctions.RHTower.ThetaZeroDivisionSource

/-!
# Real-analytic theta surgery forcing a zero inside the Xi strip

The two-packet surgery with the analytic weight `ψ(x) = k(x) e^{-x²}`: the source
`g_u = k (1 + r_u)`, `r_u = e^{-x²}(α cos(ux) + β x sin(ux) - Σ γ_i A_i)`, keeps the exact anchors
(moments through order `J`, critical charge `1/2`), has the forced zero `F_{g_u}(u + iv) = 0`, is
even, real analytic, positive and strongly log-concave, converges to `k` in every Schwartz
seminorm, and has relative tail `|g_u/k - 1| ≤ C_u (1 + |x|)^{2N+1} e^{-x²/2}`, faster than every
`e^{-c|x|}`. Its continuation `k(z)(1 + R_u(z))` to the source strip `|Im z| < π/4` converges to the
complexified source uniformly on compact subsets. The derivative control comes from Cauchy
estimates for the entire function `R_u` on thin horizontal strips. Both surgered sources have
entire Fourier transforms.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ContDiff

namespace RHTower

noncomputable section

/-! ## Exponential-growth integrability against the Gaussian-damped source -/

/-- The analytic weight `ψ(x) = k(x) e^{-x²}`. -/
def surgeryGaussWeight (x : ℝ) : ℝ := thetaCuspFullSource x * Real.exp (-x ^ 2)

theorem surgeryGaussWeight_pos (x : ℝ) : 0 < surgeryGaussWeight x :=
  mul_pos (thetaCuspFullSource_pos_all x) (Real.exp_pos _)

theorem surgeryGaussWeight_neg (x : ℝ) : surgeryGaussWeight (-x) = surgeryGaussWeight x := by
  simp [surgeryGaussWeight, thetaCuspFullSource_neg]

theorem contDiff_gaussWeight : ContDiff ℝ ∞ surgeryGaussWeight :=
  contDiff_thetaCuspFullSource.mul (by fun_prop)

theorem surgeryGaussWeight_le (x : ℝ) : surgeryGaussWeight x ≤ thetaCuspFullSource x := by
  have := thetaCuspFullSource_pos_all x
  exact mul_le_of_le_one_right this.le (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

/-- A continuous function of exponential growth is integrable against `ψ`. -/
theorem integrable_mul_gaussWeight {f : ℝ → ℝ} (hf : Continuous f) {B C : ℝ}
    (hb : ∀ x, |f x| ≤ C * Real.exp (B * |x|)) : Integrable fun x => f x * surgeryGaussWeight x := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_thetaCuspFullSource_le (|B| + 1)
  refine ((integrable_exp_neg_abs_line).const_mul (|C| * K)).mono'
    ((hf.mul contDiff_gaussWeight.continuous).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (surgeryGaussWeight_pos x)]
  have h1 : |f x| ≤ |C| * Real.exp (|B| * |x|) :=
    (hb x).trans (mul_le_mul (le_abs_self C) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (le_abs_self B) (abs_nonneg x))) (Real.exp_pos _).le (abs_nonneg C))
  have h2 : surgeryGaussWeight x ≤ K * Real.exp (-((|B| + 1) * |x|)) :=
    (surgeryGaussWeight_le x).trans ((le_abs_self _).trans (hK x))
  calc |f x| * surgeryGaussWeight x ≤ (|C| * Real.exp (|B| * |x|)) * (K * Real.exp (-((|B| + 1) * |x|))) :=
        mul_le_mul h1 h2 (surgeryGaussWeight_pos x).le (by positivity)
    _ = |C| * K * Real.exp (-|x|) := by
        rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf

theorem abs_pow_le_exp (m : ℕ) (x : ℝ) : |x ^ m| ≤ m.factorial * Real.exp (1 * |x|) := by
  rw [abs_pow, one_mul]
  have := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) m
  rwa [div_le_iff₀ (by positivity), mul_comm] at this

theorem abs_evenAnchor_le (N : ℕ) (i : Fin (N + 2)) :
    ∃ C, ∀ x, |evenAnchor N i x| ≤ C * Real.exp (1 * |x|) := by
  unfold evenAnchor
  split_ifs
  · exact ⟨_, abs_pow_le_exp _⟩
  · refine ⟨1, fun x => ?_⟩
    rw [abs_of_pos (Real.cosh_pos _), one_mul, one_mul, Real.cosh_eq]
    have h1 : Real.exp (x / 2) ≤ Real.exp |x| := Real.exp_le_exp.mpr (by
      linarith [le_abs_self x, abs_nonneg x])
    have h2 : Real.exp (-(x / 2)) ≤ Real.exp |x| := Real.exp_le_exp.mpr (by
      linarith [neg_abs_le x, abs_nonneg x])
    linarith

theorem abs_mul_exp_growth {f g : ℝ → ℝ} {B₁ C₁ B₂ C₂ : ℝ}
    (hf : ∀ x, |f x| ≤ C₁ * Real.exp (B₁ * |x|)) (hg : ∀ x, |g x| ≤ C₂ * Real.exp (B₂ * |x|))
    (x : ℝ) : |f x * g x| ≤ (C₁ * C₂) * Real.exp ((B₁ + B₂) * |x|) := by
  rw [abs_mul, add_mul, Real.exp_add]
  have hC₁ : 0 ≤ C₁ := by
    have := (abs_nonneg _).trans (hf 0); simp at this; exact this
  calc |f x| * |g x| ≤ (C₁ * Real.exp (B₁ * |x|)) * (C₂ * Real.exp (B₂ * |x|)) :=
        mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem abs_exp_mul_le (v x : ℝ) : |Real.exp (v * x)| ≤ 1 * Real.exp (|v| * |x|) := by
  rw [abs_of_pos (Real.exp_pos _), one_mul]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by rw [abs_mul]))

/-- The weight is admissible for the anchor projection. -/
theorem surgeryGaussWeight_anchorWeight (N : ℕ) : AnchorWeight N surgeryGaussWeight where
  continuous := contDiff_gaussWeight.continuous
  nonneg x := (surgeryGaussWeight_pos x).le
  pos := ⟨1, one_pos, fun x _ => surgeryGaussWeight_pos x⟩
  integrable i j := by
    obtain ⟨C₁, h₁⟩ := abs_evenAnchor_le N i
    obtain ⟨C₂, h₂⟩ := abs_evenAnchor_le N j
    have := integrable_mul_gaussWeight ((continuous_evenAnchor N i).mul (continuous_evenAnchor N j))
      (abs_mul_exp_growth h₁ h₂)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring

/-! ## Packets, directions and their evaluations -/

/-- The analytic cosine packet `ψ(x) cos(ux)`. -/
def gaussCosPacket (u x : ℝ) : ℝ := surgeryGaussWeight x * Real.cos (u * x)

/-- The analytic sine packet `x ψ(x) sin(ux)`. -/
def gaussSinPacket (u x : ℝ) : ℝ := x * surgeryGaussWeight x * Real.sin (u * x)

/-- The analytic cosine direction `Π(ψ cos(u·))`. -/
def gaussCosDirection (N : ℕ) (u : ℝ) : ℝ → ℝ := anchorProj N surgeryGaussWeight (gaussCosPacket u)

/-- The analytic sine direction `Π(x ψ sin(u·))`. -/
def gaussSinDirection (N : ℕ) (u : ℝ) : ℝ → ℝ := anchorProj N surgeryGaussWeight (gaussSinPacket u)

theorem continuous_gaussCosPacket (u : ℝ) : Continuous (gaussCosPacket u) := by
  have := contDiff_gaussWeight.continuous; unfold gaussCosPacket; fun_prop

theorem continuous_gaussSinPacket (u : ℝ) : Continuous (gaussSinPacket u) := by
  have := contDiff_gaussWeight.continuous; unfold gaussSinPacket; fun_prop

theorem integrable_stripEval_integrand_of {v u : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hi : Integrable fun x => Real.exp (v * x) * f x) :
    Integrable fun x : ℝ => cexp (-I * ((u : ℂ) + v * I) * x) * (f x : ℂ) := by
  refine hi.norm.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [cexp_packet, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  simp

theorem integrable_exp_mul_evenAnchor_gauss (N : ℕ) (i : Fin (N + 2)) (v : ℝ) :
    Integrable fun x => Real.exp (v * x) * (surgeryGaussWeight x * evenAnchor N i x) := by
  obtain ⟨C, h⟩ := abs_evenAnchor_le N i
  refine (integrable_mul_gaussWeight ((by fun_prop : Continuous fun x => Real.exp (v * x)).mul
    (continuous_evenAnchor N i)) (abs_mul_exp_growth (abs_exp_mul_le v) h)).congr
    (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]; ring

theorem stripEval_anchorProj_gauss {N : ℕ} {v u : ℝ} {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable fun x => Real.exp (v * x) * b x) :
    stripEval v u (anchorProj N surgeryGaussWeight b) = stripEval v u b -
      ∑ i, (anchorCoef N surgeryGaussWeight b i : ℂ) *
        stripEval v u fun x => surgeryGaussWeight x * evenAnchor N i x := by
  have hi : ∀ i : Fin (N + 2), Integrable fun x : ℝ => (anchorCoef N surgeryGaussWeight b i : ℂ) *
      (cexp (-I * ((u : ℂ) + v * I) * x) * ((surgeryGaussWeight x * evenAnchor N i x : ℝ) : ℂ)) :=
    fun i => (integrable_stripEval_integrand_of (contDiff_gaussWeight.continuous.mul
      (continuous_evenAnchor N i)) (integrable_exp_mul_evenAnchor_gauss N i v)).const_mul _
  simp only [stripEval]
  have hsum : ∑ i, (anchorCoef N surgeryGaussWeight b i : ℂ) *
      (∫ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) * ((surgeryGaussWeight x * evenAnchor N i x : ℝ) : ℂ)) =
      ∫ x : ℝ, ∑ i, (anchorCoef N surgeryGaussWeight b i : ℂ) *
        (cexp (-I * ((u : ℂ) + v * I) * x) * ((surgeryGaussWeight x * evenAnchor N i x : ℝ) : ℂ)) := by
    rw [integral_finsetSum _ fun i _ => hi i]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  rw [hsum, ← integral_sub (integrable_stripEval_integrand_of hb hbi)
    (integrable_finsetSum _ fun i _ => hi i)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [anchorProj]
  push_cast
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem integrable_evenAnchor_mul_gauss (N : ℕ) (j : Fin (N + 2)) {f : ℝ → ℝ} (hf : Continuous f)
    {B C : ℝ} (hb : ∀ x, |f x| ≤ C * Real.exp (B * |x|)) :
    Integrable fun x => evenAnchor N j x * (f x * surgeryGaussWeight x) := by
  obtain ⟨C', h'⟩ := abs_evenAnchor_le N j
  refine (integrable_mul_gaussWeight ((continuous_evenAnchor N j).mul hf)
    (abs_mul_exp_growth h' hb)).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]; ring

theorem abs_cos_growth (u x : ℝ) : |Real.cos (u * x)| ≤ 1 * Real.exp (0 * |x|) := by
  simp [Real.abs_cos_le_one]

theorem abs_id_growth (x : ℝ) : |x| ≤ 1 * Real.exp (1 * |x|) := by
  have := abs_pow_le_exp 1 x; simpa using this

theorem tendsto_anchorMoments_gaussCos (N : ℕ) (j : Fin (N + 2)) :
    Tendsto (fun u => anchorMoments N (gaussCosPacket u) j) atTop (𝓝 0) := by
  have hw : Integrable fun x => evenAnchor N j x * surgeryGaussWeight x := by
    have := integrable_evenAnchor_mul_gauss N j (f := fun _ => 1) continuous_const
      (B := 0) (C := 1) (fun x => by simp)
    simpa using this
  refine (tendsto_integral_mul_cos hw).congr fun u => ?_
  simp only [anchorMoments, gaussCosPacket]
  congr 1; ext x; ring

theorem tendsto_anchorMoments_gaussSin (N : ℕ) (j : Fin (N + 2)) :
    Tendsto (fun u => anchorMoments N (gaussSinPacket u) j) atTop (𝓝 0) := by
  have hw : Integrable fun x => evenAnchor N j x * (x * surgeryGaussWeight x) :=
    integrable_evenAnchor_mul_gauss N j continuous_id abs_id_growth
  refine (tendsto_integral_mul_sin hw).congr fun u => ?_
  simp only [anchorMoments, gaussSinPacket]
  congr 1; ext x; ring

theorem tendsto_correction_gauss (N : ℕ) (v : ℝ) {b : ℝ → ℝ → ℝ}
    (hb : ∀ j, Tendsto (fun u => anchorMoments N (b u) j) atTop (𝓝 0)) :
    Tendsto (fun u => ∑ i, (anchorCoef N surgeryGaussWeight (b u) i : ℂ) *
      stripEval v u fun x => surgeryGaussWeight x * evenAnchor N i x) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin (N + 2))) fun i _ =>
    ((Complex.continuous_ofReal.tendsto 0).comp (tendsto_anchorCoef (ψ := surgeryGaussWeight) hb i)).mul
      (tendsto_packet_fixed v (φ := fun x => surgeryGaussWeight x * evenAnchor N i x))
  simp only [Function.comp_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero] at h
  exact h

theorem integrable_exp_mul_gaussWeight (v : ℝ) :
    Integrable fun x => Real.exp (v * x) * surgeryGaussWeight x :=
  integrable_mul_gaussWeight (by fun_prop) (abs_exp_mul_le v)

theorem integrable_exp_mul_id_mul_gaussWeight (v : ℝ) :
    Integrable fun x => Real.exp (v * x) * (x * surgeryGaussWeight x) := by
  refine (integrable_mul_gaussWeight ((by fun_prop : Continuous fun x => Real.exp (v * x)).mul
    continuous_id) (abs_mul_exp_growth (abs_exp_mul_le v) (fun x => abs_id_growth x))).congr
    (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, id]; ring

theorem tendsto_stripEval_gaussCosDirection (N : ℕ) (v : ℝ) :
    Tendsto (fun u => stripEval v u (gaussCosDirection N u)) atTop
      (𝓝 ((1 / 2 : ℂ) * ((∫ x, Real.exp (v * x) * surgeryGaussWeight x : ℝ) : ℂ))) := by
  have hmain := tendsto_packet_cos v (φ := surgeryGaussWeight) (integrable_exp_mul_gaussWeight v)
  have h := hmain.sub (tendsto_correction_gauss N v (tendsto_anchorMoments_gaussCos N))
  rw [sub_zero] at h
  refine h.congr fun u => ?_
  have hbi : Integrable fun x => Real.exp (v * x) * gaussCosPacket u x := by
    refine (integrable_mul_gaussWeight ((by fun_prop : Continuous fun x => Real.exp (v * x)).mul
      (by fun_prop : Continuous fun x => Real.cos (u * x)))
      (abs_mul_exp_growth (abs_exp_mul_le v) (abs_cos_growth u))).congr
      (Eventually.of_forall fun x => ?_)
    simp only [gaussCosPacket, Pi.mul_apply]; ring
  rw [gaussCosDirection, stripEval_anchorProj_gauss (continuous_gaussCosPacket u) hbi]
  rfl

theorem tendsto_stripEval_gaussSinDirection (N : ℕ) (v : ℝ) :
    Tendsto (fun u => stripEval v u (gaussSinDirection N u)) atTop
      (𝓝 ((-I / 2) * ((∫ x, Real.exp (v * x) * (x * surgeryGaussWeight x) : ℝ) : ℂ))) := by
  have hmain := tendsto_packet_sin v (φ := fun x => x * surgeryGaussWeight x)
    (integrable_exp_mul_id_mul_gaussWeight v)
  have h := hmain.sub (tendsto_correction_gauss N v (tendsto_anchorMoments_gaussSin N))
  rw [sub_zero] at h
  refine h.congr fun u => ?_
  have hbi : Integrable fun x => Real.exp (v * x) * gaussSinPacket u x := by
    have hs : ∀ x, |Real.sin (u * x)| ≤ 1 * Real.exp (0 * |x|) := fun x => by
      simp [Real.abs_sin_le_one]
    refine (integrable_mul_gaussWeight (((by fun_prop : Continuous fun x => Real.exp (v * x)).mul
      continuous_id).mul (by fun_prop : Continuous fun x => Real.sin (u * x)))
      (abs_mul_exp_growth (abs_mul_exp_growth (abs_exp_mul_le v) (fun x => abs_id_growth x)) hs)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [gaussSinPacket, Pi.mul_apply, id_eq]; ring
  rw [gaussSinDirection, stripEval_anchorProj_gauss (continuous_gaussSinPacket u) hbi]
  rfl

theorem integral_exp_mul_gaussWeight_pos (v : ℝ) :
    0 < ∫ x, Real.exp (v * x) * surgeryGaussWeight x :=
  integral_pos_of_integrable_nonneg_nonzero (x := 0)
    (by have := contDiff_gaussWeight.continuous; fun_prop) (integrable_exp_mul_gaussWeight v)
    (fun x => mul_nonneg (Real.exp_pos _).le (surgeryGaussWeight_pos x).le)
    (mul_pos (Real.exp_pos _) (surgeryGaussWeight_pos 0)).ne'

theorem integral_exp_mul_id_mul_gaussWeight_pos {v : ℝ} (hv : 0 < v) :
    0 < ∫ x, Real.exp (v * x) * (x * surgeryGaussWeight x) := by
  have hi := integrable_exp_mul_id_mul_gaussWeight v
  have hsym : ∫ x, Real.exp (v * x) * (x * surgeryGaussWeight x) =
      ∫ x, Real.exp (v * -x) * (-x * surgeryGaussWeight (-x)) :=
    (integral_neg_eq_self (fun x => Real.exp (v * x) * (x * surgeryGaussWeight x)) volume).symm
  have heq : ∫ x, Real.exp (v * x) * (x * surgeryGaussWeight x) =
      ∫ x, x * Real.sinh (v * x) * surgeryGaussWeight x := by
    have h2 : 2 * ∫ x, Real.exp (v * x) * (x * surgeryGaussWeight x) =
        ∫ x, 2 * (x * Real.sinh (v * x) * surgeryGaussWeight x) := by
      rw [two_mul]
      nth_rewrite 2 [hsym]
      rw [← integral_add hi (by have := hi.comp_neg; simpa using this)]
      congr 1; ext x
      rw [surgeryGaussWeight_neg, Real.sinh_eq]
      ring_nf
    rw [integral_const_mul] at h2
    linarith
  have hneg : Integrable fun x => Real.exp (-(v * x)) * (x * surgeryGaussWeight x) := by
    have := hi.comp_neg.neg
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply, surgeryGaussWeight_neg]; ring_nf
  have hi2 : Integrable fun x => x * Real.sinh (v * x) * surgeryGaussWeight x := by
    refine ((hi.sub hneg).div_const 2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [Real.sinh_eq]; ring
  rw [heq]
  refine integral_pos_of_integrable_nonneg_nonzero (x := 1 / 2)
    (by have := contDiff_gaussWeight.continuous; fun_prop) hi2 (fun x => ?_) ?_
  · refine mul_nonneg ?_ (surgeryGaussWeight_pos x).le
    rcases le_total 0 x with h | h
    · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr (by positivity))
    · exact mul_nonneg_of_nonpos_of_nonpos h (Real.sinh_nonpos_iff.mpr (by nlinarith))
  · have : 0 < Real.sinh (v * (1 / 2)) := Real.sinh_pos_iff.mpr (by positivity)
    have := surgeryGaussWeight_pos (1 / 2)
    positivity

/-! ## The analytic two-packet solve -/

/-- The analytic cosine evaluation. -/
def gaussCosEval (N : ℕ) (v u : ℝ) : ℂ := stripEval v u (gaussCosDirection N u)

/-- The analytic sine evaluation. -/
def gaussSinEval (N : ℕ) (v u : ℝ) : ℂ := stripEval v u (gaussSinDirection N u)

/-- Real coefficient of the analytic cosine direction. -/
def gaussAlpha (N : ℕ) (v u : ℝ) : ℝ :=
  -(conj (gaussSinEval N v u) * -XiC ((u : ℂ) + v * I)).im /
    (conj (gaussCosEval N v u) * gaussSinEval N v u).im

/-- Real coefficient of the analytic sine direction. -/
def gaussBeta (N : ℕ) (v u : ℝ) : ℝ :=
  (conj (gaussCosEval N v u) * -XiC ((u : ℂ) + v * I)).im /
    (conj (gaussCosEval N v u) * gaussSinEval N v u).im

/-- The combined anchor coefficients `γ_i = α c_i(ψ cos) + β c_i(x ψ sin)`. -/
def gaussGamma (N : ℕ) (v u : ℝ) (i : Fin (N + 2)) : ℝ :=
  gaussAlpha N v u * anchorCoef N surgeryGaussWeight (gaussCosPacket u) i +
    gaussBeta N v u * anchorCoef N surgeryGaussWeight (gaussSinPacket u) i

/-- The relative perturbation
`r_u(x) = e^{-x²} (α cos(ux) + β x sin(ux) - Σ γ_i A_i(x))`. -/
def gaussRelative (N : ℕ) (v u x : ℝ) : ℝ :=
  Real.exp (-x ^ 2) * (gaussAlpha N v u * Real.cos (u * x) + gaussBeta N v u * x * Real.sin (u * x) -
    ∑ i, gaussGamma N v u i * evenAnchor N i x)

/-- **The analytic surgery** `g_u = k + α Π(ψ cos(u·)) + β Π(x ψ sin(u·))`. -/
def gaussSurgerySource (N : ℕ) (v u x : ℝ) : ℝ :=
  thetaCuspFullSource x + (gaussAlpha N v u * gaussCosDirection N u x +
    gaussBeta N v u * gaussSinDirection N u x)

theorem anchorProj_eq_sub_mul (N : ℕ) (ψ b : ℝ → ℝ) (x : ℝ) :
    anchorProj N ψ b x = b x - ψ x * ∑ i, anchorCoef N ψ b i * evenAnchor N i x := by
  rw [anchorProj, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Relative form.** `g_u = k (1 + r_u)`. -/
theorem gaussSurgerySource_eq (N : ℕ) (v u x : ℝ) :
    gaussSurgerySource N v u x = thetaCuspFullSource x * (1 + gaussRelative N v u x) := by
  have hγ : ∑ i, gaussGamma N v u i * evenAnchor N i x =
      gaussAlpha N v u * ∑ i, anchorCoef N surgeryGaussWeight (gaussCosPacket u) i * evenAnchor N i x +
      gaussBeta N v u * ∑ i, anchorCoef N surgeryGaussWeight (gaussSinPacket u) i * evenAnchor N i x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [gaussGamma]; ring
  rw [gaussSurgerySource, gaussCosDirection, gaussSinDirection, anchorProj_eq_sub_mul,
    anchorProj_eq_sub_mul, gaussRelative, hγ]
  simp only [gaussCosPacket, gaussSinPacket, surgeryGaussWeight]
  ring

theorem gaussSurgerySource_neg (N : ℕ) (v u x : ℝ) :
    gaussSurgerySource N v u (-x) = gaussSurgerySource N v u x := by
  have hc : ∀ x, gaussCosPacket u (-x) = gaussCosPacket u x := fun x => by
    simp [gaussCosPacket, surgeryGaussWeight_neg, Real.cos_neg]
  have hs : ∀ x, gaussSinPacket u (-x) = gaussSinPacket u x := fun x => by
    simp only [gaussSinPacket, surgeryGaussWeight_neg, mul_neg, Real.sin_neg]; ring
  simp only [gaussSurgerySource, gaussCosDirection, gaussSinDirection, thetaCuspFullSource_neg,
    anchorProj_neg surgeryGaussWeight_neg hc, anchorProj_neg surgeryGaussWeight_neg hs]

/-- Uniform solvability with decay `e^{-δu}` for every `δ < π/4`. -/
theorem exists_gaussSolve (N : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < Real.pi / 4) :
    ∃ K U : ℝ, 0 ≤ K ∧ ∀ u, U ≤ u →
      (conj (gaussCosEval N v u) * gaussSinEval N v u).im ≠ 0 ∧
      |gaussAlpha N v u| + |gaussBeta N v u| ≤ K * Real.exp (-(δ * u)) := by
  set A₀ := ∫ x, Real.exp (v * x) * surgeryGaussWeight x
  set B₀ := ∫ x, Real.exp (v * x) * (x * surgeryGaussWeight x)
  have hA := integral_exp_mul_gaussWeight_pos v
  have hB := integral_exp_mul_id_mul_gaussWeight_pos hv
  have hdeg : (conj ((1 / 2 : ℂ) * (A₀ : ℂ)) * ((-I / 2) * (B₀ : ℂ))).im ≠ 0 := by
    have : (conj ((1 / 2 : ℂ) * (A₀ : ℂ)) * ((-I / 2) * (B₀ : ℂ))).im = -(A₀ * B₀) / 4 := by
      simp [Complex.mul_im, Complex.mul_re]; ring
    rw [this]; exact div_ne_zero (neg_ne_zero.mpr (mul_pos hA hB).ne') (by norm_num)
  obtain ⟨K, U, hK, hU⟩ := exists_real_solve_bound (tendsto_stripEval_gaussCosDirection N v)
    (tendsto_stripEval_gaussSinDirection N v) hdeg
  obtain ⟨C, hC, hXi⟩ := exists_norm_XiC_horizontal_le (A := 1 / 2) (δ := δ) (by norm_num) hδ0
    (by linarith)
  refine ⟨K * C, max U 0, by positivity, fun u hu => ⟨(hU u (le_of_max_le_left hu)).1, ?_⟩⟩
  have hu0 : 0 ≤ u := le_of_max_le_right hu
  have h := (hU u (le_of_max_le_left hu)).2 (-XiC ((u : ℂ) + v * I))
  rw [norm_neg] at h
  have hx := hXi u v (by rw [abs_of_pos hv]; linarith)
  rw [abs_of_nonneg hu0] at hx
  rw [gaussAlpha, gaussBeta, neg_div, abs_neg]
  calc _ ≤ K * ‖XiC ((u : ℂ) + v * I)‖ := h
    _ ≤ K * (C * Real.exp (-(δ * u))) := mul_le_mul_of_nonneg_left hx hK
    _ = K * C * Real.exp (-(δ * u)) := by ring

/-! ## Exact anchors and the forced zero -/

theorem integrable_growth_mul_anchorProj_gauss {N : ℕ} {f b₀ : ℝ → ℝ} (hf : Continuous f)
    {B C : ℝ} (hfb : ∀ x, |f x| ≤ C * Real.exp (B * |x|)) (hb₀ : Continuous b₀) {B₀ C₀ : ℝ}
    (hb₀b : ∀ x, |b₀ x| ≤ C₀ * Real.exp (B₀ * |x|)) :
    Integrable fun x => f x * anchorProj N surgeryGaussWeight (fun y => b₀ y * surgeryGaussWeight y) x := by
  have h1 : Integrable fun x => (f x * b₀ x) * surgeryGaussWeight x :=
    integrable_mul_gaussWeight (hf.mul hb₀) (abs_mul_exp_growth hfb hb₀b)
  have h2 : ∀ i : Fin (N + 2), Integrable fun x =>
      anchorCoef N surgeryGaussWeight (fun y => b₀ y * surgeryGaussWeight y) i *
        ((f x * evenAnchor N i x) * surgeryGaussWeight x) := fun i => by
    obtain ⟨C', h'⟩ := abs_evenAnchor_le N i
    exact (integrable_mul_gaussWeight (hf.mul (continuous_evenAnchor N i))
      (abs_mul_exp_growth hfb h')).const_mul _
  refine (h1.sub (integrable_finsetSum Finset.univ fun i _ => h2 i)).congr
    (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, anchorProj, mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

theorem gaussCosPacket_eq (u : ℝ) :
    gaussCosPacket u = fun y => Real.cos (u * y) * surgeryGaussWeight y := by
  funext y; simp only [gaussCosPacket]; ring

theorem gaussSinPacket_eq (u : ℝ) :
    gaussSinPacket u = fun y => (y * Real.sin (u * y)) * surgeryGaussWeight y := by
  funext y; simp only [gaussSinPacket]; ring

theorem abs_sin_growth (u x : ℝ) : |Real.sin (u * x)| ≤ 1 * Real.exp (0 * |x|) := by
  simp [Real.abs_sin_le_one]

theorem abs_id_mul_sin_growth (u x : ℝ) : |x * Real.sin (u * x)| ≤ (1 * 1) * Real.exp ((1 + 0) * |x|) :=
  abs_mul_exp_growth abs_id_growth (abs_sin_growth u) x

theorem integrable_growth_mul_gaussCosDirection {N : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    {B C : ℝ} (hfb : ∀ x, |f x| ≤ C * Real.exp (B * |x|)) (u : ℝ) :
    Integrable fun x => f x * gaussCosDirection N u x := by
  rw [gaussCosDirection, gaussCosPacket_eq]
  exact integrable_growth_mul_anchorProj_gauss hf hfb (by fun_prop) (abs_cos_growth u)

theorem integrable_growth_mul_gaussSinDirection {N : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    {B C : ℝ} (hfb : ∀ x, |f x| ≤ C * Real.exp (B * |x|)) (u : ℝ) :
    Integrable fun x => f x * gaussSinDirection N u x := by
  rw [gaussSinDirection, gaussSinPacket_eq]
  exact integrable_growth_mul_anchorProj_gauss hf hfb (by fun_prop) (abs_id_mul_sin_growth u)

theorem continuous_gaussCosDirection (N : ℕ) (u : ℝ) : Continuous (gaussCosDirection N u) := by
  have := contDiff_gaussWeight.continuous
  have hA := continuous_evenAnchor N
  unfold gaussCosDirection anchorProj gaussCosPacket
  exact (by fun_prop : Continuous fun x => surgeryGaussWeight x * Real.cos (u * x)).sub
    (continuous_finsetSum _ fun i _ => continuous_const.mul (this.mul (hA i)))

theorem continuous_gaussSinDirection (N : ℕ) (u : ℝ) : Continuous (gaussSinDirection N u) := by
  have := contDiff_gaussWeight.continuous
  have hA := continuous_evenAnchor N
  unfold gaussSinDirection anchorProj gaussSinPacket
  exact (by fun_prop : Continuous fun x => x * surgeryGaussWeight x * Real.sin (u * x)).sub
    (continuous_finsetSum _ fun i _ => continuous_const.mul (this.mul (hA i)))

/-- **Forced strip zero** of the analytic surgery. -/
theorem stripEval_gaussSurgerySource_eq_zero {N : ℕ} {v u : ℝ}
    (hD : (conj (gaussCosEval N v u) * gaussSinEval N v u).im ≠ 0) :
    stripEval v u (gaussSurgerySource N v u) = 0 := by
  have hc := integrable_stripEval_integrand_of (v := v) (u := u)
    (continuous_gaussCosDirection N u)
    (integrable_growth_mul_gaussCosDirection (by fun_prop) (abs_exp_mul_le v) u)
  have hs := integrable_stripEval_integrand_of (v := v) (u := u)
    (continuous_gaussSinDirection N u)
    (integrable_growth_mul_gaussSinDirection (by fun_prop) (abs_exp_mul_le v) u)
  have hcs : Integrable fun x : ℝ =>
      (gaussAlpha N v u : ℂ) * (cexp (-I * ((u : ℂ) + v * I) * x) * (gaussCosDirection N u x : ℂ)) +
      (gaussBeta N v u : ℂ) * (cexp (-I * ((u : ℂ) + v * I) * x) * (gaussSinDirection N u x : ℂ)) :=
    (hc.const_mul _).add (hs.const_mul _)
  have hsplit : stripEval v u (gaussSurgerySource N v u) = stripEval v u thetaCuspFullSource +
      ((gaussAlpha N v u : ℂ) * gaussCosEval N v u + (gaussBeta N v u : ℂ) * gaussSinEval N v u) := by
    have e1 : stripEval v u (gaussSurgerySource N v u) = stripEval v u thetaCuspFullSource +
        ∫ x : ℝ, ((gaussAlpha N v u : ℂ) * (cexp (-I * ((u : ℂ) + v * I) * x) *
          (gaussCosDirection N u x : ℂ)) + (gaussBeta N v u : ℂ) *
            (cexp (-I * ((u : ℂ) + v * I) * x) * (gaussSinDirection N u x : ℂ))) := by
      simp only [stripEval]
      rw [← integral_add (integrable_stripEval_thetaCuspFullSource v u) hcs]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [gaussSurgerySource]; push_cast; ring
    rw [e1, integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  have hcomb : (gaussAlpha N v u : ℂ) * gaussCosEval N v u +
      (gaussBeta N v u : ℂ) * gaussSinEval N v u = -XiC ((u : ℂ) + v * I) :=
    real_combination_eq hD
  rw [hsplit, stripEval_thetaCuspFullSource, hcomb, add_neg_cancel]

theorem integral_evenAnchor_mul_gaussPerturbation (N : ℕ) (v u : ℝ) (j : Fin (N + 2)) :
    ∫ x, evenAnchor N j x * (gaussAlpha N v u * gaussCosDirection N u x +
      gaussBeta N v u * gaussSinDirection N u x) = 0 := by
  obtain ⟨C, hj⟩ := abs_evenAnchor_le N j
  have hA := continuous_evenAnchor N j
  have hc0 := integral_evenAnchor_mul_anchorProj (surgeryGaussWeight_anchorWeight N)
    (b := gaussCosPacket u) (fun j => by
      obtain ⟨C', h'⟩ := abs_evenAnchor_le N j
      rw [gaussCosPacket_eq]
      refine (integrable_mul_gaussWeight ((continuous_evenAnchor N j).mul
        (by fun_prop : Continuous fun y => Real.cos (u * y))) (abs_mul_exp_growth h'
          (abs_cos_growth u))).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring) j
  have hs0 := integral_evenAnchor_mul_anchorProj (surgeryGaussWeight_anchorWeight N)
    (b := gaussSinPacket u) (fun j => by
      obtain ⟨C', h'⟩ := abs_evenAnchor_le N j
      rw [gaussSinPacket_eq]
      refine (integrable_mul_gaussWeight ((continuous_evenAnchor N j).mul
        (by fun_prop : Continuous fun y => y * Real.sin (u * y))) (abs_mul_exp_growth h'
          (abs_id_mul_sin_growth u))).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring) j
  have i1 := (integrable_growth_mul_gaussCosDirection (N := N) hA hj u).const_mul (gaussAlpha N v u)
  have i2 := (integrable_growth_mul_gaussSinDirection (N := N) hA hj u).const_mul (gaussBeta N v u)
  rw [show (fun x => evenAnchor N j x * (gaussAlpha N v u * gaussCosDirection N u x +
      gaussBeta N v u * gaussSinDirection N u x)) = fun x =>
      gaussAlpha N v u * (evenAnchor N j x * gaussCosDirection N u x) +
        gaussBeta N v u * (evenAnchor N j x * gaussSinDirection N u x) by funext x; ring,
    integral_add i1 i2, integral_const_mul, integral_const_mul]
  simp only [gaussCosDirection, gaussSinDirection]
  rw [hc0, hs0]; ring

theorem gaussPerturbation_neg (N : ℕ) (v u x : ℝ) :
    gaussAlpha N v u * gaussCosDirection N u (-x) + gaussBeta N v u * gaussSinDirection N u (-x) =
      gaussAlpha N v u * gaussCosDirection N u x + gaussBeta N v u * gaussSinDirection N u x := by
  have := gaussSurgerySource_neg N v u x
  simp only [gaussSurgerySource, thetaCuspFullSource_neg] at this
  linarith

/-- **Exact moments** of the analytic surgery through order `2N + 1`. -/
theorem integral_pow_mul_gaussSurgerySource (N : ℕ) (v u : ℝ) {j : ℕ} (hj : j ≤ 2 * N + 1) :
    ∫ x, x ^ j * gaussSurgerySource N v u x = ∫ x, x ^ j * thetaCuspFullSource x := by
  set h : ℝ → ℝ := fun x => gaussAlpha N v u * gaussCosDirection N u x +
    gaussBeta N v u * gaussSinDirection N u x
  have hp : Integrable fun x => x ^ j * h x := by
    have hb := abs_pow_le_exp j
    have i1 := (integrable_growth_mul_gaussCosDirection (N := N) (continuous_pow j) hb u).const_mul
      (gaussAlpha N v u)
    have i2 := (integrable_growth_mul_gaussSinDirection (N := N) (continuous_pow j) hb u).const_mul
      (gaussBeta N v u)
    refine (i1.add i2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, h]; ring
  have hzero : ∫ x, x ^ j * h x = 0 := by
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | hodd
    · have hi : i < N + 1 := by omega
      have := integral_evenAnchor_mul_gaussPerturbation N v u (Fin.castSucc ⟨i, hi⟩)
      simp only [evenAnchor_castSucc] at this
      rw [← this]; congr 1; ext x; simp only [h]; ring_nf
    · exact integral_odd_real_eq_zero fun x => by
        simp only [h]; rw [gaussPerturbation_neg, hodd.neg_pow]; ring
  have hsplit : (fun x => x ^ j * gaussSurgerySource N v u x) =
      fun x => x ^ j * thetaCuspFullSource x + x ^ j * h x := by
    funext x; simp only [gaussSurgerySource, h]; ring
  rw [hsplit, integral_add (integrable_pow_mul_thetaCuspFullSource j) hp, hzero, add_zero]

/-- **Critical charge** of the analytic surgery: `∫ e^{x/2} g_u = 1/2`. -/
theorem integral_exp_half_mul_gaussSurgerySource (N : ℕ) (v u : ℝ) :
    ∫ x, Real.exp (x / 2) * gaussSurgerySource N v u x = 1 / 2 := by
  set h : ℝ → ℝ := fun x => gaussAlpha N v u * gaussCosDirection N u x +
    gaussBeta N v u * gaussSinDirection N u x
  have hk : Integrable fun x => Real.exp (x / 2) * thetaCuspFullSource x := by
    have := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource (1 / 2)
    simpa [div_eq_inv_mul, mul_comm] using this
  have hint : ∀ {f : ℝ → ℝ}, Continuous f → ∀ {B C : ℝ},
      (∀ x, |f x| ≤ C * Real.exp (B * |x|)) → Integrable fun x => f x * h x := by
    intro f hf B C hb
    refine (((integrable_growth_mul_gaussCosDirection (N := N) hf hb u).const_mul (gaussAlpha N v u)).add
      ((integrable_growth_mul_gaussSinDirection (N := N) hf hb u).const_mul (gaussBeta N v u))).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, h]; ring
  have hcoshb : ∀ x, |Real.cosh (x / 2)| ≤ 1 * Real.exp (1 * |x|) := fun x => by
    have := abs_evenAnchor_le N (Fin.last (N + 1))
    rw [abs_of_pos (Real.cosh_pos _), one_mul, one_mul, Real.cosh_eq]
    have h1 : Real.exp (x / 2) ≤ Real.exp |x| := Real.exp_le_exp.mpr (by
      linarith [le_abs_self x, abs_nonneg x])
    have h2 : Real.exp (-(x / 2)) ≤ Real.exp |x| := Real.exp_le_exp.mpr (by
      linarith [neg_abs_le x, abs_nonneg x])
    linarith
  have hsinhb : ∀ x, |Real.sinh (x / 2)| ≤ 1 * Real.exp (1 * |x|) := fun x => by
    rw [one_mul, one_mul, Real.sinh_eq, abs_le]
    have h1 : Real.exp (x / 2) ≤ Real.exp |x| := Real.exp_le_exp.mpr (by
      linarith [le_abs_self x, abs_nonneg x])
    have h2 : Real.exp (-(x / 2)) ≤ Real.exp |x| := Real.exp_le_exp.mpr (by
      linarith [neg_abs_le x, abs_nonneg x])
    have := Real.exp_pos (x / 2); have := Real.exp_pos (-(x / 2))
    constructor <;> linarith
  have hcosh := integral_evenAnchor_mul_gaussPerturbation N v u (Fin.last (N + 1))
  simp only [evenAnchor_last] at hcosh
  have hsinh : ∫ x, Real.sinh (x / 2) * h x = 0 :=
    integral_odd_real_eq_zero fun x => by
      simp only [h]; rw [gaussPerturbation_neg, neg_div, Real.sinh_neg]; ring
  have hpz : ∫ x, Real.exp (x / 2) * h x = 0 := by
    rw [show (fun x => Real.exp (x / 2) * h x) = fun x =>
      Real.cosh (x / 2) * h x + Real.sinh (x / 2) * h x by
      funext x; rw [← add_mul, Real.cosh_add_sinh],
      integral_add (hint (by fun_prop) hcoshb) (hint (by fun_prop) hsinhb), hsinh, add_zero]
    exact hcosh
  have hsplit : (fun x => Real.exp (x / 2) * gaussSurgerySource N v u x) =
      fun x => Real.exp (x / 2) * thetaCuspFullSource x + Real.exp (x / 2) * h x := by
    funext x; simp only [gaussSurgerySource, h]; ring
  rw [hsplit, integral_add hk (hint (by fun_prop) (fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_exp.mpr (by linarith [le_abs_self x, abs_nonneg x] :
      x / 2 ≤ 1 * |x|)).trans (by rw [one_mul, one_mul]))), hpz, add_zero,
    integral_exp_half_mul_thetaCuspFullSource]

/-! ## The complexified relative perturbation and Cauchy estimates -/

/-- The entire anchors `z^{2i}` and `cosh(z/2)`. -/
def anchorC (N : ℕ) (i : Fin (N + 2)) (z : ℂ) : ℂ :=
  if (i : ℕ) ≤ N then z ^ (2 * (i : ℕ)) else Complex.cosh (z / 2)

theorem anchorC_ofReal (N : ℕ) (i : Fin (N + 2)) (x : ℝ) :
    anchorC N i x = (evenAnchor N i x : ℂ) := by
  unfold anchorC evenAnchor
  split_ifs <;> push_cast <;> rfl

theorem differentiable_anchorC (N : ℕ) (i : Fin (N + 2)) : Differentiable ℂ (anchorC N i) := by
  unfold anchorC; split_ifs <;> fun_prop

/-- The entire extension `R_u(z)` of the relative perturbation. -/
def gaussRelativeC (N : ℕ) (v u : ℝ) (z : ℂ) : ℂ :=
  cexp (-z ^ 2) * ((gaussAlpha N v u : ℂ) * Complex.cos (u * z) +
    (gaussBeta N v u : ℂ) * z * Complex.sin (u * z) - ∑ i, (gaussGamma N v u i : ℂ) * anchorC N i z)

theorem gaussRelativeC_ofReal (N : ℕ) (v u x : ℝ) :
    gaussRelativeC N v u x = (gaussRelative N v u x : ℂ) := by
  simp only [gaussRelativeC, gaussRelative, anchorC_ofReal]
  push_cast
  rfl

theorem differentiable_gaussRelativeC (N : ℕ) (v u : ℝ) : Differentiable ℂ (gaussRelativeC N v u) := by
  have hA := differentiable_anchorC N
  unfold gaussRelativeC
  exact (by fun_prop : Differentiable ℂ fun z : ℂ => cexp (-z ^ 2)).mul
    (((by fun_prop : Differentiable ℂ fun z : ℂ => (gaussAlpha N v u : ℂ) * Complex.cos (u * z) +
      (gaussBeta N v u : ℂ) * z * Complex.sin (u * z))).sub
      (Differentiable.fun_sum fun i _ => (differentiable_const _).mul (hA i)))

theorem norm_ccosh_le (w : ℂ) : ‖Complex.cosh w‖ ≤ Real.exp |w.re| := by
  rw [Complex.cosh, norm_div, Complex.norm_ofNat]
  have h1 : ‖cexp w‖ ≤ Real.exp |w.re| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : ‖cexp (-w)‖ ≤ Real.exp |w.re| := by
    rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖cexp w + cexp (-w)‖ / 2 ≤ (Real.exp |w.re| + Real.exp |w.re|) / 2 := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = Real.exp |w.re| := by ring

theorem norm_anchorC_le (N : ℕ) (i : Fin (N + 2)) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖anchorC N i z‖ ≤ (1 + |z.re|) ^ (2 * N) * Real.exp (|z.re| / 2) := by
  have h1 : 1 ≤ 1 + |z.re| := by linarith [abs_nonneg z.re]
  have he : 1 ≤ Real.exp (|z.re| / 2) := Real.one_le_exp (by positivity)
  have hp : 1 ≤ (1 + |z.re|) ^ (2 * N) := one_le_pow₀ h1
  unfold anchorC
  split_ifs with hi
  · rw [norm_pow]
    have hn : ‖z‖ ≤ 1 + |z.re| := by
      have := Complex.norm_le_abs_re_add_abs_im z; linarith
    calc ‖z‖ ^ (2 * (i : ℕ)) ≤ (1 + |z.re|) ^ (2 * (i : ℕ)) :=
          pow_le_pow_left₀ (norm_nonneg _) hn _
      _ ≤ (1 + |z.re|) ^ (2 * N) := pow_le_pow_right₀ h1 (by omega)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he
  · refine (norm_ccosh_le _).trans ?_
    rw [show (z / 2).re = z.re / 2 by simp, abs_div, abs_two]
    exact le_mul_of_one_le_left (Real.exp_pos _).le hp

theorem gaussian_growth_le (m : ℕ) (t : ℝ) :
    Real.exp (-t ^ 2) * (1 + |t|) ^ m * Real.exp (|t| / 2) ≤ m.factorial * Real.exp 2 := by
  have h1 : (1 + |t|) ^ m ≤ m.factorial * Real.exp (1 + |t|) := by
    have := Real.pow_div_factorial_le_exp (1 + |t|) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  calc Real.exp (-t ^ 2) * (1 + |t|) ^ m * Real.exp (|t| / 2)
      ≤ Real.exp (-t ^ 2) * (m.factorial * Real.exp (1 + |t|)) * Real.exp (|t| / 2) := by gcongr
    _ = m.factorial * (Real.exp (-t ^ 2) * Real.exp (1 + |t|) * Real.exp (|t| / 2)) := by ring
    _ = m.factorial * Real.exp (-t ^ 2 + (1 + |t|) + |t| / 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ m.factorial * Real.exp 2 := by
        gcongr
        have := sq_abs t
        nlinarith [sq_nonneg (|t| - 3 / 4)]

/-- The constant of the complex bound. -/
def gaussRelativeConst (N : ℕ) : ℝ := Real.exp 1 * ((2 * N + 1).factorial * Real.exp 2)

/-- **Strip bound.** For `|Im z| ≤ ρ ≤ 1` and `u ≥ 0`,
`‖R_u(z)‖ ≤ L (|α| + |β| + Σ|γ_i|) e^{uρ}`. -/
theorem norm_gaussRelativeC_le (N : ℕ) (v : ℝ) {u ρ : ℝ} (hu : 0 ≤ u) (hρ1 : ρ ≤ 1) {z : ℂ}
    (hz : |z.im| ≤ ρ) :
    ‖gaussRelativeC N v u z‖ ≤ gaussRelativeConst N *
      (|gaussAlpha N v u| + |gaussBeta N v u| + ∑ i, |gaussGamma N v u i|) * Real.exp (u * ρ) := by
  set a := z.re
  set T := |gaussAlpha N v u| + |gaussBeta N v u| + ∑ i, |gaussGamma N v u i|
  have hT : 0 ≤ T := by positivity
  have hz1 : |z.im| ≤ 1 := hz.trans hρ1
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans hz
  have hE : 1 ≤ Real.exp (u * ρ) := Real.one_le_exp (by positivity)
  have h1a : 1 ≤ 1 + |a| := by linarith [abs_nonneg a]
  set P := (1 + |a|) ^ (2 * N + 1) * Real.exp (|a| / 2)
  have hP1 : 1 + |a| ≤ P := by
    have h2 : 1 + |a| ≤ (1 + |a|) ^ (2 * N + 1) := by
      simpa using pow_le_pow_right₀ h1a (by omega : 1 ≤ 2 * N + 1)
    exact h2.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
  have hPA : (1 + |a|) ^ (2 * N) * Real.exp (|a| / 2) ≤ P :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1a (by omega)) (Real.exp_pos _).le
  have hcos : ‖Complex.cos ((u : ℂ) * z)‖ ≤ Real.exp (u * ρ) := by
    refine (norm_ccos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
    rw [show ((u : ℂ) * z).im = u * z.im by simp, abs_mul, abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left hz hu
  have hsin : ‖Complex.sin ((u : ℂ) * z)‖ ≤ Real.exp (u * ρ) := by
    refine (norm_csin_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
    rw [show ((u : ℂ) * z).im = u * z.im by simp, abs_mul, abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left hz hu
  have hzn : ‖z‖ ≤ 1 + |a| := by
    have := Complex.norm_le_abs_re_add_abs_im z; linarith
  have hinner : ‖(gaussAlpha N v u : ℂ) * Complex.cos (u * z) +
      (gaussBeta N v u : ℂ) * z * Complex.sin (u * z) -
      ∑ i, (gaussGamma N v u i : ℂ) * anchorC N i z‖ ≤ T * P * Real.exp (u * ρ) := by
    have ha : ‖(gaussAlpha N v u : ℂ) * Complex.cos (u * z)‖ ≤
        |gaussAlpha N v u| * (P * Real.exp (u * ρ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hcos.trans (le_mul_of_one_le_left (Real.exp_pos _).le
        (by linarith))) (abs_nonneg _)
    have hb : ‖(gaussBeta N v u : ℂ) * z * Complex.sin (u * z)‖ ≤
        |gaussBeta N v u| * (P * Real.exp (u * ρ)) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hzn.trans hP1) hsin (norm_nonneg _)
        (by linarith)) (abs_nonneg _)
    have hg : ‖∑ i, (gaussGamma N v u i : ℂ) * anchorC N i z‖ ≤
        (∑ i, |gaussGamma N v u i|) * (P * Real.exp (u * ρ)) := by
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((norm_anchorC_le N i hz1).trans (hPA.trans
        (le_mul_of_one_le_right (by positivity) hE))) (abs_nonneg _)
    have n1 := norm_sub_le ((gaussAlpha N v u : ℂ) * Complex.cos (u * z) +
      (gaussBeta N v u : ℂ) * z * Complex.sin (u * z)) (∑ i, (gaussGamma N v u i : ℂ) * anchorC N i z)
    have n2 := norm_add_le ((gaussAlpha N v u : ℂ) * Complex.cos (u * z))
      ((gaussBeta N v u : ℂ) * z * Complex.sin (u * z))
    rw [show T * P * Real.exp (u * ρ) = T * (P * Real.exp (u * ρ)) by ring]
    simp only [T]
    nlinarith
  have hexp : ‖cexp (-z ^ 2)‖ ≤ Real.exp 1 * Real.exp (-a ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : (-z ^ 2).re = z.im ^ 2 - a ^ 2 := by simp [sq, a]
    rw [this]
    have : z.im ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z.im]
    linarith
  have hG := gaussian_growth_le (2 * N + 1) a
  calc ‖gaussRelativeC N v u z‖ ≤ (Real.exp 1 * Real.exp (-a ^ 2)) * (T * P * Real.exp (u * ρ)) := by
        rw [gaussRelativeC, norm_mul]; exact mul_le_mul hexp hinner (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * (Real.exp (-a ^ 2) * (1 + |a|) ^ (2 * N + 1) * Real.exp (|a| / 2)) * T *
          Real.exp (u * ρ) := by simp only [P]; ring
    _ ≤ Real.exp 1 * ((2 * N + 1).factorial * Real.exp 2) * T * Real.exp (u * ρ) := by gcongr
    _ = _ := by rw [gaussRelativeConst]

theorem iteratedDeriv_re_ofReal {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (F x).re) = fun x : ℝ => (iteratedDeriv n F (x : ℂ)).re := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : Differentiable ℂ (iteratedDeriv n F) :=
      (hF.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)
    rw [((hd x).hasDerivAt.real_of_complex).deriv, iteratedDeriv_succ]

theorem gaussRelative_eq_re (N : ℕ) (v u : ℝ) :
    gaussRelative N v u = fun x : ℝ => (gaussRelativeC N v u (x : ℂ)).re := by
  funext x; rw [gaussRelativeC_ofReal, Complex.ofReal_re]

/-- **Cauchy estimate** for the real relative perturbation. -/
theorem abs_iteratedDeriv_gaussRelative_le (N n : ℕ) (v : ℝ) {u ρ : ℝ} (hu : 0 ≤ u) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (x : ℝ) :
    |iteratedDeriv n (gaussRelative N v u) x| ≤ n.factorial * (gaussRelativeConst N *
      (|gaussAlpha N v u| + |gaussBeta N v u| + ∑ i, |gaussGamma N v u i|) *
        Real.exp (u * ρ)) / ρ ^ n := by
  rw [gaussRelative_eq_re, iteratedDeriv_re_ofReal (differentiable_gaussRelativeC N v u)]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ0
    (differentiable_gaussRelativeC N v u).diffContOnCl fun z hz => ?_
  refine norm_gaussRelativeC_le N v hu hρ1 ?_
  have := Complex.abs_im_le_norm (z - x)
  rw [mem_sphere_iff_norm] at hz
  simp only [sub_im, ofReal_im, sub_zero] at this
  linarith

/-! ## Uniform smallness of the relative perturbation -/

/-- All coefficients decay like `e^{-δu}`, `δ < π/4`. -/
theorem exists_gauss_coeff_bound (N : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ < Real.pi / 4) :
    ∃ K U : ℝ, 0 ≤ K ∧ ∀ u, U ≤ u →
      (conj (gaussCosEval N v u) * gaussSinEval N v u).im ≠ 0 ∧
      |gaussAlpha N v u| + |gaussBeta N v u| + ∑ i, |gaussGamma N v u i| ≤
        K * Real.exp (-(δ * u)) := by
  obtain ⟨K, U₁, hK, h₁⟩ := exists_gaussSolve N hv hv2 hδ0 hδ
  have hc : ∀ᶠ u in atTop, ∀ i, |anchorCoef N surgeryGaussWeight (gaussCosPacket u) i| ≤ 1 ∧
      |anchorCoef N surgeryGaussWeight (gaussSinPacket u) i| ≤ 1 :=
    eventually_all.mpr fun i => by
      have h1 := (tendsto_anchorCoef (ψ := surgeryGaussWeight) (tendsto_anchorMoments_gaussCos N) i).abs
      have h2 := (tendsto_anchorCoef (ψ := surgeryGaussWeight) (tendsto_anchorMoments_gaussSin N) i).abs
      rw [abs_zero] at h1 h2
      exact (h1.eventually (eventually_le_nhds one_pos)).and (h2.eventually (eventually_le_nhds one_pos))
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp hc
  refine ⟨(N + 3) * K, max U₁ U₂, by positivity, fun u hu => ⟨(h₁ u (le_of_max_le_left hu)).1, ?_⟩⟩
  have hab := (h₁ u (le_of_max_le_left hu)).2
  have hγ : ∑ i, |gaussGamma N v u i| ≤ (N + 2) * (|gaussAlpha N v u| + |gaussBeta N v u|) := by
    have : ∀ i, |gaussGamma N v u i| ≤ |gaussAlpha N v u| + |gaussBeta N v u| := fun i => by
      obtain ⟨c1, c2⟩ := hU₂ u (le_of_max_le_right hu) i
      simp only [gaussGamma]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) c1)
        (mul_le_of_le_one_right (abs_nonneg _) c2)
    calc ∑ i, |gaussGamma N v u i| ≤ ∑ _i : Fin (N + 2), (|gaussAlpha N v u| + |gaussBeta N v u|) :=
          Finset.sum_le_sum fun i _ => this i
      _ = (N + 2) * (|gaussAlpha N v u| + |gaussBeta N v u|) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hE := Real.exp_pos (-(δ * u))
  nlinarith [abs_nonneg (gaussAlpha N v u), abs_nonneg (gaussBeta N v u)]

/-- `|r_u^{(n)}(x)| ≤ B e^{-u/8}` uniformly in `x`. -/
theorem exists_bound_iteratedDeriv_gaussRelative (N n : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) :
    ∃ B U : ℝ, 0 ≤ B ∧ ∀ u, U ≤ u → ∀ x,
      |iteratedDeriv n (gaussRelative N v u) x| ≤ B * Real.exp (-(u / 8)) := by
  obtain ⟨K, U, hK, hU⟩ := exists_gauss_coeff_bound N hv hv2 (δ := 1 / 4) (by norm_num)
    (by linarith [Real.pi_gt_three])
  have hL : 0 ≤ gaussRelativeConst N := by unfold gaussRelativeConst; positivity
  refine ⟨n.factorial * (gaussRelativeConst N * K) * 8 ^ n, max U 0, by positivity,
    fun u hu x => ?_⟩
  have hu0 : 0 ≤ u := le_of_max_le_right hu
  have h := abs_iteratedDeriv_gaussRelative_le N n v hu0 (ρ := 1 / 8) (by norm_num) (by norm_num) x
  have hc := (hU u (le_of_max_le_left hu)).2
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have e1 : Real.exp (-(1 / 4 * u)) * Real.exp (u * (1 / 8)) = Real.exp (-(u / 8)) := by
    rw [← Real.exp_add]; ring_nf
  calc (n.factorial : ℝ) * (gaussRelativeConst N *
        (|gaussAlpha N v u| + |gaussBeta N v u| + ∑ i, |gaussGamma N v u i|) * Real.exp (u * (1 / 8)))
      ≤ n.factorial * (gaussRelativeConst N * (K * Real.exp (-(1 / 4 * u))) *
          Real.exp (u * (1 / 8))) := by gcongr
    _ = n.factorial * (gaussRelativeConst N * K) * Real.exp (-(u / 8)) := by rw [← e1]; ring
    _ = n.factorial * (gaussRelativeConst N * K) * 8 ^ n * Real.exp (-(u / 8)) * (1 / 8) ^ n := by
        have h8 : (8 : ℝ) ^ n * (1 / 8) ^ n = 1 := by rw [← mul_pow]; norm_num
        calc (n.factorial : ℝ) * (gaussRelativeConst N * K) * Real.exp (-(u / 8)) =
            n.factorial * (gaussRelativeConst N * K) * Real.exp (-(u / 8)) * (8 ^ n * (1 / 8) ^ n) := by
              rw [h8, mul_one]
          _ = _ := by ring

/-! ## Schwartz convergence and the relative tail -/

/-- **Schwartz convergence** of the analytic surgery. -/
theorem gaussSurgerySource_schwartz (N n p : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) : ∃ U : ℝ, ∀ u, U ≤ u → ∀ x : ℝ,
      |x| ^ p * |iteratedDeriv n (fun y => gaussSurgerySource N v u y - thetaCuspFullSource y) x|
        ≤ ε := by
  have hB : ∀ i ≤ n, ∃ B U : ℝ, 0 ≤ B ∧ ∀ u, U ≤ u → ∀ x,
      |iteratedDeriv (n - i) (gaussRelative N v u) x| ≤ B * Real.exp (-(u / 8)) :=
    fun i _ => exists_bound_iteratedDeriv_gaussRelative N (n - i) hv hv2
  choose! B U hB0 hBU using hB
  have hk : ∀ i, ∃ C, 0 ≤ C ∧ ∀ x, |iteratedDeriv i thetaCuspFullSource x| ≤ C * Real.exp (-(1 * |x|)) :=
    fun i => exists_abs_iteratedDeriv_thetaCuspFullSource_le 1 i
  choose C hC0 hC using hk
  set M := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (p.factorial * C i) * B i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i hi => by
    have := hB0 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)); have := hC0 i; positivity
  have hlim := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 8))).const_mul M
  rw [mul_zero] at hlim
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds hε))
  refine ⟨max U₀ ((Finset.range (n + 1)).sup' ⟨0, by simp⟩ U), fun u hu x => ?_⟩
  have hfun : (fun y => gaussSurgerySource N v u y - thetaCuspFullSource y) =
      thetaCuspFullSource * gaussRelative N v u := by
    funext y; rw [gaussSurgerySource_eq]; simp only [Pi.mul_apply]; ring
  have hrc : ContDiff ℝ ∞ (gaussRelative N v u) := by
    rw [gaussRelative_eq_re]
    exact (Complex.reCLM.contDiff.comp ((((differentiable_gaussRelativeC N v u).contDiff
      (n := ⊤)).restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff)).of_le le_top
  rw [hfun, iteratedDeriv_mul (contDiff_thetaCuspFullSource.contDiffAt.of_le (mod_cast le_top))
    (hrc.contDiffAt.of_le (mod_cast le_top))]
  have hxp : ∀ i, |x| ^ p * |iteratedDeriv i thetaCuspFullSource x| ≤ p.factorial * C i := by
    intro i
    have h1 : |x| ^ p ≤ p.factorial * Real.exp |x| := by
      have := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) p
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    calc |x| ^ p * |iteratedDeriv i thetaCuspFullSource x|
        ≤ (p.factorial * Real.exp |x|) * (C i * Real.exp (-(1 * |x|))) :=
          mul_le_mul h1 (hC i x) (abs_nonneg _) (by positivity)
      _ = p.factorial * C i := by rw [one_mul, mul_mul_mul_comm, ← Real.exp_add]; simp
  calc |x| ^ p * |∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i thetaCuspFullSource x *
        iteratedDeriv (n - i) (gaussRelative N v u) x|
      ≤ |x| ^ p * ∑ i ∈ Finset.range (n + 1), |(n.choose i : ℝ) * iteratedDeriv i thetaCuspFullSource x *
          iteratedDeriv (n - i) (gaussRelative N v u) x| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (p.factorial * C i) *
          (B i * Real.exp (-(u / 8))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hUi : U i ≤ u := le_trans (le_trans (Finset.le_sup' U hi) (le_max_right _ _)) hu
        rw [abs_mul, abs_mul, Nat.abs_cast]
        calc |x| ^ p * ((n.choose i : ℝ) * |iteratedDeriv i thetaCuspFullSource x| *
              |iteratedDeriv (n - i) (gaussRelative N v u) x|)
            = (n.choose i : ℝ) * (|x| ^ p * |iteratedDeriv i thetaCuspFullSource x|) *
                |iteratedDeriv (n - i) (gaussRelative N v u) x| := by ring
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hxp i) (by positivity)) (hBU i hi' u hUi x)
              (abs_nonneg _) (by have := hC0 i; positivity)
    _ = M * Real.exp (-(u / 8)) := by rw [Finset.sum_mul]; congr 1; ext i; ring
    _ ≤ ε := hU₀ u (le_of_max_le_left hu)

/-- **Relative tail.** `|g_u/k - 1| ≤ C_u (1 + |x|)^{2N+1} e^{-x²/2}`. -/
theorem exists_abs_gaussSurgerySource_div_sub_le (N : ℕ) (v u : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |gaussSurgerySource N v u x / thetaCuspFullSource x - 1| ≤
      C * (1 + |x|) ^ (2 * N + 1) * Real.exp (-(x ^ 2 / 2)) := by
  set T := |gaussAlpha N v u| + |gaussBeta N v u| + ∑ i, |gaussGamma N v u i|
  refine ⟨T * Real.exp (1 / 8), by positivity, fun x => ?_⟩
  have hk := thetaCuspFullSource_pos_all x
  rw [gaussSurgerySource_eq, mul_div_cancel_left₀ _ hk.ne', add_sub_cancel_left]
  have h1x : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hP : (1 + |x|) ^ (2 * N) * Real.exp (|x| / 2) ≤ (1 + |x|) ^ (2 * N + 1) * Real.exp (|x| / 2) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1x (by omega)) (Real.exp_pos _).le
  have hP1 : 1 + |x| ≤ (1 + |x|) ^ (2 * N + 1) * Real.exp (|x| / 2) := by
    have h2 : 1 + |x| ≤ (1 + |x|) ^ (2 * N + 1) := by
      simpa using pow_le_pow_right₀ h1x (by omega : 1 ≤ 2 * N + 1)
    exact h2.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
  set P := (1 + |x|) ^ (2 * N + 1) * Real.exp (|x| / 2)
  have hin : |gaussAlpha N v u * Real.cos (u * x) + gaussBeta N v u * x * Real.sin (u * x) -
      ∑ i, gaussGamma N v u i * evenAnchor N i x| ≤ T * P := by
    have ha : |gaussAlpha N v u * Real.cos (u * x)| ≤ |gaussAlpha N v u| * P := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((Real.abs_cos_le_one _).trans
        (by linarith)) (abs_nonneg _)
    have hb : |gaussBeta N v u * x * Real.sin (u * x)| ≤ |gaussBeta N v u| * P := by
      rw [abs_mul, abs_mul, mul_assoc]
      have hs := Real.abs_sin_le_one (u * x)
      have hxs : |x| * |Real.sin (u * x)| ≤ P := by
        have := abs_nonneg (Real.sin (u * x))
        nlinarith [abs_nonneg x]
      exact mul_le_mul_of_nonneg_left hxs (abs_nonneg _)
    have hg : |∑ i, gaussGamma N v u i * evenAnchor N i x| ≤ (∑ i, |gaussGamma N v u i|) * P := by
      rw [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := norm_anchorC_le N i (z := (x : ℂ)) (by simp)
      rw [anchorC_ofReal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at this
      exact this.trans hP
    have n1 := abs_sub (gaussAlpha N v u * Real.cos (u * x) + gaussBeta N v u * x * Real.sin (u * x))
      (∑ i, gaussGamma N v u i * evenAnchor N i x)
    have n2 := abs_add_le (gaussAlpha N v u * Real.cos (u * x)) (gaussBeta N v u * x * Real.sin (u * x))
    simp only [T]; nlinarith
  have hexp : Real.exp (-x ^ 2) * Real.exp (|x| / 2) ≤ Real.exp (1 / 8) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := sq_abs x
    nlinarith [sq_nonneg (|x| - 1 / 2)]
  rw [gaussRelative, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-x ^ 2) * |gaussAlpha N v u * Real.cos (u * x) + gaussBeta N v u * x * Real.sin (u * x) -
        ∑ i, gaussGamma N v u i * evenAnchor N i x| ≤ Real.exp (-x ^ 2) * (T * P) :=
        mul_le_mul_of_nonneg_left hin (Real.exp_pos _).le
    _ = T * (1 + |x|) ^ (2 * N + 1) * (Real.exp (-x ^ 2) * Real.exp (|x| / 2)) := by
        simp only [P]; ring
    _ ≤ T * (1 + |x|) ^ (2 * N + 1) * (Real.exp (1 / 8) * Real.exp (-(x ^ 2 / 2))) := by gcongr
    _ = T * Real.exp (1 / 8) * (1 + |x|) ^ (2 * N + 1) * Real.exp (-(x ^ 2 / 2)) := by ring

/-- The relative tail error vanishes faster than every exponential `e^{-c|x|}`. -/
theorem exists_abs_gaussSurgerySource_div_sub_le_exp (N : ℕ) (v u c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |gaussSurgerySource N v u x / thetaCuspFullSource x - 1| ≤
      C * Real.exp (-(c * |x|)) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_abs_gaussSurgerySource_div_sub_le N v u
  set m := 2 * N + 1
  refine ⟨C₀ * m.factorial * Real.exp (1 + (1 + |c|) ^ 2 / 2), by positivity, fun x => ?_⟩
  refine (h x).trans ?_
  have h1 : (1 + |x|) ^ m ≤ m.factorial * Real.exp (1 + |x|) := by
    have := Real.pow_div_factorial_le_exp (1 + |x|) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hq : 1 + |x| - x ^ 2 / 2 ≤ 1 + (1 + |c|) ^ 2 / 2 - c * |x| := by
    have := sq_abs x
    nlinarith [sq_nonneg (|x| - (1 + |c|)), le_abs_self c, abs_nonneg x, abs_nonneg c,
      mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg x)]
  calc C₀ * (1 + |x|) ^ m * Real.exp (-(x ^ 2 / 2))
      ≤ C₀ * (m.factorial * Real.exp (1 + |x|)) * Real.exp (-(x ^ 2 / 2)) := by gcongr
    _ = C₀ * m.factorial * Real.exp (1 + |x| - x ^ 2 / 2) := by
        rw [sub_eq_add_neg, Real.exp_add (1 + |x|)]; ring
    _ ≤ C₀ * m.factorial * Real.exp (1 + (1 + |c|) ^ 2 / 2 - c * |x|) := by gcongr
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

/-! ## Positivity and strong log-concavity of the analytic surgery -/

theorem contDiff_gaussRelative (N : ℕ) (v u : ℝ) : ContDiff ℝ ∞ (gaussRelative N v u) := by
  rw [gaussRelative_eq_re]
  exact (Complex.reCLM.contDiff.comp ((((differentiable_gaussRelativeC N v u).contDiff
    (n := ⊤)).restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff)).of_le le_top

/-- **Positivity and strong log-concavity:** for large `u`, `g_u > 0` and `(log g_u)'' ≤ -2`. -/
theorem gaussSurgerySource_pos_logConcave (N : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) :
    ∃ U : ℝ, ∀ u, U ≤ u → (∀ x, 0 < gaussSurgerySource N v u x) ∧
      ∀ x, iteratedDeriv 2 (fun y => Real.log (gaussSurgerySource N v u y)) x ≤ -2 := by
  have hb : ∀ j, ∃ U : ℝ, ∀ u, U ≤ u → ∀ x, |iteratedDeriv j (gaussRelative N v u) x| ≤ 1 / 6 := by
    intro j
    obtain ⟨B, U, hB, h⟩ := exists_bound_iteratedDeriv_gaussRelative N j hv hv2
    have hlim := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 8))).const_mul B
    rw [mul_zero] at hlim
    obtain ⟨U', hU'⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds
      (by norm_num : (0 : ℝ) < 1 / 6)))
    exact ⟨max U U', fun u hu x => (h u (le_of_max_le_left hu) x).trans (hU' u (le_of_max_le_right hu))⟩
  obtain ⟨U₀, h₀⟩ := hb 0
  obtain ⟨U₁, h₁⟩ := hb 1
  obtain ⟨U₂, h₂⟩ := hb 2
  refine ⟨max U₀ (max U₁ U₂), fun u hu => ?_⟩
  have e0 := h₀ u (le_of_max_le_left hu)
  have e1 := h₁ u (le_trans (le_max_left _ _) (le_of_max_le_right hu))
  have e2 := h₂ u (le_trans (le_max_right _ _) (le_of_max_le_right hu))
  set r := gaussRelative N v u
  set sfun : ℝ → ℝ := fun x => 1 + r x
  have hk := contDiff_thetaCuspFullSource
  have hr := contDiff_gaussRelative N v u
  have hs : ContDiff ℝ ∞ sfun := contDiff_const.add hr
  have hg : gaussSurgerySource N v u = thetaCuspFullSource * sfun := by
    funext x; rw [gaussSurgerySource_eq]; rfl
  have hs0 : ∀ x, 5 / 6 ≤ sfun x ∧ sfun x ≤ 7 / 6 := fun x => by
    have := e0 x; simp only [iteratedDeriv_zero] at this
    simp only [sfun]; constructor <;> linarith [(abs_le.mp this).1, (abs_le.mp this).2]
  have hsd : ∀ j, 0 < j → ∀ x, iteratedDeriv j sfun x = iteratedDeriv j r x := fun j hj x =>
    iteratedDeriv_const_add hj 1
  have hpos : ∀ x, 0 < gaussSurgerySource N v u x := fun x => by
    rw [hg]; exact mul_pos (thetaCuspFullSource_pos_all x) (by linarith [(hs0 x).1])
  refine ⟨hpos, fun x => ?_⟩
  have hgc : ContDiff ℝ ∞ (gaussSurgerySource N v u) := by rw [hg]; exact hk.mul hs
  rw [iteratedDeriv_two_log_eq hgc hpos, div_le_iff₀ (by have := hpos x; positivity)]
  have hka := hk.contDiffAt (x := x)
  have hsa := hs.contDiffAt (x := x)
  have d1 : iteratedDeriv 1 (gaussSurgerySource N v u) x =
      thetaCuspFullSource x * iteratedDeriv 1 sfun x + iteratedDeriv 1 thetaCuspFullSource x * sfun x := by
    rw [hg, iteratedDeriv_mul (hka.of_le (mod_cast le_top)) (hsa.of_le (mod_cast le_top))]
    simp [Finset.sum_range_succ]
  have d2 : iteratedDeriv 2 (gaussSurgerySource N v u) x =
      thetaCuspFullSource x * iteratedDeriv 2 sfun x +
        2 * (iteratedDeriv 1 thetaCuspFullSource x * iteratedDeriv 1 sfun x) +
        iteratedDeriv 2 thetaCuspFullSource x * sfun x := by
    rw [hg, iteratedDeriv_mul (hka.of_le (WithTop.coe_le_coe.mpr le_top))
      (hsa.of_le (WithTop.coe_le_coe.mpr le_top))]
    simp [Finset.sum_range_succ]; ring
  rw [d1, d2, hsd 1 one_pos, hsd 2 two_pos, hg]
  simp only [Pi.mul_apply]
  have hN := thetaCuspLogConcavityNumerator_le x
  unfold thetaCuspLogConcavityNumerator at hN
  have f1 := e1 x
  have f2 := e2 x
  obtain ⟨s1, s2⟩ := hs0 x
  rw [abs_le] at f1 f2
  set k0 := thetaCuspFullSource x
  set k1 := iteratedDeriv 1 thetaCuspFullSource x
  set k2 := iteratedDeriv 2 thetaCuspFullSource x
  set r1 := iteratedDeriv 1 r x
  set r2 := iteratedDeriv 2 r x
  set sv := sfun x
  have hk0 : 0 < k0 := thetaCuspFullSource_pos_all x
  have hkey : (k0 * r2 + 2 * (k1 * r1) + k2 * sv) * (k0 * sv) - (k0 * r1 + k1 * sv) ^ 2 =
      sv ^ 2 * (k2 * k0 - k1 ^ 2) + k0 ^ 2 * (sv * r2 - r1 ^ 2) := by ring
  rw [hkey]
  have h1 : sv ^ 2 * (k2 * k0 - k1 ^ 2) ≤ -4 * k0 ^ 2 * sv ^ 2 := by
    have := mul_le_mul_of_nonneg_left hN (sq_nonneg sv)
    nlinarith
  have h2 : sv * r2 - r1 ^ 2 ≤ 7 / 36 := by nlinarith
  have h3 : k0 ^ 2 * (sv * r2 - r1 ^ 2) ≤ k0 ^ 2 * (7 / 36) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg k0)
  have h4 : 25 / 36 * k0 ^ 2 ≤ sv ^ 2 * k0 ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg k0)
  have h5 : (k0 * sv) ^ 2 = k0 ^ 2 * sv ^ 2 := by ring
  nlinarith

/-! ## Holomorphic continuation to the source strip -/

/-- The holomorphic continuation `G_u(z) = k(z) (1 + R_u(z))` on `|Im z| < π/4`. -/
def gaussSurgeryC (N : ℕ) (v u : ℝ) (z : ℂ) : ℂ :=
  thetaCuspStripSource z * (1 + gaussRelativeC N v u z)

theorem gaussSurgeryC_ofReal (N : ℕ) (v u x : ℝ) :
    gaussSurgeryC N v u x = (gaussSurgerySource N v u x : ℂ) := by
  rw [gaussSurgeryC, thetaCuspStripSource_ofReal, gaussRelativeC_ofReal, gaussSurgerySource_eq]
  push_cast; ring

theorem differentiableOn_gaussSurgeryC (N : ℕ) (v u : ℝ) :
    DifferentiableOn ℂ (gaussSurgeryC N v u) thetaCuspStrip :=
  differentiableOn_thetaCuspStripSource.mul
    ((differentiable_gaussRelativeC N v u).const_add 1).differentiableOn

/-- **Real analyticity** of the analytic surgery. -/
theorem analyticAt_gaussSurgerySource (N : ℕ) (v u x : ℝ) :
    AnalyticAt ℝ (gaussSurgerySource N v u) x := by
  have hx : (x : ℂ) ∈ thetaCuspStrip := by
    simp only [thetaCuspStrip, Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]; positivity
  have h := ((differentiableOn_gaussSurgeryC N v u).analyticAt
    (isOpen_thetaCuspStrip.mem_nhds hx)).re_ofReal
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [gaussSurgeryC_ofReal, Complex.ofReal_re]

/-- **Compact-open convergence** of the continuation to the complexified theta source on every
compact subset of the strip `|Im z| < π/4`. -/
theorem tendstoUniformlyOn_gaussSurgeryC (N : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2)
    {K : Set ℂ} (hK : IsCompact K) (hKs : K ⊆ thetaCuspStrip) :
    TendstoUniformlyOn (fun u => gaussSurgeryC N v u) thetaCuspStripSource atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hne (continuous_abs.comp Complex.continuous_im).continuousOn
  set δK := |z₀.im|
  have hδK : δK < Real.pi / 4 := hKs hz₀
  have hδK0 : 0 ≤ δK := abs_nonneg _
  set δ₀ := (δK + Real.pi / 4) / 2
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (differentiableOn_thetaCuspStripSource.continuousOn.mono hKs)
  obtain ⟨Kc, U, hKc, hU⟩ := exists_gauss_coeff_bound N hv hv2 (δ := δ₀) (by positivity)
    (by simp only [δ₀]; linarith)
  have hL : 0 ≤ gaussRelativeConst N := by unfold gaussRelativeConst; positivity
  have hδ1 : δK ≤ 1 := by linarith [Real.pi_lt_four]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun u : ℝ => (|M| * (gaussRelativeConst N * Kc)) *
      Real.exp (-((δ₀ - δK) * u))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by simp only [δ₀]; linarith : (0 : ℝ) < δ₀ - δK))).const_mul
      (|M| * (gaussRelativeConst N * Kc))
    simpa using this
  filter_upwards [eventually_ge_atTop (max U 0), hlim.eventually (gt_mem_nhds hε)] with u hu hlt z hz
  have hu0 : 0 ≤ u := le_of_max_le_right hu
  have hz1 : |z.im| ≤ δK := hmax hz
  rw [dist_eq_norm, gaussSurgeryC, show thetaCuspStripSource z - thetaCuspStripSource z *
    (1 + gaussRelativeC N v u z) = -(thetaCuspStripSource z * gaussRelativeC N v u z) by ring,
    norm_neg, norm_mul]
  have hR := norm_gaussRelativeC_le N v hu0 hδ1 hz1
  have hc := (hU u (le_of_max_le_left hu)).2
  have e1 : Real.exp (-(δ₀ * u)) * Real.exp (u * δK) = Real.exp (-((δ₀ - δK) * u)) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖thetaCuspStripSource z‖ * ‖gaussRelativeC N v u z‖
      ≤ |M| * (gaussRelativeConst N * (Kc * Real.exp (-(δ₀ * u))) * Real.exp (u * δK)) := by
        refine mul_le_mul ((hM z hz).trans (le_abs_self M)) (hR.trans ?_) (norm_nonneg _)
          (abs_nonneg _)
        gcongr
    _ = |M| * (gaussRelativeConst N * Kc) * Real.exp (-((δ₀ - δK) * u)) := by rw [← e1]; ring
    _ < ε := hlt

/-! ## The real-analytic theorem -/

/-- **Real-analytic theta zero surgery.** For `0 < v < 1/2` and moment depth `J`, for all large
`u` the source `g_u = k(1 + r_u)`, `r_u = e^{-x²}(α cos(ux) + β x sin(ux) - Σ γ_i A_i)`, is even,
real analytic, positive and strongly log-concave, has the moments of `k` through order `J` and the
critical charge `1/2`, and has the forced strip zero `F_{g_u}(u + iv) = 0`. -/
theorem analytic_critical_strip_zero_engineering (J : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) :
    ∃ U : ℝ, ∀ u, U ≤ u →
      (∀ x, gaussSurgerySource (J / 2) v u (-x) = gaussSurgerySource (J / 2) v u x) ∧
      (∀ x, AnalyticAt ℝ (gaussSurgerySource (J / 2) v u) x) ∧
      (∀ x, 0 < gaussSurgerySource (J / 2) v u x) ∧
      (∀ x, iteratedDeriv 2 (fun y => Real.log (gaussSurgerySource (J / 2) v u y)) x ≤ -2) ∧
      (∀ j ≤ J, ∫ x, x ^ j * gaussSurgerySource (J / 2) v u x =
        ∫ x, x ^ j * thetaCuspFullSource x) ∧
      ∫ x, Real.exp (x / 2) * gaussSurgerySource (J / 2) v u x = 1 / 2 ∧
      stripEval v u (gaussSurgerySource (J / 2) v u) = 0 := by
  obtain ⟨U₁, h₁⟩ := gaussSurgerySource_pos_logConcave (J / 2) hv hv2
  obtain ⟨K, U₂, -, h₂⟩ := exists_gaussSolve (J / 2) hv hv2 (δ := 0) le_rfl (by positivity)
  refine ⟨max U₁ U₂, fun u hu => ⟨gaussSurgerySource_neg _ v u,
    fun x => analyticAt_gaussSurgerySource _ v u x, (h₁ u (le_of_max_le_left hu)).1,
    (h₁ u (le_of_max_le_left hu)).2,
    fun j hj => integral_pow_mul_gaussSurgerySource _ v u (by omega),
    integral_exp_half_mul_gaussSurgerySource _ v u,
    stripEval_gaussSurgerySource_eq_zero (h₂ u (le_of_max_le_right hu)).1⟩⟩

/-! ## Both surgered sources have entire Fourier transforms -/

theorem expMomentSource_of_le_thetaSource {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    {h : ℝ → ℝ} (hh : Continuous h) (hs : ∀ x, 2 ≤ |x| → h x = 0)
    (hb : ∀ x, |g x| ≤ C * thetaCuspFullSource x + |h x|) :
    ExpMomentSource fun x => (g x : ℂ) where
  continuous := by fun_prop
  moment c := by
    have hk := (expMomentSource_thetaSourceC.moment c).const_mul C
    have hh' : Integrable fun x => Real.exp (c * |x|) * |h x| :=
      integrable_of_eq_zero (by fun_prop) fun x hx => by simp [hs x hx]
    refine (hk.add hh').mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_pos (Real.exp_pos _)]
    have := hb x
    have hk0 := thetaCuspFullSource_pos_all x
    simp only [Pi.add_apply, thetaSourceC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]
    nlinarith [Real.exp_pos (c * |x|)]

/-- The compact surgery has an entire Fourier transform, vanishing at `u + iv`. -/
theorem differentiable_sourceTransform_compactSurgerySource (N : ℕ) (v u : ℝ) :
    Differentiable ℂ (sourceTransform fun x => (compactSurgerySource N v u x : ℂ)) :=
  (expMomentSource_of_le_thetaSource (by
      have := contDiff_thetaCuspFullSource.continuous
      exact this.add (continuous_compactPerturbation N v u)) (C := 1)
    (continuous_compactPerturbation N v u) (fun x hx => compactPerturbation_eq_zero hx)
    (fun x => by
      have := thetaCuspFullSource_pos_all x
      simp only [compactSurgerySource, one_mul]
      exact (abs_add_le _ _).trans (by rw [abs_of_pos this]))).differentiable_sourceTransform

theorem sourceTransform_eq_stripEval (g : ℝ → ℝ) (v u : ℝ) :
    sourceTransform (fun x => (g x : ℂ)) ((u : ℂ) + v * I) = stripEval v u g := rfl

theorem expMomentSource_gaussSurgerySource (N : ℕ) (v u : ℝ) :
    ExpMomentSource fun x => (gaussSurgerySource N v u x : ℂ) := by
  obtain ⟨C, hC, hrel⟩ := exists_abs_gaussSurgerySource_div_sub_le_exp N v u 0
  refine expMomentSource_of_le_thetaSource (C := 1 + C) (h := fun _ => 0)
    ((contDiff_thetaCuspFullSource.continuous).add
      ((continuous_const.mul (continuous_gaussCosDirection N u)).add
        (continuous_const.mul (continuous_gaussSinDirection N u))))
    continuous_const (fun _ _ => rfl) fun x => ?_
  have hk := thetaCuspFullSource_pos_all x
  have h1 := hrel x
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h1
  rw [div_sub_one hk.ne', abs_div, abs_of_pos hk, div_le_iff₀ hk] at h1
  have := abs_sub_abs_le_abs_sub (gaussSurgerySource N v u x) (thetaCuspFullSource x)
  rw [abs_of_pos hk] at this
  simp only [abs_zero, add_zero]
  nlinarith

/-- The analytic surgery has an entire Fourier transform, vanishing at `u + iv`. -/
theorem differentiable_sourceTransform_gaussSurgerySource (N : ℕ) (v u : ℝ) :
    Differentiable ℂ (sourceTransform fun x => (gaussSurgerySource N v u x : ℂ)) :=
  (expMomentSource_gaussSurgerySource N v u).differentiable_sourceTransform

end

end RHTower
