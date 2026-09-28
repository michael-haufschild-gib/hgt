import GaloisForLFunctions.RHTower.ThetaSourceSurgeryToolkit
import GaloisForLFunctions.HTGeometry.OscillatoryPacketFourier

/-!
# Compact theta surgery forcing a zero inside the Xi strip

Fix `0 < v < 1/2` and a moment depth `J`, `N = J/2`. With an even bump `ψ` (`1` on `[-1, 1]`,
supported in `[-2, 2]`) and the projection `Π` off the even anchors `1, …, x^{2N}, cosh(x/2)`, the
two directions `Π(ψ cos(u·))` and `Π(x ψ sin(u·))` have evaluations at `u + iv` tending to
`½ ∫ e^{vx} ψ > 0` and `-(i/2) ∫ x e^{vx} ψ ∈ iℝ \ {0}`. Solving one complex equation in two real
coefficients cancels `Ξ(u + iv)`: the source `g_u = k + α Π(ψ cos(u·)) + β Π(x ψ sin(u·))` has a
zero of its Fourier transform at `u + iv`, agrees with `k` outside `[-2, 2]`, keeps all moments
through order `J` and the critical charge `∫ e^{x/2} g_u = 1/2`, converges to `k` in every Schwartz
seminorm, stays positive and strongly log-concave, and keeps every finite literal prime deletion
positive on the right ray, uniformly in the prime set.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ContDiff

namespace RHTower

noncomputable section



/-! ## Uniform log-concavity of the theta source -/

/-! ## Smooth compactly supported profiles -/

/-! ## The compact weight -/

/-- The fixed even bump: `1` on `[-1, 1]`, supported in `[-2, 2]`. -/
def compactBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The compact weight `ψ`. -/
def compactWeight (x : ℝ) : ℝ := compactBump x

theorem contDiff_compactWeight : ContDiff ℝ ∞ compactWeight := compactBump.contDiff

theorem compactWeight_nonneg (x : ℝ) : 0 ≤ compactWeight x := compactBump.nonneg

theorem compactWeight_le_one (x : ℝ) : compactWeight x ≤ 1 := compactBump.le_one

theorem compactWeight_neg (x : ℝ) : compactWeight (-x) = compactWeight x := compactBump.neg x

theorem compactWeight_eq_one {x : ℝ} (hx : |x| ≤ 1) : compactWeight x = 1 :=
  compactBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

theorem compactWeight_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : compactWeight x = 0 := by
  have : x ∉ Function.support compactWeight := by
    rw [show compactWeight = (compactBump : ℝ → ℝ) from rfl, compactBump.support_eq,
      Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact hx
  simpa [Function.mem_support] using this

theorem hasCompactSupport_compactWeight : HasCompactSupport compactWeight :=
  compactBump.hasCompactSupport

theorem compactWeight_anchorWeight (N : ℕ) : AnchorWeight N compactWeight where
  continuous := contDiff_compactWeight.continuous
  nonneg := compactWeight_nonneg
  pos := ⟨1, one_pos, fun x hx => by
    rw [compactWeight_eq_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)]; exact one_pos⟩
  integrable i j := by
    refine Continuous.integrable_of_hasCompactSupport (by
      have := continuous_evenAnchor N i; have := continuous_evenAnchor N j
      have := contDiff_compactWeight.continuous; fun_prop) ?_
    exact (hasCompactSupport_compactWeight.mul_right).mul_right

/-! ## The oscillatory packets and their anchor projections -/

/-- The cosine packet `ψ(x) cos(ux)`. -/
def compactCosPacket (u x : ℝ) : ℝ := compactWeight x * Real.cos (u * x)

/-- The sine packet `x ψ(x) sin(ux)`. -/
def compactSinPacket (u x : ℝ) : ℝ := x * compactWeight x * Real.sin (u * x)

/-- The anchor-free cosine direction `Π(ψ cos(u·))`. -/
def compactCosDirection (N : ℕ) (u : ℝ) : ℝ → ℝ := anchorProj N compactWeight (compactCosPacket u)

/-- The anchor-free sine direction `Π(x ψ sin(u·))`. -/
def compactSinDirection (N : ℕ) (u : ℝ) : ℝ → ℝ := anchorProj N compactWeight (compactSinPacket u)

theorem compactCosPacket_eq_zero {u x : ℝ} (hx : 2 ≤ |x|) : compactCosPacket u x = 0 := by
  simp [compactCosPacket, compactWeight_eq_zero hx]

theorem compactSinPacket_eq_zero {u x : ℝ} (hx : 2 ≤ |x|) : compactSinPacket u x = 0 := by
  simp [compactSinPacket, compactWeight_eq_zero hx]

theorem anchorProj_compactWeight_eq_zero {N : ℕ} {b : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ |x|)
    (hb : b x = 0) : anchorProj N compactWeight b x = 0 := by
  simp [anchorProj, hb, compactWeight_eq_zero hx]

theorem compactCosDirection_eq_zero {N : ℕ} {u x : ℝ} (hx : 2 ≤ |x|) :
    compactCosDirection N u x = 0 :=
  anchorProj_compactWeight_eq_zero hx (compactCosPacket_eq_zero hx)

theorem compactSinDirection_eq_zero {N : ℕ} {u x : ℝ} (hx : 2 ≤ |x|) :
    compactSinDirection N u x = 0 :=
  anchorProj_compactWeight_eq_zero hx (compactSinPacket_eq_zero hx)

theorem compactCosPacket_neg (u x : ℝ) : compactCosPacket u (-x) = compactCosPacket u x := by
  simp [compactCosPacket, compactWeight_neg, mul_neg, Real.cos_neg]

theorem compactSinPacket_neg (u x : ℝ) : compactSinPacket u (-x) = compactSinPacket u x := by
  simp only [compactSinPacket, compactWeight_neg, mul_neg, Real.sin_neg]; ring

theorem compactCosDirection_neg (N : ℕ) (u x : ℝ) :
    compactCosDirection N u (-x) = compactCosDirection N u x :=
  anchorProj_neg compactWeight_neg (compactCosPacket_neg u) x

theorem compactSinDirection_neg (N : ℕ) (u x : ℝ) :
    compactSinDirection N u (-x) = compactSinDirection N u x :=
  anchorProj_neg compactWeight_neg (compactSinPacket_neg u) x

theorem contDiff_compactCosPacket (u : ℝ) : ContDiff ℝ ∞ (compactCosPacket u) := by
  have := contDiff_compactWeight; unfold compactCosPacket; fun_prop

theorem contDiff_compactSinPacket (u : ℝ) : ContDiff ℝ ∞ (compactSinPacket u) := by
  have := contDiff_compactWeight; unfold compactSinPacket; fun_prop

theorem contDiff_anchorProj {N : ℕ} {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (anchorProj N compactWeight b) := by
  have := contDiff_compactWeight
  have hA := contDiff_evenAnchor N
  unfold anchorProj
  exact hb.sub (ContDiff.sum fun i _ => contDiff_const.mul (this.mul (hA i)))

theorem continuous_compactCosDirection (N : ℕ) (u : ℝ) : Continuous (compactCosDirection N u) :=
  (contDiff_anchorProj (contDiff_compactCosPacket u)).continuous

theorem continuous_compactSinDirection (N : ℕ) (u : ℝ) : Continuous (compactSinDirection N u) :=
  (contDiff_anchorProj (contDiff_compactSinPacket u)).continuous

/-- A continuous function vanishing for `|x| ≥ 2` has compact support. -/
theorem hasCompactSupport_of_eq_zero {f : ℝ → ℝ} (hf : ∀ x, 2 ≤ |x| → f x = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun x hx => hf x ?_
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_of_eq_zero {f : ℝ → ℝ} (hc : Continuous f) (hf : ∀ x, 2 ≤ |x| → f x = 0) :
    Integrable f :=
  hc.integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero hf)

/-! ## Evaluation on the horizontal line `Im z = v` -/

theorem integrable_stripEval_integrand {v u : ℝ} {b : ℝ → ℝ} (hb : Continuous b)
    (hs : ∀ x, 2 ≤ |x| → b x = 0) :
    Integrable fun x : ℝ => cexp (-I * ((u : ℂ) + v * I) * x) * (b x : ℂ) := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact (hasCompactSupport_of_eq_zero hs).comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    |>.mul_left

theorem weightAnchor_eq_zero {N : ℕ} (i : Fin (N + 2)) {x : ℝ} (hx : 2 ≤ |x|) :
    compactWeight x * evenAnchor N i x = 0 := by simp [compactWeight_eq_zero hx]

theorem continuous_weightAnchor (N : ℕ) (i : Fin (N + 2)) :
    Continuous fun x => compactWeight x * evenAnchor N i x :=
  contDiff_compactWeight.continuous.mul (continuous_evenAnchor N i)

/-- `E_u(Π b) = E_u(b) - Σ c_i(b) E_u(ψ A_i)`. -/
theorem stripEval_anchorProj {N : ℕ} {v u : ℝ} {b : ℝ → ℝ} (hb : Continuous b)
    (hs : ∀ x, 2 ≤ |x| → b x = 0) :
    stripEval v u (anchorProj N compactWeight b) = stripEval v u b -
      ∑ i, (anchorCoef N compactWeight b i : ℂ) *
        stripEval v u fun x => compactWeight x * evenAnchor N i x := by
  have hi : ∀ i : Fin (N + 2), Integrable fun x : ℝ => (anchorCoef N compactWeight b i : ℂ) *
      (cexp (-I * ((u : ℂ) + v * I) * x) * ((compactWeight x * evenAnchor N i x : ℝ) : ℂ)) :=
    fun i => (integrable_stripEval_integrand (continuous_weightAnchor N i)
      fun x hx => weightAnchor_eq_zero i hx).const_mul _
  simp only [stripEval]
  have hsum : ∑ i, (anchorCoef N compactWeight b i : ℂ) *
      (∫ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) * ((compactWeight x * evenAnchor N i x : ℝ) : ℂ)) =
      ∫ x : ℝ, ∑ i, (anchorCoef N compactWeight b i : ℂ) *
        (cexp (-I * ((u : ℂ) + v * I) * x) * ((compactWeight x * evenAnchor N i x : ℝ) : ℂ)) := by
    rw [integral_finsetSum _ fun i _ => hi i]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  rw [hsum, ← integral_sub (integrable_stripEval_integrand hb hs)
    (integrable_finsetSum _ fun i _ => hi i)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [anchorProj]
  push_cast
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem tendsto_anchorMoments_cos (N : ℕ) (j : Fin (N + 2)) :
    Tendsto (fun u => anchorMoments N (compactCosPacket u) j) atTop (𝓝 0) := by
  have hw : Integrable fun x => evenAnchor N j x * compactWeight x :=
    integrable_of_eq_zero ((continuous_evenAnchor N j).mul contDiff_compactWeight.continuous)
      fun x hx => by simp [compactWeight_eq_zero hx]
  refine (tendsto_integral_mul_cos hw).congr fun u => ?_
  simp only [anchorMoments, compactCosPacket]
  congr 1; ext x; ring

theorem tendsto_anchorMoments_sin (N : ℕ) (j : Fin (N + 2)) :
    Tendsto (fun u => anchorMoments N (compactSinPacket u) j) atTop (𝓝 0) := by
  have hw : Integrable fun x => evenAnchor N j x * (x * compactWeight x) :=
    integrable_of_eq_zero ((continuous_evenAnchor N j).mul
      (continuous_id.mul contDiff_compactWeight.continuous))
      fun x hx => by simp [compactWeight_eq_zero hx]
  refine (tendsto_integral_mul_sin hw).congr fun u => ?_
  simp only [anchorMoments, compactSinPacket]
  congr 1; ext x; ring

theorem continuous_compactCosPacket (u : ℝ) : Continuous (compactCosPacket u) :=
  (contDiff_compactCosPacket u).continuous

theorem continuous_compactSinPacket (u : ℝ) : Continuous (compactSinPacket u) :=
  (contDiff_compactSinPacket u).continuous

theorem tendsto_correction (N : ℕ) (v : ℝ) {b : ℝ → ℝ → ℝ}
    (hb : ∀ j, Tendsto (fun u => anchorMoments N (b u) j) atTop (𝓝 0)) :
    Tendsto (fun u => ∑ i, (anchorCoef N compactWeight (b u) i : ℂ) *
      stripEval v u fun x => compactWeight x * evenAnchor N i x) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin (N + 2))) fun i _ =>
    ((Complex.continuous_ofReal.tendsto 0).comp (tendsto_anchorCoef (ψ := compactWeight) hb i)).mul
      (tendsto_packet_fixed v (φ := fun x => compactWeight x * evenAnchor N i x))
  simp only [Function.comp_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero] at h
  exact h

/-- The cosine weight `A₀ = ∫ e^{vx} ψ > 0`. -/
theorem integral_exp_mul_compactWeight_pos (v : ℝ) :
    0 < ∫ x, Real.exp (v * x) * compactWeight x := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (by have := contDiff_compactWeight.continuous; fun_prop)
    (hasCompactSupport_compactWeight.mul_left) (fun x => mul_nonneg (Real.exp_pos _).le
      (compactWeight_nonneg x)) ?_
  rw [compactWeight_eq_one (by simp)]; simp

/-- The sine weight `B₀ = ∫ x e^{vx} ψ = ∫ x sinh(vx) ψ > 0` for `v > 0`. -/
theorem integral_exp_mul_id_mul_compactWeight_pos {v : ℝ} (hv : 0 < v) :
    0 < ∫ x, Real.exp (v * x) * (x * compactWeight x) := by
  have hi : Integrable fun x => Real.exp (v * x) * (x * compactWeight x) :=
    integrable_of_eq_zero (by have := contDiff_compactWeight.continuous; fun_prop)
      fun x hx => by simp [compactWeight_eq_zero hx]
  have hsym : ∫ x, Real.exp (v * x) * (x * compactWeight x) =
      ∫ x, Real.exp (v * -x) * (-x * compactWeight (-x)) :=
    (integral_neg_eq_self (fun x => Real.exp (v * x) * (x * compactWeight x)) volume).symm
  have heq : ∫ x, Real.exp (v * x) * (x * compactWeight x) =
      ∫ x, x * Real.sinh (v * x) * compactWeight x := by
    have h2 : 2 * ∫ x, Real.exp (v * x) * (x * compactWeight x) =
        ∫ x, 2 * (x * Real.sinh (v * x) * compactWeight x) := by
      rw [two_mul]
      nth_rewrite 2 [hsym]
      rw [← integral_add hi (by
        have := hi.comp_neg; simpa using this)]
      congr 1; ext x
      rw [compactWeight_neg, Real.sinh_eq]
      ring_nf
    rw [integral_const_mul] at h2
    linarith
  rw [heq]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1 / 2)
    (by have := contDiff_compactWeight.continuous; fun_prop)
    (hasCompactSupport_compactWeight.mul_left) (fun x => ?_) ?_
  · refine mul_nonneg ?_ (compactWeight_nonneg x)
    rcases le_total 0 x with h | h
    · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr (by positivity))
    · exact mul_nonneg_of_nonpos_of_nonpos h (Real.sinh_nonpos_iff.mpr (by nlinarith))
  · rw [compactWeight_eq_one (by rw [abs_of_pos (by norm_num)]; norm_num)]
    have : 0 < Real.sinh (v * (1 / 2)) := Real.sinh_pos_iff.mpr (by positivity)
    positivity

/-- **The cosine direction.** `E_u(Π(ψ cos(u·))) → ½ A₀`. -/
theorem tendsto_stripEval_compactCosDirection (N : ℕ) (v : ℝ) :
    Tendsto (fun u => stripEval v u (compactCosDirection N u)) atTop
      (𝓝 ((1 / 2 : ℂ) * ((∫ x, Real.exp (v * x) * compactWeight x : ℝ) : ℂ))) := by
  have hmain := tendsto_packet_cos v (φ := compactWeight)
    (integrable_of_eq_zero (by have := contDiff_compactWeight.continuous; fun_prop)
      fun x hx => by simp [compactWeight_eq_zero hx])
  have hcorr := tendsto_correction N v (tendsto_anchorMoments_cos N)
  have h := hmain.sub hcorr
  rw [sub_zero] at h
  refine h.congr fun u => ?_
  rw [compactCosDirection, stripEval_anchorProj (continuous_compactCosPacket u)
    fun x hx => compactCosPacket_eq_zero hx]
  rfl

/-- **The sine direction.** `E_u(Π(x ψ sin(u·))) → -(i/2) B₀`. -/
theorem tendsto_stripEval_compactSinDirection (N : ℕ) (v : ℝ) :
    Tendsto (fun u => stripEval v u (compactSinDirection N u)) atTop
      (𝓝 ((-I / 2) * ((∫ x, Real.exp (v * x) * (x * compactWeight x) : ℝ) : ℂ))) := by
  have hmain := tendsto_packet_sin v (φ := fun x => x * compactWeight x)
    (integrable_of_eq_zero (by have := contDiff_compactWeight.continuous; fun_prop)
      fun x hx => by simp [compactWeight_eq_zero hx])
  have hcorr := tendsto_correction N v (tendsto_anchorMoments_sin N)
  have h := hmain.sub hcorr
  rw [sub_zero] at h
  refine h.congr fun u => ?_
  rw [compactSinDirection, stripEval_anchorProj (continuous_compactSinPacket u)
    fun x hx => compactSinPacket_eq_zero hx]
  rfl

/-! ## The two-packet solve -/

/-- The cosine evaluation `E₁(u)`. -/
def compactCosEval (N : ℕ) (v u : ℝ) : ℂ := stripEval v u (compactCosDirection N u)

/-- The sine evaluation `E₂(u)`. -/
def compactSinEval (N : ℕ) (v u : ℝ) : ℂ := stripEval v u (compactSinDirection N u)

/-- The real coefficient of the cosine direction solving `α E₁ + β E₂ = -Ξ(u + iv)`. -/
def compactAlpha (N : ℕ) (v u : ℝ) : ℝ :=
  -(conj (compactSinEval N v u) * -XiC ((u : ℂ) + v * I)).im /
    (conj (compactCosEval N v u) * compactSinEval N v u).im

/-- The real coefficient of the sine direction. -/
def compactBeta (N : ℕ) (v u : ℝ) : ℝ :=
  (conj (compactCosEval N v u) * -XiC ((u : ℂ) + v * I)).im /
    (conj (compactCosEval N v u) * compactSinEval N v u).im

/-- The perturbation `α Π(ψ cos(u·)) + β Π(x ψ sin(u·))`. -/
def compactPerturbation (N : ℕ) (v u x : ℝ) : ℝ :=
  compactAlpha N v u * compactCosDirection N u x + compactBeta N v u * compactSinDirection N u x

/-- **The compact surgery** `g_u = k + α Π(ψ cos(u·)) + β Π(x ψ sin(u·))`. -/
def compactSurgerySource (N : ℕ) (v u x : ℝ) : ℝ :=
  thetaCuspFullSource x + compactPerturbation N v u x

/-- Uniform solvability: for large `u` the real system is nondegenerate and
`|α| + |β| ≤ K ‖Ξ(u + iv)‖`. -/
theorem exists_compactSolve (N : ℕ) {v : ℝ} (hv : 0 < v) :
    ∃ K U : ℝ, 0 ≤ K ∧ ∀ u, U ≤ u →
      (conj (compactCosEval N v u) * compactSinEval N v u).im ≠ 0 ∧
      |compactAlpha N v u| + |compactBeta N v u| ≤ K * ‖XiC ((u : ℂ) + v * I)‖ := by
  set A₀ := ∫ x, Real.exp (v * x) * compactWeight x
  set B₀ := ∫ x, Real.exp (v * x) * (x * compactWeight x)
  have hA := integral_exp_mul_compactWeight_pos v
  have hB := integral_exp_mul_id_mul_compactWeight_pos hv
  have hdeg : (conj ((1 / 2 : ℂ) * (A₀ : ℂ)) * ((-I / 2) * (B₀ : ℂ))).im ≠ 0 := by
    have : (conj ((1 / 2 : ℂ) * (A₀ : ℂ)) * ((-I / 2) * (B₀ : ℂ))).im = -(A₀ * B₀) / 4 := by
      simp [Complex.mul_im, Complex.mul_re]; ring
    rw [this]; exact div_ne_zero (neg_ne_zero.mpr (mul_pos hA hB).ne') (by norm_num)
  obtain ⟨K, U, hK, hU⟩ := exists_real_solve_bound (tendsto_stripEval_compactCosDirection N v)
    (tendsto_stripEval_compactSinDirection N v) hdeg
  refine ⟨K, U, hK, fun u hu => ⟨(hU u hu).1, ?_⟩⟩
  have h := (hU u hu).2 (-XiC ((u : ℂ) + v * I))
  rw [norm_neg] at h
  rw [compactAlpha, compactBeta, neg_div, abs_neg]
  exact h

theorem compactSurgery_combination {N : ℕ} {v u : ℝ}
    (hD : (conj (compactCosEval N v u) * compactSinEval N v u).im ≠ 0) :
    (compactAlpha N v u : ℂ) * compactCosEval N v u + (compactBeta N v u : ℂ) * compactSinEval N v u =
      -XiC ((u : ℂ) + v * I) :=
  real_combination_eq hD

theorem compactPerturbation_eq_zero {N : ℕ} {v u x : ℝ} (hx : 2 ≤ |x|) :
    compactPerturbation N v u x = 0 := by
  simp [compactPerturbation, compactCosDirection_eq_zero hx, compactSinDirection_eq_zero hx]

theorem contDiff_compactPerturbation (N : ℕ) (v u : ℝ) : ContDiff ℝ ∞ (compactPerturbation N v u) :=
  (contDiff_const.mul (contDiff_anchorProj (contDiff_compactCosPacket u))).add
    (contDiff_const.mul (contDiff_anchorProj (contDiff_compactSinPacket u)))

theorem continuous_compactPerturbation (N : ℕ) (v u : ℝ) :
    Continuous (compactPerturbation N v u) := (contDiff_compactPerturbation N v u).continuous

theorem compactPerturbation_neg (N : ℕ) (v u x : ℝ) :
    compactPerturbation N v u (-x) = compactPerturbation N v u x := by
  simp [compactPerturbation, compactCosDirection_neg, compactSinDirection_neg]

/-- **Claim 1.** `g_u = k` outside the fixed interval `[-2, 2]`. -/
theorem compactSurgerySource_eq_of_two_le_abs (N : ℕ) (v u : ℝ) {x : ℝ} (hx : 2 ≤ |x|) :
    compactSurgerySource N v u x = thetaCuspFullSource x := by
  rw [compactSurgerySource, compactPerturbation_eq_zero hx, add_zero]

theorem compactSurgerySource_neg (N : ℕ) (v u x : ℝ) :
    compactSurgerySource N v u (-x) = compactSurgerySource N v u x := by
  rw [compactSurgerySource, compactSurgerySource, thetaCuspFullSource_neg, compactPerturbation_neg]

theorem stripEval_compactPerturbation (N : ℕ) (v u : ℝ) :
    stripEval v u (compactPerturbation N v u) =
      (compactAlpha N v u : ℂ) * compactCosEval N v u +
        (compactBeta N v u : ℂ) * compactSinEval N v u := by
  have h1 := (integrable_stripEval_integrand (v := v) (u := u) (continuous_compactCosDirection N u)
    fun x hx => compactCosDirection_eq_zero hx).const_mul (compactAlpha N v u : ℂ)
  have h2 := (integrable_stripEval_integrand (v := v) (u := u) (continuous_compactSinDirection N u)
    fun x hx => compactSinDirection_eq_zero hx).const_mul (compactBeta N v u : ℂ)
  simp only [stripEval, compactCosEval, compactSinEval]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [compactPerturbation]
  push_cast; ring

/-- **Claim 4.** The forced strip zero `F_{g_u}(u + iv) = 0`. -/
theorem stripEval_compactSurgerySource_eq_zero {N : ℕ} {v u : ℝ}
    (hD : (conj (compactCosEval N v u) * compactSinEval N v u).im ≠ 0) :
    stripEval v u (compactSurgerySource N v u) = 0 := by
  have hp := integrable_stripEval_integrand (v := v) (u := u) (continuous_compactPerturbation N v u)
    fun x hx => compactPerturbation_eq_zero hx
  have hsplit : stripEval v u (compactSurgerySource N v u) =
      stripEval v u thetaCuspFullSource + stripEval v u (compactPerturbation N v u) := by
    simp only [stripEval]
    rw [← integral_add (integrable_stripEval_thetaCuspFullSource v u) hp]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [compactSurgerySource]; push_cast; ring
  rw [hsplit, stripEval_thetaCuspFullSource, stripEval_compactPerturbation,
    compactSurgery_combination hD, add_neg_cancel]

/-! ## Exact anchors -/

theorem integrable_evenAnchor_mul_of_eq_zero {N : ℕ} (j : Fin (N + 2)) {b : ℝ → ℝ}
    (hb : Continuous b) (hs : ∀ x, 2 ≤ |x| → b x = 0) :
    Integrable fun x => evenAnchor N j x * b x :=
  integrable_of_eq_zero ((continuous_evenAnchor N j).mul hb) fun x hx => by simp [hs x hx]

theorem integral_evenAnchor_mul_compactPerturbation (N : ℕ) (v u : ℝ) (j : Fin (N + 2)) :
    ∫ x, evenAnchor N j x * compactPerturbation N v u x = 0 := by
  have hc := integral_evenAnchor_mul_anchorProj (compactWeight_anchorWeight N)
    (fun j => integrable_evenAnchor_mul_of_eq_zero j (continuous_compactCosPacket u)
      fun x hx => compactCosPacket_eq_zero hx) j
  have hs := integral_evenAnchor_mul_anchorProj (compactWeight_anchorWeight N)
    (fun j => integrable_evenAnchor_mul_of_eq_zero j (continuous_compactSinPacket u)
      fun x hx => compactSinPacket_eq_zero hx) j
  have i1 := (integrable_evenAnchor_mul_of_eq_zero j (continuous_compactCosDirection N u)
    fun x hx => compactCosDirection_eq_zero hx).const_mul (compactAlpha N v u)
  have i2 := (integrable_evenAnchor_mul_of_eq_zero j (continuous_compactSinDirection N u)
    fun x hx => compactSinDirection_eq_zero hx).const_mul (compactBeta N v u)
  have heq : (fun x => evenAnchor N j x * compactPerturbation N v u x) = fun x =>
      compactAlpha N v u * (evenAnchor N j x * compactCosDirection N u x) +
        compactBeta N v u * (evenAnchor N j x * compactSinDirection N u x) := by
    funext x; simp only [compactPerturbation]; ring
  rw [heq, integral_add i1 i2, integral_const_mul, integral_const_mul]
  simp only [compactCosDirection, compactSinDirection] at *
  rw [hc, hs]; ring

/-- **Claim 2 (moments).** `∫ x^j g_u = ∫ x^j k` for every `j ≤ 2N + 1`. -/
theorem integral_pow_mul_compactSurgerySource (N : ℕ) (v u : ℝ) {j : ℕ} (hj : j ≤ 2 * N + 1) :
    ∫ x, x ^ j * compactSurgerySource N v u x = ∫ x, x ^ j * thetaCuspFullSource x := by
  have hp : Integrable fun x => x ^ j * compactPerturbation N v u x :=
    integrable_of_eq_zero ((continuous_pow j).mul (continuous_compactPerturbation N v u))
      fun x hx => by simp [compactPerturbation_eq_zero hx]
  have hzero : ∫ x, x ^ j * compactPerturbation N v u x = 0 := by
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | hodd
    · have hi : i < N + 1 := by omega
      have h := integral_evenAnchor_mul_compactPerturbation N v u (Fin.castSucc ⟨i, hi⟩)
      simp only [evenAnchor_castSucc] at h
      rw [← h]; congr 1; ext x; ring_nf
    · exact integral_odd_real_eq_zero fun x => by
        rw [compactPerturbation_neg, hodd.neg_pow]; ring
  have hsplit : (fun x => x ^ j * compactSurgerySource N v u x) =
      fun x => x ^ j * thetaCuspFullSource x + x ^ j * compactPerturbation N v u x := by
    funext x; simp only [compactSurgerySource]; ring
  rw [hsplit, integral_add (integrable_pow_mul_thetaCuspFullSource j) hp, hzero, add_zero]

/-- **Claim 2 (critical charge).** `∫ e^{x/2} g_u = ∫ e^{x/2} k = 1/2`. -/
theorem integral_exp_half_mul_compactSurgerySource (N : ℕ) (v u : ℝ) :
    ∫ x, Real.exp (x / 2) * compactSurgerySource N v u x = 1 / 2 := by
  have hk : Integrable fun x => Real.exp (x / 2) * thetaCuspFullSource x := by
    have := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource (1 / 2)
    simpa [div_eq_inv_mul, mul_comm] using this
  have hp : Integrable fun x => Real.exp (x / 2) * compactPerturbation N v u x :=
    integrable_of_eq_zero (by have := continuous_compactPerturbation N v u; fun_prop)
      fun x hx => by simp [compactPerturbation_eq_zero hx]
  have hcosh := integral_evenAnchor_mul_compactPerturbation N v u (Fin.last (N + 1))
  simp only [evenAnchor_last] at hcosh
  have hsinh : ∫ x, Real.sinh (x / 2) * compactPerturbation N v u x = 0 :=
    integral_odd_real_eq_zero fun x => by
      rw [compactPerturbation_neg, neg_div, Real.sinh_neg]; ring
  have hic : Integrable fun x => Real.cosh (x / 2) * compactPerturbation N v u x :=
    integrable_of_eq_zero (by have := continuous_compactPerturbation N v u; fun_prop)
      fun x hx => by simp [compactPerturbation_eq_zero hx]
  have his : Integrable fun x => Real.sinh (x / 2) * compactPerturbation N v u x :=
    integrable_of_eq_zero (by have := continuous_compactPerturbation N v u; fun_prop)
      fun x hx => by simp [compactPerturbation_eq_zero hx]
  have hpz : ∫ x, Real.exp (x / 2) * compactPerturbation N v u x = 0 := by
    rw [show (fun x => Real.exp (x / 2) * compactPerturbation N v u x) = fun x =>
      Real.cosh (x / 2) * compactPerturbation N v u x +
        Real.sinh (x / 2) * compactPerturbation N v u x by
      funext x; rw [← add_mul, Real.cosh_add_sinh], integral_add hic his, hcosh, hsinh, add_zero]
  have hsplit : (fun x => Real.exp (x / 2) * compactSurgerySource N v u x) =
      fun x => Real.exp (x / 2) * thetaCuspFullSource x +
        Real.exp (x / 2) * compactPerturbation N v u x := by
    funext x; simp only [compactSurgerySource]; ring
  rw [hsplit, integral_add hk hp, hpz, add_zero, integral_exp_half_mul_thetaCuspFullSource]

/-! ## Derivative bounds for the directions -/

theorem contDiff_weightAnchor (N : ℕ) (i : Fin (N + 2)) :
    ContDiff ℝ ∞ fun x => compactWeight x * evenAnchor N i x :=
  contDiff_compactWeight.mul (contDiff_evenAnchor N i)

theorem iteratedDeriv_anchorProj {N : ℕ} {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (anchorProj N compactWeight b) x = iteratedDeriv n b x -
      ∑ i, anchorCoef N compactWeight b i *
        iteratedDeriv n (fun x => compactWeight x * evenAnchor N i x) x := by
  have hsum : ContDiff ℝ ∞ fun x => ∑ i, anchorCoef N compactWeight b i *
      (compactWeight x * evenAnchor N i x) :=
    ContDiff.sum fun i _ => contDiff_const.mul (contDiff_weightAnchor N i)
  rw [show anchorProj N compactWeight b = b - fun x => ∑ i, anchorCoef N compactWeight b i *
      (compactWeight x * evenAnchor N i x) from rfl,
    iteratedDeriv_sub (hb.contDiffAt.of_le (mod_cast le_top)) (hsum.contDiffAt.of_le (mod_cast le_top)),
    iteratedDeriv_fun_sum fun i _ =>
      (contDiff_const.mul (contDiff_weightAnchor N i)).contDiffAt.of_le (mod_cast le_top)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact iteratedDeriv_const_mul _ ((contDiff_weightAnchor N i).contDiffAt.of_le (mod_cast le_top))

theorem hasCompactSupport_weightAnchor (N : ℕ) (i : Fin (N + 2)) :
    HasCompactSupport fun x => compactWeight x * evenAnchor N i x :=
  hasCompactSupport_compactWeight.mul_right

/-- Uniform packet-direction bound: `|Π(b_u)^{(n)}| ≤ B (1 + u)^n` for large `u`. -/
theorem exists_bound_iteratedDeriv_direction (N n : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφs : HasCompactSupport φ) (c : ℝ) {b : ℝ → ℝ → ℝ}
    (hbdef : ∀ u x, b u x = φ x * Real.cos (u * x + c))
    (hb : ∀ j, Tendsto (fun u => anchorMoments N (b u) j) atTop (𝓝 0)) :
    ∃ B U : ℝ, 0 ≤ B ∧ ∀ u, U ≤ u → 0 ≤ u → ∀ x,
      |iteratedDeriv n (anchorProj N compactWeight (b u)) x| ≤ B * (1 + u) ^ n := by
  obtain ⟨M, hM⟩ := exists_bound_iteratedDeriv hφ hφs n
  have hWA : ∀ i : Fin (N + 2), ∃ C, ∀ x,
      |iteratedDeriv n (fun x => compactWeight x * evenAnchor N i x) x| ≤ C := fun i => by
    obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv (contDiff_weightAnchor N i)
      (hasCompactSupport_weightAnchor N i) n
    exact ⟨C, hC n le_rfl⟩
  choose C hC using hWA
  have hcoef : ∀ᶠ u in atTop, ∀ i, |anchorCoef N compactWeight (b u) i| ≤ 1 :=
    eventually_all.mpr fun i => by
      have := (tendsto_anchorCoef (ψ := compactWeight) hb i).abs
      rw [abs_zero] at this
      exact this.eventually (eventually_le_nhds one_pos)
  obtain ⟨U, hU⟩ := eventually_atTop.mp hcoef
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  refine ⟨M + ∑ i, |C i|, U, by positivity, fun u hu hu0 x => ?_⟩
  have hbu : b u = fun x => φ x * Real.cos (u * x + c) := funext (hbdef u)
  have hcont : ContDiff ℝ ∞ (b u) := by rw [hbu]; fun_prop
  rw [iteratedDeriv_anchorProj hcont]
  have h1 : |iteratedDeriv n (b u) x| ≤ M * (1 + u) ^ n := by
    rw [hbu]
    have := abs_iteratedDeriv_mul_cos_le hφ hM u c x
    rwa [abs_of_nonneg hu0] at this
  have h2 : |∑ i, anchorCoef N compactWeight (b u) i *
      iteratedDeriv n (fun x => compactWeight x * evenAnchor N i x) x| ≤ ∑ i, |C i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    calc |anchorCoef N compactWeight (b u) i| *
          |iteratedDeriv n (fun x => compactWeight x * evenAnchor N i x) x| ≤ 1 * |C i| :=
          mul_le_mul (hU u hu i) ((hC i x).trans (le_abs_self _)) (abs_nonneg _) zero_le_one
      _ = |C i| := one_mul _
  have hpow : 1 ≤ (1 + u) ^ n := one_le_pow₀ (by linarith)
  calc |iteratedDeriv n (b u) x - ∑ i, anchorCoef N compactWeight (b u) i *
        iteratedDeriv n (fun x => compactWeight x * evenAnchor N i x) x|
      ≤ M * (1 + u) ^ n + ∑ i, |C i| := (abs_sub _ _).trans (add_le_add h1 h2)
    _ ≤ (M + ∑ i, |C i|) * (1 + u) ^ n := by
        have : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg fun i _ => abs_nonneg _
        nlinarith

theorem hasCompactSupport_id_mul_compactWeight :
    HasCompactSupport fun x => x * compactWeight x :=
  hasCompactSupport_compactWeight.mul_left

theorem exists_bound_iteratedDeriv_compactCosDirection (N n : ℕ) :
    ∃ B U : ℝ, 0 ≤ B ∧ ∀ u, U ≤ u → 0 ≤ u → ∀ x,
      |iteratedDeriv n (compactCosDirection N u) x| ≤ B * (1 + u) ^ n :=
  exists_bound_iteratedDeriv_direction N n contDiff_compactWeight hasCompactSupport_compactWeight 0
    (fun u x => by simp [compactCosPacket]) (tendsto_anchorMoments_cos N)

theorem exists_bound_iteratedDeriv_compactSinDirection (N n : ℕ) :
    ∃ B U : ℝ, 0 ≤ B ∧ ∀ u, U ≤ u → 0 ≤ u → ∀ x,
      |iteratedDeriv n (compactSinDirection N u) x| ≤ B * (1 + u) ^ n :=
  exists_bound_iteratedDeriv_direction N n (contDiff_id.mul contDiff_compactWeight)
    hasCompactSupport_id_mul_compactWeight (-(Real.pi / 2))
    (fun u x => by simp only [compactSinPacket, id]; rw [← sub_eq_add_neg, Real.cos_sub_pi_div_two])
    (tendsto_anchorMoments_sin N)

/-- Exponential smallness of the solve on the line `Im z = v`, `0 < v < 1/2`. -/
theorem exists_coeff_decay (N : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) :
    ∃ K U : ℝ, 0 ≤ K ∧ ∀ u, U ≤ u →
      (conj (compactCosEval N v u) * compactSinEval N v u).im ≠ 0 ∧
      |compactAlpha N v u| + |compactBeta N v u| ≤ K * Real.exp (-(u / 4)) := by
  obtain ⟨K, U, hK, hU⟩ := exists_compactSolve N hv
  obtain ⟨C, hC, hXi⟩ := exists_norm_XiC_horizontal_le (A := 1 / 2) (δ := 1 / 4) (by norm_num)
    (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨K * C, max U 0, by positivity, fun u hu => ⟨(hU u (le_of_max_le_left hu)).1, ?_⟩⟩
  have hu0 : 0 ≤ u := le_of_max_le_right hu
  have h := hXi u v (by rw [abs_of_pos hv]; linarith)
  rw [abs_of_nonneg hu0] at h
  calc |compactAlpha N v u| + |compactBeta N v u| ≤ K * ‖XiC ((u : ℂ) + v * I)‖ :=
        (hU u (le_of_max_le_left hu)).2
    _ ≤ K * (C * Real.exp (-(1 / 4 * u))) := mul_le_mul_of_nonneg_left h hK
    _ = K * C * Real.exp (-(u / 4)) := by ring_nf

/-- **Uniform smallness of the perturbation in every `C^n`.** -/
theorem exists_bound_iteratedDeriv_compactPerturbation (N n : ℕ) {v : ℝ} (hv : 0 < v)
    (hv2 : v < 1 / 2) : ∃ B U : ℝ, 0 ≤ B ∧ ∀ u, U ≤ u → ∀ x,
      |iteratedDeriv n (compactPerturbation N v u) x| ≤ B * ((1 + u) ^ n * Real.exp (-(u / 4))) := by
  obtain ⟨B₁, U₁, hB₁, h₁⟩ := exists_bound_iteratedDeriv_compactCosDirection N n
  obtain ⟨B₂, U₂, hB₂, h₂⟩ := exists_bound_iteratedDeriv_compactSinDirection N n
  obtain ⟨K, U₃, hK, h₃⟩ := exists_coeff_decay N hv hv2
  refine ⟨K * (B₁ + B₂), max (max U₁ U₂) (max U₃ 0), by positivity, fun u hu x => ?_⟩
  have hu1 : U₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hu2 : U₂ ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hu3 : U₃ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have hu0 : 0 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hu
  have hc1 : ContDiffAt ℝ ∞ (compactCosDirection N u) x :=
    (contDiff_anchorProj (N := N) (contDiff_compactCosPacket u)).contDiffAt
  have hc2 : ContDiffAt ℝ ∞ (compactSinDirection N u) x :=
    (contDiff_anchorProj (N := N) (contDiff_compactSinPacket u)).contDiffAt
  rw [show compactPerturbation N v u = (fun x => compactAlpha N v u * compactCosDirection N u x) +
      fun x => compactBeta N v u * compactSinDirection N u x from rfl,
    iteratedDeriv_add ((contDiffAt_const.mul hc1).of_le (mod_cast le_top))
      ((contDiffAt_const.mul hc2).of_le (mod_cast le_top)),
    iteratedDeriv_const_mul _ (hc1.of_le (mod_cast le_top)),
    iteratedDeriv_const_mul _ (hc2.of_le (mod_cast le_top))]
  have e1 := h₁ u hu1 hu0 x
  have e2 := h₂ u hu2 hu0 x
  have hco := (h₃ u hu3).2
  have hpow : 0 ≤ (1 + u) ^ n := by positivity
  calc |compactAlpha N v u * iteratedDeriv n (compactCosDirection N u) x +
        compactBeta N v u * iteratedDeriv n (compactSinDirection N u) x|
      ≤ |compactAlpha N v u| * (B₁ * (1 + u) ^ n) + |compactBeta N v u| * (B₂ * (1 + u) ^ n) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
          exact mul_le_mul_of_nonneg_left (by assumption) (abs_nonneg _)
    _ ≤ (|compactAlpha N v u| + |compactBeta N v u|) * ((B₁ + B₂) * (1 + u) ^ n) := by
        have := abs_nonneg (compactAlpha N v u); have := abs_nonneg (compactBeta N v u)
        nlinarith [mul_nonneg hB₁ hpow, mul_nonneg hB₂ hpow]
    _ ≤ K * Real.exp (-(u / 4)) * ((B₁ + B₂) * (1 + u) ^ n) :=
        mul_le_mul_of_nonneg_right hco (by positivity)
    _ = K * (B₁ + B₂) * ((1 + u) ^ n * Real.exp (-(u / 4))) := by ring

/-! ## Schwartz convergence -/

theorem compactSurgerySource_sub (N : ℕ) (v u : ℝ) :
    (fun y => compactSurgerySource N v u y - thetaCuspFullSource y) = compactPerturbation N v u := by
  funext y; simp [compactSurgerySource]

theorem iteratedDeriv_compactPerturbation_eq_zero {N : ℕ} {v u x : ℝ} (hx : 2 < |x|) (n : ℕ) :
    iteratedDeriv n (compactPerturbation N v u) x = 0 := by
  have hev : compactPerturbation N v u =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
    exact compactPerturbation_eq_zero hy.le
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
  split_ifs <;> rfl

/-- **Claim 3.** `g_u → k` in every Schwartz seminorm: `sup_x |x|^p |(g_u - k)^{(n)}(x)| → 0`. -/
theorem compactSurgerySource_schwartz (N n p : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) : ∃ U : ℝ, ∀ u, U ≤ u → ∀ x : ℝ,
      |x| ^ p * |iteratedDeriv n (fun y => compactSurgerySource N v u y - thetaCuspFullSource y) x|
        ≤ ε := by
  obtain ⟨B, U₁, hB, hbd⟩ := exists_bound_iteratedDeriv_compactPerturbation N n hv hv2
  have hlim := ((tendsto_one_add_pow_mul_exp_neg n).const_mul (2 ^ p * B))
  rw [mul_zero] at hlim
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds hε))
  refine ⟨max U₁ U₂, fun u hu x => ?_⟩
  rw [compactSurgerySource_sub]
  rcases lt_or_ge 2 |x| with hx | hx
  · rw [iteratedDeriv_compactPerturbation_eq_zero hx, abs_zero, mul_zero]; exact hε.le
  · have h1 := hbd u (le_of_max_le_left hu) x
    have h2 := hU₂ u (le_of_max_le_right hu)
    have hp : |x| ^ p ≤ 2 ^ p := pow_le_pow_left₀ (abs_nonneg x) hx p
    calc |x| ^ p * |iteratedDeriv n (compactPerturbation N v u) x|
        ≤ 2 ^ p * (B * ((1 + u) ^ n * Real.exp (-(u / 4)))) :=
          mul_le_mul hp h1 (abs_nonneg _) (by positivity)
      _ = 2 ^ p * B * ((1 + u) ^ n * Real.exp (-(u / 4))) := by ring
      _ ≤ ε := h2

/-! ## Positivity and strong log-concavity -/

/-- **Claim 1.** For large `u`, `g_u > 0` and `(log g_u)'' ≤ -2` on the whole line. -/
theorem compactSurgerySource_pos_logConcave (N : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) :
    ∃ U : ℝ, ∀ u, U ≤ u → (∀ x, 0 < compactSurgerySource N v u x) ∧
      ∀ x, iteratedDeriv 2 (fun y => Real.log (compactSurgerySource N v u y)) x ≤ -2 := by
  -- bounds for `k`
  have hk := contDiff_thetaCuspFullSource
  obtain ⟨C₀, -, hC₀⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le 0 0
  obtain ⟨C₁, -, hC₁⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le 0 1
  obtain ⟨C₂, -, hC₂⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le 0 2
  set M := |C₀| + |C₁| + |C₂|
  have hM : ∀ j ≤ 2, ∀ x, |iteratedDeriv j thetaCuspFullSource x| ≤ M := by
    intro j hj x
    interval_cases j
    · have := hC₀ x; simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at this
      linarith [le_abs_self C₀, abs_nonneg C₁, abs_nonneg C₂]
    · have := hC₁ x; simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at this
      linarith [le_abs_self C₁, abs_nonneg C₀, abs_nonneg C₂]
    · have := hC₂ x; simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at this
      linarith [le_abs_self C₂, abs_nonneg C₀, abs_nonneg C₁]
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨y₀, -, hy₀⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMinOn
    (nonempty_Icc.mpr (by norm_num)) hk.continuous.continuousOn
  set m₀ := thetaCuspFullSource y₀
  have hm₀ : 0 < m₀ := thetaCuspFullSource_pos_all y₀
  -- bounds for the perturbation
  obtain ⟨B₀, U₀, hB₀, h₀⟩ := exists_bound_iteratedDeriv_compactPerturbation N 0 hv hv2
  obtain ⟨B₁, U₁, hB₁, h₁⟩ := exists_bound_iteratedDeriv_compactPerturbation N 1 hv hv2
  obtain ⟨B₂, U₂, hB₂, h₂⟩ := exists_bound_iteratedDeriv_compactPerturbation N 2 hv hv2
  set δ := min 1 (min (m₀ / 2) (2 * m₀ ^ 2 / (8 * M + 4)))
  have hδ : 0 < δ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hlim := (tendsto_one_add_pow_mul_exp_neg 2).const_mul (B₀ + B₁ + B₂)
  rw [mul_zero] at hlim
  obtain ⟨U₃, hU₃⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds hδ))
  refine ⟨max (max U₀ U₁) (max U₂ (max U₃ 0)), fun u hu => ?_⟩
  have hu0 : 0 ≤ u := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_right _ _))) hu
  have hη : ∀ j ≤ 2, ∀ x, |iteratedDeriv j (compactPerturbation N v u) x| ≤ δ := by
    have hmono : ∀ j ≤ 2, (1 + u) ^ j * Real.exp (-(u / 4)) ≤ (1 + u) ^ 2 * Real.exp (-(u / 4)) :=
      fun j hj => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hj) (by positivity)
    have hbase := hU₃ u (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hu)
    have hE : 0 ≤ (1 + u) ^ 2 * Real.exp (-(u / 4)) := by positivity
    intro j hj x
    interval_cases j
    · calc _ ≤ B₀ * ((1 + u) ^ 0 * Real.exp (-(u / 4))) :=
            h₀ u (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu) x
        _ ≤ (B₀ + B₁ + B₂) * ((1 + u) ^ 2 * Real.exp (-(u / 4))) := by
            have := hmono 0 (by norm_num); nlinarith
        _ ≤ δ := hbase
    · calc _ ≤ B₁ * ((1 + u) ^ 1 * Real.exp (-(u / 4))) :=
            h₁ u (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu) x
        _ ≤ (B₀ + B₁ + B₂) * ((1 + u) ^ 2 * Real.exp (-(u / 4))) := by
            have := hmono 1 (by norm_num); nlinarith
        _ ≤ δ := hbase
    · calc _ ≤ B₂ * ((1 + u) ^ 2 * Real.exp (-(u / 4))) :=
            h₂ u (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu) x
        _ ≤ (B₀ + B₁ + B₂) * ((1 + u) ^ 2 * Real.exp (-(u / 4))) := by nlinarith
        _ ≤ δ := hbase
  set h := compactPerturbation N v u
  have hhc : ContDiff ℝ ∞ h := contDiff_compactPerturbation N v u
  have hg : compactSurgerySource N v u = thetaCuspFullSource + h := rfl
  have hgc : ContDiff ℝ ∞ (compactSurgerySource N v u) := by rw [hg]; exact hk.add hhc
  have hderiv : ∀ j ≤ 2, ∀ x, iteratedDeriv j (compactSurgerySource N v u) x =
      iteratedDeriv j thetaCuspFullSource x + iteratedDeriv j h x := by
    intro j _ x
    rw [hg, iteratedDeriv_add (hk.contDiffAt.of_le (mod_cast le_top))
      (hhc.contDiffAt.of_le (mod_cast le_top))]
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδm : δ ≤ m₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδq : δ ≤ 2 * m₀ ^ 2 / (8 * M + 4) := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the key inequality on `[-2, 2]`
  have hin : ∀ x, |x| ≤ 2 → 0 < compactSurgerySource N v u x ∧
      iteratedDeriv 2 (compactSurgerySource N v u) x * compactSurgerySource N v u x -
        iteratedDeriv 1 (compactSurgerySource N v u) x ^ 2 ≤
          -2 * compactSurgerySource N v u x ^ 2 := by
    intro x hx
    have hkx : m₀ ≤ thetaCuspFullSource x := hy₀ (abs_le.mp hx)
    have e0 := hη 0 (by norm_num) x
    have e1 := hη 1 (by norm_num) x
    have e2 := hη 2 (by norm_num) x
    simp only [iteratedDeriv_zero] at e0
    have k1 := hM 1 (by norm_num) x
    have k2 := hM 2 (by norm_num) x
    have k0 := hM 0 (by norm_num) x
    simp only [iteratedDeriv_zero] at k0
    have hN := thetaCuspLogConcavityNumerator_le x
    unfold thetaCuspLogConcavityNumerator at hN
    rw [hderiv 2 (by norm_num), hderiv 1 (by norm_num)]
    have hgx : compactSurgerySource N v u x = thetaCuspFullSource x + h x := rfl
    rw [hgx]
    set a := thetaCuspFullSource x
    set a1 := iteratedDeriv 1 thetaCuspFullSource x
    set a2 := iteratedDeriv 2 thetaCuspFullSource x
    set b0 := h x
    set b1 := iteratedDeriv 1 h x
    set b2 := iteratedDeriv 2 h x
    rw [abs_le] at e0 e1 e2 k0 k1 k2
    have hq : δ * (8 * M + 4) ≤ 2 * m₀ ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hδq
    constructor
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_left hδ1 hδ.le, sq_nonneg (a - m₀), mul_nonneg hM0 hδ.le]
  constructor
  · intro x
    rcases le_or_gt |x| 2 with hx | hx
    · exact (hin x hx).1
    · rw [compactSurgerySource_eq_of_two_le_abs N v u hx.le]; exact thetaCuspFullSource_pos_all x
  · have hpos : ∀ x, 0 < compactSurgerySource N v u x := fun x => by
      rcases le_or_gt |x| 2 with hx | hx
      · exact (hin x hx).1
      · rw [compactSurgerySource_eq_of_two_le_abs N v u hx.le]; exact thetaCuspFullSource_pos_all x
    intro x
    rw [iteratedDeriv_two_log_eq hgc hpos, div_le_iff₀ (by have := hpos x; positivity)]
    rcases le_or_gt |x| 2 with hx | hx
    · exact (hin x hx).2
    · have h1 := iteratedDeriv_compactPerturbation_eq_zero (N := N) (v := v) (u := u) hx 1
      have h2 := iteratedDeriv_compactPerturbation_eq_zero (N := N) (v := v) (u := u) hx 2
      rw [hderiv 2 (by norm_num), hderiv 1 (by norm_num), h1, h2,
        compactSurgerySource_eq_of_two_le_abs N v u hx.le, add_zero, add_zero]
      have hN := thetaCuspLogConcavityNumerator_le x
      unfold thetaCuspLogConcavityNumerator at hN
      nlinarith [sq_nonneg (thetaCuspFullSource x)]

/-! ## Every finite prime deletion stays positive -/

/-- A profile supported in `(-2, 2)` has `|D_S f(x)| ≤ 8 sup |f|` on `x ≥ 0`, and `D_S f(x) = 0`
for `x ≥ 2`, uniformly in the finite prime set `S`. -/
theorem abs_thetaPrimeDeletion_le_of_support {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {f : ℝ → ℝ}
    (hs : ∀ y, 2 ≤ |y| → f y = 0) {η : ℝ} (hη : ∀ y, |f y| ≤ η) {x : ℝ} (hx : 0 ≤ x) :
    |thetaPrimeDeletion S f x| ≤ 8 * η ∧ (2 ≤ x → thetaPrimeDeletion S f x = 0) := by
  classical
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0)
  have hd1 : ∀ T ∈ S.powerset, (1 : ℝ) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := fun T hT => by
    have : 0 < ∏ p ∈ T, p :=
      Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
    exact_mod_cast this
  have hterm : ∀ T ∈ S.powerset, |(-1 : ℝ) ^ T.card * ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) *
      f (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)))| ≤ if ∏ p ∈ T, p < 8 then η else 0 := by
    intro T hT
    have h1 := hd1 T hT
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have hrp : ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    split_ifs with h8
    · exact (mul_le_of_le_one_left (abs_nonneg _) hrp).trans (hη _)
    · have h8' : (8 : ℝ) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast not_lt.mp h8
      have hlog : 2 ≤ Real.log ((∏ p ∈ T, p : ℕ) : ℝ) :=
        two_lt_log_eight.le.trans (Real.log_le_log (by norm_num) h8')
      rw [hs _ (by rw [abs_of_nonneg (by linarith)]; linarith), abs_zero, mul_zero]
  constructor
  · calc |thetaPrimeDeletion S f x|
        ≤ ∑ T ∈ S.powerset, (if ∏ p ∈ T, p < 8 then η else 0) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
      _ = ((S.powerset.filter fun T => ∏ p ∈ T, p < 8).card : ℝ) * η := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 8 * η := by
          refine mul_le_mul_of_nonneg_right ?_ hη0
          have hcard : (S.powerset.filter fun T => ∏ p ∈ T, p < 8).card ≤ (Finset.range 8).card :=
            Finset.card_le_card_of_injOn (fun T => ∏ p ∈ T, p)
              (fun T hT => Finset.mem_range.mpr (Finset.mem_filter.mp hT).2)
              ((Sieve.prod_injOn_powerset hS).mono fun T hT => (Finset.mem_filter.mp hT).1)
          rw [Finset.card_range] at hcard
          exact_mod_cast hcard
  · intro hx2
    refine Finset.sum_eq_zero fun T hT => ?_
    have hlog : 0 ≤ Real.log ((∏ p ∈ T, p : ℕ) : ℝ) := Real.log_nonneg (hd1 T hT)
    rw [hs _ (by rw [abs_of_nonneg (by linarith)]; linarith), mul_zero, mul_zero]

/-- **Claim 5.** For large `u`, every finite literal prime deletion of `g_u` is positive on the
right ray, simultaneously for all finite prime sets. -/
theorem thetaPrimeDeletion_compactSurgerySource_pos (N : ℕ) {v : ℝ} (hv : 0 < v)
    (hv2 : v < 1 / 2) : ∃ U : ℝ, ∀ u, U ≤ u → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      ∀ x, 0 ≤ x → 0 < thetaPrimeDeletion S (compactSurgerySource N v u) x := by
  obtain ⟨y₀, hy₀m, hy₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_isMinOn
    (nonempty_Icc.mpr (by norm_num)) continuous_thetaCuspSourceTerm_one.continuousOn
  have ha : 0 < thetaCuspSourceTerm y₀ 1 := thetaCuspSourceTerm_one_pos_of_nonneg hy₀m.1
  obtain ⟨B, U₁, hB, hbd⟩ := exists_bound_iteratedDeriv_compactPerturbation N 0 hv hv2
  have hlim := (tendsto_one_add_pow_mul_exp_neg 0).const_mul B
  rw [mul_zero] at hlim
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp (hlim.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < thetaCuspSourceTerm y₀ 1 / 8)))
  refine ⟨max U₁ U₂, fun u hu S hS x hx => ?_⟩
  set η := B * ((1 + u) ^ 0 * Real.exp (-(u / 4)))
  have hη : ∀ y, |compactPerturbation N v u y| ≤ η := fun y => by
    have := hbd u (le_of_max_le_left hu) y; simp only [iteratedDeriv_zero] at this; exact this
  have hηs : η < thetaCuspSourceTerm y₀ 1 / 8 := hU₂ u (le_of_max_le_right hu)
  obtain ⟨h8, h0⟩ := abs_thetaPrimeDeletion_le_of_support hS (f := compactPerturbation N v u)
    (fun y hy => compactPerturbation_eq_zero hy) hη hx
  rw [show compactSurgerySource N v u = fun y => thetaCuspFullSource y + compactPerturbation N v u y
    from rfl, thetaPrimeDeletion_add]
  have hk := (thetaCuspSourceTerm_one_le_thetaPrimeDeletion S hS hx).1
  rcases lt_or_ge x 2 with hx2 | hx2
  · have hmin : thetaCuspSourceTerm y₀ 1 ≤ thetaCuspSourceTerm x 1 := hy₀ ⟨hx, hx2.le⟩
    have := abs_le.mp h8
    linarith
  · rw [h0 hx2, add_zero]
    exact lt_of_lt_of_le (thetaCuspSourceTerm_one_pos_of_nonneg hx) hk

/-! ## The perturbation is genuinely nonzero -/

/-- **Claim 4 (genuine surgery).** At arbitrarily large `u` the source is actually changed. -/
theorem exists_compactSurgerySource_ne (N : ℕ) {v : ℝ} (hv : 0 < v) (U : ℝ) :
    ∃ u, U ≤ u ∧ compactSurgerySource N v u ≠ thetaCuspFullSource := by
  obtain ⟨K, U₁, -, hU₁⟩ := exists_compactSolve N hv
  obtain ⟨u, hu, hne⟩ := exists_XiC_horizontal_ne_zero v (max U U₁)
  refine ⟨u, le_trans (le_max_left _ _) hu, fun heq => hne ?_⟩
  have h0 := stripEval_compactSurgerySource_eq_zero (hU₁ u (le_trans (le_max_right _ _) hu)).1
  rw [heq, stripEval_thetaCuspFullSource] at h0
  exact h0

/-! ## The theorem -/

/-- **Compact theta zero surgery.** For `0 < v < 1/2` and moment depth `J`, for all large `u` the
source `g_u = compactSurgerySource (J/2) v u` equals `k` outside `[-2, 2]`, is even, positive and
strongly log-concave, has the moments of `k` through order `J` and the critical charge
`∫ e^{x/2} g_u = 1/2`, has the forced strip zero `F_{g_u}(u + iv) = 0`, and keeps every finite
literal prime deletion positive on the right ray. -/
theorem compact_critical_strip_zero_engineering (J : ℕ) {v : ℝ} (hv : 0 < v) (hv2 : v < 1 / 2) :
    ∃ U : ℝ, ∀ u, U ≤ u →
      (∀ x, 2 ≤ |x| → compactSurgerySource (J / 2) v u x = thetaCuspFullSource x) ∧
      (∀ x, compactSurgerySource (J / 2) v u (-x) = compactSurgerySource (J / 2) v u x) ∧
      (∀ x, 0 < compactSurgerySource (J / 2) v u x) ∧
      (∀ x, iteratedDeriv 2 (fun y => Real.log (compactSurgerySource (J / 2) v u y)) x ≤ -2) ∧
      (∀ j ≤ J, ∫ x, x ^ j * compactSurgerySource (J / 2) v u x =
        ∫ x, x ^ j * thetaCuspFullSource x) ∧
      ∫ x, Real.exp (x / 2) * compactSurgerySource (J / 2) v u x = 1 / 2 ∧
      stripEval v u (compactSurgerySource (J / 2) v u) = 0 ∧
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        ∀ x, 0 ≤ x → 0 < thetaPrimeDeletion S (compactSurgerySource (J / 2) v u) x := by
  obtain ⟨U₁, h₁⟩ := compactSurgerySource_pos_logConcave (J / 2) hv hv2
  obtain ⟨K, U₂, -, h₂⟩ := exists_compactSolve (J / 2) hv
  obtain ⟨U₃, h₃⟩ := thetaPrimeDeletion_compactSurgerySource_pos (J / 2) hv hv2
  refine ⟨max U₁ (max U₂ U₃), fun u hu => ⟨fun x hx => compactSurgerySource_eq_of_two_le_abs _ v u hx,
    compactSurgerySource_neg _ v u, (h₁ u (le_of_max_le_left hu)).1, (h₁ u (le_of_max_le_left hu)).2,
    fun j hj => integral_pow_mul_compactSurgerySource _ v u (by omega),
    integral_exp_half_mul_compactSurgerySource _ v u,
    stripEval_compactSurgerySource_eq_zero (h₂ u (le_trans (le_max_left _ _) (le_of_max_le_right hu))).1,
    h₃ u (le_trans (le_max_right _ _) (le_of_max_le_right hu))⟩⟩

end

end RHTower
