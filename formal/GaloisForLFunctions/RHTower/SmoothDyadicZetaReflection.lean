import GaloisForLFunctions.RHTower.ZetaChiLeftHalfPlaneGrowth
import GaloisForLFunctions.RHTower.SmoothAFEZetaArbitraryNegativeEdge
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone
import GaloisForLFunctions.RHTower.GaussianShiftedMoment
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralVertical

/-!
# Reflection of a smooth dyadic sum of `n^{-1-iτ}`

For the Gaussian cutoff `V` of the smooth approximate functional equation, the dyadic smooth sum
`H(τ) = ∑_n n^{-1-iτ} (V(n/2N) − V(n/N))` is the difference of two smooth AFE Mellin integrals at
`s = 1 + iτ`; the AFE turns it into the difference of the two dual integrals on `Re w = −3/2`.
There `ζ(s + w) = χ(s + w) ζ(1 − s − w)` and the dual Dirichlet series splits at `M`: the head
moves to `Re(s + w) = 1/2`, where `|χ| = 1`, and the tail moves to `Re(s + w) = 1/2 − 2j`, where
`|χ| ≤ (|t| + 2j + 2)^{2j}` and the tail is `O(M^{1/2 − 2j})`.  Result (Jutila's reflection):
`|H(τ)| ≤ N^{-1/2} ∫ e^{-v²} |∑_{m ≤ M} m^{-1/2 + i(τ+v)}| dv + (tail) + 2e^{-τ²}/|τ|`.
-/

namespace RHTower

open Complex MeasureTheory Filter Topology Set

noncomputable section

/-- The dual partial sum `∑_{m ≤ M} m^{z-1}`. -/
def dualPartialSum (M : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (z - 1)

/-- The dyadic Mellin weight `((2N)^w − N^w) e^{w²}/w`. -/
def dyadicMellinWeight (N : ℝ) (w : ℂ) : ℂ :=
  ((((2 * N : ℝ)) : ℂ) ^ w - ((N : ℝ) : ℂ) ^ w) * smoothAFEGaussianKernel w

/-- The smooth dyadic sum `∑ n^{-1-iτ}(V(n/2N) − V(n/N))`, as a difference of AFE integrals. -/
def dyadicSmoothGram (N τ : ℝ) : ℂ :=
  smoothAFEZetaMellinAt 1 ((1 : ℂ) + (τ : ℂ) * I) (2 * N) -
    smoothAFEZetaMellinAt 1 ((1 : ℂ) + (τ : ℂ) * I) N

/-- The Gaussian kernel off the imaginary axis. -/
theorem norm_smoothAFEGaussianKernel_le_of_re_ne {u : ℝ} (hu : u ≠ 0) (v : ℝ) :
    ‖smoothAFEGaussianKernel ((u : ℂ) + (v : ℂ) * I)‖ ≤
      (Real.exp (u ^ 2) / |u|) * Real.exp (-(v ^ 2)) := by
  unfold smoothAFEGaussianKernel
  have hre : ((((u : ℂ) + (v : ℂ) * I) ^ 2).re) = u ^ 2 - v ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [norm_div, Complex.norm_exp, hre]
  have hden : |u| ≤ ‖(u : ℂ) + (v : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((u : ℂ) + (v : ℂ) * I)
    simpa using this
  have hu0 : 0 < |u| := abs_pos.2 hu
  calc Real.exp (u ^ 2 - v ^ 2) / ‖(u : ℂ) + (v : ℂ) * I‖
      ≤ Real.exp (u ^ 2 - v ^ 2) / |u| := div_le_div_of_nonneg_left (by positivity) hu0 hden
    _ = (Real.exp (u ^ 2) / |u|) * Real.exp (-(v ^ 2)) := by
        rw [show u ^ 2 - v ^ 2 = u ^ 2 + -(v ^ 2) by ring, Real.exp_add]; ring

/-- The dyadic Mellin weight on a line `Re w = u < 0`. -/
theorem norm_dyadicMellinWeight_le {N u : ℝ} (hN : 0 < N) (hu : u < 0) (v : ℝ) :
    ‖dyadicMellinWeight N ((u : ℂ) + (v : ℂ) * I)‖ ≤
      (2 * N ^ u * (Real.exp (u ^ 2) / |u|)) * Real.exp (-(v ^ 2)) := by
  unfold dyadicMellinWeight
  rw [norm_mul]
  have h2N : ‖(((2 * N : ℝ)) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I)‖ = (2 * N) ^ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]; simp
  have hN' : ‖((N : ℝ) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I)‖ = N ^ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]; simp
  have hle : (2 * N) ^ u ≤ N ^ u :=
    Real.rpow_le_rpow_of_nonpos hN (by linarith) hu.le
  have hdiff : ‖(((2 * N : ℝ)) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I) -
      ((N : ℝ) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I)‖ ≤ 2 * N ^ u := by
    refine (norm_sub_le _ _).trans ?_
    rw [h2N, hN']; linarith
  have hK := norm_smoothAFEGaussianKernel_le_of_re_ne hu.ne v
  calc ‖(((2 * N : ℝ)) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I) -
        ((N : ℝ) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I)‖ *
        ‖smoothAFEGaussianKernel ((u : ℂ) + (v : ℂ) * I)‖
      ≤ (2 * N ^ u) * ((Real.exp (u ^ 2) / |u|) * Real.exp (-(v ^ 2))) :=
        mul_le_mul hdiff hK (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem differentiableAt_dyadicMellinWeight {N : ℝ} (hN : 0 < N) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℂ (dyadicMellinWeight N) w := by
  unfold dyadicMellinWeight smoothAFEGaussianKernel
  have h2 : (((2 * N : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * N : ℝ) ≠ 0)
  have h1 : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ((differentiableAt_id.const_cpow (Or.inl h2)).sub
    (differentiableAt_id.const_cpow (Or.inl h1))).mul ?_
  exact ((differentiableAt_id.pow 2).cexp).div differentiableAt_id hw

/-- **Integrability on a vertical line** of a polynomially bounded continuous factor against the
dyadic Mellin weight. -/
theorem integrable_mul_dyadicMellinWeight {N u A C : ℝ} {K : ℕ} {g : ℂ → ℂ} (hN : 0 < N)
    (hu : u < 0) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hcont : Continuous fun v : ℝ => g ((u : ℂ) + (v : ℂ) * I))
    (hg : ∀ v : ℝ, ‖g ((u : ℂ) + (v : ℂ) * I)‖ ≤ C * (A + |v|) ^ K) :
    Integrable fun v : ℝ =>
      g ((u : ℂ) + (v : ℂ) * I) * dyadicMellinWeight N ((u : ℂ) + (v : ℂ) * I) := by
  have hmeas : Continuous fun v : ℝ =>
      g ((u : ℂ) + (v : ℂ) * I) * dyadicMellinWeight N ((u : ℂ) + (v : ℂ) * I) := by
    refine hcont.mul ?_
    have hc : Continuous fun v : ℝ => ((u : ℂ) + (v : ℂ) * I) := by fun_prop
    refine continuous_iff_continuousAt.2 fun v => ?_
    have hw : ((u : ℂ) + (v : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; exact hu.ne this
    exact ContinuousAt.comp (g := dyadicMellinWeight N) (f := fun v : ℝ => (u : ℂ) + (v : ℂ) * I)
      (x := v) (differentiableAt_dyadicMellinWeight hN hw).continuousAt hc.continuousAt
  refine Integrable.mono' ((integrable_shifted_pow_mul_exp_neg_sq A K).const_mul
    (C * (2 * N ^ u * (Real.exp (u ^ 2) / |u|)))) hmeas.aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [norm_mul]
  have hW := norm_dyadicMellinWeight_le hN hu v
  calc ‖g ((u : ℂ) + (v : ℂ) * I)‖ * ‖dyadicMellinWeight N ((u : ℂ) + (v : ℂ) * I)‖
      ≤ (C * (A + |v|) ^ K) * ((2 * N ^ u * (Real.exp (u ^ 2) / |u|)) *
          Real.exp (-(v ^ 2))) := mul_le_mul (hg v) hW (norm_nonneg _) (by positivity)
    _ = C * (2 * N ^ u * (Real.exp (u ^ 2) / |u|)) *
          ((A + |v|) ^ K * Real.exp (-v ^ (2 : ℕ))) := by ring

/-- The dyadic weight on a strip `a ≤ Re w ≤ b < 0`, uniformly (for `N ≥ 1`). -/
theorem norm_dyadicMellinWeight_le_strip {N a b u : ℝ} (hN : 1 ≤ N) (hb : b < 0)
    (hau : a ≤ u) (hub : u ≤ b) (v : ℝ) :
    ‖dyadicMellinWeight N ((u : ℂ) + (v : ℂ) * I)‖ ≤
      (2 * (Real.exp (a ^ 2) / |b|)) * Real.exp (-(v ^ 2)) := by
  have hu : u < 0 := lt_of_le_of_lt hub hb
  refine (norm_dyadicMellinWeight_le (by linarith) hu v).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hNu : N ^ u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN hu.le
  have hexp : Real.exp (u ^ 2) ≤ Real.exp (a ^ 2) := by
    apply Real.exp_le_exp.2; nlinarith
  have habs : |b| ≤ |u| := by
    rw [abs_of_neg hb, abs_of_neg hu]; linarith
  have hb0 : 0 < |b| := abs_pos.2 hb.ne
  have h1 : Real.exp (u ^ 2) / |u| ≤ Real.exp (a ^ 2) / |b| :=
    div_le_div₀ (by positivity) hexp hb0 habs
  calc 2 * N ^ u * (Real.exp (u ^ 2) / |u|) ≤ 2 * 1 * (Real.exp (a ^ 2) / |b|) := by
        gcongr
    _ = 2 * (Real.exp (a ^ 2) / |b|) := by ring

/-- **Horizontal edges vanish** for a polynomially bounded factor against the dyadic weight. -/
theorem tendsto_horizontal_mul_dyadicMellinWeight {N a b A C : ℝ} {K : ℕ} {g : ℂ → ℂ}
    (hN : 1 ≤ N) (hab : a ≤ b) (hb : b < 0) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hg : ∀ u v : ℝ, a ≤ u → u ≤ b → ‖g ((u : ℂ) + (v : ℂ) * I)‖ ≤ C * (A + |v|) ^ K)
    {ε : ℝ} (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ u in a..b,
      g ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I) * dyadicMellinWeight N ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  set D : ℝ := C * (2 * (Real.exp (a ^ 2) / |b|)) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hlim : Tendsto (fun T : ℝ => (b - a) * (D * ((A + T) ^ K * Real.exp (-(T ^ 2)))))
      atTop (𝓝 0) := by
    have h := (tendsto_shifted_pow_mul_exp_neg_sq A K).const_mul D
    simpa using h.const_mul (b - a)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have habsT : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg hT]
  have hpoint : ∀ u ∈ Set.uIoc a b,
      ‖g ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I) *
        dyadicMellinWeight N ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ ≤
        D * ((A + T) ^ K * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    rw [norm_mul]
    have h1 := hg u (ε * T) hu.1.le hu.2
    have h2 := norm_dyadicMellinWeight_le_strip hN hb hu.1.le hu.2 (ε * T)
    rw [habsT] at h1
    have hsq : (ε * T) ^ 2 = T ^ 2 := by
      rw [mul_pow, show ε ^ 2 = |ε| ^ 2 by rw [sq_abs], hε, one_pow, one_mul]
    rw [hsq] at h2
    calc ‖g ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ *
          ‖dyadicMellinWeight N ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ (C * (A + T) ^ K) * ((2 * (Real.exp (a ^ 2) / |b|)) * Real.exp (-(T ^ 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = D * ((A + T) ^ K * Real.exp (-(T ^ 2))) := by rw [hD]; ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at hint
  linarith

/-- **Contour shift** across a strip `a ≤ Re w ≤ b < 0` for a holomorphic, polynomially bounded
factor against the dyadic weight. -/
theorem integral_mul_dyadicMellinWeight_shift {N a b A C : ℝ} {K : ℕ} {g : ℂ → ℂ}
    (hN : 1 ≤ N) (hab : a ≤ b) (hb : b < 0) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hdiff : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → DifferentiableAt ℂ g w)
    (hg : ∀ u v : ℝ, a ≤ u → u ≤ b → ‖g ((u : ℂ) + (v : ℂ) * I)‖ ≤ C * (A + |v|) ^ K) :
    (∫ v : ℝ, g ((b : ℂ) + (v : ℂ) * I) * dyadicMellinWeight N ((b : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, g ((a : ℂ) + (v : ℂ) * I) * dyadicMellinWeight N ((a : ℂ) + (v : ℂ) * I) := by
  have hN0 : 0 < N := by linarith
  have hline : ∀ u : ℝ, a ≤ u → u ≤ b → Integrable fun v : ℝ =>
      g ((u : ℂ) + (v : ℂ) * I) * dyadicMellinWeight N ((u : ℂ) + (v : ℂ) * I) := by
    intro u hau hub
    refine integrable_mul_dyadicMellinWeight hN0 (lt_of_le_of_lt hub hb) hA hC ?_
      (fun v => hg u v hau hub)
    have hc : Continuous fun v : ℝ => ((u : ℂ) + (v : ℂ) * I) := by fun_prop
    refine continuous_iff_continuousAt.2 fun v => ?_
    exact ContinuousAt.comp (g := g) (f := fun v : ℝ => (u : ℂ) + (v : ℂ) * I) (x := v)
      (hdiff _ (by simp [hau]) (by simp [hub])).continuousAt hc.continuousAt
  refine GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
    (G := fun w => g w * dyadicMellinWeight N w) hab ?_
    (hline a le_rfl hab) (hline b hab le_rfl) ?_ ?_
  · intro w hw
    have hw0 : w ≠ 0 := by
      intro h; have := hw.2; rw [h] at this; simp at this; linarith
    exact ((hdiff w hw.1 hw.2).mul (differentiableAt_dyadicMellinWeight hN0 hw0)).differentiableWithinAt
  · have := tendsto_horizontal_mul_dyadicMellinWeight hN hab hb hA hC hg
      (ε := -1) (by norm_num)
    simpa using this
  · have := tendsto_horizontal_mul_dyadicMellinWeight hN hab hb hA hC hg
      (ε := 1) (by norm_num)
    simpa using this

/-- A continuous function on a compact rectangle of the plane is bounded there. -/
theorem exists_norm_le_on_rect {f : ℂ → ℂ} {a b c : ℝ}
    (hf : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → |t| ≤ c → ContinuousAt f ((σ : ℂ) + (t : ℂ) * I)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ b → |t| ≤ c → ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B := by
  set S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (-c) c with hS
  have hSc : IsCompact S := isCompact_Icc.prod isCompact_Icc
  set F : ℝ × ℝ → ℂ := fun p => f ((p.1 : ℂ) + (p.2 : ℂ) * I) with hF
  have hFc : ContinuousOn F S := by
    intro p hp
    have hp1 := hp.1
    have hp2 := hp.2
    refine (ContinuousAt.comp (g := f) (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
      (hf p.1 p.2 hp1.1 hp1.2 (abs_le.2 ⟨hp2.1, hp2.2⟩)) (by fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn hFc
  refine ⟨max B 0, le_max_right _ _, fun σ t h1 h2 h3 => ?_⟩
  have := hB (σ, t) ⟨⟨h1, h2⟩, (abs_le.1 h3)⟩
  exact this.trans (le_max_left _ _)

/-- **`χ` is polynomially bounded on `1/2 − 2j ≤ Re z ≤ 1/2`, at every height.** -/
theorem exists_norm_zetaChi_strip_le_global (j : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 - 2 * j ≤ σ → σ ≤ 1 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ K := by
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := exists_norm_zetaChi_strip_le j
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_on_rect (f := zetaChi) (a := 1 / 2 - 2 * j) (b := 1 / 2)
    (c := 2) (fun σ t _ hσ _ => by
      refine (zetaChi_analyticAt (Gammaℝ_ne_zero_of_re_pos ?_)).continuousAt
      simp; linarith)
  refine ⟨max C₁ B, K₁, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have hpow : 1 ≤ (1 + |t|) ^ K₁ := one_le_pow₀ (by linarith [abs_nonneg t])
  rcases le_or_gt 2 |t| with ht | ht
  · exact (h₁ σ t hσ1 hσ2 ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B := hB σ t hσ1 hσ2 ht.le
      _ ≤ max C₁ B * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max C₁ B * (1 + |t|) ^ K₁ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- `|ζ(z)| ≤ 3` on `Re z ≥ 3/2`. -/
theorem norm_riemannZeta_le_three {z : ℂ} (hz : 3 / 2 ≤ z.re) : ‖riemannZeta z‖ ≤ 3 := by
  have hz1 : 1 < z.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz1]
  have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ ≤ ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_div, norm_one, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hn, Real.rpow_neg hn.le, one_div]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le (by linarith) hz)
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    have h1 := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
    refine h1.congr fun n => ?_
    rw [Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity)]
  have hs' := hsum.of_nonneg_of_le (fun n => norm_nonneg _) hterm
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ z‖ ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ :=
        norm_tsum_le_tsum_norm hs'
    _ ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := hs'.tsum_le_tsum hterm hsum
    _ ≤ 1 + 1 / (3 / 2 - 1) := RHTower.tsum_add_one_rpow_le (by norm_num)
    _ = 3 := by norm_num

/-- `|∑_{m ≤ M} m^{z−1}| ≤ M` on `Re z ≤ 1`. -/
theorem norm_dualPartialSum_le {M : ℕ} {z : ℂ} (hz : z.re ≤ 1) : ‖dualPartialSum M z‖ ≤ M := by
  unfold dualPartialSum
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ m ∈ Finset.Icc 1 M, ‖(m : ℂ) ^ (z - 1)‖ ≤ 1 := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    rw [show ((m : ℂ)) = (((m : ℝ)) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
    have : (z - 1).re ≤ 0 := by simp; linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Finset.mem_Icc.1 hm).1) this
  calc ∑ m ∈ Finset.Icc 1 M, ‖(m : ℂ) ^ (z - 1)‖ ≤ ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) :=
        Finset.sum_le_sum h
    _ = M := by simp

theorem differentiableAt_dualPartialSum (M : ℕ) (z : ℂ) :
    DifferentiableAt ℂ (dualPartialSum M) z := by
  unfold dualPartialSum
  have : (fun z : ℂ => ∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (z - 1)) =
      ∑ m ∈ Finset.Icc 1 M, fun z : ℂ => (m : ℂ) ^ (z - 1) := by
    funext z; simp
  rw [this]
  refine DifferentiableAt.sum fun m hm => ?_
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by have := (Finset.mem_Icc.1 hm).1; omega : m ≠ 0)
  exact (differentiableAt_id.sub_const 1).const_cpow (Or.inl hm0)

/-- The point `s + w` for `s = 1 + iτ`, `w = u + iv`. -/
theorem one_add_mul_I_add_point (τ u v : ℝ) :
    ((1 : ℂ) + (τ : ℂ) * I) + ((u : ℂ) + (v : ℂ) * I) = ((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- **The dyadic smooth sum as a dual integral on `Re w = −3/2`.** -/
theorem dyadicSmoothGram_eq_dualIntegral {N τ : ℝ} (hN : 0 < N) (hτ : τ ≠ 0) :
    dyadicSmoothGram N τ =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ v : ℝ,
        riemannZeta (((1 : ℂ) + (τ : ℂ) * I) + (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I)) *
          dyadicMellinWeight N (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I)) +
      (smoothAFEZetaShiftedPoleResidue ((1 : ℂ) + (τ : ℂ) * I) (2 * N) -
        smoothAFEZetaShiftedPoleResidue ((1 : ℂ) + (τ : ℂ) * I) N) := by
  set s : ℂ := (1 : ℂ) + (τ : ℂ) * I with hs
  have hsre : s.re = 1 := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp [hs] at this; exact hτ this
  have h2 := riemannZeta_eq_smoothAFEZetaMellin_sub_arbitrary_dualEdge_sub_residue
    (x := 2 * N) (c := 3 / 2) (by positivity) (by norm_num) hs1 (by rw [hsre]; norm_num)
    (by rw [hsre]; norm_num)
  have h1 := riemannZeta_eq_smoothAFEZetaMellin_sub_arbitrary_dualEdge_sub_residue
    (x := N) (c := 3 / 2) hN (by norm_num) hs1 (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
  have hint2 := smoothAFEZetaMellinIntegrand_verticalIntegrable_general (x := 2 * N) (s := s)
    (c := -(3 / 2)) (by positivity) (by norm_num) (by rw [hsre]; norm_num)
  have hint1 := smoothAFEZetaMellinIntegrand_verticalIntegrable_general (x := N) (s := s)
    (c := -(3 / 2)) hN (by norm_num) (by rw [hsre]; norm_num)
  have hdual : smoothAFEZetaDualMellinEdge s (2 * N) (3 / 2) -
      smoothAFEZetaDualMellinEdge s N (3 / 2) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ,
        riemannZeta (s + (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I)) *
          dyadicMellinWeight N (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEZetaDualMellinEdge
    rw [Complex.real_smul, Complex.real_smul, ← mul_sub]
    congr 1
    rw [Complex.VerticalIntegrable] at hint2 hint1
    rw [← integral_sub hint2 hint1]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smoothAFEZetaMellinIntegrand, dyadicMellinWeight]
    ring
  unfold dyadicSmoothGram
  rw [← hdual]
  linear_combination h1 - h2

/-- **The dual tail.** For `Re z < 0`, `ζ(1 − z) − ∑_{m ≤ M} m^{z−1}` is the tail of the dual series,
at most `M^{Re z}/(−Re z)`. -/
theorem norm_riemannZeta_one_sub_sub_dualPartialSum_le {z : ℂ} (hz : z.re < 0) {M : ℕ}
    (hM : 1 ≤ M) :
    ‖riemannZeta (1 - z) - dualPartialSum M z‖ ≤ (M : ℝ) ^ z.re / (-z.re) := by
  have hre : 1 < (1 - z).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ (1 - z) with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ = ((n : ℝ) + 1) ^ (-(1 - z.re)) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hf]
    rw [norm_div, norm_one, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hn, Real.rpow_neg hn.le, one_div]
    simp
  have hsum : Summable f := by
    refine Summable.of_norm ?_
    have h1 := (Real.summable_one_div_nat_add_rpow 1 (1 - z.re)).2 (by linarith)
    refine h1.congr fun n => ?_
    rw [hnorm n, Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity)]
  have hsplit := hsum.sum_add_tsum_nat_add M
  have hhead : ∑ n ∈ Finset.range M, f n = dualPartialSum M z := by
    unfold dualPartialSum
    rw [Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range, tsub_zero,
      show Finset.Icc 1 M = Finset.Ico 1 (M + 1) by
        ext m; simp [Finset.mem_Icc, Finset.mem_Ico],
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hf]
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [one_div, ← Complex.cpow_neg, neg_sub]
    push_cast; ring_nf
  have heq : (∑' n, f n) - dualPartialSum M z = ∑' i, f (i + M) := by
    rw [← hsplit, hhead]; ring
  rw [heq]
  have hsum' : Summable fun i => f (i + M) := (summable_nat_add_iff M).2 hsum
  have hn' : ∀ i : ℕ, ‖f (i + M)‖ = (((i + M + 1 : ℕ) : ℝ)) ^ (-(1 - z.re)) := by
    intro i; rw [hnorm]; push_cast; ring_nf
  have hnsum : Summable fun i => ‖f (i + M)‖ := hsum'.norm
  calc ‖∑' i, f (i + M)‖ ≤ ∑' i, ‖f (i + M)‖ := norm_tsum_le_tsum_norm hnsum
    _ = ∑' i : ℕ, (((i + M + 1 : ℕ) : ℝ)) ^ (-(1 - z.re)) := tsum_congr hn'
    _ ≤ (M : ℝ) ^ (1 - (1 - z.re)) / ((1 - z.re) - 1) :=
        RHTower.Sieve.tsum_tail_rpow_neg_le (by linarith) hM
    _ = (M : ℝ) ^ z.re / (-z.re) := by ring_nf

/-- The head factor `χ(s + w) ∑_{m ≤ M} m^{s+w−1}`, `s = 1 + iτ`. -/
def reflectionHeadFactor (τ : ℝ) (M : ℕ) (w : ℂ) : ℂ :=
  zetaChi (((1 : ℂ) + (τ : ℂ) * I) + w) * dualPartialSum M (((1 : ℂ) + (τ : ℂ) * I) + w)

/-- The tail factor `χ(s + w)(ζ(1 − s − w) − ∑_{m ≤ M} m^{s+w−1})`, `s = 1 + iτ`. -/
def reflectionTailFactor (τ : ℝ) (M : ℕ) (w : ℂ) : ℂ :=
  zetaChi (((1 : ℂ) + (τ : ℂ) * I) + w) *
    (riemannZeta (1 - (((1 : ℂ) + (τ : ℂ) * I) + w)) -
      dualPartialSum M (((1 : ℂ) + (τ : ℂ) * I) + w))

theorem differentiableAt_reflectionHeadFactor (τ : ℝ) (M : ℕ) {w : ℂ} (hw : w.re < 0) :
    DifferentiableAt ℂ (reflectionHeadFactor τ M) w := by
  unfold reflectionHeadFactor
  have hΓ : Gammaℝ (1 - (((1 : ℂ) + (τ : ℂ) * I) + w)) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hadd : DifferentiableAt ℂ (fun w : ℂ => ((1 : ℂ) + (τ : ℂ) * I) + w) w :=
    differentiableAt_const _ |>.add differentiableAt_id
  exact ((zetaChi_analyticAt hΓ).differentiableAt.comp w hadd).mul
    ((differentiableAt_dualPartialSum M _).comp w hadd)

theorem differentiableAt_reflectionTailFactor (τ : ℝ) (M : ℕ) {w : ℂ} (hw : w.re < -1) :
    DifferentiableAt ℂ (reflectionTailFactor τ M) w := by
  unfold reflectionTailFactor
  have hΓ : Gammaℝ (1 - (((1 : ℂ) + (τ : ℂ) * I) + w)) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hadd : DifferentiableAt ℂ (fun w : ℂ => ((1 : ℂ) + (τ : ℂ) * I) + w) w :=
    differentiableAt_const _ |>.add differentiableAt_id
  have hζ : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (1 - (((1 : ℂ) + (τ : ℂ) * I) + w))) w := by
    have hne : (1 - (((1 : ℂ) + (τ : ℂ) * I) + w)) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact (differentiableAt_riemannZeta hne).comp w ((differentiableAt_const _).sub hadd)
  exact ((zetaChi_analyticAt hΓ).differentiableAt.comp w hadd).mul
    (hζ.sub ((differentiableAt_dualPartialSum M _).comp w hadd))

/-- Polynomial bound of the head factor on `−3/2 ≤ Re w ≤ −1/2`. -/
theorem norm_reflectionHeadFactor_le {j : ℕ} (hj : 1 ≤ j) {Cχ : ℝ} {Kχ : ℕ}
    (hχ : ∀ σ t : ℝ, 1 / 2 - 2 * j ≤ σ → σ ≤ 1 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ Kχ) (hCχ : 0 ≤ Cχ)
    (τ : ℝ) (M : ℕ) {u : ℝ} (hu1 : -(3 / 2) ≤ u) (hu2 : u ≤ -(1 / 2)) (v : ℝ) :
    ‖reflectionHeadFactor τ M ((u : ℂ) + (v : ℂ) * I)‖ ≤
      (Cχ * M) * ((1 + |τ|) + |v|) ^ Kχ := by
  unfold reflectionHeadFactor
  rw [one_add_mul_I_add_point, norm_mul]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 := hχ (1 + u) (τ + v) (by linarith) (by linarith)
  have h2 := norm_dualPartialSum_le (M := M) (z := ((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)
    (by simp; linarith)
  have h3 : (1 + |τ + v|) ^ Kχ ≤ ((1 + |τ|) + |v|) ^ Kχ :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le τ v]) Kχ
  calc ‖zetaChi (((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ *
        ‖dualPartialSum M (((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖
      ≤ (Cχ * (1 + |τ + v|) ^ Kχ) * M := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Cχ * ((1 + |τ|) + |v|) ^ Kχ) * M := by gcongr
    _ = (Cχ * M) * ((1 + |τ|) + |v|) ^ Kχ := by ring

/-- Polynomial bound of the tail factor on `−1/2 − 2j ≤ Re w ≤ −3/2`. -/
theorem norm_reflectionTailFactor_le {j : ℕ} {Cχ : ℝ} {Kχ : ℕ}
    (hχ : ∀ σ t : ℝ, 1 / 2 - 2 * j ≤ σ → σ ≤ 1 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ Kχ) (hCχ : 0 ≤ Cχ)
    (τ : ℝ) (M : ℕ) {u : ℝ} (hu1 : -(1 / 2) - 2 * j ≤ u) (hu2 : u ≤ -(3 / 2)) (v : ℝ) :
    ‖reflectionTailFactor τ M ((u : ℂ) + (v : ℂ) * I)‖ ≤
      (Cχ * (3 + M)) * ((1 + |τ|) + |v|) ^ Kχ := by
  unfold reflectionTailFactor
  rw [one_add_mul_I_add_point, norm_mul]
  have h1 := hχ (1 + u) (τ + v) (by linarith) (by linarith)
  have h2 := norm_dualPartialSum_le (M := M) (z := ((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)
    (by simp; linarith)
  have hζ := norm_riemannZeta_le_three (z := 1 - (((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I))
    (by simp; linarith)
  have h3 : (1 + |τ + v|) ^ Kχ ≤ ((1 + |τ|) + |v|) ^ Kχ :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le τ v]) Kχ
  have hdiff : ‖riemannZeta (1 - (((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)) -
      dualPartialSum M (((1 + u : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ ≤ 3 + M :=
    (norm_sub_le _ _).trans (add_le_add hζ h2)
  calc _ ≤ (Cχ * (1 + |τ + v|) ^ Kχ) * (3 + M) :=
        mul_le_mul h1 hdiff (norm_nonneg _) (by positivity)
    _ ≤ (Cχ * ((1 + |τ|) + |v|) ^ Kχ) * (3 + M) := by gcongr
    _ = (Cχ * (3 + M)) * ((1 + |τ|) + |v|) ^ Kχ := by ring

/-- The head integral on the critical line `Re(s + w) = 1/2`. -/
theorem norm_integral_reflectionHead_le {N : ℝ} (hN : 1 ≤ N) (τ : ℝ) (M : ℕ) :
    ‖∫ v : ℝ, reflectionHeadFactor τ M (((-(1 / 2) : ℝ) : ℂ) + (v : ℂ) * I) *
        dyadicMellinWeight N (((-(1 / 2) : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      4 * Real.exp (1 / 4) * N ^ (-(1 / 2) : ℝ) *
        ∫ v : ℝ, Real.exp (-(v ^ 2)) *
          ‖dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ := by
  have hN0 : 0 < N := by linarith
  set g : ℝ → ℝ := fun v => Real.exp (-(v ^ 2)) *
    ‖dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ with hg
  have hgint : Integrable g := by
    have hcont : Continuous g := by
      simp only [hg]
      refine (by fun_prop : Continuous fun v : ℝ => Real.exp (-(v ^ 2))).mul ?_
      refine continuous_norm.comp ?_
      refine continuous_iff_continuousAt.2 fun v => ?_
      exact ContinuousAt.comp (g := dualPartialSum M)
        (f := fun v : ℝ => ((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I) (x := v)
        (differentiableAt_dualPartialSum M _).continuousAt (by fun_prop)
    refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (M : ℝ)) hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hg]; positivity)]
    simp only [hg]
    have := norm_dualPartialSum_le (M := M)
      (z := ((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I) (by simp; norm_num)
    rw [neg_one_mul]
    nlinarith [Real.exp_pos (-(v ^ 2))]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
    (hgint.const_mul _) (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [norm_mul]
  unfold reflectionHeadFactor
  rw [one_add_mul_I_add_point, norm_mul]
  have hχ : ‖zetaChi (((1 + -(1 / 2) : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ = 1 := by
    have := norm_zetaChi_critical (τ + v)
    rw [show (((1 + -(1 / 2) : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring]
    exact this
  have hW := norm_dyadicMellinWeight_le hN0 (by norm_num : (-(1 / 2) : ℝ) < 0) v
  have hpt : (((1 + -(1 / 2) : ℝ)) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hχ, one_mul, hpt]
  have habs : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
  rw [habs, show (-(1 / 2) : ℝ) ^ 2 = 1 / 4 by norm_num] at hW
  calc ‖dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ *
        ‖dyadicMellinWeight N (((-(1 / 2) : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ ‖dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ *
          ((2 * N ^ (-(1 / 2) : ℝ) * (Real.exp (1 / 4) / (1 / 2))) * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hW (norm_nonneg _)
    _ = 4 * Real.exp (1 / 4) * N ^ (-(1 / 2) : ℝ) * (Real.exp (-(v ^ 2)) *
          ‖dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖) := by ring

/-- The tail integral on the deep line `Re(s + w) = 1/2 − 2j`. -/
theorem norm_integral_reflectionTail_le {N : ℝ} (hN : 1 ≤ N) {j : ℕ} (hj : 1 ≤ j) (τ : ℝ)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖∫ v : ℝ, reflectionTailFactor τ M (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I) *
        dyadicMellinWeight N (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (2 * (Real.exp ((1 / 2 + 2 * j) ^ 2) / (1 / 2 + 2 * j)) / (2 * j - 1 / 2) *
          ∫ v : ℝ, (1 + |v|) ^ (2 * j) * Real.exp (-v ^ (2 : ℕ))) *
        ((|τ| + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
          N ^ (-(1 / 2) - 2 * j : ℝ))) := by
  have hN0 : 0 < N := by linarith
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set A : ℝ := |τ| + 2 * j + 2 with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg τ]
  set Kw : ℝ := 2 * N ^ (-(1 / 2) - 2 * j : ℝ) * (Real.exp ((1 / 2 + 2 * j) ^ 2) / (1 / 2 + 2 * j))
    with hKw
  set Kt : ℝ := (M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) / (2 * j - 1 / 2) with hKt
  have hint := integrable_shifted_pow_mul_exp_neg_sq 1 (2 * j)
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : ∀ v : ℝ,
      ‖reflectionTailFactor τ M (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I) *
        dyadicMellinWeight N (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (A ^ (2 * j) * Kt * Kw) * ((1 + |v|) ^ (2 * j) * Real.exp (-v ^ (2 : ℕ))) := by
    intro v
    rw [norm_mul]
    unfold reflectionTailFactor
    rw [one_add_mul_I_add_point, norm_mul]
    have hpt : ((1 + (-(1 / 2) - 2 * j) : ℝ) : ℂ) = ((1 / 2 - 2 * j : ℝ) : ℂ) := by
      push_cast; ring
    rw [hpt]
    have hχ := norm_zetaChi_deep_line_le j (τ + v)
    have hz : (((1 / 2 - 2 * j : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I).re < 0 := by simp; linarith
    have htail := norm_riemannZeta_one_sub_sub_dualPartialSum_le hz hM
    have hre : (((1 / 2 - 2 * j : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I).re = 1 / 2 - 2 * j := by simp
    rw [hre, show -(1 / 2 - 2 * (j : ℝ)) = 2 * j - 1 / 2 by ring] at htail
    have hW := norm_dyadicMellinWeight_le hN0 (by linarith : (-(1 / 2) - 2 * j : ℝ) < 0) v
    rw [show |(-(1 / 2) - 2 * (j : ℝ))| = 1 / 2 + 2 * j by
      rw [abs_of_neg (by linarith)]; ring,
      show (-(1 / 2) - 2 * (j : ℝ)) ^ 2 = (1 / 2 + 2 * j) ^ 2 by ring] at hW
    have hpow : (|τ + v| + 2 * j + 2) ^ (2 * j) ≤ A ^ (2 * j) * (1 + |v|) ^ (2 * j) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have := abs_add_le τ v
      rw [hA]
      nlinarith [abs_nonneg v, abs_nonneg τ]
    calc ‖zetaChi (((1 / 2 - 2 * j : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ *
          ‖riemannZeta (1 - (((1 / 2 - 2 * j : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)) -
            dualPartialSum M (((1 / 2 - 2 * j : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ *
          ‖dyadicMellinWeight N (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ (A ^ (2 * j) * (1 + |v|) ^ (2 * j)) * Kt * (Kw * Real.exp (-(v ^ 2))) := by
          have hKt0 : 0 ≤ Kt := div_nonneg (by positivity) (by linarith)
          refine mul_le_mul (mul_le_mul (hχ.trans hpow) htail (norm_nonneg _) (by positivity))
            hW (norm_nonneg _) (mul_nonneg (by positivity) hKt0)
      _ = (A ^ (2 * j) * Kt * Kw) * ((1 + |v|) ^ (2 * j) * Real.exp (-v ^ (2 : ℕ))) := by ring
  calc ∫ v : ℝ, ‖reflectionTailFactor τ M (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I) *
        dyadicMellinWeight N (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ ∫ v : ℝ, (A ^ (2 * j) * Kt * Kw) * ((1 + |v|) ^ (2 * j) * Real.exp (-v ^ (2 : ℕ))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
          (hint.const_mul _) (Eventually.of_forall hbound)
    _ = (A ^ (2 * j) * Kt * Kw) * ∫ v : ℝ, (1 + |v|) ^ (2 * j) * Real.exp (-v ^ (2 : ℕ)) :=
        integral_const_mul _ _
    _ = _ := by rw [hKt, hKw]; ring

/-- The shifted pole residue at `s = 1 + iτ` has size `e^{-τ²}/|τ|`. -/
theorem norm_smoothAFEZetaShiftedPoleResidue_one_add {x τ : ℝ} (hx : 0 < x) :
    ‖smoothAFEZetaShiftedPoleResidue ((1 : ℂ) + (τ : ℂ) * I) x‖ = Real.exp (-(τ ^ 2)) / |τ| := by
  unfold smoothAFEZetaShiftedPoleResidue
  have h1s : (1 : ℂ) - ((1 : ℂ) + (τ : ℂ) * I) = (-τ : ℝ) * I := by push_cast; ring
  rw [h1s, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  have hre1 : (((-τ : ℝ) : ℂ) * I).re = 0 := by simp
  have hre2 : ((((-τ : ℝ) : ℂ) * I) ^ (2 : ℕ)).re = -(τ ^ 2) := by
    simp [pow_two, Complex.mul_re]
  have hn : ‖((-τ : ℝ) : ℂ) * I‖ = |τ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  rw [hre1, hre2, hn, Real.rpow_zero, one_mul]

/-- **Jutila's reflection for the smooth dyadic sum.**  For `N ≥ 1`, `τ ≠ 0`, `M ≥ 1`, `j ≥ 1`:
`|H(τ)| ≤ N^{-1/2} ∫ e^{-v²} |∑_{m ≤ M} m^{-1/2+i(τ+v)}| dv
  + C_j (|τ| + 2j + 2)^{2j} M^{1/2−2j} N^{-1/2−2j} + 2e^{-τ²}/|τ|`. -/
theorem exists_norm_dyadicSmoothGram_le {j : ℕ} (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N τ : ℝ) (M : ℕ), 1 ≤ N → τ ≠ 0 → 1 ≤ M →
      ‖dyadicSmoothGram N τ‖ ≤
        N ^ (-(1 / 2) : ℝ) * (∫ v : ℝ, Real.exp (-(v ^ 2)) *
          ‖dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖) +
        C * ((|τ| + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
          N ^ (-(1 / 2) - 2 * j : ℝ))) +
        2 * (Real.exp (-(τ ^ 2)) / |τ|) := by
  obtain ⟨Cχ, Kχ, hCχ, hχ⟩ := exists_norm_zetaChi_strip_le_global j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set Ij : ℝ := ∫ v : ℝ, (1 + |v|) ^ (2 * j) * Real.exp (-v ^ (2 : ℕ)) with hIj
  have hIj0 : 0 ≤ Ij := integral_nonneg fun v => by positivity
  set Cb : ℝ := 2 * (Real.exp ((1 / 2 + 2 * j) ^ 2) / (1 / 2 + 2 * j)) / (2 * j - 1 / 2) * Ij
    with hCb
  have hCb0 : 0 ≤ Cb := by
    rw [hCb]; exact mul_nonneg (div_nonneg (by positivity) (by linarith)) hIj0
  refine ⟨(1 / (2 * Real.pi)) * Cb, by positivity, ?_⟩
  intro N τ M hN hτ hM
  have hN0 : 0 < N := by linarith
  have hA0 : (0 : ℝ) ≤ 1 + |τ| := by positivity
  rw [dyadicSmoothGram_eq_dualIntegral hN0 hτ]
  -- split the dual integrand by the functional equation
  have hsplit : ∀ v : ℝ,
      riemannZeta (((1 : ℂ) + (τ : ℂ) * I) + (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I)) *
          dyadicMellinWeight N (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) =
        reflectionHeadFactor τ M (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) *
            dyadicMellinWeight N (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) +
          reflectionTailFactor τ M (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) *
            dyadicMellinWeight N (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) := by
    intro v
    unfold reflectionHeadFactor reflectionTailFactor
    set z : ℂ := ((1 : ℂ) + (τ : ℂ) * I) + (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) with hz
    have hzre : z.re = -(1 / 2) := by rw [hz]; simp; norm_num
    have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre
    have hz1 : z ≠ 1 := by intro h; rw [h] at hzre; simp at hzre; norm_num at hzre
    have hΓ : Gammaℝ (1 - z) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [hzre]; norm_num)
    rw [zeta_eq_zetaChi_mul hz0 hz1 hΓ]
    ring
  have hcontH : Continuous fun v : ℝ =>
      reflectionHeadFactor τ M (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) := by
    refine continuous_iff_continuousAt.2 fun v => ?_
    exact ContinuousAt.comp (g := reflectionHeadFactor τ M)
      (f := fun v : ℝ => ((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) (x := v)
      (differentiableAt_reflectionHeadFactor τ M (by norm_num)).continuousAt (by fun_prop)
  have hcontT : Continuous fun v : ℝ =>
      reflectionTailFactor τ M (((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) := by
    refine continuous_iff_continuousAt.2 fun v => ?_
    exact ContinuousAt.comp (g := reflectionTailFactor τ M)
      (f := fun v : ℝ => ((-(3 / 2) : ℝ) : ℂ) + (v : ℂ) * I) (x := v)
      (differentiableAt_reflectionTailFactor τ M (by norm_num)).continuousAt (by fun_prop)
  have hintH := integrable_mul_dyadicMellinWeight (g := reflectionHeadFactor τ M) hN0
    (by norm_num : (-(3 / 2) : ℝ) < 0) hA0 (by positivity) hcontH
    (fun v => norm_reflectionHeadFactor_le hj hχ hCχ τ M le_rfl (by norm_num) v)
  have hintT := integrable_mul_dyadicMellinWeight (g := reflectionTailFactor τ M) hN0
    (by norm_num : (-(3 / 2) : ℝ) < 0) hA0 (by positivity) hcontT
    (fun v => norm_reflectionTailFactor_le hχ hCχ τ M (by linarith) le_rfl v)
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hintH hintT]
  -- shift the head to `Re w = −1/2` and the tail to `Re w = −1/2 − 2j`
  have hshiftH := integral_mul_dyadicMellinWeight_shift (g := reflectionHeadFactor τ M)
    (a := -(3 / 2)) (b := -(1 / 2)) hN (by norm_num) (by norm_num) hA0 (by positivity)
    (fun w h1 h2 => differentiableAt_reflectionHeadFactor τ M (by linarith))
    (fun u v h1 h2 => norm_reflectionHeadFactor_le hj hχ hCχ τ M h1 h2 v)
  have hshiftT := integral_mul_dyadicMellinWeight_shift (g := reflectionTailFactor τ M)
    (a := -(1 / 2) - 2 * j) (b := -(3 / 2)) hN (by linarith) (by norm_num) hA0 (by positivity)
    (fun w h1 h2 => differentiableAt_reflectionTailFactor τ M (by linarith))
    (fun u v h1 h2 => norm_reflectionTailFactor_le hχ hCχ τ M h1 h2 v)
  rw [← hshiftH, hshiftT]
  have hH := norm_integral_reflectionHead_le hN τ M
  have hT := norm_integral_reflectionTail_le hN hj τ hM
  have hρ2 := norm_smoothAFEZetaShiftedPoleResidue_one_add (x := 2 * N) (τ := τ) (by positivity)
  have hρ1 := norm_smoothAFEZetaShiftedPoleResidue_one_add (x := N) (τ := τ) hN0
  have hconst : 1 / (2 * Real.pi) * (4 * Real.exp (1 / 4)) ≤ 1 := by
    have he : Real.exp (1 / 4) ≤ 3 / 2 := by
      have := Real.exp_one_lt_d9
      have h14 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      by_contra h
      rw [not_le] at h
      have h4 := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
      rw [h14] at h4
      norm_num at h4
      linarith
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  set IH := ∫ v : ℝ, reflectionHeadFactor τ M (((-(1 / 2) : ℝ) : ℂ) + (v : ℂ) * I) *
    dyadicMellinWeight N (((-(1 / 2) : ℝ) : ℂ) + (v : ℂ) * I)
  set IT := ∫ v : ℝ, reflectionTailFactor τ M (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I) *
    dyadicMellinWeight N (((-(1 / 2) - 2 * j : ℝ) : ℂ) + (v : ℂ) * I)
  set J := ∫ v : ℝ, Real.exp (-(v ^ 2)) *
    ‖dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖
  have hJ0 : 0 ≤ J := integral_nonneg fun v => by positivity
  have hpi : ‖(((1 / (2 * Real.pi)) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖(((1 / (2 * Real.pi)) : ℝ) : ℂ) * (IH + IT) +
        (smoothAFEZetaShiftedPoleResidue ((1 : ℂ) + (τ : ℂ) * I) (2 * N) -
          smoothAFEZetaShiftedPoleResidue ((1 : ℂ) + (τ : ℂ) * I) N)‖
      ≤ 1 / (2 * Real.pi) * (‖IH‖ + ‖IT‖) +
          (Real.exp (-(τ ^ 2)) / |τ| + Real.exp (-(τ ^ 2)) / |τ|) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, hpi]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
        · refine (norm_sub_le _ _).trans ?_
          rw [hρ2, hρ1]
    _ ≤ 1 / (2 * Real.pi) * (4 * Real.exp (1 / 4) * N ^ (-(1 / 2) : ℝ) * J +
          Cb * ((|τ| + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
            N ^ (-(1 / 2) - 2 * j : ℝ)))) +
          2 * (Real.exp (-(τ ^ 2)) / |τ|) := by
        have hT' : ‖IT‖ ≤ Cb * ((|τ| + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
            N ^ (-(1 / 2) - 2 * j : ℝ))) := by
          rw [hCb]; exact hT
        have := mul_le_mul_of_nonneg_left (add_le_add hH hT')
          (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
        linarith
    _ ≤ N ^ (-(1 / 2) : ℝ) * J +
          1 / (2 * Real.pi) * Cb * ((|τ| + 2 * j + 2) ^ (2 * j) *
            ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) * N ^ (-(1 / 2) - 2 * j : ℝ))) +
          2 * (Real.exp (-(τ ^ 2)) / |τ|) := by
        have hNJ : 0 ≤ N ^ (-(1 / 2) : ℝ) * J := by positivity
        have h1 := mul_le_mul_of_nonneg_right hconst hNJ
        linarith

end

end RHTower
