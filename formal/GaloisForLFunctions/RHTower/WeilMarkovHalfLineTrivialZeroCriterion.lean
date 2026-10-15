import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.RHTower.WeilMarkovOddPositivity

/-!
# The Riemann hypothesis as a half-line inequality with trivial-zero squares

For a real `C²` test `f` supported in `[ε, ∞)` (`ε > 0`) let
* `M(f) = A(f) − P(f)` be the archimedean-minus-prime form (`markovEnergy`), with
  `A(f) = (1/2π) ∫ |f̂|² Ω` and `P(f) = Σ_n Λ(n) n^{−1/2} (∫ f(t) f(t − log n) + ∫ f(t) f(t + log n))`;
* `Σ_k (∫ f(x) e^{−(2k+½)x} dx)²` be the squares of its Laplace values at the reflected trivial zeros;
* `Π(f) = Σ_n Λ(n) n^{−1/2} ∫ f(t) f(log n − t) dt` be its product-prime pairing.

**Theorem** (`riemannHypothesis_iff_forall_halfLine_trivialZeroSquare_nonneg`).
The Riemann hypothesis holds if and only if `M(f) + Σ_k (∫ f e^{−(2k+½)x})² + Π(f) ≥ 0` for every such
`f`. Equivalently (`riemannHypothesis_iff_forall_halfLine_archForm_trivialZeroSquare_nonneg`), the
ratio pairing `P(f)` is at most `A(f) + Σ_k (∫ f e^{−(2k+½)x})² + Π(f)` on all half-line tests.

The left-hand side is half the archimedean-minus-prime form of the odd extension `f − f̃`
(`markovEnergy_oddExtension_eq`). The direction `RH ⟹` is
`halfLine_markovEnergy_add_nonneg_of_riemannHypothesis`. For the converse, take an even pole-free
test `u` supported in `[−b, b]` with negative Weil energy and its odd shifts
`O_h(x) = (u(x − h/2) − u(x + h/2))/2`; for `h > 2b`, `O_h = f − f̃` with `f = u(· − h/2)/2`
supported in `[h/2 − b, ∞)`. Averaging `W(O_h)` against the translated Riemann kernel
`Φ(h − h₀)`, whose transform `e^{iγh₀} Ξ(γ)` still vanishes at every zero, gives
`∫ W(O_h) Φ(h − h₀) dh = ½ (∫ Φ) W(u) < 0` for every `h₀` (`integral_W_oddShift_mul_weight`).
The part of this integral over `h ≤ 2b` is at most `K e^{−2h₀}` because `Φ` decays faster than
any exponential, so for large `h₀` some `h > 2b` has `W(O_h) < 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## Averaging the odd shifts against a general weight -/

/-- **The averaging identity for a weight annihilating the zeros.** If `g` is continuous,
`‖g(h)‖ e^{|h|/2} ≤ C e^{−|h|/2}`, and `∫ g(h) e^{±iγ_ρ h} dh = 0` at every zero, then
`∫ W(O_h, O_h) g(h) dh = ½ (∫ g) W(u, u)`. -/
theorem integral_W_oddShift_mul_weight {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hcpt : HasCompactSupport u) {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ} (hC0 : 0 ≤ C)
    (hgb : ∀ h : ℝ, ‖g h‖ * Real.exp (|h| / 2) ≤ C * Real.exp (-(1 / 2 * |h|)))
    (hg0 : ∀ ρ : zetaZeroConfig.carrier,
      (∫ h : ℝ, g h * cexp (I * gammaOf (ρ : ℂ) * h)) = 0 ∧
        (∫ h : ℝ, g h * cexp (I * (-gammaOf (ρ : ℂ)) * h)) = 0) :
    Integrable (fun h : ℝ => zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
        (fun x => (oddShift u h x : ℂ)) * g h) ∧
      ∫ h : ℝ, zetaZeroConfig.W (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ)) *
          g h =
        (∫ h : ℝ, g h) / 2 * zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) := by
  haveI : Countable zetaZeroConfig.carrier := WeilConditional.countable_carrier.to_subtype
  set S : zetaZeroConfig.carrier → ℂ := fun ρ =>
    zetaZeroConfig.Wsummand (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) ρ with hS
  set F : zetaZeroConfig.carrier → ℝ → ℂ := fun ρ h =>
    (2 - cexp (I * gammaOf (ρ : ℂ) * h) - cexp (-(I * gammaOf (ρ : ℂ) * h))) / 4 * S ρ * g h
    with hF
  have hSs : Summable fun ρ => ‖S ρ‖ := summable_norm_Wsummand_ofReal hu hcpt
  have hK : Integrable fun h : ℝ => C * Real.exp (-(1 / 2 * |h|)) :=
    (integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  have hFb : ∀ ρ h, ‖F ρ h‖ ≤ ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) := by
    intro ρ h
    have hw := norm_oddShiftWeight_le (abs_im_gammaOf_le ρ) h
    simp only [hF]
    rw [norm_mul, norm_mul]
    calc ‖(2 - cexp (I * gammaOf ↑ρ * ↑h) - cexp (-(I * gammaOf ↑ρ * ↑h))) / 4‖ * ‖S ρ‖ * ‖g h‖
        ≤ Real.exp (|h| / 2) * ‖S ρ‖ * ‖g h‖ := by gcongr
      _ = ‖S ρ‖ * (‖g h‖ * Real.exp (|h| / 2)) := by ring
      _ ≤ ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) :=
          mul_le_mul_of_nonneg_left (hgb h) (norm_nonneg _)
  have hFc : ∀ ρ, Continuous (F ρ) := fun ρ => by
    simp only [hF]
    exact ((continuous_const.sub (by fun_prop)).sub (by fun_prop)).div_const _
      |>.mul continuous_const |>.mul hg
  have hFi : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (hK.const_mul ‖S ρ‖).mono' (hFc ρ).aestronglyMeasurable
      (Eventually.of_forall fun h => hFb ρ h)
  have hpt : ∀ h : ℝ, zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ)) * g h = ∑' ρ, F ρ h := by
    intro h
    unfold ZeroConfig.W
    rw [← tsum_mul_right]
    refine tsum_congr fun ρ => ?_
    simp only [hF, hS]
    rw [Wsummand_oddShift hu.continuous hcpt h]
  have hM : ∀ ρ h, ‖F ρ h‖ ≤ ‖S ρ‖ * C := fun ρ h =>
    (hFb ρ h).trans (mul_le_mul_of_nonneg_left (by
      have := Real.exp_le_one_iff.mpr (show -(1 / 2 * |h|) ≤ 0 by
        have := abs_nonneg h; linarith)
      nlinarith) (norm_nonneg _))
  have hcont : Continuous fun h => ∑' ρ, F ρ h :=
    continuous_tsum hFc (hSs.mul_right C) hM
  have hint : Integrable fun h => ∑' ρ, F ρ h := by
    refine (hK.const_mul (∑' ρ, ‖S ρ‖)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun h => ?_)
    have hs : Summable fun ρ => ‖F ρ h‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => hFb ρ h)
        (hSs.mul_right _)
    calc ‖∑' ρ, F ρ h‖ ≤ ∑' ρ, ‖F ρ h‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ, ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) :=
          Summable.tsum_le_tsum (fun ρ => hFb ρ h) hs (hSs.mul_right _)
      _ = (∑' ρ, ‖S ρ‖) * (C * Real.exp (-(1 / 2 * |h|))) := tsum_mul_right
  have hgi : Integrable g :=
    hK.mono' hg.aestronglyMeasurable (Eventually.of_forall fun h => by
      have := hgb h
      have he : 1 ≤ Real.exp (|h| / 2) := Real.one_le_exp (by positivity)
      nlinarith [norm_nonneg (g h)])
  have hEi : ∀ ρ : zetaZeroConfig.carrier, ∀ s : ℂ, (s = gammaOf (ρ : ℂ) ∨ s = -gammaOf (ρ : ℂ)) →
      Integrable fun h : ℝ => g h * cexp (I * s * h) := by
    intro ρ s hs
    refine hK.mono' (hg.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun h => ?_)
    obtain ⟨e1, e2⟩ := norm_cexp_I_mul_le (abs_im_gammaOf_le ρ) h
    rw [norm_mul]
    have he : ‖cexp (I * s * h)‖ ≤ Real.exp (|h| / 2) := by
      rcases hs with rfl | rfl
      · exact e1
      · rw [show I * -gammaOf (ρ : ℂ) * (h : ℂ) = -(I * gammaOf (ρ : ℂ) * h) by ring]; exact e2
    calc ‖g h‖ * ‖cexp (I * s * h)‖ ≤ ‖g h‖ * Real.exp (|h| / 2) :=
          mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ C * Real.exp (-(1 / 2 * |h|)) := hgb h
  have hterm : ∀ ρ : zetaZeroConfig.carrier, ∫ h, F ρ h = S ρ * ((∫ h : ℝ, g h) / 2) := by
    intro ρ
    obtain ⟨p1, p2⟩ := hg0 ρ
    have i1 := hEi ρ _ (Or.inl rfl)
    have i2 := hEi ρ _ (Or.inr rfl)
    have e : (fun h => F ρ h) = fun h => S ρ / 4 * (2 * g h -
        g h * cexp (I * gammaOf (ρ : ℂ) * h) - g h * cexp (I * (-gammaOf (ρ : ℂ)) * h)) := by
      funext h
      simp only [hF]
      rw [show I * -gammaOf (ρ : ℂ) * (h : ℂ) = -(I * gammaOf (ρ : ℂ) * h) by ring]
      ring
    have j1 : Integrable fun h : ℝ => 2 * g h := hgi.const_mul 2
    have j2 : Integrable fun h : ℝ => 2 * g h - g h * cexp (I * gammaOf (ρ : ℂ) * h) := j1.sub i1
    rw [e, integral_const_mul, integral_sub j2 i2, integral_sub j1 i1, integral_const_mul, p1, p2]
    ring
  refine ⟨?_, ?_⟩
  · exact hint.congr (Eventually.of_forall fun h => (hpt h).symm)
  · rw [show (fun h : ℝ => zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
        (fun x => (oddShift u h x : ℂ)) * g h) = fun h => ∑' ρ, F ρ h from funext hpt]
    rw [← integral_tsum_of_summable_integral_norm hFi]
    · rw [tsum_congr hterm, tsum_mul_right]
      unfold ZeroConfig.W
      ring
    · refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun ρ => ?_) ((hSs.mul_right (∫ h, C * Real.exp (-(1 / 2 * |h|)))))
      calc ∫ h, ‖F ρ h‖ ≤ ∫ h, ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) :=
            integral_mono (hFi ρ).norm (hK.const_mul _) (fun h => hFb ρ h)
        _ = ‖S ρ‖ * ∫ h, C * Real.exp (-(1 / 2 * |h|)) := integral_const_mul _ _

/-! ## The translated Riemann kernel -/

/-- The translated kernel `Φ(· − h₀)` satisfies the weight bound with constant `C e^{|h₀|}`. -/
theorem exists_riemannPhiKernel_shift_weight_bound (h₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, ‖riemannPhiKernel (h - h₀)‖ * Real.exp (|h| / 2) ≤
      C * Real.exp (-(1 / 2 * |h|)) := by
  obtain ⟨C, hC0, hCb⟩ := exists_riemannPhiKernel_weight_bound
  refine ⟨C * Real.exp |h₀|, by positivity, fun h => ?_⟩
  have h1 := hCb (h - h₀)
  have htri : |h| ≤ |h - h₀| + |h₀| := by
    calc |h| = |(h - h₀) + h₀| := by ring_nf
      _ ≤ |h - h₀| + |h₀| := abs_add_le _ _
  have e1 : Real.exp (|h| / 2) ≤ Real.exp (|h - h₀| / 2) * Real.exp (|h₀| / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-(1 / 2 * |h - h₀|)) * Real.exp (|h₀| / 2) ≤
      Real.exp |h₀| * Real.exp (-(1 / 2 * |h|)) := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  calc ‖riemannPhiKernel (h - h₀)‖ * Real.exp (|h| / 2)
      ≤ ‖riemannPhiKernel (h - h₀)‖ * (Real.exp (|h - h₀| / 2) * Real.exp (|h₀| / 2)) :=
        mul_le_mul_of_nonneg_left e1 (norm_nonneg _)
    _ = (‖riemannPhiKernel (h - h₀)‖ * Real.exp (|h - h₀| / 2)) * Real.exp (|h₀| / 2) := by ring
    _ ≤ (C * Real.exp (-(1 / 2 * |h - h₀|))) * Real.exp (|h₀| / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = C * (Real.exp (-(1 / 2 * |h - h₀|)) * Real.exp (|h₀| / 2)) := by ring
    _ ≤ C * (Real.exp |h₀| * Real.exp (-(1 / 2 * |h|))) := mul_le_mul_of_nonneg_left e2 hC0
    _ = C * Real.exp |h₀| * Real.exp (-(1 / 2 * |h|)) := by ring

/-- Translating the kernel multiplies its Fourier–Laplace transform by `e^{ish₀}`. -/
theorem integral_riemannPhiKernel_shift_mul_cexp (h₀ : ℝ) (s : ℂ) :
    ∫ h : ℝ, riemannPhiKernel (h - h₀) * cexp (I * s * h) =
      cexp (I * s * h₀) * ∫ t : ℝ, riemannPhiKernel t * cexp (I * s * t) := by
  have key := integral_sub_right_eq_self (μ := volume)
    (fun t : ℝ => riemannPhiKernel t * cexp (I * s * ((t + h₀ : ℝ) : ℂ))) h₀
  simp only [sub_add_cancel] at key
  rw [key, ← integral_const_mul]
  congr 1
  funext t
  push_cast
  rw [show I * s * ((t : ℂ) + h₀) = I * s * t + I * s * h₀ by ring, Complex.exp_add]
  ring

/-- The translated kernel still annihilates every zero. -/
theorem integral_riemannPhiKernel_shift_gammaOf (h₀ : ℝ) (ρ : zetaZeroConfig.carrier) :
    (∫ h : ℝ, riemannPhiKernel (h - h₀) * cexp (I * gammaOf (ρ : ℂ) * h)) = 0 ∧
      (∫ h : ℝ, riemannPhiKernel (h - h₀) * cexp (I * (-gammaOf (ρ : ℂ)) * h)) = 0 := by
  obtain ⟨p1, p2⟩ := paperFT_riemannPhiKernel_gammaOf ρ
  have q1 : ∫ t : ℝ, riemannPhiKernel t * cexp (I * gammaOf (ρ : ℂ) * t) = 0 := p1
  have q2 : ∫ t : ℝ, riemannPhiKernel t * cexp (I * (-gammaOf (ρ : ℂ)) * t) = 0 := p2
  refine ⟨?_, ?_⟩
  · rw [integral_riemannPhiKernel_shift_mul_cexp, q1, mul_zero]
  · rw [integral_riemannPhiKernel_shift_mul_cexp, q2, mul_zero]

/-! ## The half-line witness -/

/-- **Without RH some half-line test has negative odd Markov form.** There are a real `C²`
compactly supported `f` and `ε > 0` with `f = 0` on `(−∞, ε)` and `M(f − f̃) < 0`. -/
theorem exists_halfLine_markovEnergy_oddExt_neg_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ (f : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ 0 < ε ∧
      (∀ x, x < ε → f x = 0) ∧ markovEnergy (fun x => ((f x - f (-x) : ℝ) : ℂ)) < 0 := by
  haveI : Countable zetaZeroConfig.carrier := WeilConditional.countable_carrier.to_subtype
  obtain ⟨u, hu, hcpt, heven, hp, hneg⟩ :=
    exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  have hp' : paperFT (fun x => (u x : ℂ)) (-I / 2) = 0 := by
    rw [neg_div, paperFT_ofReal_neg_of_even heven]; exact hp
  -- a support radius
  obtain ⟨b₀, hb₀⟩ := hcpt.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set b : ℝ := max b₀ 0 with hbdef
  have hb0 : 0 ≤ b := le_max_right _ _
  have hsupp : ∀ x, b < |x| → u x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hb₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    have : b₀ ≤ b := le_max_left _ _
    linarith
  -- on odd shifts the Markov energy is the Weil energy
  have hmarkov : ∀ h : ℝ, markovEnergy (fun x => (oddShift u h x : ℂ)) =
      (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ))).re := by
    intro h
    have hd : ContDiff ℝ 2 fun x => (oddShift u h x : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_oddShift hu h)
    have hc : HasCompactSupport fun x => (oddShift u h x : ℂ) :=
      (hasCompactSupport_oddShift hcpt h).comp_left Complex.ofReal_zero
    rw [markovEnergy_eq_W_sub hd hc, weilPoleTerm_weilTest_eq hd.continuous hc,
      paperFT_oddShift hu.continuous hcpt, paperFT_oddShift hu.continuous hcpt, hp, hp']
    simp
  -- a single shift beyond the support gives a half-line witness
  have hwit : ∀ h : ℝ, 2 * b < h →
      (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ))).re < 0 →
      ∃ (f : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ 0 < ε ∧
        (∀ x, x < ε → f x = 0) ∧ markovEnergy (fun x => ((f x - f (-x) : ℝ) : ℂ)) < 0 := by
    intro h hh hW
    refine ⟨fun x => u (x - h / 2) / 2, h / 2 - b, ?_, ?_, by linarith, ?_, ?_⟩
    · exact (hu.comp (contDiff_id.sub contDiff_const)).div_const _
    · refine HasCompactSupport.intro (isCompact_Icc (a := h / 2 - b) (b := h / 2 + b))
        fun x hx => ?_
      have hbx : b < |x - h / 2| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      show u (x - h / 2) / 2 = 0
      rw [hsupp _ hbx, zero_div]
    · intro x hx
      have hbx : b < |x - h / 2| := by rw [abs_of_neg (by linarith)]; linarith
      show u (x - h / 2) / 2 = 0
      rw [hsupp _ hbx, zero_div]
    · have hfun : (fun x => ((u (x - h / 2) / 2 - u (-x - h / 2) / 2 : ℝ) : ℂ)) =
          fun x => (oddShift u h x : ℂ) := by
        funext x
        unfold oddShift
        have hr : u (-x - h / 2) = u (x + h / 2) := by
          rw [show -x - h / 2 = -(x + h / 2) by ring, heven]
        rw [hr]
        push_cast
        ring
      show markovEnergy (fun x => ((u (x - h / 2) / 2 - u (-x - h / 2) / 2 : ℝ) : ℂ)) < 0
      rw [hfun, hmarkov]
      exact hW
  by_contra hcon
  have hall : ∀ h : ℝ, 2 * b < h → 0 ≤ (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ))).re := by
    intro h hh
    by_contra hlt
    exact hcon (hwit h hh (not_le.mp hlt))
  -- the uniform growth bound of the odd-shift energies
  set S : zetaZeroConfig.carrier → ℂ := fun ρ =>
    zetaZeroConfig.Wsummand (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) ρ with hS
  have hSs : Summable fun ρ => ‖S ρ‖ := summable_norm_Wsummand_ofReal hu hcpt
  set K₁ : ℝ := ∑' ρ, ‖S ρ‖ with hK₁
  have hK₁0 : 0 ≤ K₁ := tsum_nonneg fun _ => norm_nonneg _
  have hWb : ∀ h : ℝ, ‖zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ))‖ ≤ Real.exp (|h| / 2) * K₁ := by
    intro h
    unfold ZeroConfig.W
    have hs : Summable fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand
        (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ)) ρ‖ :=
      summable_norm_Wsummand_ofReal (contDiff_oddShift hu h) (hasCompactSupport_oddShift hcpt h)
    have hterm : ∀ ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand
        (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ)) ρ‖ ≤
        Real.exp (|h| / 2) * ‖S ρ‖ := by
      intro ρ
      rw [Wsummand_oddShift hu.continuous hcpt h, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_oddShiftWeight_le (abs_im_gammaOf_le ρ) h)
        (norm_nonneg _)
    calc ‖∑' ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand (fun x => (oddShift u h x : ℂ))
          (fun x => (oddShift u h x : ℂ)) (ρ : ℂ)‖
        ≤ ∑' ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand (fun x => (oddShift u h x : ℂ))
          (fun x => (oddShift u h x : ℂ)) (ρ : ℂ)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : zetaZeroConfig.carrier, Real.exp (|h| / 2) * ‖S ρ‖ :=
          Summable.tsum_le_tsum hterm hs (hSs.mul_left _)
      _ = Real.exp (|h| / 2) * K₁ := tsum_mul_left
  -- the kernel decays like `e^{−2|t|}`
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_riemannPhiKernel_le_exp (B := 2) (by norm_num)
  have hΦr : ∀ t : ℝ, riemannKernelReal t ≤ C₂ * Real.exp (-(2 * |t|)) := by
    intro t
    have := hC₂ t
    rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (riemannKernelReal_pos t).le] at this
  -- the target value
  set η : ℝ := -((∫ h, riemannKernelReal h) / 2 *
    (zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ))).re) with hη
  have hηpos : 0 < η := by
    have := integral_riemannKernelReal_pos
    rw [hη]
    nlinarith [mul_neg_of_pos_of_neg (show 0 < (∫ h, riemannKernelReal h) / 2 by positivity) hneg]
  -- the dominating profile on `h ≤ 2b`
  set I₂ : ℝ := ∫ h : ℝ, Real.exp (-(3 / 2 * |h - 2 * b|)) with hI₂
  have hI₂i : Integrable fun h : ℝ => Real.exp (-(3 / 2 * |h - 2 * b|)) :=
    (integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 2)).comp_sub_right (2 * b)
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun _ => (Real.exp_pos _).le
  set T : ℝ := K₁ * C₂ * Real.exp b * I₂ with hT
  have hT0 : 0 ≤ T := by positivity
  set h₀ : ℝ := 2 * b + max 0 (Real.log (2 * (T + 1) / η)) / 2 with hh₀
  have hh₀b : 2 * b ≤ h₀ := by
    have := le_max_left 0 (Real.log (2 * (T + 1) / η)); rw [hh₀]; linarith
  have hdecay : T * Real.exp (-(2 * (h₀ - 2 * b))) < η := by
    have hq : 0 < 2 * (T + 1) / η := by positivity
    have he : Real.exp (-(2 * (h₀ - 2 * b))) ≤ η / (2 * (T + 1)) := by
      have h1 : 2 * (h₀ - 2 * b) = max 0 (Real.log (2 * (T + 1) / η)) := by rw [hh₀]; ring
      rw [h1]
      calc Real.exp (-max 0 (Real.log (2 * (T + 1) / η)))
          ≤ Real.exp (-Real.log (2 * (T + 1) / η)) :=
            Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
        _ = η / (2 * (T + 1)) := by
            rw [Real.exp_neg, Real.exp_log hq, inv_div]
    have hlt : T * (η / (2 * (T + 1))) < η := by
      rw [show T * (η / (2 * (T + 1))) = η * (T / (2 * (T + 1))) by ring]
      have : T / (2 * (T + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith
    calc T * Real.exp (-(2 * (h₀ - 2 * b))) ≤ T * (η / (2 * (T + 1))) :=
          mul_le_mul_of_nonneg_left he hT0
      _ < η := hlt
  -- the averaging identity at `h₀`
  obtain ⟨C', hC'0, hC'⟩ := exists_riemannPhiKernel_shift_weight_bound h₀
  have hgc : Continuous fun h : ℝ => riemannPhiKernel (h - h₀) :=
    continuous_riemannPhiKernel.comp (continuous_id.sub continuous_const)
  obtain ⟨hI, hval⟩ := integral_W_oddShift_mul_weight hu hcpt hgc hC'0 hC'
    (integral_riemannPhiKernel_shift_gammaOf h₀)
  have hΦsh : (∫ h : ℝ, riemannPhiKernel (h - h₀)) = ((∫ h, riemannKernelReal h : ℝ) : ℂ) := by
    rw [integral_sub_right_eq_self (fun h => riemannPhiKernel h) h₀, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun h => riemannPhiKernel_eq_ofReal h)
  -- real parts
  set R : ℝ → ℝ := fun h => (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
    (fun x => (oddShift u h x : ℂ))).re * riemannKernelReal (h - h₀) with hR
  have hRe : ∀ h : ℝ, RCLike.re (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ)) * riemannPhiKernel (h - h₀)) = R h := by
    intro h
    show (_ * riemannPhiKernel (h - h₀)).re = _
    rw [riemannPhiKernel_eq_ofReal, Complex.re_mul_ofReal]
  have hRi : Integrable R := hI.re.congr (Eventually.of_forall hRe)
  have hRint : ∫ h, R h = -η := by
    have h1 := integral_re hI
    rw [hval, hΦsh] at h1
    rw [← integral_congr_ae (Eventually.of_forall hRe), h1, hη]
    show ((((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 *
      zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ)))).re = _
    rw [show ((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 = (((∫ h, riemannKernelReal h) / 2 : ℝ) : ℂ)
      by push_cast; ring, Complex.re_ofReal_mul]
    ring
  -- the integral over `h > 2b` is nonnegative
  have hpos : 0 ≤ ∫ h in Ioi (2 * b), R h :=
    setIntegral_nonneg measurableSet_Ioi fun h hh =>
      mul_nonneg (hall h hh) (riemannKernelReal_pos _).le
  -- the integral over `h ≤ 2b` is at least `−T e^{−2(h₀−2b)}`
  set G : ℝ → ℝ := fun h => K₁ * C₂ * Real.exp b * Real.exp (-(2 * (h₀ - 2 * b))) *
    Real.exp (-(3 / 2 * |h - 2 * b|)) with hG
  have hGi : Integrable G := hI₂i.const_mul _
  have hlow : ∀ h ∈ Iic (2 * b), -G h ≤ R h := by
    intro h hh
    rw [mem_Iic] at hh
    have hW := hWb h
    have hk := hΦr (h - h₀)
    have hk0 := (riemannKernelReal_pos (h - h₀)).le
    have habs : |(zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
        (fun x => (oddShift u h x : ℂ))).re| ≤ Real.exp (|h| / 2) * K₁ :=
      (Complex.abs_re_le_norm _).trans hW
    have hdist : |h - h₀| = (h₀ - 2 * b) + |h - 2 * b| := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
    have hexp1 : Real.exp (|h| / 2) ≤ Real.exp (|h - 2 * b| / 2) * Real.exp b := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : |h| ≤ |h - 2 * b| + 2 * b := by
        calc |h| = |(h - 2 * b) + 2 * b| := by ring_nf
          _ ≤ |h - 2 * b| + |2 * b| := abs_add_le _ _
          _ = |h - 2 * b| + 2 * b := by rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * b by linarith)]
      linarith
    have hprod : Real.exp (|h| / 2) * Real.exp (-(2 * |h - h₀|)) ≤
        Real.exp b * Real.exp (-(2 * (h₀ - 2 * b))) * Real.exp (-(3 / 2 * |h - 2 * b|)) := by
      calc Real.exp (|h| / 2) * Real.exp (-(2 * |h - h₀|))
          ≤ (Real.exp (|h - 2 * b| / 2) * Real.exp b) * Real.exp (-(2 * |h - h₀|)) :=
            mul_le_mul_of_nonneg_right hexp1 (Real.exp_pos _).le
        _ = Real.exp b * Real.exp (-(2 * (h₀ - 2 * b))) * Real.exp (-(3 / 2 * |h - 2 * b|)) := by
            rw [hdist, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1; ring
    have hRabs : |R h| ≤ G h := by
      simp only [hR, hG]
      rw [abs_mul, abs_of_nonneg hk0]
      calc |(zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
            (fun x => (oddShift u h x : ℂ))).re| * riemannKernelReal (h - h₀)
          ≤ (Real.exp (|h| / 2) * K₁) * (C₂ * Real.exp (-(2 * |h - h₀|))) :=
            mul_le_mul habs hk hk0 (by positivity)
        _ = K₁ * C₂ * (Real.exp (|h| / 2) * Real.exp (-(2 * |h - h₀|))) := by ring
        _ ≤ K₁ * C₂ * (Real.exp b * Real.exp (-(2 * (h₀ - 2 * b))) *
              Real.exp (-(3 / 2 * |h - 2 * b|))) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := by ring
    exact neg_le_of_abs_le hRabs
  have hneg_part : -(T * Real.exp (-(2 * (h₀ - 2 * b)))) ≤ ∫ h in Iic (2 * b), R h := by
    have h1 : ∫ h in Iic (2 * b), -G h ≤ ∫ h in Iic (2 * b), R h :=
      setIntegral_mono_on hGi.neg.integrableOn hRi.integrableOn measurableSet_Iic hlow
    have h2 : ∫ h in Iic (2 * b), G h ≤ ∫ h, G h :=
      setIntegral_le_integral hGi (Eventually.of_forall fun h => by positivity)
    have h3 : ∫ h, G h = T * Real.exp (-(2 * (h₀ - 2 * b))) := by
      simp only [hG]
      rw [integral_const_mul, hT]
      ring
    rw [integral_neg] at h1
    linarith
  have hsplit := integral_add_compl (s := Ioi (2 * b)) measurableSet_Ioi hRi
  rw [compl_Ioi, hRint] at hsplit
  linarith

/-! ## The criterion -/

/-- **The Riemann hypothesis as a half-line inequality.** RH holds if and only if
`M(f) + Σ_k (∫ f e^{−(2k+½)x})² + Σ_n Λ(n) n^{−1/2} (f⋆f)(log n) ≥ 0` for every real `C²`
compactly supported `f` vanishing on `(−∞, ε)` for some `ε > 0`. -/
theorem riemannHypothesis_iff_forall_halfLine_trivialZeroSquare_nonneg :
    RiemannHypothesis ↔ ∀ (f : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 f → HasCompactSupport f → 0 < ε →
      (∀ x, x < ε → f x = 0) →
      0 ≤ markovEnergy (fun x => (f x : ℂ)) + (∑' k : ℕ, trivialZeroMoment f k ^ 2) +
        productPrimePairing f := by
  constructor
  · intro hRH f ε hf hfc hε hsupp
    exact halfLine_markovEnergy_add_nonneg_of_riemannHypothesis hRH hf hfc hε hsupp
  · intro h
    by_contra hRH
    obtain ⟨f, ε, hf, hfc, hε, hsupp, hneg⟩ :=
      exists_halfLine_markovEnergy_oddExt_neg_of_not_riemannHypothesis hRH
    have h1 := h f ε hf hfc hε hsupp
    rw [markovEnergy_oddExtension_eq hf hfc hε hsupp] at hneg
    linarith

/-- **The ratio pairing is dominated on half-line tests.** RH holds if and only if
`P(f) ≤ A(f) + Σ_k (∫ f e^{−(2k+½)x})² + Π(f)` for every real `C²` compactly supported `f`
vanishing on `(−∞, ε)`: the ratio-prime pairing is bounded by the archimedean form, the squares of
the Laplace values at the reflected trivial zeros, and the product-prime pairing. -/
theorem riemannHypothesis_iff_forall_halfLine_archForm_trivialZeroSquare_nonneg :
    RiemannHypothesis ↔ ∀ (f : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 f → HasCompactSupport f → 0 < ε →
      (∀ x, x < ε → f x = 0) →
      primeSum f ≤ archForm f + (∑' k : ℕ, trivialZeroMoment f k ^ 2) + productPrimePairing f := by
  rw [riemannHypothesis_iff_forall_halfLine_trivialZeroSquare_nonneg]
  refine forall_congr' fun f => forall_congr' fun ε => ?_
  refine imp_congr_right fun hf => imp_congr_right fun hfc => ?_
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc]
  constructor
  · intro h₁ hε hs
    have := h₁ hε hs
    linarith
  · intro h₁ hε hs
    have := h₁ hε hs
    linarith

end

end RHTower
