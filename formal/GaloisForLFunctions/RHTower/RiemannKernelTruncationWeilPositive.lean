import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowNyquistExclusion

/-!
# The truncated Riemann kernel is Weil-positive

Riemann's kernel `Φ` lies in the radical of the Weil form: `Φ̂ = Ξ` vanishes at every zero of `ζ`.
Its truncation `Φχ_L` therefore has the zero-side transform `−(T_R)^ − (Φ(1 − χ_R))^` at the
zeros, for every `R ≥ L + 2`, where `T_R = Φ(χ_R − χ_L)` is the edge tail. Strip integration by
parts bounds both transforms by `4(N₀ + N₂)/(1 + |Re z|)²`. The norms of the edge tail are bounded
uniformly in `R`, and those of the outer tail `Φ(1 − χ_R)` tend to `0`. So
`W(Φχ_L, Φχ_L) = lim_R W(T_R, T_R)`. The edge tail is Weil-positive for large `L` with a margin
independent of `R` (`eventually_re_W_edgeTail_pos`), hence so is the truncation:

`Re W(Φχ_L, Φχ_L) > 0` for all large `L`, unconditionally
(`eventually_re_W_truncatedKernel_pos`).

The doubly-exponentially small Weil energy of `Φχ_L` is carried by the edge layer of width
`1/Y`, `Y = 2πe^{2L}`, where the archimedean term `≈ log Y · ‖T‖²` dominates the primes, which
see only `O(1)` integers near `e^{2L}`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

local notation "st" => Real.smoothTransition

/-! ## Derivative bounds for the cutoffs -/

theorem deriv_deriv_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv (deriv st) x = 0 := by
  rcases hx with hx | hx
  · have : deriv st =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact deriv_smoothTransition_eq_zero (Or.inl hy)
    rw [this.deriv_eq, deriv_const]
  · have : deriv st =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact deriv_smoothTransition_eq_zero (Or.inr hy)
    rw [this.deriv_eq, deriv_const]

theorem exists_bound_of_continuous_vanishing {g : ℝ → ℝ} (hg : Continuous g)
    (hz : ∀ x, x < 0 ∨ 1 < x → g x = 0) : ∃ S : ℝ, 0 ≤ S ∧ ∀ x, |g x| ≤ S := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [← Real.norm_eq_abs]; exact (hC x hx).trans (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rw [hz x hx, abs_zero]; exact le_max_right _ _

theorem exists_abs_deriv_smoothTransition_le : ∃ S : ℝ, 0 ≤ S ∧ ∀ x, |deriv st x| ≤ S :=
  exists_bound_of_continuous_vanishing
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
    fun _ hx => deriv_smoothTransition_eq_zero hx

theorem exists_abs_deriv_deriv_smoothTransition_le :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x, |deriv (deriv st) x| ≤ S := by
  have h2 : ContDiff ℝ 2 st := Real.smoothTransition.contDiff
  have hc : Continuous (deriv (deriv st)) := by
    have := h2.iterate_deriv' 1 1
    exact (this.continuous_deriv le_rfl)
  exact exists_bound_of_continuous_vanishing hc fun _ hx => deriv_deriv_smoothTransition_eq_zero hx

/-- First derivative of the edge cutoff. -/
def edgeCutoffD1 (L η u : ℝ) : ℝ :=
  deriv st ((L + η - u) / η) * (-1 / η) * st ((L + η + u) / η) +
    st ((L + η - u) / η) * (deriv st ((L + η + u) / η) * (1 / η))

/-- Second derivative of the edge cutoff. -/
def edgeCutoffD2 (L η u : ℝ) : ℝ :=
  deriv (deriv st) ((L + η - u) / η) * (-1 / η) * (-1 / η) * st ((L + η + u) / η) +
    deriv st ((L + η - u) / η) * (-1 / η) * (deriv st ((L + η + u) / η) * (1 / η)) +
    (deriv st ((L + η - u) / η) * (-1 / η) * (deriv st ((L + η + u) / η) * (1 / η)) +
      st ((L + η - u) / η) * (deriv (deriv st) ((L + η + u) / η) * (1 / η) * (1 / η)))

theorem hasDerivAt_st_comp {g : ℝ → ℝ} (hg : Differentiable ℝ g) {p q : ℝ} (u : ℝ) :
    HasDerivAt (fun v => g ((p + q * v) / q)) (deriv g ((p + q * u) / q) * (q / q)) u := by
  have h1 : HasDerivAt (fun v => (p + q * v) / q) (q / q) u := by
    simpa using ((hasDerivAt_id u).const_mul q |>.const_add p).div_const q
  exact (hg _).hasDerivAt.comp u h1

theorem hasDerivAt_edgeCutoff (L η u : ℝ) :
    HasDerivAt (edgeCutoff L η) (edgeCutoffD1 L η u) u := by
  have ha : HasDerivAt (fun v => (L + η - v) / η) (-1 / η) u := by
    simpa using ((hasDerivAt_id u).const_sub (L + η)).div_const η
  have hb : HasDerivAt (fun v => (L + η + v) / η) (1 / η) u := by
    simpa using ((hasDerivAt_id u).const_add (L + η)).div_const η
  have h1 := (differentiable_smoothTransition _).hasDerivAt.comp u ha
  have h2 := (differentiable_smoothTransition _).hasDerivAt.comp u hb
  exact h1.mul h2

theorem hasDerivAt_edgeCutoffD1 (L η u : ℝ) :
    HasDerivAt (edgeCutoffD1 L η) (edgeCutoffD2 L η u) u := by
  have ha : HasDerivAt (fun v => (L + η - v) / η) (-1 / η) u := by
    simpa using ((hasDerivAt_id u).const_sub (L + η)).div_const η
  have hb : HasDerivAt (fun v => (L + η + v) / η) (1 / η) u := by
    simpa using ((hasDerivAt_id u).const_add (L + η)).div_const η
  have hsa := (differentiable_smoothTransition _).hasDerivAt.comp u ha
  have hsb := (differentiable_smoothTransition _).hasDerivAt.comp u hb
  have hda := (differentiable_deriv_smoothTransition _).hasDerivAt.comp u ha
  have hdb := (differentiable_deriv_smoothTransition _).hasDerivAt.comp u hb
  have h := ((hda.mul_const (-1 / η)).mul hsb).add (hsa.mul (hdb.mul_const (1 / η)))
  exact h

theorem deriv_edgeCutoff (L η : ℝ) : deriv (edgeCutoff L η) = edgeCutoffD1 L η :=
  funext fun u => (hasDerivAt_edgeCutoff L η u).deriv

theorem deriv_deriv_edgeCutoff (L η : ℝ) :
    deriv (deriv (edgeCutoff L η)) = edgeCutoffD2 L η := by
  rw [deriv_edgeCutoff]; exact funext fun u => (hasDerivAt_edgeCutoffD1 L η u).deriv

theorem abs_edgeCutoffD1_le {S₁ : ℝ} (hS₁ : ∀ x, |deriv st x| ≤ S₁) {L η : ℝ} (hη : 0 < η)
    (u : ℝ) : |edgeCutoffD1 L η u| ≤ 2 * S₁ / η := by
  unfold edgeCutoffD1
  have hs0 := Real.smoothTransition.nonneg ((L + η + u) / η)
  have hs1 := Real.smoothTransition.le_one ((L + η + u) / η)
  have ht0 := Real.smoothTransition.nonneg ((L + η - u) / η)
  have ht1 := Real.smoothTransition.le_one ((L + η - u) / η)
  have h1 := hS₁ ((L + η - u) / η)
  have h2 := hS₁ ((L + η + u) / η)
  have hη' : |1 / η| = 1 / η := abs_of_pos (by positivity)
  have hη'' : |-1 / η| = 1 / η := by rw [neg_div, abs_neg, hη']
  calc |deriv st ((L + η - u) / η) * (-1 / η) * st ((L + η + u) / η) +
        st ((L + η - u) / η) * (deriv st ((L + η + u) / η) * (1 / η))|
      ≤ |deriv st ((L + η - u) / η)| * (1 / η) * 1 + 1 * (|deriv st ((L + η + u) / η)| * (1 / η)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_mul, hη'', abs_of_nonneg hs0]
          exact mul_le_mul_of_nonneg_left hs1 (by positivity)
        · rw [abs_mul, abs_mul, hη', abs_of_nonneg ht0]
          exact mul_le_mul_of_nonneg_right ht1 (by positivity)
    _ ≤ S₁ * (1 / η) * 1 + 1 * (S₁ * (1 / η)) := by gcongr
    _ = 2 * S₁ / η := by ring

theorem abs_edgeCutoffD2_le {S₁ S₂ : ℝ} (hS₁ : ∀ x, |deriv st x| ≤ S₁)
    (hS₂ : ∀ x, |deriv (deriv st) x| ≤ S₂) {L η : ℝ} (hη : 0 < η) (u : ℝ) :
    |edgeCutoffD2 L η u| ≤ (2 * S₂ + 2 * S₁ ^ 2) / η ^ 2 := by
  unfold edgeCutoffD2
  set a := deriv (deriv st) ((L + η - u) / η)
  set b := deriv st ((L + η - u) / η)
  set c := deriv st ((L + η + u) / η)
  set d := deriv (deriv st) ((L + η + u) / η)
  set p := st ((L + η - u) / η)
  set q := st ((L + η + u) / η)
  have hp : |p| ≤ 1 := abs_le.mpr ⟨by linarith [Real.smoothTransition.nonneg ((L + η - u) / η)],
    Real.smoothTransition.le_one _⟩
  have hq : |q| ≤ 1 := abs_le.mpr ⟨by linarith [Real.smoothTransition.nonneg ((L + η + u) / η)],
    Real.smoothTransition.le_one _⟩
  have ha := hS₂ ((L + η - u) / η)
  have hb := hS₁ ((L + η - u) / η)
  have hc := hS₁ ((L + η + u) / η)
  have hd := hS₂ ((L + η + u) / η)
  have e : a * (-1 / η) * (-1 / η) * q + b * (-1 / η) * (c * (1 / η)) +
      (b * (-1 / η) * (c * (1 / η)) + p * (d * (1 / η) * (1 / η))) =
      (a * q - 2 * (b * c) + p * d) / η ^ 2 := by field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < η ^ 2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : |a * q| ≤ S₂ := by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg q]
  have h2 : |b * c| ≤ S₁ ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hb hc (abs_nonneg _) ((abs_nonneg _).trans hb)
  have h3 : |p * d| ≤ S₂ := by rw [abs_mul]; nlinarith [abs_nonneg d, abs_nonneg p]
  calc |a * q - 2 * (b * c) + p * d| ≤ |a * q| + 2 * |b * c| + |p * d| := by
        have := abs_add_le (a * q - 2 * (b * c)) (p * d)
        have := abs_sub (a * q) (2 * (b * c))
        rw [abs_mul (2 : ℝ), abs_two] at this
        linarith
    _ ≤ 2 * S₂ + 2 * S₁ ^ 2 := by linarith

/-! ## Strip bounds for cut kernels -/

/-- The weight `w(x) = (‖Φ‖ + ‖Φ'‖ + ‖Φ''‖)(x) e^{|x|/2}`. -/
def kernelWeight (x : ℝ) : ℝ :=
  (‖riemannKernelDeriv 0 x‖ + ‖riemannKernelDeriv 1 x‖ + ‖riemannKernelDeriv 2 x‖) *
    Real.exp (|x| / 2)

theorem integrable_kernelDeriv_weight (k : ℕ) :
    Integrable (fun x => ‖riemannKernelDeriv k x‖ * Real.exp (|x| / 2)) := by
  have h := (superExpDecay_riemannKernelDeriv k).2 (1 / 2)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only; congr 2; ring

theorem integrable_kernelWeight : Integrable kernelWeight := by
  have h := ((integrable_kernelDeriv_weight 0).add (integrable_kernelDeriv_weight 1)).add
    (integrable_kernelDeriv_weight 2)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, kernelWeight]; ring

theorem kernelWeight_nonneg (x : ℝ) : 0 ≤ kernelWeight x := by
  unfold kernelWeight; positivity

/-- The tail mass `K(a) = ∫_{|x| ≥ a} w`. -/
def kernelTailMass (a : ℝ) : ℝ := ∫ x, (if a ≤ |x| then kernelWeight x else 0)

theorem integrable_kernelWeight_tail (a : ℝ) :
    Integrable (fun x => if a ≤ |x| then kernelWeight x else 0) := by
  have e : (fun x => if a ≤ |x| then kernelWeight x else 0) =
      {x : ℝ | a ≤ |x|}.indicator kernelWeight := by
    funext x; simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [e]
  exact integrable_kernelWeight.indicator (measurableSet_le measurable_const measurable_abs)

theorem kernelTailMass_nonneg (a : ℝ) : 0 ≤ kernelTailMass a :=
  integral_nonneg fun x => by split_ifs <;> simp [kernelWeight_nonneg x]

theorem tendsto_kernelTailMass : Tendsto kernelTailMass atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun a x => if a ≤ |x| then kernelWeight x else 0) (f := fun _ => (0 : ℝ)) kernelWeight
    (Filter.Eventually.of_forall fun a => (integrable_kernelWeight_tail a).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun x => by
      split_ifs
      · rw [Real.norm_of_nonneg (kernelWeight_nonneg x)]
      · simp [kernelWeight_nonneg x])
    integrable_kernelWeight
    (Filter.Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop |x|] with a ha
      rw [if_neg (not_le.mpr ha)])
  have h' : Tendsto (fun a => ∫ x, if a ≤ |x| then kernelWeight x else 0) atTop (𝓝 0) := by
    simpa using h
  exact h'

/-- **Strip bound for a cut kernel.** If `|ψ| + 2|ψ'| + |ψ''| ≤ B` on `|x| ≥ a` and all three
vanish on `|x| < a`, then `‖(Φψ)^(z)‖ ≤ 8B K(a)/(1 + |Re z|)²` on the strip. -/
theorem norm_paperFT_kernelCut_le {ψ ψ₁ ψ₂ : ℝ → ℝ} (hψ : Continuous ψ) (hψ₁ : Continuous ψ₁)
    (hψ₂ : Continuous ψ₂) (hd : ∀ x, HasDerivAt ψ (ψ₁ x) x) (hd₁ : ∀ x, HasDerivAt ψ₁ (ψ₂ x) x)
    {a B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, |ψ x| + 2 * |ψ₁ x| + |ψ₂ x| ≤ if a ≤ |x| then B else 0)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (fun x => riemannKernelDeriv 0 x * (ψ x : ℂ)) z‖ ≤
      4 * (2 * B * kernelTailMass a) / (1 + |z.re|) ^ 2 := by
  set Φ₀ := riemannKernelDeriv 0
  set Φ₁ := riemannKernelDeriv 1
  set Φ₂ := riemannKernelDeriv 2
  set g : ℝ → ℂ := fun x => Φ₀ x * (ψ x : ℂ) with hg
  set g' : ℝ → ℂ := fun x => Φ₁ x * (ψ x : ℂ) + Φ₀ x * (ψ₁ x : ℂ) with hg'
  set g'' : ℝ → ℂ := fun x => Φ₂ x * (ψ x : ℂ) + 2 * (Φ₁ x * (ψ₁ x : ℂ)) + Φ₀ x * (ψ₂ x : ℂ)
    with hg''
  have hc0 := continuous_riemannKernelDeriv 0
  have hc1 := continuous_riemannKernelDeriv 1
  have hc2 := continuous_riemannKernelDeriv 2
  have hgc : Continuous g := hc0.mul (Complex.continuous_ofReal.comp hψ)
  have hg'c : Continuous g' := (hc1.mul (Complex.continuous_ofReal.comp hψ)).add
    (hc0.mul (Complex.continuous_ofReal.comp hψ₁))
  have hg''c : Continuous g'' := ((hc2.mul (Complex.continuous_ofReal.comp hψ)).add
    (continuous_const.mul (hc1.mul (Complex.continuous_ofReal.comp hψ₁)))).add
    (hc0.mul (Complex.continuous_ofReal.comp hψ₂))
  have hdg : ∀ x, HasDerivAt g (g' x) x := fun x =>
    (hasDerivAt_riemannKernelDeriv 0 x).mul (hd x).ofReal_comp
  have hdg' : ∀ x, HasDerivAt g' (g'' x) x := fun x => by
    have h := ((hasDerivAt_riemannKernelDeriv 1 x).mul (hd x).ofReal_comp).add
      ((hasDerivAt_riemannKernelDeriv 0 x).mul (hd₁ x).ofReal_comp)
    refine h.congr_deriv ?_
    simp only [hg'']; ring
  -- pointwise bounds by the tail weight
  have hbound : ∀ x, (‖g x‖ * Real.exp (|x| / 2) ≤ B * (if a ≤ |x| then kernelWeight x else 0)) ∧
      (‖g' x‖ * Real.exp (|x| / 2) ≤ B * (if a ≤ |x| then kernelWeight x else 0)) ∧
      (‖g'' x‖ * Real.exp (|x| / 2) ≤ B * (if a ≤ |x| then kernelWeight x else 0)) := fun x => by
    have hb := hB x
    have he := Real.exp_pos (|x| / 2)
    have n0 := norm_nonneg (Φ₀ x)
    have n1 := norm_nonneg (Φ₁ x)
    have n2 := norm_nonneg (Φ₂ x)
    have a0 := abs_nonneg (ψ x)
    have a1 := abs_nonneg (ψ₁ x)
    have a2 := abs_nonneg (ψ₂ x)
    split_ifs at hb ⊢ with ha
    · unfold kernelWeight
      have hn0 : ‖g x‖ = ‖Φ₀ x‖ * |ψ x| := by
        simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hn1 : ‖g' x‖ ≤ ‖Φ₁ x‖ * |ψ x| + ‖Φ₀ x‖ * |ψ₁ x| := by
        simp only [hg']
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hn2 : ‖g'' x‖ ≤ ‖Φ₂ x‖ * |ψ x| + 2 * (‖Φ₁ x‖ * |ψ₁ x|) + ‖Φ₀ x‖ * |ψ₂ x| := by
        simp only [hg'']
        refine (norm_add₃_le).trans (le_of_eq ?_)
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_ofNat]
      have hW : 0 ≤ ‖Φ₀ x‖ + ‖Φ₁ x‖ + ‖Φ₂ x‖ := by positivity
      refine ⟨?_, ?_, ?_⟩
      · rw [hn0]
        have : ‖Φ₀ x‖ * |ψ x| ≤ B * (‖Φ₀ x‖ + ‖Φ₁ x‖ + ‖Φ₂ x‖) := by nlinarith
        calc ‖Φ₀ x‖ * |ψ x| * Real.exp (|x| / 2)
            ≤ B * (‖Φ₀ x‖ + ‖Φ₁ x‖ + ‖Φ₂ x‖) * Real.exp (|x| / 2) :=
              mul_le_mul_of_nonneg_right this he.le
          _ = _ := by ring
      · have : ‖Φ₁ x‖ * |ψ x| + ‖Φ₀ x‖ * |ψ₁ x| ≤ B * (‖Φ₀ x‖ + ‖Φ₁ x‖ + ‖Φ₂ x‖) := by nlinarith
        calc ‖g' x‖ * Real.exp (|x| / 2)
            ≤ B * (‖Φ₀ x‖ + ‖Φ₁ x‖ + ‖Φ₂ x‖) * Real.exp (|x| / 2) :=
              mul_le_mul_of_nonneg_right (hn1.trans this) he.le
          _ = _ := by ring
      · have : ‖Φ₂ x‖ * |ψ x| + 2 * (‖Φ₁ x‖ * |ψ₁ x|) + ‖Φ₀ x‖ * |ψ₂ x| ≤
            B * (‖Φ₀ x‖ + ‖Φ₁ x‖ + ‖Φ₂ x‖) := by nlinarith
        calc ‖g'' x‖ * Real.exp (|x| / 2)
            ≤ B * (‖Φ₀ x‖ + ‖Φ₁ x‖ + ‖Φ₂ x‖) * Real.exp (|x| / 2) :=
              mul_le_mul_of_nonneg_right (hn2.trans this) he.le
          _ = _ := by ring
    · have h0 : ψ x = 0 := abs_nonpos_iff.mp (by linarith)
      have h1 : ψ₁ x = 0 := abs_nonpos_iff.mp (by linarith)
      have h2 : ψ₂ x = 0 := abs_nonpos_iff.mp (by linarith)
      simp [hg, hg', hg'', h0, h1, h2]
  have hT := integrable_kernelWeight_tail a
  have hBT := hT.const_mul B
  have hint : Integrable (fun x => ‖g x‖ * Real.exp (|x| / 2)) :=
    hBT.mono' ((hgc.norm.mul (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]; exact (hbound x).1)
  have hint' : Integrable (fun x => ‖g' x‖ * Real.exp (|x| / 2)) :=
    hBT.mono' ((hg'c.norm.mul (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]; exact (hbound x).2.1)
  have hint'' : Integrable (fun x => ‖g'' x‖ * Real.exp (|x| / 2)) :=
    hBT.mono' ((hg''c.norm.mul (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]; exact (hbound x).2.2)
  have h := norm_paperFT_le_of_strip hgc hg'c hg''c hdg hdg' hint hint' hint'' hz
  have hN0 : ∫ x, ‖g x‖ * Real.exp (|x| / 2) ≤ B * kernelTailMass a := by
    rw [kernelTailMass, ← integral_const_mul]
    exact integral_mono hint hBT fun x => (hbound x).1
  have hN2 : ∫ x, ‖g'' x‖ * Real.exp (|x| / 2) ≤ B * kernelTailMass a := by
    rw [kernelTailMass, ← integral_const_mul]
    exact integral_mono hint'' hBT fun x => (hbound x).2.2
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-! ## The three pieces of Riemann's kernel -/

theorem riemannKernelDeriv_zero_eq_ofReal (u : ℝ) :
    riemannKernelDeriv 0 u = (riemannKernelReal u : ℂ) := by
  rw [riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal]

/-- The truncation `Φχ_L`. -/
def riemannTruncKernel (L u : ℝ) : ℝ := riemannKernelReal u * edgeCutoff L (edgeWidth L) u

/-- The outer tail `Φ(1 − χ_R)`. -/
def outerTail (R u : ℝ) : ℝ := riemannKernelReal u * (1 - edgeCutoff R 1 u)

theorem ofReal_kernel_mul (ψ : ℝ → ℝ) (u : ℝ) :
    ((riemannKernelReal u * ψ u : ℝ) : ℂ) = riemannKernelDeriv 0 u * (ψ u : ℂ) := by
  rw [riemannKernelDeriv_zero_eq_ofReal]; push_cast; ring

/-- The transform of `Φ` vanishes at both evaluation points of every zero. -/
theorem paperFT_kernel_at_zero {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    paperFT (riemannKernelDeriv 0) (gammaOf ρ) = 0 ∧
      paperFT (riemannKernelDeriv 0) ((starRingEnd ℂ) (gammaOf ρ)) = 0 := by
  have hz : ∀ σ ∈ zetaZeroConfig.carrier, riemannPhiTransform σ = 0 := by
    intro σ hσ
    rw [zetaZeroConfig_carrier] at hσ
    exact riemannPhiTransform_eq_zero_of_nontrivial hσ.1 hσ.2.1 hσ.2.2
  have h1 : 1 / 2 + I * gammaOf ρ = ρ := by
    unfold gammaOf; field_simp; ring
  have h2 : 1 / 2 + I * (starRingEnd ℂ) (gammaOf ρ) = Zeta23.reflect ρ := by
    unfold gammaOf Zeta23.reflect
    apply Complex.ext
    · simp; ring
    · simp
  rw [riemannKernelDeriv_zero, paperFT_riemannPhiKernel, paperFT_riemannPhiKernel, h1, h2]
  exact ⟨hz ρ hρ, hz _ (zetaZeroConfig.reflect_mem ρ hρ)⟩

theorem integrable_riemannKernel_cut_mul_cexp {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ1 : ∀ x, |ψ x| ≤ 1)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun x => riemannKernelDeriv 0 x * (ψ x : ℂ) * Complex.exp (I * z * x)) := by
  refine (integrable_kernelDeriv_weight 0).mono'
    (((continuous_riemannKernelDeriv 0).mul (Complex.continuous_ofReal.comp hψ)).mul
      (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_cexp_I_mul_le_exp hz x
  rw [show (1 / 2 : ℝ) * |x| = |x| / 2 by ring] at h1
  have h0 := norm_nonneg (riemannKernelDeriv 0 x)
  have hψx := hψ1 x
  calc ‖riemannKernelDeriv 0 x‖ * |ψ x| * ‖Complex.exp (I * z * x)‖
      ≤ ‖riemannKernelDeriv 0 x‖ * 1 * Real.exp (|x| / 2) := by
        gcongr
    _ = _ := by ring

theorem abs_edgeCutoff_sub_le (R L η u : ℝ) : |edgeCutoff R 1 u - edgeCutoff L η u| ≤ 1 := by
  have := edgeCutoff_nonneg R 1 u
  have := edgeCutoff_le_one R 1 u
  have := edgeCutoff_nonneg L η u
  have := edgeCutoff_le_one L η u
  rw [abs_le]; constructor <;> linarith

/-- **The radical identity at the zeros.** `(Φχ_L)^ = −(T_R)^ − (Φ(1 − χ_R))^` at both
evaluation points of every zero. -/
theorem paperFT_truncKernel_at_zero {L R : ℝ} {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    {z : ℂ} (hz : z = gammaOf ρ ∨ z = (starRingEnd ℂ) (gammaOf ρ)) :
    paperFT (fun u => (riemannTruncKernel L u : ℂ)) z =
      -paperFT (fun u => (edgeTail L R u : ℂ)) z - paperFT (fun u => (outerTail R u : ℂ)) z := by
  have hstrip : |z.im| ≤ 1 / 2 := by
    obtain ⟨hi1, hi2, -, -⟩ := strip_gammaOf hρ
    rcases hz with rfl | rfl
    · exact hi1
    · exact hi2
  have hzero : paperFT (riemannKernelDeriv 0) z = 0 := by
    obtain ⟨h1, h2⟩ := paperFT_kernel_at_zero hρ
    rcases hz with rfl | rfl
    · exact h1
    · exact h2
  have hc1 : Continuous (edgeCutoff L (edgeWidth L)) := (contDiff_edgeCutoff L _).continuous
  have hc2 : Continuous (fun u => edgeCutoff R 1 u - edgeCutoff L (edgeWidth L) u) :=
    (contDiff_edgeCutoff R 1).continuous.sub hc1
  have hc3 : Continuous (fun u => 1 - edgeCutoff R 1 u) :=
    continuous_const.sub (contDiff_edgeCutoff R 1).continuous
  have i1 := integrable_riemannKernel_cut_mul_cexp hc1 (fun u => by
    rw [abs_of_nonneg (edgeCutoff_nonneg _ _ _)]; exact edgeCutoff_le_one _ _ _) hstrip
  have i2 := integrable_riemannKernel_cut_mul_cexp hc2 (fun u => abs_edgeCutoff_sub_le _ _ _ _) hstrip
  have i3 := integrable_riemannKernel_cut_mul_cexp hc3 (fun u => by
    have := edgeCutoff_nonneg R 1 u; have := edgeCutoff_le_one R 1 u
    rw [abs_le]; constructor <;> linarith) hstrip
  have j1 : Integrable (fun u => ((riemannTruncKernel L u : ℝ) : ℂ) * Complex.exp (I * z * u)) :=
    i1.congr (Filter.Eventually.of_forall fun u => by
      simp only [riemannTruncKernel]; rw [riemannKernelDeriv_zero_eq_ofReal]; push_cast; ring)
  have j2 : Integrable (fun u => ((edgeTail L R u : ℝ) : ℂ) * Complex.exp (I * z * u)) :=
    i2.congr (Filter.Eventually.of_forall fun u => by
      simp only [edgeTail]; rw [riemannKernelDeriv_zero_eq_ofReal]; push_cast; ring)
  have j3 : Integrable (fun u => ((outerTail R u : ℝ) : ℂ) * Complex.exp (I * z * u)) :=
    i3.congr (Filter.Eventually.of_forall fun u => by
      simp only [outerTail]; rw [riemannKernelDeriv_zero_eq_ofReal]; push_cast; ring)
  have hsum : paperFT (riemannKernelDeriv 0) z =
      paperFT (fun u => (riemannTruncKernel L u : ℂ)) z + paperFT (fun u => (edgeTail L R u : ℂ)) z +
        paperFT (fun u => (outerTail R u : ℂ)) z := by
    have j12 : Integrable (fun u => ((riemannTruncKernel L u : ℝ) : ℂ) * Complex.exp (I * z * u) +
        ((edgeTail L R u : ℝ) : ℂ) * Complex.exp (I * z * u)) := j1.add j2
    simp only [paperFT]
    rw [← integral_add j1 j2, ← integral_add j12 j3]
    congr 1; funext u
    simp only [riemannTruncKernel, edgeTail, outerTail]
    rw [riemannKernelDeriv_zero_eq_ofReal]
    push_cast; ring
  rw [hzero] at hsum
  linear_combination -hsum

/-! ## Strip bounds for the two tails -/

theorem edgeCutoffD1_eq_zero {R u : ℝ} (hu : |u| < R) : edgeCutoffD1 R 1 u = 0 := by
  have h1 : 1 < (R + 1 - u) / 1 := by rw [div_one]; linarith [(abs_lt.mp hu).2]
  have h2 : 1 < (R + 1 + u) / 1 := by rw [div_one]; linarith [(abs_lt.mp hu).1]
  unfold edgeCutoffD1
  rw [deriv_smoothTransition_eq_zero (Or.inr h1), deriv_smoothTransition_eq_zero (Or.inr h2)]
  ring

theorem edgeCutoffD2_eq_zero {R u : ℝ} (hu : |u| < R) : edgeCutoffD2 R 1 u = 0 := by
  have h1 : 1 < (R + 1 - u) / 1 := by rw [div_one]; linarith [(abs_lt.mp hu).2]
  have h2 : 1 < (R + 1 + u) / 1 := by rw [div_one]; linarith [(abs_lt.mp hu).1]
  unfold edgeCutoffD2
  rw [deriv_smoothTransition_eq_zero (Or.inr h1), deriv_smoothTransition_eq_zero (Or.inr h2),
    deriv_deriv_smoothTransition_eq_zero (Or.inr h1), deriv_deriv_smoothTransition_eq_zero (Or.inr h2)]
  ring

theorem continuous_edgeCutoffD1 (L η : ℝ) : Continuous (edgeCutoffD1 L η) := by
  rw [← deriv_edgeCutoff]
  exact (contDiff_edgeCutoff L η).continuous_deriv (by exact_mod_cast le_top)

theorem continuous_edgeCutoffD2 (L η : ℝ) : Continuous (edgeCutoffD2 L η) := by
  rw [← deriv_deriv_edgeCutoff]
  have h : ContDiff ℝ 2 (edgeCutoff L η) := (contDiff_edgeCutoff L η).of_le
    (WithTop.coe_le_coe.2 le_top)
  exact (h.iterate_deriv' 1 1).continuous_deriv le_rfl

/-- The edge-tail transform is `O((1 + |Re z|)^{-2})` uniformly in `R`. -/
theorem norm_paperFT_edgeTail_le {S₁ S₂ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₂0 : 0 ≤ S₂)
    (hS₁ : ∀ x, |deriv st x| ≤ S₁) (hS₂ : ∀ x, |deriv (deriv st) x| ≤ S₂) (L R : ℝ)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (fun u => (edgeTail L R u : ℂ)) z‖ ≤
      4 * (2 * (1 + 2 * (2 * S₁ / 1 + 2 * S₁ / edgeWidth L) +
        ((2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2 + (2 * S₂ + 2 * S₁ ^ 2) / edgeWidth L ^ 2)) *
          kernelTailMass 0) / (1 + |z.re|) ^ 2 := by
  have hη := edgeWidth_pos L
  have e : (fun u => (edgeTail L R u : ℂ)) =
      fun x => riemannKernelDeriv 0 x * ((edgeCutoff R 1 x - edgeCutoff L (edgeWidth L) x : ℝ) : ℂ) := by
    funext x; simp only [edgeTail]; rw [riemannKernelDeriv_zero_eq_ofReal]; push_cast; ring
  rw [e]
  refine norm_paperFT_kernelCut_le (ψ := fun x => edgeCutoff R 1 x - edgeCutoff L (edgeWidth L) x)
    (ψ₁ := fun x => edgeCutoffD1 R 1 x - edgeCutoffD1 L (edgeWidth L) x)
    (ψ₂ := fun x => edgeCutoffD2 R 1 x - edgeCutoffD2 L (edgeWidth L) x)
    ((contDiff_edgeCutoff R 1).continuous.sub (contDiff_edgeCutoff L _).continuous)
    ((continuous_edgeCutoffD1 R 1).sub (continuous_edgeCutoffD1 L _))
    ((continuous_edgeCutoffD2 R 1).sub (continuous_edgeCutoffD2 L _))
    (fun x => (hasDerivAt_edgeCutoff R 1 x).sub (hasDerivAt_edgeCutoff L _ x))
    (fun x => (hasDerivAt_edgeCutoffD1 R 1 x).sub (hasDerivAt_edgeCutoffD1 L _ x))
    (by positivity) (fun x => ?_) hz
  rw [if_pos (abs_nonneg x)]
  have h0 := abs_edgeCutoff_sub_le R L (edgeWidth L) x
  have h1 : |edgeCutoffD1 R 1 x - edgeCutoffD1 L (edgeWidth L) x| ≤ 2 * S₁ / 1 + 2 * S₁ / edgeWidth L :=
    (abs_sub _ _).trans (add_le_add (abs_edgeCutoffD1_le hS₁ one_pos x)
      (abs_edgeCutoffD1_le hS₁ hη x))
  have h2 : |edgeCutoffD2 R 1 x - edgeCutoffD2 L (edgeWidth L) x| ≤
      (2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2 + (2 * S₂ + 2 * S₁ ^ 2) / edgeWidth L ^ 2 :=
    (abs_sub _ _).trans (add_le_add (abs_edgeCutoffD2_le hS₁ hS₂ one_pos x)
      (abs_edgeCutoffD2_le hS₁ hS₂ hη x))
  linarith

/-- The outer-tail transform is `O(K(R)(1 + |Re z|)^{-2})`. -/
theorem norm_paperFT_outerTail_le {S₁ S₂ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₂0 : 0 ≤ S₂)
    (hS₁ : ∀ x, |deriv st x| ≤ S₁) (hS₂ : ∀ x, |deriv (deriv st) x| ≤ S₂) (R : ℝ)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (fun u => (outerTail R u : ℂ)) z‖ ≤
      4 * (2 * (1 + 2 * (2 * S₁ / 1) + (2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2) * kernelTailMass R) /
        (1 + |z.re|) ^ 2 := by
  have e : (fun u => (outerTail R u : ℂ)) =
      fun x => riemannKernelDeriv 0 x * ((1 - edgeCutoff R 1 x : ℝ) : ℂ) := by
    funext x; simp only [outerTail]; rw [riemannKernelDeriv_zero_eq_ofReal]; push_cast; ring
  rw [e]
  refine norm_paperFT_kernelCut_le (ψ := fun x => 1 - edgeCutoff R 1 x)
    (ψ₁ := fun x => -edgeCutoffD1 R 1 x)
    (ψ₂ := fun x => -edgeCutoffD2 R 1 x)
    (continuous_const.sub (contDiff_edgeCutoff R 1).continuous)
    (continuous_edgeCutoffD1 R 1).neg (continuous_edgeCutoffD2 R 1).neg
    (fun x => (hasDerivAt_edgeCutoff R 1 x).const_sub 1)
    (fun x => (hasDerivAt_edgeCutoffD1 R 1 x).neg)
    (by positivity) (fun x => ?_) hz
  split_ifs with hx
  · have h0 : |1 - edgeCutoff R 1 x| ≤ 1 := by
      have := edgeCutoff_nonneg R 1 x; have := edgeCutoff_le_one R 1 x
      rw [abs_le]; constructor <;> linarith
    have h1 := abs_edgeCutoffD1_le hS₁ one_pos (L := R) x
    have h2 := abs_edgeCutoffD2_le hS₁ hS₂ one_pos (L := R) x
    rw [abs_neg, abs_neg]
    linarith
  · push Not at hx
    rw [edgeCutoff_eq_one one_pos hx.le, edgeCutoffD1_eq_zero hx, edgeCutoffD2_eq_zero hx]
    simp

/-! ## The Weil energy of the truncation -/

theorem contDiff_ofReal_truncKernel (L : ℝ) : ContDiff ℝ 2 (fun u => (riemannTruncKernel L u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_riemannKernelReal.mul
    (contDiff_edgeCutoff L (edgeWidth L))).of_le (WithTop.coe_le_coe.2 le_top))

theorem hasCompactSupport_ofReal_truncKernel (L : ℝ) :
    HasCompactSupport (fun u => (riemannTruncKernel L u : ℂ)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(L + edgeWidth L)) (b := L + edgeWidth L))
    fun u hu => ?_
  have hu' : L + edgeWidth L ≤ |u| := by
    rw [Set.mem_Icc, not_and_or] at hu
    rcases hu with h | h
    · push Not at h; exact le_abs.2 (Or.inr (by linarith))
    · push Not at h; exact le_abs.2 (Or.inl h.le)
  simp [riemannTruncKernel, edgeCutoff_eq_zero (edgeWidth_pos L) hu']

/-- **The truncation and the edge tail have nearly the same Weil energy.** If the edge-tail and
outer-tail transforms are bounded by `N_T/(1 + |Re z|)²` and `N_E/(1 + |Re z|)²` on the strip, then
`‖W(Φχ_L, Φχ_L) − W(T_R, T_R)‖ ≤ (2N_T N_E + N_E²) Σ_ρ m_ρ/(1 + |γ_ρ|)³`. -/
theorem norm_W_truncKernel_sub_le {L R : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) {NT NE : ℝ}
    (hNT : 0 ≤ NT) (hNE : 0 ≤ NE)
    (hT : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT (fun u => (edgeTail L R u : ℂ)) z‖ ≤ NT / (1 + |z.re|) ^ 2)
    (hE : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT (fun u => (outerTail R u : ℂ)) z‖ ≤ NE / (1 + |z.re|) ^ 2) :
    ‖zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ)) (fun u => (riemannTruncKernel L u : ℂ)) -
        zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ))‖ ≤
      (2 * NT * NE + NE ^ 2) *
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3 := by
  set F : ℝ → ℂ := fun u => (riemannTruncKernel L u : ℂ) with hF
  set T : ℝ → ℂ := fun u => (edgeTail L R u : ℂ) with hT_def
  set E : ℝ → ℂ := fun u => (outerTail R u : ℂ) with hE_def
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨hs, -⟩ := window_tsum_le zetaZeroConfig hA₀ hloc 0
  have hsF := summable_Wsummand_of_contDiff_two (contDiff_ofReal_truncKernel L)
    (hasCompactSupport_ofReal_truncKernel L) (contDiff_ofReal_truncKernel L)
    (hasCompactSupport_ofReal_truncKernel L)
  have hTc : HasCompactSupport T :=
    (hasCompactSupport_edgeTail hL hR).comp_left (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero
  have hsT := summable_Wsummand_of_contDiff_two (contDiff_ofReal_edgeTail L R) hTc
    (contDiff_ofReal_edgeTail L R) hTc
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand F F ρ - zetaZeroConfig.Wsummand T T ρ‖ ≤
        (2 * NT * NE + NE ^ 2) * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3) := by
    intro ρ
    obtain ⟨hi1, hi2, hr1, hr2⟩ := strip_gammaOf ρ.2
    have hF1 := paperFT_truncKernel_at_zero (L := L) (R := R) ρ.2 (Or.inl rfl)
    have hF2 := paperFT_truncKernel_at_zero (L := L) (R := R) ρ.2 (Or.inr rfl)
    set a := paperFT T (gammaOf ρ)
    set b := paperFT T ((starRingEnd ℂ) (gammaOf ρ))
    set c := paperFT E (gammaOf ρ)
    set d := paperFT E ((starRingEnd ℂ) (gammaOf ρ))
    have ha := hT _ hi1
    have hb := hT _ hi2
    have hc := hE _ hi1
    have hd := hE _ hi2
    rw [hr1] at ha hc; rw [hr2] at hb hd
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    set D := (1 + |(ρ : ℂ).im|) with hD
    have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg (ρ : ℂ).im]
    have hdiff : zetaZeroConfig.Wsummand F F ρ - zetaZeroConfig.Wsummand T T ρ =
        (zetaZeroConfig.mult ρ : ℂ) * (a * (starRingEnd ℂ) d + c * (starRingEnd ℂ) b +
          c * (starRingEnd ℂ) d) := by
      simp only [ZeroConfig.Wsummand]
      rw [hF1, hF2]
      simp only [map_sub, map_neg]
      ring
    rw [hdiff, norm_mul, Complex.norm_natCast, sub_zero]
    have hsum : ‖a * (starRingEnd ℂ) d + c * (starRingEnd ℂ) b + c * (starRingEnd ℂ) d‖ ≤
        (2 * NT * NE + NE ^ 2) / D ^ 4 := by
      refine (norm_add₃_le).trans ?_
      simp only [norm_mul, RCLike.norm_conj]
      have e : (2 * NT * NE + NE ^ 2) / D ^ 4 =
          NT / D ^ 2 * (NE / D ^ 2) + NE / D ^ 2 * (NT / D ^ 2) + NE / D ^ 2 * (NE / D ^ 2) := by
        field_simp; ring
      rw [e]
      have h0 := norm_nonneg a; have h1 := norm_nonneg b
      have h2 := norm_nonneg c; have h3 := norm_nonneg d
      gcongr
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖a * (starRingEnd ℂ) d + c * (starRingEnd ℂ) b +
          c * (starRingEnd ℂ) d‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * ((2 * NT * NE + NE ^ 2) / D ^ 4) :=
          mul_le_mul_of_nonneg_left hsum hm
      _ ≤ (2 * NT * NE + NE ^ 2) * ((zetaZeroConfig.mult ρ : ℝ) / D ^ 3) := by
          rw [show (zetaZeroConfig.mult ρ : ℝ) * ((2 * NT * NE + NE ^ 2) / D ^ 4) =
            (2 * NT * NE + NE ^ 2) * ((zetaZeroConfig.mult ρ : ℝ) / D ^ 4) by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_left hm (by positivity)
          exact pow_le_pow_right₀ hD1 (by norm_num)
  unfold ZeroConfig.W
  rw [← hsF.tsum_sub hsT, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum hpt ?_ (hs.mul_left _))
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hs.mul_left _)
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hs.mul_left _)

/-- **The truncated Riemann kernel is Weil-positive.** For all large `L`,
`Re W(Φχ_L, Φχ_L) > 0`, where `χ_L` is the even cutoff equal to `1` on `|u| ≤ L` with an edge of
width `1/(2πe^{2L})`. No hypothesis on the zeros of `ζ` is used. -/
theorem eventually_re_W_truncKernel_pos :
    ∀ᶠ L : ℝ in atTop,
      0 < (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ)) (fun u => (riemannTruncKernel L u : ℂ))).re := by
  obtain ⟨S₁, hS₁0, hS₁⟩ := exists_abs_deriv_smoothTransition_le
  obtain ⟨S₂, hS₂0, hS₂⟩ := exists_abs_deriv_deriv_smoothTransition_le
  filter_upwards [eventually_exists_margin_edgeTail, eventually_ge_atTop (1 : ℝ)] with L hmarg hL
  obtain ⟨δ, hδ, hmargin⟩ := hmarg
  set BT := 1 + 2 * (2 * S₁ / 1 + 2 * S₁ / edgeWidth L) +
    ((2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2 + (2 * S₂ + 2 * S₁ ^ 2) / edgeWidth L ^ 2) with hBT
  set BE := 1 + 2 * (2 * S₁ / 1) + (2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2 with hBE
  have hη := edgeWidth_pos L
  have hBT0 : 0 ≤ BT := by rw [hBT]; positivity
  have hBE0 : 0 ≤ BE := by rw [hBE]; positivity
  set NT := 4 * (2 * BT * kernelTailMass 0) with hNT
  have hNT0 : 0 ≤ NT := by have := kernelTailMass_nonneg 0; rw [hNT]; positivity
  set S := ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3
    with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hlim : Tendsto (fun R => (2 * NT * (4 * (2 * BE * kernelTailMass R)) +
      (4 * (2 * BE * kernelTailMass R)) ^ 2) * S) atTop (𝓝 0) := by
    have h := tendsto_kernelTailMass
    have h1 : Tendsto (fun R => 4 * (2 * BE * kernelTailMass R)) atTop (𝓝 0) := by
      simpa using (h.const_mul (2 * BE)).const_mul 4
    have h2 := ((h1.const_mul (2 * NT)).add (h1.pow 2)).mul_const S
    simpa using h2
  obtain ⟨R, hR, hsmall⟩ := ((eventually_ge_atTop (L + 2)).and
    (hlim.eventually (gt_mem_nhds (half_pos hδ)))).exists
  have hdiff := norm_W_truncKernel_sub_le (L := L) (R := R) (by linarith) hR hNT0
    (by have := kernelTailMass_nonneg R; positivity)
    (fun z hz => norm_paperFT_edgeTail_le hS₁0 hS₂0 hS₁ hS₂ L R hz)
    (fun z hz => norm_paperFT_outerTail_le hS₁0 hS₂0 hS₁ hS₂ R hz)
  have hT := hmargin R hR
  have hre := Complex.abs_re_le_norm
    (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ)) (fun u => (riemannTruncKernel L u : ℂ)) -
      zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ)))
  rw [Complex.sub_re] at hre
  have := (abs_le.mp (hre.trans hdiff)).1
  rw [← hBE, ← hS] at this
  linarith

end

end RHTower
