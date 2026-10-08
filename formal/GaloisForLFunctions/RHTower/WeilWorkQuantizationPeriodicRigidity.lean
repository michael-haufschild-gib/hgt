import GaloisForLFunctions.RHTower.WeilWorkQuantizationWindingFactor
import GaloisForLFunctions.RHTower.WeilWorkQuantizationCumulativeContinuity

/-!
# Actual resonant periodic phase rigidity

Every exponentially summable periodic representation with harmonics
2 k log q, q ≥ 2, of the canonical residual phase forces arithmetic
rigidity and RH. All rational resonances are retained. The final alternative
has only Weil positivity as its source premise; it does not assert that
Weil positivity supplies a periodic representation.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open Bottcher GaloisForLFunctions.HTGeometry

theorem quantization_cumulative_bounded_of_periodic
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → quantizationResidualCumulative hW x ≤ K := by
  obtain ⟨a, b, N, L, ha0, ha, hb, hN, hL, he⟩ :=
    quantization_phase_exists_nonpos_winding_log hW hq hp hphase
  have hC := continuousOn_quantizationResidualCumulative_of_periodic hW hq hp hphase
  let z : ℝ → ℂ := fun x => cexp (((2 * Real.log q * x : ℝ) : ℂ) * I)
  have hzn (x : ℝ) : ‖z x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hza (x : ℝ) : z x ∈ annulusSet a b := by
    change a < ‖z x‖ ∧ ‖z x‖ < b
    simpa only [hzn] using And.intro ha hb
  have hzc : Continuous z := by fun_prop
  have hLc : Continuous (fun x => L (z x)) := hL.continuousOn.comp_continuous hzc hza
  let F : ℝ → ℂ := fun x => (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I)
  let G : ℝ → ℂ := fun x => (N : ℂ) * (((2 * Real.log q * x : ℝ) : ℂ) * I) + L (z x)
  have hFc : ContinuousOn F (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hC)).mul continuousOn_const
  have hGc : ContinuousOn G (Ioi 0) := by
    have hc : Continuous (fun x : ℝ => (N : ℂ) * (((2 * Real.log q * x : ℝ) : ℂ) * I)) := by fun_prop
    exact (hc.add hLc).continuousOn
  have hFG (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : cexp (F x) = cexp (G x) := by
    dsimp only [G]
    rw [Complex.exp_add, Complex.exp_int_mul]
    exact (quantizationPeriodicSymbol_phase hW hphase hx).symm.trans (he _ (hza x))
  have hcircle : ContinuousOn L (sphere 0 1) := hL.continuousOn.mono (by
    intro w hw
    have hn : ‖w‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hw
    change a < ‖w‖ ∧ ‖w‖ < b
    simpa only [hn] using And.intro ha hb)
  obtain ⟨M, _, hM⟩ := exists_bound_on_sphere (by norm_num : (0 : ℝ) ≤ 1) hcircle
  let B : ℝ := (F 1 - G 1).im
  let K : ℝ := |(M + B) / (2 * Real.pi)| + 1
  refine ⟨K, by dsimp [K]; positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hdiff := quantization_continuous_lift_diff isPreconnected_Ioi hFc hGc hFG hx0
    (by norm_num : (1 : ℝ) ∈ Ioi 0)
  have hi : 2 * Real.pi * quantizationResidualCumulative hW x -
      ((N : ℝ) * (2 * Real.log q * x) + (L (z x)).im) = B := by
    have hi := congrArg Complex.im hdiff
    change (F x - G x).im = B at hi
    simpa only [F, G, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add] using hi
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hNx : (N : ℝ) * (2 * Real.log q * x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hN) (by positivity)
  have hLM : (L (z x)).im ≤ M := (Complex.im_le_norm _).trans
    (hM _ (by simpa only [mem_sphere_iff_norm, sub_zero] using hzn x))
  have hbound : quantizationResidualCumulative hW x ≤ (M + B) / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith
  exact hbound.trans (by dsimp [K]; linarith [le_abs_self ((M+B)/(2*Real.pi))])

theorem quantization_rigidity_of_periodic_phase
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨K, hK, hbound⟩ := quantization_cumulative_bounded_of_periodic hW hq hp hphase
  have hmono := monotone_quantizationResidualCumulative hW
  apply quantization_rigidity_of_radial_remainder hW hmono.measurable
    (ae_quantizationReflectedTraceF_cumulative_phase hW)
  intro m hm
  apply tendsto_quantization_twisted_remainder_pow hW hmono
    (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hK ?_ (2 * Real.pi) hm
  intro x hx
  exact (hbound x hx).trans (le_mul_of_one_le_right hK.le
    (Real.one_le_rpow hx (by norm_num)))

theorem quantization_rigidity_or_no_periodic_phase
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ q : ℕ, 2 ≤ q → ¬∃ p : ℤ → ℂ,
        (Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs) ∧
        ∀ x : ℝ, 0 < x →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
            ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I) := by
  by_cases hR : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl hR
  · refine Or.inr (fun q hq => ?_)
    rintro ⟨p, hp, hphase⟩
    exact hR (quantization_rigidity_of_periodic_phase hW hq hp hphase)

end RHTower.WeilSpectral
