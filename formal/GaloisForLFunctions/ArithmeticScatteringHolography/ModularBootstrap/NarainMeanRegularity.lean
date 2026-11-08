import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Meromorphic regularity after main-term subtraction

Main-term subtraction preserves global meromorphy and every arithmetic pole order, while removing positive real singularities.
-/

open Complex RHTower Set Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem meromorphic_slopeExt {f : ℂ → ℂ} (hf : Meromorphic f) (p : ℂ) :
    Meromorphic (slopeExt f p) := by
  intro z
  have hd : AnalyticAt ℂ (fun w : ℂ => w - p) z := by fun_prop
  apply ((hf z).sub (MeromorphicAt.const (f p) z) |>.div hd.meromorphicAt).congr
  by_cases hz : z = p
  · subst z
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (slopeExt_of_ne hw).symm
  · have hnear : ∀ᶠ w in 𝓝[≠] z, w ≠ p :=
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz)
    filter_upwards [hnear] with w hw
    exact (slopeExt_of_ne hw).symm

/-- The entire divided numerators express the main-pole numerator as a meromorphic quotient. -/
theorem meromorphic_narainMeanMainPoleNumerator (Y Z : Height) :
    Meromorphic (narainMeanMainPoleNumerator Y Z) := by
  have hn : Differentiable ℂ (fun u : ℂ =>
      u * dividedFilledNumeratorMean Y u * dividedFilledNumeratorMean Z u) := by
    convert! (differentiable_id.mul (differentiable_dividedFilledNumeratorMean Y)).mul
      (differentiable_dividedFilledNumeratorMean Z) using 1
  have hd : Differentiable ℂ (fun u : ℂ => 2 * (1 + 2 * u) * xi (1 + 2 * u)) := by
    convert! (by fun_prop : Differentiable ℂ (fun u : ℂ => 2 * (1 + 2 * u))).mul
      differentiable_xi_shift using 1
  intro u
  have h := (hn.analyticAt u).meromorphicAt.div (hd.analyticAt u).meromorphicAt
  apply h.congr
  filter_upwards [] with v
  exact (narainMeanMainPoleNumerator_eq_reduced Y Z v).symm

/-- Subtracting the main double pole preserves global meromorphy. -/
theorem meromorphic_narainMellinMeanRegularPart (Y Z : Height) :
    Meromorphic (narainMellinMeanRegularPart Y Z) :=
  meromorphic_slopeExt (meromorphic_slopeExt (meromorphic_narainMeanMainPoleNumerator Y Z)
    (1 / 2)) (1 / 2)

/-- The regularized physical Mellin transform has no pole on the positive real axis. -/
theorem analyticAt_narainMellinMeanRegularPart_of_real
    (Y Z : Height) {σ : ℝ} (hσ : 0 < σ) :
    AnalyticAt ℂ (narainMellinMeanRegularPart Y Z) ((σ : ℂ) - 1 / 2) := by
  have he : 1 + 2 * ((σ : ℂ) - 1 / 2) = ((2 * σ : ℝ) : ℂ) := by push_cast; ring
  have hmem : (σ : ℂ) - 1 / 2 ∈ narainMellinRegularDomain := by
    change (1 + 2 * ((σ : ℂ) - 1 / 2)) * xi (1 + 2 * ((σ : ℂ) - 1 / 2)) ≠ 0
    rw [he]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) hσ).ne')
      (xi_ne_zero_of_real (2 * σ))
  exact (differentiableOn_narainMellinMeanRegularPart Y Z).analyticAt
    (isOpen_narainMellinRegularDomain.mem_nhds hmem)

/-- Main-term subtraction preserves every arithmetic pole with its full order. -/
theorem narainMellinMeanRegularPart_full_order (p : Resonance) (Y Z : Height) :
    meromorphicOrderAt (narainMellinMeanRegularPart Y Z) p.val =
      -meromorphicOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val := by
  have hp : p.val ≠ (1 / 2 : ℂ) := by
    intro h
    have hn := re_neg_of_xi_shift_eq_zero p.property
    norm_num [h] at hn
  let Q : ℂ → ℂ := fun u => -((3 / (Real.pi : ℂ)) / (u - 1 / 2) ^ 2 +
    narainAverageConstant Y Z / (u - 1 / 2))
  have hQ : AnalyticAt ℂ Q p.val := by
    have hd : AnalyticAt ℂ (fun u : ℂ => u - 1 / 2) p.val := by fun_prop
    exact ((analyticAt_const.div (hd.pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr hp))).add
      (analyticAt_const.div hd (sub_ne_zero.mpr hp))).neg
  have heq : narainMellinMeanRegularPart Y Z =ᶠ[𝓝[≠] p.val]
      narainMellinMean Y Z + Q := by
    have hnear : ∀ᶠ u in 𝓝[≠] p.val, u ≠ (1 / 2 : ℂ) :=
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds hp)
    filter_upwards [hnear] with u hu
    have h := narainMellinMean_principalPart Y Z hu
    dsimp only [Pi.add_apply, Q]
    linear_combination -h
  have hneg : meromorphicOrderAt (narainMellinMean Y Z) p.val < 0 := by
    obtain ⟨n, hn⟩ := narainMellinMean_pole p Y Z
    rw [hn]
    norm_cast
    omega
  rw [meromorphicOrderAt_congr heq,
    meromorphicOrderAt_add_eq_left_of_lt hQ.meromorphicAt
      (hneg.trans_le hQ.meromorphicOrderAt_nonneg), narainMellinMean_full_order]

#print axioms meromorphic_narainMellinMeanRegularPart
#print axioms analyticAt_narainMellinMeanRegularPart_of_real
#print axioms narainMellinMeanRegularPart_full_order
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
