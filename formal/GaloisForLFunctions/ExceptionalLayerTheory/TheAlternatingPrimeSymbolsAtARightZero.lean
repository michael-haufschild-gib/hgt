import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.HTGeometry.HurwitzZetaEulerMaclaurinBridge
import GaloisForLFunctions.RHTower.BaezDuarteBurnolMultiplicityAllZeros

/-!
# The first surviving derivative of the alternating prime count

At a zero of multiplicity `k+1`, the two alternating rows have orders
`k+1` and `k`. Their derivatives of order `k` therefore distinguish
the two rows after multiplication by any holomorphic test function.
-/

noncomputable section

open Complex Filter Finset Topology ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

open HeckeLFunctions

/-- Complex coefficients of a real arithmetic function. -/
abbrev alternatingRowCoeffs (f : ArithmeticFunction ℝ) (n : ℕ) : ℂ := (f n : ℂ)

/-- Continuations from the bounded parity row and the square-root prime row. -/
def paritySymbol := growthCont (alternatingRowCoeffs alternatingDivisorCoeff) 0

/-- The Dirichlet symbol after counting the ordinary prime excess. -/
def parityPrimeSymbol := growthCont (alternatingRowCoeffs alternatingPrimeExcess) (1/2)

/-- The two summatory estimates at real cutoffs. -/
theorem alternatingRow_growth (x : ℝ) (hx : 1 ≤ x) :
    (‖∑ n ∈ Icc 1 ⌊x⌋₊, alternatingRowCoeffs alternatingDivisorCoeff n‖ ≤ 1*x^(0:ℝ)) ∧
    (‖∑ n ∈ Icc 1 ⌊x⌋₊, alternatingRowCoeffs alternatingPrimeExcess n‖ ≤
      (75 + 2 * |Real.eulerMascheroniConstant|)*x^(1/2:ℝ)) := by
  simp only [alternatingRowCoeffs, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  constructor
  · rw [prefix_alternatingDivisorCoeff, abs_of_nonneg (Nat.cast_nonneg _), Real.rpow_zero, mul_one]
    exact_mod_cast (show ⌊x⌋₊ % 2 ≤ 1 by omega)
  · rw [← Real.sqrt_eq_rpow]
    exact (abs_prefix_alternatingPrimeExcess _).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.floor_le (zero_le_one.trans hx))) (by positivity))

private theorem factor_analytic (s : ℂ) : AnalyticAt ℂ alternatingDivisorFactor s := by
  have hp : Differentiable ℂ (fun z : ℂ => (2:ℂ)^(-z)) :=
    differentiable_neg.const_cpow (Or.inl (by norm_num))
  exact analyticAt_const.sub (analyticAt_const.mul (hp.analyticAt s))

private theorem factor_ne_zero {s : ℂ} (hs : s.re < 1) : alternatingDivisorFactor s ≠ 0 := by
  have he : (2:ℂ)^(1-s) = 2*(2:ℂ)^(-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  apply sub_ne_zero.mpr
  rw [← he]
  intro h
  have hnorm : 1 < ‖((2:ℝ):ℂ)^(1-s)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2), sub_re, one_re]
    exact Real.one_lt_rpow (by norm_num) (sub_pos.mpr hs)
  change 1 < ‖(2:ℂ)^(1-s)‖ at hnorm
  rw [← h,norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- Continuation through the strip, with the logarithmic derivative denominator cancelled. -/
theorem alternatingSymbols_eq {s : ℂ} (hs : 1/2 < s.re) (hs1 : s ≠ 1) :
    paritySymbol s = alternatingDivisorFactor s * riemannZeta s ∧
    parityPrimeSymbol s = -alternatingDivisorFactor s *
      (deriv riemannZeta s + riemannZeta s * riemannZeta s) := by
  have hca : alternatingRowCoeffs alternatingDivisorCoeff 0 = 0 := by simp [alternatingRowCoeffs]
  have hcb : alternatingRowCoeffs alternatingPrimeExcess 0 = 0 := by simp [alternatingRowCoeffs]
  have ha := fun x hx => (alternatingRow_growth x hx).1
  have hb := fun x hx => (alternatingRow_growth x hx).2
  have hop (t : ℝ) : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const continuous_re
  have hA := differentiableOn_growthCont hca (le_refl 0) ha
  have hB := differentiableOn_growthCont hcb (by norm_num : (0:ℝ) ≤ 1/2) hb
  constructor
  · apply HTGeometry.eq_of_eq_on_one_lt_re (c := 0) (by norm_num) _ _ _ (by linarith only [hs]) hs1
    · exact fun z hz _ => hA.differentiableAt ((hop 0).mem_nhds hz)
    · exact fun z _ hz => (factor_analytic z).differentiableAt.mul (differentiableAt_riemannZeta hz)
    · intro z hz
      obtain ⟨⟨hconv,he⟩,-⟩ := alternatingDivisor_series_on_euler hz
      exact (growthCont_eq_LSeries hca (le_refl 0) ha (by linarith only [hz]) hconv).trans he
  · apply HTGeometry.eq_of_eq_on_one_lt_re (c := 1/2) (by norm_num) _ _ _ hs hs1
    · exact fun z hz _ => hB.differentiableAt ((hop _).mem_nhds hz)
    · intro z _ hz
      have hζ := analyticOn_riemannZeta z hz
      exact (factor_analytic z).neg.differentiableAt.mul
        ((hζ.deriv.add (hζ.mul hζ)).differentiableAt)
    · intro z hz
      obtain ⟨-,⟨hconv,he⟩⟩ := alternatingDivisor_series_on_euler hz
      change growthCont _ _ z = _
      rw [growthCont_eq_LSeries hcb (by norm_num : (0:ℝ) ≤ 1/2) hb (by linarith only [hz]) hconv,he]
      field_simp [riemannZeta_ne_zero_of_one_lt_re hz]
      ring

/-- Leibniz's formula at the first possibly nonzero derivative of the right factor. -/
private theorem lowest_product_deriv {k : ℕ} {ρ : ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f ρ) (hg : AnalyticAt ℂ g ρ) (hzero : ∀ j < k, iteratedDeriv j g ρ = 0) :
    iteratedDeriv k (fun s => f s * g s) ρ = f ρ * iteratedDeriv k g ρ := by
  change iteratedDeriv k (f*g) ρ = _
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, sum_eq_single_of_mem 0 (by simp)]
  · simp
  · intro j hj hj0
    have hjk := mem_range.mp hj
    rw [hzero (k-j) (by omega), mul_zero]

/-- Every right zero has a derivative order killing the alternating divisor row.
At the same order its prime convolution evaluates each analytic test at that zero
with a fixed nonzero coefficient. -/
theorem alternatingSymbols_first_surviving_derivative {ρ : ℂ} (hhalf : 1/2 < ρ.re)
    (hone : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∃ k : ℕ, ∃ d : ℂ, d ≠ 0 ∧ ∀ f : ℂ → ℂ, AnalyticAt ℂ f ρ →
      iteratedDeriv k (fun s => f s * paritySymbol s) ρ = 0 ∧
      iteratedDeriv k (fun s => f s * parityPrimeSymbol s) ρ = f ρ * d := by
  have hρ1 : ρ ≠ 1 := fun h => (ne_of_lt hone) (by rw [h,one_re])
  have hζ := analyticOn_riemannZeta ρ hρ1
  obtain ⟨hm,hlow⟩ := _root_.RHTower.one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta hρ1 hz
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
      (x := 2) (by simp) (by simpa using hρ1)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2:ℂ).re)))]
    exact ENat.zero_ne_top
  obtain ⟨k,hk⟩ : ∃ k, analyticOrderNatAt riemannZeta ρ = k+1 :=
    ⟨analyticOrderNatAt riemannZeta ρ - 1, by omega⟩
  rw [hk] at hlow
  have hn : iteratedDeriv (k+1) riemannZeta ρ ≠ 0 := by
    intro he
    have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := k+2) hζ).mpr
      (fun j hj => by
        by_cases h : j < k+1
        · exact hlow j h
        · rwa [show j = k+1 by omega])
    rw [← Nat.cast_analyticOrderNatAt htop,hk] at hle
    exact (show ¬ k+2 ≤ k+1 by omega) (by exact_mod_cast hle)
  have hcomp : IsOpen ({1}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hopen : {s : ℂ | 1/2 < s.re ∧ s ≠ 1} ∈ 𝓝 ρ :=
    ((isOpen_lt continuous_const continuous_re).inter hcomp).mem_nhds ⟨hhalf,hρ1⟩
  refine ⟨k, -alternatingDivisorFactor ρ * iteratedDeriv (k+1) riemannZeta ρ,
    mul_ne_zero (neg_ne_zero.mpr (factor_ne_zero hone)) hn, fun f hf => ?_⟩
  let g := fun s => f s * alternatingDivisorFactor s
  have hg : AnalyticAt ℂ g ρ := hf.mul (factor_analytic ρ)
  have hkill (u : ℂ → ℂ) (hu : AnalyticAt ℂ u ρ) :
      iteratedDeriv k (fun s => u s * riemannZeta s) ρ = 0 := by
    rw [lowest_product_deriv hu hζ (fun j hj => hlow j (by omega)),
      hlow k (by omega),mul_zero]
  constructor
  · have he : (fun s => f s * paritySymbol s) =ᶠ[𝓝 ρ] fun s => g s * riemannZeta s := by
      filter_upwards [hopen] with s hs
      rw [(alternatingSymbols_eq hs.1 hs.2).1]
      exact (mul_assoc _ _ _).symm
    exact (he.iteratedDeriv_eq k).trans (hkill g hg)
  · let u := fun s => -g s * deriv riemannZeta s
    let v := fun s => (-g s * riemannZeta s) * riemannZeta s
    have hu : AnalyticAt ℂ u ρ := hg.neg.mul hζ.deriv
    have hv : AnalyticAt ℂ v ρ := (hg.neg.mul hζ).mul hζ
    have he : (fun s => f s * parityPrimeSymbol s) =ᶠ[𝓝 ρ] u+v := by
      filter_upwards [hopen] with s hs
      simp only [Pi.add_apply,u,v,g,(alternatingSymbols_eq hs.1 hs.2).2]
      ring
    rw [he.iteratedDeriv_eq k,iteratedDeriv_add hu.contDiffAt hv.contDiffAt,
      show iteratedDeriv k v ρ = 0 from hkill _ (hg.neg.mul hζ),add_zero]
    change iteratedDeriv k (fun s => (-g s) * deriv riemannZeta s) ρ = _
    calc
      _ = (-g ρ)*iteratedDeriv k (deriv riemannZeta) ρ :=
        lowest_product_deriv (k := k) (f := fun s => -g s) hg.neg hζ.deriv (fun j hj => by
          rw [← iteratedDeriv_succ']; exact hlow (j+1) (by omega))
      _ = _ := by rw [← iteratedDeriv_succ']; dsimp only [g]; ring

#print axioms alternatingSymbols_eq
#print axioms alternatingSymbols_first_surviving_derivative

end GaloisForLFunctions.ExceptionalLayerTheory
