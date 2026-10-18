import GaloisForLFunctions.«arithmetic-positivity-theory».SourceRelativeSchurMarginAndPerturbationCalculus

/-! Exact rank-one pole-readout factorization, codimension-one zero-side nullspace
classification, and smoothed compact-ramp readout decomposition.

For every arithmetic scale `n` and smoothing index `k`, the boundary-corrected source
`H_{n,k} = factorialMuntzSmoothed n k` decomposes as `r_{n,k} + U_{n,k}`, where
`r_{n,k} = factorialMuntzSmoothedRamp n k` is the smoothed compact ramp and
`U_{n,k} = factorialMuntzSmoothedTail n k` is the smoothed noncompact tail.
At every `s` with `Re s > -1` (and hence at every nontrivial zeta zero `ρ` and its
reflection `1 - conj ρ`), their Mellin/Fourier readouts satisfy
`F_{r_{n,k}}(s) = F_{H_{n,k}}(s) - F_{U_{n,k}}(s)`.

Because `F_{H_{n,k}}(ρ) = F_{η_k}(ρ) c_n / ρ` with `c_n = 1 / (2 √(n + 1))`, any finite
linear combination `∑_{n ∈ S} a_n H_{n,k}` has zero-side readout proportional to the
single reciprocal mode `1 / ρ` via the scalar pole functional
`Λ_pole(S, a) = ∑_{n ∈ S} a_n c_n`. Consequently:
1. The corrected-source family spans at most one dimension in the zero-side evaluation
   space at every fixed smoothing index `k`.
2. On the codimension-one hyperplane `Λ_pole(S, a) = 0`, the compact-ramp combination
   `∑_{n ∈ S} a_n r_{n,k}` and the negated tail combination `-∑_{n ∈ S} a_n U_{n,k}`
   have identically equal readouts at every nontrivial zero.
3. Conversely, at any nontrivial zero `ρ`, the unsmoothed corrected combination has
   zero readout if and only if `Λ_pole(S, a) = 0`. -/

open MeasureTheory Set Filter Complex
open scoped Topology Convolution BigOperators ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.CHMDDoobGraph
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The smoothed compact factorial ramp `r_{n,k} = η_k * r_n`. -/
def factorialMuntzSmoothedRamp (n k : ℕ) : ℝ → ℝ :=
  CHMDDoobGraph.mollifier k ⋆[ContinuousLinearMap.mul ℝ ℝ] sourceFactorialRamp (n + 1)

private theorem mollifier_exp_integrable (k : ℕ) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
      (CHMDDoobGraph.mollifier k x : ℂ)) := by
  have hk : Continuous (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ))) := by fun_prop
  exact (hk.mul (Complex.continuous_ofReal.comp
    (mollifier_contDiff k).continuous)).integrable_of_hasCompactSupport
      ((mollifier_compact k).comp_left Complex.ofReal_zero).mul_left

private theorem ramp_exp_integrable (n : ℕ) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
      (sourceFactorialRamp (n + 1) x : ℂ)) := by
  have hk : Continuous (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ))) := by fun_prop
  have hc := hk.mul (Complex.continuous_ofReal.comp (continuous_sourceFactorialRamp (n + 1)))
  exact hc.integrable_of_hasCompactSupport
    ((hasCompactSupport_sourceFactorialRamp (N := n + 1) (by omega)).comp_left
      Complex.ofReal_zero).mul_left

private theorem paperFT_gamma_eq_mellin (f : ℝ → ℝ) (s : ℂ) :
    paperFT (fun x => (f x : ℂ)) (gammaOf s) =
      ∫ x : ℝ, Complex.exp ((s - 1 / 2) * (x : ℂ)) * (f x : ℂ) := by
  simp only [paperFT, gammaOf, mul_div_cancel₀ _ Complex.I_ne_zero, mul_comm]

/-- Exact convolution readout factorization for the smoothed compact ramp at every `s ∈ ℂ`. -/
theorem factorialMuntzSmoothedRamp_readout (n k : ℕ) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
      (factorialMuntzSmoothedRamp n k x : ℂ)) ∧
    (∫ x : ℝ, Complex.exp ((s - 1 / 2) * (x : ℂ)) *
      (factorialMuntzSmoothedRamp n k x : ℂ)) =
      factorialMuntzKernelReadout k s *
        ∫ x : ℝ, Complex.exp ((s - 1 / 2) * (x : ℂ)) *
          (sourceFactorialRamp (n + 1) x : ℂ) :=
  integral_exponential_tilt_convolution (s - 1 / 2)
    (mollifier_exp_integrable k s) (ramp_exp_integrable n s)

/-- On the half-plane `Re s > -1`, the smoothed compact-ramp readout is the exact
difference between the smoothed boundary-corrected readout and the smoothed tail readout. -/
theorem factorialMuntzSmoothedRamp_paperFT_eq_sub (n k : ℕ) {s : ℂ} (hs : -1 < s.re) :
    paperFT (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) (gammaOf s) =
      paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf s) -
        paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf s) := by
  rw [paperFT_gamma_eq_mellin, paperFT_gamma_eq_mellin, paperFT_gamma_eq_mellin,
    (factorialMuntzSmoothedRamp_readout n k s).2,
    (factorialMuntzSmoothed_readout n k s hs).2,
    (factorialMuntzSmoothedTail_readout n k s hs).2]
  change factorialMuntzKernelReadout k s * _ =
    factorialMuntzKernelReadout k s * _ - factorialMuntzKernelReadout k s * _
  rw [← mul_sub, ← factorialMuntzBoundaryCorrected_readout_sub_ramp n s hs]
  ring

/-- Pointwise bound on the smoothed ramp zero-square summand via the corrected and tail summands. -/
theorem factorialMuntzSmoothedRamp_zeroSquareSummand_le (n k : ℕ)
    (ρ : zetaZeroConfig.carrier) :
    zetaZeroSquareSummand (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ρ ≤
      2 * zetaZeroSquareSummand (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ +
        2 * zetaZeroSquareSummand (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ρ := by
  have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
  have hsub := factorialMuntzSmoothedRamp_paperFT_eq_sub n k (s := (ρ : ℂ)) (by linarith [hρ.1])
  unfold zetaZeroSquareSummand
  rw [hsub]
  set A : ℝ := ‖paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ)‖
  set B : ℝ := ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ)‖
  have hnorm : ‖paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ) -
      paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ)‖ ≤ A + B :=
    norm_sub_le _ _
  have hsq : ‖paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ) -
      paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ)‖ ^ 2 ≤
      2 * A ^ 2 + 2 * B ^ 2 := by
    have h1 : ‖paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ) -
        paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ)‖ ^ 2 ≤
        (A + B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (A - B)]
  calc
    (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ) -
          paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ)‖ ^ 2 ≤
        (zetaZeroConfig.mult ρ : ℝ) * (2 * A ^ 2 + 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = 2 * ((zetaZeroConfig.mult ρ : ℝ) * A ^ 2) +
        2 * ((zetaZeroConfig.mult ρ : ℝ) * B ^ 2) := by ring

/-- Every smoothed compact ramp has summable multiplicity-weighted zero-square mass. -/
theorem factorialMuntzSmoothedRamp_zeroSquare_summable (n k : ℕ) :
    Summable (zetaZeroSquareSummand (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))) := by
  refine Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (factorialMuntzSmoothedRamp_zeroSquareSummand_le n k) ?_
  exact ((factorialCorrected_zeroSquare_summable n k).mul_left 2).add
    ((factorialSmoothedTail_zeroSquare_summable n k).mul_left 2)

/-- The smoothed compact ramp zero-square mass is bounded by twice the sum of the
corrected and tail zero-square masses. -/
theorem factorialMuntzSmoothedRamp_zeroSquare_le (n k : ℕ) :
    zetaZeroSquareMass (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ≤
      2 * zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) +
        2 * zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) := by
  have hH := (factorialCorrected_zeroSquare_summable n k).mul_left 2
  have hU := (factorialSmoothedTail_zeroSquare_summable n k).mul_left 2
  calc
    zetaZeroSquareMass (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ≤
        ∑' ρ : zetaZeroConfig.carrier,
          (2 * zetaZeroSquareSummand (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ +
            2 * zetaZeroSquareSummand (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ρ) :=
      (factorialMuntzSmoothedRamp_zeroSquare_summable n k).tsum_le_tsum
        (factorialMuntzSmoothedRamp_zeroSquareSummand_le n k) (hH.add hU)
    _ = 2 * zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) +
        2 * zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) := by
      rw [hH.tsum_add hU, tsum_mul_left, tsum_mul_left]
      rfl

/-- Exact sesquilinear expansion of the smoothed ramp Weil summand at every nontrivial zero. -/
theorem factorialMuntzSmoothedRamp_Wsummand_eq (n k : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) ρ =
    zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ +
    zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ρ -
    zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ρ -
    zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ := by
  have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
  let σ : zetaZeroConfig.carrier := zetaZeroReflectPerm ρ
  have hσ := zetaZeroConfig.strip (σ : ℂ) σ.2
  have hγ : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (σ : ℂ) :=
    (Tail.gammaOf_reflect (ρ : ℂ)).symm
  unfold ZeroConfig.Wsummand
  rw [hγ,
    factorialMuntzSmoothedRamp_paperFT_eq_sub n k (s := (ρ : ℂ)) (by linarith [hρ.1]),
    factorialMuntzSmoothedRamp_paperFT_eq_sub n k (s := (σ : ℂ)) (by linarith [hσ.1]),
    map_sub]
  ring

/-- Exact zero-side sesquilinear expansion of `Re W(r_{n,k}, r_{n,k})`. -/
theorem factorialMuntzSmoothedRamp_re_W_eq (n k : ℕ) :
    (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re =
    (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ))).re +
    (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
    (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
    (zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ))).re := by
  set H : ℝ → ℂ := fun x => (factorialMuntzSmoothed n k x : ℂ)
  set U : ℝ → ℂ := fun x => (factorialMuntzSmoothedTail n k x : ℂ)
  have hHH := summable_Wsummand H H
    (factorialCorrected_zeroSquare_summable n k) (factorialCorrected_zeroSquare_summable n k)
  have hUU := summable_Wsummand U U
    (factorialSmoothedTail_zeroSquare_summable n k) (factorialSmoothedTail_zeroSquare_summable n k)
  have hHU := summable_Wsummand H U
    (factorialCorrected_zeroSquare_summable n k) (factorialSmoothedTail_zeroSquare_summable n k)
  have hUH := summable_Wsummand U H
    (factorialSmoothedTail_zeroSquare_summable n k) (factorialCorrected_zeroSquare_summable n k)
  have hW : zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) =
      zetaZeroConfig.W H H + zetaZeroConfig.W U U -
        zetaZeroConfig.W H U - zetaZeroConfig.W U H := by
    unfold ZeroConfig.W
    simp_rw [factorialMuntzSmoothedRamp_Wsummand_eq n k]
    rw [((hHH.add hUU).sub hHU).tsum_sub hUH, (hHH.add hUU).tsum_sub hHU, hHH.tsum_add hUU]
  rw [hW]
  simp only [Complex.sub_re, Complex.add_re]

/-- The scalar pole-residue functional `Λ_pole(S, a) = ∑_{n ∈ S} a_n / (2 √(n + 1))`
governing the rank-one zero readout of boundary-corrected source combinations. -/
def factorialPoleFunctional (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, a n * (factorialMuntzBoundaryCoefficient n : ℂ)

/-- **Rank-One Zero-Readout Factorization.** For any finite index set `S ⊆ ℕ`, coefficient
family `a : ℕ → ℂ`, smoothing index `k`, and nontrivial zero `ρ`, the linear combination
of smoothed corrected sources has readout `F_{η_k}(ρ) Λ_pole(S, a) / ρ`. -/
theorem sum_factorialMuntzSmoothed_paperFT_gamma_eq (S : Finset ℕ) (a : ℕ → ℂ)
    (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    (∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ)) =
      factorialMuntzKernelReadout k (ρ : ℂ) *
        (factorialPoleFunctional S a / (ρ : ℂ)) := by
  unfold factorialPoleFunctional
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [factorialMuntzSmoothed_paperFT_gamma]
  ring

/-- Unsmoothed rank-one zero-readout factorization at every nontrivial zero `ρ`. -/
theorem sum_factorialMuntzBoundaryCorrected_paperFT_gamma_eq (S : Finset ℕ) (a : ℕ → ℂ)
    (ρ : zetaZeroConfig.carrier) :
    (∑ n ∈ S, a n * paperFT (fun x =>
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
        (gammaOf ρ)) =
      factorialPoleFunctional S a / (ρ : ℂ) := by
  unfold factorialPoleFunctional
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [factorialMuntzBoundaryCorrected_paperFT_gamma]
  ring

/-- **Exact Codimension-One Nullspace Classification (`iff`).** At any nontrivial zero `ρ`,
the unsmoothed boundary-corrected linear combination vanishes at `ρ` if and only if
the scalar pole functional `factorialPoleFunctional S a` vanishes. -/
theorem sum_factorialMuntzBoundaryCorrected_paperFT_eq_zero_iff (S : Finset ℕ) (a : ℕ → ℂ)
    (ρ : zetaZeroConfig.carrier) :
    (∑ n ∈ S, a n * paperFT (fun x =>
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
        (gammaOf ρ)) = 0 ↔
      factorialPoleFunctional S a = 0 := by
  rw [sum_factorialMuntzBoundaryCorrected_paperFT_gamma_eq]
  have hz : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hρ_ne : (ρ : ℂ) ≠ 0 := by
    intro h0
    have hre := hz.2.1
    rw [h0, Complex.zero_re] at hre
    linarith
  exact div_eq_zero_iff.trans (or_iff_left hρ_ne)

/-- **Codimension-One Ramp–Tail Zero-Readout Equivalence.** Whenever `factorialPoleFunctional S a = 0`,
the smoothed compact-ramp combination `∑_{n ∈ S} a_n r_{n,k}` and the negated smoothed-tail
combination `-∑_{n ∈ S} a_n U_{n,k}` have identically equal readouts at every nontrivial zero `ρ`
and every smoothing index `k`. -/
theorem sum_factorialMuntzSmoothedRamp_paperFT_eq_neg_tail_of_pole_zero
    (S : Finset ℕ) (a : ℕ → ℂ) (hzero : factorialPoleFunctional S a = 0)
    (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    (∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) (gammaOf ρ)) =
      -(∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ)) := by
  have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
  have hsplit : (∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) (gammaOf ρ)) =
      (∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ)) -
        (∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [factorialMuntzSmoothedRamp_paperFT_eq_sub n k (s := (ρ : ℂ)) (by linarith [hρ.1]), mul_sub]
  rw [hsplit, sum_factorialMuntzSmoothed_paperFT_gamma_eq, hzero, zero_div, mul_zero, zero_sub]

end

end GaloisForLFunctions.ArithmeticPositivityTheory
