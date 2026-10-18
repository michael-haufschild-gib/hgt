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

/-- Finite complex linear combination of smoothed boundary-corrected sources
`H_{S, a, k}(x) = ∑_{n ∈ S} a_n H_{n,k}(x)`. -/
def factorialSmoothedCombo (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, a n * (factorialMuntzSmoothed n k x : ℂ)

/-- Finite complex linear combination of smoothed compact factorial ramps
`R_{S, a, k}(x) = ∑_{n ∈ S} a_n r_{n,k}(x)`. -/
def factorialSmoothedRampCombo (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, a n * (factorialMuntzSmoothedRamp n k x : ℂ)

/-- Finite complex linear combination of smoothed factorial correction tails
`U_{S, a, k}(x) = ∑_{n ∈ S} a_n U_{n,k}(x)`. -/
def factorialSmoothedTailCombo (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, a n * (factorialMuntzSmoothedTail n k x : ℂ)

private theorem paperFT_finset_sum_gamma (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℝ → ℝ) (s : ℂ)
    (hi : ∀ n ∈ S, Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) * (g n x : ℂ))) :
    paperFT (fun x => ∑ n ∈ S, a n * (g n x : ℂ)) (gammaOf s) =
      ∑ n ∈ S, a n * paperFT (fun x => (g n x : ℂ)) (gammaOf s) := by
  have h1 : paperFT (fun x => ∑ n ∈ S, a n * (g n x : ℂ)) (gammaOf s) =
      ∫ x : ℝ, ∑ n ∈ S, a n * (Complex.exp ((s - 1 / 2) * (x : ℂ)) * (g n x : ℂ)) := by
    simp only [paperFT, gammaOf, mul_div_cancel₀ _ Complex.I_ne_zero]
    congr 1
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [h1, integral_finsetSum S (fun n hn => (hi n hn).const_mul (a n))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, paperFT_gamma_eq_mellin]

/-- Exact zero-readout factorization for the physical linear-combination function
`factorialSmoothedCombo S a k`. -/
theorem paperFT_factorialSmoothedCombo_gamma (S : Finset ℕ) (a : ℕ → ℂ)
    (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    paperFT (factorialSmoothedCombo S a k) (gammaOf ρ) =
      factorialMuntzKernelReadout k (ρ : ℂ) *
        (factorialPoleFunctional S a / (ρ : ℂ)) := by
  have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
  unfold factorialSmoothedCombo
  rw [paperFT_finset_sum_gamma S a (fun n => factorialMuntzSmoothed n k) (ρ : ℂ)
    (fun n _ => (factorialMuntzSmoothed_readout n k (ρ : ℂ) (by linarith [hρ.1])).1),
    sum_factorialMuntzSmoothed_paperFT_gamma_eq]

/-- Exact linearity of `paperFT` at `gammaOf s` for `factorialSmoothedRampCombo`. -/
theorem paperFT_factorialSmoothedRampCombo_gamma (S : Finset ℕ) (a : ℕ → ℂ)
    (k : ℕ) (s : ℂ) :
    paperFT (factorialSmoothedRampCombo S a k) (gammaOf s) =
      ∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) (gammaOf s) := by
  unfold factorialSmoothedRampCombo
  exact paperFT_finset_sum_gamma S a (fun n => factorialMuntzSmoothedRamp n k) s
    (fun n _ => (factorialMuntzSmoothedRamp_readout n k s).1)

/-- Exact linearity of `paperFT` at `gammaOf s` (`Re s > -1`) for `factorialSmoothedTailCombo`. -/
theorem paperFT_factorialSmoothedTailCombo_gamma (S : Finset ℕ) (a : ℕ → ℂ)
    (k : ℕ) {s : ℂ} (hs : -1 < s.re) :
    paperFT (factorialSmoothedTailCombo S a k) (gammaOf s) =
      ∑ n ∈ S, a n * paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf s) := by
  unfold factorialSmoothedTailCombo
  exact paperFT_finset_sum_gamma S a (fun n => factorialMuntzSmoothedTail n k) s
    (fun n _ => (factorialMuntzSmoothedTail_readout n k s hs).1)

/-- On the pole-free hyperplane `factorialPoleFunctional S a = 0`, the linear-combination
function `factorialSmoothedCombo S a k` has vanishing readout at every nontrivial zero `ρ`. -/
theorem paperFT_factorialSmoothedCombo_eq_zero_of_pole_zero
    (S : Finset ℕ) (a : ℕ → ℂ) (hzero : factorialPoleFunctional S a = 0)
    (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    paperFT (factorialSmoothedCombo S a k) (gammaOf ρ) = 0 := by
  rw [paperFT_factorialSmoothedCombo_gamma, hzero, zero_div, mul_zero]

/-- **Zero-Square Sampling Mass Collapse on the Pole-Free Hyperplane.**
Whenever `factorialPoleFunctional S a = 0`, the corrected-source combination
`factorialSmoothedCombo S a k` has identically zero multiplicity-weighted sampling mass
`Z(H_{S, a, k}) = 0` at every smoothing index `k`. -/
theorem zetaZeroSquareMass_factorialSmoothedCombo_eq_zero_of_pole_zero
    (S : Finset ℕ) (a : ℕ → ℂ) (hzero : factorialPoleFunctional S a = 0) (k : ℕ) :
    zetaZeroSquareMass (factorialSmoothedCombo S a k) = 0 := by
  unfold zetaZeroSquareMass
  have h0 : (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroSquareSummand (factorialSmoothedCombo S a k) ρ) = fun _ => 0 := by
    funext ρ
    unfold zetaZeroSquareSummand
    rw [paperFT_factorialSmoothedCombo_eq_zero_of_pole_zero S a hzero k ρ,
      norm_zero, sq, mul_zero, mul_zero]
  rw [h0, tsum_zero]

/-- **Weil Pairing Collapse on the Pole-Free Hyperplane.**
Whenever `factorialPoleFunctional S a = 0`, the corrected-source combination
`factorialSmoothedCombo S a k` has identically zero Weil pairing against any test `g`
in both slots. -/
theorem weil_factorialSmoothedCombo_eq_zero_of_pole_zero
    (S : Finset ℕ) (a : ℕ → ℂ) (hzero : factorialPoleFunctional S a = 0)
    (k : ℕ) (g : ℝ → ℂ) :
    zetaZeroConfig.W (factorialSmoothedCombo S a k) g = 0 ∧
      zetaZeroConfig.W g (factorialSmoothedCombo S a k) = 0 := by
  constructor
  · unfold ZeroConfig.W
    have h0 : (fun ρ : zetaZeroConfig.carrier =>
        zetaZeroConfig.Wsummand (factorialSmoothedCombo S a k) g ρ) = fun _ => 0 := by
      funext ρ
      unfold ZeroConfig.Wsummand
      rw [paperFT_factorialSmoothedCombo_eq_zero_of_pole_zero S a hzero k ρ,
        mul_zero, zero_mul]
    rw [h0, tsum_zero]
  · unfold ZeroConfig.W
    have h0 : (fun ρ : zetaZeroConfig.carrier =>
        zetaZeroConfig.Wsummand g (factorialSmoothedCombo S a k) ρ) = fun _ => 0 := by
      funext ρ
      let σ : zetaZeroConfig.carrier := zetaZeroReflectPerm ρ
      have hγ : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (σ : ℂ) :=
        (Tail.gammaOf_reflect (ρ : ℂ)).symm
      unfold ZeroConfig.Wsummand
      rw [hγ, paperFT_factorialSmoothedCombo_eq_zero_of_pole_zero S a hzero k σ,
        map_zero, mul_zero]
    rw [h0, tsum_zero]

/-- On the pole-free hyperplane `factorialPoleFunctional S a = 0`, the physical linear-combination
functions `factorialSmoothedRampCombo S a k` and `factorialSmoothedTailCombo S a k` have
opposite readouts at every nontrivial zero `ρ`. -/
theorem paperFT_factorialSmoothedRampCombo_eq_neg_tailCombo_of_pole_zero
    (S : Finset ℕ) (a : ℕ → ℂ) (hzero : factorialPoleFunctional S a = 0)
    (k : ℕ) (ρ : zetaZeroConfig.carrier) :
    paperFT (factorialSmoothedRampCombo S a k) (gammaOf ρ) =
      -paperFT (factorialSmoothedTailCombo S a k) (gammaOf ρ) := by
  have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
  rw [paperFT_factorialSmoothedRampCombo_gamma,
    paperFT_factorialSmoothedTailCombo_gamma S a k (by linarith [hρ.1]),
    sum_factorialMuntzSmoothedRamp_paperFT_eq_neg_tail_of_pole_zero S a hzero k ρ]

/-- **Full Zero-Square Mass and Weil Energy Equivalence on the Pole-Free Hyperplane.**
Whenever `factorialPoleFunctional S a = 0`, the smoothed compact-ramp linear combination
`R_{S, a, k}` and the smoothed tail linear combination `U_{S, a, k}` have identically equal
zero-square sampling mass `Z(R_{S, a, k}) = Z(U_{S, a, k})` and identically equal complete
zero-side Weil energy `W(R_{S, a, k}, R_{S, a, k}) = W(U_{S, a, k}, U_{S, a, k})` at every
smoothing index `k`, with zero `O(1/N)` pole-correction loss. -/
theorem zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero
    (S : Finset ℕ) (a : ℕ → ℂ) (hzero : factorialPoleFunctional S a = 0) (k : ℕ) :
    zetaZeroSquareMass (factorialSmoothedRampCombo S a k) =
      zetaZeroSquareMass (factorialSmoothedTailCombo S a k) ∧
    zetaZeroConfig.W (factorialSmoothedRampCombo S a k) (factorialSmoothedRampCombo S a k) =
      zetaZeroConfig.W (factorialSmoothedTailCombo S a k) (factorialSmoothedTailCombo S a k) := by
  refine ⟨?_, ?_⟩
  · unfold zetaZeroSquareMass
    congr 1
    funext ρ
    unfold zetaZeroSquareSummand
    rw [paperFT_factorialSmoothedRampCombo_eq_neg_tailCombo_of_pole_zero S a hzero k ρ, norm_neg]
  · unfold ZeroConfig.W
    congr 1
    funext ρ
    let σ : zetaZeroConfig.carrier := zetaZeroReflectPerm ρ
    have hγ : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (σ : ℂ) :=
      (Tail.gammaOf_reflect (ρ : ℂ)).symm
    unfold ZeroConfig.Wsummand
    rw [hγ,
      paperFT_factorialSmoothedRampCombo_eq_neg_tailCombo_of_pole_zero S a hzero k ρ,
      paperFT_factorialSmoothedRampCombo_eq_neg_tailCombo_of_pole_zero S a hzero k σ,
      map_neg]
    ring

/-- Canonical two-scale pole-free coefficient family on `{n₁, n₂}` (`n₁ ≠ n₂`):
`a(n₁) = c_{n₂}`, `a(n₂) = -c_{n₁}`, and `0` elsewhere, where
`c_n = factorialMuntzBoundaryCoefficient n = 1 / (2 √(n + 1))`. -/
def twoScalePoleFreeCoeffs (n₁ n₂ : ℕ) (n : ℕ) : ℂ :=
  if n = n₁ then (factorialMuntzBoundaryCoefficient n₂ : ℂ)
  else if n = n₂ then -(factorialMuntzBoundaryCoefficient n₁ : ℂ)
  else 0

theorem twoScalePoleFreeCoeffs_ne_zero (n₁ n₂ : ℕ) :
    twoScalePoleFreeCoeffs n₁ n₂ n₁ ≠ 0 := by
  unfold twoScalePoleFreeCoeffs
  rw [if_pos rfl]
  exact_mod_cast (factorialMuntzBoundaryCoefficient_pos n₂).ne'

/-- For any two distinct scales `n₁ ≠ n₂`, `twoScalePoleFreeCoeffs n₁ n₂` lies in the
kernel of `factorialPoleFunctional {n₁, n₂}`. -/
theorem factorialPoleFunctional_twoScalePoleFreeCoeffs_eq_zero
    {n₁ n₂ : ℕ} (hne : n₁ ≠ n₂) :
    factorialPoleFunctional ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂) = 0 := by
  unfold factorialPoleFunctional twoScalePoleFreeCoeffs
  have hnot : n₁ ∉ ({n₂} : Finset ℕ) := by simp [hne]
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp only [↓reduceIte, hne.symm]
  ring

/-- **Canonical Two-Scale Pole-Free Ramp–Tail Coercivity Transfer.**
For any two distinct arithmetic scales `n₁ ≠ n₂` and any smoothing index `k`, the canonical
two-scale pole-free combination of smoothed compact ramps has identically the same zero-square
sampling mass and complete zero-side Weil energy as the corresponding two-scale combination
of smoothed tails. -/
theorem two_scale_pole_free_pair_zeroSquare_and_weil_eq
    {n₁ n₂ : ℕ} (hne : n₁ ≠ n₂) (k : ℕ) :
    zetaZeroSquareMass
      (factorialSmoothedRampCombo ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂) k) =
    zetaZeroSquareMass
      (factorialSmoothedTailCombo ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂) k) ∧
    zetaZeroConfig.W
      (factorialSmoothedRampCombo ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂) k)
      (factorialSmoothedRampCombo ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂) k) =
    zetaZeroConfig.W
      (factorialSmoothedTailCombo ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂) k)
      (factorialSmoothedTailCombo ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂) k) :=
  zeroSquareMass_and_weil_rampCombo_eq_tailCombo_of_pole_zero
    ({n₁, n₂} : Finset ℕ) (twoScalePoleFreeCoeffs n₁ n₂)
    (factorialPoleFunctional_twoScalePoleFreeCoeffs_eq_zero hne) k

end

end GaloisForLFunctions.ArithmeticPositivityTheory
