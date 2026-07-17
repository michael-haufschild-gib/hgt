import GaloisForLFunctions.RHTower.VonMangoldtGammaPointedWardReconstruction
import GaloisForLFunctions.RHTower.EulerTranslationAnalyticFaithful

/-!
# Cofinal pointed Ward reconstruction of the Euler--von Mangoldt germ

The finite pointed Gamma Ward law reconstructs the raw source moments from adjacent-depth anomaly
currents.  This file takes the source aperture to infinity without replacing that current by a
formal symbol.  For every positive displacement `x`, it proves:

* absolute summability of the actual von Mangoldt--Gamma atoms;
* exact identification of each atom with the corresponding logarithmically weighted Euler
  `LSeries` term at `s = x + 1`;
* convergence of every finite-aperture raw moment and Gram entry;
* positive semidefiniteness of the infinite raw Gram;
* exact equality of its entries with the analytic Euler moment germ; and
* convergence of every admissible finite adjacent-depth Bianchi Gram entry to that analytic Gram.

This is a source-effectivity theorem on the absolute Euler side.  It does not assert that inverse
critical translation preserves the Gram, nor does it provide a critical all-scale lower bound.
-/

open scoped BigOperators
open Filter Topology LSeries

namespace RHTower

noncomputable section

/-- The `n + 2` Euler atom after the pointed Ward law has removed the Gamma remainder depth. -/
def infiniteVonMangoldtGammaRawAtom (x : ℝ) (a n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt (n + 2) / ((n + 2 : ℕ) : ℝ)) *
    Real.exp (-x * Real.log (n + 2)) * Real.log (n + 2) ^ a

/-- The pointed Gamma atom is the norm-weighted Euler derivative carrier at displacement
`x + 1`. -/
theorem infiniteVonMangoldtGammaRawAtom_eq_eulerCoefficient
    (x : ℝ) (a n : ℕ) :
    infiniteVonMangoldtGammaRawAtom x a n =
      ‖GaloisForLFunctions.RHTower.eulerGeneralizedCoefficient a n‖ *
        Real.exp
          (-GaloisForLFunctions.RHTower.eulerGeneralizedFrequency n * (x + 1)) := by
  have hn : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  rw [infiniteVonMangoldtGammaRawAtom,
    GaloisForLFunctions.RHTower.eulerGeneralizedCoefficient,
    GaloisForLFunctions.RHTower.eulerGeneralizedFrequency,
    vonMangoldtLogCoeff_apply]
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [← Complex.natCast_log]
  rw [norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    abs_of_pos (Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega)))]
  rw [show Real.exp (-Real.log ((n + 2 : ℕ) : ℝ) * (x + 1)) =
      Real.exp (-x * Real.log ((n + 2 : ℕ) : ℝ)) /
        ((n + 2 : ℕ) : ℝ) by
    have hinv : (((n + 2 : ℕ) : ℝ))⁻¹ =
        Real.exp (-Real.log ((n + 2 : ℕ) : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log hn]
    rw [div_eq_mul_inv, hinv, ← Real.exp_add]
    congr 1
    ring]
  norm_num [Nat.cast_add]
  ring

/-- Exact analytic realization of one pointed Gamma atom as one Euler Dirichlet-series term. -/
theorem infiniteVonMangoldtGammaRawAtom_ofReal_eq_term
    (x : ℝ) (a n : ℕ) :
    (infiniteVonMangoldtGammaRawAtom x a n : ℂ) =
      LSeries.term (vonMangoldtLogCoeff a) ((x + 1 : ℝ) : ℂ) (n + 2) := by
  have hn0 : n + 2 ≠ 0 := by omega
  have hn : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
  rw [LSeries.term_of_ne_zero hn0, vonMangoldtLogCoeff_apply,
    infiniteVonMangoldtGammaRawAtom]
  rw [← Complex.natCast_log]
  push_cast
  norm_num [Nat.cast_add]
  have hbase : ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) := by norm_num
  have hexponent : ((x : ℂ) + 1) = (((x + 1 : ℝ)) : ℂ) := by norm_num
  rw [hbase, hexponent,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ) + 2)]
  rw [Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ) + 2)]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hN : ((n : ℂ) + 2) =
      Complex.exp (Real.log ((n : ℝ) + 2)) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by positivity : 0 < (n : ℝ) + 2)]
    norm_num
  rw [hN]
  simp_rw [← Complex.exp_neg]
  have hexp :
      Complex.exp (-((Real.log ((n : ℝ) + 2) : ℝ) : ℂ)) *
          Complex.exp (-((x * Real.log ((n : ℝ) + 2) : ℝ) : ℂ)) =
        Complex.exp
          (-((Real.log ((n : ℝ) + 2) : ℂ) * ((x : ℂ) + 1))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  push_cast at hexp ⊢
  rw [show
      (ArithmeticFunction.vonMangoldt (n + 2) : ℂ) *
            Complex.exp (-((Real.log ((n : ℝ) + 2) : ℝ) : ℂ)) *
          Complex.exp
            (-((x : ℂ) * (Real.log ((n : ℝ) + 2) : ℂ))) =
        (ArithmeticFunction.vonMangoldt (n + 2) : ℂ) *
          Complex.exp
            (-((Real.log ((n : ℝ) + 2) : ℂ) * ((x : ℂ) + 1))) by
    rw [mul_assoc, hexp]]
  ring

/-- Absolute convergence of every pointed raw Euler--Gamma moment at positive displacement. -/
theorem summable_infiniteVonMangoldtGammaRawAtom
    {x : ℝ} (hx : 0 < x) (a : ℕ) :
    Summable (infiniteVonMangoldtGammaRawAtom x a) := by
  have hs := GaloisForLFunctions.RHTower.summable_eulerGeneralizedCoefficient
    a (show 1 < x + 1 by linarith)
  exact hs.congr (fun n ↦
    (infiniteVonMangoldtGammaRawAtom_eq_eulerCoefficient x a n).symm)

/-- Infinite-aperture raw source moment. -/
def infiniteVonMangoldtGammaRawMoment (x : ℝ) (a : ℕ) : ℝ :=
  ∑' n : ℕ, infiniteVonMangoldtGammaRawAtom x a n

/-- The infinite pointed raw moment is literally the logarithmically weighted Euler `LSeries`. -/
theorem infiniteVonMangoldtGammaRawMoment_ofReal_eq_weightedLSeries
    {x : ℝ} (hx : 0 < x) (a : ℕ) :
    (infiniteVonMangoldtGammaRawMoment x a : ℂ) =
      LSeries (vonMangoldtLogCoeff a) ((x + 1 : ℝ) : ℂ) := by
  have hscast : Summable
      (fun n : ℕ ↦ (infiniteVonMangoldtGammaRawAtom x a n : ℂ)) := by
    apply Summable.of_norm
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (summable_infiniteVonMangoldtGammaRawAtom hx a).norm
  have htail : Summable
      (fun n : ℕ ↦ LSeries.term (vonMangoldtLogCoeff a)
        ((x + 1 : ℝ) : ℂ) (n + 2)) :=
    hscast.congr fun n ↦
      infiniteVonMangoldtGammaRawAtom_ofReal_eq_term x a n
  have hsum : Summable
      (LSeries.term (vonMangoldtLogCoeff a) ((x + 1 : ℝ) : ℂ)) :=
    (summable_nat_add_iff 2).mp htail
  have hsplit := hsum.sum_add_tsum_nat_add 2
  rw [infiniteVonMangoldtGammaRawMoment, Complex.ofReal_tsum,
    show LSeries (vonMangoldtLogCoeff a) ((x + 1 : ℝ) : ℂ) =
      ∑' n : ℕ, LSeries.term (vonMangoldtLogCoeff a)
        ((x + 1 : ℝ) : ℂ) n from rfl,
    ← hsplit]
  have hhead : ∑ n ∈ Finset.range 2,
      LSeries.term (vonMangoldtLogCoeff a) ((x + 1 : ℝ) : ℂ) n = 0 := by
    simp [Finset.sum_range_succ, LSeries.term_def, vonMangoldtLogCoeff_one]
  rw [hhead, zero_add]
  exact tsum_congr fun n ↦
    infiniteVonMangoldtGammaRawAtom_ofReal_eq_term x a n

/-- Real-form identification with the existing analytic Euler moment germ. -/
theorem infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment
    {x : ℝ} (hx : 0 < x) (a : ℕ) :
    infiniteVonMangoldtGammaRawMoment x a =
      vonMangoldtLogMoment a (x + 1) := by
  have h := congrArg Complex.re
    (infiniteVonMangoldtGammaRawMoment_ofReal_eq_weightedLSeries hx a)
  simpa [vonMangoldtLogMoment] using h

/-- The existing finite raw moment is the initial partial sum of the infinite source. -/
theorem finiteVonMangoldtGammaRawMoment_eq_partialSum
    (M : ℕ) (x : ℝ) (a : ℕ) :
    finiteVonMangoldtGammaRawMoment M x a =
      ∑ n ∈ Finset.range M, infiniteVonMangoldtGammaRawAtom x a n := by
  rw [finiteVonMangoldtGammaRawMoment, finiteExponentialGammaRawMoment]
  simpa [infiniteVonMangoldtGammaRawAtom] using
    Fin.sum_univ_eq_sum_range
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt (n + 2) / ((n + 2 : ℕ) : ℝ) *
          Real.exp (-x * Real.log ((n + 2 : ℕ) : ℝ)) *
            Real.log ((n + 2 : ℕ) : ℝ) ^ a) M

/-- Cofinal convergence of every pointed raw moment. -/
theorem tendsto_finiteVonMangoldtGammaRawMoment
    {x : ℝ} (hx : 0 < x) (a : ℕ) :
    Tendsto (fun M ↦ finiteVonMangoldtGammaRawMoment M x a) atTop
      (nhds (infiniteVonMangoldtGammaRawMoment x a)) := by
  rw [infiniteVonMangoldtGammaRawMoment]
  convert (summable_infiniteVonMangoldtGammaRawAtom hx a).hasSum.tendsto_sum_nat using 1
  funext M
  exact finiteVonMangoldtGammaRawMoment_eq_partialSum M x a

/-- Infinite raw mixed moment Gram. -/
def infiniteVonMangoldtGammaRawGram
    {n : ℕ} (x : ℝ) (a : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ infiniteVonMangoldtGammaRawMoment x (a i + a j)

/-- Entrywise convergence of the finite raw Grams. -/
theorem tendsto_finiteVonMangoldtGammaRawGram_apply
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ) (i j : Fin n) :
    Tendsto (fun M ↦ finiteVonMangoldtGammaRawGram M x a i j) atTop
      (nhds (infiniteVonMangoldtGammaRawGram x a i j)) := by
  simpa only [finiteVonMangoldtGammaRawGram_apply,
    infiniteVonMangoldtGammaRawGram] using
      tendsto_finiteVonMangoldtGammaRawMoment hx (a i + a j)

/-- The cofinal raw Euler--Gamma Gram remains positive semidefinite. -/
theorem infiniteVonMangoldtGammaRawGram_posSemidef
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ) :
    (infiniteVonMangoldtGammaRawGram x a).PosSemidef := by
  have hherm : (infiniteVonMangoldtGammaRawGram x a).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, infiniteVonMangoldtGammaRawGram,
      star_trivial, add_comm]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro c
  have hrow (i : Fin n) :
      Tendsto
        (fun M ↦ (finiteVonMangoldtGammaRawGram M x a).mulVec c i)
        atTop
        (nhds ((infiniteVonMangoldtGammaRawGram x a).mulVec c i)) := by
    simp only [Matrix.mulVec, dotProduct]
    apply tendsto_finsetSum
    intro j hj
    exact (tendsto_finiteVonMangoldtGammaRawGram_apply hx a i j).mul_const (c j)
  have hquad :
      Tendsto
        (fun M ↦ star c ⬝ᵥ (finiteVonMangoldtGammaRawGram M x a).mulVec c)
        atTop
        (nhds (star c ⬝ᵥ (infiniteVonMangoldtGammaRawGram x a).mulVec c)) := by
    simp only [dotProduct]
    apply tendsto_finsetSum
    intro i hi
    exact tendsto_const_nhds.mul (hrow i)
  apply ge_of_tendsto hquad
  exact Filter.Eventually.of_forall fun M ↦
    (finiteVonMangoldtGammaRawGram_posSemidef M x a).dotProduct_mulVec_nonneg c

/-- The cofinal pointed Gamma--Bianchi Gram, written directly in the analytic Euler realization. -/
def vonMangoldtGammaCofinalBianchiGram
    {n : ℕ} (x : ℝ) (a : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ vonMangoldtLogMoment (a i + a j) (x + 1)

/-- The raw-source and analytic-Euler realizations of the cofinal Bianchi Gram agree exactly. -/
theorem infiniteVonMangoldtGammaRawGram_eq_cofinalBianchiGram
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ) :
    infiniteVonMangoldtGammaRawGram x a =
      vonMangoldtGammaCofinalBianchiGram x a := by
  ext i j
  exact infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment
    hx (a i + a j)

/-- Unconditional positivity of every finite analytic Euler packet reconstructed by the cofinal
pointed Gamma Bianchi current. -/
theorem vonMangoldtGammaCofinalBianchiGram_posSemidef
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a : Fin n → ℕ) :
    (vonMangoldtGammaCofinalBianchiGram x a).PosSemidef := by
  rw [← infiniteVonMangoldtGammaRawGram_eq_cofinalBianchiGram hx a]
  exact infiniteVonMangoldtGammaRawGram_posSemidef hx a

/-- Every admissible finite adjacent-depth anomaly Bianchi entry converges to the corresponding
analytic Euler moment.  The Gamma-depth label disappears because the pointed Ward law reconstructs
the same raw source before the cofinal limit is taken. -/
theorem tendsto_finiteVonMangoldtGammaAnomalyBianchiMixedGram_apply
    {x : ℝ} (hx : 0 < x) {n : ℕ} (a b : Fin n → ℕ)
    (hadm : ∀ i j, b i + b j < a i + a j) (i j : Fin n) :
    Tendsto
      (fun M ↦ finiteVonMangoldtGammaAnomalyBianchiMixedGram M x a b hadm i j)
      atTop
      (nhds (vonMangoldtGammaCofinalBianchiGram x a i j)) := by
  rw [show (fun M ↦
      finiteVonMangoldtGammaAnomalyBianchiMixedGram M x a b hadm i j) =
      (fun M ↦ finiteVonMangoldtGammaRawGram M x a i j) by
    funext M
    rw [finiteVonMangoldtGammaAnomalyBianchiMixedGram_eq_rawGram]]
  simpa only [vonMangoldtGammaCofinalBianchiGram,
    infiniteVonMangoldtGammaRawGram_eq_cofinalBianchiGram hx a] using
      tendsto_finiteVonMangoldtGammaRawGram_apply hx a i j

end

end RHTower
