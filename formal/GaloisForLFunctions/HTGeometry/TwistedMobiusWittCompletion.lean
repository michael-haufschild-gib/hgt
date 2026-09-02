import GaloisForLFunctions.RHTower.ShiftedEulerMobiusSynthesis
import GaloisForLFunctions.RHTower.SeamRealAxisGrowth
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization

/-!
# Twisted Möbius--Witt completion

Exact Möbius recovery annihilates every nontrivial divisor fibre at neutral horizontal grade.
Twisting recovery by a positive real character leaves a positive Euler-product coefficient and a
boundary mass `1 / ζ(1 + a)` strictly between consecutive divisor orders.  Hence this mass cannot
be the cofinal logarithmic current of a single-valued nonzero meromorphic germ.
-/

open Set Filter Topology Complex
open scoped ArithmeticFunction.Moebius BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coefficient left after twisting exact Möbius recovery by horizontal grade `a`. -/
def twistedMobiusWittCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors,
    (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-a)

/-- Cofinal boundary mass of the grade-`a` twisted recovery law. -/
def twistedMobiusWittBoundaryIndex (a : ℝ) : ℝ :=
  ∑' n : ℕ,
    (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-(1 + a))

/-- Neutral grade restores ordinary Möbius inversion. -/
theorem twistedMobiusWittCoefficient_zero (n : ℕ) :
    twistedMobiusWittCoefficient 0 n = if n = 1 then 1 else 0 := by
  simpa [twistedMobiusWittCoefficient] using sum_divisors_moebius_real n

/-- Every nonzero twisted coefficient is its squarefree Euler product. -/
theorem twistedMobiusWittCoefficient_eq_primeProduct
    (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    twistedMobiusWittCoefficient a n =
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-a)) := by
  have h := RHTower.sum_divisors_moebius_rpow (a / 2) hn
  have hexp : -(2 * (a / 2)) = -a := by ring
  simpa [twistedMobiusWittCoefficient, hexp] using h

/-- Positive grade leaves a strictly positive coefficient on every nonzero divisor fibre. -/
theorem twistedMobiusWittCoefficient_pos
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0) :
    0 < twistedMobiusWittCoefficient a n := by
  rw [twistedMobiusWittCoefficient_eq_primeProduct a hn]
  refine Finset.prod_pos fun p hp => sub_pos.mpr ?_
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpprime.one_lt) (by linarith)

/-- Real zeta is strictly bigger than one, not merely nonnegative, on its Dirichlet ray. -/
theorem one_lt_re_riemannZeta_ofReal (s : ℝ) (hs : 1 < s) :
    (1 : ℝ) < (riemannZeta (s : ℂ)).re := by
  have hsC : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  have hs0 : (s : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (s : ℂ)) :=
    summable_one_div_nat_cpow.mpr hs
  have hz : riemannZeta (s : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (s : ℂ) :=
    zeta_eq_tsum_one_div_nat_cpow hsC
  rw [hz, re_tsum hsum]
  have hnonneg : ∀ n : ℕ, 0 ≤ (1 / (n : ℂ) ^ (s : ℂ)).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Complex.zero_cpow hs0]
    · have hbase : ((n : ℂ)) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) := by
        rw [ofReal_cpow (Nat.cast_nonneg n) s]
        push_cast
        ring
      rw [hbase, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      positivity
  have hsumre : Summable (fun n : ℕ => (1 / (n : ℂ) ^ (s : ℂ)).re) :=
    hsum.mapL Complex.reCLM
  have h12 :
      1 + (1 / ((2 : ℕ) : ℂ) ^ (s : ℂ)).re ≤
        ∑' n : ℕ, (1 / (n : ℂ) ^ (s : ℂ)).re := by
    have hfin := hsumre.sum_le_tsum ({1, 2} : Finset ℕ) (fun n _ => hnonneg n)
    simpa [Complex.one_cpow] using hfin
  have h2pos : 0 < (1 / ((2 : ℕ) : ℂ) ^ (s : ℂ)).re := by
    change 0 < (1 / (2 : ℂ) ^ (s : ℂ)).re
    have hbase : (2 : ℂ) ^ (s : ℂ) = (((2 : ℝ) ^ s : ℝ) : ℂ) := by
      rw [ofReal_cpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) s]
      norm_num
    rw [hbase, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    positivity
  linarith

/-- Dirichlet evaluation identifies boundary index with reciprocal zeta. -/
theorem ofReal_twistedMobiusWittBoundaryIndex_eq_inv_riemannZeta
    {a : ℝ} (ha : 0 < a) :
    ((twistedMobiusWittBoundaryIndex a : ℝ) : ℂ) =
      (riemannZeta (((1 + a : ℝ) : ℂ)))⁻¹ := by
  simpa [twistedMobiusWittBoundaryIndex] using
    (RHTower.ofReal_tsum_moebius_rpow (s := 1 + a) (by linarith))

/-- Positive horizontal grade produces a fractional boundary index. -/
theorem twistedMobiusWittBoundaryIndex_mem_Ioo
    {a : ℝ} (ha : 0 < a) :
    twistedMobiusWittBoundaryIndex a ∈ Set.Ioo (0 : ℝ) 1 := by
  have hs : 1 < 1 + a := by linarith
  have hzgt : (1 : ℝ) < (riemannZeta (((1 + a : ℝ) : ℂ))).re :=
    one_lt_re_riemannZeta_ofReal (1 + a) hs
  have hzim : (riemannZeta (((1 + a : ℝ) : ℂ))).im = 0 :=
    riemannZeta_im_eq_zero_of_one_lt hs
  have hzreal : riemannZeta (((1 + a : ℝ) : ℂ)) =
      (((riemannZeta (((1 + a : ℝ) : ℂ))).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · norm_num at hzim ⊢
      exact hzim
  have hEqC := ofReal_twistedMobiusWittBoundaryIndex_eq_inv_riemannZeta ha
  rw [hzreal, ← Complex.ofReal_inv] at hEqC
  have hEq : twistedMobiusWittBoundaryIndex a =
      (riemannZeta (((1 + a : ℝ) : ℂ))).re⁻¹ :=
    Complex.ofReal_injective hEqC
  rw [hEq]
  constructor
  · exact inv_pos.mpr (lt_trans zero_lt_one hzgt)
  · exact inv_lt_one_of_one_lt₀ hzgt

/-- Meromorphic divisor orders cannot equal the positive-grade completion index. -/
theorem twistedMobiusWittBoundaryIndex_not_integer
    {a : ℝ} (ha : 0 < a) (k : ℤ) :
    twistedMobiusWittBoundaryIndex a ≠ (k : ℝ) := by
  have hfrac := twistedMobiusWittBoundaryIndex_mem_Ioo ha
  intro hk
  rw [hk] at hfrac
  rcases hfrac with ⟨hkpos, hklt⟩
  have hk_cases : k ≤ 0 ∨ 1 ≤ k := by omega
  rcases hk_cases with hk0 | hk1
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    linarith
  · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith

/-- Real points below one approach the cofinal point inside its punctured complex neighbourhood. -/
theorem tendsto_ofReal_nhdsWithin_lt_one_nhdsNE :
    Tendsto (fun r : ℝ => (r : ℂ)) (nhdsWithin 1 (Set.Iio 1)) (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using hr.ne

/-- A nonzero meromorphic germ has integral cofinal completion current. -/
theorem meromorphic_completionCurrent_tendsto_integer
    {W : ℂ → ℂ} (hW : MeromorphicAt W 1)
    (hWne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), W z ≠ 0) :
    ∃ k : ℤ,
      Tendsto (fun z : ℂ => (1 - z) * (-z * logDeriv W z))
        (𝓝[≠] (1 : ℂ)) (𝓝 (k : ℂ)) := by
  have hnotTop : meromorphicOrderAt W 1 ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hW).mpr hWne
  obtain ⟨k, hk⟩ : ∃ k : ℤ, meromorphicOrderAt W 1 = (k : WithTop ℤ) := by
    cases hord : meromorphicOrderAt W 1 with
    | top => exact absurd hord hnotTop
    | coe k => exact ⟨k, rfl⟩
  refine ⟨k, ?_⟩
  have hres := logDeriv_residue_of_meromorphicOrder hW hk
  have hz : Tendsto (fun z : ℂ => z) (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  convert hz.mul hres using 1
  · funext z
    ring_nf
  · ring_nf

/-- Positive twisted recovery cannot be the boundary current of any single-valued nonzero
meromorphic completion germ. -/
theorem no_meromorphic_completion_of_twistedMobiusWittBoundaryIndex
    {a : ℝ} (ha : 0 < a) :
    ¬ ∃ W : ℂ → ℂ,
      MeromorphicAt W 1 ∧
      (∀ᶠ z in 𝓝[≠] (1 : ℂ), W z ≠ 0) ∧
      Tendsto
        (fun r : ℝ =>
          (1 - (r : ℂ)) * (-(r : ℂ) * logDeriv W (r : ℂ)))
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 ((twistedMobiusWittBoundaryIndex a : ℝ) : ℂ)) := by
  rintro ⟨W, hW, hWne, hboundary⟩
  obtain ⟨k, hk⟩ := meromorphic_completionCurrent_tendsto_integer hW hWne
  have hkray := hk.comp tendsto_ofReal_nhdsWithin_lt_one_nhdsNE
  have hEqC : ((twistedMobiusWittBoundaryIndex a : ℝ) : ℂ) = (k : ℂ) :=
    tendsto_nhds_unique hboundary hkray
  have hEqR : twistedMobiusWittBoundaryIndex a = (k : ℝ) := by
    exact_mod_cast hEqC
  exact twistedMobiusWittBoundaryIndex_not_integer ha k hEqR

/-- Closed fractional-index law: zero grade collapses exactly, while every positive grade leaves
strictly positive fibres and a boundary mass excluded from the integer divisor lattice. -/
theorem twistedMobiusWitt_fractional_boundary_index_law :
    (∀ n : ℕ, twistedMobiusWittCoefficient 0 n = if n = 1 then 1 else 0) ∧
    (∀ a : ℝ, 0 < a →
      (∀ n : ℕ, n ≠ 0 → 0 < twistedMobiusWittCoefficient a n) ∧
      twistedMobiusWittBoundaryIndex a ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ k : ℤ, twistedMobiusWittBoundaryIndex a ≠ (k : ℝ)) ∧
      ¬ ∃ W : ℂ → ℂ,
        MeromorphicAt W 1 ∧
        (∀ᶠ z in 𝓝[≠] (1 : ℂ), W z ≠ 0) ∧
        Tendsto
          (fun r : ℝ =>
            (1 - (r : ℂ)) * (-(r : ℂ) * logDeriv W (r : ℂ)))
          (nhdsWithin 1 (Set.Iio 1))
          (𝓝 ((twistedMobiusWittBoundaryIndex a : ℝ) : ℂ))) := by
  refine ⟨twistedMobiusWittCoefficient_zero, ?_⟩
  intro a ha
  exact ⟨fun _ hn => twistedMobiusWittCoefficient_pos ha hn,
    twistedMobiusWittBoundaryIndex_mem_Ioo ha,
    twistedMobiusWittBoundaryIndex_not_integer ha,
    no_meromorphic_completion_of_twistedMobiusWittBoundaryIndex ha⟩

end

end GaloisForLFunctions.HTGeometry
