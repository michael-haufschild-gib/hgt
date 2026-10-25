import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH

/-!
# Künneth positivity is point-count positivity

For a curve datum over `𝔽_q` with point counts `N_n`, the external product of Adams twists
`ψ^{m_1} C × ⋯ × ψ^{m_k} C` has ghost sequence `n ↦ Π_i N_{m_i n}` (`kunnethCount`), and its zeta
series is the λ-ring exponential `σ(g) = exp(Σ_{j ≥ 1} g(j) X^j / j)` (`sigmaSeries`), whose
coefficients count effective zero-cycles of the symmetric powers.

* **Newton–Witt positivity** (`exists_sigmaCoeff_eq_ofReal_nonneg`). If `g(j) ≥ 0` for `j ≥ 1`,
  every coefficient of `σ(g)` is a nonnegative real: `(n+1)σ_{n+1} = Σ_{j ≤ n} σ_j g(n+1−j)`
  involves only indices `n + 1 − j ≥ 1`.
* **Collapse** (`kunneth_positivity_tfae`). The following are equivalent: all point counts
  `N_n ≥ 0`; all Künneth–Adams counts are nonnegative; every coefficient of every Künneth–Adams
  zeta series is a nonnegative real. The first coefficient of `σ` is `g(1)`, and the one-factor
  product `ψ^n C` has `g(1) = N_n`.
* **The golden datum** (`goldenDatum_kunneth_positive_not_pure`). The fake curve `1 − 5X + 5X²` over
  `𝔽₅` satisfies every Künneth positivity, is not pure, and fails the Hodge index on its Frobenius
  span.

So positivity of products of the spectrum, of Adams twists and of symmetric powers is a single
condition, `N_n ≥ 0`, strictly weaker than purity. The positivity in Weil's proof is a positivity of
correspondences on `C × C`: the Hodge index (`CurveDatum.hodgeIndexOnSpan_iff_unitary`).
-/

open PowerSeries

namespace GaloisForLFunctions.ArithmeticKunnethTheory

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι]

/-- The ghost sequence `n ↦ Π_i N_{m_i n}` of the external product of the Adams twists
`ψ^{m_i} C`. -/
noncomputable def kunnethCount (D : CurveDatum ι) {k : ℕ} (m : Fin k → ℕ) (n : ℕ) : ℝ :=
  ∏ i, D.pointCount (m i * n)

/-- **Newton–Witt positivity.** A ghost sequence that is nonnegative in positive degrees has a
λ-ring exponential with nonnegative real coefficients. -/
theorem exists_sigmaCoeff_eq_ofReal_nonneg {g : ℕ → ℝ} (hg : ∀ j, 1 ≤ j → 0 ≤ g j) (n : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ sigmaCoeff (fun j => (g j : ℂ)) n = c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · exact ⟨1, zero_le_one, by rw [sigmaCoeff_zero, Complex.ofReal_one]⟩
    · choose! c hc0 hc using ih
      refine ⟨((m : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (m + 1), c j * g (m + 1 - j), ?_, ?_⟩
      · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j hj => ?_)
        have hj' : j < m + 1 := Finset.mem_range.mp hj
        exact mul_nonneg (hc0 j hj') (hg _ (by omega))
      · rw [sigmaCoeff_succ, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_add,
          Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_sum]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hc j (Finset.mem_range.mp hj), Complex.ofReal_mul]

/-- The first coefficient of the λ-ring exponential is the first ghost component. -/
theorem sigmaCoeff_one (g : ℕ → ℂ) : sigmaCoeff g 1 = g 1 := by
  rw [sigmaCoeff_succ]
  simp [sigmaCoeff_zero]

/-- **Künneth positivity collapses to point-count positivity.** For a curve datum, nonnegative
point counts, nonnegative Künneth–Adams counts, and nonnegative real coefficients of every
Künneth–Adams zeta series are equivalent. -/
theorem kunneth_positivity_tfae (D : CurveDatum ι) :
    List.TFAE
      [∀ n, 1 ≤ n → 0 ≤ D.pointCount n,
       ∀ (k : ℕ) (m : Fin k → ℕ), (∀ i, 1 ≤ m i) → ∀ n, 1 ≤ n → 0 ≤ kunnethCount D m n,
       ∀ (k : ℕ) (m : Fin k → ℕ), (∀ i, 1 ≤ m i) → ∀ n, ∃ c : ℝ, 0 ≤ c ∧
         coeff n (sigmaSeries fun j => (kunnethCount D m j : ℂ)) = c] := by
  tfae_have 1 → 2 := fun h k m hm n hn =>
    Finset.prod_nonneg fun i _ => h _ (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp (hm i)) (Nat.one_le_iff_ne_zero.mp hn)))
  tfae_have 2 → 3 := fun h k m hm n => by
    rw [coeff_sigmaSeries]
    exact exists_sigmaCoeff_eq_ofReal_nonneg (h k m hm) n
  tfae_have 3 → 1 := fun h n hn => by
    obtain ⟨c, hc0, hc⟩ := h 1 ![n] (fun i => by fin_cases i; exact hn) 1
    rw [coeff_sigmaSeries, sigmaCoeff_one] at hc
    have hcount : kunnethCount D ![n] 1 = D.pointCount n := by simp [kunnethCount]
    rw [hcount] at hc
    exact (Complex.ofReal_injective hc) ▸ hc0
  tfae_finish

/-- **The golden datum is Künneth-positive and impure.** Every Künneth–Adams zeta series of the fake
curve `1 − 5X + 5X²` over `𝔽₅` has nonnegative real coefficients, yet the datum is not pure and
the Hodge index fails on its Frobenius span. -/
theorem goldenDatum_kunneth_positive_not_pure :
    (∀ (k : ℕ) (m : Fin k → ℕ), (∀ i, 1 ≤ m i) → ∀ n, ∃ c : ℝ, 0 ≤ c ∧
        coeff n (sigmaSeries fun j => (kunnethCount goldenDatum m j : ℂ)) = c) ∧
      ¬ (∀ i, ‖goldenDatum.β i‖ = 1) ∧
      ¬ (∀ (S : Finset ℕ) (d : ℕ → ℝ), 0 ≤ goldenDatum.spanDefect S d) := by
  have h1 : ∀ n, 1 ≤ n → 0 ≤ goldenDatum.pointCount n := fun n _ =>
    goldenDatum_pointCount_nonneg n
  refine ⟨((kunneth_positivity_tfae goldenDatum).out 0 2).mp h1, goldenDatum_not_unitary, ?_⟩
  rw [CurveDatum.hodgeIndexOnSpan_iff_unitary]
  exact goldenDatum_not_unitary

end GaloisForLFunctions.ArithmeticKunnethTheory
