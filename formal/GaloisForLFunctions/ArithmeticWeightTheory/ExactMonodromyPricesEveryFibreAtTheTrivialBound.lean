import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant

/-!
# Exact monodromy prices every fibre at the trivial bound

Deligne bounds the Frobenius of one closed point by the whole `L(F^{⊗2k})`: positivity of the
Euler factors transfers a global bound to one fibre, and the global bound comes from `H²_c`,
computed geometrically. A family of twists of `Spec ℤ` can compute its coinvariants only by
orthogonality of a measure. This file shows that this route returns exactly the trivial bound at
every fibre, for every family and every tensor power.

**Uncertainty** (`measureReal_singleton_mul_card_le`). Let `ν` be any probability measure on the
gauge torus whose twists are orthonormal on a finite set `s` of positive integers. Then every
point has mass `ν{x₀} ≤ 1/#s`: a family that computes its coinvariants exactly up to length `L`
gives each fibre mass at most `1/L`.

**Pricing** (`measureReal_singleton_mul_pow_le`). Let `S_x = Σ_{n∈s} a_n χ_x(n)` with `a ≥ 0`, and
suppose `ν` is orthonormal on the products of `k` elements of `s` (exact coinvariants of the
`2k`-th tensor power). Then for every fibre `x₀`

  `ν{x₀} · (Σ_n a_n)^{2k} ≤ ∫ |S|^{2k} dν`,

so the positivity transfer `|S_{x₀}|^{2k} ≤ ∫ |S|^{2k} dν / ν{x₀}` never certifies anything below
the trivial bound `(Σ a_n)^{2k}`, which is the value at the trivial fibre. The Haar family has
`ν{x₀} = 0`; a Dirichlet family mod `q` is exact on the `k`-fold products only for
`q > max product`, which makes the principal fibre's mass `1/φ(q)` too small by exactly the
Cauchy–Schwarz factor. Over `𝔽_q` the multiplicative group is finite, so a finite family is exact
at every tensor power; over `ℤ` exactness at power `k` costs volume `≥ (length)^k`.
-/

open MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry ArithmeticKunnethTheory

/-- Orthonormality of the twists on `s` under a measure `ν`. -/
def TwistOrthonormalOn (ν : Measure GaugeTorus) (s : Finset ℕ) : Prop :=
  ∀ m ∈ s, ∀ n ∈ s, ∫ x, twist x m * conj (twist x n) ∂ν = if m = n then 1 else 0

/-- Parseval for twisted polynomials under an orthonormal family. -/
theorem integral_normSq_twistSum_of_orthonormal {ν : Measure GaugeTorus} [IsProbabilityMeasure ν]
    {s : Finset ℕ} (horth : TwistOrthonormalOn ν s) (c : ℕ → ℂ) :
    ∫ x, ‖twistSum s c x‖ ^ 2 ∂ν = ∑ n ∈ s, ‖c n‖ ^ 2 := by
  classical
  have hint : ∀ m n : ℕ, Integrable (fun x => twist x m * conj (twist x n)) ν := fun m n =>
    ((continuous_twist m).mul (Complex.continuous_conj.comp (continuous_twist n))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC : ∫ x, twistSum s c x * conj (twistSum s c x) ∂ν = ∑ n ∈ s, c n * conj (c n) := by
    simp_rw [twistSum_mul_conj]
    rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => (hint m n).const_mul _]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [integral_finsetSum _ fun n _ => (hint m n).const_mul _]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single m]
    · rw [horth m hm m hm, if_pos rfl, mul_one]
    · intro n hn hnm
      rw [horth m hm n hn, if_neg (Ne.symm hnm), mul_zero]
    · exact fun h => absurd hm h
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hC
  rw [integral_complex_ofReal] at hC
  exact_mod_cast hC

/-- **Uncertainty.** Exact coinvariants on `s` give every fibre mass at most `1/#s`. -/
theorem measureReal_singleton_mul_card_le {ν : Measure GaugeTorus} [IsProbabilityMeasure ν]
    {s : Finset ℕ} (horth : TwistOrthonormalOn ν s) (x₀ : GaugeTorus) :
    ν.real {x₀} * s.card ≤ 1 := by
  set c : ℕ → ℂ := fun n => conj (twist x₀ n)
  have hpar := integral_normSq_twistSum_of_orthonormal horth c
  have hc1 : ∀ n, ‖c n‖ ^ 2 = 1 := fun n => by simp [c, norm_twist]
  simp only [hc1, Finset.sum_const, nsmul_eq_mul, mul_one] at hpar
  have hval : twistSum s c x₀ = s.card := by
    simp only [twistSum, c]
    rw [Finset.sum_congr rfl fun n _ => by rw [mul_comm, twist_mul_conj_self]]
    simp
  have hint : Integrable (fun x => ‖twistSum s c x‖ ^ 2) ν :=
    ((continuous_twistSum s c).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hset := setIntegral_le_integral (s := {x₀}) hint
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖twistSum s c x‖)
  rw [integral_singleton, hpar, hval, smul_eq_mul, Complex.norm_natCast] at hset
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [h0]; simp
  · have hcard : (0 : ℝ) < s.card := by exact_mod_cast hpos
    nlinarith

/-- **Pricing.** With exact coinvariants of the `2k`-th tensor power, the positivity transfer from
the family to any fibre is never below the trivial bound `(Σ a_n)^{2k}`. -/
theorem measureReal_singleton_mul_pow_le {ν : Measure GaugeTorus} [IsProbabilityMeasure ν]
    {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {k : ℕ}
    (horth : TwistOrthonormalOn ν (powSupport s k)) (x₀ : GaugeTorus) :
    ν.real {x₀} * (∑ n ∈ s, a n) ^ (2 * k) ≤
      ∫ x, ‖twistSum s (fun n => (a n : ℂ)) x‖ ^ (2 * k) ∂ν := by
  set P := powSupport s k
  set b : ℕ → ℝ := powCoeffReal s a k
  have hb0 : ∀ N, 0 ≤ b N := powCoeffReal_nonneg ha k
  -- the moment is the coinvariant sum
  have hpow : ∀ x, ‖twistSum s (fun n => (a n : ℂ)) x‖ ^ (2 * k) =
      ‖twistSum P (fun N => (b N : ℂ)) x‖ ^ 2 := by
    intro x
    have hcoef : powCoeff s (fun n => (a n : ℂ)) k = fun N => ((powCoeffReal s a k N : ℝ) : ℂ) :=
      funext fun N => powCoeff_ofReal s a k N
    rw [mul_comm, pow_mul, ← norm_pow, twistSum_pow hs, hcoef]
  have hmom : ∫ x, ‖twistSum s (fun n => (a n : ℂ)) x‖ ^ (2 * k) ∂ν = ∑ N ∈ P, b N ^ 2 := by
    simp_rw [hpow]
    rw [integral_normSq_twistSum_of_orthonormal horth]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the coinvariants sum to the trivial value
  have hsum : (∑ n ∈ s, a n) ^ k = ∑ N ∈ P, b N := by
    have h := twistSum_pow hs (fun n => (a n : ℂ)) k 0
    have h0 : ∀ n, twist (0 : GaugeTorus) n = 1 := fun n => by
      have h1 := twist_add (0 : GaugeTorus) 0 n
      rw [add_zero] at h1
      have hne : twist (0 : GaugeTorus) n ≠ 0 := fun hz => by
        have := norm_twist (0 : GaugeTorus) n
        rw [hz, norm_zero] at this
        exact zero_ne_one this
      exact mul_left_cancel₀ hne (h1.symm.trans (mul_one _).symm)
    simp only [twistSum, h0, mul_one] at h
    simp only [powCoeff_ofReal] at h
    exact_mod_cast h
  have hunc := measureReal_singleton_mul_card_le horth x₀
  have hcs : (∑ N ∈ P, b N) ^ 2 ≤ P.card * ∑ N ∈ P, b N ^ 2 := sq_sum_le_card_mul_sum_sq
  have hν0 : 0 ≤ ν.real {x₀} := measureReal_nonneg
  have hS0 : 0 ≤ ∑ N ∈ P, b N ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hmom, pow_mul', hsum]
  calc ν.real {x₀} * (∑ N ∈ P, b N) ^ 2 ≤ ν.real {x₀} * (P.card * ∑ N ∈ P, b N ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hν0
    _ = (ν.real {x₀} * P.card) * ∑ N ∈ P, b N ^ 2 := by ring
    _ ≤ 1 * ∑ N ∈ P, b N ^ 2 := mul_le_mul_of_nonneg_right hunc hS0
    _ = ∑ N ∈ P, b N ^ 2 := one_mul _

end GaloisForLFunctions.ArithmeticWeightTheory
