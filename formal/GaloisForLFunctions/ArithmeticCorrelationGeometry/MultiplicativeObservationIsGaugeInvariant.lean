import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.ArithmeticKunnethTheory.ProductMomentsAreDiagonalBelowTheThreshold

/-!
# Multiplicative observation is gauge invariant

**The gauge group.** A point `x` of the torus `G = (ℝ/ℤ)^ℕ` twists an arithmetic source by the
unimodular completely multiplicative function `χ_x(n) = ∏_p e(x_p v_p(n))` (`twist`); only the
prime coordinates are read. Every unimodular completely multiplicative function is a twist
(`exists_twist_eq`): Dirichlet characters with their values at the conductor reset to one, the
Liouville sign, and the vertical shifts `n^{it}`, which form the archimedean line
(`twist_clockPhasePoint`).

**Orthogonality** (`integral_twist_mul_conj`). Against Haar measure, `∫ χ_x(m) χ̄_x(n) dx = [m = n]`
for positive integers. Unique factorization says that distinct positive integers have distinct
exponent vectors, and the characters of a compact torus are orthonormal.

**Gauge moments carry only unique factorization.** For a source `a` on positive integers the gauge
mean square of `Σ a_n χ_x(n)` is `Σ |a_n|²` (`integral_twistSum_mul_conj`), and the gauge `2k`-th
moment is the multiplicative diagonal `Σ_N |a^{*k}(N)|²` for every `k` and every length
(`integral_normSq_twistSum_pow`). The archimedean line reproduces this diagonal only below the
square-root threshold (`ArithmeticKunnethTheory.integral_pairTransform_mul_normSq_pow_eq_diag`).

**Gauge projection** (`integral_monomial_twist`, `monomial_twist_eq_iff`). A correlation monomial
`a(m₁)⋯a(m_k) ā(n₁)⋯ā(n_l)` of the twisted source has gauge mean equal to its untwisted value when
`m₁⋯m_k = n₁⋯n_l`, and zero otherwise; it is gauge invariant exactly in the first case. Every
correlation built from coincidences of products is constant on gauge orbits, and every other
correlation has gauge mean zero.
-/

open MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry ArithmeticKunnethTheory

/-! ### The gauge torus and its twists -/

/-- The gauge torus: one phase for each index; twists read the prime coordinates. -/
abbrev GaugeTorus := UnitAddTorus ℕ

/-- Haar probability measure on the gauge torus. -/
abbrev gaugeHaar : Measure GaugeTorus := torusHaar ℕ

/-- The exponent vector of `n`: its factorization read in `ℤ`. -/
def expVec (n : ℕ) : ℕ →₀ ℤ := Finsupp.mapRange (fun k : ℕ => (k : ℤ)) Nat.cast_zero n.factorization

theorem expVec_apply (n p : ℕ) : expVec n p = (n.factorization p : ℤ) := rfl

theorem expVec_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : expVec (m * n) = expVec m + expVec n := by
  rw [expVec, Nat.factorization_mul hm hn, Finsupp.mapRange_add (fun _ _ => Nat.cast_add _ _)]
  rfl

@[simp] theorem expVec_one : expVec 1 = 0 := by
  ext p
  simp [expVec_apply]

theorem expVec_inj {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : expVec m = expVec n ↔ m = n := by
  refine ⟨fun h => Nat.factorization_inj hm hn ?_, fun h => h ▸ rfl⟩
  ext p
  have := congrArg (fun v : ℕ →₀ ℤ => v p) h
  simpa [expVec_apply] using this

theorem support_expVec (n : ℕ) : (expVec n).support = n.factorization.support :=
  Finsupp.support_mapRange_of_injective _ _ Nat.cast_injective

/-- The gauge twist `χ_x(n) = ∏_p e(x_p v_p(n))`. -/
def twist (x : GaugeTorus) (n : ℕ) : ℂ := torusCharacter (expVec n) x

theorem continuous_twist (n : ℕ) : Continuous fun x : GaugeTorus => twist x n :=
  (torusCharacter (expVec n)).continuous

@[simp] theorem twist_one (x : GaugeTorus) : twist x 1 = 1 := by
  rw [twist, expVec_one, torusCharacter_zero]

/-- Twists are completely multiplicative on the positive integers. -/
theorem twist_mul (x : GaugeTorus) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    twist x (m * n) = twist x m * twist x n := by
  rw [twist, expVec_mul hm hn, torusCharacter_add_index]
  rfl

/-- Twists act on the torus by characters: `χ_{x+y} = χ_x χ_y`. -/
theorem twist_add (x y : GaugeTorus) (n : ℕ) : twist (x + y) n = twist x n * twist y n :=
  torusCharacter_add _ x y

theorem conj_twist (x : GaugeTorus) (n : ℕ) :
    conj (twist x n) = torusCharacter (-expVec n) x :=
  (torusCharacter_neg_index _ x).symm

theorem twist_mul_conj_twist (x : GaugeTorus) (m n : ℕ) :
    twist x m * conj (twist x n) = torusCharacter (expVec m - expVec n) x := by
  rw [conj_twist, twist, ← torusCharacter_add_index, sub_eq_add_neg]

/-- Twists are unimodular. -/
theorem twist_mul_conj_self (x : GaugeTorus) (n : ℕ) : twist x n * conj (twist x n) = 1 := by
  rw [twist_mul_conj_twist, sub_self, torusCharacter_zero]

theorem norm_twist (x : GaugeTorus) (n : ℕ) : ‖twist x n‖ = 1 := by
  have h := twist_mul_conj_self x n
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h' : ‖twist x n‖ ^ 2 = 1 := by exact_mod_cast h
  nlinarith [norm_nonneg (twist x n), sq_nonneg (‖twist x n‖ - 1)]

/-- Twists are multiplicative over finite products of positive integers. -/
theorem twist_prod {ι : Type*} (x : GaugeTorus) (s : Finset ι) (t : ι → ℕ)
    (ht : ∀ i ∈ s, t i ≠ 0) : twist x (∏ i ∈ s, t i) = ∏ i ∈ s, twist x (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj,
      twist_mul x (ht j (Finset.mem_insert_self j s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => ht i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => ht i (Finset.mem_insert_of_mem hi)]

/-- **The archimedean line.** Along the phase flow with frequencies `log p`, the twist is the
vertical shift `n^{it}`. -/
theorem twist_clockPhasePoint (t : ℝ) (n : ℕ) :
    twist (clockPhasePoint (fun p => Real.log p) t) n =
      Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  rw [twist, torusCharacter_clockPhasePoint]
  congr 4
  rw [characterDetuning, support_expVec, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  rfl

/-- **Every unimodular completely multiplicative function is a twist.** -/
theorem exists_twist_eq (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hfmul : ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n)
    (hfp : ∀ p, p.Prime → ‖f p‖ = 1) :
    ∃ x : GaugeTorus, ∀ n, n ≠ 0 → twist x n = f n := by
  classical
  refine ⟨fun p => ((Complex.arg (f p) / (2 * Real.pi) : ℝ) : UnitAddCircle), fun n hn => ?_⟩
  have hprime : ∀ p, p.Prime → ∀ k : ℕ,
      fourier (k : ℤ) (((Complex.arg (f p) / (2 * Real.pi) : ℝ) : UnitAddCircle)) = f p ^ k := by
    intro p hp k
    rw [fourier_coe_apply]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hexp : f p = Complex.exp ((Complex.arg (f p) : ℂ) * Complex.I) := by
      have h := Complex.norm_mul_exp_arg_mul_I (f p)
      rw [hfp p hp, Complex.ofReal_one, one_mul] at h
      exact h.symm
    conv_rhs => rw [hexp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  -- the twist is the product of prime factors
  have hpow : ∀ p k : ℕ, p ≠ 0 → f (p ^ k) = f p ^ k := by
    intro p k hp
    induction k with
    | zero => simpa using hf1
    | succ k ih => rw [pow_succ, hfmul _ _ (pow_ne_zero _ hp) hp, ih, pow_succ]
  have hcop : ∀ x y : ℕ, x.Coprime y → f (x * y) = f x * f y := by
    intro x y hxy
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [Nat.coprime_zero_left] at hxy
      rw [hxy, mul_one, hf1, mul_one]
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · rw [Nat.coprime_zero_right] at hxy
      rw [hxy, one_mul, hf1, one_mul]
    exact hfmul x y hx.ne' hy.ne'
  have hfn : f n = n.factorization.prod fun p k => f p ^ k := by
    rw [Nat.multiplicative_factorization f hcop hf1 hn]
    refine Finset.prod_congr rfl fun p hp => hpow p _ ?_
    exact (Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)).ne_zero
  rw [hfn, twist, torusCharacter_apply, support_expVec, Finsupp.prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [expVec_apply]
  exact hprime p (Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)) _

/-! ### Orthogonality and gauge moments -/

theorem integrable_twist_mul_conj (m n : ℕ) :
    Integrable (fun x : GaugeTorus => twist x m * conj (twist x n)) gaugeHaar :=
  ((continuous_twist m).mul (Complex.continuous_conj.comp (continuous_twist n))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Gauge orthogonality.** Distinct positive integers have orthogonal twists. -/
theorem integral_twist_mul_conj {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x, twist x m * conj (twist x n) ∂gaugeHaar = if m = n then 1 else 0 := by
  classical
  simp_rw [twist_mul_conj_twist]
  rw [integral_torusCharacter]
  congr 1
  exact propext (sub_eq_zero.trans (expVec_inj hm hn))

/-- The twisted Dirichlet polynomial `Σ_{n ∈ s} a_n χ_x(n)`. -/
def twistSum (s : Finset ℕ) (a : ℕ → ℂ) (x : GaugeTorus) : ℂ := ∑ n ∈ s, a n * twist x n

theorem continuous_twistSum (s : Finset ℕ) (a : ℕ → ℂ) : Continuous (twistSum s a) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_twist n)

theorem twistSum_mul_conj (s t : Finset ℕ) (a b : ℕ → ℂ) (x : GaugeTorus) :
    twistSum s a x * conj (twistSum t b x) =
      ∑ m ∈ s, ∑ n ∈ t, a m * conj (b n) * (twist x m * conj (twist x n)) := by
  rw [twistSum, twistSum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul]
  ring

/-- **Gauge Parseval.** For sources on positive integers the gauge inner product of twisted
Dirichlet polynomials is the coefficient inner product. -/
theorem integral_twistSum_mul_conj {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (a b : ℕ → ℂ) :
    ∫ x, twistSum s a x * conj (twistSum s b x) ∂gaugeHaar = ∑ n ∈ s, a n * conj (b n) := by
  classical
  simp_rw [twistSum_mul_conj]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_twist_mul_conj m n).const_mul _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun n _ => (integrable_twist_mul_conj m n).const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single m]
  · rw [integral_twist_mul_conj (hs m hm) (hs m hm), if_pos rfl, mul_one]
  · intro n hn hnm
    rw [integral_twist_mul_conj (hs m hm) (hs n hn), if_neg (Ne.symm hnm), mul_zero]
  · exact fun h => absurd hm h

/-- **The gauge mean square is the coefficient energy.** -/
theorem integral_normSq_twistSum {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (a : ℕ → ℂ) :
    ∫ x, ‖twistSum s a x‖ ^ 2 ∂gaugeHaar = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have h := integral_twistSum_mul_conj hs a a
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The `k`-th power of a twisted polynomial is the twisted polynomial of `a^{*k}` on the products. -/
theorem twistSum_pow {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (a : ℕ → ℂ) (k : ℕ) (x : GaugeTorus) :
    twistSum s a x ^ k = twistSum (powSupport s k) (powCoeff s a k) x := by
  classical
  have hprod : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => s),
      ∏ i, (a (t i) * twist x (t i)) = (∏ i, a (t i)) * twist x (∏ i, t i) := by
    intro t ht
    rw [Fintype.mem_piFinset] at ht
    rw [Finset.prod_mul_distrib, twist_prod x _ t fun i _ => hs _ (ht i)]
  rw [twistSum, ← Fin.prod_const, Finset.prod_univ_sum, Finset.sum_congr rfl hprod, twistSum]
  rw [← Finset.sum_fiberwise_of_maps_to (t := powSupport s k) (g := fun t => ∏ i, t i)
    (fun t ht => Finset.mem_image.mpr ⟨t, ht, rfl⟩)]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [powCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_filter.mp ht).2]

theorem ne_zero_of_mem_powSupport {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {k N : ℕ}
    (hN : N ∈ powSupport s k) : N ≠ 0 := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hN
  rw [Fintype.mem_piFinset] at ht
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hs _ (ht i)

/-- **Gauge moments of every order are multiplicative diagonals.** For every product order `k` and
every length, the gauge `2k`-th moment of `Σ a_n χ_x(n)` is `Σ_N |a^{*k}(N)|²`. -/
theorem integral_normSq_twistSum_pow {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (a : ℕ → ℂ) (k : ℕ) :
    ∫ x, ‖twistSum s a x‖ ^ (2 * k) ∂gaugeHaar =
      ∑ N ∈ powSupport s k, ‖powCoeff s a k N‖ ^ 2 := by
  have h : ∀ x, ‖twistSum s a x‖ ^ (2 * k) = ‖twistSum (powSupport s k) (powCoeff s a k) x‖ ^ 2 := by
    intro x
    rw [← twistSum_pow hs, norm_pow, ← pow_mul, mul_comm]
  simp_rw [h]
  exact integral_normSq_twistSum (fun N hN => ne_zero_of_mem_powSupport hs hN) _

/-! ### Gauge projection of correlation monomials -/

/-- The correlation monomial `a(m₁)⋯a(m_k) ā(n₁)⋯ā(n_l)`. -/
def monomial {k l : ℕ} (m : Fin k → ℕ) (n : Fin l → ℕ) (a : ℕ → ℂ) : ℂ :=
  (∏ i, a (m i)) * ∏ j, conj (a (n j))

/-- The twisted source `χ_x a`. -/
def twisted (x : GaugeTorus) (a : ℕ → ℂ) : ℕ → ℂ := fun n => twist x n * a n

/-- A monomial of the twisted source is the untwisted monomial times one character. -/
theorem monomial_twisted {k l : ℕ} {m : Fin k → ℕ} {n : Fin l → ℕ} (hm : ∀ i, m i ≠ 0)
    (hn : ∀ j, n j ≠ 0) (a : ℕ → ℂ) (x : GaugeTorus) :
    monomial m n (twisted x a) =
      twist x (∏ i, m i) * conj (twist x (∏ j, n j)) * monomial m n a := by
  simp only [monomial, twisted, map_mul, Finset.prod_mul_distrib]
  rw [← twist_prod x _ m fun i _ => hm i,
    show ∏ j, conj (twist x (n j)) = conj (twist x (∏ j, n j)) by
      rw [twist_prod x _ n fun j _ => hn j, map_prod]]
  ring

/-- **Gauge projection.** The gauge mean of a twisted monomial is the monomial when the products
coincide and zero otherwise. -/
theorem integral_monomial_twist {k l : ℕ} {m : Fin k → ℕ} {n : Fin l → ℕ} (hm : ∀ i, m i ≠ 0)
    (hn : ∀ j, n j ≠ 0) (a : ℕ → ℂ) :
    ∫ x, monomial m n (twisted x a) ∂gaugeHaar =
      if ∏ i, m i = ∏ j, n j then monomial m n a else 0 := by
  have hM : ∏ i, m i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hm i
  have hN : ∏ j, n j ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hn j
  simp_rw [monomial_twisted hm hn a]
  rw [integral_mul_const, integral_twist_mul_conj hM hN]
  split_ifs <;> simp

/-- **Gauge invariance is multiplicative coincidence.** A monomial whose untwisted value is
nonzero is unchanged by every twist iff its two products coincide. -/
theorem monomial_twist_eq_iff {k l : ℕ} {m : Fin k → ℕ} {n : Fin l → ℕ} (hm : ∀ i, m i ≠ 0)
    (hn : ∀ j, n j ≠ 0) {a : ℕ → ℂ} (ha : monomial m n a ≠ 0) :
    (∀ x, monomial m n (twisted x a) = monomial m n a) ↔ ∏ i, m i = ∏ j, n j := by
  constructor
  · intro h
    by_contra hne
    have hint := integral_monomial_twist hm hn a
    rw [if_neg hne] at hint
    simp_rw [h] at hint
    rw [integral_const, probReal_univ, one_smul] at hint
    exact ha hint
  · intro h x
    rw [monomial_twisted hm hn, h, twist_mul_conj_self, one_mul]

end GaloisForLFunctions.ArithmeticCorrelationGeometry
