import GaloisForLFunctions.HTGeometry.ZeroEstimate
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureLiouvilleDense

/-!
# The native orbit gives genericity, not the arithmetic edge bound

The diagonal Kronecker orbit `t ↦ (p^{-it})_p` on the prime torus is the object that supplies the
genericity/upper-bound half of the multi-`q` transcendence estimate.  Its statement mentions only
the primes: it is literally the *same* dense orbit whatever auxiliary is carried along it.

The lower bound lives instead at the fixed arithmetic point `s = 1`, where the relevant quantity is
a prime-log linear form `⟨m, ℓ⟩ = Σ_p m_p log p`.  This file proves the two facts that separate the
faces:

* the edge form of a nonzero exponent vector is nonzero (unique factorization), but
* it is **not bounded below by any positive constant**: nonzero edge forms take arbitrarily small
  values, because the prime-log lattice is dense in the line.

Consequently no quantity extracted from the orbit — which does not see the auxiliary at all — can
lower-bound the edge magnitude.  The only valid lower bound is the *arithmetic* height bound
`H(m)^{-1} ≤ |⟨m, ℓ⟩|`, and along a family with vanishing edge value the heights necessarily blow
up.  That is exactly the orbit/edge orthogonality.

## Main results

* `edgeForm_ne_zero` — a nonzero exponent vector has nonzero edge form;
* `exists_edgeForm_pos_lt` — nonzero edge forms take arbitrarily small values;
* `not_exists_uniform_edge_lower_bound` — no positive constant bounds the edge magnitude below;
* `primeLogHeight_unbounded_of_edgeForm_small` — the height must blow up along such a family;
* `edge_lower_bound_is_arithmetic` — the height bound is the valid lower bound.
-/

noncomputable section

namespace GaloisForLFunctions

namespace DSSOrbitEdge

open scoped BigOperators

/-- The `s = 1` edge form of a friable auxiliary: the prime-log linear form `⟨m, ℓ⟩`. -/
def edgeForm (m : Nat.Primes →₀ ℤ) : ℝ :=
  m.sum fun p z => (z : ℝ) * Real.log ((p : ℕ) : ℝ)

/-- **Unique factorization at the edge.**  A nonzero exponent vector has a nonzero edge form; the
height bound gives the explicit positive lower bound. -/
theorem edgeForm_ne_zero {m : Nat.Primes →₀ ℤ} (hm : m ≠ 0) : edgeForm m ≠ 0 := by
  have hb := logPrime_height_bound m hm
  have hpos : (0 : ℝ) < ((primeLogHeight m : ℕ) : ℝ) := by
    exact_mod_cast primeLogHeight_pos m
  intro h
  rw [edgeForm] at h
  rw [h] at hb
  simp only [abs_zero] at hb
  exact absurd hb (not_le.mpr (by positivity))

/-- **The valid lower bound is arithmetic.**  The reciprocal multiplicative height, not the orbit,
is what bounds the edge form below. -/
theorem edge_lower_bound_is_arithmetic {m : Nat.Primes →₀ ℤ} (hm : m ≠ 0) :
    ((primeLogHeight m : ℕ) : ℝ)⁻¹ ≤ |edgeForm m| :=
  logPrime_height_bound m hm

/-- The two-prime exponent vector realizing an integer pair. -/
def twoPrimeVector (a b : ℤ) : Nat.Primes →₀ ℤ :=
  Finsupp.single ⟨2, Nat.prime_two⟩ a + Finsupp.single ⟨3, Nat.prime_three⟩ b

theorem edgeForm_twoPrimeVector (a b : ℤ) :
    edgeForm (twoPrimeVector a b)
      = (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 := by
  classical
  have hne : (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ ⟨3, Nat.prime_three⟩ := by
    intro h
    exact absurd (congrArg Subtype.val h) (by norm_num)
  rw [edgeForm, twoPrimeVector, Finsupp.sum_add_index']
  · rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> simp
  · intro p
    simp
  · intro p b₁ b₂
    push_cast
    ring

/-- **The edge form is not bounded below.**  Nonzero prime-log edge forms take arbitrarily small
positive values, because the rank-two prime-log lattice is dense in the line. -/
theorem exists_edgeForm_pos_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ m : Nat.Primes →₀ ℤ, m ≠ 0 ∧ 0 < |edgeForm m| ∧ |edgeForm m| < ε := by
  classical
  have hdense := RHTower.dense_range_primeLogValuation (P := Fin 2) ![2, 3]
    (by
      intro p
      fin_cases p
      · exact Nat.prime_two
      · exact Nat.prime_three)
    (by
      intro p q hpq
      fin_cases p <;> fin_cases q <;> simp_all)
    (p₀ := 0) (p₁ := 1) (by decide)
  obtain ⟨y, hy, hyball⟩ :=
    (hdense.exists_mem_open (Metric.isOpen_ball (x := ε / 2) (ε := ε / 4))
      ⟨ε / 2, Metric.mem_ball_self (by linarith)⟩)
  obtain ⟨ν, hν⟩ := hy
  have hdist : |y - ε / 2| < ε / 4 := by
    have := Metric.mem_ball.mp hyball
    rwa [Real.dist_eq] at this
  have hy1 : ε / 4 < y := by
    have := abs_lt.mp hdist
    linarith [this.1]
  have hy2 : y < ε := by
    have := abs_lt.mp hdist
    linarith [this.2]
  refine ⟨twoPrimeVector (ν 0) (ν 1), ?_, ?_, ?_⟩
  · intro hzero
    have : edgeForm (twoPrimeVector (ν 0) (ν 1)) = 0 := by
      rw [hzero, edgeForm]
      simp
    rw [edgeForm_twoPrimeVector] at this
    have hval : (ν 0 : ℝ) * Real.log 2 + (ν 1 : ℝ) * Real.log 3 = y := by
      rw [← hν]
      simp [Fin.sum_univ_two]
    rw [hval] at this
    linarith
  · rw [edgeForm_twoPrimeVector]
    have hval : (ν 0 : ℝ) * Real.log 2 + (ν 1 : ℝ) * Real.log 3 = y := by
      rw [← hν]
      simp [Fin.sum_univ_two]
    rw [hval, abs_of_pos (by linarith)]
    linarith
  · rw [edgeForm_twoPrimeVector]
    have hval : (ν 0 : ℝ) * Real.log 2 + (ν 1 : ℝ) * Real.log 3 = y := by
      rw [← hν]
      simp [Fin.sum_univ_two]
    rw [hval, abs_of_pos (by linarith)]
    exact hy2

/-- **The orbit cannot supply the lower bound.**  There is no positive constant bounding the edge
magnitude of every nonzero auxiliary from below; in particular no quantity extracted from the
Kronecker orbit — whose statement does not mention the auxiliary at all — can do so. -/
theorem not_exists_uniform_edge_lower_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ m : Nat.Primes →₀ ℤ, m ≠ 0 → c ≤ |edgeForm m| := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨m, hm, _, hlt⟩ := exists_edgeForm_pos_lt hc
  exact absurd (hbound m hm) (not_le.mpr hlt)

/-- **The height blows up along a vanishing edge family.**  Any auxiliary whose edge value is below
`ε` has multiplicative height above `1/ε`: the lower bound is genuinely arithmetic. -/
theorem primeLogHeight_unbounded_of_edgeForm_small {m : Nat.Primes →₀ ℤ} (hm : m ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hsmall : |edgeForm m| < ε) :
    ε⁻¹ < ((primeLogHeight m : ℕ) : ℝ) := by
  have hb := logPrime_height_bound m hm
  have hpos : (0 : ℝ) < ((primeLogHeight m : ℕ) : ℝ) := by
    exact_mod_cast primeLogHeight_pos m
  have hchain : ((primeLogHeight m : ℕ) : ℝ)⁻¹ < ε := lt_of_le_of_lt hb hsmall
  have := (inv_lt_comm₀ hpos hε).mp hchain
  exact this

/-- **The edge form is also unbounded above.**  Together with the previous results, the edge value
carries information about the auxiliary that the orbit — identical for all auxiliaries — cannot
see in either direction. -/
theorem exists_edgeForm_gt (R : ℝ) :
    ∃ m : Nat.Primes →₀ ℤ, R < |edgeForm m| := by
  classical
  obtain ⟨k, hk⟩ := exists_nat_gt (R / Real.log 2)
  refine ⟨twoPrimeVector (k : ℤ) 0, ?_⟩
  rw [edgeForm_twoPrimeVector]
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hval : ((k : ℤ) : ℝ) * Real.log 2 + ((0 : ℤ) : ℝ) * Real.log 3
      = (k : ℝ) * Real.log 2 := by
    push_cast
    ring
  rw [hval, abs_of_nonneg (by positivity)]
  calc R = (R / Real.log 2) * Real.log 2 := by field_simp
    _ < (k : ℝ) * Real.log 2 := by
        exact mul_lt_mul_of_pos_right hk hlog

end DSSOrbitEdge

end GaloisForLFunctions
