import GaloisForLFunctions.HTGeometry.ZeroEstimate
import GaloisForLFunctions.RHTower.ZeroEstimateOrder
import GaloisForLFunctions.PNTPlus.Consequences
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.BoundedWeightMultiplicity
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Uniformity of the diagonal multi-`q` zero estimate

The diagonal pullback of a Bohr polynomial is a friable Dirichlet polynomial
`F(s) = Σ λ_m n_m^{-s}` with `n_m = ∏ p^{m_p}`.  Unique factorization makes the moduli — hence the
frequencies `-log n_m` — pairwise distinct, so the Vandermonde order bound applies with constant one
and no Diophantine input: `F` vanishes to order at most `K - 1`, where `K` is the number of exponent
vectors.

The Vandermonde determinant controlling that system is `∏_{i<j} ⟨m_i - m_j, ℓ⟩`, and each factor is
bounded below by the reciprocal multiplicative height of the difference — a bound whose constant is
`1` and which mentions neither the prime set nor Baker's theorem.

Finally the only remaining `S`-dependence is through the largest prime `P_S`: every height of a
degree-`≤ D` exponent vector supported in `S` is at most `P_S^D`, so every form is at least
`P_S^{-D}`.  Along the canonical exhaustion `S_N = {first N primes}` the prime number theorem makes
`P_S` polynomially bounded in `N = |S|`, which is exactly the uniformity the lower-bound race needs.

## Main results

* `diagonalDirichlet_has_nonzero_iteratedDeriv_lt_card` — (a) the order bound, constant one;
* `prod_inv_primeLogHeight_le_abs_det_vandermonde` — (b) the `S`-free determinant size bound;
* `primeLogHeight_le_pow`, `inv_pow_le_abs_primeLogForm` — (c) the `P_S`-polynomial height and form
  bounds at fixed degree;
* `card_boundedDegreeMonomials_eq`, `card_boundedDegreeMonomials_le` — (c) the exact monomial
  count `C(|S|+d, d)`;
* `eventually_nth_prime_le_two_mul`, `eventually_nth_prime_le_sq` — the PNT link making `P_S`
  polynomial in `|S|` along the canonical exhaustion.
-/

noncomputable section

namespace GaloisForLFunctions

namespace ZeroEstimateUniformity

open Filter Topology

/-! ### (a) The diagonal pullback and the uniform order bound -/

/-- The diagonal frequency attached to a Bohr monomial: `μ_m = -log ∏ p^{m_p}`. -/
def diagonalFrequency (m : Nat.Primes →₀ ℕ) : ℂ :=
  -((Real.log ((primeProduct m : ℕ) : ℝ) : ℝ) : ℂ)

/-- **Unique factorization separates the diagonal frequencies.** -/
theorem injective_diagonalFrequency : Function.Injective diagonalFrequency := by
  intro a b hab
  have hlog : Real.log ((primeProduct a : ℕ) : ℝ) = Real.log ((primeProduct b : ℕ) : ℝ) := by
    have := congrArg Neg.neg hab
    simp only [diagonalFrequency, neg_neg] at this
    exact_mod_cast this
  have ha : (0 : ℝ) < ((primeProduct a : ℕ) : ℝ) := by
    exact_mod_cast primeProduct_pos a
  have hb : (0 : ℝ) < ((primeProduct b : ℕ) : ℝ) := by
    exact_mod_cast primeProduct_pos b
  have : ((primeProduct a : ℕ) : ℝ) = ((primeProduct b : ℕ) : ℝ) := by
    have h1 : Real.exp (Real.log ((primeProduct a : ℕ) : ℝ)) = ((primeProduct a : ℕ) : ℝ) :=
      Real.exp_log ha
    have h2 : Real.exp (Real.log ((primeProduct b : ℕ) : ℝ)) = ((primeProduct b : ℕ) : ℝ) :=
      Real.exp_log hb
    rw [← h1, ← h2, hlog]
  exact primeProduct_injective (by exact_mod_cast this)

/-- The Dirichlet monomial of a Bohr exponent vector is the exponential of its diagonal
frequency. -/
theorem cpow_neg_eq_exp_mul_diagonalFrequency (m : Nat.Primes →₀ ℕ) (s : ℂ) :
    (((primeProduct m : ℕ) : ℂ)) ^ (-s) = Complex.exp (s * diagonalFrequency m) := by
  have hpos : (0 : ℝ) < ((primeProduct m : ℕ) : ℝ) := by
    exact_mod_cast primeProduct_pos m
  have hne : (((primeProduct m : ℕ) : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (primeProduct_pos m).ne'
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  have hlog : Complex.log (((primeProduct m : ℕ) : ℂ))
      = ((Real.log ((primeProduct m : ℕ) : ℝ) : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hpos.le).symm
  rw [hlog, diagonalFrequency]
  ring

/-- **(a) The uniform order bound, constant one.**  A nonzero friable Dirichlet polynomial whose
`K` exponent vectors are pairwise distinct has a nonvanishing derivative of some order `< K` at
every base point; it therefore vanishes to order at most `K - 1`.  No Diophantine input is used —
only unique factorization. -/
theorem diagonalDirichlet_has_nonzero_iteratedDeriv_lt_card {K : ℕ}
    (m : Fin K → (Nat.Primes →₀ ℕ)) (hm : Function.Injective m)
    (lam : Fin K → ℂ) (hlam : lam ≠ 0) (s₀ : ℂ) :
    ∃ k : Fin K,
      iteratedDeriv (k : ℕ)
        (fun s : ℂ => ∑ j : Fin K, lam j * (((primeProduct (m j) : ℕ) : ℂ)) ^ (-s)) s₀ ≠ 0 := by
  have hfun : (fun s : ℂ => ∑ j : Fin K, lam j * (((primeProduct (m j) : ℕ) : ℂ)) ^ (-s))
      = fun s : ℂ => exponentialSum (fun j => diagonalFrequency (m j)) lam s := by
    funext s
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [cpow_neg_eq_exp_mul_diagonalFrequency]
  rw [hfun]
  exact exponentialSum_has_nonzero_iteratedDeriv_lt_card
    (injective_diagonalFrequency.comp hm) hlam s₀

/-! ### (b) The `S`-free Vandermonde size bound -/

/-- The prime-log linear form `⟨m, ℓ_S⟩ = Σ_p m_p log p`. -/
def primeLogForm (m : Nat.Primes →₀ ℤ) : ℝ :=
  m.sum fun p z => (z : ℝ) * Real.log ((p : ℕ) : ℝ)

theorem primeLogForm_sub (m m' : Nat.Primes →₀ ℤ) :
    primeLogForm (m - m') = primeLogForm m - primeLogForm m' := by
  unfold primeLogForm
  refine Finsupp.sum_sub_index ?_
  intro p z₁ z₂
  push_cast
  ring

/-- **(b) The determinant size bound.**  The Vandermonde determinant of the prime-log forms is at
least the product of the reciprocal heights of the exponent differences.  The constant is `1` and
the bound does not mention the prime set. -/
theorem prod_inv_primeLogHeight_le_abs_det_vandermonde {K : ℕ}
    (m : Fin K → (Nat.Primes →₀ ℤ)) (hm : Function.Injective m) :
    ∏ i : Fin K, ∏ j ∈ Finset.Ioi i, ((primeLogHeight (m j - m i) : ℝ))⁻¹
      ≤ |(Matrix.vandermonde (fun i => primeLogForm (m i))).det| := by
  rw [Matrix.det_vandermonde, Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · exact Finset.prod_nonneg (fun j _ => by positivity)
  · rw [Finset.abs_prod]
    refine Finset.prod_le_prod (fun j _ => by positivity) (fun j hj => ?_)
    have hne : m j - m i ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro heq
      have : j = i := hm heq
      simp [this] at hj
    have hbound := logPrime_height_bound (m j - m i) hne
    have hform : primeLogForm (m j - m i) = primeLogForm (m j) - primeLogForm (m i) :=
      primeLogForm_sub _ _
    rw [primeLogForm] at hform
    rw [← hform] at *
    exact hbound

/-! ### (c) `P_S`-polynomial bounds at fixed degree -/

/-- The `ℓ¹` degree of an integer exponent vector. -/
def primeLogDegree (m : Nat.Primes →₀ ℤ) : ℕ :=
  m.support.sum fun p => (m p).natAbs

theorem primeProduct_le_pow {S : Finset Nat.Primes} {P : ℕ} (hP : ∀ p ∈ S, (p : ℕ) ≤ P)
    (ν : Nat.Primes →₀ ℕ) (hsupp : ν.support ⊆ S) :
    primeProduct ν ≤ P ^ (ν.sum fun _ k => k) := by
  classical
  unfold primeProduct
  rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod' (fun p hp => ?_)
  exact Nat.pow_le_pow_left (hP p (hsupp hp)) _

theorem sum_positivePart_add_sum_negativePart (m : Nat.Primes →₀ ℤ) :
    ((positivePart m).sum fun _ k => k) + ((negativePart m).sum fun _ k => k)
      = primeLogDegree m := by
  classical
  have hsubp : (positivePart m).support ⊆ m.support := by
    intro p hp
    simp only [Finsupp.mem_support_iff] at hp ⊢
    intro h
    exact hp (by simp [positivePart, h])
  have hsubn : (negativePart m).support ⊆ m.support := by
    intro p hp
    simp only [Finsupp.mem_support_iff] at hp ⊢
    intro h
    exact hp (by simp [negativePart, h])
  have hpos : ((positivePart m).sum fun _ k => k)
      = m.support.sum fun p => (m p).toNat := by
    rw [Finsupp.sum_of_support_subset _ hsubp _ (fun _ _ => rfl)]
    exact Finset.sum_congr rfl (fun p _ => by simp [positivePart])
  have hneg : ((negativePart m).sum fun _ k => k)
      = m.support.sum fun p => (-(m p)).toNat := by
    rw [Finsupp.sum_of_support_subset _ hsubn _ (fun _ _ => rfl)]
    exact Finset.sum_congr rfl (fun p _ => by simp [negativePart])
  rw [hpos, hneg, ← Finset.sum_add_distrib, primeLogDegree]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  omega

/-- **(c) The height bound at fixed degree.**  An exponent vector supported in `S` with `ℓ¹` degree
at most `D` has multiplicative height at most `P_S^D`. -/
theorem primeLogHeight_le_pow {S : Finset Nat.Primes} {P : ℕ} (hP1 : 1 ≤ P)
    (hP : ∀ p ∈ S, (p : ℕ) ≤ P)
    (m : Nat.Primes →₀ ℤ) (hsupp : m.support ⊆ S) {D : ℕ} (hD : primeLogDegree m ≤ D) :
    primeLogHeight m ≤ P ^ D := by
  classical
  have hsp : (positivePart m).support ⊆ S := by
    intro p hp
    refine hsupp ?_
    simp only [positivePart, Finsupp.mem_support_iff, Finsupp.mapRange_apply] at hp
    simp only [Finsupp.mem_support_iff]
    intro h
    exact hp (by simp [h])
  have hsn : (negativePart m).support ⊆ S := by
    intro p hp
    refine hsupp ?_
    simp only [negativePart, Finsupp.mem_support_iff, Finsupp.mapRange_apply] at hp
    simp only [Finsupp.mem_support_iff]
    intro h
    exact hp (by simp [h])
  have h1 := primeProduct_le_pow hP _ hsp
  have h2 := primeProduct_le_pow hP _ hsn
  calc primeLogHeight m
      = primeProduct (positivePart m) * primeProduct (negativePart m) := rfl
    _ ≤ P ^ ((positivePart m).sum fun _ k => k) * P ^ ((negativePart m).sum fun _ k => k) :=
        Nat.mul_le_mul h1 h2
    _ = P ^ primeLogDegree m := by
        rw [← pow_add, sum_positivePart_add_sum_negativePart]
    _ ≤ P ^ D := Nat.pow_le_pow_right hP1 hD

/-- **(c) The form bound at fixed degree.**  Every nonzero prime-log form of a degree-`≤ D` exponent
vector supported in `S` is at least `P_S^{-D}` in absolute value. -/
theorem inv_pow_le_abs_primeLogForm {S : Finset Nat.Primes} {P : ℕ} (hP1 : 1 ≤ P)
    (hP : ∀ p ∈ S, (p : ℕ) ≤ P)
    (m : Nat.Primes →₀ ℤ) (hm : m ≠ 0) (hsupp : m.support ⊆ S) {D : ℕ}
    (hD : primeLogDegree m ≤ D) :
    (((P : ℝ) ^ D))⁻¹ ≤ |primeLogForm m| := by
  have hbound := logPrime_height_bound m hm
  have hheight := primeLogHeight_le_pow hP1 hP m hsupp hD
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP1
  have hcast : ((primeLogHeight m : ℕ) : ℝ) ≤ ((P : ℝ) ^ D) := by
    have := (Nat.cast_le (α := ℝ)).mpr hheight
    simpa using this
  have hpos : (0 : ℝ) < ((primeLogHeight m : ℕ) : ℝ) := by
    exact_mod_cast primeLogHeight_pos m
  have hstep : (1 : ℝ) / ((P : ℝ) ^ D) ≤ 1 / ((primeLogHeight m : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hpos hcast
  rw [one_div, one_div] at hstep
  simpa [primeLogForm] using hstep.trans hbound

/-! ### (c) The monomial count -/

/-- Encode a prime into the mode alphabet `Option ↥S`, sending everything outside `S` to the
padding symbol. -/
def modeEncode (S : Finset Nat.Primes) (p : Nat.Primes) : Option {q : Nat.Primes // q ∈ S} :=
  if h : p ∈ S then some ⟨p, h⟩ else none

theorem modeEncode_eq_some_iff {S : Finset Nat.Primes} {p : Nat.Primes}
    {q : {q : Nat.Primes // q ∈ S}} :
    modeEncode S p = some q ↔ p = (q : Nat.Primes) := by
  classical
  unfold modeEncode
  by_cases hp : p ∈ S
  · rw [dif_pos hp]
    constructor
    · intro h
      exact congrArg Subtype.val (Option.some.inj h)
    · intro h
      exact congrArg some (Subtype.ext h)
  · rw [dif_neg hp]
    constructor
    · intro h
      exact absurd h (by simp)
    · intro h
      exact absurd (h ▸ q.2) hp

/-- The occupation multiset of a bounded-degree monomial, padded to length `d`. -/
def monomialMode (S : Finset Nat.Primes) (d : ℕ) (m : Nat.Primes →₀ ℕ) :
    Multiset (Option {q : Nat.Primes // q ∈ S}) :=
  (m.toMultiset.map (modeEncode S)) + Multiset.replicate (d - m.sum fun _ k => k) none

theorem card_monomialMode {S : Finset Nat.Primes} {d : ℕ} {m : Nat.Primes →₀ ℕ}
    (hdeg : (m.sum fun _ k => k) ≤ d) :
    Multiset.card (monomialMode S d m) = d := by
  unfold monomialMode
  rw [Multiset.card_add, Multiset.card_map, Multiset.card_replicate,
    Finsupp.card_toMultiset]
  have : (m.sum fun _ => id) = m.sum fun _ k => k := rfl
  omega

theorem count_monomialMode {S : Finset Nat.Primes} {d : ℕ} (m : Nat.Primes →₀ ℕ)
    (q : {q : Nat.Primes // q ∈ S}) :
    (monomialMode S d m).count (some q) = m (q : Nat.Primes) := by
  classical
  unfold monomialMode
  rw [Multiset.count_add, Multiset.count_replicate, if_neg (by simp), add_zero,
    Multiset.count_map]
  have hfilter : Multiset.filter (fun a => some q = modeEncode S a) m.toMultiset
      = Multiset.filter (fun a => (q : Nat.Primes) = a) m.toMultiset := by
    refine Multiset.filter_congr (fun a _ => ?_)
    constructor
    · intro h
      exact (modeEncode_eq_some_iff.mp h.symm).symm
    · intro h
      exact (modeEncode_eq_some_iff.mpr h.symm).symm
  rw [hfilter, ← Multiset.count_eq_card_filter_eq, Finsupp.count_toMultiset]

/-- Monomials supported in `S` of total degree at most `d` are counted exactly by
`C(|S| + d, d)`: a padding variable turns bounded degree into fixed degree. -/
theorem card_boundedDegreeMonomials_eq (S : Finset Nat.Primes) (d : ℕ) :
    Nat.card {m : Nat.Primes →₀ ℕ // m.support ⊆ S ∧ (m.sum fun _ k => k) ≤ d}
      = (S.card + d).choose d :=
  ArithmeticHarmonicAnalysis.card_bounded_supported_exponents S d

/-- The exact monomial count supplies the uniform upper bound. -/
theorem card_boundedDegreeMonomials_le (S : Finset Nat.Primes) (d : ℕ) :
    Nat.card {m : Nat.Primes →₀ ℕ // m.support ⊆ S ∧ (m.sum fun _ k => k) ≤ d}
      ≤ (S.card + d).choose d :=
  (card_boundedDegreeMonomials_eq S d).le

/-! ### The prime number theorem link -/

/-- **PNT link.**  The `n`-th prime is eventually at most `2 n log n`. -/
theorem eventually_nth_prime_le_two_mul :
    ∀ᶠ n : ℕ in atTop, ((nth_prime n : ℕ) : ℝ) ≤ 2 * ((n : ℝ) * Real.log (n : ℝ)) := by
  have hlo := nth_prime_asymp.isLittleO
  have hbound := hlo.bound (by norm_num : (0 : ℝ) < 1)
  have hlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  filter_upwards [hbound, hlarge] with n hn hn1
  have hlogn : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hvnonneg : (0 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (le_trans zero_le_one hn1) hlogn
  have habs : |((nth_prime n : ℕ) : ℝ) - (n : ℝ) * Real.log (n : ℝ)|
      ≤ (n : ℝ) * Real.log (n : ℝ) := by
    have h := hn
    simp only [Real.norm_eq_abs, one_mul] at h
    rwa [abs_of_nonneg hvnonneg] at h
  have := abs_le.mp habs
  linarith [this.2]

/-- Hence the `n`-th prime is eventually at most `2 n²`: polynomially bounded in `n`. -/
theorem eventually_nth_prime_le_sq :
    ∀ᶠ n : ℕ in atTop, ((nth_prime n : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
  have hlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact_mod_cast hn
  filter_upwards [eventually_nth_prime_le_two_mul, hlarge] with n hn hn1
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hn1)
    linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := le_trans zero_le_one hn1
  nlinarith [hn, mul_le_mul_of_nonneg_left hlog hnn]

end ZeroEstimateUniformity

end GaloisForLFunctions

#print axioms GaloisForLFunctions.ZeroEstimateUniformity.card_boundedDegreeMonomials_eq
