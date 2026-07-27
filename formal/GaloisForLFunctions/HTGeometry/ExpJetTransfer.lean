import GaloisForLFunctions.HTGeometry.TaylorFormalBridge

/-!
# Jets of a function composed with an exponential

Composing an entire function with `z ↦ exp (a z)` transports jets triangularly: the `k`-th
derivative of `g (exp (a z))` is a fixed linear combination of `exp (a z) ^ j · g⁽ʲ⁾(exp (a z))` for
`j ≤ k`, with coefficients depending only on `a`, and the diagonal coefficient `a ^ k` is a unit.

The coefficients obey `c_{k+1,j} = a (j · c_{k,j} + c_{k,j-1})`, which is the chain rule applied to
one term: differentiating `exp(az)^j · g⁽ʲ⁾(exp(az))` produces `a j` times itself plus `a` times the
next term.  Triangularity and the unit diagonal are what make the transfer invertible, which is the
point of recording them.

* `expJetCoeff`, `expJetCoeff_eq_zero_of_lt`, **`expJetCoeff_diag`** — the coefficients, triangular
  with diagonal `a ^ k`;
* `deriv_expTerm` — differentiating one term `exp(az)^j · g⁽ʲ⁾(exp(az))` produces exactly
  `a · (j ·` itself `+` the next term `)`, which is the recursion;
* `sum_transfer_step` — the reindexing that turns that termwise derivative into the next
  combination;
* **`iteratedDeriv_comp_exp`** — the transfer identity.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The jet-transfer coefficients along `z ↦ exp (a z)`. -/
noncomputable def expJetCoeff (a : ℂ) : ℕ → ℕ → ℂ
  | 0, j => if j = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, j + 1 => a * ((j + 1 : ℂ) * expJetCoeff a k (j + 1) + expJetCoeff a k j)

@[simp] theorem expJetCoeff_zero_zero (a : ℂ) : expJetCoeff a 0 0 = 1 := by
  simp [expJetCoeff]

@[simp] theorem expJetCoeff_succ_zero (a : ℂ) (k : ℕ) : expJetCoeff a (k + 1) 0 = 0 := rfl

theorem expJetCoeff_succ_succ (a : ℂ) (k j : ℕ) :
    expJetCoeff a (k + 1) (j + 1)
      = a * ((j + 1 : ℂ) * expJetCoeff a k (j + 1) + expJetCoeff a k j) := rfl

/-- The transfer is triangular: no jet above the order contributes. -/
theorem expJetCoeff_eq_zero_of_lt (a : ℂ) : ∀ {k j : ℕ}, k < j → expJetCoeff a k j = 0 := by
  intro k
  induction k with
  | zero =>
      intro j hj
      have : j ≠ 0 := by omega
      simp [expJetCoeff, this]
  | succ k ih =>
      intro j hj
      match j with
      | 0 => omega
      | j + 1 =>
          rw [expJetCoeff_succ_succ, ih (by omega), ih (by omega)]
          ring

/-- The diagonal coefficient is `a ^ k`, a unit whenever `a` is. -/
theorem expJetCoeff_diag (a : ℂ) : ∀ k : ℕ, expJetCoeff a k k = a ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [expJetCoeff_succ_succ, expJetCoeff_eq_zero_of_lt a (by omega), ih]
      ring

/-! ### The transfer identity -/

theorem deriv_expTerm {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) (a : ℂ) (j : ℕ) (z : ℂ) :
    deriv (fun w => Complex.exp (a * w) ^ j * iteratedDeriv j g (Complex.exp (a * w))) z
      = a * ((j : ℂ) * Complex.exp (a * z) ^ j * iteratedDeriv j g (Complex.exp (a * z))
        + Complex.exp (a * z) ^ (j + 1) * iteratedDeriv (j + 1) g (Complex.exp (a * z))) := by
  have hE : ∀ w : ℂ, HasDerivAt (fun u : ℂ => Complex.exp (a * u)) (a * Complex.exp (a * w)) w := by
    intro w
    simpa [mul_comm] using ((hasDerivAt_id w).const_mul a).cexp
  have hDj : Differentiable ℂ (iteratedDeriv j g) :=
    (contDiff_iteratedDeriv j hg).differentiable (by simp)
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (a * w) ^ j)
      ((j : ℂ) * Complex.exp (a * z) ^ (j - 1) * (a * Complex.exp (a * z))) z :=
    (hE z).pow j
  have h2 : HasDerivAt (fun w : ℂ => iteratedDeriv j g (Complex.exp (a * w)))
      (iteratedDeriv (j + 1) g (Complex.exp (a * z)) * (a * Complex.exp (a * z))) z := by
    have hcomp := (((hDj (Complex.exp (a * z))).hasDerivAt).comp z (hE z))
    rw [iteratedDeriv_succ]
    exact hcomp
  have hprod : HasDerivAt
      (fun w : ℂ => Complex.exp (a * w) ^ j * iteratedDeriv j g (Complex.exp (a * w)))
      ((j : ℂ) * Complex.exp (a * z) ^ (j - 1) * (a * Complex.exp (a * z)) *
          iteratedDeriv j g (Complex.exp (a * z))
        + Complex.exp (a * z) ^ j *
          (iteratedDeriv (j + 1) g (Complex.exp (a * z)) * (a * Complex.exp (a * z)))) z :=
    h1.mul h2
  rw [hprod.deriv]
  cases j with
  | zero => simp; ring
  | succ i =>
      have hpow : Complex.exp (a * z) ^ (i + 1) = Complex.exp (a * z) * Complex.exp (a * z) ^ i := by
        ring
      simp only [Nat.add_sub_cancel]
      push_cast
      rw [hpow]
      ring


/-! ### The shift identity behind the recursion -/

/-- The algebraic core: with coefficients obeying the transfer recursion, differentiating the
order-`k` combination termwise and reindexing gives the order-`k+1` combination. -/
theorem sum_transfer_step (a E : ℂ) (D : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (hc0 : ∀ m, c (m + 1) 0 = 0)
    (hcs : ∀ m j, c (m + 1) (j + 1) = a * ((j + 1 : ℂ) * c m (j + 1) + c m j))
    (k : ℕ) (htri : c k (k + 1) = 0) :
    ∑ j ∈ range (k + 1), c k j * (a * ((j : ℂ) * E ^ j * D j + E ^ (j + 1) * D (j + 1)))
      = ∑ i ∈ range (k + 2), c (k + 1) i * E ^ i * D i := by
  have hRHS : ∑ i ∈ range (k + 2), c (k + 1) i * E ^ i * D i
      = ∑ i ∈ range (k + 1),
          a * (((i : ℂ) + 1) * c k (i + 1) + c k i) * E ^ (i + 1) * D (i + 1) := by
    rw [sum_range_succ' (fun i => c (k + 1) i * E ^ i * D i) (k + 1), hc0 k]
    simp only [zero_mul]
    rw [add_zero]
    exact sum_congr rfl fun i _ => by rw [hcs k i]
  have hsplit : ∑ j ∈ range (k + 1),
        c k j * (a * ((j : ℂ) * E ^ j * D j + E ^ (j + 1) * D (j + 1)))
      = (∑ j ∈ range (k + 1), a * (j : ℂ) * c k j * E ^ j * D j)
        + ∑ j ∈ range (k + 1), a * c k j * E ^ (j + 1) * D (j + 1) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hfirst : ∑ j ∈ range (k + 1), a * (j : ℂ) * c k j * E ^ j * D j
      = ∑ i ∈ range (k + 1), a * ((i : ℂ) + 1) * c k (i + 1) * E ^ (i + 1) * D (i + 1) := by
    rw [sum_range_succ' (fun j => a * (j : ℂ) * c k j * E ^ j * D j) k,
      sum_range_succ (fun i => a * ((i : ℂ) + 1) * c k (i + 1) * E ^ (i + 1) * D (i + 1)) k, htri]
    have hz : a * ((0 : ℕ) : ℂ) * c k 0 * E ^ 0 * D 0 = 0 := by push_cast; ring
    rw [hz, add_zero]
    have hlast : a * ((k : ℂ) + 1) * (0 : ℂ) * E ^ (k + 1) * D (k + 1) = 0 := by ring
    rw [hlast, add_zero]
    exact sum_congr rfl fun i _ => by push_cast; ring
  rw [hsplit, hfirst, hRHS, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- **The jet transfer along an exponential.**  Every derivative of `g (exp (a z))` is the triangular
combination of `exp (a z) ^ j · g⁽ʲ⁾(exp (a z))` prescribed by `expJetCoeff`. -/
theorem iteratedDeriv_comp_exp {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) (a : ℂ) :
    ∀ (k : ℕ) (z : ℂ),
      iteratedDeriv k (fun w => g (Complex.exp (a * w))) z
        = ∑ j ∈ range (k + 1),
            expJetCoeff a k j * Complex.exp (a * z) ^ j *
              iteratedDeriv j g (Complex.exp (a * z)) := by
  intro k
  induction k with
  | zero => intro z; simp
  | succ k ih =>
      intro z
      have hdiff : ∀ j : ℕ,
          DifferentiableAt ℂ (fun w : ℂ => Complex.exp (a * w) ^ j *
            iteratedDeriv j g (Complex.exp (a * w))) z := by
        intro j
        have hE : DifferentiableAt ℂ (fun u : ℂ => Complex.exp (a * u)) z := by fun_prop
        have hDj : Differentiable ℂ (iteratedDeriv j g) :=
          (contDiff_iteratedDeriv j hg).differentiable (by simp)
        exact (hE.pow j).mul ((hDj _).comp z hE)
      have hfun : iteratedDeriv k (fun w => g (Complex.exp (a * w)))
          = fun w => ∑ j ∈ range (k + 1),
              expJetCoeff a k j * (Complex.exp (a * w) ^ j *
                iteratedDeriv j g (Complex.exp (a * w))) := by
        funext w
        rw [ih w]
        exact sum_congr rfl fun j _ => by ring
      rw [iteratedDeriv_succ, hfun,
        deriv_fun_sum (fun j _ => (hdiff j).const_mul (expJetCoeff a k j))]
      have hstep : ∀ j ∈ range (k + 1),
          deriv (fun w => expJetCoeff a k j * (Complex.exp (a * w) ^ j *
            iteratedDeriv j g (Complex.exp (a * w)))) z
          = expJetCoeff a k j * (a * ((j : ℂ) * Complex.exp (a * z) ^ j *
              iteratedDeriv j g (Complex.exp (a * z))
            + Complex.exp (a * z) ^ (j + 1) *
              iteratedDeriv (j + 1) g (Complex.exp (a * z)))) := by
        intro j _
        rw [deriv_const_mul _ (hdiff j), deriv_expTerm hg a j z]
      rw [sum_congr rfl hstep]
      exact sum_transfer_step a (Complex.exp (a * z))
        (fun j => iteratedDeriv j g (Complex.exp (a * z))) (expJetCoeff a)
        (expJetCoeff_succ_zero a) (expJetCoeff_succ_succ a) k
        (expJetCoeff_eq_zero_of_lt a (by omega))

end GaloisForLFunctions.HTGeometry
