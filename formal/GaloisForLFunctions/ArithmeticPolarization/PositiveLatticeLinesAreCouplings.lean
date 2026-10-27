import GaloisForLFunctions.ArithmeticPolarization.PositivityIsInheritedByTheLeadingLine
import GaloisForLFunctions.HTGeometry.FejerRieszFactorization

/-!
# Positive lattice lines are couplings

A polar configuration on one vertical line whose ordinates lie in a lattice `ωℤ` (with `|k| ≤ n`)
has trigonometric sum `T(t) = Σ_z c(z) cos(Im z · t)`, a trigonometric polynomial of degree `n` in
`e^{iωt}`.

* **Positive lattice lines are Hermitian squares** (`posDef_latticeLine_iff_normSq`): the
  configuration has positive-definite vertical sections right of the line iff
  `T(t) = |Q(e^{iωt})|²` for a polynomial `Q` of degree `≤ n` (Fejér–Riesz, with the one-line law
  `posDef_polarSum_of_line`).
* **The leading line of a positive configuration is a coupling** (`leadingSum_eq_normSq`): if the
  ordinates of the rightmost line lie in `ωℤ`, its trigonometric sum is a single modulus square.

A modulus square `|Q|²` is the kernel count of a coupling: its collided points carry even
multiplicity. So on a commensurable line every positive completion is a coupling and collides
evenly; a positive completion that collides oddly must use incommensurable ordinates on its leading
line.
-/

open Complex Polynomial Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry HTGeometry

/-- The polynomial `Σ_z (c(z)/2)(X^{n + k_z} + X^{n − k_z})` of a lattice line. -/
def latticePoly (S : Finset ℂ) (c : ℂ → ℝ) (n : ℕ) (k : ℂ → ℤ) : ℂ[X] :=
  ∑ z ∈ S, C ((c z : ℂ) / 2) * (X ^ ((n : ℤ) + k z).toNat + X ^ ((n : ℤ) - k z).toNat)

theorem natDegree_latticePoly {S : Finset ℂ} {c : ℂ → ℝ} {n : ℕ} {k : ℂ → ℤ}
    (hk : ∀ z ∈ S, |k z| ≤ n) : (latticePoly S c n k).natDegree ≤ 2 * n := by
  refine natDegree_sum_le_of_forall_le _ _ fun z hz => ?_
  have hb := abs_le.mp (hk z hz)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le ?_ ?_))
  · refine (natDegree_X_pow_le _).trans ?_
    have : ((n : ℤ) + k z).toNat ≤ 2 * n := by
      rw [Int.toNat_le]; push_cast; linarith
    exact this
  · refine (natDegree_X_pow_le _).trans ?_
    have : ((n : ℤ) - k z).toNat ≤ 2 * n := by
      rw [Int.toNat_le]; push_cast; linarith
    exact this

/-- `e^{−inθ} e^{i(n+k)θ} = e^{ikθ}` for `|k| ≤ n`. -/
theorem exp_mul_pow_toNat (n : ℕ) {m : ℤ} (hm : 0 ≤ (n : ℤ) + m) (θ : ℝ) :
    Complex.exp (-((n : ℂ) * θ * I)) * Complex.exp (θ * I) ^ ((n : ℤ) + m).toNat =
      Complex.exp ((m : ℂ) * θ * I) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have h : (((n : ℤ) + m).toNat : ℂ) = (n : ℂ) + m := by
    have := Int.toNat_of_nonneg hm
    exact_mod_cast this
  rw [h]
  ring

/-- On the circle the lattice polynomial is the cosine sum `Σ c(z) cos(k_z θ)`. -/
theorem circleTrig_latticePoly {S : Finset ℂ} {c : ℂ → ℝ} {n : ℕ} {k : ℂ → ℤ}
    (hk : ∀ z ∈ S, |k z| ≤ n) (θ : ℝ) :
    circleTrig n (latticePoly S c n k) θ = ((∑ z ∈ S, c z * Real.cos (k z * θ) : ℝ) : ℂ) := by
  rw [circleTrig, latticePoly, eval_finsetSum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun z hz => ?_
  have hb := abs_le.mp (hk z hz)
  rw [eval_mul, eval_C, eval_add, eval_pow, eval_pow, eval_X]
  have h1 := exp_mul_pow_toNat n (m := k z) (by linarith) θ
  have h2 := exp_mul_pow_toNat n (m := -k z) (by linarith) θ
  rw [← sub_eq_add_neg] at h2
  have hcos : Complex.exp ((k z : ℂ) * θ * I) + Complex.exp (((-k z : ℤ) : ℂ) * θ * I) =
      2 * Complex.cos ((k z : ℂ) * θ) := by
    rw [Complex.two_cos]
    push_cast
    ring_nf
  calc Complex.exp (-((n : ℂ) * θ * I)) * ((c z : ℂ) / 2 *
        (Complex.exp (θ * I) ^ ((n : ℤ) + k z).toNat + Complex.exp (θ * I) ^ ((n : ℤ) - k z).toNat))
      = (c z : ℂ) / 2 * (Complex.exp ((k z : ℂ) * θ * I) +
          Complex.exp (((-k z : ℤ) : ℂ) * θ * I)) := by
        rw [← h1, ← h2]; ring
    _ = (c z : ℂ) * Complex.cos ((k z : ℂ) * θ) := by rw [hcos]; ring

/-- **A nonnegative lattice cosine sum is a modulus square** (Fejér–Riesz). -/
theorem exists_normSq_of_lattice {S : Finset ℂ} {c : ℂ → ℝ} {ω : ℝ} {n : ℕ} (hω : ω ≠ 0)
    (hlat : ∀ z ∈ S, ∃ k : ℤ, |k| ≤ n ∧ z.im = k * ω)
    (hT : ∀ t : ℝ, 0 ≤ ∑ z ∈ S, c z * Real.cos (z.im * t)) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧ ∀ t : ℝ,
      ∑ z ∈ S, c z * Real.cos (z.im * t) =
        Complex.normSq (Q.eval (Complex.exp (((ω * t : ℝ) : ℂ) * I))) := by
  classical
  choose! k hk using hlat
  -- the cosine sum at angle `θ` is `T(θ/ω)`
  have hkey : ∀ θ : ℝ, circleTrig n (latticePoly S c n k) θ =
      ((∑ z ∈ S, c z * Real.cos (z.im * (θ / ω)) : ℝ) : ℂ) := by
    intro θ
    rw [circleTrig_latticePoly (fun z hz => (hk z hz).1)]
    refine congrArg _ (Finset.sum_congr rfl fun z hz => ?_)
    rw [(hk z hz).2, show (k z : ℝ) * ω * (θ / ω) = k z * θ by field_simp]
  obtain ⟨Q, hQ, hQT⟩ := fejerRiesz n (latticePoly S c n k)
    (natDegree_latticePoly fun z hz => (hk z hz).1)
    (fun θ => by rw [hkey]; exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hT _⟩)
  refine ⟨Q, hQ, fun t => ?_⟩
  have h := hQT (ω * t)
  rw [hkey, show ω * t / ω = t by field_simp] at h
  exact_mod_cast h

/-- **Positive lattice lines are Hermitian squares.** -/
theorem posDef_latticeLine_iff_normSq {S : Finset ℂ} {c : ℂ → ℝ} {σ₀ ω : ℝ} {n : ℕ}
    (hω : ω ≠ 0) (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hline : ∀ z ∈ S, z.re = σ₀) (hlat : ∀ z ∈ S, ∃ k : ℤ, |k| ≤ n ∧ z.im = k * ω) :
    (∀ σ : ℝ, σ₀ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) ↔
      ∃ Q : ℂ[X], Q.natDegree ≤ n ∧ ∀ t : ℝ,
        ∑ z ∈ S, c z * Real.cos (z.im * t) =
          Complex.normSq (Q.eval (Complex.exp (((ω * t : ℝ) : ℂ) * I))) := by
  constructor
  · intro hpd
    refine exists_normSq_of_lattice hω hlat fun t => ?_
    have h := leadingSum_nonneg hS_conj hc_conj (fun z hz => (hline z hz).le) hpd
      (fun z hz _ => (hline z hz).le) t
    rwa [leadingSum, Finset.filter_true_of_mem hline] at h
  · rintro ⟨Q, -, hQ⟩ σ hσ
    exact posDef_polarSum_of_line hline (fun t _ => by rw [hQ t]; exact Complex.normSq_nonneg _) hσ

/-- **The leading line of a positive configuration is a coupling** when its ordinates are
commensurable. -/
theorem leadingSum_eq_normSq {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ σmax ω : ℝ} {n : ℕ} (hω : ω ≠ 0)
    (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σmax)
    (hlat : ∀ z ∈ S, z.re = σmax → ∃ k : ℤ, |k| ≤ n ∧ z.im = k * ω) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧ ∀ t : ℝ,
      leadingSum S c σmax t = Complex.normSq (Q.eval (Complex.exp (((ω * t : ℝ) : ℂ) * I))) :=
  exists_normSq_of_lattice hω
    (fun z hz => hlat z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2)
    (fun t => leadingSum_nonneg hS_conj hc_conj hS_re hpd hmax t)

end GaloisForLFunctions.ArithmeticPolarization
