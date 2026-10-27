import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The Hecke cocycle of renormalization

Weil's prime kernel `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on torsion orders is the renormalized limit of the
positive torsion energies: `Q_r(x) + log|1 − r| Σ x_n² → −Σ x_m x_n P(m, n) − Σ x_n² c(n)` with
`c(n) = I(n, n)/φ(n)` (AET `weilPrimeKernel_renormalized_torsion_energy`). The kernel `P` is invariant
under the Hecke correspondence `n ↦ tn` (`weilPrimeKernel_mul_left`); the counterterm is not.

* **The Hecke variation law** (`tendsto_heckeVariation`): transporting a cycle `x` on orders `S` to
  `t S`, `Q_r(T_t x) − Q_r(x) → −Σ_n x_n² β(n, t)`, with the **Hecke cocycle** `β(n, t) = c(tn) − c(n)`.
* **The cocycle is the anomaly minus the tame ramification** (`heckeCocycle_eq`):
  `β(n, t) = log t − Σ_{p ∣ t, p ∤ n} log p/(p − 1)`. The term `log t` is the regulator anomaly of `[t]`
  (`tendsto_log_one_sub_pow_sub_log_one_sub`); the correction is the tame different of
  `ℚ(ζ_{tn})/ℚ(ζ_n)` per unit degree.
* **Cocycle laws** (`heckeCocycle_mul`, `selfIntersection_le_heckeCocycle`, `heckeCocycle_le_log`,
  `heckeCocycle_of_subset`): `β(n, st) = β(n, s) + β(sn, t)`; `0 ≤ c(t) ≤ β(n, t) ≤ log t`; on orders
  divisible by every prime of `t` the cocycle is the pure anomaly `log t`.
* **Nontriviality** (`not_exists_bounded_potential`): `β` is not the coboundary of a bounded potential.
  No bounded change of the diagonal makes the renormalized torsion form Hecke covariant.
* **Covariance up to the degree character** (`tendsto_heckeVariation_of_saturated`,
  `tameDifferent_mul_of_subset`): on saturated cycles the variation is `−log t Σ x_n²`; the
  degree-normalized limit `−P + diag(Σ_{p ∣ n} log p/(p − 1))` is Hecke invariant there.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-! ### The Hecke cocycle -/

/-- The **Hecke cocycle** `β(n, t) = c(tn) − c(n)`: the change of the self-intersection density under
the Hecke correspondence `n ↦ tn`. -/
def heckeCocycle (n t : ℕ) : ℝ := selfIntersection (t * n) - selfIntersection n

/-- **The Hecke cocycle is the anomaly minus the tame ramification**:
`β(n, t) = log t − Σ_{p ∣ t, p ∤ n} log p/(p − 1)`. -/
theorem heckeCocycle_eq {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    heckeCocycle n t =
      Real.log t - ∑ p ∈ t.primeFactors \ n.primeFactors, Real.log p / ((p : ℝ) - 1) := by
  have htn : 0 < t * n := Nat.mul_pos ht hn
  rw [heckeCocycle, selfIntersection_eq htn, selfIntersection_eq hn, tameDifferent, tameDifferent,
    Nat.primeFactors_mul ht.ne' hn.ne', union_comm, ← union_sdiff_self_eq_union,
    sum_union disjoint_sdiff, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast ht.ne') (by exact_mod_cast hn.ne')]
  ring

/-- **The cocycle identity** `β(n, st) = β(n, s) + β(sn, t)`. -/
theorem heckeCocycle_mul (n s t : ℕ) :
    heckeCocycle n (s * t) = heckeCocycle n s + heckeCocycle (s * n) t := by
  simp only [heckeCocycle]
  rw [show s * t * n = t * (s * n) by ring]
  ring

theorem tameDifferent_term_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log p / ((p : ℝ) - 1) := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_nonneg (Real.log_nonneg h1.le) (by linarith)

/-- The cocycle is at most the anomaly: `β(n, t) ≤ log t`. -/
theorem heckeCocycle_le_log {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    heckeCocycle n t ≤ Real.log t := by
  rw [heckeCocycle_eq hn ht, sub_le_self_iff]
  exact sum_nonneg fun p hp =>
    tameDifferent_term_nonneg (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1)

/-- The cocycle dominates the self-intersection of `t`: `c(t) ≤ β(n, t)`, hence `β ≥ 0`. -/
theorem selfIntersection_le_heckeCocycle {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    selfIntersection t ≤ heckeCocycle n t := by
  rw [heckeCocycle_eq hn ht, selfIntersection_eq ht, tameDifferent]
  refine sub_le_sub_left (sum_le_sum_of_subset_of_nonneg sdiff_subset fun p hp _ =>
    tameDifferent_term_nonneg (Nat.prime_of_mem_primeFactors hp)) _

theorem heckeCocycle_nonneg {n t : ℕ} (hn : 0 < n) (ht : 0 < t) : 0 ≤ heckeCocycle n t :=
  (selfIntersection_nonneg ht).trans (selfIntersection_le_heckeCocycle hn ht)

/-- **On saturated orders the cocycle is the pure anomaly**: if every prime of `t` divides `n`,
`β(n, t) = log t`. -/
theorem heckeCocycle_of_subset {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hsub : t.primeFactors ⊆ n.primeFactors) : heckeCocycle n t = Real.log t := by
  rw [heckeCocycle_eq hn ht, sdiff_eq_empty_iff_subset.mpr hsub, sum_empty, sub_zero]

/-- On saturated orders the tame different is Hecke invariant. -/
theorem tameDifferent_mul_of_subset {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hsub : t.primeFactors ⊆ n.primeFactors) : tameDifferent (t * n) = tameDifferent n := by
  rw [tameDifferent, tameDifferent, Nat.primeFactors_mul ht.ne' hn.ne', union_eq_right.mpr hsub]

/-- The self-intersection of `O_{2^k}` is `(k − 1) log 2`. -/
theorem selfIntersection_two_pow {k : ℕ} (hk : k ≠ 0) :
    selfIntersection (2 ^ k) = ((k : ℝ) - 1) * Real.log 2 := by
  rw [selfIntersection_eq (by positivity), tameDifferent_prime_pow Nat.prime_two hk]
  push_cast
  rw [Real.log_pow]
  norm_num
  ring

/-- **The Hecke cocycle is not a bounded coboundary.** No potential `b` with `|b| ≤ B` satisfies
`b(tn) − b(n) = β(n, t)` for all orders: along `n = 2^k` the cocycle grows like `k log 2`. -/
theorem not_exists_bounded_potential :
    ¬ ∃ (b : ℕ → ℝ) (B : ℝ), (∀ n, |b n| ≤ B) ∧
      ∀ n t, 0 < n → 0 < t → b (t * n) - b n = heckeCocycle n t := by
  rintro ⟨b, B, hB, hb⟩
  obtain ⟨k, hk⟩ := exists_nat_gt ((2 * B) / Real.log 2 + 1)
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    have : (0 : ℝ) < 2 * B / Real.log 2 + 1 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      positivity
    simp at hk; linarith
  have h := hb 1 (2 ^ k) one_pos (by positivity)
  rw [mul_one, heckeCocycle, mul_one, selfIntersection_two_pow hk0,
    selfIntersection_eq one_pos, tameDifferent, Nat.primeFactors_one, sum_empty, Nat.cast_one,
    Real.log_one, sub_zero] at h
  have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have h1 := abs_le.mp (hB (2 ^ k))
  have h2 := abs_le.mp (hB 1)
  have hk' : 2 * B < ((k : ℝ) - 1) * Real.log 2 := by
    have := (div_lt_iff₀ hl).mp (show 2 * B / Real.log 2 < (k : ℝ) - 1 by linarith)
    linarith
  linarith [h1.2, h2.1]

/-! ### Hecke invariance of Weil's prime kernel -/

/-- **Weil's prime kernel is Hecke invariant**: `P(tm, tn) = P(m, n)`. -/
theorem weilPrimeKernel_mul_left {t : ℕ} (ht : 0 < t) (m n : ℕ) :
    weilPrimeKernel (t * m) (t * n) = weilPrimeKernel m n := by
  have hinj : ∀ a b : ℕ, t * a = t * b ↔ a = b := fun a b => Nat.mul_left_cancel_iff ht
  simp only [weilPrimeKernel, Nat.mul_dvd_mul_iff_left ht, ne_eq, hinj,
    Nat.mul_div_mul_left _ _ ht]

/-! ### The Hecke variation law -/

variable {S : Finset ℕ}

/-- The regularized torsion form `Q_r(x) = Σ_{m,n ∈ S} x_m x_n G(m,n) T_r(m,n)/√(mn)`. -/
def torsionForm (r : ℝ) (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n

/-- The renormalized limit `−Σ x_m x_n P(m,n) − Σ x_n² c(n)`. -/
def renormalizedTorsionForm (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  -(∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n) - ∑ n ∈ S, x n ^ 2 * selfIntersection n

/-- The Hecke transport `T_t` of a cycle on orders: `(T_t x)(a) = x(a/t)` on `t S`. -/
def heckeTransport (t : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun a => x (a / t)

theorem tendsto_torsionForm (hS : ∀ n ∈ S, 0 < n) (x : ℕ → ℝ) :
    Tendsto (fun r => torsionForm r S x + Real.log |1 - r| * ∑ n ∈ S, x n ^ 2) (𝓝 1)
      (𝓝 (renormalizedTorsionForm S x)) := by
  have h := (weilPrimeKernel_renormalized_torsion_energy hS x).2
  simpa [torsionForm, renormalizedTorsionForm, selfIntersection] using h

theorem sum_image_mul_left {t : ℕ} (ht : 0 < t) (f : ℕ → ℝ) :
    ∑ a ∈ S.image (t * ·), f a = ∑ n ∈ S, f (t * n) :=
  sum_image fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left ht h

theorem heckeTransport_mul {t : ℕ} (ht : 0 < t) (x : ℕ → ℝ) (n : ℕ) :
    heckeTransport t x (t * n) = x n := by
  simp [heckeTransport, Nat.mul_div_cancel_left n ht]

/-- The renormalized form of the transported cycle: the prime part is unchanged, the diagonal moves
by the cocycle. -/
theorem renormalizedTorsionForm_transport {t : ℕ} (ht : 0 < t) (x : ℕ → ℝ) :
    renormalizedTorsionForm (S.image (t * ·)) (heckeTransport t x) =
      renormalizedTorsionForm S x - ∑ n ∈ S, x n ^ 2 * heckeCocycle n t := by
  simp only [renormalizedTorsionForm, sum_image_mul_left ht, heckeTransport_mul ht,
    weilPrimeKernel_mul_left ht, heckeCocycle, mul_sub, sum_sub_distrib]
  ring

/-- **The Hecke variation law.** `Q_r(T_t x) − Q_r(x) → −Σ_n x_n² β(n, t)` as `r → 1`. -/
theorem tendsto_heckeVariation (hS : ∀ n ∈ S, 0 < n) {t : ℕ} (ht : 0 < t) (x : ℕ → ℝ) :
    Tendsto (fun r => torsionForm r (S.image (t * ·)) (heckeTransport t x) - torsionForm r S x)
      (𝓝 1) (𝓝 (-∑ n ∈ S, x n ^ 2 * heckeCocycle n t)) := by
  have hS' : ∀ a ∈ S.image (t * ·), 0 < a := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
    exact Nat.mul_pos ht (hS n hn)
  have hmass : ∑ a ∈ S.image (t * ·), heckeTransport t x a ^ 2 = ∑ n ∈ S, x n ^ 2 := by
    rw [sum_image_mul_left ht]
    simp only [heckeTransport_mul ht]
  have h := (tendsto_torsionForm hS' (heckeTransport t x)).sub (tendsto_torsionForm hS x)
  rw [renormalizedTorsionForm_transport ht, hmass,
    show ∀ R c : ℝ, R - c - R = -c from fun R c => by ring] at h
  exact Tendsto.congr (fun r => by ring) h

/-- **Covariance up to the degree character.** On saturated cycles (every prime of `t` divides every
order in `S`) the Hecke variation is `−log t Σ x_n²`. -/
theorem tendsto_heckeVariation_of_saturated (hS : ∀ n ∈ S, 0 < n) {t : ℕ} (ht : 0 < t)
    (hsat : ∀ n ∈ S, t.primeFactors ⊆ n.primeFactors) (x : ℕ → ℝ) :
    Tendsto (fun r => torsionForm r (S.image (t * ·)) (heckeTransport t x) - torsionForm r S x)
      (𝓝 1) (𝓝 (-(Real.log t * ∑ n ∈ S, x n ^ 2))) := by
  have h := tendsto_heckeVariation hS ht x
  rwa [sum_congr rfl fun n hn => by rw [heckeCocycle_of_subset (hS n hn) ht (hsat n hn)],
    ← sum_mul, mul_comm] at h

end GaloisForLFunctions.ArithmeticIntersectionTheory
