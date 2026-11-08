import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesAreTheJumpsOfTheHeckeKernel

/-!
# No metric on `ℙ¹_ℤ` carries the jets of the trivial zeros

On the arithmetic surface `ℙ¹_ℤ` with a metric on `O(1)` of potential `φ`, the archimedean Green
function of two points of `ℂ` is `g_φ(z, w) = −log|z − w| + φ(z) + φ(w)`. Two torsion orbits pair by

  `A_φ(m, n) = Σ_{ζ ∈ O_m, η ∈ O_n} g_φ(ζ, η) = −I(m, n) + φ(n)·P(m) + φ(m)·P(n)`

(`arakelovPairing_eq`), with `I` the finite intersection of `ArithmeticEffectivityTheory`, `φ(·)` Euler's
function and `P(k) = Σ_{ζ ∈ O_k} φ(ζ)`: the archimedean fibre returns the prime channel with the
opposite sign (the product formula) plus a kernel of rank at most two. On coprime orders the prime
channel vanishes, so every combination `α I + β A_φ`, twisted by `G(m, n)`, is a rank-two kernel
`u(m)v(n) + v(m)u(n)` there.

The Frobenius intersection of `Spec ℤ` on coprime orders is the archimedean term
`min/(1 − (min/max)²)` alone, and its block on rows `{2, 3, 5}` and columns `{7, 11, 13}` is
nonsingular (`det_archBlock_ne_zero`), while a rank-two kernel has singular `3 × 3` blocks
(`det_rankTwo_eq_zero`). Hence no metric on `ℙ¹_ℤ` and no weights `α, β` make the Frobenius
intersection a gcd-twisted Arakelov pairing of torsion orbits (`not_exists_arakelov_frobeniusIntersection`).

The jets of the trivial zeros have infinite rank; the genus-zero half-product `ℙ¹_ℤ`, for any metric,
supplies the primes and two archimedean dimensions only.
-/

open Finset Matrix
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

/-- The Arakelov pairing of the torsion orbits `O_m, O_n` for the metric of potential `φ`. -/
def arakelovPairing (φ : ℂ → ℝ) (m n : ℕ) : ℝ :=
  ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ, (-Real.log ‖ζ - η‖ + φ ζ + φ η)

/-- The potential summed over one orbit. -/
def potentialSum (φ : ℂ → ℝ) (k : ℕ) : ℝ := ∑ ζ ∈ primitiveRoots k ℂ, φ ζ

theorem card_primitiveRoots_complex {k : ℕ} (hk : 0 < k) :
    ((primitiveRoots k ℂ).card : ℝ) = Nat.totient k := by
  rw [(Complex.isPrimitiveRoot_exp k hk.ne').card_primitiveRoots]

/-- **The archimedean fibre of `ℙ¹_ℤ`**: minus the finite intersection, plus rank two. -/
theorem arakelovPairing_eq (φ : ℂ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    arakelovPairing φ m n =
      -orbitIntersection m n + Nat.totient n * potentialSum φ m + Nat.totient m * potentialSum φ n := by
  unfold arakelovPairing orbitIntersection potentialSum
  simp only [sum_add_distrib, sum_neg_distrib, sum_const, nsmul_eq_mul]
  rw [← sum_mul, card_primitiveRoots_complex hn, card_primitiveRoots_complex hm, mul_sum]
  ring

/-- On coprime orders torsion orbits do not meet at finite places. -/
theorem orbitIntersection_of_coprime {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (h : Nat.Coprime m n) :
    orbitIntersection m n = 0 := by
  have hmn : m ≠ n := fun e => by
    subst e; rw [Nat.coprime_self] at h; omega
  have h1 : ¬ m ∣ n := fun d => by
    have := Nat.Coprime.eq_one_of_dvd h d; omega
  have h2 : ¬ n ∣ m := fun d => by
    have := Nat.Coprime.eq_one_of_dvd h.symm d; omega
  rw [orbitIntersection_eq (by omega) (by omega) hmn, if_neg h2, if_neg h1]

/-- The archimedean Frobenius kernel `min/(1 − (min/max)²)`. -/
def archKernel (m n : ℕ) : ℝ := min (m : ℝ) n / (1 - (min (m : ℝ) n / max (m : ℝ) n) ^ 2)

theorem frobeniusIntersection_of_coprime {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (h : Nat.Coprime m n) :
    frobeniusIntersection m n = archKernel m n := by
  have hmn : m ≠ n := fun e => by
    subst e; rw [Nat.coprime_self] at h; omega
  rw [frobeniusIntersection_eq (by omega) (by omega) hmn, orbitIntersection_of_coprime hm hn h,
    mul_zero, add_zero, archKernel]

/-- A kernel of rank two has singular `3 × 3` blocks. -/
theorem det_rankTwo_eq_zero (u v : Fin 3 → ℝ) (u' v' : Fin 3 → ℝ) :
    Matrix.det (Matrix.of fun i j => u i * v' j + v i * u' j) = 0 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  ring

/-- The archimedean block on rows `{2, 3, 5}` and columns `{7, 11, 13}`. -/
def archBlock : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => archKernel (![2, 3, 5] i) (![7, 11, 13] j)

/-- The block, entry by entry: `r c²/(c² − r²)`. -/
theorem archBlock_eq : archBlock = !![98 / 45, 242 / 117, 338 / 165;
    147 / 40, 363 / 112, 507 / 160; 245 / 24, 605 / 96, 845 / 144] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [archBlock, archKernel, Matrix.of_apply, min_def, max_def]

/-- **The jets have rank at least three.** -/
theorem det_archBlock_ne_zero : Matrix.det archBlock ≠ 0 := by
  rw [archBlock_eq, Matrix.det_fin_three]
  norm_num

/-- **No metric on `ℙ¹_ℤ` carries the jets.** No potential `φ` and weights `α, β` make the
Frobenius intersection of `Spec ℤ` a gcd-twisted combination of the finite and archimedean
intersections of torsion orbits on `ℙ¹_ℤ`. -/
theorem not_exists_arakelov_frobeniusIntersection :
    ¬ ∃ (φ : ℂ → ℝ) (α β : ℝ), ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      frobeniusIntersection m n =
        gcdTwist m n * (α * orbitIntersection m n + β * arakelovPairing φ m n) := by
  rintro ⟨φ, α, β, h⟩
  -- on coprime orders the pairing is the rank-two kernel `β (φ(n) P(m) + φ(m) P(n))`
  have hrank : ∀ m n : ℕ, 1 < m → 1 < n → Nat.Coprime m n →
      archKernel m n = β * potentialSum φ m * Nat.totient n + Nat.totient m * (β * potentialSum φ n) := by
    intro m n hm hn hc
    have hmn : m ≠ n := fun e => by
      subst e; rw [Nat.coprime_self] at hc; omega
    have := h m n (by omega) (by omega) hmn
    rw [frobeniusIntersection_of_coprime hm hn hc, gcdTwist_of_coprime hc, one_mul,
      arakelovPairing_eq φ (by omega) (by omega), orbitIntersection_of_coprime hm hn hc] at this
    rw [this]; ring
  have hblock : archBlock = Matrix.of fun i j =>
      (β * potentialSum φ (![2, 3, 5] i)) * (Nat.totient (![7, 11, 13] j) : ℝ) +
        (Nat.totient (![2, 3, 5] i) : ℝ) * (β * potentialSum φ (![7, 11, 13] j)) := by
    ext i j
    rw [archBlock, Matrix.of_apply, Matrix.of_apply]
    fin_cases i <;> fin_cases j <;> exact hrank _ _ (by norm_num) (by norm_num) (by norm_num)
  exact det_archBlock_ne_zero (by rw [hblock]; exact det_rankTwo_eq_zero _ _ _ _)

end GaloisForLFunctions.SurfaceOfSpecZ
