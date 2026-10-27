import GaloisForLFunctions.ArithmeticEffectivityTheory.TheArchimedeanComputationOfTheLogTorsion
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood

/-!
# The Fourier coefficients of the torsion measure

The torsion characteristics of order `≤ N` on the characteristic circle — the roots of unity of
order `≤ N`, the arithmetic point `0` included — form a measure `ν_N`. Contribution of
`TheArchimedeanComputationOfTheLogTorsion`: its logarithmic potential at the arithmetic point is
`−ψ(N)`. Here: its Fourier coefficients are Möbius sums.

* **Ramanujan's formula** (`ramanujanSum_eq_sum_moebius`). The `m`-th Fourier coefficient of the
  primitive `n`-th roots is `c_n(m) = Σ_{d e = n} μ(d) · e · [e ∣ m]`: Möbius inversion of
  `Σ_{ζ^n = 1} ζ^m = n [n ∣ m]` (`sum_nthRoots_pow`) over the decomposition of the `n`-th roots by
  exact order (`sum_nthRoots_eq_sum_divisors`).
* **The first coefficient is the Möbius function** (`sum_primitiveRoots_eq_moebius`):
  `Σ_{ζ primitive} ζ = μ(n)`. Hence **the first Fourier coefficient of `ν_N` is the Mertens function**
  (`torsionFourier_eq_mertens`), `ν̂_N(1) = M(N)`.
* **The two currencies on one measure** (`riemannHypothesis_iff_torsionFourier`,
  `torsion_measure_currencies`). RH holds iff `ν̂_N(1) = O(N^{1/2+δ})` for every `δ > 0`
  (Littlewood), iff the potential of `ν_N` at `0` is `−N + O(√N log² N)` (von Koch).

So the gauge-charged sums of the walls (the Mertens function) and the log-torsion of the horizon
are the first Fourier coefficient and the logarithmic potential at the arithmetic point of the same
measure: the torsion of the characteristic circle of the theta surface. The logarithmic kernel
`−log |1 − e(a)| = Σ_{m ≥ 1} cos(2πma)/m` links them, frequency by frequency.
-/

noncomputable section

open Polynomial Finset Complex
open scoped Real

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The **Ramanujan sum** `c_n(m) = Σ_{ζ primitive n-th root} ζ^m`. -/
def ramanujanSum (n m : ℕ) : ℂ := ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ m

/-- The `n`-th roots of unity are the powers `ω^k`, `k < n`, of a primitive one. -/
theorem nthRootsFinset_eq_image {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n) :
    nthRootsFinset n (1 : ℂ) = (range n).image (ω ^ ·) := by
  ext ζ
  simp only [mem_image, mem_range, Polynomial.mem_nthRootsFinset hn]
  constructor
  · intro h
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨i, hi, rfl⟩ := hω.eq_pow_of_pow_eq_one h
    exact ⟨i, hi, rfl⟩
  · rintro ⟨k, -, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]

/-- **Orthogonality**: `Σ_{ζ^n = 1} ζ^m = n [n ∣ m]`. -/
theorem sum_nthRoots_pow {n : ℕ} (hn : 0 < n) (m : ℕ) :
    ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ζ ^ m = if n ∣ m then (n : ℂ) else 0 := by
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω n := ⟨_, Complex.isPrimitiveRoot_exp n hn.ne'⟩
  rw [nthRootsFinset_eq_image hn hω, sum_image fun a ha b hb hab =>
    hω.pow_inj (mem_range.mp ha) (mem_range.mp hb) hab]
  simp_rw [← pow_mul, mul_comm _ m, pow_mul]
  split_ifs with hdvd
  · obtain ⟨c, rfl⟩ := hdvd
    simp [pow_mul, hω.pow_eq_one]
  · have h1 : ω ^ m ≠ 1 := fun h => hdvd (hω.dvd_of_pow_eq_one m h)
    have hn1 : (ω ^ m) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have h := mul_neg_geom_sum (ω ^ m) n
    rw [hn1, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm h1))

/-- The `n`-th roots of unity split by exact order. -/
theorem sum_nthRoots_eq_sum_divisors (n : ℕ) (f : ℂ → ℂ) :
    ∑ ζ ∈ nthRootsFinset n (1 : ℂ), f ζ = ∑ d ∈ n.divisors, ∑ ζ ∈ primitiveRoots d ℂ, f ζ := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, sum_biUnion]
  intro a ha b hb hab
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
  exact disjoint_left.mpr fun ζ hza hzb =>
    hab (((mem_primitiveRoots ha0).mp hza).unique ((mem_primitiveRoots hb0).mp hzb))

/-- **Ramanujan's formula**: `c_n(m) = Σ_{de = n} μ(d) e [e ∣ m]`. -/
theorem ramanujanSum_eq_sum_moebius {n : ℕ} (hn : 0 < n) (m : ℕ) :
    ramanujanSum n m = ∑ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℂ) * (if x.2 ∣ m then (x.2 : ℂ) else 0) :=
  (((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := fun d => ramanujanSum d m)
    (g := fun d => if d ∣ m then (d : ℂ) else 0)).mp fun d hd => by
      rw [← sum_nthRoots_pow hd m, sum_nthRoots_eq_sum_divisors]; rfl) n hn).symm

/-- **The first Fourier coefficient of the primitive roots is the Möbius function.** -/
theorem sum_primitiveRoots_eq_moebius {n : ℕ} (hn : 0 < n) :
    ∑ ζ ∈ primitiveRoots n ℂ, ζ = (ArithmeticFunction.moebius n : ℂ) := by
  have h := ramanujanSum_eq_sum_moebius hn 1
  simp only [ramanujanSum, pow_one] at h
  rw [h, Nat.sum_divisorsAntidiagonal' (fun a b =>
    (ArithmeticFunction.moebius a : ℂ) * (if b ∣ 1 then (b : ℂ) else 0)),
    sum_eq_single 1]
  · simp
  · intro b _ hb1
    rw [if_neg (by rwa [Nat.dvd_one]), mul_zero]
  · intro h1; exact absurd (Nat.one_mem_divisors.mpr hn.ne') h1

/-- The first Fourier coefficient of the torsion measure of order `≤ N`. -/
def torsionFourier (N : ℕ) : ℂ := ∑ n ∈ Icc 1 N, ∑ ζ ∈ primitiveRoots n ℂ, ζ

theorem sum_Icc_moebius_eq_mertens (N : ℕ) :
    ∑ n ∈ Icc 1 N, (ArithmeticFunction.moebius n : ℂ) = RHTower.mobiusMertensPartialSum N := by
  induction N with
  | zero => simp [RHTower.mobiusMertensPartialSum, RHTower.mobiusComplexCoefficient]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, RHTower.mobiusMertensPartialSum,
      RHTower.mobiusMertensPartialSum, Finset.sum_range_succ _ (N + 1)]
    simp [RHTower.mobiusComplexCoefficient]

/-- **`ν̂_N(1) = M(N)`**: the Mertens function is the first Fourier coefficient of the torsion
measure. -/
theorem torsionFourier_eq_mertens (N : ℕ) :
    torsionFourier N = RHTower.mobiusMertensPartialSum N := by
  rw [← sum_Icc_moebius_eq_mertens]
  exact sum_congr rfl fun n hn => sum_primitiveRoots_eq_moebius (by simp at hn; omega)

/-- **Littlewood on the torsion measure**: RH iff the first Fourier coefficient of the torsion
measure of order `≤ N` is `O(N^{1/2 + δ})` for every `δ > 0`. -/
theorem riemannHypothesis_iff_torsionFourier :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖torsionFourier N‖ ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
  rw [← RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis,
    RHTower.MobiusMertensAllStrictHalfPowerBound]
  simp only [torsionFourier_eq_mertens]

/-- **The two currencies on one measure.** The torsion characteristics of order `≤ N` have first
Fourier coefficient `M(N)` and, away from the arithmetic point, logarithmic potential at `0` equal
to `−ψ(N)`. -/
theorem torsion_measure_currencies (N : ℕ) :
    torsionFourier N = RHTower.mobiusMertensPartialSum N ∧
      Chebyshev.psi N = ∑ n ∈ Icc 2 N, torsionLogSum n :=
  ⟨torsionFourier_eq_mertens N, psi_eq_fareySum N⟩

end GaloisForLFunctions.ArithmeticEffectivityTheory
