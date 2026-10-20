import GaloisForLFunctions.BezoutValuationIncidence.FlatSelbergRowAndExactQuadraticSandwichOrder
import GaloisForLFunctions.BezoutValuationIncidence.DiscretePrimitiveEnergyAndJordanComparison

/-!
# The canonical primitive as an exponential sum, and its windows

The canonical successor primitive `W(k) = -Σ_{d ≤ N} c(d) ψ_d(k)`, with `ψ_d` the centered sawtooth of
modulus `d`, is the zero-mean primitive of the centered response: `W(k+1) - W(k) = s(k+1) - H`. On
the response frequencies `T_N` this integration is division by `ζ - 1`, so

`W(k) = Σ_{ζ ∈ T_N, ζ ≠ 1} Y(ord ζ) ζ / (ζ - 1) · ζ^k`.

Finite Parseval over the factorial period identifies the coefficient energy
`Σ_{ζ ≠ 1} Y(ord ζ)² / |ζ - 1|²` with the primitive energy `E`, whose Jordan form is
`12 E = Σ_{2 ≤ q ≤ N} J₂(q) Y(q)²`. The window sandwich then gives, at every phase and length,

`|Σ_{A<k≤A+K} W(k)² - K E| ≤ (2N² - 1) E`,

and Cauchy–Schwarz gives the pointwise bound `W(k)² ≤ (Φ(N) - 1) E`. The prefix discrepancy differs
from `W` by the constant `W(0)`, so the same laws hold for `L_N(M, c) - W(0)`: the prefix discrepancy
has its period energy on every window longer than `N²`, up to a relative error of order `N²/K`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Finite Parseval for root-of-unity sums -/

/-- **Parseval over a full period.** If every frequency is a `P`-th root of unity, the mean square
of `Σ a(ζ) ζ^k` over `k < P` is the coefficient energy. -/
theorem sum_range_norm_sq_sum_mul_pow {P : ℕ} {T : Finset ℂ} (hT : ∀ ζ ∈ T, ζ ^ P = 1)
    (hP : 0 < P) (a : ℂ → ℂ) :
    ∑ k ∈ range P, ‖∑ ζ ∈ T, a ζ * ζ ^ k‖ ^ 2 = P * ∑ ζ ∈ T, ‖a ζ‖ ^ 2 := by
  classical
  have hnorm : ∀ ζ ∈ T, ‖ζ‖ = 1 := fun ζ hζ =>
    Complex.norm_eq_one_of_pow_eq_one (hT ζ hζ) hP.ne'
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [norm_sq_sum_mul_pow]
  rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast, sum_comm, mul_sum]
  refine sum_congr rfl fun ζ hζ => ?_
  rw [sum_comm, ← add_sum_erase T _ hζ]
  have hdiag : ∑ k ∈ range P, a ζ * conj (a ζ) * (ζ * conj ζ) ^ k = P * ((‖a ζ‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : ζ * conj ζ = 1 := by
      rw [mul_comm]
      exact conj_mul_self_of_norm_eq_one (hnorm ζ hζ)
    rw [h1]
    simp only [one_pow, mul_one, sum_const, card_range, nsmul_eq_mul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hoff : ∑ ξ ∈ T.erase ζ, ∑ k ∈ range P, a ζ * conj (a ξ) * (ζ * conj ξ) ^ k = 0 := by
    refine sum_eq_zero fun ξ hξ => ?_
    have hξT := mem_of_mem_erase hξ
    have hne : ξ ≠ ζ := ne_of_mem_erase hξ
    have hz : (ζ * conj ξ) ^ P = 1 := by
      rw [mul_pow, ← map_pow, hT ζ hζ, hT ξ hξT, map_one, one_mul]
    have hz1 : ζ * conj ξ ≠ 1 := by
      intro h
      apply hne
      calc ξ = ξ * (ζ * conj ξ) := by rw [h, mul_one]
        _ = (conj ξ * ξ) * ζ := by ring
        _ = ζ := by rw [conj_mul_self_of_norm_eq_one (hnorm ξ hξT), one_mul]
    rw [← mul_sum, geom_sum_eq hz1, hz, sub_self, zero_div, mul_zero]
  rw [hdiag, hoff, add_zero]

/-! ## §2. The spectral form of the canonical primitive -/

/-- The nontrivial response frequencies. -/
def primitiveRoots' (N : ℕ) : Finset ℂ := (responseRoots N).erase 1

/-- The spectral coefficient `Y(ord ζ) ζ / (ζ - 1)` of the canonical primitive. -/
def primitiveSpectralCoeff (N : ℕ) (c : ℕ → ℝ) (ζ : ℂ) : ℂ :=
  (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ζ / (ζ - 1)

theorem one_mem_responseRoots {N : ℕ} (hN : 1 ≤ N) : (1 : ℂ) ∈ responseRoots N :=
  mem_biUnion.mpr ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩,
    (Polynomial.mem_nthRootsFinset one_pos 1).mpr (one_pow 1)⟩

/-- The centered response is the exponential sum over the nontrivial frequencies. -/
theorem sieveSeq_sub_harmonic_eq_sum_primitiveRoots' {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (k : ℕ) :
    ((sieveSeq N c k - finiteHarmonicSum N c : ℝ) : ℂ) =
      ∑ ζ ∈ primitiveRoots' N, (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ζ ^ k := by
  rw [Complex.ofReal_sub, sieveSeq_eq_sum_responseRoots, ← add_sum_erase _ _ (one_mem_responseRoots hN),
    orderOf_one, one_pow, mul_one, selbergMultiplesCoord_one_eq_finiteHarmonicSum, add_sub_cancel_left]
  rfl

/-- **Spectral form of the canonical primitive.** `W(k) = Σ_{ζ ≠ 1} Y(ord ζ) ζ/(ζ - 1) ζ^k`. -/
theorem weightedCenteredSawtoothSum_eq_spectral {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (k : ℕ) :
    (weightedCenteredSawtoothSum N c k : ℂ) =
      ∑ ζ ∈ primitiveRoots' N, primitiveSpectralCoeff N c ζ * ζ ^ k := by
  set F : ℕ → ℂ := fun k => ∑ ζ ∈ primitiveRoots' N, primitiveSpectralCoeff N c ζ * ζ ^ k
  set G : ℕ → ℂ := fun k => (weightedCenteredSawtoothSum N c k : ℂ) - F k with hG
  have hne1 : ∀ ζ ∈ primitiveRoots' N, ζ - 1 ≠ 0 := fun ζ hζ =>
    sub_ne_zero.mpr (ne_of_mem_erase hζ)
  -- equal increments
  have hstep : ∀ k, G (k + 1) = G k := by
    intro k
    have hW := weightedCenteredSawtoothSum_succ_sub_eq N c k
    rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum] at hW
    have hF : F (k + 1) - F k =
        ((sieveSeq N c (k + 1) - finiteHarmonicSum N c : ℝ) : ℂ) := by
      rw [sieveSeq_sub_harmonic_eq_sum_primitiveRoots' hN, ← sum_sub_distrib]
      refine sum_congr rfl fun ζ hζ => ?_
      unfold primitiveSpectralCoeff
      field_simp [hne1 ζ hζ]
      ring
    have hWc : ((weightedCenteredSawtoothSum N c (k + 1) : ℝ) : ℂ) -
        (weightedCenteredSawtoothSum N c k : ℂ) =
        ((sieveSeq N c (k + 1) - finiteHarmonicSum N c : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sub, hW]
    simp only [hG]
    linear_combination hWc - hF
  have hconst : ∀ k, G k = G 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep, ih]
  -- zero period mean on both sides
  have hP := Nat.factorial_pos N
  have hsumW : ∑ k ∈ range N.factorial, (weightedCenteredSawtoothSum N c k : ℂ) = 0 := by
    rw [← Complex.ofReal_sum, weightedCenteredSawtoothSum_period_sum, Complex.ofReal_zero]
  have hsumF : ∑ k ∈ range N.factorial, F k = 0 := by
    simp only [F]
    rw [sum_comm]
    refine sum_eq_zero fun ζ hζ => ?_
    rw [← mul_sum, geom_sum_eq (ne_of_mem_erase hζ),
      pow_factorial_eq_one_of_mem_responseRoots (mem_of_mem_erase hζ), sub_self, zero_div,
      mul_zero]
  have hG0 : (N.factorial : ℂ) * G 0 = 0 := by
    have h := sum_congr rfl fun k (_ : k ∈ range N.factorial) => hconst k
    rw [sum_const, card_range, nsmul_eq_mul] at h
    rw [← h]
    simp only [hG, sum_sub_distrib, hsumW, hsumF, sub_self]
  have hG0' : G 0 = 0 :=
    (mul_eq_zero.mp hG0).resolve_left (by exact_mod_cast (Nat.factorial_pos N).ne')
  have := hconst k
  rw [hG0'] at this
  exact sub_eq_zero.mp this

/-! ## §3. The coefficient energy is the primitive energy -/

theorem sum_norm_sq_primitiveSpectralCoeff {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    ∑ ζ ∈ primitiveRoots' N, ‖primitiveSpectralCoeff N c ζ‖ ^ 2 = sievePrimitiveEnergy N c := by
  have hP := Nat.factorial_pos N
  have hPar := sum_range_norm_sq_sum_mul_pow (P := N.factorial) (T := primitiveRoots' N)
    (fun ζ hζ => pow_factorial_eq_one_of_mem_responseRoots (mem_of_mem_erase hζ)) hP
    (primitiveSpectralCoeff N c)
  simp only [← weightedCenteredSawtoothSum_eq_spectral hN, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hPar
  unfold sievePrimitiveEnergy
  rw [hPar]
  have : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  field_simp

/-- The Jordan form of the coefficient energy: `12 Σ |Y ζ/(ζ - 1)|² = Σ_{q ≥ 2} J₂(q) Y(q)²`. -/
theorem twelve_mul_sum_norm_sq_primitiveSpectralCoeff {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    12 * ∑ ζ ∈ primitiveRoots' N, ‖primitiveSpectralCoeff N c ζ‖ ^ 2 =
      ∑ q ∈ Icc 2 N, jordanTotient2 q * selbergMultiplesCoord N c q ^ 2 := by
  rw [sum_norm_sq_primitiveSpectralCoeff hN, twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]

/-! ## §4. Windows and pointwise bounds -/

/-- **Window energy of the canonical primitive at quadratic order.** -/
theorem abs_window_sum_sq_weightedCenteredSawtoothSum_sub_le {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (A K : ℕ) :
    |∑ k ∈ Icc (A + 1) (A + K), weightedCenteredSawtoothSum N c k ^ 2 -
        K * sievePrimitiveEnergy N c| ≤ (2 * (N : ℝ) ^ 2 - 1) * sievePrimitiveEnergy N c := by
  have h := abs_window_sum_norm_sq_sub_le hN (erase_subset 1 (responseRoots N))
    (primitiveSpectralCoeff N c) A K
  rw [show (responseRoots N).erase 1 = primitiveRoots' N from rfl] at h
  simp only [← weightedCenteredSawtoothSum_eq_spectral (by omega : 1 ≤ N), Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h
  rwa [sum_norm_sq_primitiveSpectralCoeff (by omega)] at h

theorem card_responseRoots (N : ℕ) : ((responseRoots N).card : ℝ) = cyclotomicIncidenceOrder N := by
  have h : ∑ ζ ∈ responseRoots N, (1 : ℝ) = ∑ q ∈ Icc 1 N, (q.totient : ℝ) * 1 :=
    sum_responseRoots_orderOf N (fun _ => 1)
  rw [sum_const, nsmul_eq_mul, mul_one] at h
  simp only [mul_one] at h
  rw [h, cyclotomicIncidenceOrder]
  push_cast
  rfl

/-- **Pointwise bound.** `W(k)² ≤ (Φ(N) - 1) E` at every point. -/
theorem weightedCenteredSawtoothSum_sq_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (k : ℕ) :
    weightedCenteredSawtoothSum N c k ^ 2 ≤
      ((cyclotomicIncidenceOrder N : ℝ) - 1) * sievePrimitiveEnergy N c := by
  have hcard : ((primitiveRoots' N).card : ℝ) = (cyclotomicIncidenceOrder N : ℝ) - 1 := by
    rw [primitiveRoots', card_erase_of_mem (one_mem_responseRoots hN), Nat.cast_sub
      (card_pos.mpr ⟨1, one_mem_responseRoots hN⟩), card_responseRoots, Nat.cast_one]
  have hspec := weightedCenteredSawtoothSum_eq_spectral hN c k
  have habs : |weightedCenteredSawtoothSum N c k| ≤
      ∑ ζ ∈ primitiveRoots' N, ‖primitiveSpectralCoeff N c ζ‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hspec]
    refine (norm_sum_le _ _).trans (sum_le_sum fun ζ hζ => ?_)
    rw [norm_mul, norm_pow,
      norm_eq_one_of_mem_responseRoots (mem_of_mem_erase hζ), one_pow, mul_one]
  have hcs := sq_sum_le_card_mul_sum_sq (s := primitiveRoots' N)
    (f := fun ζ => ‖primitiveSpectralCoeff N c ζ‖)
  rw [hcard, sum_norm_sq_primitiveSpectralCoeff hN] at hcs
  calc weightedCenteredSawtoothSum N c k ^ 2 = |weightedCenteredSawtoothSum N c k| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (∑ ζ ∈ primitiveRoots' N, ‖primitiveSpectralCoeff N c ζ‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := hcs

/-! ## §5. The prefix discrepancy -/

/-- The prefix discrepancy is the canonical primitive shifted by its value at the origin. -/
theorem sievePrefixDiscrepancy_eq_sub (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c =
      weightedCenteredSawtoothSum N c M - weightedCenteredSawtoothSum N c 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h1 := sievePrefixDiscrepancy_succ_sub N M c
    have h2 := weightedCenteredSawtoothSum_succ_sub_eq N c M
    rw [← sieveSeq_eq_sievedDivisorSum N c (by omega : 1 ≤ M + 1)] at h1
    rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum] at h2
    linarith

/-- **Window energy of the prefix discrepancy at quadratic order.** With `m = -W(0)` the period mean
of the prefix discrepancy, `|Σ_W (L_N(M, c) - m)² - K E| ≤ (2N² - 1) E` at every phase. -/
theorem abs_window_sum_sq_sievePrefixDiscrepancy_sub_le {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (A K : ℕ) :
    |∑ M ∈ Icc (A + 1) (A + K),
        (sievePrefixDiscrepancy N M c + weightedCenteredSawtoothSum N c 0) ^ 2 -
        K * sievePrimitiveEnergy N c| ≤ (2 * (N : ℝ) ^ 2 - 1) * sievePrimitiveEnergy N c := by
  simp only [sievePrefixDiscrepancy_eq_sub, sub_add_cancel]
  exact abs_window_sum_sq_weightedCenteredSawtoothSum_sub_le hN c A K

end

end GaloisForLFunctions.BezoutValuationIncidence
