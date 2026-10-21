import GaloisForLFunctions.BezoutValuationIncidence.KuzminLandauGainForFlatSmallScaleRows

/-!
# A discrete Gallagher inequality and the window spectrum of a row

Every frequency of a row lives on the `M`-th roots of unity `μ_M` for one modulus `M` (`M = N!`
for rows supported on `[1, N]`), so Gallagher's lemma has an exact finite form. For `T ⊆ μ_M`,
coefficients `a`, an arc length `L ≥ 1` and a window length `K` with `4KL ≤ M`, put
`ω = e^{2πi/M}` and the arc sums

`G(ξ) = Σ_{y < L} 1_T(ξωʸ) a(ξωʸ) (ξωʸ)^A`,  `ξ ∈ μ_M`.

Then `Σ_ξ G(ξ) ξʲ = D(j) Σ_{ζ ∈ T} a(ζ) ζ^{A+j}` with the Dirichlet kernel `D(j) = Σ_{y<L} ω^{-yj}`.
For `j < K` its real part is at least `L(1 - π²/24) ≥ L/2`. Parseval on `μ_M` gives

`Σ_{j < K} |Σ_{ζ ∈ T} a(ζ) ζ^{A+j}|² ≤ (4M/L²) Σ_{ξ ∈ μ_M} |G(ξ)|²`.

This is a Riemann sum for Gallagher's `(πK)² ∫ |Σ_{θ_ζ ∈ [x, x+1/(4K)]} a(ζ) e(Aθ_ζ)|² dx`.

Applied to the canonical primitive `F_c(M) = Σ_{ζ ≠ 1} Y_c(ord ζ) ζ/(ζ - 1) ζᴹ` of a row, the window
energy of the receiver on `[X, X+K)` is at most `4M/(L²X²)` times the energy of the twisted arc
clusters `Σ_{ζ ∈ arc} Y_c(ord ζ) ζ/(ζ - 1) ζ^X` of the Selberg spectrum, at resolution `L/M ≍ 1/K`.
The window energy below the quadratic horizon is governed by how the Farey spectrum of the row
clusters at scale `1/X`. The coherent blocks of the Type-II no-go are exactly such clusters.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The Dirichlet kernel near the origin -/

theorem sum_range_cast_sq_le (N : ℕ) : ∑ y ∈ range N, (y : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 / 3 := by
  rw [sum_range_cast_sq_eq]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; norm_num
  · have hN : (1 : ℝ) ≤ N := by exact_mod_cast h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : (0 : ℝ) ≤ 3 * N - 1)]

/-- `Re Σ_{y < L} ω^{-yj} ≥ L/2` when `4 j L ≤ M`. -/
theorem half_le_re_sum_range_inv_pow {M L j : ℕ} (hM : 0 < M) (hjL : 4 * j * L ≤ M) :
    (L : ℝ) / 2 ≤ (∑ y ∈ range L, ((stdRoot M ^ y)⁻¹) ^ j).re := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hre : ∀ y : ℕ, (((stdRoot M ^ y)⁻¹) ^ j).re = Real.cos (2 * Real.pi * (y * j : ℕ) / M) := by
    intro y
    have hn : ‖stdRoot M ^ (y * j)‖ = 1 := by
      rw [stdRoot_pow, mul_comm, Complex.norm_exp_ofReal_mul_I]
    rw [inv_pow, ← pow_mul, Complex.inv_eq_conj hn, Complex.conj_re, re_stdRoot_pow]
  rw [Complex.re_sum]
  simp_rw [hre]
  have hcos : ∀ y ∈ range L, 1 - (2 * Real.pi * (y * j : ℕ) / M) ^ 2 / 2 ≤
      Real.cos (2 * Real.pi * (y * j : ℕ) / M) := fun y _ => Real.one_sub_sq_div_two_le_cos
  refine le_trans ?_ (sum_le_sum hcos)
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  have hsq : ∑ y ∈ range L, (2 * Real.pi * (y * j : ℕ) / M) ^ 2 / 2 =
      2 * Real.pi ^ 2 * (j : ℝ) ^ 2 / (M : ℝ) ^ 2 * ∑ y ∈ range L, (y : ℝ) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    push_cast
    field_simp
  rw [hsq]
  have hy := sum_range_cast_sq_le L
  have hjLR : 4 * (j : ℝ) * L ≤ M := by exact_mod_cast hjL
  have hpi : Real.pi ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  -- `2π² j² L³/(3M²) ≤ π² L/24 ≤ L/2`
  have hkey : 2 * Real.pi ^ 2 * (j : ℝ) ^ 2 / (M : ℝ) ^ 2 * ((L : ℝ) ^ 3 / 3) ≤ (L : ℝ) / 2 := by
    have h1 : ((j : ℝ) * L) ^ 2 ≤ ((M : ℝ) / 4) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 * L)
    have h3 : Real.pi ^ 2 * L * ((M : ℝ) / 4) ^ 2 ≤ 12 * L * ((M : ℝ) / 4) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpi.le hL0) (by positivity)
    calc 2 * Real.pi ^ 2 * (j : ℝ) ^ 2 / (M : ℝ) ^ 2 * ((L : ℝ) ^ 3 / 3)
        = 4 / 3 * (Real.pi ^ 2 * L * ((j : ℝ) * L) ^ 2) / (M : ℝ) ^ 2 / 2 := by ring
      _ ≤ 4 / 3 * (12 * L * ((M : ℝ) / 4) ^ 2) / (M : ℝ) ^ 2 / 2 := by gcongr
      _ = (L : ℝ) / 2 := by field_simp; ring
  have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * (j : ℝ) ^ 2 /
    (M : ℝ) ^ 2)
  linarith

/-! ## §2. The discrete Gallagher inequality -/

/-- **Discrete Gallagher inequality.** For `T ⊆ μ_M`, `1 ≤ L`, `4KL ≤ M`:
`Σ_{j<K} |Σ_{ζ ∈ T} a(ζ) ζ^{A+j}|² ≤ (4M/L²) Σ_{ξ ∈ μ_M} |Σ_{y<L} 1_T(ξωʸ) a(ξωʸ) (ξωʸ)^A|²`. -/
theorem discrete_gallagher {M L K A : ℕ} (hM : 0 < M) (hL : 1 ≤ L) (hKL : 4 * K * L ≤ M)
    {T : Finset ℂ} (hT : ∀ ζ ∈ T, ζ ^ M = 1) (a : ℂ → ℂ) :
    ∑ j ∈ range K, ‖∑ ζ ∈ T, a ζ * ζ ^ (A + j)‖ ^ 2 ≤
      4 * M / (L : ℝ) ^ 2 * ∑ ξ ∈ Polynomial.nthRootsFinset M (1 : ℂ),
        ‖∑ y ∈ range L, (if ξ * stdRoot M ^ y ∈ T then
          a (ξ * stdRoot M ^ y) * (ξ * stdRoot M ^ y) ^ A else 0)‖ ^ 2 := by
  classical
  set U := Polynomial.nthRootsFinset M (1 : ℂ)
  set ω := stdRoot M
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM.ne'
  have hU : ∀ z, z ∈ U ↔ z ^ M = 1 := fun z => Polynomial.mem_nthRootsFinset hM 1
  have hTU : T ⊆ U := fun ζ hζ => (hU ζ).mpr (hT ζ hζ)
  set A' : ℂ → ℂ := fun z => if z ∈ T then a z * z ^ A else 0
  set G : ℂ → ℂ := fun ξ => ∑ y ∈ range L, A' (ξ * ω ^ y)
  set f : ℕ → ℂ := fun j => ∑ z ∈ U, A' z * z ^ j
  set D : ℕ → ℂ := fun j => ∑ y ∈ range L, ((ω ^ y)⁻¹) ^ j
  have hf : ∀ j, f j = ∑ ζ ∈ T, a ζ * ζ ^ (A + j) := by
    intro j
    simp only [f, A']
    rw [← sum_subset hTU fun z _ hz => by simp [hz]]
    refine sum_congr rfl fun z hz => ?_
    rw [if_pos hz, pow_add]
    ring
  have hωy : ∀ y, ω ^ y ∈ U := fun y => (hU _).mpr (by rw [← pow_mul, mul_comm, pow_mul,
    hω.pow_eq_one, one_pow])
  have hne : ∀ y, ω ^ y ≠ 0 := fun y => pow_ne_zero _ (hω.ne_zero hM.ne')
  -- the arc sums transform to the kernel times the window sum
  have hGtrans : ∀ j, ∑ ξ ∈ U, G ξ * ξ ^ j = D j * f j := by
    intro j
    simp only [G, D, f, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]
    refine sum_nbij' (fun ξ => ξ * ω ^ y) (fun z => z * (ω ^ y)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro ξ hξ
      exact (hU _).mpr (by rw [mul_pow, (hU ξ).mp hξ, (hU _).mp (hωy y), one_mul])
    · intro z hz
      exact (hU _).mpr (by rw [mul_pow, inv_pow, (hU z).mp hz, (hU _).mp (hωy y), inv_one,
        one_mul])
    · intro ξ _
      rw [mul_assoc, mul_inv_cancel₀ (hne y), mul_one]
    · intro z _
      rw [mul_assoc, inv_mul_cancel₀ (hne y), mul_one]
    · intro ξ _
      have h0 : (ω ^ y) ^ j ≠ 0 := pow_ne_zero _ (hne y)
      rw [mul_pow, inv_pow]
      field_simp
  -- Parseval on `μ_M`
  have hpars := sum_range_norm_sq_sum_mul_pow (P := M) (T := U) (fun z hz => (hU z).mp hz) hM G
  have hK : K ≤ M := by nlinarith
  have hlow : ∀ j ∈ range K, (L : ℝ) / 2 ≤ ‖D j‖ := by
    intro j hj
    have hjK := mem_range.mp hj
    have h := half_le_re_sum_range_inv_pow hM (j := j) (L := L)
      (le_trans (by nlinarith) hKL)
    exact h.trans (Complex.re_le_norm _)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  calc ∑ j ∈ range K, ‖∑ ζ ∈ T, a ζ * ζ ^ (A + j)‖ ^ 2
      = ∑ j ∈ range K, ‖f j‖ ^ 2 := sum_congr rfl fun j _ => by rw [hf]
    _ ≤ ∑ j ∈ range K, (4 / (L : ℝ) ^ 2) * ‖D j * f j‖ ^ 2 := by
        refine sum_le_sum fun j hj => ?_
        rw [norm_mul, mul_pow]
        have h := hlow j hj
        have hsq : ((L : ℝ) / 2) ^ 2 ≤ ‖D j‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
        rw [div_pow] at hsq
        calc ‖f j‖ ^ 2 = 4 / (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 / 2 ^ 2 * ‖f j‖ ^ 2) := by
              field_simp; norm_num
          _ ≤ 4 / (L : ℝ) ^ 2 * (‖D j‖ ^ 2 * ‖f j‖ ^ 2) := by gcongr
    _ = (4 / (L : ℝ) ^ 2) * ∑ j ∈ range K, ‖∑ ξ ∈ U, G ξ * ξ ^ j‖ ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [hGtrans]
    _ ≤ (4 / (L : ℝ) ^ 2) * ∑ j ∈ range M, ‖∑ ξ ∈ U, G ξ * ξ ^ j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hK)
          fun _ _ _ => by positivity) (by positivity)
    _ = 4 * M / (L : ℝ) ^ 2 * ∑ ξ ∈ U, ‖G ξ‖ ^ 2 := by rw [hpars]; ring

/-! ## §3. The window spectrum of a row -/

/-- **Window energy through Gallagher.** For every row `c` on `[1, N]`, `1 ≤ X`, `1 ≤ L`,
`4KL ≤ N!`, with `ω = e^{2πi/N!}` and `κ(ζ) = Y_c(ord ζ) ζ/(ζ - 1)`:
`Σ_{X ≤ M < X+K} F_c(M)²/(M(M+1)) ≤ (4 N!/(L² X²)) Σ_{ξ ∈ μ_{N!}} |Σ_{y<L} 1(ξωʸ ≠ 1) κ(ξωʸ)(ξωʸ)^X|²`. -/
theorem window_energy_le_gallagher {N X K L : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (hL : 1 ≤ L)
    (hKL : 4 * K * L ≤ N.factorial) (c : ℕ → ℝ) :
    ∑ j ∈ range K, rowFluct N c (X + j) ^ 2 / (pronicSeq (X + j) : ℝ) ≤
      4 * N.factorial / ((L : ℝ) ^ 2 * (X : ℝ) ^ 2) *
        ∑ ξ ∈ Polynomial.nthRootsFinset N.factorial (1 : ℂ),
          ‖∑ y ∈ range L, (if ξ * stdRoot N.factorial ^ y ∈ primitiveRoots' N then
            primitiveSpectralCoeff N c (ξ * stdRoot N.factorial ^ y) *
              (ξ * stdRoot N.factorial ^ y) ^ X else 0)‖ ^ 2 := by
  have hM : 0 < N.factorial := Nat.factorial_pos N
  have hT : ∀ ζ ∈ primitiveRoots' N, ζ ^ N.factorial = 1 := fun ζ hζ =>
    pow_factorial_eq_one_of_mem_responseRoots (mem_of_mem_erase hζ)
  have hgal := discrete_gallagher (A := X) hM hL hKL hT (primitiveSpectralCoeff N c)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hterm : ∀ j ∈ range K, rowFluct N c (X + j) ^ 2 / (pronicSeq (X + j) : ℝ) ≤
      1 / (X : ℝ) ^ 2 * ‖∑ ζ ∈ primitiveRoots' N, primitiveSpectralCoeff N c ζ * ζ ^ (X + j)‖ ^ 2 := by
    intro j _
    have hspec : (rowFluct N c (X + j) : ℂ) =
        ∑ ζ ∈ primitiveRoots' N, primitiveSpectralCoeff N c ζ * ζ ^ (X + j) := by
      rw [rowFluct_eq_weightedCenteredSawtoothSum, weightedCenteredSawtoothSum_eq_spectral hN]
    rw [← hspec, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_eq_mul_one_div, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hp : (X : ℝ) ^ 2 ≤ (pronicSeq (X + j) : ℝ) := by
      rw [pronicSeq]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) j]
    exact one_div_le_one_div_of_le (by positivity) hp
  calc ∑ j ∈ range K, rowFluct N c (X + j) ^ 2 / (pronicSeq (X + j) : ℝ)
      ≤ ∑ j ∈ range K, 1 / (X : ℝ) ^ 2 *
          ‖∑ ζ ∈ primitiveRoots' N, primitiveSpectralCoeff N c ζ * ζ ^ (X + j)‖ ^ 2 :=
        sum_le_sum hterm
    _ = 1 / (X : ℝ) ^ 2 *
          ∑ j ∈ range K, ‖∑ ζ ∈ primitiveRoots' N, primitiveSpectralCoeff N c ζ * ζ ^ (X + j)‖ ^ 2 := by
        rw [mul_sum]
    _ ≤ 1 / (X : ℝ) ^ 2 * (4 * N.factorial / (L : ℝ) ^ 2 *
          ∑ ξ ∈ Polynomial.nthRootsFinset N.factorial (1 : ℂ),
            ‖∑ y ∈ range L, (if ξ * stdRoot N.factorial ^ y ∈ primitiveRoots' N then
              primitiveSpectralCoeff N c (ξ * stdRoot N.factorial ^ y) *
                (ξ * stdRoot N.factorial ^ y) ^ X else 0)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hgal (by positivity)
    _ = _ := by field_simp

end

end GaloisForLFunctions.BezoutValuationIncidence
