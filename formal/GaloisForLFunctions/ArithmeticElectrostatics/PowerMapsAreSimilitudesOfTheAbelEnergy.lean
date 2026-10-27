import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# Power maps are similitudes of the Abel energy

The regularized (Abel) energy of two torsion groups `μ_A`, `μ_B` of the circle,
`T_r(A, B) = Σ_{ζ^A = 1} Σ_{η^B = 1} −log |1 − r ζ η̄|`, `0 ≤ r < 1`, is a positive Hermitian structure
on torsion cycles. This file computes it and the action of the Hecke correspondences on it.

* **Closed form** (`fullTorsionEnergy_eq`): `T_r(A, B) = gcd(A, B) · log(1/(1 − r^{lcm(A, B)}))`.
  The Fourier coefficients of `μ_A` are `A [A ∣ k]` (orthogonality), so only the multiples of
  `lcm(A, B)` survive in `Σ_k r^k/k · Re(Ŝ_A(k) conj Ŝ_B(k))`.
* **Positivity** (`sum_sum_fullTorsionEnergy_nonneg`): the matrix
  `gcd(A, B) log(1/(1 − r^{lcm(A, B)}))` is positive semidefinite on every finite set of orders.
* **Similitude** (`fullTorsionEnergy_mul`): pulling back by the power map `z ↦ z^t` (which sends
  `μ_{At}` onto `μ_A`) multiplies the energy by the degree `t` and changes the regularization
  `r ↦ r^t`: `T_r(At, Bt) = t · T_{r^t}(A, B)`. With `r = e^{−ε}`, the cutoff is rescaled by the
  degree — the archimedean flow acting on the regularization.
* **Renormalized limit** (`tendsto_fullTorsionEnergy_sub_log`): removing the self-energy
  `gcd(A, B) log(1/(1 − r))` of the `gcd(A, B)` common points and letting `r → 1` leaves
  `−gcd(A, B) log lcm(A, B) = −J(A, B)`, minus the logarithmic energy of `μ_A` against `μ_B`.
* **Adjunction** (`logEnergy_mul`): `J(At, Bt) = t (J(A, B) + gcd(A, B) log t)`: the similitude
  shifts the counterterm by `log t` per common point.

So on the circle the Hecke correspondences are computed similitudes of a positive Hermitian
structure, exactly up to the rescaling of the cutoff, and the adjunction term is the shift of the
self-energy under that rescaling. The structure Weil's argument needs over `𝔽_q` — positivity
with the Frobenius a similitude — exists on the base, regularized; its renormalized limit is the
torsion intersection theory, where positivity survives only with the counterterm.
-/

noncomputable section

open Finset Filter Complex
open scoped Topology ComplexConjugate

namespace GaloisForLFunctions.ArithmeticElectrostatics

open GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The **Abel energy** of `μ_A` against `μ_B`. -/
def fullTorsionEnergy (r : ℝ) (A B : ℕ) : ℝ :=
  ∑ ζ ∈ Polynomial.nthRootsFinset A (1 : ℂ), ∑ η ∈ Polynomial.nthRootsFinset B (1 : ℂ),
    -Real.log ‖1 - (r : ℂ) * (ζ * conj η)‖

/-- The Fourier coefficient `Ŝ_A(k) = Σ_{ζ^A = 1} ζ^k`. -/
def torsionCoeff (A k : ℕ) : ℂ := ∑ ζ ∈ Polynomial.nthRootsFinset A (1 : ℂ), ζ ^ k

/-- `T_r(A, B) = Σ_k (r^k/k) Re(Ŝ_A(k) conj Ŝ_B(k))`. -/
theorem hasSum_fullTorsionEnergy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {A B : ℕ} (hA : 0 < A)
    (hB : 0 < B) :
    HasSum (fun k : ℕ => r ^ k / k * (torsionCoeff A k * conj (torsionCoeff B k)).re)
      (fullTorsionEnergy r A B) := by
  have h := hasSum_sum fun ζ (hζ : ζ ∈ Polynomial.nthRootsFinset A (1 : ℂ)) => hasSum_sum
    fun η (hη : η ∈ Polynomial.nthRootsFinset B (1 : ℂ)) => hasSum_neg_log_norm_one_sub hr0 hr1
      (w := ζ * conj η) (by
        rw [norm_mul, Complex.norm_conj, norm_eq_one_of_mem_nthRoots hA hζ,
          norm_eq_one_of_mem_nthRoots hB hη, one_mul])
  rw [fullTorsionEnergy]
  convert h using 1
  funext k
  rw [torsionCoeff, torsionCoeff, map_sum, sum_mul_sum, Complex.re_sum, mul_sum]
  refine sum_congr rfl fun ζ _ => ?_
  rw [Complex.re_sum, mul_sum]
  refine sum_congr rfl fun η _ => ?_
  rw [mul_pow, map_pow]

/-- The coefficient product is `AB` on the multiples of `lcm(A, B)` and `0` elsewhere. -/
theorem torsionCoeff_mul_conj_re {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (k : ℕ) :
    (torsionCoeff A k * conj (torsionCoeff B k)).re =
      if Nat.lcm A B ∣ k then (A : ℝ) * B else 0 := by
  rw [torsionCoeff, torsionCoeff, sum_nthRoots_pow hA, sum_nthRoots_pow hB]
  by_cases h : Nat.lcm A B ∣ k
  · obtain ⟨hAk, hBk⟩ := Nat.lcm_dvd_iff.mp h
    rw [if_pos hAk, if_pos hBk, if_pos h, Complex.conj_natCast, ← Nat.cast_mul,
      Complex.natCast_re, Nat.cast_mul]
  · rw [if_neg h]
    by_cases hAk : A ∣ k
    · have hBk : ¬ B ∣ k := fun hBk => h (Nat.lcm_dvd_iff.mpr ⟨hAk, hBk⟩)
      rw [if_neg hBk]; simp
    · rw [if_neg hAk]; simp

/-- `Σ_{L ∣ k} r^k/k = (1/L) log(1/(1 − r^L))`. -/
theorem hasSum_multiples {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {L : ℕ} (hL : 0 < L) :
    HasSum (fun k : ℕ => if L ∣ k then r ^ k / k else 0)
      ((1 / L) * -Real.log (1 - r ^ L)) := by
  have hrL : |r ^ L| < 1 := by
    rw [abs_of_nonneg (pow_nonneg hr0 L)]; exact pow_lt_one₀ hr0 hr1 hL.ne'
  -- the logarithmic series `Σ_{j ≥ 0} x^j/j`, whose `j = 0` term is `0`
  have hlog : HasSum (fun j : ℕ => (r ^ L) ^ j / j) (-Real.log (1 - r ^ L)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [Nat.cast_add, Nat.cast_one] using Real.hasSum_pow_div_log_of_abs_lt_one hrL
  have hinj : Function.Injective fun j : ℕ => L * j := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hL h
  rw [← hinj.hasSum_iff fun k hk => by
    rw [if_neg]; rintro ⟨j, rfl⟩; exact hk ⟨j, rfl⟩]
  convert hlog.mul_left (1 / (L : ℝ)) using 1
  funext j
  simp only [Function.comp, dvd_mul_right, if_true, Nat.cast_mul, pow_mul]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    field_simp

/-- **Closed form**: `T_r(A, B) = gcd(A, B) · log(1/(1 − r^{lcm(A, B)}))`. -/
theorem fullTorsionEnergy_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {A B : ℕ} (hA : 0 < A)
    (hB : 0 < B) :
    fullTorsionEnergy r A B = Nat.gcd A B * -Real.log (1 - r ^ Nat.lcm A B) := by
  have hL : 0 < Nat.lcm A B := Nat.lcm_pos hA hB
  have h1 := hasSum_fullTorsionEnergy hr0 hr1 hA hB
  have h2 := (hasSum_multiples hr0 hr1 hL).mul_left ((A : ℝ) * B)
  have hfun : (fun k : ℕ => r ^ k / k * (torsionCoeff A k * conj (torsionCoeff B k)).re) =
      fun k => (A : ℝ) * B * (if Nat.lcm A B ∣ k then r ^ k / k else 0) := by
    funext k
    rw [torsionCoeff_mul_conj_re hA hB]
    split_ifs <;> ring
  rw [hfun] at h1
  rw [h1.unique h2]
  have hgl : (Nat.gcd A B : ℝ) * Nat.lcm A B = A * B := by exact_mod_cast Nat.gcd_mul_lcm A B
  have hL0 : (Nat.lcm A B : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [← hgl]
  field_simp

/-- **Positivity**: the Abel–gcd matrix `gcd(A, B) log(1/(1 − r^{lcm(A, B)}))` is positive
semidefinite on every finite set of orders. -/
theorem sum_sum_fullTorsionEnergy_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (x : ℕ → ℝ) :
    0 ≤ ∑ A ∈ S, ∑ B ∈ S, x A * x B * fullTorsionEnergy r A B := by
  have h := hasSum_sum fun A (hA : A ∈ S) => hasSum_sum fun B (hB : B ∈ S) =>
    (hasSum_fullTorsionEnergy hr0 hr1 (hS A hA) (hS B hB)).mul_left (x A * x B)
  refine h.nonneg fun k => ?_
  have hsq : ∑ A ∈ S, ∑ B ∈ S,
      x A * x B * (r ^ k / k * (torsionCoeff A k * conj (torsionCoeff B k)).re) =
      r ^ k / k * Complex.normSq (∑ A ∈ S, (x A : ℂ) * torsionCoeff A k) := by
    rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, sum_mul_sum,
      Complex.re_sum, mul_sum]
    refine sum_congr rfl fun A _ => ?_
    rw [Complex.re_sum, mul_sum]
    refine sum_congr rfl fun B _ => ?_
    rw [map_mul, Complex.conj_ofReal, show (x A : ℂ) * torsionCoeff A k *
      ((x B : ℂ) * conj (torsionCoeff B k)) = ((x A * x B : ℝ) : ℂ) *
        (torsionCoeff A k * conj (torsionCoeff B k)) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  rw [hsq]
  exact mul_nonneg (div_nonneg (pow_nonneg hr0 k) (Nat.cast_nonneg k)) (Complex.normSq_nonneg _)

/-- **Power maps are similitudes**: `T_r(At, Bt) = t · T_{r^t}(A, B)`. -/
theorem fullTorsionEnergy_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {A B t : ℕ} (hA : 0 < A)
    (hB : 0 < B) (ht : 0 < t) :
    fullTorsionEnergy r (A * t) (B * t) = t * fullTorsionEnergy (r ^ t) A B := by
  have hrt1 : r ^ t < 1 := pow_lt_one₀ hr0 hr1 ht.ne'
  rw [fullTorsionEnergy_eq hr0 hr1 (Nat.mul_pos hA ht) (Nat.mul_pos hB ht),
    fullTorsionEnergy_eq (pow_nonneg hr0 t) hrt1 hA hB, Nat.gcd_mul_right, Nat.lcm_mul_right,
    ← pow_mul, mul_comm (Nat.lcm A B) t]
  push_cast
  ring

/-- **The renormalized limit**: removing the self-energy of the `gcd(A, B)` common points,
`T_r(A, B) − gcd(A, B) log(1/(1 − r)) → −gcd(A, B) log lcm(A, B) = −J(A, B)` as `r → 1⁻`. -/
theorem tendsto_fullTorsionEnergy_sub_log {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun r : ℝ => fullTorsionEnergy r A B - Nat.gcd A B * -Real.log (1 - r))
      (𝓝[<] 1) (𝓝 (-logEnergy A B)) := by
  set L := Nat.lcm A B
  have hL : 0 < L := Nat.lcm_pos hA hB
  -- `1 − r^L = (1 − r) Σ_{i < L} r^i`
  have hgeom : Tendsto (fun r : ℝ => ∑ i ∈ range L, r ^ i) (𝓝[<] 1) (𝓝 (L : ℝ)) := by
    have hc : Continuous fun r : ℝ => ∑ i ∈ range L, r ^ i := by fun_prop
    have := hc.tendsto 1
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun r : ℝ => (Nat.gcd A B : ℝ) * -Real.log (∑ i ∈ range L, r ^ i))
      (𝓝[<] 1) (𝓝 ((Nat.gcd A B : ℝ) * -Real.log L)) :=
    ((Real.continuousAt_log (by exact_mod_cast hL.ne')).tendsto.comp hgeom).neg.const_mul _
  rw [logEnergy_eq hA hB, show -((Nat.gcd A B : ℝ) * Real.log (Nat.lcm A B)) =
    (Nat.gcd A B : ℝ) * -Real.log L by ring]
  refine hlim.congr' ?_
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 := by
    have h1 : ∀ᶠ r in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r :=
      (eventually_ge_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, h2] with r hr1 hr0 using ⟨hr0, hr1⟩
  filter_upwards [hev] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  rw [fullTorsionEnergy_eq hr0 hr1 hA hB]
  have h1r : 0 < 1 - r := by linarith
  have hsum : 0 < ∑ i ∈ range L, r ^ i := by
    have := single_le_sum (f := fun i => r ^ i) (fun i _ => pow_nonneg hr0 i) (mem_range.mpr hL)
    simp only [pow_zero] at this
    linarith
  have hfac : 1 - r ^ L = (1 - r) * ∑ i ∈ range L, r ^ i := by
    have := geom_sum_mul r L
    linarith
  rw [hfac, Real.log_mul h1r.ne' hsum.ne']
  ring

/-- **Adjunction for full torsion**: `J(At, Bt) = t (J(A, B) + gcd(A, B) log t)`. -/
theorem logEnergy_mul {A B t : ℕ} (hA : 0 < A) (hB : 0 < B) (ht : 0 < t) :
    logEnergy (A * t) (B * t) = t * (logEnergy A B + Nat.gcd A B * Real.log t) := by
  rw [logEnergy_eq (Nat.mul_pos hA ht) (Nat.mul_pos hB ht), logEnergy_eq hA hB,
    Nat.gcd_mul_right, Nat.lcm_mul_right, Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (Nat.lcm_pos hA hB).ne') (by exact_mod_cast ht.ne')]
  ring

end GaloisForLFunctions.ArithmeticElectrostatics
