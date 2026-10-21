import GaloisForLFunctions.BezoutValuationIncidence.BlockEquidistributionSufficesForCrossScaleDispersion

/-!
# The short-window mean square carries the cross-scale loss

For a weighted large-scale row `x(n) = c'(n)/n²` with generating polynomial `X(z) = Σ_n x(n) zⁿ`, let
`x̄ = x ⋆ 𝟙_{[0,H)}/H` be its average over windows of length `H`. Then exactly

`X̄(z) = B_H(z) X(z)`,  `B_H(z) = (1/H) Σ_{i<H} zⁱ`,

with `B_H(1) = 1`, `|B_H| ≤ 1` and `|1 - B_H(ζ)| ≤ H |ζ - 1|` on the unit circle. In the Fourier form
`Σ_n x(n) Φ_p(kn) = Σ_{η ∈ T_p} |η - 1|^{-2} X(η^k)` the averaged part `x̄` takes the full weight
`Σ_η |η - 1|^{-4} ≤ p⁴/64`, while the difference `x - x̄` has multiplier `1 - B_H(η^k)`, so its weight is
`Σ_η |η - 1|^{-4} min(2, Hk|η - 1|)² ≤ 2Hk Σ_η |η - 1|^{-3} ≤ Hk p³/8`; the classes `p ∣ k` cancel
because `x̄` and `x` have the same mass. Powering by `k` permutes the nontrivial `p`-th roots for
`p ∤ k`, so for every prime `p`

`|Σ_n x(n) 𝔅(p, n)| ≤ (π²/48) p² ‖X̄‖_p + |Σ_n x(n)|/6 + √(2Hp³) ‖X‖_p`,

`‖X‖_p² = Σ_{ζ ∈ T_p} |X(ζ)|²`. The log-free large sieve over the primes of the small scale gives, for
`c` on primes `≤ Q₀` and `c'` on `[A+1, A+L]`,

`|B + m R' + β H'| ≤ (π²/48) √(Σ c(p)² p²) √(L + H + 2Q₀²) ‖x̄‖₂
  + √(2H) √(Σ c(p)² p) √(L + 2Q₀²) ‖x‖₂ + |Σ_n x(n)| Σ_p |c(p)|/(6p) + ¾ Σ |c| p² Σ |c'|/n³`.

Against the large-sieve bound `½ √(Σ c(p)² p²) √(L + 2Q₀²) ‖x‖₂`, which coherent large-scale rows
attain, the loss splits into the normalized short-window mean square `‖x̄‖₂/‖x‖₂` and the factor
`√(H/P)` for `c` on `(P, 2P]`. A large-scale row that cancels in almost all windows of a length
`H = o(P)` therefore beats the Type-II barrier at every cross-scale exponent.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The short-window average and its multiplier -/

/-- The average of a row over the window of length `H` ending at `n`. -/
def shortWindowAverage (H : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ range H, x (n - i)) / H

/-- The generating polynomial `X(z) = Σ_{1 ≤ n ≤ N} x(n) zⁿ` of a row. -/
def rowPoly (N : ℕ) (x : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (x n : ℂ) * z ^ n

/-- The box multiplier `B_H(z) = (1/H) Σ_{i < H} zⁱ`. -/
def boxMultiplier (H : ℕ) (z : ℂ) : ℂ :=
  (∑ i ∈ range H, z ^ i) / H

theorem rowPoly_sub (N : ℕ) (x y : ℕ → ℝ) (z : ℂ) :
    rowPoly N (fun n => x n - y n) z = rowPoly N x z - rowPoly N y z := by
  simp only [rowPoly, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- A shift of the row by `i` multiplies its polynomial by `zⁱ`. -/
theorem sum_Icc_sub_mul_pow {N i : ℕ} {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hsupp : ∀ n, x n ≠ 0 → n + i ≤ N) (z : ℂ) :
    ∑ n ∈ Icc 1 N, (x (n - i) : ℂ) * z ^ n = z ^ i * rowPoly N x z := by
  rw [rowPoly, mul_sum]
  symm
  refine sum_bij_ne_zero (fun m _ _ => m + i) (fun m hm h => ?_) (fun _ _ _ _ _ _ h => by omega)
    (fun n hn h => ?_) (fun m _ _ => ?_)
  · have hx : x m ≠ 0 := fun h0 => h (by rw [h0]; simp)
    have := hsupp m hx
    exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, this⟩
  · have hx : x (n - i) ≠ 0 := fun h0 => h (by rw [h0]; simp)
    have hni : n - i ≠ 0 := fun h0 => hx (by rw [h0, hx0])
    have hn' := mem_Icc.mp hn
    refine ⟨n - i, mem_Icc.mpr ⟨by omega, by omega⟩, fun h0 => h ?_, by omega⟩
    have hpow : z ^ n = z ^ i * z ^ (n - i) := by rw [← pow_add]; congr 1; omega
    rw [hpow]
    linear_combination h0
  · rw [Nat.add_sub_cancel]
    ring

/-- The averaged row has polynomial `B_H(z) X(z)`. -/
theorem rowPoly_shortWindowAverage {N H : ℕ} {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hsupp : ∀ n, x n ≠ 0 → n + H ≤ N + 1) (z : ℂ) :
    rowPoly N (shortWindowAverage H x) z = boxMultiplier H z * rowPoly N x z := by
  have hi : ∀ i ∈ range H, ∑ n ∈ Icc 1 N, (x (n - i) : ℂ) * z ^ n = z ^ i * rowPoly N x z :=
    fun i hi => sum_Icc_sub_mul_pow hx0 (fun n hn => by
      have h1 := hsupp n hn
      have h2 := mem_range.mp hi
      omega) z
  calc rowPoly N (shortWindowAverage H x) z
      = ∑ n ∈ Icc 1 N, ∑ i ∈ range H, (x (n - i) : ℂ) * z ^ n / H := by
        refine sum_congr rfl fun n _ => ?_
        simp only [shortWindowAverage]
        push_cast
        rw [div_mul_eq_mul_div, sum_mul, sum_div]
    _ = ∑ i ∈ range H, (∑ n ∈ Icc 1 N, (x (n - i) : ℂ) * z ^ n) / H := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => (sum_div _ _ _).symm
    _ = ∑ i ∈ range H, z ^ i * rowPoly N x z / H := sum_congr rfl fun i hi' => by rw [hi i hi']
    _ = boxMultiplier H z * rowPoly N x z := by
        rw [boxMultiplier, div_mul_eq_mul_div, sum_mul, sum_div]

theorem boxMultiplier_one {H : ℕ} (hH : 1 ≤ H) : boxMultiplier H 1 = 1 := by
  have : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [boxMultiplier, this]

theorem norm_boxMultiplier_le {H : ℕ} (hH : 1 ≤ H) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖boxMultiplier H ζ‖ ≤ 1 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  rw [boxMultiplier, norm_div, Complex.norm_natCast, div_le_one hHR]
  calc ‖∑ i ∈ range H, ζ ^ i‖ ≤ ∑ i ∈ range H, ‖ζ ^ i‖ := norm_sum_le _ _
    _ = H := by simp [norm_pow, hζ]

/-- `|1 - B_H(ζ)| ≤ H |ζ - 1|` on the unit circle. -/
theorem norm_one_sub_boxMultiplier_le {H : ℕ} (hH : 1 ≤ H) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖1 - boxMultiplier H ζ‖ ≤ H * ‖ζ - 1‖ := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHC : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : 1 - boxMultiplier H ζ = (∑ i ∈ range H, (1 - ζ ^ i)) / H := by
    rw [boxMultiplier, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
  rw [he, norm_div, Complex.norm_natCast, div_le_iff₀ hHR]
  calc ‖∑ i ∈ range H, (1 - ζ ^ i)‖ ≤ ∑ i ∈ range H, ‖1 - ζ ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range H, (H : ℝ) * ‖ζ - 1‖ := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_sub_rev]
        refine (norm_pow_sub_one_le hζ i).trans ?_
        have : (i : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hi).le
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = H * ‖ζ - 1‖ * H := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ## §2. The Fourier form for general rows -/

/-- For a prime `p` the nontrivial `p`-th roots are the primitive ones. -/
theorem nontrivialRoots_eq_primitiveRoots {p : ℕ} (hp : p.Prime) :
    nontrivialRoots p = primitiveRoots p ℂ := by
  ext η
  rw [mem_nontrivialRoots hp.pos, mem_primitiveRoots hp.pos]
  constructor
  · rintro ⟨h1, hη⟩
    haveI := Fact.mk hp
    rw [← orderOf_eq_prime hη h1]
    exact IsPrimitiveRoot.orderOf η
  · intro h
    exact ⟨h.ne_one hp.one_lt, h.pow_eq_one⟩

/-- Powering by `k` with `p ∤ k` permutes the nontrivial `p`-th roots. -/
theorem sum_nontrivialRoots_pow_eq {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k) (f : ℂ → ℝ) :
    ∑ η ∈ nontrivialRoots p, f (η ^ k) = ∑ ζ ∈ nontrivialRoots p, f ζ := by
  classical
  have hinj : Set.InjOn (fun η : ℂ => η ^ k) (nontrivialRoots p : Set ℂ) := by
    intro η hη η' hη' heq
    have hpη := ((mem_nontrivialRoots hp.pos).mp hη).2
    have hpη' := ((mem_nontrivialRoots hp.pos).mp hη').2
    have hη0 : η' ≠ 0 := fun h0 => by rw [h0, zero_pow hp.ne_zero] at hpη'; exact zero_ne_one hpη'
    have hk1 : (η * η'⁻¹) ^ k = 1 := by
      simp only at heq
      rw [mul_pow, inv_pow, heq, mul_inv_cancel₀ (pow_ne_zero _ hη0)]
    have hp1 : (η * η'⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, hpη, hpη', inv_one, mul_one]
    have hg := pow_gcd_eq_one.mpr ⟨hk1, hp1⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)),
      pow_one] at hg
    exact (mul_inv_eq_one₀ hη0).mp hg
  have himg : (nontrivialRoots p).image (fun η : ℂ => η ^ k) = nontrivialRoots p := by
    refine eq_of_subset_of_card_le (fun ζ hζ => ?_) (by rw [card_image_of_injOn hinj])
    obtain ⟨η, hη, rfl⟩ := mem_image.mp hζ
    exact pow_mem_nontrivialRoots hp hη hk
  conv_rhs => rw [← himg]
  rw [sum_image hinj]

theorem residuePotential_of_dvd {d M : ℕ} (hdM : d ∣ M) :
    residuePotential d M = ((d : ℝ) ^ 2 - 1) / 12 := by
  rw [residuePotential, Nat.mod_eq_zero_of_dvd hdM]
  simp

/-- `Σ_n y(n) Φ_d(kn) = Σ_{η ∈ T_d} |η - 1|^{-2} Y(η^k)` for every row `y`. -/
theorem sum_mul_residuePotential_eq_rowPoly {d : ℕ} (hd : 0 < d) (N k : ℕ) (y : ℕ → ℝ) :
    ((∑ n ∈ Icc 1 N, y n * residuePotential d (k * n) : ℝ) : ℂ) =
      ∑ η ∈ nontrivialRoots d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowPoly N y (η ^ k) := by
  push_cast
  simp_rw [residuePotential_eq_spectral hd, rowPoly, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun η _ => sum_congr rfl fun n _ => ?_
  rw [pow_mul]
  push_cast
  ring

/-- The averaged row keeps the mass. -/
theorem sum_shortWindowAverage {N H : ℕ} (hH : 1 ≤ H) {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hsupp : ∀ n, x n ≠ 0 → n + H ≤ N + 1) :
    ∑ n ∈ Icc 1 N, shortWindowAverage H x n = ∑ n ∈ Icc 1 N, x n := by
  have h := rowPoly_shortWindowAverage hx0 hsupp 1
  rw [boxMultiplier_one hH, one_mul] at h
  simp only [rowPoly, one_pow, mul_one] at h
  exact_mod_cast h

/-! ## §3. One modulus -/

/-- Cauchy–Schwarz over the roots, after the permutation `η ↦ η^k`. -/
theorem norm_sum_weight_mul_rowPoly_pow_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k)
    (N : ℕ) (x : ℕ → ℝ) (w : ℂ → ℝ) (m : ℂ → ℂ) :
    ‖∑ η ∈ nontrivialRoots p, (w η : ℂ) * (m (η ^ k) * rowPoly N x (η ^ k))‖ ≤
      Real.sqrt (∑ η ∈ nontrivialRoots p, (w η * ‖m (η ^ k)‖) ^ 2) *
        Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N x ζ‖ ^ 2) := by
  calc _ ≤ ∑ η ∈ nontrivialRoots p, |w η| * ‖m (η ^ k)‖ * ‖rowPoly N x (η ^ k)‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun η _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    _ ≤ Real.sqrt (∑ η ∈ nontrivialRoots p, (|w η| * ‖m (η ^ k)‖) ^ 2) *
          Real.sqrt (∑ η ∈ nontrivialRoots p, ‖rowPoly N x (η ^ k)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
        rw [sum_nontrivialRoots_pow_eq hp hk (fun ζ => ‖rowPoly N x ζ‖ ^ 2)]
        congr 2
        refine sum_congr rfl fun η _ => ?_
        rw [mul_pow, mul_pow, sq_abs]

theorem inv_norm_sq_sq_eq {η : ℂ} : ((‖η - 1‖ ^ 2)⁻¹) ^ 2 = 1 / ‖η - 1‖ ^ (2 + 2) := by
  rw [inv_pow, ← pow_mul, one_div]

/-- A full layer: `|Σ_n y(n) Φ_p(kn)| ≤ (p²/8) ‖Y‖_p` for `p ∤ k`. -/
theorem abs_sum_mul_residuePotential_le_rootEnergy {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k)
    (N : ℕ) (y : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, y n * residuePotential p (k * n)| ≤
      (p : ℝ) ^ 2 / 8 * Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N y ζ‖ ^ 2) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_residuePotential_eq_rowPoly hp.pos]
  have h := norm_sum_weight_mul_rowPoly_pow_le hp hk N y (fun η => (‖η - 1‖ ^ 2)⁻¹) (fun _ => 1)
  simp only [one_mul, norm_one, mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  rw [show (p : ℝ) ^ 2 / 8 = Real.sqrt (((p : ℝ) / 4) ^ 2 * ((p : ℝ) ^ 2 / 4)) by
    rw [show ((p : ℝ) / 4) ^ 2 * ((p : ℝ) ^ 2 / 4) = ((p : ℝ) ^ 2 / 8) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  rw [nontrivialRoots_eq_primitiveRoots hp, sum_congr rfl fun η _ => inv_norm_sq_sq_eq]
  exact sum_primitiveRoots_inv_norm_sub_one_pow_le hp.two_le 2

/-- A smoothed-away layer: if `E = (1 - B_H) X`, then `|Σ_n e(n) Φ_p(kn)| ≤ √(Hkp³/8) ‖X‖_p`. -/
theorem abs_sum_mul_residuePotential_le_boxDefect {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k)
    {N H : ℕ} (hH : 1 ≤ H) {e x : ℕ → ℝ}
    (hE : ∀ z, rowPoly N e z = (1 - boxMultiplier H z) * rowPoly N x z) :
    |∑ n ∈ Icc 1 N, e n * residuePotential p (k * n)| ≤
      Real.sqrt (H * k * (p : ℝ) ^ 3 / 8) *
        Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N x ζ‖ ^ 2) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_residuePotential_eq_rowPoly hp.pos]
  simp_rw [hE]
  refine (norm_sum_weight_mul_rowPoly_pow_le hp hk N x (fun η => (‖η - 1‖ ^ 2)⁻¹)
    (fun z => 1 - boxMultiplier H z)).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  refine Real.sqrt_le_sqrt ?_
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hkey : ∀ η ∈ nontrivialRoots p, ((‖η - 1‖ ^ 2)⁻¹ * ‖1 - boxMultiplier H (η ^ k)‖) ^ 2 ≤
      2 * H * k * (1 / ‖η - 1‖ ^ (1 + 2)) := by
    intro η hη
    have hη1 := norm_eq_one_of_mem_nontrivialRoots hp.pos hη
    have hpos : 0 < ‖η - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ((mem_nontrivialRoots hp.pos).mp hη).1)
    have hηk : ‖η ^ k‖ = 1 := by rw [norm_pow, hη1, one_pow]
    set b := ‖1 - boxMultiplier H (η ^ k)‖
    have hb0 : 0 ≤ b := norm_nonneg _
    have hb2 : b ≤ 2 := (norm_sub_le _ _).trans (by
      rw [norm_one]; linarith [norm_boxMultiplier_le hH hηk])
    have hbk : b ≤ H * k * ‖η - 1‖ := (norm_one_sub_boxMultiplier_le hH hηk).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_pow_sub_one_le hη1 k) (by positivity))
    have hbb : b ^ 2 ≤ 2 * (H * k * ‖η - 1‖) := by
      rw [sq]; exact mul_le_mul hb2 hbk hb0 (by norm_num)
    rw [mul_pow, inv_pow, ← pow_mul]
    calc (‖η - 1‖ ^ (2 * 2))⁻¹ * b ^ 2 ≤ (‖η - 1‖ ^ (2 * 2))⁻¹ * (2 * (H * k * ‖η - 1‖)) :=
          mul_le_mul_of_nonneg_left hbb (by positivity)
      _ = 2 * H * k * (1 / ‖η - 1‖ ^ (1 + 2)) := by field_simp; ring
  calc ∑ η ∈ nontrivialRoots p, ((‖η - 1‖ ^ 2)⁻¹ * ‖1 - boxMultiplier H (η ^ k)‖) ^ 2
      ≤ ∑ η ∈ nontrivialRoots p, 2 * H * k * (1 / ‖η - 1‖ ^ (1 + 2)) := sum_le_sum hkey
    _ = 2 * H * k * ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ (1 + 2) := by
        rw [← mul_sum, nontrivialRoots_eq_primitiveRoots hp]
    _ ≤ 2 * H * k * (((p : ℝ) / 4) ^ 1 * ((p : ℝ) ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le hp.two_le 1)
          (by positivity)
    _ = H * k * (p : ℝ) ^ 3 / 8 := by ring

/-- A layer with `p ∣ k` reads only the mass. -/
theorem sum_mul_residuePotential_of_dvd {p k : ℕ} (hpk : p ∣ k) (N : ℕ) (y : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, y n * residuePotential p (k * n) =
      ((p : ℝ) ^ 2 - 1) / 12 * ∑ n ∈ Icc 1 N, y n := by
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by
    rw [residuePotential_of_dvd (Dvd.dvd.mul_right hpk n)]; ring

theorem sum_range_sqrt_succ_div_sq_le (K : ℕ) :
    ∑ j ∈ range K, Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2 ≤ 4 := by
  refine le_trans (le_of_eq ?_) (sum_Icc_sqrt_div_sq_le K)
  refine sum_nbij' (· + 1) (· - 1) (fun j hj => ?_) (fun j hj => ?_) (fun j _ => ?_)
    (fun j hj => ?_) (fun j _ => ?_)
  · simp only [mem_range, mem_Icc] at hj ⊢; omega
  · simp only [mem_range, mem_Icc] at hj ⊢; omega
  · simp
  · simp only [mem_Icc] at hj; omega
  · push_cast; rfl

/-- **One modulus.** For a prime `p` and a row `x` on `[1, N + 1 - H]`,
`|Σ_n x(n) 𝔅(p, n)| ≤ (π²/48) p² ‖X̄‖_p + |Σ_n x(n)|/6 + √(2Hp³) ‖X‖_p`. -/
theorem abs_sum_mul_bernoulliKernel_le_shortWindow {p : ℕ} (hp : p.Prime) {N H : ℕ} (hH : 1 ≤ H)
    {x : ℕ → ℝ} (hx0 : x 0 = 0) (hsupp : ∀ n, x n ≠ 0 → n + H ≤ N + 1) :
    |∑ n ∈ Icc 1 N, x n * bernoulliKernel p n| ≤
      Real.pi ^ 2 / 48 * (p : ℝ) ^ 2 *
          Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N (shortWindowAverage H x) ζ‖ ^ 2) +
        |∑ n ∈ Icc 1 N, x n| / 6 +
        Real.sqrt (2 * H * (p : ℝ) ^ 3) *
          Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N x ζ‖ ^ 2) := by
  set xb := shortWindowAverage H x
  set e : ℕ → ℝ := fun n => x n - xb n
  set Eb := Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N xb ζ‖ ^ 2)
  set E := Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N x ζ‖ ^ 2)
  set m := ∑ n ∈ Icc 1 N, x n
  have hEb0 : 0 ≤ Eb := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hdef : ∀ z, rowPoly N e z = (1 - boxMultiplier H z) * rowPoly N x z := fun z => by
    rw [rowPoly_sub, rowPoly_shortWindowAverage hx0 hsupp]; ring
  have hmb : ∑ n ∈ Icc 1 N, xb n = m := sum_shortWindowAverage hH hx0 hsupp
  have hme : ∑ n ∈ Icc 1 N, e n = 0 := by
    simp only [e]; rw [sum_sub_distrib, hmb]; ring
  set t : ℕ → ℝ := fun j => ∑ n ∈ Icc 1 N, x n *
    (residuePotential p ((j + 1) * n) / ((j : ℝ) + 1) ^ 2)
  have ht : HasSum t (∑ n ∈ Icc 1 N, x n * bernoulliKernel p n) :=
    hasSum_sum fun n _ => (hasSum_bernoulliKernel hp.pos n).mul_left (x n)
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  set γ := Real.sqrt (H * (p : ℝ) ^ 3 / 8)
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  have hm0 : 0 ≤ ((p : ℝ) ^ 2 - 1) / 12 * |m| := by
    have : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  -- each layer splits into the averaged row and the smoothed-away defect
  have hlayer : ∀ j, |t j| ≤
      ((p : ℝ) ^ 2 - 1) / 12 * |m| * (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) +
        (p : ℝ) ^ 2 / 8 * Eb * (1 / ((j : ℝ) + 1) ^ 2) +
        γ * E * (Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2) := by
    intro j
    set w : ℝ := 1 / ((j : ℝ) + 1) ^ 2
    have hw : 0 ≤ w := by positivity
    have hsplit : t j = (∑ n ∈ Icc 1 N, xb n * residuePotential p ((j + 1) * n)) * w +
        (∑ n ∈ Icc 1 N, e n * residuePotential p ((j + 1) * n)) * w := by
      rw [← add_mul, ← sum_add_distrib, sum_mul]
      refine sum_congr rfl fun n _ => ?_
      simp only [e, w]
      ring
    have hsq : 0 ≤ Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2 := by positivity
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    by_cases hpj : p ∣ j + 1
    · rw [sum_mul_residuePotential_of_dvd hpj, sum_mul_residuePotential_of_dvd hpj, hmb, hme,
        mul_zero, abs_zero, zero_mul, add_zero, if_pos hpj, abs_mul,
        abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ ((p : ℝ) ^ 2 - 1) / 12)]
      have : 0 ≤ (p : ℝ) ^ 2 / 8 * Eb * w := by positivity
      have : 0 ≤ γ * E * (Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2) := by positivity
      linarith
    · rw [if_neg hpj, mul_zero, zero_add]
      have h1 := abs_sum_mul_residuePotential_le_rootEnergy hp hpj N xb
      have h2 := abs_sum_mul_residuePotential_le_boxDefect hp hpj hH hdef
      have hk : Real.sqrt (H * ((j + 1 : ℕ) : ℝ) * (p : ℝ) ^ 3 / 8) = γ * Real.sqrt ((j : ℝ) + 1) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        push_cast
        ring
      rw [hk] at h2
      have e2 : γ * Real.sqrt ((j : ℝ) + 1) * E * w =
          γ * E * (Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2) := by
        simp only [w]; ring
      calc _ ≤ (p : ℝ) ^ 2 / 8 * Eb * w + γ * Real.sqrt ((j : ℝ) + 1) * E * w :=
            add_le_add (mul_le_mul_of_nonneg_right h1 hw) (mul_le_mul_of_nonneg_right h2 hw)
        _ = _ := by rw [e2]
  have hbound : ∀ K, |∑ j ∈ range K, t j| ≤ Real.pi ^ 2 / 48 * (p : ℝ) ^ 2 * Eb + |m| / 6 +
      Real.sqrt (2 * H * (p : ℝ) ^ 3) * E := by
    intro K
    have hA := sum_range_ite_dvd_div_sq_le hp.pos K
    have hB : ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 :=
      sum_le_hasSum _ (fun j _ => by positivity) hz
    have hC := sum_range_sqrt_succ_div_sq_le K
    have hγ : Real.sqrt (2 * H * (p : ℝ) ^ 3) = 4 * γ := by
      rw [show (2 : ℝ) * H * (p : ℝ) ^ 3 = 4 ^ 2 * (H * (p : ℝ) ^ 3 / 8) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have hm6 : ((p : ℝ) ^ 2 - 1) / 12 * |m| * (2 / (p : ℝ) ^ 2) ≤ |m| / 6 := by
      have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
      rw [show ((p : ℝ) ^ 2 - 1) / 12 * |m| * (2 / (p : ℝ) ^ 2) =
          |m| / 6 * (((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2) by field_simp; ring]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [div_le_one hp2]; linarith
    calc |∑ j ∈ range K, t j| ≤ ∑ j ∈ range K, |t j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range K, (((p : ℝ) ^ 2 - 1) / 12 * |m| *
            (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) +
          (p : ℝ) ^ 2 / 8 * Eb * (1 / ((j : ℝ) + 1) ^ 2) +
          γ * E * (Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2)) := sum_le_sum fun j _ => hlayer j
      _ = ((p : ℝ) ^ 2 - 1) / 12 * |m| *
            ∑ j ∈ range K, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) +
          (p : ℝ) ^ 2 / 8 * Eb * ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 +
          γ * E * ∑ j ∈ range K, Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1) ^ 2 := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
      _ ≤ ((p : ℝ) ^ 2 - 1) / 12 * |m| * (2 / (p : ℝ) ^ 2) +
          (p : ℝ) ^ 2 / 8 * Eb * (Real.pi ^ 2 / 6) + γ * E * 4 := by
        gcongr
      _ ≤ _ := by
        rw [hγ]
        nlinarith [hm6]
  exact le_of_tendsto' ht.tendsto_sum_nat.abs hbound

/-! ## §4. The cross-scale remainder -/

/-- The polynomial of a row supported on a window is its window sum. -/
theorem rowPoly_eq_window {N A K : ℕ} (hA : A + K ≤ N) {x : ℕ → ℝ}
    (hsupp : ∀ n, x n ≠ 0 → n ∈ Icc (A + 1) (A + K)) (z : ℂ) :
    rowPoly N x z = ∑ n ∈ Icc (A + 1) (A + K), (x n : ℂ) * z ^ n := by
  rw [rowPoly]
  symm
  refine sum_subset (Icc_subset_Icc (by omega) hA) fun n _ hn => ?_
  have : x n = 0 := by by_contra h; exact hn (hsupp n h)
  simp [this]

/-- The large sieve over the nontrivial roots of the primes of `S`. -/
theorem sum_sum_norm_rowPoly_sq_le {N Q₀ A K : ℕ} {S : Finset ℕ} (hQ₀ : 2 ≤ Q₀)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Q₀) (hA : A + K ≤ N) {x : ℕ → ℝ}
    (hsupp : ∀ n, x n ≠ 0 → n ∈ Icc (A + 1) (A + K)) :
    ∑ p ∈ S, ∑ ζ ∈ nontrivialRoots p, ‖rowPoly N x ζ‖ ^ 2 ≤
      ((K : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * ∑ n ∈ Icc (A + 1) (A + K), x n ^ 2 := by
  classical
  set T := S.biUnion fun p => primitiveRoots p ℂ
  have hdisj : (S : Set ℕ).PairwiseDisjoint fun p => primitiveRoots p ℂ := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro ζ hζp hζq
    have h1 := ((mem_primitiveRoots (hS p hp).1.pos).mp hζp).eq_orderOf
    have h2 := ((mem_primitiveRoots (hS q hq).1.pos).mp hζq).eq_orderOf
    exact hpq (h1.trans h2.symm)
  have hTroots : T ⊆ responseRoots Q₀ := by
    intro ζ hζ
    obtain ⟨p, hp, hζp⟩ := mem_biUnion.mp hζ
    have hprim := (mem_primitiveRoots (hS p hp).1.pos).mp hζp
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2⟩,
      (Polynomial.mem_nthRootsFinset (hS p hp).1.pos 1).mpr hprim.pow_eq_one⟩
  have hls := largeSieve_responseRoots hQ₀ hTroots A K (fun n => (x n : ℂ))
  rw [sum_congr rfl fun p hp => by rw [nontrivialRoots_eq_primitiveRoots (hS p hp).1],
    ← sum_biUnion hdisj]
  simp_rw [rowPoly_eq_window hA hsupp]
  refine hls.trans ?_
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have : (0 : ℝ) ≤ ∑ n ∈ Icc (A + 1) (A + K), x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  nlinarith

/-- The averaged row lives on the window extended by `H`. -/
theorem shortWindowAverage_supp {A L H : ℕ} {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hsupp : ∀ n, x n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (n : ℕ) (hn : shortWindowAverage H x n ≠ 0) :
    n ∈ Icc (A + 1) (A + (L + H - 1)) := by
  rw [shortWindowAverage] at hn
  obtain ⟨i, hi, hxi⟩ := exists_ne_zero_of_sum_ne_zero (div_ne_zero_iff.mp hn).1
  have hni : n - i ≠ 0 := fun h0 => hxi (by rw [h0, hx0])
  have := mem_Icc.mp (hsupp _ hxi)
  have := mem_range.mp hi
  exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- **The short-window mean square carries the cross-scale loss.** For `c` on primes `≤ Q₀`, `c'` on
`[A+1, A+L]`, `x(n) = c'(n)/n²` and its `H`-window average `x̄`,
`|B + m R' + β H'| ≤ (π²/48) √(Σ c(p)² p²) √(L + H + 2Q₀²) ‖x̄‖₂
  + √(2H) √(Σ c(p)² p) √(L + 2Q₀²) ‖x‖₂ + |Σ_n x(n)| Σ_p |c(p)|/(6p) + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_shortWindow {N Q₀ A L H : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) {c c' : ℕ → ℝ}
    (hsupp : ∀ n, c n ≠ 0 → n ∈ S) (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L))
    (hH : 1 ≤ H) (hN : A + L + H ≤ N + 1) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      Real.pi ^ 2 / 48 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt ((L : ℝ) + H + 2 * (Q₀ : ℝ) ^ 2) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L + H),
            shortWindowAverage H (fun n => c' n / (n : ℝ) ^ 2) n ^ 2) +
        Real.sqrt (2 * H) * Real.sqrt (∑ p ∈ S, c p ^ 2 * p) *
          Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        |∑ n ∈ Icc (A + 1) (A + L), c' n / (n : ℝ) ^ 2| / 6 * ∑ p ∈ S, |c p| / p +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  classical
  set x : ℕ → ℝ := fun n => c' n / (n : ℝ) ^ 2 with hxdef
  set xb := shortWindowAverage H x
  have hx0 : x 0 = 0 := by simp [x]
  have hxsupp : ∀ n, x n ≠ 0 → n ∈ Icc (A + 1) (A + L) := fun n hn =>
    hsupp' n fun h => hn (by simp [x, h])
  have hxN : ∀ n, x n ≠ 0 → n + H ≤ N + 1 := fun n hn => by
    have := mem_Icc.mp (hxsupp n hn); omega
  have hxbsupp := shortWindowAverage_supp (H := H) hx0 hxsupp
  have hsub : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2.1⟩
  set Eb : ℕ → ℝ := fun p => Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N xb ζ‖ ^ 2)
  set E : ℕ → ℝ := fun p => Real.sqrt (∑ ζ ∈ nontrivialRoots p, ‖rowPoly N x ζ‖ ^ 2)
  set m := ∑ n ∈ Icc 1 N, x n
  have hm : m = ∑ n ∈ Icc (A + 1) (A + L), c' n / (n : ℝ) ^ 2 := by
    simp only [m]
    symm
    refine sum_subset (Icc_subset_Icc (by omega) (by omega)) fun n _ hn => ?_
    by_contra h; exact hn (hxsupp n h)
  -- the second-order law and the one-modulus bound
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set M := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  have hM : M = ∑ p ∈ S, c p / p * ∑ n ∈ Icc 1 N, x n * bernoulliKernel p n := by
    simp only [M]
    rw [sum_comm, ← sum_subset hsub fun d _ hd => by
      have : c d = 0 := by by_contra h; exact hd (hsupp d h)
      simp [this]]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by simp only [x]; ring
  have hMb : |M| ≤ Real.pi ^ 2 / 48 * ∑ p ∈ S, |c p| * p * Eb p + |m| / 6 * ∑ p ∈ S, |c p| / p +
      Real.sqrt (2 * H) * ∑ p ∈ S, |c p| * Real.sqrt p * E p := by
    rw [hM, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hpS => ?_)
    have hp := (hS p hpS).1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hk := abs_sum_mul_bernoulliKernel_le_shortWindow hp hH hx0 hxN
    rw [abs_mul, abs_div, abs_of_pos hpR]
    have hsq : Real.sqrt (2 * H * (p : ℝ) ^ 3) = Real.sqrt (2 * H) * Real.sqrt p * p := by
      rw [← Real.sqrt_mul (by positivity), show (2 * H * (p : ℝ)) = 2 * H * p from rfl,
        show 2 * (H : ℝ) * (p : ℝ) ^ 3 = 2 * H * p * p ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hpR.le]
    rw [hsq] at hk
    calc |c p| / p * |∑ n ∈ Icc 1 N, x n * bernoulliKernel p n|
        ≤ |c p| / p * (Real.pi ^ 2 / 48 * (p : ℝ) ^ 2 * Eb p + |m| / 6 +
            Real.sqrt (2 * H) * Real.sqrt p * p * E p) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by field_simp
  -- Cauchy–Schwarz over the primes and the large sieve
  have hEbsq : ∀ p, Eb p ^ 2 = ∑ ζ ∈ nontrivialRoots p, ‖rowPoly N xb ζ‖ ^ 2 := fun p =>
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hEsq : ∀ p, E p ^ 2 = ∑ ζ ∈ nontrivialRoots p, ‖rowPoly N x ζ‖ ^ 2 := fun p =>
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ Q₀ := fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩
  have hLSb := sum_sum_norm_rowPoly_sq_le (N := N) (K := L + H - 1) hQ₀ hS' (by omega) hxbsupp
  have hLS := sum_sum_norm_rowPoly_sq_le (N := N) (K := L) hQ₀ hS' (by omega) hxsupp
  have hwin : ∑ n ∈ Icc (A + 1) (A + (L + H - 1)), xb n ^ 2 ≤
      ∑ n ∈ Icc (A + 1) (A + L + H), xb n ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (by omega)) fun _ _ _ => sq_nonneg _
  have hKb : ((L + H - 1 : ℕ) : ℝ) ≤ L + H := by
    have : ((L + H - 1 : ℕ) : ℝ) ≤ ((L + H : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
    push_cast at this; exact this
  have hCb : ∑ p ∈ S, |c p| * p * Eb p ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
      (Real.sqrt ((L : ℝ) + H + 2 * (Q₀ : ℝ) ^ 2) *
        Real.sqrt (∑ n ∈ Icc (A + 1) (A + L + H), xb n ^ 2)) := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt S (fun p => |c p| * (p : ℝ)) Eb
    have e1 : ∑ p ∈ S, (|c p| * (p : ℝ)) ^ 2 = ∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2 :=
      sum_congr rfl fun p _ => by rw [mul_pow, sq_abs]
    rw [e1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [sum_congr rfl fun p _ => hEbsq p]
    refine hLSb.trans ?_
    have h0 : (0 : ℝ) ≤ ∑ n ∈ Icc (A + 1) (A + (L + H - 1)), xb n ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    calc (((L + H - 1 : ℕ) : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * ∑ n ∈ Icc (A + 1) (A + (L + H - 1)), xb n ^ 2
        ≤ ((L : ℝ) + H + 2 * (Q₀ : ℝ) ^ 2) * ∑ n ∈ Icc (A + 1) (A + (L + H - 1)), xb n ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ ≤ _ := mul_le_mul_of_nonneg_left hwin (by positivity)
  have hC : ∑ p ∈ S, |c p| * Real.sqrt p * E p ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * p) *
      (Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2) *
        Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4)) := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt S (fun p => |c p| * Real.sqrt p) E
    have e1 : ∑ p ∈ S, (|c p| * Real.sqrt p) ^ 2 = ∑ p ∈ S, c p ^ 2 * p :=
      sum_congr rfl fun p _ => by rw [mul_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [e1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [sum_congr rfl fun p _ => hEsq p]
    refine hLS.trans (le_of_eq ?_)
    congr 1
    exact sum_congr rfl fun n _ => by simp only [x]; ring
  have hcub : 0 ≤ 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
      ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by positivity
  have hpi : 0 ≤ Real.pi ^ 2 / 48 := by positivity
  have hsH : 0 ≤ Real.sqrt (2 * H) := Real.sqrt_nonneg _
  have htri : |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c'| ≤ |M| + 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
        ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
    have := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c') M
    linarith
  rw [← hm]
  calc _ ≤ |M| + _ := htri
    _ ≤ (Real.pi ^ 2 / 48 * ∑ p ∈ S, |c p| * p * Eb p + |m| / 6 * ∑ p ∈ S, |c p| / p +
          Real.sqrt (2 * H) * ∑ p ∈ S, |c p| * Real.sqrt p * E p) +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 :=
        add_le_add hMb le_rfl
    _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left hCb hpi
        have h2 := mul_le_mul_of_nonneg_left hC hsH
        nlinarith [h1, h2]

end

end GaloisForLFunctions.BezoutValuationIncidence
