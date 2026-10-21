import GaloisForLFunctions.BezoutValuationIncidence.KernelMeanAtCompositeModuliAndTheAllRowsLaws
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant

/-!
# The Fourier form of the cubic kernel and fourth-order large-sieve dispersion

**Spectral forms of the cubic potential and kernel.** Over the nontrivial `d`-th roots of unity `T_d`,
the cubic potential `Ψ_d` satisfies `Ψ_d(M + 1) - Ψ_d(M) = Φ_d(M + 1)` with zero period sum, giving

`Ψ_d(M) = Σ_{η ∈ T_d} (η / (|η - 1|² (η - 1))) η^M`,
`2Ψ_d(M) - Φ_d(M) = Σ_{η ∈ T_d} w₃(η) η^M`,  `w₃(η) = (η + 1) / (|η - 1|² (η - 1)) = -η(η + 1)/(η - 1)³`.

Because `2Ψ_d(0) - Φ_d(0) = 0`, the cubic spectral weights satisfy `Σ_{η ∈ T_d} w₃(η) = 0` at every
modulus `d ≥ 1`. Since `{η ∈ T_d | η^j = 1} = T_{gcd(j, d)}`, the `η^j = 1` zero-modes of the quadratic
potential sum to `(gcd(j, d)² - 1)/12` (the `j`-th harmonic of `m_d`), while the `η^j = 1` zero-modes of
the cubic potential sum to `0`. Consequently, for **every** modulus `d ≥ 1` (prime or composite) and
every harmonic `j ≥ 1`, only the nontrivial frequencies `η^j ≠ 1` survive in both layers of the third-order
kernel statistic `Λ_d(c')`:

`Σ_n (c'(n)/n²)(Φ_d(jn) - (gcd(j, d)² - 1)/12) = Σ_{η ∈ T_d, η^j ≠ 1} |η - 1|^{-2} S₂(η^j)`,
`Σ_n (c'(n)/n³)(2Ψ_d(jn) - Φ_d(jn)) = Σ_{η ∈ T_d, η^j ≠ 1} w₃(η) S₃(η^j)`,

where `S₂(z) = Σ_n (c'(n)/n²) z^n` and `S₃(z) = Σ_n (c'(n)/n³) z^n`.

**Fourth-order large-sieve dispersion of the dual norm.** Applying Cauchy–Schwarz, Farey separation
`Σ_{ζ prim p} |ζ - 1|^{-4} ≤ p⁴/64` and `Σ_{ζ prim p} |ζ - 1|^{-6} ≤ p⁶/1024`, and the dilated
log-free large sieve to both layers of `Λ_p(c')` disperses the third-order `p²/n³` remainder into an `ℓ²`
large-sieve term smaller by `P/Q`, pushing the deterministic remainder to fourth order `O(P⁴/Q³)` and
bounding the strong `ℓ¹` dual norm `Σ_{p ∈ S} (|c(p)|/p) |Λ_p(c')|` uniformly over all sign patterns of `c`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Spectral forms of the cubic potential and of the odd cubic polynomial -/

/-- **Fourier form of the cubic potential.**
`Ψ_d(M) = Σ_{η ∈ T_d} (η / (|η - 1|² (η - 1))) η^M`. -/
theorem cubicPotential_eq_spectral {d : ℕ} (hd : 0 < d) (M : ℕ) :
    (cubicPotential d M : ℂ) =
      ∑ η ∈ nontrivialRoots d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * (η / (η - 1)) * η ^ M := by
  set F : ℕ → ℂ := fun M =>
    ∑ η ∈ nontrivialRoots d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * (η / (η - 1)) * η ^ M
  have hstep : ∀ M, F (M + 1) - F M = (residuePotential d (M + 1) : ℂ) := by
    intro M
    rw [residuePotential_eq_spectral hd (M + 1)]
    simp only [F, ← sum_sub_distrib]
    refine sum_congr rfl fun η hη => ?_
    have h1 : η - 1 ≠ 0 := sub_ne_zero.mpr ((mem_nontrivialRoots hd).mp hη).1
    field_simp
    ring
  have hconst : ∀ M, (cubicPotential d M : ℂ) - F M = (cubicPotential d 0 : ℂ) - F 0 := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih =>
      rw [← ih]
      have h := cubicPotential_succ_sub hd M
      have hC : (cubicPotential d (M + 1) : ℂ) = cubicPotential d M + residuePotential d (M + 1) := by
        rw [← h]; push_cast; ring
      rw [hC, ← hstep M]
      ring
  have hperF : ∑ M ∈ range d, F M = 0 := by
    simp only [F]
    rw [sum_comm]
    refine sum_eq_zero fun η hη => ?_
    rw [← mul_sum]
    obtain ⟨h1, hdη⟩ := (mem_nontrivialRoots hd).mp hη
    rw [geom_sum_eq h1, hdη, sub_self, zero_div, mul_zero]
  have hperΨ : ∑ M ∈ range d, (cubicPotential d M : ℂ) = 0 := by
    have h := sum_Ico_cubicPotential_period hd 0
    rw [zero_add, ← range_eq_Ico] at h
    exact_mod_cast h
  have hsum : ∑ M ∈ range d, ((cubicPotential d M : ℂ) - F M) = 0 := by
    rw [sum_sub_distrib, hperΨ, hperF, sub_zero]
  rw [sum_congr rfl fun M _ => hconst M, sum_const, card_range, nsmul_eq_mul] at hsum
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h0 := (mul_eq_zero.mp hsum).resolve_left hd0
  have := hconst M
  rw [h0] at this
  exact sub_eq_zero.mp this

/-- The cubic spectral weight `w₃(η) = (η + 1) / (|η - 1|² (η - 1))`. -/
def cubicSpectralWeight (η : ℂ) : ℂ :=
  (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((η + 1) / (η - 1))

/-- On the unit circle, `w₃(η) = -η(η + 1)/(η - 1)³`. -/
theorem cubicSpectralWeight_eq {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) :
    cubicSpectralWeight η = -η * (η + 1) / (η - 1) ^ 3 := by
  have hsub : η - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [cubicSpectralWeight, inv_norm_sub_one_sq_eq hη h1]
  field_simp

/-- On the unit circle, `‖w₃(η)‖ ≤ 2 / ‖η - 1‖³`. -/
theorem norm_cubicSpectralWeight_le {η : ℂ} (hη : ‖η‖ = 1) :
    ‖cubicSpectralWeight η‖ ≤ 2 / ‖η - 1‖ ^ 3 := by
  rw [cubicSpectralWeight, norm_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have hadd : ‖η + 1‖ ≤ 2 := by
    calc ‖η + 1‖ ≤ ‖η‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [hη, norm_one]; ring
  calc (‖η - 1‖ ^ 2)⁻¹ * (‖η + 1‖ / ‖η - 1‖)
      ≤ (‖η - 1‖ ^ 2)⁻¹ * (2 / ‖η - 1‖) := by gcongr
    _ = 2 / ‖η - 1‖ ^ 3 := by ring

/-- **Fourier form of the odd cubic Bernoulli polynomial.**
`2Ψ_d(M) - Φ_d(M) = Σ_{η ∈ T_d} w₃(η) η^M`. -/
theorem two_mul_cubicPotential_sub_eq_spectral {d : ℕ} (hd : 0 < d) (M : ℕ) :
    ((2 * cubicPotential d M - residuePotential d M : ℝ) : ℂ) =
      ∑ η ∈ nontrivialRoots d, cubicSpectralWeight η * η ^ M := by
  push_cast
  rw [cubicPotential_eq_spectral hd M, residuePotential_eq_spectral hd M, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun η hη => ?_
  have h1 : η - 1 ≠ 0 := sub_ne_zero.mpr ((mem_nontrivialRoots hd).mp hη).1
  simp only [cubicSpectralWeight]
  field_simp
  ring

/-- The cubic spectral weights sum to zero over `T_d` at every modulus `d ≥ 1`. -/
theorem sum_nontrivialRoots_cubicSpectralWeight {d : ℕ} (hd : 0 < d) :
    ∑ η ∈ nontrivialRoots d, cubicSpectralWeight η = 0 := by
  have h := (two_mul_cubicPotential_sub_eq_spectral hd 0).symm
  simp only [pow_zero, mul_one] at h
  rw [h, two_mul_cubicPotential_sub_eq_poly hd 0, Nat.zero_mod, Nat.cast_zero, cubicDiffPoly_zero,
    Complex.ofReal_zero]

/-! ## §2. Zero-mode cancellation at all moduli and the spectral form of both kernels -/

/-- At any modulus `d ≥ 1`, if `η ∈ T_d` and `η^j ≠ 1`, then `η^j ∈ T_d`. -/
theorem pow_mem_nontrivialRoots_of_ne_one {d : ℕ} (hd : 0 < d) {η : ℂ}
    (hη : η ∈ nontrivialRoots d) {j : ℕ} (hj : η ^ j ≠ 1) :
    η ^ j ∈ nontrivialRoots d := by
  obtain ⟨_, hdη⟩ := (mem_nontrivialRoots hd).mp hη
  exact (mem_nontrivialRoots hd).mpr ⟨hj, by rw [← pow_mul, mul_comm, pow_mul, hdη, one_pow]⟩

/-- The `η^j = 1` zero-modes of the quadratic weight sum to `(gcd(j, d)² - 1)/12`. -/
theorem sum_filter_pow_eq_one_inv_norm_sq {d : ℕ} (hd : 0 < d) (j : ℕ) :
    ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j = 1), (‖η - 1‖ ^ 2)⁻¹ =
      (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12 := by
  rw [nontrivialRoots_filter_pow_eq_one hd j,
    sum_nontrivialRoots_inv_norm_sq (Nat.gcd_pos_of_pos_right j hd)]

/-- The `η^j = 1` zero-modes of the cubic weight sum to `0` at every modulus `d ≥ 1`. -/
theorem sum_filter_pow_eq_one_cubicSpectralWeight {d : ℕ} (hd : 0 < d) (j : ℕ) :
    ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j = 1), cubicSpectralWeight η = 0 := by
  rw [nontrivialRoots_filter_pow_eq_one hd j,
    sum_nontrivialRoots_cubicSpectralWeight (Nat.gcd_pos_of_pos_right j hd)]

/-- **Centred quadratic harmonic in the Fourier basis.** Subtracting `(gcd(j, d)² - 1)/12` removes
precisely the `η^j = 1` zero-modes at every modulus `d ≥ 1`. -/
theorem sum_mul_residuePotential_sub_gcd_eq_spectral {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    ((∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12) : ℝ) : ℂ) =
      ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
        (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) := by
  have hsplit : ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
      (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12) =
      ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d (j * n) -
        (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12 * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit, Complex.ofReal_sub, sum_mul_residuePotential_eq_spectral hd N j c']
  have hpart := (sum_filter_add_sum_filter_not (nontrivialRoots d) (fun η : ℂ => η ^ j = 1)
    (fun η => (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j))).symm
  have hzero : ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j = 1),
      (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) =
      (((((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12 * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    have h1 : ∀ η ∈ (nontrivialRoots d).filter (fun η => η ^ j = 1),
        (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) =
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' 1 := fun η hη => by
      rw [(mem_filter.mp hη).2]
    rw [sum_congr rfl h1, ← sum_mul, ← Complex.ofReal_sum, sum_filter_pow_eq_one_inv_norm_sq hd j]
    simp only [rowTransform, one_pow, mul_one]
    push_cast
    ring
  rw [hpart, hzero, add_sub_cancel_left]

/-- The cubic weighted Fourier transform `S₃(z) = Σ_n (c'(n)/n³) z^n` of a large-scale row. -/
def cubicRowTransform (N : ℕ) (c' : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, ((c' n / (n : ℝ) ^ 3 : ℝ) : ℂ) * z ^ n

/-- Unfiltered spectral form of the `j`-th cubic harmonic. -/
theorem sum_mul_cubicDiff_eq_spectral_unfiltered {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    ((∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n)) : ℝ) : ℂ) =
      ∑ η ∈ nontrivialRoots d, cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) := by
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, two_mul_cubicPotential_sub_eq_spectral hd, cubicRowTransform, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun η _ => sum_congr rfl fun n _ => ?_
  rw [pow_mul]
  ring

/-- **Cubic harmonic in the Fourier basis.** The `η^j = 1` zero-modes vanish identically at every
modulus `d ≥ 1`. -/
theorem sum_mul_cubicDiff_eq_spectral {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    ((∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n)) : ℝ) : ℂ) =
      ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
        cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) := by
  rw [sum_mul_cubicDiff_eq_spectral_unfiltered hd N j c']
  have hpart := (sum_filter_add_sum_filter_not (nontrivialRoots d) (fun η : ℂ => η ^ j = 1)
    (fun η => cubicSpectralWeight η * cubicRowTransform N c' (η ^ j))).symm
  have hzero : ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j = 1),
      cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) = 0 := by
    have h1 : ∀ η ∈ (nontrivialRoots d).filter (fun η => η ^ j = 1),
        cubicSpectralWeight η * cubicRowTransform N c' (η ^ j) =
          cubicSpectralWeight η * cubicRowTransform N c' 1 := fun η hη => by
      rw [(mem_filter.mp hη).2]
    rw [sum_congr rfl h1, ← sum_mul, sum_filter_pow_eq_one_cubicSpectralWeight hd j, zero_mul]
  rw [hpart, hzero, zero_add]

/-! ## §3. Unconditional Fourier bounds for the centred quadratic and cubic kernels at all moduli -/

/-- Norm bound on the `j`-th centred quadratic harmonic over `T_d`. -/
theorem abs_sum_mul_residuePotential_sub_gcd_le_sum {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12)| ≤
      ∑ η ∈ nontrivialRoots d, (‖η - 1‖ ^ 2)⁻¹ * ‖rowTransform N c' (η ^ j)‖ := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_residuePotential_sub_gcd_eq_spectral hd N j c']
  calc ‖∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j)‖
      ≤ ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          (‖η - 1‖ ^ 2)⁻¹ * ‖rowTransform N c' (η ^ j)‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun η _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ ∑ η ∈ nontrivialRoots d, (‖η - 1‖ ^ 2)⁻¹ * ‖rowTransform N c' (η ^ j)‖ :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun η _ _ => by positivity

/-- Norm bound on the `j`-th cubic harmonic over `T_d`. -/
theorem abs_sum_mul_cubicDiff_le_sum {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n))| ≤
      ∑ η ∈ nontrivialRoots d, 2 / ‖η - 1‖ ^ 3 * ‖cubicRowTransform N c' (η ^ j)‖ := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_cubicDiff_eq_spectral hd N j c']
  calc ‖∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          cubicSpectralWeight η * cubicRowTransform N c' (η ^ j)‖
      ≤ ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          2 / ‖η - 1‖ ^ 3 * ‖cubicRowTransform N c' (η ^ j)‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun η hη => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (norm_cubicSpectralWeight_le (norm_eq_one_of_mem_nontrivialRoots hd (mem_filter.mp hη).1))
          (norm_nonneg _)
    _ ≤ ∑ η ∈ nontrivialRoots d, 2 / ‖η - 1‖ ^ 3 * ‖cubicRowTransform N c' (η ^ j)‖ :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun η _ _ => by positivity

/-- The maximum of `‖S₂(ζ)‖` on the nontrivial `d`-th roots of unity (`0` if `T_d` is empty). -/
def rowTransformMax (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) : ℝ :=
  if h : (nontrivialRoots d).Nonempty then
    (nontrivialRoots d).sup' h (fun ζ => ‖rowTransform N c' ζ‖)
  else 0

/-- The maximum of `‖S₃(ζ)‖` on the nontrivial `d`-th roots of unity (`0` if `T_d` is empty). -/
def cubicRowTransformMax (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) : ℝ :=
  if h : (nontrivialRoots d).Nonempty then
    (nontrivialRoots d).sup' h (fun ζ => ‖cubicRowTransform N c' ζ‖)
  else 0

theorem rowTransformMax_nonneg (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) :
    0 ≤ rowTransformMax N c' d := by
  unfold rowTransformMax
  split_ifs with h
  · obtain ⟨ζ, hζ⟩ := h
    exact (norm_nonneg _).trans (le_sup' (fun z => ‖rowTransform N c' z‖) hζ)
  · exact le_rfl

theorem cubicRowTransformMax_nonneg (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) :
    0 ≤ cubicRowTransformMax N c' d := by
  unfold cubicRowTransformMax
  split_ifs with h
  · obtain ⟨ζ, hζ⟩ := h
    exact (norm_nonneg _).trans (le_sup' (fun z => ‖cubicRowTransform N c' z‖) hζ)
  · exact le_rfl

theorem norm_rowTransform_le_max (N : ℕ) (c' : ℕ → ℝ) {d : ℕ} {ζ : ℂ}
    (hζ : ζ ∈ nontrivialRoots d) :
    ‖rowTransform N c' ζ‖ ≤ rowTransformMax N c' d := by
  have h : (nontrivialRoots d).Nonempty := ⟨ζ, hζ⟩
  rw [rowTransformMax, dif_pos h]
  exact le_sup' (fun z => ‖rowTransform N c' z‖) hζ

theorem norm_cubicRowTransform_le_max (N : ℕ) (c' : ℕ → ℝ) {d : ℕ} {ζ : ℂ}
    (hζ : ζ ∈ nontrivialRoots d) :
    ‖cubicRowTransform N c' ζ‖ ≤ cubicRowTransformMax N c' d := by
  have h : (nontrivialRoots d).Nonempty := ⟨ζ, hζ⟩
  rw [cubicRowTransformMax, dif_pos h]
  exact le_sup' (fun z => ‖cubicRowTransform N c' z‖) hζ

/-- Unconditional bound on the `j`-th centred quadratic harmonic at any modulus `d ≥ 1`. -/
theorem abs_sum_mul_residuePotential_sub_gcd_le {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12)| ≤
      ((d : ℝ) ^ 2 - 1) / 12 * rowTransformMax N c' d := by
  have hσ₂0 := rowTransformMax_nonneg N c' d
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_residuePotential_sub_gcd_eq_spectral hd N j c',
    ← sum_nontrivialRoots_inv_norm_sq hd, sum_mul]
  calc ‖∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j)‖
      ≤ ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          (‖η - 1‖ ^ 2)⁻¹ * rowTransformMax N c' d := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun η hη => ?_)
        obtain ⟨hηd, hj⟩ := mem_filter.mp hη
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (norm_rowTransform_le_max N c' (pow_mem_nontrivialRoots_of_ne_one hd hηd hj))
          (by positivity)
    _ ≤ ∑ η ∈ nontrivialRoots d, (‖η - 1‖ ^ 2)⁻¹ * rowTransformMax N c' d :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun η _ _ => by positivity

/-- Unconditional bound on the `j`-th cubic harmonic at any modulus `d ≥ 1`. -/
theorem abs_sum_mul_cubicDiff_le {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n))| ≤
      (2 * ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d := by
  have hσ₃0 := cubicRowTransformMax_nonneg N c' d
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_cubicDiff_eq_spectral hd N j c',
    mul_sum, sum_mul]
  calc ‖∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          cubicSpectralWeight η * cubicRowTransform N c' (η ^ j)‖
      ≤ ∑ η ∈ (nontrivialRoots d).filter (fun η => η ^ j ≠ 1),
          2 * (1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun η hη => ?_)
        obtain ⟨hηd, hj⟩ := mem_filter.mp hη
        rw [norm_mul, show 2 * (1 / ‖η - 1‖ ^ 3) = 2 / ‖η - 1‖ ^ 3 by ring]
        exact mul_le_mul (norm_cubicSpectralWeight_le (norm_eq_one_of_mem_nontrivialRoots hd hηd))
          (norm_cubicRowTransform_le_max N c' (pow_mem_nontrivialRoots_of_ne_one hd hηd hj))
          (norm_nonneg _) (by positivity)
    _ ≤ ∑ η ∈ nontrivialRoots d, 2 * (1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun η _ _ => by positivity

/-- Harmonic series expansion of the centred quadratic kernel against `c'`. -/
theorem hasSum_sum_mul_bernoulliKernel_sub_kernelMean {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    HasSum (fun j : ℕ =>
      (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d ((j + 1) * n) - (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12)) *
        (1 / ((j : ℝ) + 1) ^ 2))
      (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)) := by
  have h := hasSum_sum fun n (_ : n ∈ Icc 1 N) =>
    ((hasSum_bernoulliKernel hd n).sub (hasSum_kernelMean hd)).mul_left (c' n / (n : ℝ) ^ 2)
  refine h.congr_fun fun j => ?_
  rw [sum_mul]
  refine sum_congr rfl fun n _ => ?_
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Harmonic series expansion of the cubic kernel against `c'`. -/
theorem hasSum_sum_mul_cubicKernel {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    HasSum (fun j : ℕ =>
      (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n))) *
        (1 / ((j : ℝ) + 1) ^ 3))
      (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n) := by
  have h := hasSum_sum fun n (_ : n ∈ Icc 1 N) =>
    (hasSum_cubicKernel hd n).mul_left (c' n / (n : ℝ) ^ 3)
  refine h.congr_fun fun j => ?_
  rw [sum_mul]
  exact sum_congr rfl fun n _ => by ring

/-- **All-moduli Fourier bound for the centred Bernoulli kernel.** Subtracting `m_d` eliminates the
`S₀` diagonal leak at every modulus `d ≥ 1`. -/
theorem abs_sum_mul_bernoulliKernel_sub_kernelMean_le_fourier {d : ℕ} (hd : 0 < d) (N : ℕ)
    (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)| ≤
      Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * rowTransformMax N c' d := by
  have hσ₂0 := rowTransformMax_nonneg N c' d
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hd1 : (0 : ℝ) ≤ ((d : ℝ) ^ 2 - 1) / 12 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have ht := hasSum_sum_mul_bernoulliKernel_sub_kernelMean hd N c'
  refine le_of_tendsto' (ht.tendsto_sum_nat.abs) fun K => ?_
  calc |∑ j ∈ range K, (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
          (residuePotential d ((j + 1) * n) - (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12)) *
          (1 / ((j : ℝ) + 1) ^ 2)|
      ≤ ∑ j ∈ range K, ((d : ℝ) ^ 2 - 1) / 12 * rowTransformMax N c' d * (1 / ((j : ℝ) + 1) ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 2)]
        exact mul_le_mul_of_nonneg_right
          (abs_sum_mul_residuePotential_sub_gcd_le hd N (j + 1) c') (by positivity)
    _ = ((d : ℝ) ^ 2 - 1) / 12 * rowTransformMax N c' d *
          ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 := by rw [← mul_sum]
    _ ≤ ((d : ℝ) ^ 2 - 1) / 12 * rowTransformMax N c' d * (Real.pi ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun j _ => by positivity) hz) (by positivity)
    _ = Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * rowTransformMax N c' d := by ring

/-- **All-moduli Fourier bound for the cubic Bernoulli kernel.** -/
theorem abs_sum_mul_cubicKernel_le_fourier {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n| ≤
      Real.pi ^ 2 / 3 * (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d := by
  have hσ₃0 := cubicRowTransformMax_nonneg N c' d
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  set W₃ := ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3
  have hW₃ : 0 ≤ W₃ := sum_nonneg fun η _ => by positivity
  have ht := hasSum_sum_mul_cubicKernel hd N c'
  refine le_of_tendsto' (ht.tendsto_sum_nat.abs) fun K => ?_
  calc |∑ j ∈ range K, (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
          (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n))) *
          (1 / ((j : ℝ) + 1) ^ 3)|
      ≤ ∑ j ∈ range K, 2 * W₃ * cubicRowTransformMax N c' d * (1 / ((j : ℝ) + 1) ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 3)]
        have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
          have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
        have hpow : 1 / ((j : ℝ) + 1) ^ 3 ≤ 1 / ((j : ℝ) + 1) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hj1 (by norm_num))
        exact mul_le_mul (abs_sum_mul_cubicDiff_le hd N (j + 1) c') hpow
          (by positivity) (by positivity)
    _ = 2 * W₃ * cubicRowTransformMax N c' d * ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 := by rw [← mul_sum]
    _ ≤ 2 * W₃ * cubicRowTransformMax N c' d * (Real.pi ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun j _ => by positivity) hz) (by positivity)
    _ = Real.pi ^ 2 / 3 * W₃ * cubicRowTransformMax N c' d := by ring

/-- **All-moduli Fourier bound for the kernel statistic `Λ_d(c')`.** -/
theorem abs_kernelStatisticAll_le_fourier {d : ℕ} (hd : 0 < d) (N : ℕ) (c' : ℕ → ℝ) :
    |kernelStatisticAll N c' d| ≤
      Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * rowTransformMax N c' d +
        Real.pi ^ 2 / 3 * (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d := by
  rw [kernelStatisticAll, sum_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_sum_mul_bernoulliKernel_sub_kernelMean_le_fourier hd N c')
    (abs_sum_mul_cubicKernel_le_fourier hd N c'))

/-- **All-moduli fourth-order Fourier cross-scale law.** Valid for all `N : ℕ` and all rows `c, c'`. -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_fourier (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      Real.pi ^ 2 / 72 * ∑ d ∈ Icc 1 N, |c d| * d * rowTransformMax N c' d +
        Real.pi ^ 2 / 3 * ∑ d ∈ Icc 1 N, |c d| / d *
          (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d +
        6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  have hlaw := abs_rowBilinear_sub_kernelStatisticAll_le N c c'
  have hstat : |∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d| ≤
      Real.pi ^ 2 / 72 * ∑ d ∈ Icc 1 N, |c d| * d * rowTransformMax N c' d +
        Real.pi ^ 2 / 3 * ∑ d ∈ Icc 1 N, |c d| / d *
          (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hσ₂0 := rowTransformMax_nonneg N c' d
    rw [abs_mul, abs_div, abs_of_pos hdR]
    calc |c d| / d * |kernelStatisticAll N c' d|
        ≤ |c d| / d * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * rowTransformMax N c' d +
            Real.pi ^ 2 / 3 * (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) *
              cubicRowTransformMax N c' d) :=
          mul_le_mul_of_nonneg_left (abs_kernelStatisticAll_le_fourier hd0 N c') (by positivity)
      _ ≤ Real.pi ^ 2 / 72 * (|c d| * d * rowTransformMax N c' d) +
            Real.pi ^ 2 / 3 * (|c d| / d * (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) *
              cubicRowTransformMax N c' d) := by
          have e1 : |c d| / d * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * rowTransformMax N c' d) =
              Real.pi ^ 2 / 72 * (|c d| * d * rowTransformMax N c' d) -
                Real.pi ^ 2 / 72 * (|c d| * rowTransformMax N c' d / d) := by field_simp
          have e2 : |c d| / d * (Real.pi ^ 2 / 3 * (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) *
              cubicRowTransformMax N c' d) =
              Real.pi ^ 2 / 3 * (|c d| / d * (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) *
                cubicRowTransformMax N c' d) := by ring
          have hpos : 0 ≤ Real.pi ^ 2 / 72 * (|c d| * rowTransformMax N c' d / d) := by positivity
          linarith
  have key := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c')
    (∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d)
  linarith

/-- At a prime `p`, `kernelMean p` coincides with `primeKernelMean p`. -/
theorem kernelMean_prime {p : ℕ} (hp : p.Prime) : kernelMean p = primeKernelMean p := by
  rw [kernelMean, sum_range_bernoulliKernel_prime hp, primeKernelMean]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp

/-- At a prime `p`, `kernelStatisticAll N c' p` coincides with `kernelStatistic N c' p`. -/
theorem kernelStatisticAll_prime {p : ℕ} (hp : p.Prime) (N : ℕ) (c' : ℕ → ℝ) :
    kernelStatisticAll N c' p = kernelStatistic N c' p := by
  simp only [kernelStatisticAll, kernelStatistic, kernelMean_prime hp]

/-- At a prime `p`, the nontrivial `p`-th roots are the primitive `p`-th roots. -/
theorem nontrivialRoots_eq_primitiveRoots {p : ℕ} (hp : p.Prime) :
    nontrivialRoots p = primitiveRoots p ℂ := by
  ext ζ
  rw [mem_nontrivialRoots hp.pos, mem_primitiveRoots hp.pos, IsPrimitiveRoot.iff_orderOf]
  constructor
  · rintro ⟨h1, hpζ⟩
    haveI := Fact.mk hp
    exact orderOf_eq_prime hpζ h1
  · intro hord
    refine ⟨?_, ?_⟩
    · intro h1
      rw [h1, orderOf_one] at hord
      exact hp.ne_one hord.symm
    · rw [← hord, pow_orderOf_eq_one]

/-- **Prime-modulus Fourier bound for the kernel statistic `Λ_p(c')`.** -/
theorem abs_kernelStatistic_le_fourier {p : ℕ} (hp : p.Prime) (N : ℕ) (c' : ℕ → ℝ) :
    |kernelStatistic N c' p| ≤
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 * rowTransformMax N c' p +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 * cubicRowTransformMax N c' p := by
  have hσ₃0 := cubicRowTransformMax_nonneg N c' p
  rw [← kernelStatisticAll_prime hp]
  refine (abs_kernelStatisticAll_le_fourier hp.pos N c').trans (add_le_add le_rfl ?_)
  rw [nontrivialRoots_eq_primitiveRoots hp]
  have h3 := sum_primitiveRoots_inv_norm_sub_one_pow_le hp.two_le 1
  calc Real.pi ^ 2 / 3 * (∑ η ∈ primitiveRoots p ℂ, 1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' p
      ≤ Real.pi ^ 2 / 3 * (((p : ℝ) / 4) ^ 1 * ((p : ℝ) ^ 2 / 4)) * cubicRowTransformMax N c' p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) hσ₃0
    _ = Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 * cubicRowTransformMax N c' p := by ring

/-! ## §4. Fourth-order large-sieve dispersion of the dual norm and cross-scale functional -/

/-- The dilated roots of unity `ζ^j` have at most `j` preimages, so the Montgomery–Vaughan large sieve
over roots of unity of order at most `Q₀` costs a factor `j` with the sharp factor `L + Q₀² - 1`. -/
theorem sum_norm_sq_dilated_sharp_le {T : Finset ℂ} {Q₀ : ℕ} (hQ₀ : 2 ≤ Q₀)
    (hT : T ⊆ responseRoots Q₀) {j : ℕ} (hj : 0 < j) (A L : ℕ) (y : ℕ → ℂ) :
    ∑ ζ ∈ T, ‖∑ k ∈ Icc (A + 1) (A + L), y k * (ζ ^ j) ^ k‖ ^ 2 ≤
      j * (((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) * ∑ k ∈ Icc (A + 1) (A + L), ‖y k‖ ^ 2) := by
  classical
  set f : ℂ → ℝ := fun ξ => ‖∑ k ∈ Icc (A + 1) (A + L), y k * ξ ^ k‖ ^ 2
  rw [show (∑ ζ ∈ T, ‖∑ k ∈ Icc (A + 1) (A + L), y k * (ζ ^ j) ^ k‖ ^ 2) =
    ∑ ζ ∈ T, f (ζ ^ j) from rfl, sum_comp]
  have himg : ∀ ξ ∈ T.image (· ^ j), ∃ d, 1 ≤ d ∧ d ≤ Q₀ ∧ ξ ^ d = 1 := by
    intro ξ hξ
    obtain ⟨ζ, hζ, rfl⟩ := mem_image.mp hξ
    obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp (hT hζ)
    obtain ⟨hd1, hdQ⟩ := mem_Icc.mp hd
    have hpow := (Polynomial.mem_nthRootsFinset hd1 1).mp hζd
    exact ⟨d, hd1, hdQ, by rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]⟩
  have hls := largeSieve_rootsOfUnity_sharp hQ₀ himg A L y
  calc ∑ ξ ∈ T.image (· ^ j), (T.filter (· ^ j = ξ)).card • f ξ
      ≤ ∑ ξ ∈ T.image (· ^ j), (j : ℝ) * f ξ := by
        refine sum_le_sum fun ξ _ => ?_
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have hsub : T.filter (· ^ j = ξ) ⊆ Polynomial.nthRootsFinset j ξ := fun ζ hζ =>
          (Polynomial.mem_nthRootsFinset hj ξ).mpr (mem_filter.mp hζ).2
        have hcard : (Polynomial.nthRootsFinset j ξ).card ≤ j := by
          rw [Polynomial.nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots j ξ)
        exact_mod_cast (card_le_card hsub).trans hcard
    _ = (j : ℝ) * ∑ ξ ∈ T.image (· ^ j), f ξ := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hls (Nat.cast_nonneg j)

/-- `Σ_{1 ≤ j ≤ K} √j / j³ ≤ 2`. -/
theorem sum_Icc_sqrt_div_cube_le (K : ℕ) :
    ∑ j ∈ Icc 1 K, Real.sqrt j / (j : ℝ) ^ 3 ≤ 2 := by
  calc ∑ j ∈ Icc 1 K, Real.sqrt j / (j : ℝ) ^ 3
      ≤ ∑ j ∈ Icc 1 K, 1 / (j : ℝ) ^ 2 := by
        refine sum_le_sum fun j hj => ?_
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
        have hsqrt : Real.sqrt j ≤ (j : ℝ) := by
          calc Real.sqrt j ≤ Real.sqrt ((j : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = (j : ℝ) := Real.sqrt_sq (by linarith)
        calc Real.sqrt j / (j : ℝ) ^ 3 ≤ (j : ℝ) / (j : ℝ) ^ 3 := by gcongr
          _ = 1 / (j : ℝ) ^ 2 := by field_simp
    _ ≤ 2 := by
        rcases Nat.eq_zero_or_pos K with rfl | hK
        · simp
        · have := sum_Icc_one_div_sq_le hK
          have : 0 ≤ 1 / (K : ℝ) := by positivity
          linarith

/-- Window restriction of `rowTransform`. -/
theorem rowTransform_eq_window {N A L : ℕ} {c' : ℕ → ℝ}
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) (z : ℂ) :
    rowTransform N c' z =
      ∑ n ∈ Icc (A + 1) (A + L), ((c' n / (n : ℝ) ^ 2 : ℝ) : ℂ) * z ^ n := by
  have hWN : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  rw [rowTransform, ← sum_subset hWN fun n _ hn => by
    have : c' n = 0 := by by_contra h; exact hn (hsupp' n h)
    simp [this]]

/-- Window restriction of `cubicRowTransform`. -/
theorem cubicRowTransform_eq_window {N A L : ℕ} {c' : ℕ → ℝ}
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) (z : ℂ) :
    cubicRowTransform N c' z =
      ∑ n ∈ Icc (A + 1) (A + L), ((c' n / (n : ℝ) ^ 3 : ℝ) : ℂ) * z ^ n := by
  have hWN : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  rw [cubicRowTransform, ← sum_subset hWN fun n _ hn => by
    have : c' n = 0 := by by_contra h; exact hn (hsupp' n h)
    simp [this]]

/-- **Large-sieve dispersion of the centred quadratic kernel statistics.** -/
theorem sum_abs_mul_bernoulliKernel_sub_mean_le_largeSieve {N Q₀ A L : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) (c c' : ℕ → ℝ)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    ∑ p ∈ S, |c p| / p *
        |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p)| ≤
      1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
        Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
        Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) := by
  classical
  set W := Icc (A + 1) (A + L)
  set T := S.biUnion fun p => primitiveRoots p ℂ with hT
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
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2⟩,
      (Polynomial.mem_nthRootsFinset (hS p hp).1.pos 1).mpr hprim.pow_eq_one⟩
  set α₂ : ℂ → ℝ := fun ζ => |c (orderOf ζ)| / (orderOf ζ : ℝ) * (‖ζ - 1‖ ^ 2)⁻¹
  have hα₂eq : ∀ p ∈ S, ∀ ζ ∈ primitiveRoots p ℂ, α₂ ζ = |c p| / p * (‖ζ - 1‖ ^ 2)⁻¹ := by
    intro p hp ζ hζ
    show |c (orderOf ζ)| / (orderOf ζ : ℝ) * (‖ζ - 1‖ ^ 2)⁻¹ = |c p| / p * (‖ζ - 1‖ ^ 2)⁻¹
    rw [← ((mem_primitiveRoots (hS p hp).1.pos).mp hζ).eq_orderOf]
  have hα₂sum : Real.sqrt (∑ ζ ∈ T, α₂ ζ ^ 2) ≤
      1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) := by
    rw [show (1 : ℝ) / 8 = Real.sqrt (1 / 64) by
      rw [show (1 : ℝ) / 64 = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    rw [hT, sum_biUnion hdisj, mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hp2 := (hS p hp).1.two_le
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    have hsq : ∑ ζ ∈ primitiveRoots p ℂ, α₂ ζ ^ 2 =
        (c p / p) ^ 2 * ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ (2 + 2) := by
      rw [mul_sum]
      refine sum_congr rfl fun ζ hζ => ?_
      rw [hα₂eq p hp ζ hζ, mul_pow, div_pow, sq_abs]
      ring
    rw [hsq]
    calc (c p / p) ^ 2 * ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ (2 + 2)
        ≤ (c p / p) ^ 2 * (((p : ℝ) / 4) ^ 2 * ((p : ℝ) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le hp2 2) (sq_nonneg _)
      _ = 1 / 64 * (c p ^ 2 * (p : ℝ) ^ 2) := by field_simp; ring
  set X : ℝ := (L : ℝ) + (Q₀ : ℝ) ^ 2 - 1
  set Y₂ : ℝ := ∑ n ∈ W, c' n ^ 2 / (n : ℝ) ^ 4
  have hX : 0 ≤ X := by
    have : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
    simp only [X]; nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hY₂ : 0 ≤ Y₂ := sum_nonneg fun n _ => by positivity
  have hjbound : ∀ j : ℕ, 1 ≤ j →
      ∑ p ∈ S, |c p| / p *
        |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
          (residuePotential p (j * n) - (((Nat.gcd j p : ℕ) : ℝ) ^ 2 - 1) / 12)| ≤
        Real.sqrt (∑ ζ ∈ T, α₂ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₂) * Real.sqrt j := by
    intro j hj
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    set y₂ : ℕ → ℂ := fun n => ((c' n / (n : ℝ) ^ 2 : ℝ) : ℂ)
    have hy₂ : ∑ n ∈ W, ‖y₂ n‖ ^ 2 = Y₂ := by
      refine sum_congr rfl fun n _ => ?_
      simp only [y₂, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
      ring
    have hls := sum_norm_sq_dilated_sharp_le hQ₀ hTroots hj A L y₂
    rw [hy₂] at hls
    calc ∑ p ∈ S, |c p| / p *
          |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
            (residuePotential p (j * n) - (((Nat.gcd j p : ℕ) : ℝ) ^ 2 - 1) / 12)|
        ≤ ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ, α₂ ζ * ‖rowTransform N c' (ζ ^ j)‖ := by
          refine sum_le_sum fun p hp => ?_
          have h1 := abs_sum_mul_residuePotential_sub_gcd_le_sum (hS p hp).1.pos N j c'
          rw [nontrivialRoots_eq_primitiveRoots (hS p hp).1] at h1
          have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
          refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (le_of_eq ?_)
          rw [mul_sum]
          refine sum_congr rfl fun ζ hζ => ?_
          rw [hα₂eq p hp ζ hζ, mul_assoc]
      _ = ∑ ζ ∈ T, α₂ ζ * ‖∑ n ∈ W, y₂ n * (ζ ^ j) ^ n‖ := by
          rw [hT, sum_biUnion hdisj]
          refine sum_congr rfl fun p _ => sum_congr rfl fun ζ _ => ?_
          rw [rowTransform_eq_window hsupp' hAL]
      _ ≤ Real.sqrt (∑ ζ ∈ T, α₂ ζ ^ 2) *
            Real.sqrt (∑ ζ ∈ T, ‖∑ n ∈ W, y₂ n * (ζ ^ j) ^ n‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt T _ _
      _ ≤ Real.sqrt (∑ ζ ∈ T, α₂ ζ ^ 2) * Real.sqrt ((j : ℝ) * (X * Y₂)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hls) (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑ ζ ∈ T, α₂ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₂) * Real.sqrt j := by
          rw [Real.sqrt_mul hjR.le, Real.sqrt_mul hX]; ring
  set t₂ : ℕ → ℕ → ℝ := fun p j =>
    (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
      (residuePotential p ((j + 1) * n) - (((Nat.gcd (j + 1) p : ℕ) : ℝ) ^ 2 - 1) / 12)) *
      (1 / ((j : ℝ) + 1) ^ 2)
  have htend : Tendsto (fun K : ℕ => ∑ p ∈ S, |c p| / p * |∑ j ∈ range K, t₂ p j|) atTop
      (𝓝 (∑ p ∈ S, |c p| / p *
        |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p)|)) := by
    refine tendsto_finsetSum S fun p hp => ?_
    have ht := hasSum_sum_mul_bernoulliKernel_sub_kernelMean (hS p hp).1.pos N c'
    rw [kernelMean_prime (hS p hp).1] at ht
    exact (ht.tendsto_sum_nat.abs).const_mul _
  refine le_of_tendsto' htend fun K => ?_
  calc ∑ p ∈ S, |c p| / p * |∑ j ∈ range K, t₂ p j|
      ≤ ∑ j ∈ range K, (1 / ((j : ℝ) + 1) ^ 2) *
          ∑ p ∈ S, |c p| / p *
            |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
              (residuePotential p ((j + 1) * n) -
                (((Nat.gcd (j + 1) p : ℕ) : ℝ) ^ 2 - 1) / 12)| := by
        calc ∑ p ∈ S, |c p| / p * |∑ j ∈ range K, t₂ p j|
            ≤ ∑ p ∈ S, ∑ j ∈ range K, |c p| / p * |t₂ p j| := by
              refine sum_le_sum fun p hp => ?_
              have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
              rw [← mul_sum]
              exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
          _ = ∑ j ∈ range K, (1 / ((j : ℝ) + 1) ^ 2) *
                ∑ p ∈ S, |c p| / p *
                  |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
                    (residuePotential p ((j + 1) * n) -
                      (((Nat.gcd (j + 1) p : ℕ) : ℝ) ^ 2 - 1) / 12)| := by
              rw [sum_comm]
              refine sum_congr rfl fun j _ => ?_
              rw [mul_sum]
              refine sum_congr rfl fun p _ => ?_
              simp only [t₂]
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 2)]
              ring
    _ ≤ ∑ j ∈ range K, Real.sqrt (∑ ζ ∈ T, α₂ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₂) *
          (Real.sqrt (j + 1 : ℕ) / ((j + 1 : ℕ) : ℝ) ^ 2) := by
        refine sum_le_sum fun j _ => ?_
        have h := mul_le_mul_of_nonneg_left (hjbound (j + 1) (by omega))
          (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 2)
        refine h.trans (le_of_eq ?_)
        push_cast
        ring
    _ = Real.sqrt (∑ ζ ∈ T, α₂ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₂) *
          ∑ j ∈ Icc 1 K, Real.sqrt j / (j : ℝ) ^ 2 := by
        rw [← mul_sum]
        congr 1
        induction K with
        | zero => simp
        | succ K ih => rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]
    _ ≤ 1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * (Real.sqrt X * Real.sqrt Y₂) * 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hα₂sum (by positivity))
          (sum_Icc_sqrt_div_sq_le K) (sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = 1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt X * Real.sqrt Y₂ := by ring

/-- **Large-sieve dispersion of the cubic kernel statistics.** -/
theorem sum_abs_mul_cubicKernel_le_largeSieve {N Q₀ A L : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) (c c' : ℕ → ℝ)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    ∑ p ∈ S, |c p| / p * |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel p n| ≤
      1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 4) *
        Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
        Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) := by
  classical
  set W := Icc (A + 1) (A + L)
  set T := S.biUnion fun p => primitiveRoots p ℂ with hT
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
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2⟩,
      (Polynomial.mem_nthRootsFinset (hS p hp).1.pos 1).mpr hprim.pow_eq_one⟩
  set α₃ : ℂ → ℝ := fun ζ => |c (orderOf ζ)| / (orderOf ζ : ℝ) * (2 / ‖ζ - 1‖ ^ 3)
  have hα₃eq : ∀ p ∈ S, ∀ ζ ∈ primitiveRoots p ℂ, α₃ ζ = |c p| / p * (2 / ‖ζ - 1‖ ^ 3) := by
    intro p hp ζ hζ
    show |c (orderOf ζ)| / (orderOf ζ : ℝ) * (2 / ‖ζ - 1‖ ^ 3) = |c p| / p * (2 / ‖ζ - 1‖ ^ 3)
    rw [← ((mem_primitiveRoots (hS p hp).1.pos).mp hζ).eq_orderOf]
  have hα₃sum : Real.sqrt (∑ ζ ∈ T, α₃ ζ ^ 2) ≤
      1 / 16 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 4) := by
    rw [show (1 : ℝ) / 16 = Real.sqrt (1 / 256) by
      rw [show (1 : ℝ) / 256 = (1 / 16) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    rw [hT, sum_biUnion hdisj, mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hp2 := (hS p hp).1.two_le
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    have hsq : ∑ ζ ∈ primitiveRoots p ℂ, α₃ ζ ^ 2 =
        4 * (c p / p) ^ 2 * ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ (4 + 2) := by
      rw [mul_sum]
      refine sum_congr rfl fun ζ hζ => ?_
      rw [hα₃eq p hp ζ hζ, mul_pow, div_pow, sq_abs]
      ring
    rw [hsq]
    calc 4 * (c p / p) ^ 2 * ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ (4 + 2)
        ≤ 4 * (c p / p) ^ 2 * (((p : ℝ) / 4) ^ 4 * ((p : ℝ) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le hp2 4)
            (by positivity)
      _ = 1 / 256 * (c p ^ 2 * (p : ℝ) ^ 4) := by field_simp; ring
  set X : ℝ := (L : ℝ) + (Q₀ : ℝ) ^ 2 - 1
  set Y₃ : ℝ := ∑ n ∈ W, c' n ^ 2 / (n : ℝ) ^ 6
  have hX : 0 ≤ X := by
    have : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
    simp only [X]; nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hY₃ : 0 ≤ Y₃ := sum_nonneg fun n _ => by positivity
  have hjbound : ∀ j : ℕ, 1 ≤ j →
      ∑ p ∈ S, |c p| / p *
        |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
          (2 * cubicPotential p (j * n) - residuePotential p (j * n))| ≤
        Real.sqrt (∑ ζ ∈ T, α₃ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₃) * Real.sqrt j := by
    intro j hj
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    set y₃ : ℕ → ℂ := fun n => ((c' n / (n : ℝ) ^ 3 : ℝ) : ℂ)
    have hy₃ : ∑ n ∈ W, ‖y₃ n‖ ^ 2 = Y₃ := by
      refine sum_congr rfl fun n _ => ?_
      simp only [y₃, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
      ring
    have hls := sum_norm_sq_dilated_sharp_le hQ₀ hTroots hj A L y₃
    rw [hy₃] at hls
    calc ∑ p ∈ S, |c p| / p *
          |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
            (2 * cubicPotential p (j * n) - residuePotential p (j * n))|
        ≤ ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ, α₃ ζ * ‖cubicRowTransform N c' (ζ ^ j)‖ := by
          refine sum_le_sum fun p hp => ?_
          have h1 := abs_sum_mul_cubicDiff_le_sum (hS p hp).1.pos N j c'
          rw [nontrivialRoots_eq_primitiveRoots (hS p hp).1] at h1
          have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
          refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (le_of_eq ?_)
          rw [mul_sum]
          refine sum_congr rfl fun ζ hζ => ?_
          rw [hα₃eq p hp ζ hζ, mul_assoc]
      _ = ∑ ζ ∈ T, α₃ ζ * ‖∑ n ∈ W, y₃ n * (ζ ^ j) ^ n‖ := by
          rw [hT, sum_biUnion hdisj]
          refine sum_congr rfl fun p _ => sum_congr rfl fun ζ _ => ?_
          rw [cubicRowTransform_eq_window hsupp' hAL]
      _ ≤ Real.sqrt (∑ ζ ∈ T, α₃ ζ ^ 2) *
            Real.sqrt (∑ ζ ∈ T, ‖∑ n ∈ W, y₃ n * (ζ ^ j) ^ n‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt T _ _
      _ ≤ Real.sqrt (∑ ζ ∈ T, α₃ ζ ^ 2) * Real.sqrt ((j : ℝ) * (X * Y₃)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hls) (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑ ζ ∈ T, α₃ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₃) * Real.sqrt j := by
          rw [Real.sqrt_mul hjR.le, Real.sqrt_mul hX]; ring
  set t₃ : ℕ → ℕ → ℝ := fun p j =>
    (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
      (2 * cubicPotential p ((j + 1) * n) - residuePotential p ((j + 1) * n))) *
      (1 / ((j : ℝ) + 1) ^ 3)
  have htend : Tendsto (fun K : ℕ => ∑ p ∈ S, |c p| / p * |∑ j ∈ range K, t₃ p j|) atTop
      (𝓝 (∑ p ∈ S, |c p| / p * |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel p n|)) := by
    refine tendsto_finsetSum S fun p hp => ?_
    exact ((hasSum_sum_mul_cubicKernel (hS p hp).1.pos N c').tendsto_sum_nat.abs).const_mul _
  refine le_of_tendsto' htend fun K => ?_
  calc ∑ p ∈ S, |c p| / p * |∑ j ∈ range K, t₃ p j|
      ≤ ∑ j ∈ range K, (1 / ((j : ℝ) + 1) ^ 3) *
          ∑ p ∈ S, |c p| / p *
            |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
              (2 * cubicPotential p ((j + 1) * n) - residuePotential p ((j + 1) * n))| := by
        calc ∑ p ∈ S, |c p| / p * |∑ j ∈ range K, t₃ p j|
            ≤ ∑ p ∈ S, ∑ j ∈ range K, |c p| / p * |t₃ p j| := by
              refine sum_le_sum fun p hp => ?_
              have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
              rw [← mul_sum]
              exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
          _ = ∑ j ∈ range K, (1 / ((j : ℝ) + 1) ^ 3) *
                ∑ p ∈ S, |c p| / p *
                  |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
                    (2 * cubicPotential p ((j + 1) * n) - residuePotential p ((j + 1) * n))| := by
              rw [sum_comm]
              refine sum_congr rfl fun j _ => ?_
              rw [mul_sum]
              refine sum_congr rfl fun p _ => ?_
              simp only [t₃]
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 3)]
              ring
    _ ≤ ∑ j ∈ range K, Real.sqrt (∑ ζ ∈ T, α₃ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₃) *
          (Real.sqrt (j + 1 : ℕ) / ((j + 1 : ℕ) : ℝ) ^ 3) := by
        refine sum_le_sum fun j _ => ?_
        have h := mul_le_mul_of_nonneg_left (hjbound (j + 1) (by omega))
          (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 3)
        refine h.trans (le_of_eq ?_)
        push_cast
        ring
    _ = Real.sqrt (∑ ζ ∈ T, α₃ ζ ^ 2) * (Real.sqrt X * Real.sqrt Y₃) *
          ∑ j ∈ Icc 1 K, Real.sqrt j / (j : ℝ) ^ 3 := by
        rw [← mul_sum]
        congr 1
        induction K with
        | zero => simp
        | succ K ih => rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]
    _ ≤ 1 / 16 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 4) * (Real.sqrt X * Real.sqrt Y₃) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hα₃sum (by positivity))
          (sum_Icc_sqrt_div_cube_le K) (sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = 1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 4) * Real.sqrt X * Real.sqrt Y₃ := by ring

/-- **Fourth-order large-sieve dispersion of the weighted dual norm `Σ_{p ∈ S} (|c(p)|/p) |Λ_p(c')|`.** -/
theorem sum_abs_kernelStatistic_le_largeSieve {N Q₀ A L : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) (c c' : ℕ → ℝ)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    ∑ p ∈ S, |c p| / p * |kernelStatistic N c' p| ≤
      1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 4) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) := by
  calc ∑ p ∈ S, |c p| / p * |kernelStatistic N c' p|
      ≤ ∑ p ∈ S, |c p| / p *
          |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p)| +
        ∑ p ∈ S, |c p| / p * |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel p n| := by
        rw [← sum_add_distrib]
        refine sum_le_sum fun p hp => ?_
        have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
        rw [← mul_add, kernelStatistic, sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ ≤ _ := add_le_add
        (sum_abs_mul_bernoulliKernel_sub_mean_le_largeSieve hQ₀ hS c c' hsupp' hAL)
        (sum_abs_mul_cubicKernel_le_largeSieve hQ₀ hS c c' hsupp' hAL)

/-- **Large-sieve dispersion of the `ℓ¹` dual norm `Σ_{p ∈ S} |Λ_p(c')|/p`.** -/
theorem dual_norm_kernelStatistic_le_largeSieve {N Q₀ A L : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) (c' : ℕ → ℝ)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    ∑ p ∈ S, |kernelStatistic N c' p| / p ≤
      1 / 2 * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 4) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) := by
  have h := sum_abs_kernelStatistic_le_largeSieve hQ₀ hS (fun _ => 1) c' hsupp' hAL
  simpa [div_eq_mul_inv, mul_comm] using h

/-- **Fourth-order large-sieve dispersion of the cross-scale functional.** -/
theorem abs_rowBilinear_sub_equidistributedMain_le_fourthOrder_largeSieve
    {N Q₀ A L : ℕ} {S : Finset ℕ} (hQ₀ : 2 ≤ Q₀)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) {c c' : ℕ → ℝ}
    (hsupp : ∀ d, c d ≠ 0 → d ∈ S)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c'| ≤
      1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 4) *
          Real.sqrt ((L : ℝ) + (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 6) +
        6 * (∑ p ∈ S, |c p| * (p : ℝ) ^ 3) *
          ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 4 := by
  have hSI : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2.1⟩
  have hWN : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  have hlaw := abs_rowBilinear_sub_kernelStatistic_le N c' (c := c)
    (fun d hd => (hS d (hsupp d hd)).1)
  have hcube : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3 = ∑ p ∈ S, |c p| * (p : ℝ) ^ 3 := by
    rw [← sum_subset hSI fun d _ hd => by
      have : c d = 0 := by by_contra h; exact hd (hsupp d h)
      simp [this]]
  have hquart : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 =
      ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 4 := by
    rw [← sum_subset hWN fun n _ hn => by
      have : c' n = 0 := by by_contra h; exact hn (hsupp' n h)
      simp [this]]
  have hstat : |∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d| ≤
      ∑ p ∈ S, |c p| / p * |kernelStatistic N c' p| := by
    rw [← sum_subset hSI fun d _ hd => by
      have : c d = 0 := by by_contra h; exact hd (hsupp d h)
      simp [this]]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    rw [abs_mul, abs_div, abs_of_pos hpR]
  have hls := sum_abs_kernelStatistic_le_largeSieve hQ₀ hS c c' hsupp' hAL
  rw [hcube, hquart] at hlaw
  have key := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c')
    (∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d)
  linarith

/-- **Hypothesis-free large-sieve dispersion of the `ℓ¹` dual norm over all primes `≤ N`.** Valid
for all `N : ℕ` and all `c' : ℕ → ℝ` with zero side conditions. -/
theorem dual_norm_kernelStatistic_prime_filter_le_largeSieve (N : ℕ) (c' : ℕ → ℝ) :
    ∑ p ∈ (Icc 1 N).filter Nat.Prime, |kernelStatistic N c' p| / p ≤
      1 / 2 * Real.sqrt (∑ p ∈ (Icc 1 N).filter Nat.Prime, (p : ℝ) ^ 2) *
          Real.sqrt ((N : ℝ) + (max N 2 : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 8 * Real.sqrt (∑ p ∈ (Icc 1 N).filter Nat.Prime, (p : ℝ) ^ 4) *
          Real.sqrt ((N : ℝ) + (max N 2 : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 6) := by
  set c'₀ : ℕ → ℝ := fun n => if n ∈ Icc 1 N then c' n else 0
  have hstat : ∀ p, kernelStatistic N c' p = kernelStatistic N c'₀ p := fun p => by
    unfold kernelStatistic
    exact sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
  have hsq4 : ∑ n ∈ Icc (0 + 1) (0 + N), c'₀ n ^ 2 / (n : ℝ) ^ 4 =
      ∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 4 := by
    rw [zero_add, zero_add]
    exact sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
  have hsq6 : ∑ n ∈ Icc (0 + 1) (0 + N), c'₀ n ^ 2 / (n : ℝ) ^ 6 =
      ∑ n ∈ Icc 1 N, c' n ^ 2 / (n : ℝ) ^ 6 := by
    rw [zero_add, zero_add]
    exact sum_congr rfl fun n hn => by simp only [c'₀, if_pos hn]
  have h := dual_norm_kernelStatistic_le_largeSieve (N := N) (Q₀ := max N 2) (A := 0) (L := N)
    (S := (Icc 1 N).filter Nat.Prime) (le_max_right N 2)
    (fun p hp => by
      obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
      exact ⟨hpP, (mem_Icc.mp hpI).2, (mem_Icc.mp hpI).2.trans (le_max_left N 2)⟩)
    c'₀ (fun n hn => by
      rw [zero_add, zero_add]
      by_contra hnot
      exact hn (by simp only [c'₀, if_neg hnot])) (by omega)
  simp_rw [← hstat] at h
  rw [hsq4, hsq6, Nat.cast_max, Nat.cast_ofNat] at h
  exact h

end

end GaloisForLFunctions.BezoutValuationIncidence
