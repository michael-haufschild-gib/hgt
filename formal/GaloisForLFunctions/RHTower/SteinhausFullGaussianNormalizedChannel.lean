import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorModes
import GaloisForLFunctions.RHTower.SteinhausCofactorPrimeBlocks


open Finset Complex
noncomputable section
namespace RHTower

/-- The full Gaussian channel after removing the node's conductor factor. -/
def normalizedFullGaussianCofactorChannel {J : ℕ} (s : Fin J → ℂ) (R : ℝ)
    (ω : SteinhausModel.Omega) : Fin J → ℂ :=
  fun j => (R : ℂ) * fullGaussianCofactorNodeVector s R ω j

/-- The complete normalized channel retains exactly the real cofactor scale and common phase. -/
theorem normalizedFullGaussianCofactorChannel_eq_mode {J : ℕ} (s : Fin J → ℂ)
    (t : ℝ) {A : ℂ} (hA : A ≠ 0) {R : ℝ} (hR : 0 < R)
    (ω : SteinhausModel.Omega) (j : Fin J) :
    normalizedFullGaussianCofactorChannel s R ω j =
      ((R : ℂ) * A * (R : ℂ) ^ ((t : ℂ) * I)) *
        relativeFullGaussianCofactorMode s t A R ω j := by
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hpow : (R : ℂ) ^ ((t : ℂ) * I) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hRC)
  simp only [normalizedFullGaussianCofactorChannel, relativeFullGaussianCofactorMode,
    Pi.smul_apply, smul_eq_mul, Complex.cpow_neg]
  field_simp

/-- Pairing a full normalized channel removes the common coherent phase without loss. -/
theorem norm_normalizedFullGaussianCofactorChannel_dot_eq {J : ℕ} (s : Fin J → ℂ)
    (t : ℝ) {A : ℂ} (hA : A ≠ 0) {R : ℝ} (hR : 0 < R)
    (ω : SteinhausModel.Omega) (u : Fin J → ℂ) :
    ‖∑ j, normalizedFullGaussianCofactorChannel s R ω j * u j‖ =
      R * ‖A‖ * ‖∑ j, relativeFullGaussianCofactorMode s t A R ω j * u j‖ := by
  have heq : (∑ j, normalizedFullGaussianCofactorChannel s R ω j * u j) =
      ((R : ℂ) * A * (R : ℂ) ^ ((t : ℂ) * I)) *
        (∑ j, relativeFullGaussianCofactorMode s t A R ω j * u j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [normalizedFullGaussianCofactorChannel_eq_mode s t hA hR ω j]
    ring
  rw [heq, norm_mul]
  simp only [norm_mul, Complex.norm_of_nonneg hR.le,
    Complex.norm_cpow_eq_rpow_re_of_pos hR, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_self,
    Real.rpow_zero, mul_one]

/-- The existing reciprocal prime blocks already control the exact real cofactor scales. -/
theorem cofactorPrimeBlock_real_scale_bounds {M N p : ℕ} (hM : 0 < M)
    (hp : p ∈ cofactorPrimeBlock M N) :
    (M : ℝ) ≤ (N : ℝ) / p ∧ (N : ℝ) / p < 2 * (M : ℝ) := by
  obtain ⟨hpp, hlo, hhi⟩ := cofactorPrimeBlock_mem_bounds hM hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  constructor
  · apply (le_div_iff₀ hpR).mpr
    exact_mod_cast (Nat.le_div_iff_mul_le hpp.pos).mp hlo
  · apply (div_lt_iff₀ hpR).mpr
    exact_mod_cast (Nat.div_lt_iff_lt_mul hpp.pos).mp hhi

/-- Exact conductor normalization of a full Gaussian prime channel; no floor factor remains. -/
theorem fullGaussian_prime_channel_factor {J : ℕ} (s : Fin J → ℂ)
    {N p : ℝ} (hN : 0 < N) (hp : 0 < p) (ω : SteinhausModel.Omega) (j : Fin J) :
    (p : ℂ) ^ (s j - 1) * steinhausFullGaussianCofactor (s j) (N / p) ω =
      (N : ℂ) ^ (s j - 1) * normalizedFullGaussianCofactorChannel s (N / p) ω j := by
  let R : ℝ := N / p
  have hR : 0 < R := div_pos hN hp
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hNR : N = p * R := by dsimp only [R]; field_simp
  have hpowers : (R : ℂ) ^ (s j - 1) * (R : ℂ) * (R : ℂ) ^ (-s j) = 1 := by
    calc
      _ = (R : ℂ) ^ (s j - 1) * (R : ℂ) ^ (1 : ℂ) * (R : ℂ) ^ (-s j) := by
        rw [Complex.cpow_one]
      _ = (R : ℂ) ^ ((s j - 1) + 1 + (-s j)) := by
        rw [← Complex.cpow_add _ _ hRC, ← Complex.cpow_add _ _ hRC]
      _ = 1 := by rw [show (s j - 1) + 1 + (-s j) = 0 by ring, Complex.cpow_zero]
  change (p : ℂ) ^ (s j - 1) * steinhausFullGaussianCofactor (s j) R ω =
    (N : ℂ) ^ (s j - 1) * ((R : ℂ) *
      (steinhausFullGaussianCofactor (s j) R ω * (R : ℂ) ^ (-s j)))
  conv_rhs => rw [hNR, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hp.le hR.le]
  calc
    _ = ((p : ℂ) ^ (s j - 1) * steinhausFullGaussianCofactor (s j) R ω) *
        ((R : ℂ) ^ (s j - 1) * (R : ℂ) * (R : ℂ) ^ (-s j)) := by rw [hpowers, mul_one]
    _ = _ := by ring

end RHTower
