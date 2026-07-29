import Mathlib

/-!
# An anisotropic Gaussian-rational mesh for transverse pole detection

The mesh has horizontal spacing `1/n` and vertical spacing `1/n^2`.  For every complex target
`sigma`, an explicit ceiling/floor choice produces a mesh point whose horizontal displacement is
between `1/n` and `2/n`, while its vertical displacement has norm below `1/n^2`.

This geometry is independent of Xi.  Its role in the top-down RH chain is to approach a hypothetical
left-half-strip source pole from a uniformly positive transverse direction without making any
Diophantine assumption on the pole ordinate.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- The `1/n` by `1/n^2` Gaussian-rational mesh. -/
def xiTaylorAnisotropicMeshPoint (n : ℕ) (a b : ℤ) : ℂ :=
  Complex.ofReal ((a : ℝ) / (n : ℝ)) +
    Complex.ofReal ((b : ℝ) / (n : ℝ) ^ 2) * I

/-- The explicit mesh point immediately to the right of `sigma`, with a finer vertical floor. -/
def xiTaylorAnisotropicRightApprox (sigma : ℂ) (n : ℕ) : ℂ :=
  xiTaylorAnisotropicMeshPoint n
    (Int.ceil ((n : ℝ) * sigma.re) + 1)
    (Int.floor ((n : ℝ) ^ 2 * sigma.im))

@[simp] theorem xiTaylorAnisotropicMeshPoint_re (n : ℕ) (a b : ℤ) :
    (xiTaylorAnisotropicMeshPoint n a b).re = (a : ℝ) / (n : ℝ) := by
  rw [xiTaylorAnisotropicMeshPoint, add_re, mul_re, Complex.ofReal_re,
    Complex.ofReal_im, I_re, I_im]
  ring

@[simp] theorem xiTaylorAnisotropicMeshPoint_im (n : ℕ) (a b : ℤ) :
    (xiTaylorAnisotropicMeshPoint n a b).im = (b : ℝ) / (n : ℝ) ^ 2 := by
  rw [xiTaylorAnisotropicMeshPoint, add_im, mul_im, Complex.ofReal_re,
    Complex.ofReal_im, I_re, I_im]
  ring

/-- The chosen mesh point is horizontally between `1/n` and `2/n` to the right of `sigma`. -/
theorem xiTaylorAnisotropicRightApprox_re_sub_bounds
    (sigma : ℂ) {n : ℕ} (hn : 0 < n) :
    1 / (n : ℝ) ≤ (xiTaylorAnisotropicRightApprox sigma n - sigma).re ∧
      (xiTaylorAnisotropicRightApprox sigma n - sigma).re < 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlo := Int.le_ceil ((n : ℝ) * sigma.re)
  have hhi := Int.ceil_lt_add_one ((n : ℝ) * sigma.re)
  rw [xiTaylorAnisotropicRightApprox, sub_re,
    xiTaylorAnisotropicMeshPoint_re]
  have hrepr :
      ((Int.ceil ((n : ℝ) * sigma.re) + 1 : ℤ) : ℝ) / (n : ℝ) - sigma.re =
        ((((Int.ceil ((n : ℝ) * sigma.re) + 1 : ℤ) : ℝ) -
          (n : ℝ) * sigma.re) / (n : ℝ)) := by
    field_simp
  rw [hrepr]
  constructor
  · rw [div_le_div_iff_of_pos_right hnR]
    push_cast
    linarith
  · rw [div_lt_div_iff_of_pos_right hnR]
    push_cast
    linarith

/-- The vertical error of the chosen mesh point is strictly smaller than `1/n^2`. -/
theorem abs_xiTaylorAnisotropicRightApprox_im_sub_lt
    (sigma : ℂ) {n : ℕ} (hn : 0 < n) :
    |(xiTaylorAnisotropicRightApprox sigma n - sigma).im| <
      1 / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hlo := Int.floor_le ((n : ℝ) ^ 2 * sigma.im)
  have hhi := Int.lt_floor_add_one ((n : ℝ) ^ 2 * sigma.im)
  rw [xiTaylorAnisotropicRightApprox, sub_im,
    xiTaylorAnisotropicMeshPoint_im]
  have hrepr :
      ((Int.floor ((n : ℝ) ^ 2 * sigma.im) : ℤ) : ℝ) / (n : ℝ) ^ 2 - sigma.im =
        ((((Int.floor ((n : ℝ) ^ 2 * sigma.im) : ℤ) : ℝ) -
          (n : ℝ) ^ 2 * sigma.im) / (n : ℝ) ^ 2) := by
    field_simp
  rw [hrepr]
  have hnumLow : (-1 : ℝ) <
      ((Int.floor ((n : ℝ) ^ 2 * sigma.im) : ℤ) : ℝ) -
        (n : ℝ) ^ 2 * sigma.im := by
    linarith
  have hnumHigh :
      ((Int.floor ((n : ℝ) ^ 2 * sigma.im) : ℤ) : ℝ) -
        (n : ℝ) ^ 2 * sigma.im ≤ 0 := by
    linarith
  rw [abs_lt]
  constructor
  · rw [show -(1 / (n : ℝ) ^ 2) = (-1 : ℝ) / (n : ℝ) ^ 2 by ring,
      div_lt_div_iff_of_pos_right hn2]
    exact hnumLow
  · rw [div_lt_div_iff_of_pos_right hn2]
    linarith

/-- Any displacement with the anisotropic mesh geometry has reciprocal real part growing at
least linearly: `n / 5 < Re (delta⁻¹)`.  This is the quantitative pole amplifier used by the
sublinear-flux RH criterion. -/
theorem nat_div_five_lt_inv_re_of_anisotropic
    {delta : ℂ} {n : ℕ} (hn : 0 < n)
    (hxlo : 1 / (n : ℝ) ≤ delta.re)
    (hxhi : delta.re < 2 / (n : ℝ))
    (hy : |delta.im| < 1 / (n : ℝ) ^ 2) :
    (n : ℝ) / 5 < delta⁻¹.re := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (n : ℝ)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu_le_one : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one hnR]
    exact_mod_cast hn
  have hx0 : 0 < delta.re := lt_of_lt_of_le hu hxlo
  have hx2 : delta.re ^ 2 < (2 * u) ^ 2 := by
    apply (sq_lt_sq₀ hx0.le (by positivity)).2
    simpa [u, div_eq_mul_inv] using hxhi
  have hy2 : delta.im ^ 2 < (u ^ 2) ^ 2 := by
    have h := (sq_lt_sq₀ (abs_nonneg delta.im) (sq_nonneg u)).2
    have habs2 := h (by simpa [u, div_pow] using hy)
    rwa [sq_abs] at habs2
  have hu4 : u ^ 4 ≤ u ^ 2 := by
    nlinarith [sq_nonneg u, sq_nonneg (u ^ 2 - u)]
  have hnorm : Complex.normSq delta < 5 * u ^ 2 := by
    rw [Complex.normSq_apply]
    nlinarith
  have hnormPos : 0 < Complex.normSq delta := by
    rw [Complex.normSq_pos]
    exact ne_of_apply_ne Complex.re (ne_of_gt hx0)
  rw [Complex.inv_re, lt_div_iff₀ hnormPos]
  calc
    (n : ℝ) / 5 * Complex.normSq delta <
        (n : ℝ) / 5 * (5 * u ^ 2) := by
      exact mul_lt_mul_of_pos_left hnorm (by positivity)
    _ = u := by
      dsimp [u]
      field_simp
    _ ≤ delta.re := hxlo

/-- A positive `1/n` real displacement bounds the reciprocal norm by `n`. -/
theorem norm_inv_le_nat_of_inv_nat_le_re
    {delta : ℂ} {n : ℕ} (hn : 0 < n)
    (hxlo : 1 / (n : ℝ) ≤ delta.re) :
    ‖delta⁻¹‖ ≤ (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hxpos : 0 < delta.re := lt_of_lt_of_le (by positivity) hxlo
  have hnorm : 1 / (n : ℝ) ≤ ‖delta‖ :=
    hxlo.trans ((le_abs_self delta.re).trans (Complex.abs_re_le_norm delta))
  rw [norm_inv]
  calc
    ‖delta‖⁻¹ = 1 / ‖delta‖ := by rw [one_div]
    _ ≤ 1 / (1 / (n : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hnorm
    _ = (n : ℝ) := by field_simp

/-- The explicit right-approximating mesh sequence converges to its target through the punctured
neighborhood.  Thus it may be composed directly with normalized logarithmic-residue limits. -/
theorem tendsto_xiTaylorAnisotropicRightApprox_succ
    (sigma : ℂ) :
    Tendsto (fun n : ℕ => xiTaylorAnisotropicRightApprox sigma (n + 1)) atTop
      (nhdsWithin sigma ({sigma}ᶜ)) := by
  have hdist : ∀ n : ℕ,
      ‖xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma‖ <
        3 * (1 / ((n : ℝ) + 1)) := by
    intro n
    let N : ℕ := n + 1
    have hN : 0 < N := by dsimp [N]; omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hre := xiTaylorAnisotropicRightApprox_re_sub_bounds sigma hN
    have him := abs_xiTaylorAnisotropicRightApprox_im_sub_lt sigma hN
    have hinvSq : 1 / (N : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
      apply one_div_le_one_div_of_le hNR
      nlinarith
    have hreNonneg : 0 ≤ (xiTaylorAnisotropicRightApprox sigma N - sigma).re :=
      le_trans (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)) hre.1
    calc
      ‖xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma‖ =
          ‖xiTaylorAnisotropicRightApprox sigma N - sigma‖ := by rfl
      _ ≤ |(xiTaylorAnisotropicRightApprox sigma N - sigma).re| +
          |(xiTaylorAnisotropicRightApprox sigma N - sigma).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = (xiTaylorAnisotropicRightApprox sigma N - sigma).re +
          |(xiTaylorAnisotropicRightApprox sigma N - sigma).im| := by
        rw [abs_of_nonneg hreNonneg]
      _ < 2 / (N : ℝ) + 1 / (N : ℝ) :=
        add_lt_add hre.2 (him.trans_le hinvSq)
      _ = 3 * (1 / ((n : ℝ) + 1)) := by
        dsimp [N]
        push_cast
        ring
  have hnorm : Tendsto
      (fun n : ℕ => ‖xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma‖)
      atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall fun n => (hdist n).le)
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3
  have htend : Tendsto
      (fun n : ℕ => xiTaylorAnisotropicRightApprox sigma (n + 1))
      atTop (nhds sigma) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  rw [tendsto_nhdsWithin_iff]
  refine ⟨htend, Eventually.of_forall fun n => ?_⟩
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro heq
  have hre := (xiTaylorAnisotropicRightApprox_re_sub_bounds sigma
    (show 0 < n + 1 by omega)).1
  rw [heq, sub_self, zero_re] at hre
  have : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  linarith

end

end RHTower
