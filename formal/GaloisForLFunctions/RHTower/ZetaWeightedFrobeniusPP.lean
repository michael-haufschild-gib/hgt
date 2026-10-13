import GaloisForLFunctions.RHTower.ZetaJacksonProductWindow

/-!
# The prime–prime part of the weighted Frobenius norm: algebraic expansion

For real coefficients `c_n` and complex numbers `z_n`, `(Σ_n c_n Re z_n)² = ½ Σ_{n,m} c_n c_m (Re(z_n z̄_m) + Re(z_n z_m))`
(`sq_sum_mul_re_eq`).  Applied entrywise to the closed form `G^P_kl = −2 Σ_n a_n Re[e^{iy_nτ_l} A_n(τ_k − τ_l)]`, the
weighted prime–prime Frobenius sum splits into difference frequencies `y_n − y_m` and sum frequencies `y_n + y_m`
(`weighted_sq_sum_mul_re_eq`):

`Σ_{k,l} W_k W_l (Σ_n c_n Re z_n(k,l))² = ½ Σ_{n,m} c_n c_m Σ_{k,l} W_k W_l (Re(z_n z̄_m) + Re(z_n z_m))(k,l)`.
-/

open Finset

noncomputable section

namespace RHTower

/-- `Re a · Re b = ½ (Re(a b̄) + Re(a b))`. -/
theorem re_mul_re_eq_half (a b : ℂ) : a.re * b.re = ((a * starRingEnd ℂ b).re + (a * b).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- `(Σ_n c_n Re z_n)² = ½ Σ_{n,m} c_n c_m (Re(z_n z̄_m) + Re(z_n z_m))`. -/
theorem sq_sum_mul_re_eq {ι : Type*} (s : Finset ι) (c : ι → ℝ) (z : ι → ℂ) :
    (∑ n ∈ s, c n * (z n).re) ^ 2
      = ∑ n ∈ s, ∑ m ∈ s, c n * c m * (((z n * starRingEnd ℂ (z m)).re + (z n * z m).re) / 2) := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [← re_mul_re_eq_half]
  ring

/-- **Weighted expansion of the prime–prime Frobenius sum.** -/
theorem weighted_sq_sum_mul_re_eq {κ ι : Type*} (S : Finset κ) (s : Finset ι) (W : κ → ℝ) (c : ι → ℝ)
    (z : ι → κ → κ → ℂ) :
    ∑ k ∈ S, ∑ l ∈ S, W k * W l * (∑ n ∈ s, c n * (z n k l).re) ^ 2
      = ∑ n ∈ s, ∑ m ∈ s, c n * c m * (∑ k ∈ S, ∑ l ∈ S,
          W k * W l * (((z n k l * starRingEnd ℂ (z m k l)).re + (z n k l * z m k l).re) / 2)) := by
  have h1 : ∀ k l, W k * W l * (∑ n ∈ s, c n * (z n k l).re) ^ 2
      = ∑ n ∈ s, ∑ m ∈ s, c n * c m * (W k * W l
          * (((z n k l * starRingEnd ℂ (z m k l)).re + (z n k l * z m k l).re) / 2)) := by
    intro k l
    rw [sq_sum_mul_re_eq s c (fun n => z n k l), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => h1 k l]
  have h2 : ∀ n m, c n * c m * (∑ k ∈ S, ∑ l ∈ S, W k * W l
        * (((z n k l * starRingEnd ℂ (z m k l)).re + (z n k l * z m k l).re) / 2))
      = ∑ k ∈ S, ∑ l ∈ S, c n * c m * (W k * W l
        * (((z n k l * starRingEnd ℂ (z m k l)).re + (z n k l * z m k l).re) / 2)) := by
    intro n m
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => h2 n m]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end RHTower
