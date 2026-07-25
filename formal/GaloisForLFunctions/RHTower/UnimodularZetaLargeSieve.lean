/-
# The unimodular large sieve for Dirichlet characters, and Montgomery's large-value bound

For a finite frequency set `W` and unimodular weights `c` write `Ψ(n) = ∑_{t ∈ W} c_t n^{-it}`.
The *unimodular large sieve* at scale `N` is the `ℓ^∞ → ℓ²` operator-norm bound

  `∑_{n ∈ [N,2N]} |Ψ(n)|² ≤ B · |W|`.

Two consequences are proved here, both unconditional and purely algebraic.

* `montgomery_of_uzls`: for any matrix with `ℓ^∞`-normalised input, the unimodular large sieve
  forces `|W| · V² ≤ N · B` for every uniform lower bound `V` on the values of the associated
  Dirichlet polynomial.  With `B = N^{1+ε}` this reads `|W| ≤ N^{2+ε} / V²`, Montgomery's
  large-value bound.  The `ℓ^∞` hypothesis on the coefficients is used exactly once.

* `dirichletChar_mul`: the multiplicative dilation identity `(em)^{-it} = e^{-it} · m^{-it}`.
  Restricting the sum over `n ∈ [N,2N]` to multiples of `e` therefore produces the same kind of
  sum at scale `N/e`, with the same frequency set and with the weights twisted by the unimodular
  factor `e^{-it}`; the estimate is thus invariant under multiplicative dilation.
-/
import Mathlib

open Finset

namespace GaloisForLFunctions
namespace RHTower
namespace UZLS

/-- **UZLS ⟹ Montgomery's large-value bound** (abstract matrix form).

`M : ι → κ → ℂ` plays the role of the Dirichlet matrix `M n t = n^{-it}`, `b` is an
`ℓ^∞`-normalised coefficient vector (`‖b n‖ ≤ 1`), and the hypothesis is the `ℓ^∞ → ℓ²` operator-norm
bound `∑_n ‖∑_t c_t M n t‖² ≤ B · |κ|` valid for every `ℓ^∞`-normalised `c`.

If the Dirichlet polynomial `t ↦ ∑_n b n · M n t` has norm at least `V` at *every* `t ∈ κ`, then
`|κ| · V² ≤ |ι| · B`. -/
theorem montgomery_of_uzls
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (b : ι → ℂ)
    (hb : ∀ n, ‖b n‖ ≤ 1)
    (B V : ℝ) (hV : 0 ≤ V) (hB0 : 0 ≤ B)
    (hUZLS : ∀ c : κ → ℂ, (∀ t, ‖c t‖ ≤ 1) →
        ∑ n : ι, ‖∑ t : κ, c t * M n t‖ ^ 2 ≤ B * (Fintype.card κ))
    (hlarge : ∀ t : κ, V ≤ ‖∑ n : ι, b n * M n t‖) :
    (Fintype.card κ : ℝ) * V ^ 2 ≤ (Fintype.card ι : ℝ) * B := by
  classical
  set D : κ → ℂ := fun t => ∑ n : ι, b n * M n t with hDdef
  set u : κ → ℂ := fun t => if D t = 0 then 0 else (starRingEnd ℂ) (D t) / (‖D t‖ : ℂ) with hudef
  have hu : ∀ t, ‖u t‖ ≤ 1 := by
    intro t
    by_cases h : D t = 0
    · simp [hudef, h]
    · simp [hudef, h, Complex.norm_real]
  have hkey : ∀ t, u t * D t = ((‖D t‖ : ℝ) : ℂ) := by
    intro t
    by_cases h : D t = 0
    · simp [hudef, h]
    · have hn : ((‖D t‖ : ℝ) : ℂ) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using h
      have h1 : u t * D t = ((starRingEnd ℂ) (D t) * D t) / ((‖D t‖ : ℝ) : ℂ) := by
        simp [hudef, h, div_mul_eq_mul_div]
      rw [h1, Complex.conj_mul']
      field_simp
  set Φ : ι → ℂ := fun n => ∑ t : κ, u t * M n t with hΦdef
  have hA : ∑ t : κ, ((‖D t‖ : ℝ) : ℂ) = ∑ n : ι, b n * Φ n := by
    have h2 : ∑ t : κ, u t * D t = ∑ n : ι, b n * Φ n := by
      simp only [hDdef, hΦdef, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun t _ => by ring
    rw [← h2]
    exact Finset.sum_congr rfl fun t _ => (hkey t).symm
  have h0 : (0:ℝ) ≤ ∑ t : κ, ‖D t‖ := Finset.sum_nonneg fun t _ => norm_nonneg _
  have hAreal : ∑ t : κ, ‖D t‖ = ‖∑ n : ι, b n * Φ n‖ := by
    have hcast : ((∑ t : κ, ‖D t‖ : ℝ) : ℂ) = ∑ n : ι, b n * Φ n := by push_cast; exact hA
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  have hBstep : (Fintype.card κ : ℝ) * V ≤ ∑ t : κ, ‖D t‖ := by
    calc (Fintype.card κ : ℝ) * V = ∑ _t : κ, V := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ t : κ, ‖D t‖ := Finset.sum_le_sum fun t _ => hlarge t
  -- the only place the `ℓ^∞` normalisation `‖b n‖ ≤ 1` is used
  have hC : ∑ t : κ, ‖D t‖ ≤ ∑ n : ι, ‖Φ n‖ := by
    rw [hAreal]
    calc ‖∑ n : ι, b n * Φ n‖ ≤ ∑ n : ι, ‖b n * Φ n‖ := norm_sum_le _ _
      _ = ∑ n : ι, ‖b n‖ * ‖Φ n‖ := by simp
      _ ≤ ∑ n : ι, 1 * ‖Φ n‖ := Finset.sum_le_sum fun n _ =>
            mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _)
      _ = ∑ n : ι, ‖Φ n‖ := by simp
  have hD2 : (∑ n : ι, ‖Φ n‖) ^ 2 ≤ (Fintype.card ι : ℝ) * (B * (Fintype.card κ : ℝ)) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun _ => (1 : ℝ)) (fun n => ‖Φ n‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
    refine hcs.trans ?_
    exact mul_le_mul_of_nonneg_left (hUZLS u hu) (Nat.cast_nonneg _)
  have hle : (Fintype.card κ : ℝ) * V ≤ ∑ n : ι, ‖Φ n‖ := hBstep.trans hC
  have hnn : (0:ℝ) ≤ (Fintype.card κ : ℝ) * V := mul_nonneg (Nat.cast_nonneg _) hV
  have hcombine :
      ((Fintype.card κ : ℝ) * V) ^ 2 ≤ (Fintype.card ι : ℝ) * (B * (Fintype.card κ : ℝ)) := by
    nlinarith [hle, hnn, hD2]
  rcases Nat.eq_zero_or_pos (Fintype.card κ) with hk | hk
  · have hz : (Fintype.card κ : ℝ) = 0 := by exact_mod_cast hk
    rw [hz]
    simpa using mul_nonneg (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ) ≤ _) hB0
  · have hkpos : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hk
    nlinarith [hcombine, hkpos]

/-- The Dirichlet character `n ↦ n^{-it}` used by the large-value problem. -/
noncomputable def dirichletChar (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) * Complex.I * (Real.log n : ℂ))

/-- The entries of the Dirichlet matrix are unimodular. -/
theorem norm_dirichletChar (n : ℕ) (t : ℝ) : ‖dirichletChar n t‖ = 1 := by
  have hre : (-(t : ℂ) * Complex.I * ((Real.log n : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [dirichletChar, Complex.norm_exp, hre, Real.exp_zero]

/-- Multiplicative dilation: `(em)^{-it} = e^{-it} · m^{-it}`, so restricting the sum at scale `N`
to the multiples of `e` gives the same sum at scale `N/e` with the same frequency set and the
weights twisted by the unimodular factor `e^{-it}`.  This is the
source of the scale invariance of the estimate. -/
theorem dirichletChar_mul {e m : ℕ} (he : 0 < e) (hm : 0 < m) (t : ℝ) :
    dirichletChar (e * m) t = dirichletChar e t * dirichletChar m t := by
  have hlog : Real.log ((e * m : ℕ) : ℝ) = Real.log (e : ℝ) + Real.log (m : ℝ) := by
    push_cast
    exact Real.log_mul (by positivity) (by positivity)
  simp only [dirichletChar, hlog]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end UZLS
end RHTower
end GaloisForLFunctions
