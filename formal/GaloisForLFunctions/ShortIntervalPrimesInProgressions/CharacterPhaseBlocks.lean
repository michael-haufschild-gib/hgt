import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel
import Mathlib.Analysis.Fourier.ZMod

/-!
# Dyadic blocks of a twisted Dirichlet series

For a Dirichlet character `χ` modulo `q`, a run of `L ≤ N + 1` consecutive terms
`Σ_{N ≤ n < N + L} χ(n) n^{-it}` obeys the `k`-th derivative test bound of the untwisted series,
with an extra factor `q` (`norm_character_block_le`).

The character is a combination of the additive characters `n ↦ e(jn/q)` with coefficients of
modulus at most `1` (finite Fourier inversion on `ZMod q`), and the phase
`-(t/2π) log x + (j/q) x` of `e(jn/q) n^{-it}` has the same derivatives of order `≥ 2` as the
logarithmic phase: the linear twist disappears from the `k`-th derivative test
(`norm_twisted_block_le`).
-/

open Complex Finset RHTower.Sieve

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

/-- The derivative chain of the twisted phase `-(t/2π) log x + a x`. -/
def twistChain (t a : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => logPhaseChain t 0 x + a * x
  | 1 => fun x => logPhaseChain t 1 x + a
  | (i + 2) => logPhaseChain t (i + 2)

theorem twistChain_of_two_le (t a : ℝ) {i : ℕ} (hi : 2 ≤ i) :
    twistChain t a i = logPhaseChain t i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rfl

theorem twistChain_hasDerivAt (t a : ℝ) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (twistChain t a i) (twistChain t a (i + 1) x) x := by
  match i with
  | 0 =>
    have h := (logPhaseChain_hasDerivAt t 0 hx).add ((hasDerivAt_id x).const_mul a)
    simp only [id, mul_one] at h
    exact h
  | 1 =>
    have h := (logPhaseChain_hasDerivAt t 1 hx).add_const a
    simpa [twistChain] using h
  | (i + 2) => exact logPhaseChain_hasDerivAt t (i + 2) hx

/-- `e(a n) n^{-it}` is the phase `e(g(n))` of the twisted chain. -/
theorem twisted_term_eq (t a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Complex.exp (((2 * Real.pi * (a * n) : ℝ) : ℂ) * I) * (n : ℂ) ^ (-(I * (t : ℂ)))
      = Complex.exp (((2 * Real.pi * twistChain t a 0 (n : ℝ) : ℝ) : ℂ) * I) := by
  rw [natCast_cpow_neg_I_mul t n hn, ← Complex.exp_add]
  congr 1
  simp only [twistChain, logPhaseChain]
  push_cast
  ring

/-- **The twisted dyadic block bound.**  The bound of `dirichlet_block_bound`, for the terms
`e(a n) n^{-it}`. -/
theorem norm_twisted_block_le (t : ℝ) (ht : 0 < t) (a : ℝ) (k N L : ℕ) (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hlam1 : t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k ≤ 1) :
    ‖∑ j ∈ Finset.range L, Complex.exp (((2 * Real.pi * (a * (N + j : ℕ)) : ℝ) : ℂ) * I) *
        ((N + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))‖
      ≤ 256 * ((L : ℝ)
            * ((4 : ℝ) ^ k * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k)) ^ (1 / ((2 : ℝ) ^ k - 2))
          + (L : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k)
            * (t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ)
                / (2 * (N : ℝ)) ^ k) ^ (-(2 / (2 : ℝ) ^ k))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlam1 ⊢
  set lam : ℝ := t / (2 * Real.pi) * (Nat.factorial j : ℝ) / (2 * (N : ℝ)) ^ (j + 1)
    with hlamdef
  have hπ := Real.pi_pos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    have h1 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
    have h2 : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have h3 : (0 : ℝ) < (2 * (N : ℝ)) ^ (j + 1) := by positivity
    exact div_pos (mul_pos h1 h2) h3
  have hgrow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hlam_eq : lam
      = t / (2 * Real.pi) * (Nat.factorial j : ℝ) * ((2 * (N : ℝ)) ^ (j + 1))⁻¹ := by
    rw [hlamdef, div_eq_mul_inv]
  have hupper_eq : (2 : ℝ) ^ (j + 1) * lam
      = t / (2 * Real.pi) * (Nat.factorial j : ℝ) * (((N : ℝ)) ^ (j + 1))⁻¹ := by
    rw [hlamdef]
    field_simp [mul_pow]
    ring
  have hspan_mem : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      0 < x ∧ x ∈ Set.Icc ((N : ℝ)) (2 * (N : ℝ)) := by
    intro x hx
    have hL1 : ((L - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : L - 1 ≤ N := by omega
      exact_mod_cast this
    exact ⟨by linarith [hx.1], hx.1, by linarith [hx.2]⟩
  have hphase : ∀ i ∈ Finset.range L,
      Complex.exp (((2 * Real.pi * (a * (N + i : ℕ)) : ℝ) : ℂ) * I) *
        ((N + i : ℕ) : ℂ) ^ (-(I * (t : ℂ)))
      = Complex.exp (((2 * Real.pi * twistChain t a 0 ((N : ℝ) + i) : ℝ) : ℂ) * I) := by
    intro i _
    have harg : ((N + i : ℕ) : ℝ) = (N : ℝ) + (i : ℝ) := by push_cast; ring
    rw [twisted_term_eq t a (N + i) (by omega), harg]
  rw [Finset.sum_congr rfl hphase]
  rw [show (4 : ℝ) ^ (j + 1) = ((2 : ℝ) ^ (j + 1)) ^ 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]]
  have htop : twistChain t a (j + 1) = logPhaseChain t (j + 1) :=
    twistChain_of_two_le t a (by omega)
  have hchain : ∀ i < j + 1, ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
      HasDerivAt (twistChain t a i) (twistChain t a (i + 1) x) x :=
    fun i _ x hx => twistChain_hasDerivAt t a i (hspan_mem x hx).1
  rcases Nat.even_or_odd (j + 1) with hev | hodd
  · have hone : ((-1 : ℝ)) ^ (j + 1) = 1 := Even.neg_one_pow hev
    have hlo : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        lam ≤ twistChain t a (j + 1) x := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).1
      rw [hone, one_mul] at hb
      rw [htop, hlam_eq]
      exact hb
    have hhi : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        twistChain t a (j + 1) x ≤ (2 : ℝ) ^ (j + 1) * lam := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).2
      rw [hone, one_mul] at hb
      rw [htop, hupper_eq]
      exact hb
    exact kth_derivative_test (j + 1) hk (twistChain t a) (N : ℝ) L hL
      hlam0 hlam1 hgrow1 hchain hlo hhi
  · have hneg : ((-1 : ℝ)) ^ (j + 1) = -1 := Odd.neg_one_pow hodd
    have hchain' : ∀ i < j + 1, ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        HasDerivAt (fun y => -(twistChain t a i y)) (-(twistChain t a (i + 1) x)) x :=
      fun i hi x hx => (hchain i hi x hx).neg
    have hlo : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        lam ≤ -(twistChain t a (j + 1) x) := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).1
      rw [hneg, neg_one_mul] at hb
      rw [htop, hlam_eq]
      exact hb
    have hhi : ∀ x ∈ Set.Icc ((N : ℝ)) ((N : ℝ) + ((L - 1 : ℕ) : ℝ)),
        -(twistChain t a (j + 1) x) ≤ (2 : ℝ) ^ (j + 1) * lam := by
      intro x hx
      have hb := (logPhaseChain_signed_bounds t ht j
        (lt_of_lt_of_le one_pos hN1) (hspan_mem x hx).2).2
      rw [hneg, neg_one_mul] at hb
      rw [htop, hupper_eq]
      exact hb
    have hDk := kth_derivative_test (j + 1) hk (fun i y => -(twistChain t a i y))
      (N : ℝ) L hL hlam0 hlam1 hgrow1 hchain' hlo hhi
    rw [← norm_phase_sum_neg (twistChain t a 0) (N : ℝ) L]
    exact hDk

/-! ### Characters as combinations of additive characters -/

open ZMod in
/-- **Finite Fourier inversion for a character.**  `χ(n) = q⁻¹ Σ_j \hat χ(j) e(j.val · n / q)`. -/
theorem character_eq_fourier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ n = (q : ℂ)⁻¹ * ∑ j : ZMod q, (𝓕 (fun a : ZMod q => χ a) j) *
      Complex.exp (((2 * Real.pi * (((j.val : ℝ) / q) * n)) : ℝ) * I) := by
  have h := congrFun ((ZMod.dft (E := ℂ)).symm_apply_apply (fun a : ZMod q => χ a)) (n : ZMod q)
  rw [← h, invDFT_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 1
  have hj : j * (n : ZMod q) = ((j.val * n : ℕ) : ZMod q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hj, stdAddChar_apply, toCircle_natCast]
  congr 1
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  push_cast
  field_simp

open ZMod in
theorem norm_dft_character_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (j : ZMod q) :
    ‖𝓕 (fun a : ZMod q => χ a) j‖ ≤ q := by
  rw [dft_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : ZMod q, ‖stdAddChar (-(i * j)) • χ i‖ ≤ ∑ _i : ZMod q, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        have h1 : ‖(stdAddChar (-(i * j)) : ℂ)‖ = 1 := by
          rw [stdAddChar_apply]; exact Circle.norm_coe _
        rw [show ‖stdAddChar (-(i * j))‖ = ‖(stdAddChar (-(i * j)) : ℂ)‖ from rfl, h1, one_mul]
        exact DirichletCharacter.norm_le_one χ i
    _ = q := by simp

/-- **The character block bound.**  If every twisted block `Σ e(a n) n^{-it}` over a run is at
most `P`, the character block over the same run is at most `q P`. -/
theorem norm_character_run_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    (N L : ℕ) (P : ℝ)
    (hP : ∀ a : ℝ, ‖∑ j ∈ Finset.range L,
        Complex.exp (((2 * Real.pi * (a * (N + j : ℕ)) : ℝ) : ℂ) * I) *
          ((N + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))‖ ≤ P) :
    ‖∑ j ∈ Finset.range L, χ (N + j : ℕ) * ((N + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))‖ ≤ q * P := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hexp : ∀ j ∈ Finset.range L,
      χ (N + j : ℕ) * ((N + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))
        = (q : ℂ)⁻¹ * ∑ b : ZMod q, (ZMod.dft (fun a : ZMod q => χ a) b) *
          (Complex.exp (((2 * Real.pi * (((b.val : ℝ) / q) * (N + j : ℕ))) : ℝ) * I) *
            ((N + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))) := by
    intro j _
    have h := character_eq_fourier χ (N + j)
    push_cast at h ⊢
    rw [h, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hb : ∀ b : ZMod q, ‖ZMod.dft (fun a : ZMod q => χ a) b *
      ∑ j ∈ Finset.range L,
        Complex.exp (((2 * Real.pi * (((b.val : ℝ) / q) * (N + j : ℕ))) : ℝ) * I) *
          ((N + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))‖ ≤ q * P := by
    intro b
    rw [norm_mul]
    exact mul_le_mul (norm_dft_character_le χ b) (hP _) (norm_nonneg _) hq.le
  calc (q : ℝ)⁻¹ * ‖∑ b : ZMod q, ZMod.dft (fun a : ZMod q => χ a) b *
          ∑ j ∈ Finset.range L,
            Complex.exp (((2 * Real.pi * (((b.val : ℝ) / q) * (N + j : ℕ))) : ℝ) * I) *
              ((N + j : ℕ) : ℂ) ^ (-(I * (t : ℂ)))‖
      ≤ (q : ℝ)⁻¹ * ∑ _b : ZMod q, (q * P) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb b))
          (by positivity)
    _ = q * P := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
