import GaloisForLFunctions.RHTower.SelbergEisensteinStar

open Complex MeasureTheory UpperHalfPlane
open scoped FourierTransform

/-!
# The `Γ(N)` Eisenstein series: constant term plus a part holomorphic on `Re s > 1/2`

For `N ≥ 3` and `Re s > 1` the Eisenstein series at `∞` (the Poincaré series with `m = 0`) splits as
`E(z,s) = y^s + Σ_c cterm_c(z,s) + E^*(z,s)` (`eisenstein_decomp`), where
`cterm_c = c^{-2s} N^{-s} 𝓕ker_{0,y/N,s}(0) S_N(0,0;c)` are the `n = 0` Kloosterman terms (summable for `Re s > 1` by the
trivial bound `|S_N| ≤ |c|N`, `summable_cterm`) and `E^*` is the non-constant part, holomorphic on `Re s > 1/2`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinDecomposition
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergEisensteinStar
  GaloisForLFunctions.RHTower.SelbergPoincare

variable (N : ℕ) [NeZero N]

/-- The constant-term contributions of the Kloosterman part. -/
noncomputable def cterm (s : ℂ) (z : ℍ) (c : ℤ) : ℂ :=
  if c = 0 then 0 else
    cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
      (𝓕 (ker 0 (z.im / N) s) 0 * ksum N 0 c 0)

omit [NeZero N] in
theorem Qc_split (s : ℂ) (z : ℍ) (c : ℤ) (hsum : Summable (fun k : ℤ => eterm N s z (c, k))) :
    Qc N 0 s z c = cterm N s z c + ∑' k, eterm N s z (c, k) := by
  unfold Qc cterm
  by_cases hc : c = 0
  · simp [hc, eterm]
  simp only [if_neg hc]
  have hβ : ((0 : ℕ) : ℝ) / ((c : ℝ) ^ 2 * N) / N = 0 := by simp
  rw [hβ]
  have hs : Summable (fun k : ℤ => 𝓕 (ker 0 (z.im / N) s) k * cexp (2 * Real.pi * Complex.I * k * z.re / N) *
      ksum N 0 c k) := by
    have hE : cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    have h2 := hsum.mul_left (cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)))⁻¹
    refine (h2.add (summable_of_ne_finset_zero (s := {0})
      (f := fun k : ℤ => if k = 0 then 𝓕 (ker 0 (z.im / N) s) 0 * ksum N 0 c 0 else 0)
      (fun k hk => by simp at hk; simp [hk]))).congr (fun k => ?_)
    by_cases hk : k = 0
    · subst hk; simp [eterm]
    · simp only [eterm, hc, hk, or_self, if_false, add_zero]
      field_simp
  rw [hs.tsum_eq_add_tsum_ite 0, mul_add]
  congr 1
  · simp
  · rw [← tsum_mul_left]
    apply tsum_congr; intro k
    by_cases hk : k = 0
    · simp [hk, eterm]
    · simp only [eterm, hc, hk, or_self, if_false]

omit [NeZero N] in
theorem norm_ksum_le_trivial (m : ℕ) (c n : ℤ) : ‖ksum N m c n‖ ≤ c.natAbs * N := by
  unfold ksum
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ r ∈ Finset.range (c.natAbs * N), ‖(adm N).indicator (kphase N m n) (c, (r : ℤ))‖ ≤ 1 := by
    intro r _
    by_cases hmem : (c, (r : ℤ)) ∈ adm N
    · rw [Set.indicator_of_mem hmem, kphase, phase, norm_mul]
      rw [show 2 * Real.pi * Complex.I * m * ((((r : ℤ) : ZMod (c.natAbs * N))⁻¹.val : ℕ) : ℂ) / ((c : ℂ) * N) =
          ((2 * Real.pi * m * (((r : ℤ) : ZMod (c.natAbs * N))⁻¹.val : ℕ) / (c * N) : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        show 2 * Real.pi * Complex.I * n * (r : ℤ) / ((c : ℂ) * N) = ((2 * Real.pi * n * r / (c * N) : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul]
    · rw [Set.indicator_of_notMem hmem, norm_zero]; norm_num
  calc ∑ r ∈ Finset.range (c.natAbs * N), ‖(adm N).indicator (kphase N m n) (c, (r : ℤ))‖
      ≤ ∑ _r ∈ Finset.range (c.natAbs * N), (1 : ℝ) := Finset.sum_le_sum hb
    _ = c.natAbs * N := by simp

theorem summable_eterm {s : ℂ} (hs : 1 / 2 < s.re) (z : ℍ) : Summable (eterm N s z) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have he : 0 ≤ econst N z.im s.re s.re ‖s‖ := by
    have := cst_nonneg s.re; have hy : 0 < z.im / N := div_pos z.im_pos hN
    unfold econst; positivity
  have hf := summable_ite_abs (b := 2 * s.re) (by linarith) 1 zero_le_one
  have hg := summable_ite_abs (b := 2) (by norm_num) _ he
  refine Summable.of_norm_bounded (Summable.mul_of_nonneg hf hg (fun c => by split_ifs <;> positivity)
    (fun k => by split_ifs <;> positivity)) (fun p => (norm_eterm_le N z hs le_rfl le_rfl le_rfl p).trans ?_)
  simp only [one_mul]; rfl

theorem summable_cterm {s : ℂ} (hs : 1 < s.re) (z : ℍ) : Summable (cterm N s z) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set C := ‖𝓕 (ker 0 (z.im / N) s) 0‖ * N
  have hf := summable_ite_abs (b := 2 * s.re - 1) (by linarith) C (by positivity)
  refine Summable.of_norm_bounded hf (fun c => ?_)
  unfold cterm
  by_cases hc : c = 0
  · simp [hc]
  rw [if_neg hc, if_neg hc]
  have hc2 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ c ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs c]
    exact_mod_cast this
  have hE := norm_exp_neg_mul_log (s := s) hc2 le_rfl
  have hEN := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 (by linarith)
  rw [neg_zero, Real.rpow_zero] at hEN
  have hK := norm_ksum_le_trivial N 0 c 0
  have hca : (0 : ℝ) < |(c : ℝ)| := by positivity
  have hcsq : ((c : ℝ) ^ 2) ^ (-s.re) = |(c : ℝ)| ^ (-(2 * s.re)) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; push_cast; ring_nf
  have hnat : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by simp [Nat.cast_natAbs]
  rw [hnat] at hK
  rw [norm_mul, norm_mul, norm_mul]
  have hpow : |(c : ℝ)| ^ (-(2 * s.re)) * |(c : ℝ)| = |(c : ℝ)| ^ (-(2 * s.re - 1)) := by
    rw [show -(2 * s.re - 1) = -(2 * s.re) + 1 by ring, Real.rpow_add hca, Real.rpow_one]
  calc ‖cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ))‖ * ‖cexp (-s * (Real.log N : ℂ))‖ *
        (‖𝓕 (ker 0 (z.im / N) s) 0‖ * ‖ksum N 0 c 0‖)
      ≤ |(c : ℝ)| ^ (-(2 * s.re)) * 1 * (‖𝓕 (ker 0 (z.im / N) s) 0‖ * (|(c : ℝ)| * N)) := by
        rw [← hcsq]; gcongr
    _ = C * |(c : ℝ)| ^ (-(2 * s.re - 1)) := by rw [← hpow]; simp only [C]; ring

open GaloisForLFunctions.RHTower.SelbergPoincare in
/-- **Eisenstein decomposition** (`N ≥ 3`, `Re s > 1`): `E(z,s) = y^s + Σ_c cterm_c + E^*(z,s)`. -/
theorem eisenstein_decomp (hN : 3 ≤ N) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    poincare N 0 s z = (z.im : ℂ) ^ s + ∑' c, cterm N s z c + Estar N s z := by
  have hse := summable_eterm N (s := s) (by linarith) z
  rw [poincare_eq_Q N 0 hN hs z, Q]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, mul_one]
  rw [add_assoc]
  congr 1
  have h1 : ∀ c, Qc N 0 s z c = cterm N s z c + ∑' k, eterm N s z (c, k) :=
    fun c => Qc_split N s z c (hse.prod_factor c)
  simp_rw [h1]
  rw [Summable.tsum_add (summable_cterm N hs z) hse.prod, Estar, Summable.tsum_prod hse]

end GaloisForLFunctions.RHTower.SelbergEisensteinDecomposition
