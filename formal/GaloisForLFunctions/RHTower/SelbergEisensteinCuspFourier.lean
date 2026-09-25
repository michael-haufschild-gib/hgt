import GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry
import GaloisForLFunctions.RHTower.CoprimeClassRamanujan
import GaloisForLFunctions.RHTower.SelbergEisensteinStar

open Complex UpperHalfPlane Metric
open scoped MatrixGroups FourierTransform

/-!
# The Fourier expansion of `E_∞(σz, s)` at the cusp `σ∞`: slices, Ramanujan bound, holomorphy

For `c ≠ 0`, Poisson summation over `d ≡ r (mod |c|N)` turns the row slice of `E_∞(σz, s)` into
`c^{-2s} N^{-s} Σ_n 𝓕ker_{0,y/N,s}(n) e(nx/N) S_σ(0, n; c)` (`sliceσ`) with the Ramanujan-type sum
`S_σ(0,n;c) = Σ_{d mod |c|N, (c,d) a row at σ∞} e(nd/(cN))` (`ksumσ`). The rows are the primitive rows
`≡ (σ₁₀, σ₁₁) (N)`, so `S_σ` is a coprime-class exponential sum and `|S_σ(0,n;c)| ≤ n²` uniformly in `c`
(`norm_ksumσ_le`, from `CoprimeClassRamanujan`; the class condition uses `det σ = 1`, `coprime_class`). With the
fourth-order decay of `𝓕ker₀` this gives the locally uniform majorant `|c|^{-2σ₁} · C n^{-2}` for the non-constant
terms (`norm_etermσ_le`), so `E^*_σ(z, ·)` is holomorphic on `Re s > 1/2` (`differentiableAt_Estarσ`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCusp
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount GaloisForLFunctions.RHTower.CoprimeClassRamanujan
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergEisensteinKernel
  GaloisForLFunctions.RHTower.SelbergEisensteinStar GaloisForLFunctions.RHTower.SelbergPoincare

theorem esum_eq_esumxy (s : ℂ) (z : ℍ) (p : ℤ × ℤ) : esum s z p = esumxy s z.im z.re p := by
  unfold esum esumxy
  congr 3
  rw [Complex.normSq_apply]
  simp only [add_re, mul_re, intCast_re, intCast_im, add_im, mul_im, zero_mul, sub_zero, add_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem cpow_neg_eq_exp {c : ℤ} (hc : c ≠ 0) (s : ℂ) :
    (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) = cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) := by
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  rw [cpow_def_of_ne_zero (by exact_mod_cast hc2.ne'), ← ofReal_log hc2.le, mul_comm]

theorem esum_c (s : ℂ) (z : ℍ) {c : ℤ} (hc : c ≠ 0) (d : ℤ) :
    esum s z (c, d) = cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * ker 0 z.im s (z.re + d / c) := by
  rw [esum_eq_esumxy, esumxy_eq z.im_pos s z.re hc d, cpow_neg_eq_exp hc]

variable (N : ℕ) (σ : SL(2, ℤ))

/-- The Ramanujan–Kloosterman sum at `σ∞`: `S_σ(0, n; c) = Σ_{d mod |c|N, (c,d) a row at σ∞} e(nd/(cN))`. -/
noncomputable def ksumσ (c n : ℤ) : ℂ :=
  ∑ r ∈ Finset.range (c.natAbs * N), (rowMul σ '' adm N).indicator (kphase N 0 n) (c, r)

theorem kphase_zero_eq (n : ℤ) (p : ℤ × ℤ) :
    kphase N 0 n p = cexp (2 * Real.pi * Complex.I * n * p.2 / ((p.1 : ℂ) * N)) := by
  simp [kphase, phase]

theorem norm_kphase_zero (n : ℤ) (p : ℤ × ℤ) : ‖kphase N 0 n p‖ ≤ 1 := by
  rw [kphase_zero_eq]
  by_cases h : (p.1 : ℂ) * N = 0
  · rw [h, div_zero, Complex.exp_zero, norm_one]
  · rw [show 2 * Real.pi * Complex.I * n * p.2 / ((p.1 : ℂ) * N) =
        ((2 * Real.pi * (n * p.2 / (p.1 * N)) : ℝ) : ℂ) * Complex.I by
        have : ((p.1 : ℝ) * N : ℝ) ≠ 0 := by exact_mod_cast h
        push_cast; field_simp,
      Complex.norm_exp_ofReal_mul_I]

variable [NeZero N]

/-- **The `c`-slice of `E_∞(σz, s)`** (`c ≠ 0`): Poisson summation over `d ≡ r (mod |c|N)`. -/
theorem sliceσ {c : ℤ} (hc : c ≠ 0) {s : ℂ} (hs : 3 / 4 ≤ s.re) (z : ℍ)
    (hsum : Summable fun d : ℤ => (rowMul σ '' adm N).indicator (esum s z) (c, d)) :
    ∑' d : ℤ, (rowMul σ '' adm N).indicator (esum s z) (c, d) =
      cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
        ∑' n : ℤ, 𝓕 (ker 0 (z.im / N) s) n * cexp (2 * Real.pi * Complex.I * n * z.re / N) * ksumσ N σ c n := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hK : 0 < c.natAbs * N := Nat.mul_pos (Int.natAbs_pos.mpr hc) hN
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  set S := rowMul σ '' adm N
  set E := cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ))
  set EN := cexp (-s * (Real.log N : ℂ))
  set Fh : ℤ → ℂ := fun n => 𝓕 (ker 0 (z.im / N) s) n
  have hFs : Summable fun n => ‖Fh n‖ :=
    summable_norm_fourier_ker le_rfl (div_pos z.im_pos (by exact_mod_cast hN)) (by linarith)
  rw [tsum_eq_sum_residues hsum _ hK]
  have hr : ∀ r ∈ Finset.range (c.natAbs * N),
      ∑' j : ℤ, S.indicator (esum s z) (c, (r : ℤ) + ((c.natAbs * N : ℕ) : ℤ) * j) =
        E * EN * ∑' n : ℤ, Fh n * cexp (2 * Real.pi * Complex.I * n * z.re / N) * S.indicator (kphase N 0 n) (c, r) := by
    intro r _
    by_cases hmem : (c, (r : ℤ)) ∈ S
    · have hterm : ∀ j : ℤ, S.indicator (esum s z) (c, (r : ℤ) + ((c.natAbs * N : ℕ) : ℤ) * j) =
          E * ker 0 z.im s (z.re + (r : ℝ) / c + N * ((c.sign * j : ℤ) : ℝ)) := by
        intro j
        rw [Set.indicator_of_mem ((mem_image_shift N σ c r j).mpr hmem), esum_c s z hc, arg_shift N hc]
        push_cast
        rfl
      simp_rw [hterm]
      rw [tsum_mul_left, tsum_sign hc (fun j => ker 0 z.im s (z.re + (r : ℝ) / c + N * (j : ℝ))),
        tsum_ker_shift N le_rfl z.im_pos hs hN]
      simp_rw [Set.indicator_of_mem hmem, kphase_zero_eq]
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [Fh, zero_div]
      have hsplit : cexp (2 * Real.pi * Complex.I * n * ((z.re + (r : ℝ) / c : ℝ) : ℂ) / N) =
          cexp (2 * Real.pi * Complex.I * n * z.re / N) * cexp (2 * Real.pi * Complex.I * n * (r : ℤ) / ((c : ℂ) * N)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; field_simp
      rw [hsplit]
      ring
    · have h0 : ∀ j : ℤ, S.indicator (esum s z) (c, (r : ℤ) + ((c.natAbs * N : ℕ) : ℤ) * j) = 0 :=
        fun j => Set.indicator_of_notMem (fun h => hmem ((mem_image_shift N σ c r j).mp h)) _
      simp_rw [h0, Set.indicator_of_notMem hmem, mul_zero, tsum_zero, mul_zero]
  rw [Finset.sum_congr rfl hr, ← Finset.mul_sum]
  congr 1
  have hsum_n : ∀ r ∈ Finset.range (c.natAbs * N), Summable fun n : ℤ =>
      Fh n * cexp (2 * Real.pi * Complex.I * n * z.re / N) * S.indicator (kphase N 0 n) (c, r) := by
    intro r _
    refine Summable.of_norm_bounded (g := fun n => ‖Fh n‖) hFs (fun n => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (2 * Real.pi * Complex.I * n * z.re / N)‖ = 1 := by
      rw [show 2 * Real.pi * Complex.I * n * z.re / N = 2 * Real.pi * Complex.I * ((n * z.re / N : ℝ) : ℂ) by
        push_cast; ring]
      exact norm_cexp_two_pi_I_real _
    have h2 : ‖S.indicator (kphase N 0 n) (c, r)‖ ≤ 1 := by
      by_cases hmem : (c, (r : ℤ)) ∈ S
      · rw [Set.indicator_of_mem hmem]; exact norm_kphase_zero N n _
      · rw [Set.indicator_of_notMem hmem, norm_zero]; norm_num
    rw [h1, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) h2
  rw [← Summable.tsum_finsetSum hsum_n]
  apply tsum_congr
  intro n
  rw [ksumσ, Finset.mul_sum]

/-- The class residue `b = σ₁₁ mod N` is coprime to `gcd(|c|, N)` when `c ≡ σ₁₀ (N)` (`det σ = 1`). -/
theorem coprime_class {c : ℤ} (hcl : (c : ZMod N) = σ 1 0) :
    (c.natAbs.gcd N).Coprime ((σ 1 1 : ℤ) : ZMod N).val := by
  set b := ((σ 1 1 : ℤ) : ZMod N).val
  have hbσ : ((b : ℕ) : ZMod N) = ((σ 1 1 : ℤ) : ZMod N) := ZMod.natCast_zmod_val _
  refine Nat.coprime_of_dvd (fun p hp hpg hpb => ?_)
  have hpc : (p : ℤ) ∣ c := Int.natCast_dvd.mpr (hpg.trans (Nat.gcd_dvd_left _ _))
  have hpN : (p : ℤ) ∣ N := Int.natCast_dvd_natCast.mpr (hpg.trans (Nat.gcd_dvd_right _ _))
  have h10 : (p : ℤ) ∣ σ 1 0 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp hcl
    have h := dvd_add (hpN.trans this) hpc
    simpa using h
  have h11 : (p : ℤ) ∣ σ 1 1 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp (by rw [← hbσ]; push_cast; rfl :
      (((b : ℕ) : ℤ) : ZMod N) = ((σ 1 1 : ℤ) : ZMod N))
    have h := dvd_add (Int.natCast_dvd_natCast.mpr hpb) (hpN.trans this)
    simpa using h
  have h1 : (p : ℤ) ∣ 1 := by
    rw [← det_eq σ]
    exact dvd_sub (dvd_mul_of_dvd_right h11 _) (dvd_mul_of_dvd_right h10 _)
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)

theorem kphase_eq_ph {c : ℤ} (hc : c ≠ 0) (n : ℤ) (r : ℕ) :
    kphase N 0 n (c, r) = ph (c.sign * n) (c.natAbs * N) r := by
  rw [kphase_zero_eq]
  unfold ph
  congr 1
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rcases lt_or_gt_of_ne hc with h | h
  · rw [Int.sign_eq_neg_one_of_neg h]
    have hz : ((c.natAbs : ℕ) : ℤ) = -c := by omega
    have e : ((c.natAbs : ℕ) : ℂ) = -(c : ℂ) := by
      rw [show ((c.natAbs : ℕ) : ℂ) = (((c.natAbs : ℕ) : ℤ) : ℂ) by rw [Int.cast_natCast], hz]; push_cast; ring
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast; rw [e]; field_simp
  · rw [Int.sign_eq_one_of_pos h]
    have hz : ((c.natAbs : ℕ) : ℤ) = c := by omega
    have e : ((c.natAbs : ℕ) : ℂ) = (c : ℂ) := by
      rw [show ((c.natAbs : ℕ) : ℂ) = (((c.natAbs : ℕ) : ℤ) : ℂ) by rw [Int.cast_natCast], hz]
    push_cast; rw [e]; ring

/-- **Uniform Ramanujan bound at `σ∞`**: `|S_σ(0, n; c)| ≤ n²` for `c, n ≠ 0`. -/
theorem norm_ksumσ_le {c : ℤ} (hc : c ≠ 0) {n : ℤ} (hn : n ≠ 0) : ‖ksumσ N σ c n‖ ≤ (n.natAbs : ℝ) ^ 2 := by
  classical
  unfold ksumσ
  by_cases hcl : (c : ZMod N) = σ 1 0
  · set b := ((σ 1 1 : ℤ) : ZMod N).val
    have hbσ : ((b : ℕ) : ZMod N) = ((σ 1 1 : ℤ) : ZMod N) := ZMod.natCast_zmod_val _
    have hmem : ∀ r : ℕ, (c, (r : ℤ)) ∈ rowMul σ '' adm N ↔ (r ≡ b [MOD N] ∧ c.natAbs.Coprime r) := by
      intro r
      rw [mem_image_congr, Int.isCoprime_iff_nat_coprime, ← ZMod.natCast_eq_natCast_iff, hbσ]
      simp [hcl]
    have hsum : ∑ r ∈ Finset.range (c.natAbs * N), (rowMul σ '' adm N).indicator (kphase N 0 n) (c, (r : ℤ)) =
        ∑ r ∈ (Finset.range (c.natAbs * N)).filter (fun r => r ≡ b [MOD N] ∧ c.natAbs.Coprime r),
          ph (c.sign * n) (c.natAbs * N) r := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      rw [Set.indicator_apply]
      simp only [hmem, kphase_eq_ph N hc n r]
    rw [hsum]
    have hsn : c.sign * n ≠ 0 := mul_ne_zero (fun h => hc (Int.sign_eq_zero_iff_zero.mp h)) hn
    have := norm_class_sum_le (Int.natAbs_pos.mpr hc) (Nat.pos_of_ne_zero (NeZero.ne N))
      (coprime_class N σ hcl) hsn
    rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hc, one_mul] at this
  · have h0 : ∀ r ∈ Finset.range (c.natAbs * N),
        (rowMul σ '' adm N).indicator (kphase N 0 n) (c, (r : ℤ)) = 0 :=
      fun r _ => Set.indicator_of_notMem (fun h => hcl ((mem_image_congr N σ _).mp h).1) _
    rw [Finset.sum_eq_zero h0, norm_zero]
    positivity

/-- The non-constant Fourier terms of `E_∞(σz, s)` at `σ∞`. -/
noncomputable def etermσ (s : ℂ) (z : ℍ) (p : ℤ × ℤ) : ℂ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else
    cexp (-s * (Real.log ((p.1 : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
      (𝓕 (ker 0 (z.im / N) s) p.2 * cexp (2 * Real.pi * Complex.I * p.2 * z.re / N) * ksumσ N σ p.1 p.2)

/-- The non-constant part `E^*_σ(z, s)` of the Fourier expansion at `σ∞`. -/
noncomputable def Estarσ (s : ℂ) (z : ℍ) : ℂ := ∑' p : ℤ × ℤ, etermσ N σ s z p

theorem norm_ksumσ_le' {c : ℤ} (hc : c ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    ‖ksumσ N σ c n‖ ≤ (N : ℝ) ^ 2 * |(n : ℝ)| ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  refine (norm_ksumσ_le N σ hc hn).trans ?_
  have : (n.natAbs : ℝ) = |(n : ℝ)| := by simp [Nat.cast_natAbs]
  rw [this]
  have h0 : 0 ≤ |(n : ℝ)| ^ 2 := by positivity
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  nlinarith

theorem norm_etermσ_le (z : ℍ) {s : ℂ} {σ₁ σ₂ R : ℝ} (hσ₁ : 1 / 2 < σ₁) (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂)
    (hs : ‖s‖ ≤ R) (p : ℤ × ℤ) :
    ‖etermσ N σ s z p‖ ≤ (if p.1 = 0 then 0 else |(p.1 : ℝ)| ^ (-(2 * σ₁))) *
      (if p.2 = 0 then 0 else econst N z.im σ₁ σ₂ R * |(p.2 : ℝ)| ^ (-(2 : ℝ))) := by
  unfold etermσ
  by_cases hp : p.1 = 0 ∨ p.2 = 0
  · rw [if_pos hp, norm_zero]
    have hR : 0 ≤ R := (norm_nonneg s).trans hs
    have hc := cst_nonneg σ₁
    have hy : 0 < z.im / N := div_pos z.im_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    have he : 0 ≤ econst N z.im σ₁ σ₂ R := by unfold econst; positivity
    split_ifs <;> positivity
  push Not at hp
  obtain ⟨hc, hk⟩ := hp
  rw [if_neg (not_or.mpr ⟨hc, hk⟩), if_neg hc, if_neg hk]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : (0 : ℝ) < N := by linarith
  have hy : 0 < z.im / N := div_pos z.im_pos hN
  have hc2 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ p.1 ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs p.1]
    exact_mod_cast this
  have hE := norm_exp_neg_mul_log (s := s) hc2 h1
  have hEN := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 (by linarith)
  rw [neg_zero, Real.rpow_zero] at hEN
  have hcsq : ((p.1 : ℝ) ^ 2) ^ (-σ₁) = |(p.1 : ℝ)| ^ (-(2 * σ₁)) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; push_cast; ring_nf
  rw [hcsq] at hE
  have hs' : 1 / 2 < s.re := by linarith
  have hF := norm_fourier_ker0_le_four (y := z.im / N) (s := s) hy hs' (p.2 : ℝ)
  have hvv : vv (z.im / N) s ≤ (1 + R) / (z.im / N) := by
    unfold vv; gcongr
  have hX : (z.im / N) ^ (1 - s.re) * cst s.re ≤ ((z.im / N) ^ (1 - σ₂) + (z.im / N) ^ (1 - σ₁)) * cst σ₁ :=
    mul_le_mul (rpow_le_add hy (by linarith) (by linarith)) (cst_anti hσ₁ h1) (cst_nonneg _) (by positivity)
  have hF' : ‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ ≤
      109 * ((1 + R) / (z.im / N)) ^ 4 * (((z.im / N) ^ (1 - σ₂) + (z.im / N) ^ (1 - σ₁)) * cst σ₁) /
        ((2 * Real.pi) ^ 4 * |(p.2 : ℝ)| ^ 4) := by
    have hk1 : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    rw [le_div_iff₀ (by positivity)]
    have hv := vv_nonneg (y := z.im / N) (s := s) hy
    have := cst_nonneg s.re
    calc ‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ * ((2 * Real.pi) ^ 4 * |(p.2 : ℝ)| ^ 4)
        = (2 * Real.pi * |(p.2 : ℝ)|) ^ 4 * ‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ := by ring
      _ ≤ 109 * vv (z.im / N) s ^ 4 * ((z.im / N) ^ (1 - s.re) * cst s.re) := hF
      _ ≤ _ := by gcongr
  have hK' := norm_ksumσ_le' N σ hc hk
  have hexp : ‖cexp (2 * Real.pi * Complex.I * p.2 * z.re / N)‖ = 1 := norm_cexp_two_pi_I_div _ _ _
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hexp, mul_one]
  have hk2 : |(p.2 : ℝ)| ^ (-(2 : ℝ)) = (|(p.2 : ℝ)| ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _)]; norm_cast
  rw [hk2]
  set A := 109 * ((1 + R) / (z.im / N)) ^ 4 * (((z.im / N) ^ (1 - σ₂) + (z.im / N) ^ (1 - σ₁)) * cst σ₁)
  have hA : 0 ≤ A := by have := cst_nonneg σ₁; have : 0 ≤ R := (norm_nonneg s).trans hs; simp only [A]; positivity
  have hk4 : 0 < |(p.2 : ℝ)| := by positivity
  calc ‖cexp (-s * (Real.log ((p.1 : ℝ) ^ 2) : ℂ))‖ * ‖cexp (-s * (Real.log N : ℂ))‖ *
        (‖𝓕 (ker 0 (z.im / N) s) (p.2 : ℝ)‖ * ‖ksumσ N σ p.1 p.2‖)
      ≤ |(p.1 : ℝ)| ^ (-(2 * σ₁)) * 1 * (A / ((2 * Real.pi) ^ 4 * |(p.2 : ℝ)| ^ 4) *
          ((N : ℝ) ^ 2 * |(p.2 : ℝ)| ^ 2)) := by
        gcongr
    _ = |(p.1 : ℝ)| ^ (-(2 * σ₁)) * (econst N z.im σ₁ σ₂ R * (|(p.2 : ℝ)| ^ 2)⁻¹) := by
        simp only [econst, A]; field_simp

theorem summable_etermσ {s : ℂ} (hs : 1 / 2 < s.re) (z : ℍ) : Summable (etermσ N σ s z) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have he : 0 ≤ econst N z.im s.re s.re ‖s‖ := by
    have := cst_nonneg s.re; have hy : 0 < z.im / N := div_pos z.im_pos hN
    unfold econst; positivity
  have hf := summable_ite_abs (b := 2 * s.re) (by linarith) 1 zero_le_one
  have hg := summable_ite_abs (b := 2) (by norm_num) _ he
  refine Summable.of_norm_bounded (Summable.mul_of_nonneg hf hg (fun c => by split_ifs <;> positivity)
    (fun k => by split_ifs <;> positivity)) (fun p => (norm_etermσ_le N σ z hs le_rfl le_rfl le_rfl p).trans ?_)
  simp only [one_mul]; rfl

/-- **Holomorphy of the non-constant part at `σ∞`** on `Re s > 1/2`. -/
theorem differentiableAt_Estarσ (z : ℍ) {s₀ : ℂ} (h : 1 / 2 < s₀.re) :
    DifferentiableAt ℂ (fun s => Estarσ N σ s z) s₀ := by
  set r := (s₀.re - 1 / 2) / 2
  have hr : 0 < r := by simp only [r]; linarith
  set σ₁ := s₀.re - r
  set σ₂ := s₀.re + r
  set R := ‖s₀‖ + r
  have hσ₁ : 1 / 2 < σ₁ := by simp only [σ₁, r]; linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hy : 0 < z.im / N := div_pos z.im_pos hN
  have he : 0 ≤ econst N z.im σ₁ σ₂ R := by
    have := cst_nonneg σ₁; have : 0 ≤ R := by simp only [R]; positivity
    unfold econst; positivity
  set f : ℤ → ℝ := fun c => if c = 0 then 0 else 1 * |(c : ℝ)| ^ (-(2 * σ₁))
  set g : ℤ → ℝ := fun k => if k = 0 then 0 else econst N z.im σ₁ σ₂ R * |(k : ℝ)| ^ (-(2 : ℝ))
  have hf : Summable f := summable_ite_abs (by linarith) 1 zero_le_one
  have hg : Summable g := summable_ite_abs (by norm_num) _ he
  unfold Estarσ
  apply GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated hr
    (bound := fun p : ℤ × ℤ => f p.1 * g p.2)
  · intro p s hs
    obtain ⟨h1, _, _⟩ := ball_props hs
    apply DifferentiableAt.differentiableWithinAt
    unfold etermσ
    by_cases hp : p.1 = 0 ∨ p.2 = 0
    · simp only [if_pos hp]; exact differentiableAt_const _
    simp only [if_neg hp]
    refine ((differentiable_exp_neg_mul _).differentiableAt.mul (differentiable_exp_neg_mul _).differentiableAt).mul ?_
    exact ((differentiableAt_fourier_ker le_rfl hy
      (by linarith) _).mul_const _).mul_const _
  · intro p s hs
    obtain ⟨h1, h2, h3⟩ := ball_props hs
    refine (norm_etermσ_le N σ z hσ₁ h1 h2 h3 p).trans (le_of_eq ?_)
    simp only [f, g, one_mul]; rfl
  · exact Summable.mul_of_nonneg hf hg (fun c => by simp only [f]; split_ifs <;> positivity)
      (fun k => by simp only [g]; split_ifs <;> positivity)

end GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier
