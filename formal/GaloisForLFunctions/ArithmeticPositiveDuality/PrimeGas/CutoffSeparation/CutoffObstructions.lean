import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.StripLowerBounds
import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveTwoPrimeAnnihilators
import GaloisForLFunctions.RHTower.ZetaVoroninUniversalityOnCompactSets

/-!
# Vertical-line universality and one-prime positive surgery obstructions to naive cutoff proofs

Four structural theorems sharpen what any strip lower-bound proof for `renormalizedCutoff` must use:

1. **Functional reflection of cutoff extinction (`cutoff_vanishes_symm_one_sub`)**: inside the open
   critical strip `0 < Re w < 1`, `renormalizedCutoff t j X w → 0` iff
   `renormalizedCutoff t j X (1 - w) → 0`.
2. **Uniform vertical floor in the Euler half-plane (`vertical_line_uniform_floor_of_one_lt`)**: for
   every `σ > 1`, a single `τ`-independent constant `ε > 0` bounds `‖renormalizedCutoff‖` from below
   eventually in `X` at every height `τ ∈ ℝ`.
3. **Failure of vertical-line uniform floors in the strip (`pos_density_small_cutoff_on_vertical_line`)**:
   for every `1/2 < σ < 1` (including the zero-free strip `20999/24000 < σ < 1`) and every `ε > 0`,
   Voronin universality forces positive lower density of heights `τ ≥ 0` at which
   `‖renormalizedCutoff t j X (σ + iτ)‖ < ε` for all sufficiently large `X`.
4. **One-prime positive surgery extinction (`exists_one_prime_positive_surgery_cutoff_extinction`)**:
   for any nonreal `w₀` in `0 < Re w₀ < 1`, modifying the arithmetic weight at powers of a single
   prime `p ∈ {2, 3}` produces a multiplicative weight `a : ℕ → ℝ` with `a(n) ≥ 1`, `a(n) = 1` for
   `(n, p) = 1`, `O(1)` linear counting remainder, and the exact radix-`C` shell recursion whose
   renormalized cutoffs vanish at `w₀`, while breaking functional reflection symmetry across `1 - w₀`
   on `20999/24000 < Re w₀ < 1`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter MeasureTheory Set
open scoped Topology ComplexConjugate

/-- Functional-equation reflection invariance of cutoff extinction across `0 < Re w < 1`. -/
theorem cutoff_vanishes_symm_one_sub (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Tendsto (fun X => renormalizedCutoff t j X w) atTop (𝓝 0) ↔
      Tendsto (fun X => renormalizedCutoff t j X (1 - w)) atTop (𝓝 0) := by
  have hw1 : w ≠ 1 := fun he => h1.ne (by rw [he, Complex.one_re])
  have h1w0 : 0 < (1 - w).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1w1 : 1 - w ≠ 1 := fun he =>
    h0.ne' (by have := congrArg Complex.re he; simp only [Complex.sub_re, Complex.one_re] at this; linarith)
  rw [cutoff_vanishes_iff t j ⟨w, h0, hw1⟩, cutoff_vanishes_iff t j ⟨1 - w, h1w0, h1w1⟩]
  exact (_root_.RHTower.riemannZeta_one_sub_eq_zero_iff h0 h1).symm

/-- On every vertical line `Re w = σ > 1` in the Euler half-plane, a single `τ`-independent constant
`ε > 0` bounds `‖renormalizedCutoff t j X (σ + iτ)‖` below eventually in `X` at every `τ ∈ ℝ`. -/
theorem vertical_line_uniform_floor_of_one_lt (t : ExceptionalTime) (j : ℕ)
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : ℝ, ∀ᶠ X : ℕ in atTop,
      ε ≤ ‖renormalizedCutoff t j X ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
  set C := tailRadix t j
  let Cr : ℝ := C.val
  have hCr0 : (0 : ℝ) < Cr := Nat.cast_pos.mpr C.pos
  set B : ℝ := 1 + 1 / (σ - 1)
  set cZ : ℝ := Real.exp ((-22 - 3 * Real.log B - Real.log B) / 4)
  have hcZ : 0 < cZ := Real.exp_pos _
  set ε : ℝ := (Cr ^ σ + 1)⁻¹ * cZ
  have hCrσ : 0 < Cr ^ σ := Real.rpow_pos_of_pos hCr0 σ
  have hε : 0 < ε := mul_pos (inv_pos.mpr (by linarith)) hcZ
  refine ⟨ε, hε, fun τ => ?_⟩
  set w : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  have hw_re : w.re = σ := by simp [w]
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hσ.ne' (by simpa [hw_re] using congrArg Complex.re he)
  set q := heat w C
  set L := 2 * q * riemannZeta w / (1 - q)
  have hzeta_ge : cZ ≤ ‖riemannZeta w‖ := by
    apply _root_.RHTower.Sieve.exp_le_norm_riemannZeta_shift hσ
    have hre2 : ((σ : ℂ) + (2 * τ : ℂ) * Complex.I).re = σ := by simp [Complex.mul_re]
    simpa only [B, hre2] using
      _root_.RHTower.Sieve.norm_riemannZeta_le
        (s := (σ : ℂ) + (2 * τ : ℂ) * Complex.I) (by rw [hre2]; exact hσ)
  have hq_norm : ‖q‖ = Cr ^ (-σ) := by
    rw [norm_heat, hw_re, energy, Real.rpow_def_of_pos hCr0]
    congr 1; dsimp only [Cr]; ring
  have h1q_le : ‖(1 : ℂ) - q‖ ≤ 1 + Cr ^ (-σ) := by
    refine (norm_sub_le _ _).trans ?_; rw [norm_one, hq_norm]
  have h1q_pos : 0 < ‖(1 : ℂ) - q‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun he =>
      (heat_contraction C (radix_gt_one t j) w hw0).ne (by dsimp only [q] at he; rw [← he, norm_one]))
  have hfactor : 2 * Cr ^ (-σ) / (1 + Cr ^ (-σ)) = 2 * (Cr ^ σ + 1)⁻¹ := by
    rw [Real.rpow_neg hCr0.le σ]
    field_simp [hCrσ.ne', (by linarith : Cr ^ σ + 1 ≠ 0), (by positivity : 1 + (Cr ^ σ)⁻¹ ≠ 0)]
  have hL_ge : 2 * ε ≤ ‖L‖ := by
    calc 2 * ε = 2 * (Cr ^ σ + 1)⁻¹ * cZ := by dsimp only [ε]; ring
      _ ≤ 2 * (Cr ^ σ + 1)⁻¹ * ‖riemannZeta w‖ :=
          mul_le_mul_of_nonneg_left hzeta_ge (by positivity)
      _ = (2 * Cr ^ (-σ) * ‖riemannZeta w‖) / (1 + Cr ^ (-σ)) := by rw [← hfactor]; ring
      _ ≤ (2 * Cr ^ (-σ) * ‖riemannZeta w‖) / ‖(1 : ℂ) - q‖ :=
          div_le_div_of_nonneg_left (by positivity) h1q_pos h1q_le
      _ = ‖L‖ := by
          dsimp only [L]
          rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, hq_norm]
  have hlim := (renormalized_cutoff_limit t j ⟨w, hw0, hw1⟩).norm
  dsimp only at hlim
  filter_upwards [hlim.eventually (Ioi_mem_nhds (by linarith : ε < ‖L‖))] with X hX
  exact hX.le

/-- Vertical-line obstruction in the right half of the critical strip: for every `1/2 < σ < 1` and
every `ε > 0`, positive lower density of heights `τ ≥ 0` force `‖renormalizedCutoff‖ < ε` for all
sufficiently large `X`. No `τ`-uniform floor can hold on any line `1/2 < σ < 1`. -/
theorem pos_density_small_cutoff_on_vertical_line (t : ExceptionalTime) (j : ℕ)
    {σ : ℝ} (hlo : 1 / 2 < σ) (hhi : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (c * T) ≤
        volume ({τ : ℝ | ∀ᶠ X : ℕ in atTop,
          ‖renormalizedCutoff t j X ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ < ε} ∩ Icc 0 T) := by
  set C := tailRadix t j
  let Cr : ℝ := C.val
  have hCr1 : (1 : ℝ) < Cr := by dsimp only [Cr]; exact_mod_cast radix_gt_one t j
  have hCr0 : (0 : ℝ) < Cr := by positivity
  have hrpow_lt1 : Cr ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hCr1 (by linarith)
  have hden_pos : 0 < 1 - Cr ^ (-σ) := sub_pos.mpr hrpow_lt1
  set M : ℝ := 2 * Cr ^ (-σ) / (1 - Cr ^ (-σ)) + 1
  have hM_pos : 0 < M := by positivity
  set η : ℝ := ε / (4 * M)
  have hη_pos : 0 < η := by positivity
  have hη_ne : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη_pos.ne'
  obtain ⟨c, hc, hT⟩ :=
    _root_.RHTower.exists_pos_density_zetaTargetReturnSet_const_of_isCompact
      (K := {((σ : ℂ))}) isCompact_singleton
      (fun s hs => by rw [mem_singleton_iff.mp hs, Complex.ofReal_re]; exact ⟨hlo, hhi⟩)
      hη_ne hη_pos
  refine ⟨c, hc, hT.mono fun T hT_vol => hT_vol.trans (measure_mono (inter_subset_inter_left _ ?_))⟩
  intro τ hτ
  rw [mem_setOf_eq]
  have happrox : ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I) - (η : ℂ)‖ < η :=
    hτ (σ : ℂ) (mem_singleton _)
  set w : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  have hw_re : w.re = σ := by simp [w]
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hhi.ne (by simpa [hw_re] using congrArg Complex.re he)
  have hzeta_lt : ‖riemannZeta w‖ < 2 * η := by
    have htri : ‖riemannZeta w‖ ≤ ‖riemannZeta w - (η : ℂ)‖ + ‖(η : ℂ)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (riemannZeta w - (η : ℂ)) (η : ℂ)
    have hη_norm : ‖(η : ℂ)‖ = η := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη_pos]
    linarith
  set q := heat w C
  have hq_norm : ‖q‖ = Cr ^ (-σ) := by
    rw [norm_heat, hw_re, energy, Real.rpow_def_of_pos hCr0]
    congr 1; dsimp only [Cr]; ring
  have h1q_ge : 1 - Cr ^ (-σ) ≤ ‖(1 : ℂ) - q‖ := by
    have h := norm_sub_norm_le (1 : ℂ) q
    rwa [norm_one, hq_norm] at h
  set L := 2 * q * riemannZeta w / (1 - q)
  have hL_lt : ‖L‖ < ε := by
    have hL_le : ‖L‖ ≤ (2 * Cr ^ (-σ) / (1 - Cr ^ (-σ))) * ‖riemannZeta w‖ := by
      dsimp only [L]
      rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, hq_norm]
      calc 2 * Cr ^ (-σ) * ‖riemannZeta w‖ / ‖(1 : ℂ) - q‖
          ≤ 2 * Cr ^ (-σ) * ‖riemannZeta w‖ / (1 - Cr ^ (-σ)) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos h1q_ge
        _ = (2 * Cr ^ (-σ) / (1 - Cr ^ (-σ))) * ‖riemannZeta w‖ := by ring
    have hcoeff_le : 2 * Cr ^ (-σ) / (1 - Cr ^ (-σ)) ≤ M := by dsimp only [M]; linarith
    have hprod : ‖L‖ ≤ M * (2 * η) := by
      refine hL_le.trans ?_
      calc (2 * Cr ^ (-σ) / (1 - Cr ^ (-σ))) * ‖riemannZeta w‖
          ≤ M * ‖riemannZeta w‖ := mul_le_mul_of_nonneg_right hcoeff_le (norm_nonneg _)
        _ ≤ M * (2 * η) := mul_le_mul_of_nonneg_left hzeta_lt.le hM_pos.le
    have hMη : M * (2 * η) = ε / 2 := by
      dsimp only [η]; field_simp [hM_pos.ne']; ring
    linarith
  have hlim := (renormalized_cutoff_limit t j ⟨w, hw0, hw1⟩).norm
  dsimp only at hlim
  exact hlim.eventually (Iio_mem_nhds hL_lt)

/-! ### Weighted shell cutoffs and one-prime positive surgery -/

/-- Radial Dirichlet partial sum with general arithmetic weight `a : ℕ → ℝ`. -/
def weightedRadialCutoff (a : ℕ → ℝ) (Y : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Y, (a n : ℂ) * (n : ℂ) ^ (-w)

/-- Antipodal shell sum with general arithmetic weight `a : ℕ → ℝ`. -/
def weightedShellCutoff (a : ℕ → ℝ) (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℂ :=
  let C := tailRadix t j
  2 * ∑ i ∈ Finset.range (Nat.log C.val X),
    (heat w C) ^ (i + 1) * weightedRadialCutoff a (X / C.val ^ (i + 1)) w

/-- Renormalized weighted shell cutoff with counting density `ρ`. -/
def weightedRenormalizedCutoff (a : ℕ → ℝ) (ρ : ℝ)
    (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℂ :=
  weightedShellCutoff a t j X w -
    (ρ : ℂ) * (2 / ((tailRadix t j).val - 1 : ℂ)) * ((X : ℂ) ^ (1 - w) / (1 - w))

/-- Every arithmetic weight `a : ℕ → ℝ` obeys the exact radix-`C` shell recursion. -/
theorem weightedShellCutoff_recursion (a : ℕ → ℝ) (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    let C := tailRadix t j
    weightedShellCutoff a t j X w =
      heat w C * (2 * weightedRadialCutoff a (X / C.val) w +
        weightedShellCutoff a t j (X / C.val) w) := by
  dsimp only
  set C := tailRadix t j with hCdef
  set q := heat w C with hqdef
  have hC1 : 1 < C.val := radix_gt_one t j
  by_cases hXC : X < C.val
  · have hdiv0 : X / C.val = 0 := Nat.div_eq_of_lt hXC
    have hlog0 : Nat.log C.val X = 0 := by
      rcases Nat.eq_zero_or_pos X with rfl | hX0
      · simp
      · exact (Nat.log_eq_iff (Or.inr ⟨hC1, hX0.ne'⟩)).mpr ⟨by simp; omega, by simpa using hXC⟩
    rw [weightedShellCutoff, weightedShellCutoff, ← hCdef, ← hqdef, hlog0, hdiv0]
    simp [weightedRadialCutoff]
  · push Not at hXC
    have hdiv_pos : 1 ≤ X / C.val :=
      (Nat.le_div_iff_mul_le C.pos).mpr (by simpa only [one_mul] using hXC)
    set L' := Nat.log C.val (X / C.val)
    have hlo' : C.val ^ L' ≤ X / C.val := Nat.pow_log_le_self C.val (by omega)
    have hhi' : X / C.val < C.val ^ (L' + 1) := Nat.lt_pow_succ_log_self hC1 (X / C.val)
    have hlog_succ : Nat.log C.val X = L' + 1 := by
      rw [Nat.log_eq_iff (Or.inr ⟨hC1, by omega⟩)]
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        exact (Nat.le_div_iff_mul_le C.pos).mp hlo'
      · by_contra hge
        push Not at hge
        rw [show L' + 1 + 1 = (L' + 1) + 1 by rfl, pow_succ] at hge
        exact hhi'.not_ge ((Nat.le_div_iff_mul_le C.pos).mpr hge)
    rw [weightedShellCutoff, weightedShellCutoff, ← hCdef, ← hqdef, hlog_succ,
      Finset.sum_range_succ']
    have hshift : (∑ k ∈ Finset.range L',
        q ^ (k + 1 + 1) * weightedRadialCutoff a (X / C.val ^ (k + 1 + 1)) w) =
        q * ∑ k ∈ Finset.range L',
          q ^ (k + 1) * weightedRadialCutoff a (X / C.val / C.val ^ (k + 1)) w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hdiv_eq : X / C.val ^ (k + 1 + 1) = X / C.val / C.val ^ (k + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ']
      rw [hdiv_eq, pow_succ', mul_assoc]
    change 2 * ((∑ k ∈ Finset.range L',
        q ^ (k + 1 + 1) * weightedRadialCutoff a (X / C.val ^ (k + 1 + 1)) w) +
      q ^ (0 + 1) * weightedRadialCutoff a (X / C.val ^ (0 + 1)) w) =
      q * (2 * weightedRadialCutoff a (X / C.val) w +
        2 * ∑ i ∈ Finset.range L',
          q ^ (i + 1) * weightedRadialCutoff a (X / C.val / C.val ^ (i + 1)) w)
    rw [hshift, Nat.zero_add, pow_one, pow_one]
    ring

/-- One-prime three-term positive surgery weight `1 + c₁ [p^k ∣ n] + c₂ [p^(2k) ∣ n]`. -/
def surgWeight (p k : ℕ) (c₁ c₂ : ℝ) (n : ℕ) : ℝ :=
  1 + (if p ^ k ∣ n then c₁ else 0) + (if p ^ (2 * k) ∣ n then c₂ else 0)

/-- Linear counting density of `surgWeight p k c₁ c₂`. -/
def surgDensity (p k : ℕ) (c₁ c₂ : ℝ) : ℝ :=
  1 + c₁ / ((p ^ k : ℕ) : ℝ) + c₂ / ((p ^ (2 * k) : ℕ) : ℝ)

/-- Finite Dirichlet polynomial `1 + c₁ p^(-kw) + c₂ p^(-2kw)` multiplying `ζ(w)`. -/
def surgPoly (p k : ℕ) (c₁ c₂ : ℝ) (w : ℂ) : ℂ :=
  1 + (c₁ : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-w) + (c₂ : ℂ) * ((p ^ (2 * k) : ℕ) : ℂ) ^ (-w)

private theorem sum_Icc_ite_dvd {α : Type*} [AddCommMonoid α]
    {M : ℕ} (hM : 0 < M) (Y : ℕ) (f : ℕ → α) :
    (∑ n ∈ Finset.Icc 1 Y, if M ∣ n then f n else 0) =
      ∑ q ∈ Finset.Icc 1 (Y / M), f (M * q) := by
  classical
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij (fun q _ => M * q) ?_ ?_ ?_ ?_).symm
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right M q⟩
    · exact Nat.mul_pos hM hq.1
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hM).mp hq.2
  · intro q₁ _ q₂ _ heq
    exact Nat.eq_of_mul_eq_mul_left hM heq
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn.2 with ⟨q, rfl⟩
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · simp at hn
      · exact hq0
    have hq2 : q ≤ Y / M := (Nat.le_div_iff_mul_le hM).mpr (by rw [mul_comm]; exact hn.1.2)
    exact ⟨q, Finset.mem_Icc.mpr ⟨hq1, hq2⟩, rfl⟩
  · intro _ _; rfl

theorem surgWeight_ge_one {p k : ℕ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (n : ℕ) :
    1 ≤ surgWeight p k c₁ c₂ n := by
  unfold surgWeight
  split_ifs <;> linarith

theorem surgWeight_eq_one_of_coprime {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k)
    (c₁ c₂ : ℝ) {n : ℕ} (hcop : Nat.Coprime n p) :
    surgWeight p k c₁ c₂ n = 1 := by
  have hnot_p : ¬(p ∣ n) := by
    intro hdvd
    have h1 : p ∣ Nat.gcd n p := Nat.dvd_gcd hdvd (dvd_refl p)
    rw [hcop] at h1
    exact hp.not_dvd_one h1
  have hd1 : ¬(p ^ k ∣ n) := fun hd => hnot_p ((dvd_pow_self p (by omega)).trans hd)
  have hd2 : ¬(p ^ (2 * k) ∣ n) := fun hd => hnot_p ((dvd_pow_self p (by omega)).trans hd)
  simp [surgWeight, hd1, hd2]

theorem surgWeight_mul_of_coprime {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k)
    (c₁ c₂ : ℝ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    surgWeight p k c₁ c₂ (m * n) = surgWeight p k c₁ c₂ m * surgWeight p k c₁ c₂ n := by
  by_cases hpm : p ∣ m
  · have hpn : ¬(p ∣ n) := fun h =>
      hp.not_dvd_one (hmn ▸ Nat.dvd_gcd hpm h)
    have hcop_np : Nat.Coprime n p := (hp.coprime_iff_not_dvd.mpr hpn).symm
    rw [surgWeight_eq_one_of_coprime hp hk c₁ c₂ hcop_np, mul_one]
    have hc1 : Nat.Coprime (p ^ k) n := (hp.coprime_iff_not_dvd.mpr hpn).pow_left k
    have hc2 : Nat.Coprime (p ^ (2 * k)) n := (hp.coprime_iff_not_dvd.mpr hpn).pow_left (2 * k)
    have hd1 : p ^ k ∣ m * n ↔ p ^ k ∣ m :=
      ⟨fun h => hc1.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h n⟩
    have hd2 : p ^ (2 * k) ∣ m * n ↔ p ^ (2 * k) ∣ m :=
      ⟨fun h => hc2.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h n⟩
    simp only [surgWeight, hd1, hd2]
  · have hcop_mp : Nat.Coprime m p := (hp.coprime_iff_not_dvd.mpr hpm).symm
    rw [surgWeight_eq_one_of_coprime hp hk c₁ c₂ hcop_mp, one_mul]
    have hc1 : Nat.Coprime (p ^ k) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left k
    have hc2 : Nat.Coprime (p ^ (2 * k)) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left (2 * k)
    have hd1 : p ^ k ∣ m * n ↔ p ^ k ∣ n :=
      ⟨fun h => hc1.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h m⟩
    have hd2 : p ^ (2 * k) ∣ m * n ↔ p ^ (2 * k) ∣ n :=
      ⟨fun h => hc2.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h m⟩
    simp only [surgWeight, hd1, hd2]

/-- Uniform `O(1)` linear counting remainder for `surgWeight`. -/
theorem abs_sum_surgWeight_sub_density_le {p k : ℕ} (hp : 0 < p)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (Y : ℕ) :
    |(∑ n ∈ Finset.Icc 1 Y, surgWeight p k c₁ c₂ n) - surgDensity p k c₁ c₂ * (Y : ℝ)| ≤
      c₁ + c₂ := by
  have hM1 : 0 < p ^ k := pow_pos hp k
  have hM2 : 0 < p ^ (2 * k) := pow_pos hp (2 * k)
  have hsum : (∑ n ∈ Finset.Icc 1 Y, surgWeight p k c₁ c₂ n) =
      (Y : ℝ) + c₁ * ((Y / p ^ k : ℕ) : ℝ) + c₂ * ((Y / p ^ (2 * k) : ℕ) : ℝ) := by
    unfold surgWeight
    simp only [Finset.sum_add_distrib]
    rw [sum_Icc_ite_dvd hM1 Y (fun _ => c₁), sum_Icc_ite_dvd hM2 Y (fun _ => c₂)]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  have hdiv_err : ∀ M : ℕ, 0 < M →
      0 ≤ (Y : ℝ) / (M : ℝ) - ((Y / M : ℕ) : ℝ) ∧
        (Y : ℝ) / (M : ℝ) - ((Y / M : ℕ) : ℝ) ≤ 1 := by
    intro M hM
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    have hdm : ((M * (Y / M) + Y % M : ℕ) : ℝ) = (Y : ℝ) := by exact_mod_cast Nat.div_add_mod Y M
    have hmod : ((Y % M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.mod_lt Y hM).le
    push_cast at hdm
    have heq : (Y : ℝ) / (M : ℝ) - ((Y / M : ℕ) : ℝ) = ((Y % M : ℕ) : ℝ) / (M : ℝ) := by
      field_simp [hMr.ne']; linarith
    rw [heq]
    exact ⟨by positivity, (div_le_one hMr).mpr hmod⟩
  obtain ⟨hl1, hu1⟩ := hdiv_err (p ^ k) hM1
  obtain ⟨hl2, hu2⟩ := hdiv_err (p ^ (2 * k)) hM2
  have hdiff : (∑ n ∈ Finset.Icc 1 Y, surgWeight p k c₁ c₂ n) -
      surgDensity p k c₁ c₂ * (Y : ℝ) =
      -(c₁ * ((Y : ℝ) / ((p ^ k : ℕ) : ℝ) - ((Y / p ^ k : ℕ) : ℝ)) +
        c₂ * ((Y : ℝ) / ((p ^ (2 * k) : ℕ) : ℝ) - ((Y / p ^ (2 * k) : ℕ) : ℝ))) := by
    rw [hsum]; unfold surgDensity; ring
  rw [hdiff, abs_neg, abs_le]
  constructor <;> nlinarith

private theorem weightedRadialCutoff_surgWeight {p k : ℕ} (hp : 0 < p)
    (c₁ c₂ : ℝ) (Y : ℕ) (w : ℂ) :
    weightedRadialCutoff (surgWeight p k c₁ c₂) Y w =
      radialCutoff Y w +
        (c₁ : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-w) * radialCutoff (Y / p ^ k) w +
        (c₂ : ℂ) * ((p ^ (2 * k) : ℕ) : ℂ) ^ (-w) * radialCutoff (Y / p ^ (2 * k)) w := by
  have hM1 : 0 < p ^ k := pow_pos hp k
  have hM2 : 0 < p ^ (2 * k) := pow_pos hp (2 * k)
  have hmul_sum : ∀ M : ℕ, 0 < M → ∀ c : ℝ,
      (∑ n ∈ Finset.Icc 1 Y, ((if M ∣ n then c else 0 : ℝ) : ℂ) * (n : ℂ) ^ (-w)) =
        (c : ℂ) * (M : ℂ) ^ (-w) * radialCutoff (Y / M) w := by
    intro M hM c
    have hite : ∀ n : ℕ, ((if M ∣ n then c else 0 : ℝ) : ℂ) * (n : ℂ) ^ (-w) =
        if M ∣ n then (c : ℂ) * (n : ℂ) ^ (-w) else 0 := fun n => by split_ifs <;> simp
    simp_rw [hite]
    rw [sum_Icc_ite_dvd hM Y (fun n => (c : ℂ) * (n : ℂ) ^ (-w)), radialCutoff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hMr0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hqr0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hcpow : ((M * q : ℕ) : ℂ) ^ (-w) = (M : ℂ) ^ (-w) * (q : ℂ) ^ (-w) := by
      rw [Nat.cast_mul, show (M : ℂ) * (q : ℂ) = ((M : ℝ) : ℂ) * ((q : ℝ) : ℂ) by simp,
        Complex.mul_cpow_ofReal_nonneg hMr0 hqr0]
      simp
    rw [hcpow]
    ring
  unfold weightedRadialCutoff surgWeight radialCutoff
  simp only [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul, Finset.sum_add_distrib]
  rw [hmul_sum (p ^ k) hM1 c₁, hmul_sum (p ^ (2 * k)) hM2 c₂]
  rfl

private theorem weightedShellCutoff_surgWeight (t : ExceptionalTime) (j : ℕ)
    {p k : ℕ} (hp : 0 < p) (c₁ c₂ : ℝ) (X : ℕ) (w : ℂ) :
    weightedShellCutoff (surgWeight p k c₁ c₂) t j X w =
      shellCutoff t j X w +
        (c₁ : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-w) * shellCutoff t j (X / p ^ k) w +
        (c₂ : ℂ) * ((p ^ (2 * k) : ℕ) : ℂ) ^ (-w) * shellCutoff t j (X / p ^ (2 * k)) w := by
  set C := tailRadix t j with hCdef
  set q := heat w C with hqdef
  have hC1 : 1 < C.val := radix_gt_one t j
  have htrim : ∀ M : ℕ, 0 < M →
      2 * (∑ i ∈ Finset.range (Nat.log C.val X),
          q ^ (i + 1) * ((M : ℂ) ^ (-w) * radialCutoff (X / C.val ^ (i + 1) / M) w)) =
        (M : ℂ) ^ (-w) * shellCutoff t j (X / M) w := by
    intro M _
    have hLM_le : Nat.log C.val (X / M) ≤ Nat.log C.val X := by
      rcases Nat.eq_zero_or_pos (X / M) with h0 | hpos
      · rw [h0]; simp
      · have hle : C.val ^ Nat.log C.val (X / M) ≤ X :=
          (Nat.pow_log_le_self C.val hpos.ne').trans (Nat.div_le_self X M)
        have hlt : C.val ^ Nat.log C.val (X / M) < C.val ^ (Nat.log C.val X + 1) :=
          hle.trans_lt (Nat.lt_pow_succ_log_self hC1 X)
        exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right hC1).mp hlt)
    have hsub : (∑ i ∈ Finset.range (Nat.log C.val X),
          q ^ (i + 1) * ((M : ℂ) ^ (-w) * radialCutoff (X / C.val ^ (i + 1) / M) w)) =
        ∑ i ∈ Finset.range (Nat.log C.val (X / M)),
          q ^ (i + 1) * ((M : ℂ) ^ (-w) * radialCutoff (X / M / C.val ^ (i + 1)) w) := by
      have hcomm : ∀ i : ℕ, X / C.val ^ (i + 1) / M = X / M / C.val ^ (i + 1) := fun i => by
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
      simp_rw [hcomm]
      refine (Finset.sum_subset
        (fun i hi => Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hLM_le)) ?_).symm
      intro i _ hi_not
      have hge : Nat.log C.val (X / M) ≤ i := not_lt.mp ( mt Finset.mem_range.mpr hi_not )
      have hlt_pow : X / M < C.val ^ (i + 1) :=
        (Nat.lt_pow_succ_log_self hC1 (X / M)).trans_le
          (Nat.pow_le_pow_right C.pos (Nat.succ_le_succ hge))
      rw [Nat.div_eq_of_lt hlt_pow, radialCutoff_zero, mul_zero, mul_zero]
    rw [hsub]
    have hshell := shellCutoff_eq_sum_log t j (X / M) w
    dsimp only at hshell
    rw [hshell, ← hCdef, ← hqdef, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [weightedShellCutoff, ← hCdef, ← hqdef]
  simp_rw [weightedRadialCutoff_surgWeight hp c₁ c₂ _ w, mul_add, Finset.sum_add_distrib, mul_add]
  have h0 := shellCutoff_eq_sum_log t j X w
  dsimp only at h0
  rw [← h0]
  have h1 := htrim (p ^ k) (pow_pos hp k)
  have h2 := htrim (p ^ (2 * k)) (pow_pos hp (2 * k))
  have hc1_pull : 2 * (∑ x ∈ Finset.range (Nat.log C.val X),
      q ^ (x + 1) * ((c₁ : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-w) *
        radialCutoff (X / C.val ^ (x + 1) / p ^ k) w)) =
      (c₁ : ℂ) * (2 * ∑ x ∈ Finset.range (Nat.log C.val X),
        q ^ (x + 1) * (((p ^ k : ℕ) : ℂ) ^ (-w) *
          radialCutoff (X / C.val ^ (x + 1) / p ^ k) w)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hc2_pull : 2 * (∑ x ∈ Finset.range (Nat.log C.val X),
      q ^ (x + 1) * ((c₂ : ℂ) * ((p ^ (2 * k) : ℕ) : ℂ) ^ (-w) *
        radialCutoff (X / C.val ^ (x + 1) / p ^ (2 * k)) w)) =
      (c₂ : ℂ) * (2 * ∑ x ∈ Finset.range (Nat.log C.val X),
        q ^ (x + 1) * (((p ^ (2 * k) : ℕ) : ℂ) ^ (-w) *
          radialCutoff (X / C.val ^ (x + 1) / p ^ (2 * k)) w)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hc1_pull, h1, hc2_pull, h2]
  ring

private theorem tendsto_scaled_renormalized_shift (t : ExceptionalTime) (j : ℕ)
    {M : ℕ} (hM : 0 < M) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    Tendsto (fun X : ℕ =>
      (M : ℂ) ^ (-w) * shellCutoff t j (X / M) w -
        (((M : ℝ)⁻¹ : ℝ) : ℂ) * (2 / ((C.val : ℂ) - 1)) * ((X : ℂ) ^ (1 - w) / (1 - w)))
      atTop (𝓝 ((M : ℂ) ^ (-w) * (2 * q * riemannZeta w / (1 - q)))) := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hdiv_top : Tendsto (fun X : ℕ => X / M) atTop atTop :=
    tendsto_atTop.mpr fun B => (eventually_ge_atTop (B * M)).mono fun X hX =>
      (Nat.le_div_iff_mul_le hM).mpr hX
  have hren := ((renormalized_cutoff_limit t j ⟨w, hw, hw1⟩).comp hdiv_top).const_mul ((M : ℂ) ^ (-w))
  dsimp only [Function.comp_apply] at hren
  -- Bound the counterterm rounding discrepancy `((X / M)^ (1-w) - (X / M : ℝ)^(1-w)) / (1 - w)`.
  set err : ℕ → ℂ := fun X =>
    (2 / (((C.val : ℂ) - 1) * (1 - w))) * (M : ℂ) ^ (-w) *
      ((((X / M : ℕ) : ℂ) ^ (1 - w) - (((X : ℝ) / (M : ℝ) : ℝ) : ℂ) ^ (1 - w)))
  have herr : Tendsto err atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    set K : ℝ := ‖(2 / (((C.val : ℂ) - 1) * (1 - w))) * (M : ℂ) ^ (-w)‖ * ‖(1 : ℂ) - w‖
    have h0 : Tendsto (fun X : ℕ => K * (((X / M : ℕ) : ℝ)) ^ (-w.re)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using
        (((tendsto_rpow_neg_atTop hw).comp
          (tendsto_natCast_atTop_atTop.comp hdiv_top)).const_mul K)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [eventually_ge_atTop M] with X hXM
    have hY1 : 1 ≤ X / M := (Nat.le_div_iff_mul_le hM).mpr (by simpa only [one_mul] using hXM)
    set a : ℝ := ((X / M : ℕ) : ℝ)
    set b : ℝ := (X : ℝ) / (M : ℝ)
    have ha0 : 0 < a := by dsimp only [a]; exact_mod_cast hY1
    have hdm : ((M * (X / M) + X % M : ℕ) : ℝ) = (X : ℝ) := by exact_mod_cast Nat.div_add_mod X M
    have hmod : ((X % M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.mod_lt X hM).le
    push_cast at hdm
    have hab : a ≤ b := by
      dsimp only [a, b]; rw [le_div_iff₀ hMr]; linarith [Nat.cast_nonneg (α := ℝ) (X % M)]
    have hba1 : b - a ≤ 1 := by
      have : b - a = ((X % M : ℕ) : ℝ) / (M : ℝ) := by
        dsimp only [a, b]; field_simp [hMr.ne']; linarith
      rw [this]; exact (div_le_one hMr).mpr hmod
    have hz : (0 : ℝ) ∉ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]
    have h1w_ne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw1.symm
    have hprim : (∫ u in a..b, (u : ℂ) ^ (-w)) = ((b : ℂ) ^ (1 - w) - (a : ℂ) ^ (1 - w)) / (1 - w) := by
      rw [integral_cpow (Or.inr ⟨neg_injective.ne hw1, hz⟩), show -w + 1 = 1 - w by ring]
    have hdiff_eq : (a : ℂ) ^ (1 - w) - (b : ℂ) ^ (1 - w) = -((1 - w) * ∫ u in a..b, (u : ℂ) ^ (-w)) := by
      rw [hprim]; field_simp [h1w_ne]; ring
    have hint_le : ‖∫ u in a..b, (u : ℂ) ^ (-w)‖ ≤ a ^ (-w.re) := by
      have hbd : ∀ u ∈ Set.uIoc a b, ‖(u : ℂ) ^ (-w)‖ ≤ a ^ (-w.re) := by
        intro u hu
        rw [Set.uIoc_of_le hab] at hu
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha0.trans hu.1), Complex.neg_re]
        exact Real.rpow_le_rpow_of_nonpos ha0 hu.1.le (neg_nonpos.mpr hw.le)
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
      rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hle
      exact hle.trans (mul_le_of_le_one_right (Real.rpow_nonneg ha0.le _) hba1)
    have herr_norm : ‖err X‖ = K * ‖∫ u in a..b, (u : ℂ) ^ (-w)‖ := by
      dsimp only [err, K]
      rw [show ((X / M : ℕ) : ℂ) = (a : ℂ) by simp [a],
        show (((X : ℝ) / (M : ℝ) : ℝ) : ℂ) = (b : ℂ) by rfl, hdiff_eq,
        norm_mul ((2 / (((C.val : ℂ) - 1) * (1 - w))) * (M : ℂ) ^ (-w)),
        norm_neg, norm_mul (1 - w), ← mul_assoc]
    rw [herr_norm]
    exact mul_le_mul_of_nonneg_left hint_le (by dsimp only [K]; positivity)
  have hsum := hren.add herr
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX0
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX0
  have hC1 : (C.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (radix_gt_one t j).ne')
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  have hcancel : (M : ℂ) ^ (-w) * (((X : ℝ) / (M : ℝ) : ℝ) : ℂ) ^ (1 - w) =
      (M : ℂ)⁻¹ * (X : ℂ) ^ (1 - w) := by
    simpa only [Complex.ofReal_natCast] using _root_.RHTower.cpow_neg_mul_div_cpow hMr hXpos w
  have hsub1 : (M : ℂ) ^ (-w) * renormalizedCutoff t j (X / M) w + err X =
      (M : ℂ) ^ (-w) * shellCutoff t j (X / M) w -
        (2 / (((C.val : ℂ) - 1) * (1 - w))) *
          ((M : ℂ) ^ (-w) * (((X : ℝ) / (M : ℝ) : ℝ) : ℂ) ^ (1 - w)) := by
    dsimp only [err]; rw [renormalizedCutoff_eq]; dsimp only [C] at hC1 ⊢
    field_simp [hC1, h1w]; ring
  rw [hsub1, hcancel, Complex.ofReal_inv, Complex.ofReal_natCast, div_mul_eq_div_div]
  ring

/-- Convergence of the renormalized surgery cutoffs to `surgPoly * 2 q ζ(w) / (1 - q)`. -/
theorem weightedRenormalizedCutoff_surgWeight_limit (t : ExceptionalTime) (j : ℕ)
    {p : ℕ} (hp : 0 < p) (k : ℕ) (c₁ c₂ : ℝ) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let q := heat w (tailRadix t j)
    Tendsto (fun X : ℕ =>
      weightedRenormalizedCutoff (surgWeight p k c₁ c₂) (surgDensity p k c₁ c₂) t j X w)
      atTop (𝓝 (surgPoly p k c₁ c₂ w * (2 * q * riemannZeta w / (1 - q)))) := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  have h0 := renormalized_cutoff_limit t j ⟨w, hw, hw1⟩
  have h1 := (tendsto_scaled_renormalized_shift t j (pow_pos hp k) hw hw1).const_mul (c₁ : ℂ)
  have h2 := (tendsto_scaled_renormalized_shift t j (pow_pos hp (2 * k)) hw hw1).const_mul (c₂ : ℂ)
  dsimp only at h0
  have hcomb := (h0.add h1).add h2
  have hlim_eq : 2 * q * riemannZeta w / (1 - q) +
      (c₁ : ℂ) * (((p ^ k : ℕ) : ℂ) ^ (-w) * (2 * q * riemannZeta w / (1 - q))) +
      (c₂ : ℂ) * (((p ^ (2 * k) : ℕ) : ℂ) ^ (-w) * (2 * q * riemannZeta w / (1 - q))) =
      surgPoly p k c₁ c₂ w * (2 * q * riemannZeta w / (1 - q)) := by
    unfold surgPoly; ring
  rw [hlim_eq] at hcomb
  refine hcomb.congr fun X => ?_
  rw [weightedRenormalizedCutoff, weightedShellCutoff_surgWeight t j hp c₁ c₂ X w,
    renormalizedCutoff_eq]
  unfold surgDensity; push_cast; ring

/-- One-prime positive surgery obstruction: for every nonreal `w₀` in `0 < Re w₀ < 1`, there exist
`p ∈ {2, 3}`, `k ≥ 1`, and `c₁, c₂ > 0` such that the coprime-multiplicative weight
`a = surgWeight p k c₁ c₂ ≥ 1` (untouched away from `p`, with `O(1)` linear counting remainder and
the exact radix-`C` shell recursion) has renormalized cutoffs converging to `0` at `w₀`, while on
`20999/24000 < Re w₀ < 1` its reflected cutoffs at `1 - w₀` stay bounded away from `0`. -/
theorem exists_one_prime_positive_surgery_cutoff_extinction
    (t : ExceptionalTime) (j : ℕ) {w₀ : ℂ}
    (hlo : 0 < w₀.re) (hhi : w₀.re < 1) (him : w₀.im ≠ 0) :
    ∃ (p k : ℕ) (c₁ c₂ : ℝ),
      (p = 2 ∨ p = 3) ∧ 1 ≤ k ∧ 0 < c₁ ∧ 0 < c₂ ∧
      (∀ n : ℕ, 1 ≤ surgWeight p k c₁ c₂ n) ∧
      (∀ n : ℕ, Nat.Coprime n p → surgWeight p k c₁ c₂ n = 1) ∧
      (∀ m n : ℕ, Nat.Coprime m n →
        surgWeight p k c₁ c₂ (m * n) = surgWeight p k c₁ c₂ m * surgWeight p k c₁ c₂ n) ∧
      (∀ Y : ℕ,
        |(∑ n ∈ Finset.Icc 1 Y, surgWeight p k c₁ c₂ n) - surgDensity p k c₁ c₂ * (Y : ℝ)| ≤
          c₁ + c₂) ∧
      Tendsto (fun X : ℕ =>
        weightedRenormalizedCutoff (surgWeight p k c₁ c₂) (surgDensity p k c₁ c₂) t j X w₀)
        atTop (𝓝 0) ∧
      ((20999 / 24000 : ℝ) < w₀.re →
        ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℕ in atTop,
          ε ≤ ‖weightedRenormalizedCutoff (surgWeight p k c₁ c₂) (surgDensity p k c₁ c₂)
                t j X (1 - w₀)‖) := by
  -- Select `p ∈ {2, 3}` with nontrivial phase at frequency `w₀.im ≠ 0`.
  have hphase := PositiveAnnihilator.two_three_phase_ne_one him
  obtain ⟨p, hp23, hu_ne1⟩ : ∃ p : ℕ, (p = 2 ∨ p = 3) ∧
      Complex.exp (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I) ≠ 1 := by
    rcases hphase with h2 | h3
    · exact ⟨2, Or.inl rfl, by simpa using h2⟩
    · exact ⟨3, Or.inr rfl, by simpa using h3⟩
  have hp_prime : Nat.Prime p := by rcases hp23 with rfl | rfl <;> decide
  have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp_prime.one_lt
  have hp_pos : (0 : ℝ) < p := by positivity
  set u : ℂ := Complex.exp (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I)
  have hu_norm : ‖u‖ = 1 := by
    dsimp only [u]; rw [Complex.norm_exp]
    have hre0 : (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre0, Real.exp_zero]
  obtain ⟨k, hk1, hvk_neg⟩ := PositiveAnnihilator.exists_large_pow_re_neg hu_norm hu_ne1 1
  set v : ℂ := u ^ k
  have hv_norm : ‖v‖ = 1 := by dsimp only [v]; rw [norm_pow, hu_norm, one_pow]
  set r : ℝ := (p : ℝ) ^ (-(k : ℝ) * w₀.re)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hp_pos _
  set c₁ : ℝ := -2 * v.re * r⁻¹
  set c₂ : ℝ := (r⁻¹) ^ 2
  have hc₁ : 0 < c₁ := mul_pos (by linarith) (inv_pos.mpr hr_pos)
  have hc₂ : 0 < c₂ := pow_pos (inv_pos.mpr hr_pos) 2
  -- Evaluate `(p^k)^(-w₀) = r * v` and `(p^(2k))^(-w₀) = (r * v)^2`.
  have hpk_cpow : ((p ^ k : ℕ) : ℂ) ^ (-w₀) = (r : ℂ) * v := by
    have hpk_pos : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast pow_pos hp_prime.pos k
    rw [show ((p ^ k : ℕ) : ℂ) = (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpk_pos.ne'),
      ← Complex.ofReal_log hpk_pos.le, Nat.cast_pow, Real.log_pow]
    dsimp only [r, v, u]
    rw [Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im w₀]
    push_cast
    ring
  have hp2k_sq : ∀ s : ℂ, ((p ^ (2 * k) : ℕ) : ℂ) ^ (-s) = (((p ^ k : ℕ) : ℂ) ^ (-s)) ^ 2 := by
    intro s
    have hpk_nn : (0 : ℝ) ≤ (p ^ k : ℕ) := Nat.cast_nonneg _
    rw [pow_mul', sq (p ^ k), Nat.cast_mul,
      show ((p ^ k : ℕ) : ℂ) * ((p ^ k : ℕ) : ℂ) =
        (((p ^ k : ℕ) : ℝ) : ℂ) * (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.mul_cpow_ofReal_nonneg hpk_nn hpk_nn, ← sq]
    simp
  have hpoly_zero : surgPoly p k c₁ c₂ w₀ = 0 := by
    unfold surgPoly
    rw [hp2k_sq w₀, hpk_cpow]
    have hquad := PositiveAnnihilator.unit_quadratic hv_norm
    have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
    have hsimp : 1 + (c₁ : ℂ) * ((r : ℂ) * v) + (c₂ : ℂ) * ((r : ℂ) * v) ^ 2 =
        1 + ((-2 * v.re : ℝ) : ℂ) * v + v ^ 2 := by
      dsimp only [c₁, c₂]
      push_cast
      field_simp [hr_ne]
    rw [hsimp]
    exact hquad
  have hw₀_ne1 : w₀ ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  have hlim_zero : Tendsto (fun X : ℕ =>
      weightedRenormalizedCutoff (surgWeight p k c₁ c₂) (surgDensity p k c₁ c₂) t j X w₀)
      atTop (𝓝 0) := by
    have hlim := weightedRenormalizedCutoff_surgWeight_limit t j hp_prime.pos k c₁ c₂ hlo hw₀_ne1
    dsimp only at hlim
    simpa only [hpoly_zero, zero_mul] using hlim
  refine ⟨p, k, c₁, c₂, hp23, hk1, hc₁, hc₂,
    surgWeight_ge_one hc₁ hc₂,
    fun _ hcop => surgWeight_eq_one_of_coprime hp_prime hk1 c₁ c₂ hcop,
    fun _ _ hmn => surgWeight_mul_of_coprime hp_prime hk1 c₁ c₂ hmn,
    abs_sum_surgWeight_sub_density_le hp_prime.pos hc₁ hc₂,
    hlim_zero, ?_⟩
  -- On `20999 / 24000 < w₀.re < 1`, show `surgPoly (1 - w₀) ≠ 0` and `ζ(1 - w₀) ≠ 0`.
  intro hright
  set w₁ : ℂ := 1 - w₀
  have hw₁_re0 : 0 < w₁.re := by simp [w₁]; linarith
  have hw₁_lt : w₁.re < (3001 / 24000 : ℝ) := by simp [w₁]; linarith
  have hw₁_ne1 : w₁ ≠ 1 := fun he => by rw [he, Complex.one_re] at hw₁_lt; norm_num at hw₁_lt
  have hzeta_ne : riemannZeta w₁ ≠ 0 :=
    MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_one_eighth
      hw₁_re0 hw₁_lt
  -- Every root of `1 + (-2 v.re) W + W^2 = 0` has `‖W‖ = 1`, whereas `‖r⁻¹ (p^k)^(-w₁)‖ > 1`.
  have hpoly_ne : surgPoly p k c₁ c₂ w₁ ≠ 0 := by
    set Z₁ : ℂ := ((p ^ k : ℕ) : ℂ) ^ (-w₁)
    set W : ℂ := ((r⁻¹ : ℝ) : ℂ) * Z₁
    have hW_gt1 : 1 < ‖W‖ := by
      have hpk_pos : 0 < p ^ k := pow_pos hp_prime.pos k
      have hZ_norm : ‖Z₁‖ = (p : ℝ) ^ (-(k : ℝ) * (1 - w₀.re)) := by
        dsimp only [Z₁, w₁]
        rw [Complex.norm_natCast_cpow_of_pos hpk_pos, Nat.cast_pow,
          ← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp_pos.le]
        congr 1; simp; ring
      dsimp only [W]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr_pos)]
      dsimp only [r]
      rw [hZ_norm, ← Real.rpow_neg hp_pos.le, ← Real.rpow_add hp_pos]
      apply Real.one_lt_rpow hp_gt1
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hdiff_pos : 0 < 2 * w₀.re - 1 := by linarith
      have hexp : -(-(k : ℝ) * w₀.re) + -(k : ℝ) * (1 - w₀.re) = (k : ℝ) * (2 * w₀.re - 1) := by
        ring
      rw [hexp]
      exact mul_pos hk_pos hdiff_pos
    intro hzero
    have hW_quad : 1 + ((-2 * v.re : ℝ) : ℂ) * W + W ^ 2 = 0 := by
      unfold surgPoly at hzero
      rw [hp2k_sq w₁] at hzero
      dsimp only [W, Z₁, c₁, c₂] at hzero ⊢
      push_cast at hzero ⊢
      linear_combination hzero
    have hc : v.re * v.re + v.im * v.im = 1 ^ 2 := by
      have h := Complex.normSq_eq_norm_sq v
      rwa [Complex.normSq_apply, hv_norm] at h
    have hfac : (W - v) * (W - conj v) = 1 + ((-2 * v.re : ℝ) : ℂ) * W + W ^ 2 := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im,
          Complex.sub_im, Complex.add_re, Complex.one_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, sq]
        nlinarith only [hc]
      · simp only [Complex.mul_im, Complex.sub_re, Complex.conj_re, Complex.conj_im,
          Complex.sub_im, Complex.add_im, Complex.one_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, zero_add, add_zero, sq]
        ring
    rw [← hfac] at hW_quad
    rcases mul_eq_zero.mp hW_quad with hWv | hWcv
    · have : W = v := sub_eq_zero.mp hWv
      exact hW_gt1.ne' (by rw [this, hv_norm])
    · have : W = conj v := sub_eq_zero.mp hWcv
      have hcv_sq : ‖conj v‖ ^ 2 = 1 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.conj_re, Complex.conj_im]
        nlinarith only [hc]
      have hcv : ‖conj v‖ = 1 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hcv_sq
      exact hW_gt1.ne' (by rw [this, hcv])
  -- Deduce eventual lower bound at `1 - w₀`.
  set C := tailRadix t j
  set q₁ := heat w₁ C
  have hq₁_lt : ‖q₁‖ < 1 := heat_contraction C (radix_gt_one t j) w₁ hw₁_re0
  have h1q₁ : (1 : ℂ) - q₁ ≠ 0 := sub_ne_zero.mpr fun he => hq₁_lt.ne (by rw [← he, norm_one])
  set L₁ := surgPoly p k c₁ c₂ w₁ * (2 * q₁ * riemannZeta w₁ / (1 - q₁))
  have hL₁_ne : L₁ ≠ 0 :=
    mul_ne_zero hpoly_ne
      (div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)) hzeta_ne) h1q₁)
  have hL₁_pos : 0 < ‖L₁‖ := norm_pos_iff.mpr hL₁_ne
  have hlim_raw := weightedRenormalizedCutoff_surgWeight_limit t j hp_prime.pos k c₁ c₂ hw₁_re0 hw₁_ne1
  dsimp only at hlim_raw
  have hlim₁ : Tendsto (fun X : ℕ =>
      ‖weightedRenormalizedCutoff (surgWeight p k c₁ c₂) (surgDensity p k c₁ c₂) t j X w₁‖)
      atTop (𝓝 ‖L₁‖) := hlim_raw.norm
  refine ⟨‖L₁‖ / 2, half_pos hL₁_pos, ?_⟩
  filter_upwards [hlim₁.eventually (Ioi_mem_nhds (half_lt_self hL₁_pos))] with X hX
  exact hX.le

/-! ### Out-of-support `{5, 7}` surgery extinguishing all clock comparisons and reconstructions -/

/-- Counterterm-free adjacent refinement contrast for a general arithmetic weight `a : ℕ → ℝ`. -/
def weightedAdjacentCutoff (a : ℕ → ℝ) (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℂ :=
  weightedShellCutoff a t j X w -
    (((tailRadix t j).val : ℂ) + 1) * weightedShellCutoff a t (j + 1) X w

theorem weightedAdjacentCutoff_eq_renormalized (a : ℕ → ℝ) (ρ : ℝ)
    (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    weightedAdjacentCutoff a t j X w =
      weightedRenormalizedCutoff a ρ t j X w -
        (((tailRadix t j).val : ℂ) + 1) * weightedRenormalizedCutoff a ρ t (j + 1) X w := by
  have hrad_pnat : tailRadix t (j + 1) = (tailRadix t j) ^ 2 := by
    rw [radix_sq]
    change (block t) ^ (windingOrder (refined t (j + 1)) / 2) = _
    rw [(refined_parameters t (j + 1)).2.2, (refined_parameters t j).2.2, pow_succ' 2 j,
      Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hrad_succ : (tailRadix t (j + 1)).val = (tailRadix t j).val ^ 2 := by
    rw [hrad_pnat, PNat.pow_coe]
  set c : ℂ := ((tailRadix t j).val : ℂ) with hcdef
  have hC1 : 1 < (tailRadix t j).val := radix_gt_one t j
  have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr (by rw [hcdef]; exact_mod_cast hC1.ne')
  have hc2 : c ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (by
    rw [hcdef]; exact_mod_cast (one_lt_pow₀ hC1 (by norm_num : 2 ≠ 0)).ne')
  have hden : 2 / (c - 1) - (c + 1) * (2 / (c ^ 2 - 1)) = 0 := by
    field_simp [hc1, hc2]; ring
  rw [weightedAdjacentCutoff, weightedRenormalizedCutoff, weightedRenormalizedCutoff,
    hrad_succ, Nat.cast_pow, ← hcdef]
  linear_combination (ρ : ℂ) * ((X : ℂ) ^ (1 - w) / (1 - w)) * hden

/-- Phases at `5` and `7` cannot both be trivial at a nonzero frequency. -/
theorem five_seven_phase_ne_one {γ : ℝ} (hγ : γ ≠ 0) :
    Complex.exp (-(Real.log 5 : ℂ) * (γ : ℂ) * Complex.I) ≠ 1 ∨
    Complex.exp (-(Real.log 7 : ℂ) * (γ : ℂ) * Complex.I) ≠ 1 := by
  by_contra! h
  let f : ℝ → ℂ := fun x => Complex.exp (-(x : ℂ) * (γ : ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  have hperiod {p : ℕ} (hp : Complex.exp (-(Real.log p : ℂ) * (γ : ℂ) * Complex.I) = 1)
      (x : ℝ) : f (x + Real.log p) = f x := by
    dsimp [f]
    rw [Complex.ofReal_add, neg_add, add_mul, add_mul, Complex.exp_add, hp, mul_one]
  have hind : ∀ m n : ℕ, 0 < m → 0 < n → (5 : ℕ) ^ m ≠ 7 ^ n := by
    intro m n hm _ heq
    have hd5 : 5 ∣ (5 : ℕ) ^ m := dvd_pow_self 5 hm.ne'
    rw [heq] at hd5
    have hp5 : Nat.Prime 5 := by decide
    have hd57 : 5 ∣ 7 := hp5.dvd_of_dvd_pow hd5
    omega
  have heq := _root_.RHTower.eq_of_two_dilation_invariance hf (by norm_num : 2 ≤ (5 : ℕ))
    (by norm_num : 2 ≤ (7 : ℕ)) hind (hperiod h.1) (hperiod h.2) (Real.pi / γ) 0
  have harg : -((Real.pi / γ : ℝ) : ℂ) * (γ : ℂ) * Complex.I = -(Real.pi : ℂ) * Complex.I := by
    push_cast
    have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
    field_simp
  dsimp [f] at heq
  rw [harg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] at heq
  norm_num at heq

/-- Single-prime `{5, 7}` positive surgery obstruction against multi-clock / two-prime `{2, 3}`
reconstruction: for every nonreal `w₀` in `0 < Re w₀ < 1`, modifying a single prime `p ∈ {5, 7}`
leaves all `{2, 3}`-smooth integers equal to `1` (preserving the `{2, 3}` clock supports, weights
`≥ 1`, coprime multiplicativity, `O(1)` linear counting, and all radix recursions), yet drives both
`weightedRenormalizedCutoff` and `weightedAdjacentCutoff` to `0` at `w₀` simultaneously across
**every** exceptional clock `t` and refinement `j`. -/
theorem exists_coprime_prime_surgery_killing_all_clocks {w₀ : ℂ}
    (hlo : 0 < w₀.re) (hhi : w₀.re < 1) (him : w₀.im ≠ 0) :
    ∃ (p k : ℕ) (c₁ c₂ : ℝ),
      (p = 5 ∨ p = 7) ∧ 1 ≤ k ∧ 0 < c₁ ∧ 0 < c₂ ∧
      (∀ n : ℕ, 1 ≤ surgWeight p k c₁ c₂ n) ∧
      (∀ u v : ℕ, surgWeight p k c₁ c₂ (2 ^ u * 3 ^ v) = 1) ∧
      (∀ m n : ℕ, Nat.Coprime m n →
        surgWeight p k c₁ c₂ (m * n) = surgWeight p k c₁ c₂ m * surgWeight p k c₁ c₂ n) ∧
      (∀ Y : ℕ,
        |(∑ n ∈ Finset.Icc 1 Y, surgWeight p k c₁ c₂ n) - surgDensity p k c₁ c₂ * (Y : ℝ)| ≤
          c₁ + c₂) ∧
      (∀ (t : ExceptionalTime) (j : ℕ),
        Tendsto (fun X : ℕ =>
          weightedRenormalizedCutoff (surgWeight p k c₁ c₂) (surgDensity p k c₁ c₂) t j X w₀)
          atTop (𝓝 0)) ∧
      (∀ (t : ExceptionalTime) (j : ℕ),
        Tendsto (fun X : ℕ => weightedAdjacentCutoff (surgWeight p k c₁ c₂) t j X w₀)
          atTop (𝓝 0)) := by
  have hphase := five_seven_phase_ne_one him
  obtain ⟨p, hp57, hu_ne1⟩ : ∃ p : ℕ, (p = 5 ∨ p = 7) ∧
      Complex.exp (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I) ≠ 1 := by
    rcases hphase with h5 | h7
    · exact ⟨5, Or.inl rfl, by simpa using h5⟩
    · exact ⟨7, Or.inr rfl, by simpa using h7⟩
  have hp_prime : Nat.Prime p := by rcases hp57 with rfl | rfl <;> decide
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
  set u : ℂ := Complex.exp (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I)
  have hu_norm : ‖u‖ = 1 := by
    dsimp only [u]; rw [Complex.norm_exp]
    have hre0 : (-(Real.log p : ℂ) * (w₀.im : ℂ) * Complex.I).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre0, Real.exp_zero]
  obtain ⟨k, hk1, hvk_neg⟩ := PositiveAnnihilator.exists_large_pow_re_neg hu_norm hu_ne1 1
  set v : ℂ := u ^ k
  have hv_norm : ‖v‖ = 1 := by dsimp only [v]; rw [norm_pow, hu_norm, one_pow]
  set r : ℝ := (p : ℝ) ^ (-(k : ℝ) * w₀.re)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hp_pos _
  set c₁ : ℝ := -2 * v.re * r⁻¹
  set c₂ : ℝ := (r⁻¹) ^ 2
  have hc₁ : 0 < c₁ := mul_pos (by linarith) (inv_pos.mpr hr_pos)
  have hc₂ : 0 < c₂ := pow_pos (inv_pos.mpr hr_pos) 2
  have hpk_cpow : ((p ^ k : ℕ) : ℂ) ^ (-w₀) = (r : ℂ) * v := by
    have hpk_pos : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast pow_pos hp_prime.pos k
    rw [show ((p ^ k : ℕ) : ℂ) = (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpk_pos.ne'),
      ← Complex.ofReal_log hpk_pos.le, Nat.cast_pow, Real.log_pow]
    dsimp only [r, v, u]
    rw [Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im w₀]
    push_cast
    ring
  have hp2k_sq : ((p ^ (2 * k) : ℕ) : ℂ) ^ (-w₀) = (((p ^ k : ℕ) : ℂ) ^ (-w₀)) ^ 2 := by
    have hpk_nn : (0 : ℝ) ≤ (p ^ k : ℕ) := Nat.cast_nonneg _
    rw [pow_mul', sq (p ^ k), Nat.cast_mul,
      show ((p ^ k : ℕ) : ℂ) * ((p ^ k : ℕ) : ℂ) =
        (((p ^ k : ℕ) : ℝ) : ℂ) * (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.mul_cpow_ofReal_nonneg hpk_nn hpk_nn, ← sq]
    simp
  have hpoly_zero : surgPoly p k c₁ c₂ w₀ = 0 := by
    unfold surgPoly
    rw [hp2k_sq, hpk_cpow]
    have hquad := PositiveAnnihilator.unit_quadratic hv_norm
    have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
    have hsimp : 1 + (c₁ : ℂ) * ((r : ℂ) * v) + (c₂ : ℂ) * ((r : ℂ) * v) ^ 2 =
        1 + ((-2 * v.re : ℝ) : ℂ) * v + v ^ 2 := by
      dsimp only [c₁, c₂]
      push_cast
      field_simp [hr_ne]
    rw [hsimp]
    exact hquad
  have hw₀_ne1 : w₀ ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  have hren_zero : ∀ (t : ExceptionalTime) (j : ℕ),
      Tendsto (fun X : ℕ =>
        weightedRenormalizedCutoff (surgWeight p k c₁ c₂) (surgDensity p k c₁ c₂) t j X w₀)
        atTop (𝓝 0) := by
    intro t j
    have hlim := weightedRenormalizedCutoff_surgWeight_limit t j hp_prime.pos k c₁ c₂ hlo hw₀_ne1
    dsimp only at hlim
    simpa only [hpoly_zero, zero_mul] using hlim
  have hadj_zero : ∀ (t : ExceptionalTime) (j : ℕ),
      Tendsto (fun X : ℕ => weightedAdjacentCutoff (surgWeight p k c₁ c₂) t j X w₀)
        atTop (𝓝 0) := by
    intro t j
    have h0 := hren_zero t j
    have h1 := (hren_zero t (j + 1)).const_mul (((tailRadix t j).val : ℂ) + 1)
    rw [mul_zero] at h1
    have hsub := h0.sub h1
    rw [sub_zero] at hsub
    exact hsub.congr fun X =>
      (weightedAdjacentCutoff_eq_renormalized (surgWeight p k c₁ c₂)
        (surgDensity p k c₁ c₂) t j X w₀).symm
  have hsmooth : ∀ u₂ v₃ : ℕ, surgWeight p k c₁ c₂ (2 ^ u₂ * 3 ^ v₃) = 1 := by
    intro u₂ v₃
    have hcop2 : Nat.Coprime 2 p := by rcases hp57 with rfl | rfl <;> decide
    have hcop3 : Nat.Coprime 3 p := by rcases hp57 with rfl | rfl <;> decide
    exact surgWeight_eq_one_of_coprime hp_prime hk1 c₁ c₂
      ((hcop2.pow_left u₂).mul_left (hcop3.pow_left v₃))
  exact ⟨p, k, c₁, c₂, hp57, hk1, hc₁, hc₂,
    surgWeight_ge_one hc₁ hc₂, hsmooth,
    fun _ _ hmn => surgWeight_mul_of_coprime hp_prime hk1 c₁ c₂ hmn,
    abs_sum_surgWeight_sub_density_le hp_prime.pos hc₁ hc₂,
    hren_zero, hadj_zero⟩

#print axioms cutoff_vanishes_symm_one_sub
#print axioms vertical_line_uniform_floor_of_one_lt
#print axioms pos_density_small_cutoff_on_vertical_line
#print axioms weightedShellCutoff_recursion
#print axioms surgWeight_mul_of_coprime
#print axioms abs_sum_surgWeight_sub_density_le
#print axioms weightedRenormalizedCutoff_surgWeight_limit
#print axioms exists_one_prime_positive_surgery_cutoff_extinction
#print axioms exists_coprime_prime_surgery_killing_all_clocks

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
