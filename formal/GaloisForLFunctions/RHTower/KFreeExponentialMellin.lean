import GaloisForLFunctions.RHTower.SquarefreeExponentialRH
import GaloisForLFunctions.RHTower.BoseMellinCoordinate

/-!
# The exponentially weighted `k`-free count and its Mellin transform

For `k ≥ 2` let `A_k(t) = Σ_{m ≥ 1} μ(m)/(e^{m^k t} - 1)`, the Lambert series over `k`-th powers.
Expanding `1/(e^u - 1) = Σ_{j ≥ 1} e^{-ju}`, it is `Σ_n (Σ_{m^k ∣ n} μ(m)) e^{-nt}`; the inner sum is
the indicator of `k`-free `n`. Let `c_k = Σ_m μ(m)/m^k`.

* **Mellin transform** (`mellin_kProfile`). For `Re s > 1`,
  `∫_0^∞ A_k(t) t^{s-1} dt = Γ(s) ζ(s)/ζ(ks)`.
* **Möbius form of the error** (`kProfile_sub_eq_tsum`).
  `A_k(t) - c_k/t = Σ_m μ(m) h(m^k t)` with `h(u) = 1/(e^u - 1) - 1/u`.
* **Size** (`abs_kProfile_le`). `|A_k(t)| ≤ ζ(2)/t` and the tail decays exponentially.

**Proof of the Mellin transform.** Index the double series by pairs `(m, j)` with frequencies
`(j + 1) m^k` and apply `hasSum_mellin`. The resulting double Dirichlet series factors as
`(Σ_m μ(m) m^{-ks})(Σ_j (j+1)^{-s}) = ζ(s)/ζ(ks)`.
-/

open Filter Topology MeasureTheory Set Complex
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower.KFreeExponential

noncomputable section

open RHTower.SquarefreeExponential

/-- The Bose kernel `1/(e^u - 1)`. -/
def bose (u : ℝ) : ℝ := (Real.exp u - 1)⁻¹

theorem bose_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ bose u :=
  inv_nonneg.mpr (RHTower.SquarefreeExponential.exp_sub_one_pos hu).le

theorem bose_le_inv {u : ℝ} (hu : 0 < u) : bose u ≤ 1 / u := by
  rw [bose, ← one_div]
  exact one_div_le_one_div_of_le hu (by linarith [Real.add_one_le_exp u])

/-- `A_k(t) = Σ_m μ(m)/(e^{m^k t} - 1)`. -/
def kProfile (k : ℕ) (t : ℝ) : ℝ := ∑' m : ℕ, (μ m : ℝ) * bose ((m : ℝ) ^ k * t)

/-- `c_k = Σ_m μ(m)/m^k`. -/
def kDensity (k : ℕ) : ℝ := ∑' m : ℕ, (μ m : ℝ) / (m : ℝ) ^ k

theorem abs_moebius_real_le (m : ℕ) : |(μ m : ℝ)| ≤ 1 := by
  exact_mod_cast abs_moebius_le_one

theorem summable_inv_pow {k : ℕ} (hk : 2 ≤ k) : Summable fun m : ℕ => 1 / (m : ℝ) ^ k :=
  Real.summable_one_div_nat_pow.mpr (by omega)

theorem abs_term_le {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    |(μ m : ℝ) * bose ((m : ℝ) ^ k * t)| ≤ 1 / (m : ℝ) ^ k / t := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [zero_pow (show k ≠ 0 by omega)]
  · have hmt : 0 < (m : ℝ) ^ k * t := by positivity
    rw [abs_mul, abs_of_nonneg (bose_nonneg hmt)]
    calc |(μ m : ℝ)| * bose ((m : ℝ) ^ k * t) ≤ 1 * (1 / ((m : ℝ) ^ k * t)) :=
          mul_le_mul (abs_moebius_real_le m) (bose_le_inv hmt) (bose_nonneg hmt) zero_le_one
      _ = 1 / (m : ℝ) ^ k / t := by rw [one_mul, div_div]

theorem summable_kProfile_term {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    Summable fun m : ℕ => (μ m : ℝ) * bose ((m : ℝ) ^ k * t) :=
  Summable.of_norm_bounded ((summable_inv_pow hk).div_const t) fun m => by
    rw [Real.norm_eq_abs]; exact abs_term_le hk ht m

theorem summable_kDensity_term {k : ℕ} (hk : 2 ≤ k) :
    Summable fun m : ℕ => (μ m : ℝ) / (m : ℝ) ^ k :=
  Summable.of_norm_bounded (summable_inv_pow hk) fun m => by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (a := (m : ℝ) ^ k) (pow_nonneg (Nat.cast_nonneg m) k)]
    exact div_le_div_of_nonneg_right (abs_moebius_real_le m) (pow_nonneg (Nat.cast_nonneg m) k)

/-- `|A_k(t)| ≤ ζ(2)/t`, where `ζ(2) = Σ 1/m²`. -/
theorem abs_kProfile_le {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    |kProfile k t| ≤ (∑' m : ℕ, 1 / (m : ℝ) ^ k) / t := by
  rw [kProfile, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_kProfile_term hk ht).norm).trans ?_
  rw [← tsum_div_const]
  exact Summable.tsum_le_tsum (fun m => by rw [Real.norm_eq_abs]; exact abs_term_le hk ht m)
    (summable_kProfile_term hk ht).norm ((summable_inv_pow hk).div_const t)

/-! ## The Möbius form of the error -/

/-- `A_k(t) - c_k/t = Σ_m μ(m) h(m^k t)`. -/
theorem kProfile_sub_eq_tsum {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    kProfile k t - kDensity k / t = ∑' m : ℕ, (μ m : ℝ) * kernelH ((m : ℝ) ^ k * t) := by
  have hs2 : Summable fun m : ℕ => (μ m : ℝ) / (m : ℝ) ^ k / t :=
    (summable_kDensity_term hk).div_const t
  rw [kProfile, kDensity, ← tsum_div_const, ← (summable_kProfile_term hk ht).tsum_sub hs2]
  refine tsum_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [kernelH, bose]
  · have hmk : (m : ℝ) ^ k ≠ 0 := by positivity
    rw [kernelH, bose, ← one_div]
    field_simp

/-! ## The Mellin transform -/

/-- The frequency `(j + 1) m^k` of the pair `(m, j)`. -/
def freq (k : ℕ) (q : ℕ × ℕ) : ℝ := ((q.2 : ℝ) + 1) * (q.1 : ℝ) ^ k

theorem hasSum_bose_pairs {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 < t) :
    HasSum (fun q : ℕ × ℕ => ((μ q.1 : ℂ)) * (Real.exp (-freq k q * t) : ℂ))
      ((kProfile k t : ℝ) : ℂ) := by
  -- the real family over pairs
  set f : ℕ × ℕ → ℝ := fun q => (μ q.1 : ℝ) * Real.exp (-freq k q * t) with hf
  have hfiber : ∀ m : ℕ, HasSum (fun j : ℕ => f (m, j)) ((μ m : ℝ) * bose ((m : ℝ) ^ k * t)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hf]
    · have hmt : 0 < (m : ℝ) ^ k * t := by positivity
      have h := (hasSum_boseKernel hmt).mul_left (μ m : ℝ)
      refine h.congr_fun fun j => ?_
      simp only [hf, freq]
      congr 2
      ring
  have hnorm : ∀ m : ℕ, Summable fun j : ℕ => ‖f (m, j)‖ := fun m => (hfiber m).summable.norm
  have hfiber_norm : ∀ m : ℕ, ∑' j : ℕ, ‖f (m, j)‖ ≤ 1 / (m : ℝ) ^ k / t := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hf, zero_pow (show k ≠ 0 by omega)]
    · have hmt : 0 < (m : ℝ) ^ k * t := by positivity
      have hn : ∀ j : ℕ, ‖f (m, j)‖ = |(μ m : ℝ)| * Real.exp (-((j : ℝ) + 1) * ((m : ℝ) ^ k * t)) := by
        intro j
        simp only [hf, freq, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        congr 2
        ring
      rw [tsum_congr hn, tsum_mul_left, (hasSum_boseKernel hmt).tsum_eq]
      calc |(μ m : ℝ)| * (Real.exp ((m : ℝ) ^ k * t) - 1)⁻¹ ≤ 1 * (1 / ((m : ℝ) ^ k * t)) :=
            mul_le_mul (abs_moebius_real_le m) (bose_le_inv hmt) (bose_nonneg hmt) zero_le_one
        _ = 1 / (m : ℝ) ^ k / t := by rw [one_mul, div_div]
  have hsumm : Summable f := by
    refine Summable.of_norm ?_
    refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hnorm, ?_⟩
    refine Summable.of_nonneg_of_le (fun m => tsum_nonneg fun _ => norm_nonneg _) hfiber_norm
      ((summable_inv_pow hk).div_const t)
  have hval : ∑' q : ℕ × ℕ, f q = kProfile k t := by
    rw [hsumm.tsum_prod, kProfile]
    exact tsum_congr fun m => (hfiber m).tsum_eq
  have hreal : HasSum f (kProfile k t) := hval ▸ hsumm.hasSum
  have h := Complex.ofRealCLM.hasSum hreal
  refine h.congr_fun fun q => ?_
  simp [hf]

theorem summable_mellin_pairs {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable fun q : ℕ × ℕ => ‖((μ q.1 : ℂ))‖ / freq k q ^ s.re := by
  have hσ : 0 < s.re := by linarith
  set g₁ : ℕ → ℝ := fun m => |(μ m : ℝ)| / ((m : ℝ) ^ k) ^ s.re with hg₁
  set g₂ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) ^ s.re with hg₂
  have hs1 : Summable g₁ := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (Real.summable_one_div_nat_rpow.mpr (show 1 < (k : ℝ) * s.re by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith))
    rw [hg₁]
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
    exact div_le_div_of_nonneg_right (abs_moebius_real_le m) (by positivity)
  have hs2 : Summable g₂ := by
    have h := (Real.summable_one_div_nat_rpow (p := s.re)).mpr hs
    exact ((summable_nat_add_iff 1).mpr h).congr fun j => by simp [hg₂]
  have hprod := hs1.mul_of_nonneg hs2 (fun m => by positivity) (fun j => by positivity)
  refine hprod.congr fun q => ?_
  simp only [hg₁, hg₂, freq, Complex.norm_intCast]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  field_simp

theorem natCast_pow_cpow (m k : ℕ) (s : ℂ) :
    ((((m : ℝ) ^ k : ℝ)) : ℂ) ^ s = ((m : ℂ)) ^ ((k : ℂ) * s) := by
  rw [Complex.cpow_nat_mul]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (Nat.cast_nonneg m), ih, pow_succ]
    push_cast
    rfl

/-- **The Mellin transform.** `𝓜A_k(s) = Γ(s) ζ(s)/ζ(ks)` for `Re s > 1`. -/
theorem mellin_kProfile {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => ((kProfile k t : ℝ) : ℂ)) s =
      Complex.Gamma s * (riemannZeta s / riemannZeta (k * s)) := by
  have hs0 : 0 < s.re := by linarith
  have hks : 1 < ((k : ℂ) * s).re := by
    have hre : ((k : ℂ) * s).re = (k : ℝ) * s.re := by simp [Complex.mul_re]
    rw [hre]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hp : ∀ q : ℕ × ℕ, ((μ q.1 : ℂ)) = 0 ∨ 0 < freq k q := by
    intro q
    rcases Nat.eq_zero_or_pos q.1 with h0 | hm
    · left; simp [h0]
    · right; unfold freq; positivity
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun q : ℕ × ℕ => ((μ q.1 : ℂ)) * (Real.exp (-freq k q * t) : ℂ))
      (((kProfile k t : ℝ) : ℂ)) := fun t ht => hasSum_bose_pairs hk ht
  have hmain := hasSum_mellin hp hs0 hF (summable_mellin_pairs hk hs)
  rw [← hmain.tsum_eq]
  -- factor the double series
  set u : ℕ → ℂ := fun m => (μ m : ℂ) / ((((m : ℝ) ^ k : ℝ)) : ℂ) ^ s with hu
  set v : ℕ → ℂ := fun j => 1 / ((((j : ℝ) + 1 : ℝ)) : ℂ) ^ s with hv
  have hterm : ∀ q : ℕ × ℕ, Complex.Gamma s * ((μ q.1 : ℂ)) / ((freq k q : ℝ) : ℂ) ^ s =
      Complex.Gamma s * (u q.1 * v q.2) := by
    intro q
    simp only [hu, hv, freq]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    ring
  have hun : Summable fun m => ‖u m‖ := by
    have h := (LSeriesSummable_of_bounded_of_one_lt_re (f := fun m => (μ m : ℂ)) (m := 1)
      (fun n _ => by rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one) hks).norm
    refine h.congr fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hu]
    · rw [LSeries.term_of_ne_zero hm.ne', hu]
      simp only
      rw [natCast_pow_cpow]
  have hvn : Summable fun j => ‖v j‖ := by
    have h := (Real.summable_one_div_nat_rpow (p := s.re)).mpr hs
    refine ((summable_nat_add_iff 1).mpr h).congr fun j => ?_
    simp only [hv, norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
    push_cast
    ring_nf
  rw [tsum_congr hterm, tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hun hvn]
  have hU : ∑' m, u m = (riemannZeta (k * s))⁻¹ := by
    rw [← RHTower.LSeries_moebius_eq_inv_riemannZeta hks, LSeries]
    refine tsum_congr fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hu]
    · rw [LSeries.term_of_ne_zero hm.ne', hu]
      simp only
      rw [natCast_pow_cpow]
  have hV : ∑' j, v j = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun j => ?_
    simp [hv]
  rw [hU, hV]
  ring

end

end RHTower.KFreeExponential
