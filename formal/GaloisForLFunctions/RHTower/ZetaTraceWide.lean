import GaloisForLFunctions.RHTower.FamilyTraceWide
import Zeta23.GammaFacts.Complete

/-!
# The prime-side trace for ζ at any bandwidth

Alpöge–Furman's trace proposition for `ζ` is stated under `LocalHypsCore`, which caps the bandwidth at
`λ ≤ 1`.  Its proof uses only the window facts collected in `LocalHypsCoreW`.  Splitting the diagonal
entries of the Gram matrix along `ν_X = μ + Π_X + P_X` (`GentryA_diag_eq_W`):

* the archimedean part is the modulus-one archimedean trace `tr G̃(1, 0)` of the Dirichlet theory, since
  `μ = μ_{0,1}` (`mu_eq_muq`), already evaluated at every bandwidth (`trace_mu_wide`);
* the pole part is `O(L √X)` (`Pi_part_bound_W`);
* the prime part is `O(L √X)`, since `P_X = P_{X,1}` (`PX_eq_PXc_one`).

Hence (`prop_trace_zeta_wide`) at every bandwidth `λ > 0`

`|tr G̃ − a L N| ≤ C L (1 + log T + √X)`   whenever `|N − Tℓ₁/2π| ≤ A log T`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem mu_eq_muq : Zeta23.mu = muq 0 1 := by
  funext τ
  unfold Zeta23.mu muq
  rw [Nat.cast_one, show Real.log (1 / π) = -Real.log π by rw [one_div, Real.log_inv]]
  simp only [Nat.cast_zero, zero_div, add_zero]
  ring

theorem PX_eq_PXc_one (X τ : ℝ) : Zeta23.PX X τ = PXc (fun _ => 1) X τ := by
  rw [PXc_eq_sum_cos_sin]
  unfold Zeta23.PX
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
  simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, add_zero]
  rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

theorem coeffOK_one : CoeffOK 1 (fun _ => 1) :=
  ⟨fun _ => by simp, fun n h => absurd (Nat.coprime_one_right n) h⟩

theorem coeffOK_zero : CoeffOK 1 (fun _ => 0) :=
  ⟨fun _ => by simp, fun _ _ => rfl⟩

theorem PiX_shift_bound_W (hF : LocalHypsCoreW cϱ p F) {t : ℝ} (ht : 2 ≤ t) (r : ℝ) :
    |Zeta23.PiX p.X (t + r)| ≤ 6 * Real.sqrt p.X / t + 12 * Real.sqrt p.X * r ^ 2 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hb := hF.PiX_bound (t + r)
  have hA : 0 ≤ 6 * Real.sqrt p.X / t := by positivity
  have hB : 0 ≤ 12 * Real.sqrt p.X * r ^ 2 / t ^ 2 := by positivity
  rcases le_or_gt |r| (t / 2) with hr | hr
  · refine hb.trans ((le_of_le_of_eq ?_ rfl).trans (le_add_of_nonneg_right hB))
    have : t / 2 ≤ 1 + |t + r| := by
      have : t - |r| ≤ |t + r| := by
        have := abs_sub_abs_le_abs_sub t (-r)
        rw [abs_neg, sub_neg_eq_add, abs_of_pos ht0] at this; linarith
      linarith
    calc 3 * Real.sqrt p.X / (1 + |t + r|) ≤ 3 * Real.sqrt p.X / (t / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) this
      _ = 6 * Real.sqrt p.X / t := by field_simp; ring
  · refine hb.trans (le_trans ?_ (le_add_of_nonneg_left hA))
    have h1 : 3 * Real.sqrt p.X / (1 + |t + r|) ≤ 3 * Real.sqrt p.X :=
      div_le_self (by positivity) (by linarith [abs_nonneg (t + r)])
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have : t ^ 2 ≤ 4 * r ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
    nlinarith

theorem Pi_part_bound_W (hF : LocalHypsCoreW cϱ p F) {t : ℝ} (ht : 2 ≤ t) :
    |∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)|
      ≤ (6 * Real.sqrt p.X / t) * (2 * π * F.a * p.L)
        + (12 * Real.sqrt p.X / t ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2 := by
  have hgi : Integrable (fun r => (6 * Real.sqrt p.X / t) * F.phiHat r ^ 2
      + (12 * Real.sqrt p.X / t ^ 2) * (F.phiHat r ^ 2 * r ^ 2)) :=
    (hF.phiHat_sq_integrable.const_mul _).add (hF.phiHat_sq_mul_sq_integrable.const_mul _)
  rw [← Real.norm_eq_abs]
  calc ‖∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)‖
      ≤ ∫ r, (6 * Real.sqrt p.X / t) * F.phiHat r ^ 2
          + (12 * Real.sqrt p.X / t ^ 2) * (F.phiHat r ^ 2 * r ^ 2) := by
        refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun r => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc F.phiHat r ^ 2 * |Zeta23.PiX p.X (t + r)|
            ≤ F.phiHat r ^ 2 * (6 * Real.sqrt p.X / t + 12 * Real.sqrt p.X * r ^ 2 / t ^ 2) := by
              gcongr; exact PiX_shift_bound_W hF ht r
          _ = _ := by ring
    _ = _ := by
        rw [integral_add (hF.phiHat_sq_integrable.const_mul _)
          (hF.phiHat_sq_mul_sq_integrable.const_mul _), integral_const_mul, integral_const_mul,
          hF.phiHat_sq_integral]

theorem Pi_part_integrable_W (hF : LocalHypsCoreW cϱ p F) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)) := by
  refine hF.phiHat_sq_mul_integrable_of_bdd (hF.PiX_cont.comp (continuous_const_add t))
    (c := 3 * Real.sqrt p.X) (fun x => (hF.PiX_bound _).trans ?_)
  exact div_le_self (by positivity) (by linarith [abs_nonneg (t + x)])

theorem P_part_integrable_W (hF : LocalHypsCoreW cϱ p F) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.PX p.X (t + r)) := by
  refine hF.phiHat_sq_mul_integrable_of_bdd ((PX_continuous p.X).comp (continuous_const_add t))
    (c := 1 / Real.pi * ∑ n ∈ primeRange p.X, acoef n) (fun x => ?_)
  simp only [PX_eq]
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have ha : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg ha]
  calc acoef n * |Real.cos ((t + x) * ycoef n)| ≤ acoef n * 1 := by
        gcongr; exact Real.abs_cos_le_one _
    _ = acoef n := mul_one _

theorem mu_part_integrable_W (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCoreW cϱ p F) {t : ℝ}
    (ht0 : 0 < t) : Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) := by
  obtain ⟨M, hM0, hM⟩ := mu_linear_bound hΓ
  have hmeas : AEStronglyMeasurable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) volume := by
    have hc : Continuous fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r) := by
      have := hΓ.smooth.continuous; have := hF.phiHat_cont; fun_prop
    exact hc.aestronglyMeasurable
  refine Integrable.mono'
    ((hF.phiHat_sq_integrable.const_mul (M + t)).add hF.phiHat_sq_mul_abs_integrable) hmeas ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have htr : |t + r| ≤ t + |r| := by
    calc |t + r| ≤ |t| + |r| := abs_add_le _ _
      _ = t + |r| := by rw [abs_of_pos ht0]
  calc F.phiHat r ^ 2 * |Zeta23.mu (t + r)| ≤ F.phiHat r ^ 2 * (M + |t + r|) := by
        gcongr; exact hM _
    _ ≤ F.phiHat r ^ 2 * (M + (t + |r|)) := by gcongr
    _ = (M + t) * F.phiHat r ^ 2 + F.phiHat r ^ 2 * |r| := by ring

/-- **Decomposition of a diagonal entry at any bandwidth.** -/
theorem GentryA_diag_eq_W (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCoreW cϱ p F) (k : ℤ)
    (hk : 0 < p.tau k) :
    GentryA p F k k = (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) := by
  unfold GentryA
  have htrans : (∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau k) * Zeta23.nuX p.X τ)
      = ∫ r, F.phiHat r ^ 2 * Zeta23.nuX p.X (p.tau k + r) := by
    rw [← integral_add_right_eq_self _ (p.tau k)]
    congr 1; funext r; simp only [add_sub_cancel_right]; ring_nf
  rw [htrans]
  have hν : ∀ r, F.phiHat r ^ 2 * Zeta23.nuX p.X (p.tau k + r)
      = (F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r) + F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
        + F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r) := by
    intro r; simp only [Zeta23.nuX]; ring
  simp_rw [hν]
  have h12 : Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)
      + F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)) :=
    (mu_part_integrable_W hΓ hF hk).add (Pi_part_integrable_W hF _)
  rw [integral_add h12 (P_part_integrable_W hF _),
    integral_add (mu_part_integrable_W hΓ hF hk) (Pi_part_integrable_W hF _)]

/-- `tr G̃ = tr G̃(1, 0) + L⁻¹ Σ_k G^Π_kk + L⁻¹ Σ_k G^P_kk`. -/
theorem trGtA_split (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) :
    trGtA p F = trGtChiA 0 1 (fun _ => 0) p F
      + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
      + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) := by
  have hL : 0 < p.L := hF.L_pos
  have hΓq := GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl
  unfold trGtA trGtChiA
  rw [Fin.sum_univ_eq_sum_range (fun k => GentryA p F k k) p.d,
    Fin.sum_univ_eq_sum_range (fun k => GentryChiA 0 1 (fun _ => 0) p F k k) p.d]
  have hτ : ∀ k ∈ Finset.range p.d, 0 < p.tau k := fun k hk =>
    lt_of_lt_of_le hT (p.tau_mem hL hT.le hk).1
  rw [Finset.sum_congr rfl fun (k : ℕ) hk => GentryA_diag_eq_W Zeta23.gammaFacts hF (k : ℤ) (hτ k hk),
    Finset.sum_congr rfl fun (k : ℕ) hk =>
      GentryChiA_diag_eq hΓq le_rfl hF coeffOK_zero (k : ℤ) (hτ k hk)]
  simp_rw [PXc_zero, mul_zero, integral_zero, add_zero, ← mu_eq_muq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- **The trace for ζ at any bandwidth.** -/
theorem prop_trace_zeta_wide {lam : ℝ} (hlam : 0 < lam) (A : ℝ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F →
      ∀ N : ℝ, |N - p.T / (2 * π) * ell1q 1 p.T| ≤ A * Real.log p.T →
        |trGtA p F - F.a * p.L * N| ≤ C * (p.L * (1 + Real.log p.T + Real.sqrt p.X)) := by
  have hΓ0 := GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl
  obtain ⟨K0, hK00, hK0⟩ := muq_increment_bound hΓ0 le_rfl
  obtain ⟨Cm0, Tm0, hCm00, hCm0⟩ := muq_abs_le 0 1 hΓ0 le_rfl
  obtain ⟨τ0, -, hτ0⟩ := muq_nonneg_eventually hΓ0 le_rfl
  obtain ⟨Cu0, Tu0, hCu0⟩ := hΓ0.int_mu
  obtain ⟨x₀, hx₀⟩ := Cheb.chebyshevMertens.cheb1b
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨Cb, hCbdef⟩ : ∃ x : ℝ, x = K0 * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cm0 / lam + |Cu0| + |A| :=
    ⟨_, rfl⟩
  refine ⟨|Cb| + (14 + 2 * cϱ ^ 2) + 3 / Real.log 2,
    max (max (max Tm0 Tu0) (τ0 + 1)) (max (2 * π * Real.exp (|x₀| / lam)) 4), by positivity,
    fun p F hp hT hF N hN => ?_⟩
  have hTa := (le_max_left _ _).trans hT
  have hTb := (le_max_right _ _).trans hT
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T := (le_max_left _ _).trans hTb
  have hT4 : 4 ≤ p.T := (le_max_right _ _).trans hTb
  have hT0 : 0 < p.T := by linarith
  have hL : 0 < p.L := hF.L_pos
  have hL8 := hF.eight_le_L
  have hlam0 : 0 < p.lam := hp ▸ hlam
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hp]; exact hTx)
  have hsX0 : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hlogT : 0 ≤ Real.log p.T := Real.log_nonneg (by linarith)
  have ha0 : 0 ≤ F.a := hF.a_pos.le
  have ha1 : F.a ≤ 1 := hF.a_le_one
  have hc4 := hF.four_le_cϱ
  -- the archimedean part
  have hbase : |trGtChiA 0 1 (fun _ => 0) p F - F.a * p.L * N|
      ≤ |Cb| * (p.L * (1 + Real.log p.T + Real.sqrt p.X)) := by
    have h := trace_mu_wide (le_refl 0 |>.trans (by norm_num)) hK00 hK0 hCm00.le
      (hCm0 p ((le_max_left _ _).trans ((le_max_left _ _).trans hTa))) hτ0
      (hCu0 p.T ((le_max_right _ _).trans ((le_max_left _ _).trans hTa))) hF hT4
      ((le_max_right _ _).trans hTa) N hN
    refine h.trans ?_
    rw [hp, ← hCbdef]
    have h1 : p.L * (1 + Real.log p.T) ≤ p.L * (1 + Real.log p.T + Real.sqrt p.X) :=
      mul_le_mul_of_nonneg_left (by linarith) hL.le
    exact mul_le_mul (le_abs_self _) h1 (by positivity) (abs_nonneg _)
  -- the pole part
  set I₂ := ∫ r, F.phiHat r ^ 2 * r ^ 2 with hI₂
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun r => by positivity
  have hI₂le : I₂ ≤ 8 + 2 * cϱ ^ 2 := by
    refine hF.integral_phiHat_sq_mul_sq_le.trans ?_
    have : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith [hF.one_le_w])
    linarith
  have hPi : |(p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))|
      ≤ (14 + 2 * cϱ ^ 2) * (p.L * Real.sqrt p.X) := by
    have hterm : ∀ k ∈ Finset.range p.d, |∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)|
        ≤ (6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T ^ 2) * I₂ := by
      intro k hk
      have hτk := p.tau_mem hL hT0.le hk
      have h2 : 2 ≤ p.tau k := by linarith [hτk.1]
      refine (Pi_part_bound_W hF h2).trans ?_
      have hA : 6 * Real.sqrt p.X / p.tau k ≤ 6 * Real.sqrt p.X / p.T :=
        div_le_div_of_nonneg_left (by positivity) hT0 hτk.1
      have hB : 12 * Real.sqrt p.X / p.tau k ^ 2 ≤ 12 * Real.sqrt p.X / p.T ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hT0.le hτk.1 2)
      have hC : 2 * π * F.a * p.L ≤ 2 * π * p.L := by
        have := mul_le_mul_of_nonneg_left ha1 (by positivity : (0:ℝ) ≤ 2 * π)
        nlinarith
      have hD : (6 * Real.sqrt p.X / p.tau k) * (2 * π * F.a * p.L)
          ≤ (6 * Real.sqrt p.X / p.T) * (2 * π * p.L) :=
        mul_le_mul hA hC (by positivity) (by positivity)
      have hE : (12 * Real.sqrt p.X / p.tau k ^ 2) * I₂ ≤ (12 * Real.sqrt p.X / p.T ^ 2) * I₂ :=
        mul_le_mul_of_nonneg_right hB hI₂0
      linarith
    have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hd : (p.d : ℝ) ≤ p.L * p.T / (2 * π) := by
      unfold Setting.d; exact Nat.floor_le (by positivity)
    rw [abs_mul, abs_of_pos (inv_pos.mpr hL)]
    have hbr0 : 0 ≤ (6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T ^ 2) * I₂ := by
      positivity
    have h1 : (p.L)⁻¹ * |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)|
        ≤ (p.L)⁻¹ * ((p.L * p.T / (2 * π)) * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L)
          + (12 * Real.sqrt p.X / p.T ^ 2) * I₂)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hd hbr0)) (by positivity)
    have e : (p.L)⁻¹ * ((p.L * p.T / (2 * π)) * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L)
          + (12 * Real.sqrt p.X / p.T ^ 2) * I₂))
        = 6 * (p.L * Real.sqrt p.X) + (6 / π) * (Real.sqrt p.X * I₂ / p.T) := by
      field_simp; ring
    rw [e] at h1
    have h2 : (6 / π) * (Real.sqrt p.X * I₂ / p.T) ≤ (8 + 2 * cϱ ^ 2) * (p.L * Real.sqrt p.X) := by
      have hπ : 6 / π ≤ 2 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
      have hq : Real.sqrt p.X * I₂ / p.T ≤ Real.sqrt p.X * I₂ := div_le_self (by positivity) (by linarith)
      have h3 : Real.sqrt p.X * I₂ ≤ Real.sqrt p.X * (8 + 2 * cϱ ^ 2) :=
        mul_le_mul_of_nonneg_left hI₂le hsX0
      have h4 : (6 / π) * (Real.sqrt p.X * I₂ / p.T) ≤ 2 * (Real.sqrt p.X * (8 + 2 * cϱ ^ 2)) :=
        mul_le_mul hπ (hq.trans h3) (by positivity) (by norm_num)
      have h5 : 2 * (Real.sqrt p.X * (8 + 2 * cϱ ^ 2)) ≤ (8 + 2 * cϱ ^ 2) * (p.L * Real.sqrt p.X) := by
        have h2L : (2:ℝ) ≤ p.L := by linarith only [hL8]
        have := mul_le_mul_of_nonneg_right h2L (by positivity : (0:ℝ) ≤ Real.sqrt p.X * (8 + 2 * cϱ ^ 2))
        have e : (8 + 2 * cϱ ^ 2) * (p.L * Real.sqrt p.X) = p.L * (Real.sqrt p.X * (8 + 2 * cϱ ^ 2)) := by
          ring
        linarith only [this, e]
      linarith only [h4, h5]
    linarith only [h1, h2]
  -- the prime part
  have hP : |(p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r))|
      ≤ 3 / Real.log 2 * (p.L * Real.sqrt p.X) := by
    have hPX : ∀ k ∈ Finset.range p.d, (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r))
        = ∫ r, F.phiHat r ^ 2 * PXc (fun _ => 1) p.X (p.tau k + r) := fun k _ => by
      simp_rw [PX_eq_PXc_one]
    rw [Finset.sum_congr rfl hPX]
    have h := sum_P_part_chi_bound hF coeffOK_one
    have hconv : ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))
        = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, Λ n / Real.sqrt n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    rw [hconv] at h
    have h3 := hx₀ p.X hX
    rw [abs_mul, abs_of_pos (inv_pos.mpr hL)]
    calc (p.L)⁻¹ * |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc (fun _ => 1) p.X (p.tau k + r)|
        ≤ (p.L)⁻¹ * (p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X)) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 / Real.log 2 * (p.L * Real.sqrt p.X) := by field_simp
  rw [trGtA_split hF hT0]
  have hW : p.L * Real.sqrt p.X ≤ p.L * (1 + Real.log p.T + Real.sqrt p.X) :=
    mul_le_mul_of_nonneg_left (by linarith) hL.le
  have hsplit : trGtChiA 0 1 (fun _ => 0) p F
        + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
        + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r))
        - F.a * p.L * N
      = (trGtChiA 0 1 (fun _ => 0) p F - F.a * p.L * N)
        + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
        + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) := by
    ring
  rw [hsplit]
  refine (abs_add_three _ _ _).trans ?_
  have hW0 : 0 ≤ p.L * (1 + Real.log p.T + Real.sqrt p.X) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hW (by positivity : (0:ℝ) ≤ 14 + 2 * cϱ ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hW (by positivity : (0:ℝ) ≤ 3 / Real.log 2)
  have e : (|Cb| + (14 + 2 * cϱ ^ 2) + 3 / Real.log 2) * (p.L * (1 + Real.log p.T + Real.sqrt p.X))
      = |Cb| * (p.L * (1 + Real.log p.T + Real.sqrt p.X))
        + (14 + 2 * cϱ ^ 2) * (p.L * (1 + Real.log p.T + Real.sqrt p.X))
        + 3 / Real.log 2 * (p.L * (1 + Real.log p.T + Real.sqrt p.X)) := by ring
  linarith only [hbase, hPi, hP, h2, h3, e]

end RHTower
