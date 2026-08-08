import GaloisForLFunctions.RHTower.PowerSievedLiouvilleDirichlet
import GaloisForLFunctions.RHTower.LiouvilleEvenIndexPositiveRecurrence

/-!
# Unconditional positive recurrence for the power-sieved Liouville family

For every `m ≥ 2` the sieved family `a_m` has Dirichlet series `ζ(ms)/ζ(s)`
(`LSeries_sievedLiouville_mul_riemannZeta`), whose structural pole at `s = 1/m` is unconditional:
it comes from the pole of `ζ` at `1`, not from any zeta-zero information.  The same half-plane
identity-theorem argument as for Liouville shows the exponential profile cannot decay like `x^{-b}`
for `0 ≤ b < 1/m` (`not_isBigO_sievedProfile_rpow`), which feeds the even-index parity law and gives

`1 ≤ ∑_{a+b=2q} a_m(a) a_m(b)` for infinitely many `q`
(`frequently_one_le_sievedBinaryCorrelation`)

together with the order lower edge `k - 1 ≤ Ψ_k^even` (`le_evenIndexOrder_sieved`).
At `m = 2` this is the Liouville endpoint.
-/

open Complex Filter Set MeasureTheory Asymptotics ArithmeticFunction
open scoped LSeries.notation Topology BigOperators

namespace RHTower

noncomputable section

/-! ### The Dirichlet series of the sieved family -/

theorem sievedNatPowCpow (k : ℕ) (_hk : k ≠ 0) (s : ℂ) : ∀ m : ℕ,
    ((k ^ m : ℕ) : ℂ) ^ s = ((k : ℂ) ^ s) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hcast : ((k ^ (m + 1) : ℕ) : ℂ)
          = (((k ^ m : ℕ) : ℝ) : ℂ) * (((k : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      rw [show (((k ^ m : ℕ) : ℝ) : ℂ) = ((k ^ m : ℕ) : ℂ) by push_cast; ring,
        show (((k : ℕ) : ℝ) : ℂ) = ((k : ℕ) : ℂ) by push_cast; ring, ih, pow_succ]

theorem sievedCpowNatMul (k : ℕ) (hk : (k : ℂ) ≠ 0) (s : ℂ) : ∀ m : ℕ,
    (k : ℂ) ^ ((m : ℂ) * s) = ((k : ℂ) ^ s) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℂ) * s = (m : ℂ) * s + s by push_cast; ring,
        Complex.cpow_add _ _ hk, ih, pow_succ]

theorem LSeries_powerIndicator {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < ((m : ℂ) * s).re) :
    LSeries (fun n : ℕ => powerIndicator m n) s = riemannZeta ((m : ℂ) * s) := by
  have hterm : ∀ k : ℕ,
      LSeries.term (fun n : ℕ => powerIndicator m n) s (k ^ m) =
        LSeries.term (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) ((m : ℂ) * s) k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [zero_pow hm]
      simp [LSeries.term]
    · have hknz : k ^ m ≠ 0 := pow_ne_zero m hk
      have hkc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      rw [LSeries.term_of_ne_zero hknz, LSeries.term_of_ne_zero hk,
        powerIndicator_apply, if_pos ⟨hknz, ⟨k, rfl⟩⟩,
        sievedNatPowCpow k hk s m, sievedCpowNatMul k hkc s m]
      simp [ArithmeticFunction.zeta_apply, hk]
  have hsupp : Function.support (LSeries.term (fun n : ℕ => powerIndicator m n) s)
      ⊆ Set.range fun k : ℕ => k ^ m := by
    intro n hn
    rw [Function.mem_support] at hn
    rcases eq_or_ne n 0 with rfl | h0
    · exact absurd (LSeries.term_zero (f := fun n : ℕ => powerIndicator m n) (s := s)) hn
    have hval : powerIndicator m n ≠ 0 := by
      intro h
      exact hn (by rw [LSeries.term_of_ne_zero h0, h, zero_div])
    have hpow : ∃ k, n = k ^ m := by
      by_contra hcon
      exact hval (by rw [powerIndicator_apply, if_neg (by tauto)])
    obtain ⟨k, hk⟩ := hpow
    exact ⟨k, hk.symm⟩
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, LSeries, LSeries]
  rw [← Function.Injective.tsum_eq (g := fun k : ℕ => k ^ m) (Nat.pow_left_injective hm) hsupp]
  exact tsum_congr hterm

/-- **Closed form of the sieved Dirichlet series.**  `L ↗a_m s * ζ s = ζ (m s)`. -/
theorem LSeries_sievedLiouville_mul_riemannZeta {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => sievedLiouville m n) s * riemannZeta s = riemannZeta ((m : ℂ) * s) := by
  have hms : 1 < ((m : ℂ) * s).re := by
    rw [Complex.mul_re]
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmim : ((m : ℂ)).im = 0 := by simp
    have hmre : ((m : ℂ)).re = (m : ℝ) := by simp
    rw [hmim, hmre]
    nlinarith [hs]
  have hsummableA : LSeriesSummable (fun n : ℕ => sievedLiouville m n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => norm_sievedLiouville_le_one hm n) hs
  have hsummableZ : LSeriesSummable
      ↗(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => ?_) hs
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]
  have hprod := LSeries_mul' (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := sievedLiouville m) hsummableZ hsummableA
  rw [zeta_mul_sievedLiouville] at hprod
  have hzeta : LSeries ↗(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s = riemannZeta s := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    exact LSeries_congr (fun {n} _ => by simp [ArithmeticFunction.natCoe_apply]) s
  rw [hzeta] at hprod
  rw [← LSeries_powerIndicator (m := m) (by omega) hms, hprod]
  ring

/-! ### The structural pole and its consequences -/

/-- The exponential profile of the sieved family. -/
def sievedProfile (m : ℕ) : ℝ → ℂ :=
  GaloisForLFunctions.HTGeometry.coeffLaplaceProfile (fun n : ℕ => sievedLiouville m n)

theorem sievedLiouville_apply_zero (m : ℕ) : (fun n : ℕ => sievedLiouville m n) 0 = 0 := by simp

/-- **No origin decay below the structural pole.**  For `0 ≤ b < 1/m` the sieved profile is not
`O(x^{-b})` at the origin. -/
theorem not_isBigO_sievedProfile_rpow {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (hb0 : 0 ≤ b)
    (hbm : b < 1 / (m : ℝ)) :
    ¬ (sievedProfile m =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b)) := by
  intro hO
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmC : ((m : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hb1 : b < 1 := by
    have : 1 / (m : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hm
    linarith
  have hbb : ∀ n : ℕ, ‖sievedLiouville m n‖ ≤ 1 := norm_sievedLiouville_le_one hm
  have hint : LocallyIntegrableOn (sievedProfile m) (Ioi 0) volume :=
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_locallyIntegrableOn hbb
  have htop : sievedProfile m =O[atTop] fun x : ℝ => Real.exp (-1 * x) :=
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_isBigO_exp_neg hbb
      (sievedLiouville_apply_zero m)
  set U : Set ℂ := {s : ℂ | b < s.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_decayHalfPlane b).isPreconnected
  have hnotpole : ∀ s ∈ U, ∀ j : ℕ, s ≠ -(j : ℂ) := by
    intro s hs j hcon
    have hsre : b < s.re := hs
    rw [hcon] at hsre
    simp at hsre
    linarith
  have hGammaDiff : ∀ s ∈ U, DifferentiableAt ℂ Complex.Gamma s := fun s hs =>
    Complex.differentiableAt_Gamma s (hnotpole s hs)
  have hGammaNe : ∀ s ∈ U, Complex.Gamma s ≠ 0 := fun s hs =>
    Complex.Gamma_ne_zero (hnotpole s hs)
  have hMellinDiff : ∀ s ∈ U, DifferentiableAt ℂ (mellin (sievedProfile m)) s := by
    intro s hs
    exact mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := b) (by norm_num)
      hint htop hO hs
  set G : ℂ → ℂ := fun s => mellin (sievedProfile m) s / Complex.Gamma s with hGdef
  have hGdiff : ∀ s ∈ U, DifferentiableAt ℂ G s := fun s hs =>
    (hMellinDiff s hs).div (hGammaDiff s hs) (hGammaNe s hs)
  have hlin : Differentiable ℂ fun s : ℂ => (m : ℂ) * s - 1 := by fun_prop
  have hlin' : Differentiable ℂ fun s : ℂ => s - 1 := by fun_prop
  have hF1 : AnalyticOnNhd ℂ (fun s : ℂ => ((m : ℂ) * s - 1) * G s * zetaEntire s) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    exact (((hlin s).mul (hGdiff s hs)).mul (differentiable_zetaEntire s)).differentiableWithinAt
  have hF2 : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * zetaEntire ((m : ℂ) * s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun s _ => ?_) hUopen
    have h2 : DifferentiableAt ℂ (fun s : ℂ => zetaEntire ((m : ℂ) * s)) s :=
      (differentiable_zetaEntire ((m : ℂ) * s)).comp s (by fun_prop)
    exact ((hlin' s).mul h2).differentiableWithinAt
  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2V : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  have hagree : (fun s : ℂ => ((m : ℂ) * s - 1) * G s * zetaEntire s)
      =ᶠ[𝓝 (2 : ℂ)] fun s : ℂ => (s - 1) * zetaEntire ((m : ℂ) * s) := by
    filter_upwards [hVopen.mem_nhds h2V] with s hs
    have hs1 : (1 : ℝ) < s.re := hs
    have hsU : s ∈ U := by
      have : b < s.re := by linarith
      exact this
    have hsne : s ≠ 1 := by
      intro h
      rw [h] at hs1
      simp at hs1
    have hmsne : (m : ℂ) * s ≠ 1 := by
      intro h
      have hre : ((m : ℂ) * s).re = (1 : ℂ).re := by rw [h]
      rw [Complex.mul_re] at hre
      simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.one_re] at hre
      have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    have hmel := GaloisForLFunctions.HTGeometry.mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries
      hbb (sievedLiouville_apply_zero m) hs1
    have hGs : G s = LSeries (fun n : ℕ => sievedLiouville m n) s := by
      rw [hGdef]
      simp only [sievedProfile] at *
      rw [hmel, mul_comm, mul_div_assoc, div_self (hGammaNe s hsU), mul_one]
    have hLz := LSeries_sievedLiouville_mul_riemannZeta hm hs1
    rw [hGs, zetaEntire_eq hsne, zetaEntire_eq hmsne]
    linear_combination ((m : ℂ) * s - 1) * (s - 1) * hLz
  have h2U : (2 : ℂ) ∈ U := by
    show b < (2 : ℂ).re
    simp only [Complex.re_ofNat]
    linarith
  have hinvU : ((m : ℂ))⁻¹ ∈ U := by
    show b < ((m : ℂ))⁻¹.re
    have hinvre : ((m : ℂ))⁻¹.re = 1 / (m : ℝ) := by
      rw [show ((m : ℂ)) = (((m : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
        Complex.ofReal_re, one_div]
    rw [hinvre]
    exact hbm
  have heq := hF1.eqOn_of_preconnected_of_eventuallyEq hF2 hUconn h2U hagree
  have hval := heq hinvU
  simp only at hval
  rw [mul_inv_cancel₀ hmC, sub_self, zero_mul, zero_mul, zetaEntire_one] at hval
  have hfin : ((m : ℂ))⁻¹ - 1 = 0 := by linear_combination -hval
  have : ((m : ℂ))⁻¹ = 1 := by linear_combination hfin
  rw [inv_eq_one] at this
  have : (m : ℕ) = 1 := by exact_mod_cast this
  omega

/-- Radial blow-up of the sieved Abel series at the boundary of the unit disc. -/
theorem exists_norm_gt_sieved {m : ℕ} (hm : 2 ≤ m) (B : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ B < ‖∑' N : ℕ, sievedLiouville m N * (r : ℂ) ^ N‖ := by
  refine exists_norm_gt_of_not_isBigO (fun n : ℕ => sievedLiouville m n)
    (Af := sievedProfile m)
    (fun x => GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_eq_tsum_pow _ x) ?_ B
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  exact not_isBigO_sievedProfile_rpow hm le_rfl (by positivity)

/-- **Even-index sign recurrence for the sieved family.** -/
theorem frequently_re_pos_sieved {m : ℕ} (hm : 2 ≤ m) {k : ℕ} (hk : 1 ≤ k) :
    ∃ᶠ q in atTop,
      0 < (mixedAdditiveConvolutionPower (fun n : ℕ => sievedLiouville m n) k (2 * q)).re :=
  frequently_re_pos_of_norm_unbounded _ hk
    (fun _r hr0 hr1 => GaloisForLFunctions.HTGeometry.summable_norm_coeff_mul_pow
      (norm_sievedLiouville_le_one hm) hr0 hr1)
    (exists_norm_gt_sieved hm)

/-- The ordered binary additive correlation of the sieved family. -/
def sievedBinaryCorrelation (m N : ℕ) : ℂ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    sievedLiouville m ab.1 * sievedLiouville m ab.2

theorem mixedAdditiveConvolutionPower_sieved_eq (m N : ℕ) :
    mixedAdditiveConvolutionPower (fun n : ℕ => sievedLiouville m n) 1 N
      = sievedBinaryCorrelation m N := by
  rw [mixedAdditiveConvolutionPower_one, sievedBinaryCorrelation]
  exact Finset.sum_congr rfl fun ab _ => by rw [conj_sievedLiouville]

/-- **Unconditional sign majority for the sieved family `(32)`.**  For infinitely many even totals
the ordered binary additive correlation of `a_m` has positive real part. -/
theorem frequently_re_pos_sievedBinaryCorrelation {m : ℕ} (hm : 2 ≤ m) :
    ∃ᶠ q in atTop, 0 < (sievedBinaryCorrelation m (2 * q)).re := by
  refine (frequently_re_pos_sieved hm (le_refl 1)).mono fun q hq => ?_
  rwa [mixedAdditiveConvolutionPower_sieved_eq] at hq

/-! ### The order lower edge for the sieved family -/

theorem inv_le_of_evenIndex_subpower_sieved {m : ℕ} (hm : 2 ≤ m) {k : ℕ} {α C : ℝ} (hk : 0 < k)
    (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hupper : ∀ q : ℕ,
      (mixedAdditiveConvolutionPower (fun n : ℕ => sievedLiouville m n) k (2 * q)).re
        ≤ C * ((q : ℝ) + 1) ^ α) :
    1 / (m : ℝ) ≤ (α + 1) / (2 * (k : ℝ)) := by
  by_contra hcon
  push Not at hcon
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hb0 : (0 : ℝ) ≤ (α + 1) / (2 * (k : ℝ)) := by positivity
  refine not_isBigO_sievedProfile_rpow hm hb0 hcon ?_
  have hbig := isBigO_zero_of_evenIndex_subpower (a := fun n : ℕ => sievedLiouville m n) hk hα hC
    (fun r hr0 hr1 => GaloisForLFunctions.HTGeometry.summable_norm_coeff_mul_pow
      (norm_sievedLiouville_le_one hm) hr0 hr1) hupper
  refine hbig.congr' ?_ EventuallyEq.rfl
  filter_upwards with x
  exact (GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_eq_tsum_pow _ x).symm

/-- **The sieved even-index order lower edge `(33)`.** -/
theorem le_evenIndexOrder_sieved {m : ℕ} (hm : 2 ≤ m) (j : ℕ) :
    2 * ((j : ℝ) + 1) / (m : ℝ) - 1
      ≤ evenIndexOrder (fun n : ℕ => sievedLiouville m n) (j + 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hthr : ∀ α C : ℝ, 0 ≤ α → 0 ≤ C →
      (∀ q : ℕ,
        (mixedAdditiveConvolutionPower (fun n : ℕ => sievedLiouville m n) (j + 1) (2 * q)).re
          ≤ C * ((q : ℝ) + 1) ^ α) →
      1 / (m : ℝ) ≤ (α + 1) / (2 * ((j : ℝ) + 1)) := by
    intro α C hα hC hbound
    have hkey := inv_le_of_evenIndex_subpower_sieved hm (k := j + 1) (Nat.succ_pos j) hα hC hbound
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rwa [hcast] at hkey
  have h := le_evenIndexOrder_of_subpower_threshold (norm_sievedLiouville_le_one hm) hthr
  calc 2 * ((j : ℝ) + 1) / (m : ℝ) - 1 = 2 * ((j : ℝ) + 1) * (1 / (m : ℝ)) - 1 := by ring
    _ ≤ _ := h

end

end RHTower
