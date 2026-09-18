import GaloisForLFunctions.RHTower.ZetaGateProductAFEBlockExpansion
import GaloisForLFunctions.RHTower.ZetaGateProductAFEDiagonalIndex
import GaloisForLFunctions.RHTower.ZetaGateProductAFEMainTermInputs
import GaloisForLFunctions.RHTower.DirectOffDiagonalEnvelope
import GaloisForLFunctions.RHTower.SmoothDiagonalContour
import GaloisForLFunctions.RHTower.DualDiagonalContour

/-!
# The block twisted moment of `ζΨ`: diagonals and off-diagonals

For a mollifier pair `(h,k)` with `g = gcd(h,k)`, `h = g h'`, `k = g k'`, the direct series
`Σ'_P directTerm` splits into its diagonal `(m+1)h = (n+1)k`, which is
`(hk)^{-σ₀} (h'k')^{-σ₀} · smoothDiagonal σ₀ (h'k') x · ∫w`, and an off-diagonal part whose terms
have the norms `directOffDiagTerm`.  The dual series splits in the same way along
`(n+1)h = (m+1)k` with the diagonal `(hk)^{-σ₀} (h'k')^{-(½+d)} ∫ w(t)·dualDiagonal d (h'k') x t dt`
and off-diagonal norms `dualOffDiagTerm`.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## The mass of the window -/

theorem integral_norm_blockWindowC_le {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q) :
    ∫ t, ‖blockWindowC p q η t‖ ≤ q - p + 2 * η := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (p - η) (q + η))
    (fun t ht => by rw [blockWindowC_eq_zero hη ht, norm_zero])]
  calc ∫ t in Set.Icc (p - η) (q + η), ‖blockWindowC p q η t‖
      ≤ ∫ _ in Set.Icc (p - η) (q + η), (1 : ℝ) :=
        setIntegral_mono_on (integrable_blockWindowC hη).norm.integrableOn
          (integrableOn_const (by simp)) measurableSet_Icc
          (fun t _ => norm_blockWindowC_le_one p q η t)
    _ = q - p + 2 * η := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

theorem norm_blockWindowC_eq (p q η t : ℝ) : ‖blockWindowC p q η t‖ = blockWindow p q η t := by
  unfold blockWindowC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (blockWindow_nonneg p q η t)]

theorem integral_blockWindowC_eq_ofReal (p q η : ℝ) :
    ∫ t, blockWindowC p q η t = ((∫ t, blockWindow p q η t : ℝ) : ℂ) := by
  unfold blockWindowC
  exact integral_ofReal

theorem integral_blockWindow_nonneg (p q η : ℝ) : 0 ≤ ∫ t, blockWindow p q η t :=
  integral_nonneg fun t => blockWindow_nonneg p q η t

theorem integral_blockWindow_le {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q) :
    ∫ t, blockWindow p q η t ≤ q - p + 2 * η := by
  refine le_trans (le_of_eq ?_) (integral_norm_blockWindowC_le hη hpq)
  congr 1
  funext t
  rw [norm_blockWindowC_eq]

theorem norm_integral_blockWindowC_le {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q) :
    ‖∫ t, blockWindowC p q η t‖ ≤ q - p + 2 * η :=
  (norm_integral_le_integral_norm _).trans (integral_norm_blockWindowC_le hη hpq)

/-- The window against a unimodular phase has norm at most the window mass. -/
theorem norm_integral_blockWindowC_mul_cexp_le_mass {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q) (ξ : ℝ) :
    ‖∫ t, blockWindowC p q η t * Complex.exp (-(ξ * t) * I)‖ ≤ q - p + 2 * η := by
  refine (norm_integral_le_integral_norm _).trans ?_
  refine le_trans (le_of_eq ?_) (integral_norm_blockWindowC_le hη hpq)
  congr 1
  funext t
  rw [norm_mul, norm_cexp_neg_mul_I, mul_one]

/-! ## `ζ` just to the right of `1` -/

/-- `‖ζ(1+δ)‖ ≤ 3/2 + 1/δ` for `δ > 0`, from Euler–Maclaurin at one term. -/
theorem norm_riemannZeta_one_add_le {δ : ℝ} (hδ : 0 < δ) :
    ‖riemannZeta ((1 + δ : ℝ) : ℂ)‖ ≤ 3 / 2 + 1 / δ := by
  have hσ0 : 0 < 1 + δ := by linarith
  have hre : 0 < (((1 + δ : ℝ) : ℂ)).re := by simp [hσ0]
  have hs1 : ((1 + δ : ℝ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs0 : ((1 + δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  rw [← Zeta0EqZeta one_pos hre hs1, riemannZeta0_apply]
  have hI := ZetaBnd_aux1b 1 le_rfl (t := (0 : ℝ)) hσ0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Nat.cast_one,
    Real.rpow_neg zero_le_one, Real.one_rpow, inv_one] at hI
  simp_rw [div_cpow_eq_cpow_neg] at hI
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
    Complex.zero_cpow hs0, Complex.one_cpow, div_zero, zero_add, div_one]
  set X : ℂ := ((1 + δ : ℝ) : ℂ) * ∫ x in Set.Ioi (1 : ℝ),
    ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(((1 + δ : ℝ) : ℂ) + 1)) with hX
  have hXnorm : ‖X‖ ≤ 1 := by
    rw [hX, norm_mul, Complex.norm_of_nonneg hσ0.le]
    calc (1 + δ) * ‖∫ x in Set.Ioi (1 : ℝ),
          ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(((1 + δ : ℝ) : ℂ) + 1))‖
        ≤ (1 + δ) * (1 / (1 + δ)) := mul_le_mul_of_nonneg_left hI hσ0.le
      _ = 1 := by field_simp
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have e : (1 : ℂ) + (-1 / (1 - ((1 + δ : ℝ) : ℂ)) + -1 / 2 + X)
      = ((1 / 2 + 1 / δ : ℝ) : ℂ) + X := by
    have h1 : (1 : ℂ) - ((1 + δ : ℝ) : ℂ) = -(δ : ℂ) := by push_cast; ring
    rw [h1, neg_div_neg_eq]
    push_cast
    ring
  rw [e]
  calc ‖((1 / 2 + 1 / δ : ℝ) : ℂ) + X‖ ≤ ‖((1 / 2 + 1 / δ : ℝ) : ℂ)‖ + ‖X‖ := norm_add_le _ _
    _ ≤ (1 / 2 + 1 / δ) + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
    _ = 3 / 2 + 1 / δ := by ring

/-! ## The direct series: off-diagonal norms, summability, diagonal -/

/-- Off the diagonal the norm of a direct term is the envelope term. -/
theorem norm_directTerm_eq_offDiag {d x p q η : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (P : ℕ × ℕ) (hP : (P.1 + 1) * h ≠ (P.2 + 1) * k) :
    ‖directTerm d x p q η h k P‖ = directOffDiagTerm (1 / 2 - d) x p q η h k P := by
  unfold directTerm directOffDiagTerm
  rw [if_pos hP]
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity),
    Real.mul_rpow (x := (P.1 + 1 : ℝ) * (P.2 + 1)) (y := (h : ℝ) * k) (by positivity)
      (by positivity)]
  ring

theorem directOffDiagTerm_eq_zero_of_diag {σ₀ x p q η : ℝ} {h k : ℕ} (P : ℕ × ℕ)
    (hP : (P.1 + 1) * h = (P.2 + 1) * k) : directOffDiagTerm σ₀ x p q η h k P = 0 := by
  unfold directOffDiagTerm
  rw [if_neg (not_not.mpr hP)]

/-- A direct term is at most the window mass times the modulus of its summand. -/
theorem norm_directTerm_le {d x p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q) {h k : ℕ} (hh : 0 < h)
    (hk : 0 < k) (P : ℕ × ℕ) :
    ‖directTerm d x p q η h k P‖
      ≤ (q - p + 2 * η) * (((h : ℝ) * k) ^ (-(1 / 2 - d))
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d))
          * ‖smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1 : ℝ)) / x)‖)) := by
  unfold directTerm
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hint : ‖∫ t, blockWindowC p q η t * Complex.exp
      (-((Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ)) * t) * I)‖
      ≤ q - p + 2 * η := by
    have := norm_integral_blockWindowC_mul_cexp_le_mass hη hpq
      (Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ))
    simp only [Complex.ofReal_sub] at this
    exact this
  calc ((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d))
        * ‖smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1)) / x)‖
        * ‖∫ t, blockWindowC p q η t * Complex.exp
          (-((Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ)) * t) * I)‖
      ≤ ((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 - d))
        * ‖smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1)) / x)‖ * (q - p + 2 * η) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring

theorem summable_directTerm {d x p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hpq : p ≤ q) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Summable (directTerm d x p q η h k) := by
  obtain ⟨u, hu, hbound⟩ := exists_direct_majorant hd hd4 hx
  refine Summable.of_norm_bounded (g := fun P => (q - p + 2 * η) * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * u P))
    ((hu.mul_left _).mul_left _) fun P => ?_
  refine (norm_directTerm_le hη hpq hh hk P).trans ?_
  have hb := hbound P 0
  rw [norm_direct_summand] at hb
  have hlen : 0 ≤ q - p + 2 * η := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hlen

/-- On the diagonal `(m+1)h = (n+1)k`, `h = g h'`, `k = g k'`, the direct term is the `j`-th term of
the smoothed diagonal, times the window mass. -/
theorem directTerm_diagIndex {d x p q η : ℝ} {g h' k' h k : ℕ} (hh' : 0 < h') (hk' : 0 < k')
    (hhg : h = g * h') (hkg : k = g * k') (j : ℕ) :
    directTerm d x p q η h k (diagIndex h' k' j)
      = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((j + 1 : ℂ) ^ (-((2 * (1 / 2 - d) : ℝ) : ℂ))
          * smoothAFECutoff (((j + 1 : ℝ) ^ 2 * ((h' * k' : ℕ) : ℝ)) / x))
        * ∫ t, blockWindowC p q η t := by
  unfold directTerm
  have e1 : ((diagIndex h' k' j).1 : ℝ) + 1 = ((j : ℝ) + 1) * k' := by
    exact_mod_cast diagIndex_fst_add_one hk' j
  have e2 : ((diagIndex h' k' j).2 : ℝ) + 1 = ((j : ℝ) + 1) * h' := by
    exact_mod_cast diagIndex_snd_add_one hh' j
  have e3 : ((diagIndex h' k' j).1 + 1) * h = ((diagIndex h' k' j).2 + 1) * k := by
    rw [diagIndex_fst_add_one hk', diagIndex_snd_add_one hh', hhg, hkg]
    ring
  rw [e3, sub_self]
  simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [e1, e2]
  have hc : (0 : ℝ) < ((h' * k' : ℕ) : ℝ) := by positivity
  have e4 : (((j : ℝ) + 1) * k' * (((j : ℝ) + 1) * h')) ^ (-(1 / 2 - d))
      = ((j : ℝ) + 1) ^ (-(2 * (1 / 2 - d))) * ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) := by
    rw [show ((j : ℝ) + 1) * k' * (((j : ℝ) + 1) * h')
        = ((j : ℝ) + 1) ^ (2 : ℕ) * ((h' * k' : ℕ) : ℝ) by push_cast; ring,
      Real.mul_rpow (by positivity) hc.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2
    push_cast
    ring
  have e5 : ((((j : ℝ) + 1) ^ (-(2 * (1 / 2 - d))) : ℝ) : ℂ)
      = (j + 1 : ℂ) ^ (-((2 * (1 / 2 - d) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_neg]
    push_cast
    ring_nf
  have e6 : ((j : ℝ) + 1) * k' * (((j : ℝ) + 1) * h') / x
      = ((j : ℝ) + 1) ^ 2 * ((h' * k' : ℕ) : ℝ) / x := by
    push_cast
    ring
  rw [e4, e6, Complex.ofReal_mul, e5]
  ring

/-- **The direct diagonal is the smoothed diagonal times the window mass.** -/
theorem tsum_directTerm_diagIndex {d x p q η : ℝ} {g h' k' h k : ℕ} (hh' : 0 < h') (hk' : 0 < k')
    (hhg : h = g * h') (hkg : k = g * k') :
    ∑' j : ℕ, directTerm d x p q η h k (diagIndex h' k' j)
      = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * smoothDiagonal (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x * ∫ t, blockWindowC p q η t := by
  simp_rw [directTerm_diagIndex hh' hk' hhg hkg]
  rw [tsum_mul_right, tsum_mul_left]
  rfl

/-! ## The dual series: off-diagonal norms, summability, diagonal -/

/-- Off the dual diagonal the norm of a dual term is the envelope term. -/
theorem norm_dualTerm_eq_offDiag {d x p q η : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (P : ℕ × ℕ) (hP : (P.2 + 1) * h ≠ (P.1 + 1) * k) :
    ‖dualTerm d x p q η h k P‖ = dualOffDiagTerm d x p q η h k P := by
  unfold dualTerm dualOffDiagTerm
  rw [if_pos hP]
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  ring

theorem dualOffDiagTerm_eq_zero_of_diag {d x p q η : ℝ} {h k : ℕ} (P : ℕ × ℕ)
    (hP : (P.2 + 1) * h = (P.1 + 1) * k) : dualOffDiagTerm d x p q η h k P = 0 := by
  unfold dualOffDiagTerm
  rw [if_neg (not_not.mpr hP)]

/-- The windowed carrier weight against a phase, bounded by the window mass and the right-shift
bound of the carrier weight on the support. -/
theorem norm_integral_window_dualCarrierWeight_mul_cexp_le {d p q η : ℝ} (hd : 0 < d)
    (hdq : d ≤ 1 / 4) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {Y : ℝ} (hY : 0 < Y)
    {C : ℝ} (hC : ∀ Y τ : ℝ, 0 < Y → ‖dualCarrierWeight d Y τ‖ ≤
        C * (1 + |τ|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) * Y ^ (-(1 / 2 - d + (1 : ℕ)))) (ξ : ℝ) :
    ‖∫ t, blockWindowC p q η t * dualCarrierWeight d Y t * Complex.exp (-(ξ * t) * I)‖
      ≤ (q - p + 2 * η) * (C * (1 + (q + η)) ^ (3 : ℝ) * Y ^ (-(3 / 2 - d))) := by
  have hC0 : 0 ≤ C := by
    have := hC 1 0 one_pos
    have hn0 := norm_nonneg (dualCarrierWeight d 1 0)
    nlinarith [Real.one_rpow (2 * ((1 : ℕ) + 1 / 2 : ℝ)), Real.one_rpow (-(1 / 2 - d + (1 : ℕ)))]
  set M : ℝ := C * (1 + (q + η)) ^ (3 : ℝ) * Y ^ (-(3 / 2 - d)) with hM
  have hqη : 0 ≤ 1 + (q + η) := by linarith
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hqη _)) (Real.rpow_nonneg hY.le _)
  have hpt : ∀ t, ‖blockWindowC p q η t * dualCarrierWeight d Y t * Complex.exp (-(ξ * t) * I)‖
      ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul, norm_mul, norm_cexp_neg_mul_I, mul_one]
    by_cases ht : t ∈ Set.Icc (p - η) (q + η)
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hT : |t| ≤ q + η := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      have h1T : (1 + |t|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) ≤ (1 + (q + η)) ^ (3 : ℝ) := by
        rw [show (2 * ((1 : ℕ) + 1 / 2 : ℝ)) = (3 : ℝ) by norm_num]
        exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have hYpow : Y ^ (-(1 / 2 - d + (1 : ℕ))) = Y ^ (-(3 / 2 - d)) := by
        congr 1
        push_cast
        ring
      calc ‖dualCarrierWeight d Y t‖
          ≤ C * (1 + |t|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) * Y ^ (-(1 / 2 - d + (1 : ℕ))) := hC Y t hY
        _ ≤ C * (1 + (q + η)) ^ (3 : ℝ) * Y ^ (-(3 / 2 - d)) := by
            rw [hYpow]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1T hC0) (by positivity)
    · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
  have hint : Integrable (fun t => blockWindowC p q η t * dualCarrierWeight d Y t
      * Complex.exp (-(ξ * t) * I)) := by
    have := integrable_window_mul hη (p := p) (q := q) (g := fun t => dualCarrierWeight d Y t
      * Complex.exp (-(ξ * t) * I)) ((continuous_dualCarrierWeight hd hdq hY).mul
      (by fun_prop)).continuousOn
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    ring
  calc ‖∫ t, blockWindowC p q η t * dualCarrierWeight d Y t * Complex.exp (-(ξ * t) * I)‖
      ≤ ∫ t, ‖blockWindowC p q η t * dualCarrierWeight d Y t * Complex.exp (-(ξ * t) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖blockWindowC p q η t‖ * M :=
        integral_mono hint.norm ((integrable_blockWindowC hη).norm.mul_const _) hpt
    _ = (∫ t, ‖blockWindowC p q η t‖) * M := integral_mul_const _ _
    _ ≤ (q - p + 2 * η) * M :=
        mul_le_mul_of_nonneg_right (integral_norm_blockWindowC_le hη hpq) hM0

/-- A dual term is at most the window mass times the right-shift majorant. -/
theorem norm_dualTerm_le {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {C : ℝ} (hC : ∀ Y τ : ℝ, 0 < Y → ‖dualCarrierWeight d Y τ‖ ≤
        C * (1 + |τ|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) * Y ^ (-(1 / 2 - d + (1 : ℕ)))) (P : ℕ × ℕ) :
    ‖dualTerm d x p q η h k P‖
      ≤ ((q - p + 2 * η) * (C * (1 + (q + η)) ^ (3 : ℝ) * x ^ (-(3 / 2 - d))))
        * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ))) := by
  unfold dualTerm
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < P.1 + 1 := by positivity
  have hn : (0 : ℝ) < P.2 + 1 := by positivity
  have hmn : (0 : ℝ) < (P.1 + 1 : ℝ) * (P.2 + 1) := by positivity
  have hY : 0 < (P.1 + 1 : ℝ) * (P.2 + 1) * x := by positivity
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hint := norm_integral_window_dualCarrierWeight_mul_cexp_le hd hdq hη hL hpq hY hC
    (Real.log (((P.2 + 1) * h : ℕ) : ℝ) - Real.log (((P.1 + 1) * k : ℕ) : ℝ))
  have hYpow : ((P.1 + 1 : ℝ) * (P.2 + 1) * x) ^ (-(3 / 2 - d))
      = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(3 / 2 - d)) * x ^ (-(3 / 2 - d)) :=
    Real.mul_rpow hmn.le hx.le
  have hexp : ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d))
      * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(3 / 2 - d)) = ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hmn]
    congr 1
    ring
  calc ((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d))
        * ‖∫ t, blockWindowC p q η t * dualCarrierWeight d ((P.1 + 1 : ℝ) * (P.2 + 1) * x) t
            * Complex.exp (-(((Real.log (((P.2 + 1) * h : ℕ) : ℝ)
                - Real.log (((P.1 + 1) * k : ℕ) : ℝ) : ℝ) : ℂ) * t) * I)‖
      ≤ ((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d))
        * ((q - p + 2 * η) * (C * (1 + (q + η)) ^ (3 : ℝ)
          * ((P.1 + 1 : ℝ) * (P.2 + 1) * x) ^ (-(3 / 2 - d)))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ((q - p + 2 * η) * (C * (1 + (q + η)) ^ (3 : ℝ) * x ^ (-(3 / 2 - d))))
        * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(1 / 2 + d))
          * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(3 / 2 - d)))) := by
        rw [hYpow]; ring
    _ = _ := by rw [hexp]

theorem summable_dualTerm {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Summable (dualTerm d x p q η h k) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_dualCarrierWeight_le_rightShift (K'' := 1) le_rfl
  refine Summable.of_norm_bounded
    (g := fun P : ℕ × ℕ => ((q - p + 2 * η) * (C * (1 + (q + η)) ^ (3 : ℝ) * x ^ (-(3 / 2 - d))))
      * (((h : ℝ) * k) ^ (-(1 / 2 - d)) * ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(2 : ℝ))))
    (((summable_prod_succ_rpow_neg (by norm_num : (1 : ℝ) < 2)).mul_left _).mul_left _)
    fun P => norm_dualTerm_le hd hdq hx hη hL hpq hh hk (fun Y τ hY => hC d Y τ hd hdq hY) P

/-- On the dual diagonal `(n+1)h = (m+1)k`, `h = g h'`, `k = g k'`, the dual term is the window
integral of the `j`-th term of the dual diagonal. -/
theorem dualTerm_diagIndex {d x p q η : ℝ} {g h' k' h k : ℕ} (hh' : 0 < h') (hk' : 0 < k')
    (hhg : h = g * h') (hkg : k = g * k') (j : ℕ) :
    dualTerm d x p q η h k (diagIndex k' h' j)
      = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
        * ∫ t, blockWindowC p q η t * ((j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
          * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * ((h' * k' : ℕ) : ℝ) * x) t) := by
  unfold dualTerm
  have e1 : ((diagIndex k' h' j).1 : ℝ) + 1 = ((j : ℝ) + 1) * h' := by
    exact_mod_cast diagIndex_fst_add_one hh' j
  have e2 : ((diagIndex k' h' j).2 : ℝ) + 1 = ((j : ℝ) + 1) * k' := by
    exact_mod_cast diagIndex_snd_add_one hk' j
  have e3 : ((diagIndex k' h' j).2 + 1) * h = ((diagIndex k' h' j).1 + 1) * k := by
    rw [diagIndex_fst_add_one hh', diagIndex_snd_add_one hk', hhg, hkg]
    ring
  rw [e3, sub_self]
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [e1, e2]
  have hc : (0 : ℝ) < ((h' * k' : ℕ) : ℝ) := by positivity
  have e4 : (((j : ℝ) + 1) * h' * (((j : ℝ) + 1) * k')) ^ (-(1 / 2 + d))
      = ((j : ℝ) + 1) ^ (-(1 + 2 * d)) * ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) := by
    rw [show ((j : ℝ) + 1) * h' * (((j : ℝ) + 1) * k')
        = ((j : ℝ) + 1) ^ (2 : ℕ) * ((h' * k' : ℕ) : ℝ) by push_cast; ring,
      Real.mul_rpow (by positivity) hc.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2
    push_cast
    ring
  have e5 : ((((j : ℝ) + 1) ^ (-(1 + 2 * d)) : ℝ) : ℂ)
      = (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ)) := by
    rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_neg]
    push_cast
    ring_nf
  have e6 : ((j : ℝ) + 1) * h' * (((j : ℝ) + 1) * k') * x
      = ((j : ℝ) + 1) ^ 2 * ((h' * k' : ℕ) : ℝ) * x := by
    push_cast
    ring
  rw [e4, e6, Complex.ofReal_mul, e5, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext t
  ring

/-- The majorant of the `j`-th dual diagonal term on a height window. -/
theorem norm_dualDiagonal_term_le {d c x : ℝ} (hc : 0 < c)
    (hx : 0 < x) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ Y τ : ℝ, 0 < Y → ‖dualCarrierWeight d Y τ‖ ≤
        C * (1 + |τ|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) * Y ^ (-(1 / 2 - d + (1 : ℕ))))
    {T t : ℝ} (ht : |t| ≤ T) (j : ℕ) :
    ‖(j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ)) * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * c * x) t‖
      ≤ (C * (1 + T) ^ (3 : ℝ) * (c * x) ^ (-(3 / 2 - d))) * ((j : ℝ) + 1) ^ (-(4 : ℝ)) := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hY : 0 < ((j : ℝ) + 1) ^ 2 * c * x := by positivity
  rw [norm_mul]
  have e1 : ‖(j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))‖ = ((j : ℝ) + 1) ^ (-(1 + 2 * d)) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos hj (-((1 + 2 * d : ℝ) : ℂ))
    push_cast at this ⊢
    rw [this]
    congr 1
    simp
  rw [e1]
  have h1T : (1 + |t|) ^ (2 * ((1 : ℕ) + 1 / 2 : ℝ)) ≤ (1 + T) ^ (3 : ℝ) := by
    rw [show (2 * ((1 : ℕ) + 1 / 2 : ℝ)) = (3 : ℝ) by norm_num]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hYpow : (((j : ℝ) + 1) ^ 2 * c * x) ^ (-(1 / 2 - d + (1 : ℕ)))
      = ((j : ℝ) + 1) ^ (-(3 - 2 * d)) * (c * x) ^ (-(3 / 2 - d)) := by
    rw [show (-(1 / 2 - d + ((1 : ℕ) : ℝ)) : ℝ) = -(3 / 2 - d) by push_cast; ring,
      mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hj.le]
    congr 2
    push_cast
    ring
  have hexp : ((j : ℝ) + 1) ^ (-(1 + 2 * d)) * ((j : ℝ) + 1) ^ (-(3 - 2 * d))
      = ((j : ℝ) + 1) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hj]
    congr 1
    ring
  calc ((j : ℝ) + 1) ^ (-(1 + 2 * d)) * ‖dualCarrierWeight d (((j : ℝ) + 1) ^ 2 * c * x) t‖
      ≤ ((j : ℝ) + 1) ^ (-(1 + 2 * d)) * (C * (1 + T) ^ (3 : ℝ)
          * (((j : ℝ) + 1) ^ 2 * c * x) ^ (-(1 / 2 - d + (1 : ℕ)))) := by
        refine mul_le_mul_of_nonneg_left ((hC _ t hY).trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1T hC0) (by positivity)
    _ = (C * (1 + T) ^ (3 : ℝ) * (c * x) ^ (-(3 / 2 - d)))
          * (((j : ℝ) + 1) ^ (-(1 + 2 * d)) * ((j : ℝ) + 1) ^ (-(3 - 2 * d))) := by
        rw [hYpow]; ring
    _ = _ := by rw [hexp]

/-- The dual diagonal is continuous on every bounded height set. -/
theorem continuousOn_dualDiagonal {d c x : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hc : 0 < c)
    (hx : 0 < x) (T : ℝ) : ContinuousOn (dualDiagonal d c x) (Set.Icc (-T) T) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_dualCarrierWeight_le_rightShift (K'' := 1) le_rfl
  have hb : ∀ j : ℕ, ∀ t ∈ Set.Icc (-T) T,
      ‖(j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ)) * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * c * x) t‖
      ≤ (C * (1 + T) ^ (3 : ℝ) * (c * x) ^ (-(3 / 2 - d))) * ((j : ℝ) + 1) ^ (-(4 : ℝ)) :=
    fun j t ht => norm_dualDiagonal_term_le hc hx hC0 (fun Y τ hY => hC d Y τ hd hdq hY)
      (abs_le.mpr ⟨ht.1, ht.2⟩) j
  have hf : ∀ j : ℕ, ContinuousOn (fun t : ℝ => (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
      * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * c * x) t) (Set.Icc (-T) T) := fun j =>
    (continuous_const.mul (continuous_dualCarrierWeight hd hdq (by positivity))).continuousOn
  delta dualDiagonal
  exact continuousOn_tsum hf ((summable_nat_succ_rpow_neg (by norm_num : (1 : ℝ) < 4)).mul_left _)
    hb

/-- **The dual diagonal is the window integral of `dualDiagonal`.** -/
theorem tsum_dualTerm_diagIndex {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hh' : 0 < h') (hk' : 0 < k')
    (hhg : h = g * h') (hkg : k = g * k') :
    ∑' j : ℕ, dualTerm d x p q η h k (diagIndex k' h' j)
      = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
        * ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
        * ∫ t, blockWindowC p q η t * dualDiagonal d ((h' * k' : ℕ) : ℝ) x t := by
  simp_rw [dualTerm_diagIndex hh' hk' hhg hkg]
  rw [tsum_mul_left]
  congr 1
  obtain ⟨C, hC0, hC⟩ := exists_norm_dualCarrierWeight_le_rightShift (K'' := 1) le_rfl
  have hc : (0 : ℝ) < ((h' * k' : ℕ) : ℝ) := by positivity
  have hFint : ∀ j : ℕ, Integrable (fun t => blockWindowC p q η t
      * ((j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
        * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * ((h' * k' : ℕ) : ℝ) * x) t)) := fun j =>
    integrable_window_mul hη
      (continuous_const.mul (continuous_dualCarrierWeight hd hdq (by positivity))).continuousOn
  have hw : Integrable (fun t => ‖blockWindowC p q η t‖) := (integrable_blockWindowC hη).norm
  have hsum : Summable fun j : ℕ => ∫ t, ‖blockWindowC p q η t
      * ((j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
        * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * ((h' * k' : ℕ) : ℝ) * x) t)‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _)
      (fun j => ?_) (((summable_nat_succ_rpow_neg (by norm_num : (1 : ℝ) < 4)).mul_left
        ((∫ t, ‖blockWindowC p q η t‖)
          * (C * (1 + (q + η)) ^ (3 : ℝ) * (((h' * k' : ℕ) : ℝ) * x) ^ (-(3 / 2 - d))))))
    have hpt : ∀ t, ‖blockWindowC p q η t * ((j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
        * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * ((h' * k' : ℕ) : ℝ) * x) t)‖
        ≤ ‖blockWindowC p q η t‖ * ((C * (1 + (q + η)) ^ (3 : ℝ)
          * (((h' * k' : ℕ) : ℝ) * x) ^ (-(3 / 2 - d))) * ((j : ℝ) + 1) ^ (-(4 : ℝ))) := by
      intro t
      rw [norm_mul]
      by_cases ht : t ∈ Set.Icc (p - η) (q + η)
      · have hT : |t| ≤ q + η := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        exact mul_le_mul_of_nonneg_left
          (norm_dualDiagonal_term_le hc hx hC0 (fun Y τ hY => hC d Y τ hd hdq hY) hT j)
          (norm_nonneg _)
      · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
    calc ∫ t, ‖blockWindowC p q η t * ((j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
          * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * ((h' * k' : ℕ) : ℝ) * x) t)‖
        ≤ ∫ t, ‖blockWindowC p q η t‖ * ((C * (1 + (q + η)) ^ (3 : ℝ)
          * (((h' * k' : ℕ) : ℝ) * x) ^ (-(3 / 2 - d))) * ((j : ℝ) + 1) ^ (-(4 : ℝ))) :=
          integral_mono (hFint j).norm (hw.mul_const _) hpt
      _ = (∫ t, ‖blockWindowC p q η t‖) * (C * (1 + (q + η)) ^ (3 : ℝ)
          * (((h' * k' : ℕ) : ℝ) * x) ^ (-(3 / 2 - d))) * ((j : ℝ) + 1) ^ (-(4 : ℝ)) := by
          rw [integral_mul_const]; ring
  rw [integral_tsum_of_summable_integral_norm hFint hsum]
  congr 1
  funext t
  delta dualDiagonal
  rw [tsum_mul_left]

/-! ## The residue split of the windowed dual diagonal -/

/-- The left-line remainder of the dual diagonal at height `t`. -/
def dualLeft (d c x t : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ, dualDiagonalIntegrand d c x t (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)

theorem dualDiagonal_eq_main_add_left {d c x : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hc : 0 < c)
    (hx : 0 < x) (t : ℝ) :
    dualDiagonal d c x t = chiPairWeight d t * riemannZeta ((1 + 2 * d : ℝ) : ℂ)
      + dualDiagonalShiftedResidue d c x + dualLeft d c x t := by
  rw [dualDiagonal_eq_residues_add_left hd hd8 hc hx]
  rfl

theorem continuous_chiPairWeight {d : ℝ} (hd : 0 < d) : Continuous (chiPairWeight d) :=
  (contDiff_chiPairWeight hd 0).continuous

theorem continuousOn_dualLeft {d c x : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hc : 0 < c) (hx : 0 < x)
    (T : ℝ) : ContinuousOn (dualLeft d c x) (Set.Icc (-T) T) := by
  have hdq : d ≤ 1 / 4 := by linarith
  have : ContinuousOn (fun t => dualDiagonal d c x t
      - chiPairWeight d t * riemannZeta ((1 + 2 * d : ℝ) : ℂ)
      - dualDiagonalShiftedResidue d c x) (Set.Icc (-T) T) :=
    ((continuousOn_dualDiagonal hd hdq hc hx T).sub
      ((continuous_chiPairWeight hd).continuousOn.mul continuousOn_const)).sub continuousOn_const
  refine this.congr fun t _ => ?_
  dsimp only
  rw [dualDiagonal_eq_main_add_left hd hd8 hc hx t]
  ring

/-- `∫ w·dualDiagonal = ζ(1+2d)·∫ w·χχ + dualRes·∫ w + ∫ w·left`. -/
theorem integral_window_dualDiagonal_eq {d c x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) :
    ∫ t, blockWindowC p q η t * dualDiagonal d c x t
      = riemannZeta ((1 + 2 * d : ℝ) : ℂ) * (∫ t, blockWindowC p q η t * chiPairWeight d t)
        + dualDiagonalShiftedResidue d c x * (∫ t, blockWindowC p q η t)
        + ∫ t, blockWindowC p q η t * dualLeft d c x t := by
  have hdq : d ≤ 1 / 4 := by linarith
  have hsub : Set.Icc (p - η) (q + η) ⊆ Set.Icc (-(q + η)) (q + η) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have h1 : Integrable (fun t => blockWindowC p q η t * chiPairWeight d t) :=
    integrable_window_mul hη (continuous_chiPairWeight hd).continuousOn
  have h2 : Integrable (fun t => blockWindowC p q η t * dualDiagonalShiftedResidue d c x) :=
    integrable_window_mul hη continuousOn_const
  have hleft : ContinuousOn (dualLeft d c x) (Set.Icc (p - η) (q + η)) :=
    (continuousOn_dualLeft hd hd8 hc hx (q + η)).mono hsub
  have h3 : Integrable (fun t => blockWindowC p q η t * dualLeft d c x t) :=
    integrable_window_mul hη hleft
  have hpt : (fun t => blockWindowC p q η t * dualDiagonal d c x t)
      = fun t => riemannZeta ((1 + 2 * d : ℝ) : ℂ) * (blockWindowC p q η t * chiPairWeight d t)
        + blockWindowC p q η t * dualDiagonalShiftedResidue d c x
        + blockWindowC p q η t * dualLeft d c x t := by
    funext t
    rw [dualDiagonal_eq_main_add_left hd hd8 hc hx t]
    ring
  rw [hpt, integral_add, integral_add, integral_const_mul, integral_mul_const]
  · ring
  · exact h1.const_mul _
  · exact h2
  · exact (h1.const_mul _).add h2
  · exact h3

/-! ## The two series split into diagonal and off-diagonal parts -/

/-- The direct diagonal set for the reduced pair `(h', k')`. -/
def directDiag (h' k' : ℕ) : Set (ℕ × ℕ) := {P | (P.1 + 1) * h' = (P.2 + 1) * k'}

/-- The dual diagonal set for the reduced pair `(h', k')`. -/
def dualDiag (h' k' : ℕ) : Set (ℕ × ℕ) := {P | (P.1 + 1) * k' = (P.2 + 1) * h'}

theorem tsum_directTerm_eq_diag_add {d x p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hh' : 0 < h') (hk' : 0 < k')
    (hcop : Nat.Coprime h' k') (hhg : h = g * h') (hkg : k = g * k') :
    ∑' P : ℕ × ℕ, directTerm d x p q η h k P
      = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
          * ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
          * smoothDiagonal (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x * (∫ t, blockWindowC p q η t)
        + ∑' P : ↥((directDiag h' k')ᶜ), directTerm d x p q η h k P := by
  have hh : 0 < h := by rw [hhg]; positivity
  have hk : 0 < k := by rw [hkg]; positivity
  rw [tsum_eq_tsum_diagIndex_add_compl hh' hk' hcop (summable_directTerm hd hd4 hx hη hpq hh hk),
    tsum_directTerm_diagIndex hh' hk' hhg hkg]
  rfl

theorem tsum_dualTerm_eq_diag_add {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hh' : 0 < h')
    (hk' : 0 < k') (hcop : Nat.Coprime h' k') (hhg : h = g * h') (hkg : k = g * k') :
    ∑' P : ℕ × ℕ, dualTerm d x p q η h k P
      = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
          * ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
          * (∫ t, blockWindowC p q η t * dualDiagonal d ((h' * k' : ℕ) : ℝ) x t)
        + ∑' P : ↥((dualDiag h' k')ᶜ), dualTerm d x p q η h k P := by
  have hh : 0 < h := by rw [hhg]; positivity
  have hk : 0 < k := by rw [hkg]; positivity
  rw [tsum_eq_tsum_diagIndex_add_compl hk' hh' hcop.symm
    (summable_dualTerm hd hdq hx hη hL hpq hh hk),
    tsum_dualTerm_diagIndex hd hdq hx hη hL hpq hh' hk' hhg hkg]
  rfl

/-- The off-diagonal part of the direct series is at most the direct envelope sum. -/
theorem norm_tsum_compl_directTerm_le {d x p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hhg : h = g * h') (hkg : k = g * k')
    (hh : 0 < h) (hk : 0 < k) :
    ‖∑' P : ↥((directDiag h' k')ᶜ), directTerm d x p q η h k P‖
      ≤ ∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P := by
  have hs := summable_directTerm hd hd4 hx hη hpq hh hk
  have hoff : ∀ P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P
      ≤ ‖directTerm d x p q η h k P‖ := by
    intro P
    by_cases hP : (P.1 + 1) * h = (P.2 + 1) * k
    · rw [directOffDiagTerm_eq_zero_of_diag P hP]
      exact norm_nonneg _
    · rw [norm_directTerm_eq_offDiag hh hk P hP]
  have hsoff : Summable (directOffDiagTerm (1 / 2 - d) x p q η h k) :=
    Summable.of_nonneg_of_le (fun P => directOffDiagTerm_nonneg _ _ _ _ _ _ _ P) hoff hs.norm
  calc ‖∑' P : ↥((directDiag h' k')ᶜ), directTerm d x p q η h k P‖
      ≤ ∑' P : ↥((directDiag h' k')ᶜ), ‖directTerm d x p q η h k P‖ :=
        norm_tsum_le_tsum_norm (hs.norm.subtype _)
    _ = ∑' P : ↥((directDiag h' k')ᶜ), directOffDiagTerm (1 / 2 - d) x p q η h k P := by
        refine tsum_congr fun P => ?_
        have hP' : ¬ ((P.1.1 + 1) * h' = (P.1.2 + 1) * k') := P.2
        have hP : (P.1.1 + 1) * h ≠ (P.1.2 + 1) * k := by
          intro hcontra
          apply hP'
          rw [hhg, hkg] at hcontra
          have : ((P.1.1 + 1) * h') * g = ((P.1.2 + 1) * k') * g := by
            calc ((P.1.1 + 1) * h') * g = (P.1.1 + 1) * (g * h') := by ring
              _ = (P.1.2 + 1) * (g * k') := hcontra
              _ = ((P.1.2 + 1) * k') * g := by ring
          exact Nat.eq_of_mul_eq_mul_right hg this
        exact norm_directTerm_eq_offDiag hh hk P.1 hP
    _ ≤ ∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P :=
        Summable.tsum_subtype_le _ _ (fun P => directOffDiagTerm_nonneg _ _ _ _ _ _ _ P) hsoff

/-- The off-diagonal part of the dual series is at most the dual envelope sum. -/
theorem norm_tsum_compl_dualTerm_le {d x p q η : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hhg : h = g * h')
    (hkg : k = g * k') (hh : 0 < h) (hk : 0 < k) :
    ‖∑' P : ↥((dualDiag h' k')ᶜ), dualTerm d x p q η h k P‖
      ≤ ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P := by
  have hs := summable_dualTerm hd hdq hx hη hL hpq hh hk
  have hoff : ∀ P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P ≤ ‖dualTerm d x p q η h k P‖ := by
    intro P
    by_cases hP : (P.2 + 1) * h = (P.1 + 1) * k
    · rw [dualOffDiagTerm_eq_zero_of_diag P hP]
      exact norm_nonneg _
    · rw [norm_dualTerm_eq_offDiag hh hk P hP]
  have hsoff : Summable (dualOffDiagTerm d x p q η h k) :=
    Summable.of_nonneg_of_le (fun P => dualOffDiagTerm_nonneg _ _ _ _ _ _ _ P) hoff hs.norm
  calc ‖∑' P : ↥((dualDiag h' k')ᶜ), dualTerm d x p q η h k P‖
      ≤ ∑' P : ↥((dualDiag h' k')ᶜ), ‖dualTerm d x p q η h k P‖ :=
        norm_tsum_le_tsum_norm (hs.norm.subtype _)
    _ = ∑' P : ↥((dualDiag h' k')ᶜ), dualOffDiagTerm d x p q η h k P := by
        refine tsum_congr fun P => ?_
        have hP' : ¬ ((P.1.1 + 1) * k' = (P.1.2 + 1) * h') := P.2
        have hP : (P.1.2 + 1) * h ≠ (P.1.1 + 1) * k := by
          intro hcontra
          apply hP'
          rw [hhg, hkg] at hcontra
          have : ((P.1.1 + 1) * k') * g = ((P.1.2 + 1) * h') * g := by
            calc ((P.1.1 + 1) * k') * g = (P.1.1 + 1) * (g * k') := by ring
              _ = (P.1.2 + 1) * (g * h') := hcontra.symm
              _ = ((P.1.2 + 1) * h') * g := by ring
          exact Nat.eq_of_mul_eq_mul_right hg this
        exact norm_dualTerm_eq_offDiag hh hk P.1 hP
    _ ≤ ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P :=
        Summable.tsum_subtype_le _ _ (fun P => dualOffDiagTerm_nonneg _ _ _ _ _ _ _ P) hsoff

/-! ## The smoothed diagonal and the residue cancellation -/

/-- The left-line remainder of the smoothed diagonal. -/
def smoothLeft (σ₀ c x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)

theorem smoothDiagonal_eq_main_add_left {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hσ0 : 1 / 4 ≤ σ₀)
    (hσ1 : σ₀ < 1 / 2) :
    smoothDiagonal σ₀ c x
      = riemannZeta ((2 * σ₀ : ℝ) : ℂ) + smoothDiagonalShiftedResidue σ₀ c x + smoothLeft σ₀ c x :=
  smoothDiagonal_eq_residues_add_left hc hx hσ0 hσ1

/-- The two diagonal residues cancel against the real coefficients `c^{-σ₀}` and `c^{-(½+d)}`. -/
theorem residue_cancel_ofReal {d c x : ℝ} (hd : 0 < d) (hc : 0 < c) (hx : 0 < x) :
    (((c ^ (-(1 / 2 - d)) : ℝ) : ℂ)) * smoothDiagonalShiftedResidue (1 / 2 - d) c x
      + (((c ^ (-(1 / 2 + d)) : ℝ) : ℂ)) * dualDiagonalShiftedResidue d c x = 0 := by
  have h := smoothDiagonalShiftedResidue_add_dual_cancel hd hc hx
  have e1 : (((c ^ (-(1 / 2 - d)) : ℝ) : ℂ)) = (c : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) := by
    rw [Complex.ofReal_cpow hc.le, Complex.ofReal_neg]
  have e2 : (((c ^ (-(1 / 2 + d)) : ℝ) : ℂ)) = (c : ℂ) ^ (((1 / 2 - d : ℝ) : ℂ) - 1) := by
    rw [Complex.ofReal_cpow hc.le]
    congr 1
    push_cast
    ring
  rw [e1, e2]
  exact h

/-! ## The residue term -/

/-- `‖ζ(σ+it)‖ ≤ 3/2 + 1/|1−s| + 2|t|/σ` on `0 < σ ≤ 2`, `|t| ≥ 2` (Euler–Maclaurin at one term). -/
theorem norm_riemannZeta_le_strip' {σ t : ℝ} (hσ : σ ∈ Set.Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ 3 / 2 + 1 / ‖1 - ((σ : ℂ) + t * I)‖ + 2 * |t| / σ := by
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht0 this
  have hs0 : (σ : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht0 this
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp [hσ.1]
  rw [← Zeta0EqZeta one_pos hre hs1, riemannZeta0_apply]
  have hI := ZetaBnd_aux1 1 le_rfl hσ ht
  simp_rw [div_cpow_eq_cpow_neg] at hI
  simp only [Nat.cast_one, Real.rpow_neg (zero_le_one' ℝ), Real.one_rpow, inv_one, mul_one] at hI
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
    Complex.zero_cpow hs0, Complex.one_cpow, div_zero, zero_add, div_one]
  set X : ℂ := ((σ : ℂ) + t * I) * ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) *
    (x : ℂ) ^ (-(((σ : ℂ) + t * I) + 1)) with hX
  have h1 : ‖(1 : ℂ) + (-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2 + X)‖
      ≤ 1 + 1 / ‖1 - ((σ : ℂ) + t * I)‖ + 1 / 2 + ‖X‖ := by
    calc ‖(1 : ℂ) + (-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2 + X)‖
        ≤ ‖(1 : ℂ)‖ + ‖-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2 + X‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + (‖-1 / (1 - ((σ : ℂ) + t * I)) + -1 / 2‖ + ‖X‖) := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + ((‖-1 / (1 - ((σ : ℂ) + t * I))‖ + ‖(-1 / 2 : ℂ)‖) + ‖X‖) := by
          gcongr; exact norm_add_le _ _
      _ = 1 + 1 / ‖1 - ((σ : ℂ) + t * I)‖ + 1 / 2 + ‖X‖ := by
          rw [norm_one, norm_div, norm_neg, norm_one, norm_div, norm_neg, norm_one]
          norm_num
          ring
  refine h1.trans ?_
  have hXle : ‖X‖ ≤ 2 * |t| / σ := hI
  linarith

/-- The product-AFE residue on the displaced line: Gaussian decay in the height. -/
theorem norm_productAFEShiftedResidue_le {d x : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx1 : 1 ≤ x)
    {t : ℝ} (ht : 4 ≤ |t|) :
    ‖productAFEShiftedResidue (displacedLinePt d t) (displacedLinePt d (-t)) x‖
      ≤ 9 * Real.exp 1 * x * Real.exp (-(t ^ 2)) := by
  have hx : 0 < x := by linarith
  have ht0 : 0 < |t| := by linarith
  unfold productAFEShiftedResidue
  have hs1 : (1 : ℂ) - displacedLinePt d t = ((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  have hz : displacedLinePt d (-t) + (1 - displacedLinePt d t)
      = ((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  rw [hz, norm_div, norm_mul, norm_mul, hs1]
  have h1 : ‖(x : ℂ) ^ (((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤ x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).re = 1 / 2 + d := by simp
    rw [hre]
    calc x ^ (1 / 2 + d) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have h2 : ‖Complex.exp ((((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) ^ 2)‖
      ≤ Real.exp 1 * Real.exp (-(t ^ 2)) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : ((((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) ^ 2).re = (1 / 2 + d) ^ 2 - t ^ 2 := by
      simp [sq]
      try ring
    rw [this]
    nlinarith
  have h3 : ‖riemannZeta (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖ ≤ 3 / 2 + 1 / 8 + 8 * |t| := by
    have hσ : (1 : ℝ) ∈ Set.Ioc 0 2 := ⟨by norm_num, by norm_num⟩
    have habs : |(-2 * t : ℝ)| = 2 * |t| := by rw [abs_mul, abs_neg, abs_two]
    have ht2 : 2 ≤ |(-2 * t : ℝ)| := by rw [habs]; linarith
    have h := norm_riemannZeta_le_strip' hσ ht2
    have hden : ‖(1 : ℂ) - (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖ = 2 * |t| := by
      have : (1 : ℂ) - (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I) = ((2 * t : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_two]
    rw [hden, habs] at h
    have h8 : 1 / (2 * |t|) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    calc ‖riemannZeta (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖
        ≤ 3 / 2 + 1 / (2 * |t|) + 2 * (2 * |t|) / 1 := h
      _ ≤ 3 / 2 + 1 / 8 + 8 * |t| := by linarith
  have h4 : |t| ≤ ‖((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm (((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
    have him : (((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).im = -t := by simp
    rw [him, abs_neg] at this
    exact this
  have hden0 : 0 < ‖((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ := by linarith
  rw [div_le_iff₀ hden0]
  calc ‖(x : ℂ) ^ (((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖
        * ‖Complex.exp ((((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) ^ 2)‖
        * ‖riemannZeta (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖
      ≤ x * (Real.exp 1 * Real.exp (-(t ^ 2))) * (3 / 2 + 1 / 8 + 8 * |t|) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hx.le) h3 (norm_nonneg _) (by positivity)
    _ = (x * Real.exp 1 * Real.exp (-(t ^ 2))) * (3 / 2 + 1 / 8 + 8 * |t|) := by ring
    _ ≤ (x * Real.exp 1 * Real.exp (-(t ^ 2))) * (9 * |t|) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 9 * Real.exp 1 * x * Real.exp (-(t ^ 2)) * |t| := by ring
    _ ≤ 9 * Real.exp 1 * x * Real.exp (-(t ^ 2))
        * ‖((1 / 2 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

theorem norm_residuePair_le {d x : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx1 : 1 ≤ x) {t : ℝ}
    (ht : 4 ≤ |t|) :
    ‖residuePair d x t‖ ≤ 18 * Real.exp 1 * x * Real.exp (-(t ^ 2)) := by
  unfold residuePair
  have hr1 := norm_productAFEShiftedResidue_le hd hd4 hx1 ht
  have hr2 := norm_productAFEShiftedResidue_le hd hd4 hx1 (t := -t) (by rwa [abs_neg])
  rw [neg_neg, neg_sq] at hr2
  calc ‖productAFEShiftedResidue (displacedLinePt d t) (displacedLinePt d (-t)) x
        + productAFEShiftedResidue (displacedLinePt d (-t)) (displacedLinePt d t) x‖
      ≤ ‖productAFEShiftedResidue (displacedLinePt d t) (displacedLinePt d (-t)) x‖
        + ‖productAFEShiftedResidue (displacedLinePt d (-t)) (displacedLinePt d t) x‖ :=
        norm_add_le _ _
    _ ≤ 9 * Real.exp 1 * x * Real.exp (-(t ^ 2)) + 9 * Real.exp 1 * x * Real.exp (-(t ^ 2)) :=
        add_le_add hr1 hr2
    _ = 18 * Real.exp 1 * x * Real.exp (-(t ^ 2)) := by ring

/-- The residue term of a mollifier pair is Gaussian-small in the block height. -/
theorem norm_residueTerm_le {d x p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hx1 : 1 ≤ x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖residueTerm d x p q η h k‖
      ≤ (q - p + 2 * η) * (((h : ℝ) * k) ^ (-(1 / 2 - d))
        * (18 * Real.exp 1 * x * Real.exp (-((p - η) ^ 2)))) := by
  have hx : 0 < x := by linarith
  rw [← integral_window_pairCoeff_residuePair]
  set M : ℝ := ((h : ℝ) * k) ^ (-(1 / 2 - d)) * (18 * Real.exp 1 * x * Real.exp (-((p - η) ^ 2)))
    with hM
  have hM0 : 0 ≤ M := by positivity
  have hres : ContinuousOn (residuePair d x) (Set.Icc (p - η) (q + η)) := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h0
      rw [h0] at this
      linarith
    exact (continuousAt_residuePair hd hx ht0).continuousWithinAt
  have hint : Integrable (fun t => blockWindowC p q η t * pairCoeff d h k t * residuePair d x t) :=
    integrable_window_pairCoeff_mul hη hh hk hres
  have hpt : ∀ t, ‖blockWindowC p q η t * pairCoeff d h k t * residuePair d x t‖
      ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul, norm_mul, norm_pairCoeff hh hk, mul_assoc]
    by_cases ht : t ∈ Set.Icc (p - η) (q + η)
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hpη : 0 ≤ p - η := by linarith
      have ht4 : 4 ≤ |t| := by
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.1]
      have hexp : Real.exp (-(t ^ 2)) ≤ Real.exp (-((p - η) ^ 2)) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.1])
      rw [hM]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖residuePair d x t‖ ≤ 18 * Real.exp 1 * x * Real.exp (-(t ^ 2)) :=
            norm_residuePair_le hd hd4 hx1 ht4
        _ ≤ 18 * Real.exp 1 * x * Real.exp (-((p - η) ^ 2)) := by gcongr
    · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
  calc ‖∫ t, blockWindowC p q η t * pairCoeff d h k t * residuePair d x t‖
      ≤ ∫ t, ‖blockWindowC p q η t * pairCoeff d h k t * residuePair d x t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖blockWindowC p q η t‖ * M :=
        integral_mono hint.norm ((integrable_blockWindowC hη).norm.mul_const _) hpt
    _ = (∫ t, ‖blockWindowC p q η t‖) * M := integral_mul_const _ _
    _ ≤ (q - p + 2 * η) * M :=
        mul_le_mul_of_nonneg_right (integral_norm_blockWindowC_le hη hpq) hM0

/-! ## The pair decomposition -/

/-- The error part of the block twisted moment of a mollifier pair. -/
def pairError (d x p q η : ℝ) (h' k' h k : ℕ) : ℂ :=
  (∑' P : ↥((directDiag h' k')ᶜ), directTerm d x p q η h k P)
    + (∑' P : ↥((dualDiag h' k')ᶜ), dualTerm d x p q η h k P)
    + ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
      * (((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
          * smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x * (∫ t, blockWindowC p q η t)
        + ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
          * ∫ t, blockWindowC p q η t * dualLeft d ((h' * k' : ℕ) : ℝ) x t)
    - residueTerm d x p q η h k

/-- **The pair decomposition.**  The block twisted moment of the pair `(h,k) = (gh', gk')` is the
two main terms `ζ(2σ₀)(∫w)` and `ζ(1+2d)∫wχχ` with their gcd coefficients, plus the error. -/
theorem blockPair_eq {d x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx : 0 < x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hh' : 0 < h') (hk' : 0 < k')
    (hcop : Nat.Coprime h' k') (hhg : h = g * h') (hkg : k = g * k') :
    (∑' P : ℕ × ℕ, directTerm d x p q η h k P) + (∑' P : ℕ × ℕ, dualTerm d x p q η h k P)
        - residueTerm d x p q η h k
      = ((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
          * (((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
              * riemannZeta ((2 * (1 / 2 - d) : ℝ) : ℂ) * (∫ t, blockWindowC p q η t)
            + ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
              * riemannZeta ((1 + 2 * d : ℝ) : ℂ) * (∫ t, blockWindowC p q η t * chiPairWeight d t))
        + pairError d x p q η h' k' h k := by
  have hd4 : d ≤ 1 / 4 := by linarith
  have hc : (0 : ℝ) < ((h' * k' : ℕ) : ℝ) := by positivity
  rw [tsum_directTerm_eq_diag_add hd hd4 hx hη hpq hg hh' hk' hcop hhg hkg,
    tsum_dualTerm_eq_diag_add hd hd4 hx hη hL hpq hg hh' hk' hcop hhg hkg,
    smoothDiagonal_eq_main_add_left hc hx (by linarith) (by linarith),
    integral_window_dualDiagonal_eq hd hd8 hc hx hη hL hpq]
  unfold pairError
  have hcancel := residue_cancel_ofReal hd hc hx
  linear_combination
    (((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ) * (∫ t, blockWindowC p q η t)) * hcancel

/-- The windowed dual left-line remainder is at most the window mass times its bound at the
bottom of the block. -/
theorem norm_integral_window_dualLeft_le {d c x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {K₂ : ℝ} (hK₂0 : 0 ≤ K₂)
    (hK₂ : ∀ τ : ℝ, ‖dualLeft d c x τ‖ ≤ K₂ * (c * x) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-(1 / 2 - 2 * d))) :
    ‖∫ t, blockWindowC p q η t * dualLeft d c x t‖
      ≤ (q - p + 2 * η) * (K₂ * (c * x) ^ (1 / 4 : ℝ) * (1 + (p - η)) ^ (-(1 / 2 - 2 * d))) := by
  have hsub : Set.Icc (p - η) (q + η) ⊆ Set.Icc (-(q + η)) (q + η) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  set M : ℝ := K₂ * (c * x) ^ (1 / 4 : ℝ) * (1 + (p - η)) ^ (-(1 / 2 - 2 * d)) with hM
  have hpη : 0 < 1 + (p - η) := by linarith
  have hM0 : 0 ≤ M := by positivity
  have hint : Integrable (fun t => blockWindowC p q η t * dualLeft d c x t) :=
    integrable_window_mul hη ((continuousOn_dualLeft hd hd8 hc hx (q + η)).mono hsub)
  have hpt : ∀ t, ‖blockWindowC p q η t * dualLeft d c x t‖ ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul]
    by_cases ht : t ∈ Set.Icc (p - η) (q + η)
    · refine mul_le_mul_of_nonneg_left ((hK₂ t).trans ?_) (norm_nonneg _)
      rw [hM]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : 1 + (p - η) ≤ 1 + |t| := by
        have := le_abs_self t
        linarith [ht.1]
      exact Real.rpow_le_rpow_of_nonpos hpη h1 (by linarith)
    · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
  calc ‖∫ t, blockWindowC p q η t * dualLeft d c x t‖
      ≤ ∫ t, ‖blockWindowC p q η t * dualLeft d c x t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖blockWindowC p q η t‖ * M :=
        integral_mono hint.norm ((integrable_blockWindowC hη).norm.mul_const _) hpt
    _ = (∫ t, ‖blockWindowC p q η t‖) * M := integral_mul_const _ _
    _ ≤ (q - p + 2 * η) * M :=
        mul_le_mul_of_nonneg_right (integral_norm_blockWindowC_le hη hpq) hM0

/-- **The pair error bound.** -/
theorem norm_pairError_le {d x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx1 : 1 ≤ x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hh' : 0 < h') (hk' : 0 < k')
    (hhg : h = g * h') (hkg : k = g * k') {K₁ K₂ : ℝ} (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ‖smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x‖
      ≤ K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ)))
    (hK₂ : ∀ τ : ℝ, ‖dualLeft d ((h' * k' : ℕ) : ℝ) x τ‖
      ≤ K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-(1 / 2 - 2 * d))) :
    ‖pairError d x p q η h' k' h k‖
      ≤ (∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P)
        + (∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P)
        + ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d))
              * (K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ))) * (q - p + 2 * η)
            + ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d))
              * ((q - p + 2 * η) * (K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ (1 / 4 : ℝ)
                * (1 + (p - η)) ^ (-(1 / 2 - 2 * d)))))
        + (q - p + 2 * η) * (((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (18 * Real.exp 1 * x * Real.exp (-((p - η) ^ 2)))) := by
  have hd4 : d ≤ 1 / 4 := by linarith
  have hx : 0 < x := by linarith
  have hh : 0 < h := by rw [hhg]; positivity
  have hk : 0 < k := by rw [hkg]; positivity
  have hc : (0 : ℝ) < ((h' * k' : ℕ) : ℝ) := by positivity
  unfold pairError
  have e1 := norm_tsum_compl_directTerm_le hd hd4 hx hη hpq hg hhg hkg hh hk
  have e2 := norm_tsum_compl_dualTerm_le hd hd4 hx hη hL hpq hg hhg hkg hh hk
  have e3 : ‖((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
      * (((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
          * smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x * (∫ t, blockWindowC p q η t)
        + ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
          * ∫ t, blockWindowC p q η t * dualLeft d ((h' * k' : ℕ) : ℝ) x t)‖
      ≤ ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d))
              * (K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ))) * (q - p + 2 * η)
            + ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d))
              * ((q - p + 2 * η) * (K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ (1 / 4 : ℝ)
                * (1 + (p - η)) ^ (-(1 / 2 - 2 * d))))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hK₁ (by positivity))
        (norm_integral_blockWindowC_le hη hpq) (norm_nonneg _) (by positivity)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (norm_integral_window_dualLeft_le hd hd8 hc hx hη hL hpq hK₂0 hK₂) (by positivity)
  have e4 := norm_residueTerm_le hd hd4 hx1 hη hL hpq hh hk
  calc ‖_ + _ + _ - residueTerm d x p q η h k‖
      ≤ ‖_ + _ + _‖ + ‖residueTerm d x p q η h k‖ := norm_sub_le _ _
    _ ≤ ‖_ + _‖ + ‖_‖ + ‖residueTerm d x p q η h k‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖_‖ + ‖_‖ + ‖_‖ + ‖residueTerm d x p q η h k‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by
        gcongr

end RHTower.ZetaGateProductAFE

end
