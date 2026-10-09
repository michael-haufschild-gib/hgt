import GaloisForLFunctions.RHTower.ExactNullCertificateDivisorTransfer
import GaloisForLFunctions.RHTower.IntegerBlindLogarithmicCarlsonCritical

/-!
# Exact-null certificates: the ζ-free logarithmic growth law

Combining the divisor transfer (`logNode_blind_iff_certKernel_vanishes`) with the critical
logarithmic Carlson theorem for `log ℕ`: if a test `ĝ(t) = Ξ(t)² R(½+it)` vanishes at every
`log n`, `n ≥ 2`, and
`∫ |G(½+it)|² |R(½+it)| e^{(π/2)(|t| − |t|/log(|t|+3))} dt < ∞`,  `G(s) = s(s−1)Γ_ℝ(s)/2`,
then `∫ Ξ² R = 0` (`integral_xi_sq_eq_zero_of_logNode_blind_of_logRoom`). Since
`|G(½+it)|² ≍ |t|^{7/2} e^{−π|t|/2}`, a nonzero positive exact-null test blind at `log ℕ_{≥2}`
needs `∫ |t|^{7/2} |R(t)| e^{−(π/2)|t|/log(|t|+3)} dt = ∞`. The condition involves `R` alone:
the factor `|ζ(½+it)|²` of `Ξ²` is removed by the Dirichlet inverse `μ ⋆ μ` of `ζ²`.

The kernel `Ψ_R = 𝓜^{−1}[G²R]` may be read on any line of the strip (`certKernel_eq_mellinInv_half`);
on `Re s = ½` its values at `n` are the Dirichlet moments of `t ↦ G(½+it)² R(½+it)`.
-/

open Complex MeasureTheory

noncomputable section

namespace RHTower.ExactNullDivisorTransfer

open RHTower.PrimeBlindCarlson

/-- On `½ ≤ Re s ≤ 3` the kernel can be read on the critical line. -/
theorem certKernel_eq_mellinInv_half (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → ‖archXi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {x : ℝ} (hx : 0 < x) :
    certKernel R x = mellinInv (1 / 2) (fun s => archXi s ^ 2 * R s) x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hstrip : ∀ s : ℂ, s.re ∈ Set.uIcc (3 : ℝ) (1 / 2) → 1 / 2 ≤ s.re ∧ s.re ≤ 3 := by
    intro s hs
    rw [Set.uIcc_of_ge (by norm_num)] at hs
    exact hs
  have hcp : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 →
      ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 : ℝ)) := by
    intro s h1 h2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    rcases le_or_gt x 1 with hx1 | hx1
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show -s.re ≥ -3 by linarith)
      have : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hx1.le (show -s.re ≤ -(1 / 2) by linarith)
      have : 0 ≤ x ^ (-(3 : ℝ)) := Real.rpow_nonneg hx.le _
      linarith
  unfold certKernel mellinInv
  congr 1
  have key := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay
    (Φ := fun s : ℂ => (x : ℂ) ^ (-s) * (archXi s ^ 2 * R s)) (c₁ := 3) (c₂ := 1 / 2)
    (C := (x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 : ℝ))) * C)
    (fun s hs => by
      obtain ⟨h1, h2⟩ := hstrip s hs
      have hre : 0 < s.re := by linarith
      exact (((differentiableAt_id.neg).const_cpow (Or.inl hx0))).mul
        (((differentiableAt_archXi hre).pow 2).mul (hR s h1 h2)))
    (fun s hs => by
      obtain ⟨h1, h2⟩ := hstrip s hs
      rw [norm_mul, mul_div_assoc]
      exact mul_le_mul (hcp s h1 h2) (hC s h1 h2) (norm_nonneg _) (by positivity))
  simpa [smul_eq_mul] using key

/-- **ζ-free growth law for exact-null certificates.** If a test `ĝ = Ξ² R` is blind at every
`log n`, `n ≥ 2`, and its kernel symbol `G(½+it)² R(½+it)` is integrable against the critical
logarithmic room `e^{(π/2)(|t| − |t|/log(|t|+3))}`, then `∫ Ξ² R = 0`: the test is zero at the
origin. So a nonzero positive exact-null certificate needs `∫ |G(½+it)|² |R| · room = ∞`. -/
theorem integral_xi_sq_eq_zero_of_logNode_blind_of_logRoom (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → ‖xi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {C'' : ℝ}
    (hC'' : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → ‖archXi s ^ 2 * R s‖ ≤ C'' / (1 + s.im ^ 2))
    (hroom : Integrable fun t : ℝ =>
      ‖archXi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I)‖ * logRoomWeight (Real.pi / 2) t)
    (hblind : ∀ n : ℕ, 2 ≤ n →
      ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) = 0) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) = 0 := by
  have hC' : ∀ t : ℝ, ‖archXi (3 + t * I) ^ 2 * R (3 + t * I)‖ ≤ C'' / (1 + t ^ 2) := by
    intro t
    have := hC'' (3 + t * I) (by simp; norm_num) (by simp)
    simpa using this
  have hvan := (logNode_blind_iff_certKernel_vanishes R hR hC hC').mp hblind
  set w : ℝ → ℂ := fun t => archXi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) with hw
  have hwcont : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : (0 : ℝ) < ((1 / 2 : ℂ) + t * I).re := by simp
    have h3 : DifferentiableAt ℂ (fun s => archXi s ^ 2 * R s) ((1 / 2 : ℂ) + t * I) :=
      ((differentiableAt_archXi hre).pow 2).mul (hR _ (by simp) (by simp; norm_num))
    exact ContinuousAt.comp (g := fun s => archXi s ^ 2 * R s) h3.continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t)
  -- the Dirichlet moments of `w` are the kernel values
  have hmoment : ∀ x : ℝ, 0 < x → certKernel R x =
      (1 / (2 * Real.pi) : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) * ∫ t, w t * cexp (-(I * t) * Real.log x) := by
    intro x hx
    rw [certKernel_eq_mellinInv_half R hR hC'' hx, mellinInv, Complex.real_smul,
      ← integral_const_mul, ← integral_const_mul]
    push_cast
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hcp : (x : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-(I * t) * Real.log x) := by
      rw [show -((1 / 2 : ℂ) + t * I) = -(1 / 2 : ℂ) + (-(t * I)) by ring,
        Complex.cpow_add _ _ hx0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
      ring_nf
    simp only [smul_eq_mul, hw]
    rw [hcp]; ring
  have hmom : ∀ n ∈ {n : ℕ | 2 ≤ n}, ∫ t, w t * cexp (-(I * t) * Real.log n) = 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by simp at hn; omega : 0 < n)
    have h := hmoment n hn0
    rw [hvan n hn] at h
    have hc : (1 / (2 * Real.pi) : ℂ) * ((n : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
      refine mul_ne_zero (one_div_ne_zero (by
        exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0))) ?_
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h0; exact absurd h0 (by exact_mod_cast hn0.ne')
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  have hzero := fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical
    (fun n hn => hn) not_summable_one_div_mul_log hwcont.aestronglyMeasurable hroom hmom 0
  have hk1 : certKernel R 1 = 0 := by
    rw [hmoment 1 one_pos]
    simp only [Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hzero ⊢
    rw [hzero, mul_zero]
  rw [integral_xi_sq_eq_certKernel_one R hR hC hC' hvan, hk1, mul_zero]

end RHTower.ExactNullDivisorTransfer
