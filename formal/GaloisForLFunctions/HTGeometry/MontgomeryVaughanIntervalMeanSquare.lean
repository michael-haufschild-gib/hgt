import GaloisForLFunctions.HTGeometry.RiemannGaussian.MontgomeryVaughan.Final

/-!
# Montgomery–Vaughan lower bound for the interval mean square of a separated exponential sum

For frequencies `u_r` with pairwise gaps at least `D`, the mean square of
`S(α) = Σ_r c_r e^{2πi u_r α}` over any interval of length `ℓ` is at least
`(ℓ − 26/(πD)) Σ_r |c_r|²`.  The diagonal gives `ℓ Σ|c_r|²`; the off-diagonal
is a difference of two bilinear Hilbert forms at the two endpoints, each
bounded by the corpus's Montgomery–Vaughan inequality with constant `26`.
-/

open Complex MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exponential `e^{2πi u α}` as a complex function of the real variable `α`. -/
def mvExp (u : ℝ) (α : ℝ) : ℂ := cexp ((2 * Real.pi * I * (u : ℂ)) * (α : ℂ))

theorem norm_mvExp (u α : ℝ) : ‖mvExp u α‖ = 1 := by
  unfold mvExp
  rw [Complex.norm_exp]
  have : ((2 * Real.pi * I * (u : ℂ)) * (α : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero]

theorem continuous_mvExp (u : ℝ) : Continuous (mvExp u) := by
  unfold mvExp
  fun_prop

theorem conj_mvExp (u α : ℝ) : conj (mvExp u α) = cexp ((-(2 * Real.pi * I * (u : ℂ))) * (α : ℂ)) := by
  unfold mvExp
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- Product of an exponential with the conjugate of another: a single exponential at the
difference frequency. -/
theorem mvExp_mul_conj_mvExp (u v α : ℝ) :
    mvExp u α * conj (mvExp v α) = cexp ((2 * Real.pi * I * ((u - v : ℝ) : ℂ)) * (α : ℂ)) := by
  rw [conj_mvExp]
  unfold mvExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Interval integral of the difference-frequency exponential. -/
theorem integral_mvExp_diff {u v : ℝ} (huv : u ≠ v) (a b : ℝ) :
    ∫ α in a..b, cexp ((2 * Real.pi * I * ((u - v : ℝ) : ℂ)) * (α : ℂ)) =
      (cexp ((2 * Real.pi * I * ((u - v : ℝ) : ℂ)) * (b : ℂ)) -
        cexp ((2 * Real.pi * I * ((u - v : ℝ) : ℂ)) * (a : ℂ))) /
        (2 * Real.pi * I * ((u - v : ℝ) : ℂ)) := by
  apply integral_exp_mul_complex
  have h1 : ((u - v : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr huv
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero h2 h1

/-- **Montgomery–Vaughan interval mean square, lower bound.**  For frequencies with pairwise
gaps at least `D > 0`, the mean square of `Σ_r c_r e^{2πi u_r α}` over `[a, a+ℓ]` is at least
`(ℓ − 26/(πD)) Σ_r ‖c_r‖²`. -/
theorem interval_integral_normSq_expSum_ge {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (c : ι → ℂ) {D a ℓ : ℝ} (hD : 0 < D)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    (ℓ - 26 / (Real.pi * D)) * ∑ r, ‖c r‖ ^ 2 ≤
      ∫ α in a..a + ℓ, ‖∑ r, c r * mvExp (u r) α‖ ^ 2 := by
  classical
  set b := a + ℓ with hb
  set S : ℝ → ℂ := fun α => ∑ r, c r * mvExp (u r) α with hS
  set K : ι → ι → ℂ := fun r s => 2 * Real.pi * I * ((u r - u s : ℝ) : ℂ) with hK
  set Sc : ℝ := ∑ r, ‖c r‖ ^ 2 with hSc
  have hSc0 : 0 ≤ Sc := Finset.sum_nonneg fun r _ => by positivity
  -- pointwise expansion of the squared modulus
  have hpt : ∀ α : ℝ, ((‖S α‖ ^ 2 : ℝ) : ℂ) =
      ∑ r, ∑ s, c r * conj (c s) * cexp (K r s * (α : ℂ)) := by
    intro α
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [hS, map_sum, Finset.sum_mul_sum, map_mul]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have := mvExp_mul_conj_mvExp (u r) (u s) α
    calc
      c r * mvExp (u r) α * (conj (c s) * conj (mvExp (u s) α)) =
          c r * conj (c s) * (mvExp (u r) α * conj (mvExp (u s) α)) := by ring
      _ = _ := by rw [this]
  -- the real integral as the real part of a complex double sum
  have hcont : ∀ r s, Continuous (fun α : ℝ => c r * conj (c s) * cexp (K r s * (α : ℂ))) := by
    intro r s
    fun_prop
  have hint : (∫ α in a..b, ‖S α‖ ^ 2) =
      (∑ r, ∑ s, c r * conj (c s) * ∫ α in a..b, cexp (K r s * (α : ℂ))).re := by
    have h1 : ((∫ α in a..b, ‖S α‖ ^ 2 : ℝ) : ℂ) = ∫ α in a..b, ((‖S α‖ ^ 2 : ℝ) : ℂ) :=
      (intervalIntegral.integral_ofReal).symm
    have h2 : (∫ α in a..b, ((‖S α‖ ^ 2 : ℝ) : ℂ)) =
        ∑ r, ∑ s, c r * conj (c s) * ∫ α in a..b, cexp (K r s * (α : ℂ)) := by
      simp_rw [hpt]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun s _ => ?_
          rw [intervalIntegral.integral_const_mul]
        · intro s _
          exact (hcont r s).intervalIntegrable _ _
      · intro r _
        exact (continuous_finsetSum _ fun s _ => hcont r s).intervalIntegrable _ _
    have h3 := congrArg Complex.re (h1.trans h2)
    rw [Complex.ofReal_re] at h3
    exact h3
  -- evaluate the integrals
  have hdiag : ∀ r, (∫ α in a..b, cexp (K r r * (α : ℂ))) = (ℓ : ℂ) := by
    intro r
    have : K r r = 0 := by simp [hK]
    simp only [this, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const, hb]
    simp
  have hoff : ∀ r s, r ≠ s → (∫ α in a..b, cexp (K r s * (α : ℂ))) =
      (cexp (K r s * (b : ℂ)) - cexp (K r s * (a : ℂ))) / K r s := by
    intro r s hrs
    have huv : u r ≠ u s := by
      intro h
      have := hsep r s hrs
      rw [h, sub_self, abs_zero] at this
      linarith
    exact integral_mvExp_diff huv a b
  -- split the double sum into diagonal and off-diagonal
  have hsplit : ∀ (g : ι → ι → ℂ), (∑ r, ∑ s, g r s) =
      ∑ r, g r r + ∑ r, ∑ s, (if r = s then 0 else g r s) := by
    intro g
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hpt' : ∀ s, g r s = (if r = s then g r s else 0) + (if r = s then 0 else g r s) := by
      intro s
      split_ifs <;> simp
    conv_lhs => rw [Finset.sum_congr rfl fun s _ => hpt' s]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  -- the two endpoint Hilbert forms
  set x : ℝ → ι → ℂ := fun t r => c r * mvExp (u r) t with hx
  set Mform : ℝ → ℂ := fun t => ∑ r, ∑ s, (if r = s then (0 : ℂ)
      else x t r * conj (x t s) / ((u r - u s : ℝ) : ℂ)) with hM
  have hoffterm : ∀ r s, r ≠ s →
      c r * conj (c s) * ((cexp (K r s * (b : ℂ)) - cexp (K r s * (a : ℂ))) / K r s) =
        (1 / (2 * Real.pi * I)) *
          (x b r * conj (x b s) / ((u r - u s : ℝ) : ℂ) -
            x a r * conj (x a s) / ((u r - u s : ℝ) : ℂ)) := by
    intro r s hrs
    have huv : u r ≠ u s := by
      intro h
      have := hsep r s hrs
      rw [h, sub_self, abs_zero] at this
      linarith
    have hne : ((u r - u s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr huv
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    have hxb : x b r * conj (x b s) = c r * conj (c s) * cexp (K r s * (b : ℂ)) := by
      simp only [hx, map_mul]
      rw [show c r * mvExp (u r) b * (conj (c s) * conj (mvExp (u s) b)) =
        c r * conj (c s) * (mvExp (u r) b * conj (mvExp (u s) b)) by ring,
        mvExp_mul_conj_mvExp]
    have hxa : x a r * conj (x a s) = c r * conj (c s) * cexp (K r s * (a : ℂ)) := by
      simp only [hx, map_mul]
      rw [show c r * mvExp (u r) a * (conj (c s) * conj (mvExp (u s) a)) =
        c r * conj (c s) * (mvExp (u r) a * conj (mvExp (u s) a)) by ring,
        mvExp_mul_conj_mvExp]
    rw [hxb, hxa]
    have hKne : K r s ≠ 0 := mul_ne_zero hpi hne
    rw [hK]
    field_simp
  have hMbound : ∀ t : ℝ, ‖Mform t‖ ≤ 26 * (Sc / D) := by
    intro t
    have hinj : Function.Injective u := by
      intro r s h
      by_contra hrs
      have := hsep r s hrs
      rw [h, sub_self, abs_zero] at this
      linarith
    have hmv := RiemannGaussian.MontgomeryVaughan.mvHilbert_twentySix ι u (fun _ => D)
      (x t) (x t) hinj (fun _ => hD) (fun r s hrs => hsep r s hrs)
    have hnormx : ∀ r, ‖x t r‖ = ‖c r‖ := by
      intro r
      simp only [hx, norm_mul, norm_mvExp, mul_one]
    have hsum : (∑ r, ‖x t r‖ ^ 2 / D) = Sc / D := by
      rw [hSc, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by rw [hnormx]
    rw [hsum] at hmv
    have hsq : Real.sqrt (Sc / D) * Real.sqrt (Sc / D) = Sc / D :=
      Real.mul_self_sqrt (div_nonneg hSc0 hD.le)
    calc
      ‖Mform t‖ = ‖∑ r, ∑ s, (if r = s then (0 : ℂ)
          else x t r * conj (x t s) / ((u r - u s : ℝ) : ℂ))‖ := rfl
      _ ≤ 26 * Real.sqrt (Sc / D) * Real.sqrt (Sc / D) := hmv
      _ = 26 * (Sc / D) := by rw [mul_assoc, hsq]
  -- assemble
  have hdouble : (∑ r, ∑ s, c r * conj (c s) * ∫ α in a..b, cexp (K r s * (α : ℂ))) =
      (ℓ : ℂ) * (Sc : ℂ) + (1 / (2 * Real.pi * I)) * (Mform b - Mform a) := by
    rw [hsplit]
    congr 1
    · rw [hSc]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hdiag, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    · simp only [hM, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      split_ifs with hrs
      · simp
      · rw [hoff r s hrs, hoffterm r s hrs]
  have hOffnorm : ‖(1 / (2 * Real.pi * I : ℂ)) * (Mform b - Mform a)‖ ≤ 26 / (Real.pi * D) * Sc := by
    rw [norm_mul, norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
    have h1 := hMbound b
    have h2 := hMbound a
    have h3 : ‖Mform b - Mform a‖ ≤ 2 * (26 * (Sc / D)) := by
      calc
        ‖Mform b - Mform a‖ ≤ ‖Mform b‖ + ‖Mform a‖ := norm_sub_le _ _
        _ ≤ 26 * (Sc / D) + 26 * (Sc / D) := add_le_add h1 h2
        _ = _ := by ring
    calc
      1 / (2 * Real.pi) * ‖Mform b - Mform a‖ ≤ 1 / (2 * Real.pi) * (2 * (26 * (Sc / D))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 26 / (Real.pi * D) * Sc := by
        field_simp
  rw [hint, hdouble, Complex.add_re]
  have hre1 : ((ℓ : ℂ) * (Sc : ℂ)).re = ℓ * Sc := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre1]
  have hre2 : -(26 / (Real.pi * D) * Sc) ≤ ((1 / (2 * Real.pi * I : ℂ)) * (Mform b - Mform a)).re := by
    have := Complex.abs_re_le_norm ((1 / (2 * Real.pi * I : ℂ)) * (Mform b - Mform a))
    have := (abs_le.mp this).1
    linarith
  nlinarith [hre2]

/-- **Montgomery–Vaughan interval mean square, upper bound.**  Same hypotheses: the mean square over
`[a, a+ℓ]` is at most `(ℓ + 26/(πD)) Σ_r ‖c_r‖²`. -/
theorem interval_integral_normSq_expSum_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (c : ι → ℂ) {D a ℓ : ℝ} (hD : 0 < D)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    (∫ α in a..a + ℓ, ‖∑ r, c r * mvExp (u r) α‖ ^ 2) ≤
      (ℓ + 26 / (Real.pi * D)) * ∑ r, ‖c r‖ ^ 2 := by
  classical
  set b := a + ℓ with hb
  set S : ℝ → ℂ := fun α => ∑ r, c r * mvExp (u r) α with hS
  set K : ι → ι → ℂ := fun r s => 2 * Real.pi * I * ((u r - u s : ℝ) : ℂ) with hK
  set Sc : ℝ := ∑ r, ‖c r‖ ^ 2 with hSc
  have hSc0 : 0 ≤ Sc := Finset.sum_nonneg fun r _ => by positivity
  have hpt : ∀ α : ℝ, ((‖S α‖ ^ 2 : ℝ) : ℂ) =
      ∑ r, ∑ s, c r * conj (c s) * cexp (K r s * (α : ℂ)) := by
    intro α
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [hS, map_sum, Finset.sum_mul_sum, map_mul]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have := mvExp_mul_conj_mvExp (u r) (u s) α
    calc
      c r * mvExp (u r) α * (conj (c s) * conj (mvExp (u s) α)) =
          c r * conj (c s) * (mvExp (u r) α * conj (mvExp (u s) α)) := by ring
      _ = _ := by rw [this]
  have hcont : ∀ r s, Continuous (fun α : ℝ => c r * conj (c s) * cexp (K r s * (α : ℂ))) := by
    intro r s
    fun_prop
  have hint : (∫ α in a..b, ‖S α‖ ^ 2) =
      (∑ r, ∑ s, c r * conj (c s) * ∫ α in a..b, cexp (K r s * (α : ℂ))).re := by
    have h1 : ((∫ α in a..b, ‖S α‖ ^ 2 : ℝ) : ℂ) = ∫ α in a..b, ((‖S α‖ ^ 2 : ℝ) : ℂ) :=
      (intervalIntegral.integral_ofReal).symm
    have h2 : (∫ α in a..b, ((‖S α‖ ^ 2 : ℝ) : ℂ)) =
        ∑ r, ∑ s, c r * conj (c s) * ∫ α in a..b, cexp (K r s * (α : ℂ)) := by
      simp_rw [hpt]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun s _ => ?_
          rw [intervalIntegral.integral_const_mul]
        · intro s _
          exact (hcont r s).intervalIntegrable _ _
      · intro r _
        exact (continuous_finsetSum _ fun s _ => hcont r s).intervalIntegrable _ _
    have h3 := congrArg Complex.re (h1.trans h2)
    rw [Complex.ofReal_re] at h3
    exact h3
  have hdiag : ∀ r, (∫ α in a..b, cexp (K r r * (α : ℂ))) = (ℓ : ℂ) := by
    intro r
    have : K r r = 0 := by simp [hK]
    simp only [this, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const, hb]
    simp
  have hoff : ∀ r s, r ≠ s → (∫ α in a..b, cexp (K r s * (α : ℂ))) =
      (cexp (K r s * (b : ℂ)) - cexp (K r s * (a : ℂ))) / K r s := by
    intro r s hrs
    have huv : u r ≠ u s := by
      intro h
      have := hsep r s hrs
      rw [h, sub_self, abs_zero] at this
      linarith
    exact integral_mvExp_diff huv a b
  have hsplit : ∀ (g : ι → ι → ℂ), (∑ r, ∑ s, g r s) =
      ∑ r, g r r + ∑ r, ∑ s, (if r = s then 0 else g r s) := by
    intro g
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hpt' : ∀ s, g r s = (if r = s then g r s else 0) + (if r = s then 0 else g r s) := by
      intro s
      split_ifs <;> simp
    conv_lhs => rw [Finset.sum_congr rfl fun s _ => hpt' s]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  set x : ℝ → ι → ℂ := fun t r => c r * mvExp (u r) t with hx
  set Mform : ℝ → ℂ := fun t => ∑ r, ∑ s, (if r = s then (0 : ℂ)
      else x t r * conj (x t s) / ((u r - u s : ℝ) : ℂ)) with hM
  have hoffterm : ∀ r s, r ≠ s →
      c r * conj (c s) * ((cexp (K r s * (b : ℂ)) - cexp (K r s * (a : ℂ))) / K r s) =
        (1 / (2 * Real.pi * I)) *
          (x b r * conj (x b s) / ((u r - u s : ℝ) : ℂ) -
            x a r * conj (x a s) / ((u r - u s : ℝ) : ℂ)) := by
    intro r s hrs
    have huv : u r ≠ u s := by
      intro h
      have := hsep r s hrs
      rw [h, sub_self, abs_zero] at this
      linarith
    have hne : ((u r - u s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr huv
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    have hxb : x b r * conj (x b s) = c r * conj (c s) * cexp (K r s * (b : ℂ)) := by
      simp only [hx, map_mul]
      rw [show c r * mvExp (u r) b * (conj (c s) * conj (mvExp (u s) b)) =
        c r * conj (c s) * (mvExp (u r) b * conj (mvExp (u s) b)) by ring,
        mvExp_mul_conj_mvExp]
    have hxa : x a r * conj (x a s) = c r * conj (c s) * cexp (K r s * (a : ℂ)) := by
      simp only [hx, map_mul]
      rw [show c r * mvExp (u r) a * (conj (c s) * conj (mvExp (u s) a)) =
        c r * conj (c s) * (mvExp (u r) a * conj (mvExp (u s) a)) by ring,
        mvExp_mul_conj_mvExp]
    rw [hxb, hxa]
    have hKne : K r s ≠ 0 := mul_ne_zero hpi hne
    rw [hK]
    field_simp
  have hMbound : ∀ t : ℝ, ‖Mform t‖ ≤ 26 * (Sc / D) := by
    intro t
    have hinj : Function.Injective u := by
      intro r s h
      by_contra hrs
      have := hsep r s hrs
      rw [h, sub_self, abs_zero] at this
      linarith
    have hmv := RiemannGaussian.MontgomeryVaughan.mvHilbert_twentySix ι u (fun _ => D)
      (x t) (x t) hinj (fun _ => hD) (fun r s hrs => hsep r s hrs)
    have hnormx : ∀ r, ‖x t r‖ = ‖c r‖ := by
      intro r
      simp only [hx, norm_mul, norm_mvExp, mul_one]
    have hsum : (∑ r, ‖x t r‖ ^ 2 / D) = Sc / D := by
      rw [hSc, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by rw [hnormx]
    rw [hsum] at hmv
    have hsq : Real.sqrt (Sc / D) * Real.sqrt (Sc / D) = Sc / D :=
      Real.mul_self_sqrt (div_nonneg hSc0 hD.le)
    calc
      ‖Mform t‖ = ‖∑ r, ∑ s, (if r = s then (0 : ℂ)
          else x t r * conj (x t s) / ((u r - u s : ℝ) : ℂ))‖ := rfl
      _ ≤ 26 * Real.sqrt (Sc / D) * Real.sqrt (Sc / D) := hmv
      _ = 26 * (Sc / D) := by rw [mul_assoc, hsq]
  have hdouble : (∑ r, ∑ s, c r * conj (c s) * ∫ α in a..b, cexp (K r s * (α : ℂ))) =
      (ℓ : ℂ) * (Sc : ℂ) + (1 / (2 * Real.pi * I)) * (Mform b - Mform a) := by
    rw [hsplit]
    congr 1
    · rw [hSc]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hdiag, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    · simp only [hM, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      split_ifs with hrs
      · simp
      · rw [hoff r s hrs, hoffterm r s hrs]
  have hOffnorm : ‖(1 / (2 * Real.pi * I : ℂ)) * (Mform b - Mform a)‖ ≤ 26 / (Real.pi * D) * Sc := by
    rw [norm_mul, norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
    have h1 := hMbound b
    have h2 := hMbound a
    have h3 : ‖Mform b - Mform a‖ ≤ 2 * (26 * (Sc / D)) := by
      calc
        ‖Mform b - Mform a‖ ≤ ‖Mform b‖ + ‖Mform a‖ := norm_sub_le _ _
        _ ≤ 26 * (Sc / D) + 26 * (Sc / D) := add_le_add h1 h2
        _ = _ := by ring
    calc
      1 / (2 * Real.pi) * ‖Mform b - Mform a‖ ≤ 1 / (2 * Real.pi) * (2 * (26 * (Sc / D))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 26 / (Real.pi * D) * Sc := by
        field_simp
  rw [hint, hdouble, Complex.add_re]
  have hre1 : ((ℓ : ℂ) * (Sc : ℂ)).re = ℓ * Sc := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre1]
  have hre2 : ((1 / (2 * Real.pi * I : ℂ)) * (Mform b - Mform a)).re ≤ 26 / (Real.pi * D) * Sc := by
    have := Complex.abs_re_le_norm ((1 / (2 * Real.pi * I : ℂ)) * (Mform b - Mform a))
    have := (abs_le.mp this).2
    linarith
  nlinarith [hre2]

end

end GaloisForLFunctions.HTGeometry
