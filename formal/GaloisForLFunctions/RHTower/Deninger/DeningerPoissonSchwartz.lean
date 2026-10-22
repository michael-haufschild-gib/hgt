import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonWeight
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz

/-!
# Every exponential weight of a Poisson sum is a Schwartz function

Choosing the decay order from the weight — two orders above `|s|` suffices — the two-ended
estimates of the Poisson sum beat the exponential weight at both ends of the logarithmic line: at
`+∞` the large-end estimate leaves a factor `e^{-t}`, at `−∞` the small-end estimate leaves a
factor `e^{t}`, and `uᵏe^{-u} ≤ k!` finishes.  Since every derivative of a weighted Poisson sum is
again a weighted Poisson sum of a member of Meyer's space, the same bound applies at every order.

So each weight `t ↦ e^{st}G_f(t)` is a Schwartz function of the logarithmic coordinate, and the
family of all integer weights is a member of the radial space: this is the Poisson operator
`Z : ℋ_∩ → ℋ_−` of the card, constructed as a linear map.

* `deningerPoissonSchwartz` : **the weight, as a Schwartz map.**
* `deningerPoissonFamily_mem` : **the family of all integer weights lies in the radial space.**
* `deningerPoissonLM` : **the Poisson operator `Z : ℋ_∩ → ℋ_−`, linear.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## The decay index -/

/-- The decay order used against the weight `e^{st}`: two orders above `|s|`. -/
def deningerPoissonDecayIndex (s : ℤ) : ℕ := s.natAbs + 1

theorem deningerPoisson_natAbs_cast (s : ℤ) : ((s.natAbs : ℕ) : ℝ) = |(s : ℝ)| := by
  rw [Nat.cast_natAbs]
  rw [Int.cast_abs]

theorem deningerPoisson_large_exponent (s : ℤ) :
    (s : ℝ) - (ccmRationalArchimedeanDecayExponent (deningerPoissonDecayIndex s) : ℕ) + 1 ≤ 0 := by
  rw [ccmRationalArchimedeanDecayExponent, deningerPoissonDecayIndex]
  have habs : ((s.natAbs : ℕ) : ℝ) = |(s : ℝ)| := deningerPoisson_natAbs_cast s
  have hle : (s : ℝ) ≤ |(s : ℝ)| := le_abs_self _
  have hnn : (0 : ℝ) ≤ |(s : ℝ)| := abs_nonneg _
  push_cast
  rw [habs]
  linarith

theorem deningerPoisson_small_exponent (s : ℤ) :
    0 ≤ (s : ℝ) + (ccmRationalArchimedeanDecayExponent (deningerPoissonDecayIndex s) : ℕ) - 2 := by
  rw [ccmRationalArchimedeanDecayExponent, deningerPoissonDecayIndex]
  have habs : ((s.natAbs : ℕ) : ℝ) = |(s : ℝ)| := deningerPoisson_natAbs_cast s
  have hle : -|(s : ℝ)| ≤ (s : ℝ) := neg_abs_le _
  have hnn : (0 : ℝ) ≤ |(s : ℝ)| := abs_nonneg _
  push_cast
  rw [habs]
  linarith

/-! ## The constraints of Meyer's space in analytic form -/

theorem deningerMeyerCap_even {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerMeyerCap) :
    ∀ x : ℝ, h (-x) = h x := ((deningerMeyerCap_mem_iff h).mp hh).1

theorem deningerMeyerCap_zero {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerMeyerCap) : h 0 = 0 :=
  ((deningerMeyerCap_mem_iff h).mp hh).2.1

theorem deningerMeyerCap_fourier_zero {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerMeyerCap) :
    (𝓕 (h : ℝ → ℂ)) 0 = 0 := by
  have hF := ((deningerMeyerCap_mem_iff h).mp hh).2.2
  have hcle : (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) h) = fourierSCLM h := by
    rw [FourierTransform.fourierCLE_apply, fourierSCLM_eq]
  rw [hcle] at hF
  exact hF

/-! ## The decay of a weighted Poisson sum -/

theorem norm_deningerPoissonWeight (s : ℤ) (h : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖deningerPoissonWeight s h t‖
      = Real.exp ((s : ℝ) * t) * ‖deningerPoissonLog h t‖ := by
  rw [deningerPoissonWeight, norm_mul, deningerExpWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem norm_deningerPoissonWeight_le_of_nonneg (s : ℤ) (k : ℕ) {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerMeyerCap) {t : ℝ} (ht : 0 ≤ t) :
    ‖t‖ ^ k * ‖deningerPoissonWeight s h t‖
      ≤ ccmRationalArchimedeanDecayConstant h (deningerPoissonDecayIndex s) / 2
        * (Nat.factorial k : ℝ) := by
  set N : ℕ := deningerPoissonDecayIndex s with hN
  set p : ℕ := ccmRationalArchimedeanDecayExponent N with hp
  set C : ℝ := ccmRationalArchimedeanDecayConstant h N with hC
  have hCnn : 0 ≤ C := ccmRationalArchimedeanDecayConstant_nonneg h N
  have hexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hvalue := norm_deningerPoissonValue_le_large (deningerMeyerCap_even hh)
    (deningerMeyerCap_zero hh) N hexp
  have hlog : ‖deningerPoissonLog h t‖ ≤ C / (Real.exp t) ^ p / 2 := by
    rw [deningerPoissonLog_eq]
    exact hvalue
  have hpow : (Real.exp t) ^ p = Real.exp ((p : ℝ) * t) := by
    rw [Real.exp_nat_mul]
  have hnormt : ‖t‖ = t := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht]
  rw [norm_deningerPoissonWeight, hnormt]
  have hchain : t ^ k * (Real.exp ((s : ℝ) * t) * ‖deningerPoissonLog h t‖)
      ≤ t ^ k * (Real.exp ((s : ℝ) * t) * (C / Real.exp ((p : ℝ) * t) / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    rw [← hpow]
    exact hlog
  refine hchain.trans ?_
  have hrw : t ^ k * (Real.exp ((s : ℝ) * t) * (C / Real.exp ((p : ℝ) * t) / 2))
      = C / 2 * (t ^ k * Real.exp (((s : ℝ) - (p : ℝ)) * t)) := by
    rw [show ((s : ℝ) - (p : ℝ)) * t = (s : ℝ) * t - (p : ℝ) * t by ring, Real.exp_sub]
    have hne : Real.exp ((p : ℝ) * t) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [hrw]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hexpon : ((s : ℝ) - (p : ℝ)) * t ≤ -t := by
    have hle : (s : ℝ) - (p : ℝ) + 1 ≤ 0 := deningerPoisson_large_exponent s
    nlinarith [ht]
  calc t ^ k * Real.exp (((s : ℝ) - (p : ℝ)) * t)
      ≤ t ^ k * Real.exp (-t) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpon) (by positivity)
    _ ≤ (Nat.factorial k : ℝ) := pow_mul_exp_neg_le_factorial k ht

theorem norm_deningerPoissonWeight_le_of_nonpos (s : ℤ) (k : ℕ) {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerMeyerCap) {t : ℝ} (ht : t ≤ 0) :
    ‖t‖ ^ k * ‖deningerPoissonWeight s h t‖
      ≤ ccmRationalArchimedeanDecayConstant (𝓕 h) (deningerPoissonDecayIndex s) / 2
        * (Nat.factorial k : ℝ) := by
  set N : ℕ := deningerPoissonDecayIndex s with hN
  set p : ℕ := ccmRationalArchimedeanDecayExponent N with hp
  set C : ℝ := ccmRationalArchimedeanDecayConstant (𝓕 h) N with hC
  have hCnn : 0 ≤ C := ccmRationalArchimedeanDecayConstant_nonneg (𝓕 h) N
  have hexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hvalue := norm_deningerPoissonValue_le_small (deningerMeyerCap_even hh)
    (deningerMeyerCap_zero hh) (deningerMeyerCap_fourier_zero hh) N hexp
  have hlog : ‖deningerPoissonLog h t‖ ≤ C * (Real.exp t) ^ (p - 1) / 2 := by
    rw [deningerPoissonLog_eq]
    exact hvalue
  have hpow : (Real.exp t) ^ (p - 1) = Real.exp (((p : ℝ) - 1) * t) := by
    have hple : 1 ≤ p := (ccmRationalArchimedeanDecayExponent_gt_one N).le
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      have : (1 : ℕ) ≤ p := hple
      push_cast [Nat.cast_sub this]
      ring
    rw [← hcast, Real.exp_nat_mul]
  have hnormt : ‖t‖ = -t := by
    rw [Real.norm_eq_abs, abs_of_nonpos ht]
  rw [norm_deningerPoissonWeight, hnormt]
  have hnegnn : (0 : ℝ) ≤ -t := by linarith
  have hchain : (-t) ^ k * (Real.exp ((s : ℝ) * t) * ‖deningerPoissonLog h t‖)
      ≤ (-t) ^ k * (Real.exp ((s : ℝ) * t) * (C * Real.exp (((p : ℝ) - 1) * t) / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hnegnn k)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    rw [← hpow]
    exact hlog
  refine hchain.trans ?_
  have hrw : (-t) ^ k * (Real.exp ((s : ℝ) * t) * (C * Real.exp (((p : ℝ) - 1) * t) / 2))
      = C / 2 * ((-t) ^ k * Real.exp (((s : ℝ) + (p : ℝ) - 1) * t)) := by
    rw [show ((s : ℝ) + (p : ℝ) - 1) * t = (s : ℝ) * t + ((p : ℝ) - 1) * t by ring,
      Real.exp_add]
    ring
  rw [hrw]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hexpon : ((s : ℝ) + (p : ℝ) - 1) * t ≤ -(-t) := by
    have hle : 0 ≤ (s : ℝ) + (p : ℝ) - 2 := deningerPoisson_small_exponent s
    nlinarith [ht]
  calc (-t) ^ k * Real.exp (((s : ℝ) + (p : ℝ) - 1) * t)
      ≤ (-t) ^ k * Real.exp (-(-t)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpon) (pow_nonneg hnegnn k)
    _ ≤ (Nat.factorial k : ℝ) := pow_mul_exp_neg_le_factorial k (by linarith)

/-- **Every weighted Poisson sum of a member of Meyer's space has bounded polynomial weights.** -/
theorem exists_bound_deningerPoissonWeight (s : ℤ) (k : ℕ) {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerMeyerCap) :
    ∃ C : ℝ, ∀ t : ℝ, ‖t‖ ^ k * ‖deningerPoissonWeight s h t‖ ≤ C := by
  refine ⟨max (ccmRationalArchimedeanDecayConstant h (deningerPoissonDecayIndex s) / 2
      * (Nat.factorial k : ℝ))
    (ccmRationalArchimedeanDecayConstant (𝓕 h) (deningerPoissonDecayIndex s) / 2
      * (Nat.factorial k : ℝ)), fun t => ?_⟩
  rcases le_total 0 t with ht | ht
  · exact (norm_deningerPoissonWeight_le_of_nonneg s k hh ht).trans (le_max_left _ _)
  · exact (norm_deningerPoissonWeight_le_of_nonpos s k hh ht).trans (le_max_right _ _)

/-! ## The Schwartz map and the Poisson operator -/

/-- **The `s`-th exponential weight of the Poisson sum, as a Schwartz map** of the logarithmic
coordinate. -/
def deningerPoissonSchwartz (s : ℤ) (h : 𝓢(ℝ, ℂ)) (hh : h ∈ DeningerMeyerCap) : 𝓢(ℝ, ℂ) where
  toFun := deningerPoissonWeight s h
  smooth' := contDiff_deningerPoissonWeight s h
  decay' k n := by
    obtain ⟨C, hC⟩ := exists_bound_deningerPoissonWeight s k
      (deningerMeyerCap_shiftCLM_iterate hh s n)
    refine ⟨C, fun t => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_deningerPoissonWeight]
    exact hC t

@[simp] theorem deningerPoissonSchwartz_apply (s : ℤ) (h : 𝓢(ℝ, ℂ)) (hh : h ∈ DeningerMeyerCap)
    (t : ℝ) : deningerPoissonSchwartz s h hh t = deningerPoissonWeight s h t := rfl

/-- The family of all integer weights of the Poisson sum of a member of Meyer's space. -/
def deningerPoissonFamily (h : 𝓢(ℝ, ℂ)) (hh : h ∈ DeningerMeyerCap) : ∀ _ : ℤ, 𝓢(ℝ, ℂ) :=
  fun s => deningerPoissonSchwartz s h hh

/-- **The family of weights lies in the radial space.** -/
theorem deningerPoissonFamily_mem (h : 𝓢(ℝ, ℂ)) (hh : h ∈ DeningerMeyerCap) :
    deningerPoissonFamily h hh ∈ deningerRadialCompat := by
  intro s t
  show deningerPoissonWeight s h t = Complex.exp ((s : ℂ) * t) * deningerPoissonWeight 0 h t
  rw [deningerPoissonWeight, deningerPoissonWeight, deningerExpWeight, deningerExpWeight]
  have hzero : ((Real.exp (((0 : ℤ) : ℝ) * t) : ℝ) : ℂ) = 1 := by
    norm_num
  rw [hzero, one_mul]
  have hcast : ((Real.exp (((s : ℤ) : ℝ) * t) : ℝ) : ℂ) = Complex.exp ((s : ℂ) * t) := by
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hcast]

/-! ## The operator -/

theorem deningerPoissonWeight_add (s : ℤ) (f g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deningerPoissonWeight s (f + g) t
      = deningerPoissonWeight s f t + deningerPoissonWeight s g t := by
  rw [deningerPoissonWeight, deningerPoissonWeight, deningerPoissonWeight,
    deningerPoissonLog_add]
  ring

theorem deningerPoissonWeight_smul (s : ℤ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deningerPoissonWeight s (c • f) t = c * deningerPoissonWeight s f t := by
  rw [deningerPoissonWeight, deningerPoissonWeight, deningerPoissonLog_smul]
  ring

/-- **The Poisson operator `Z : ℋ_∩ → ℋ_−`**, as a linear map: it sends a member of Meyer's space
to the family of all integer exponential weights of its Poisson sum. -/
def deningerPoissonLM : DeningerMeyerCap →ₗ[ℂ] deningerRadialCompat where
  toFun h := ⟨deningerPoissonFamily (h : 𝓢(ℝ, ℂ)) h.2,
    deningerPoissonFamily_mem (h : 𝓢(ℝ, ℂ)) h.2⟩
  map_add' h g := by
    refine Subtype.ext ?_
    funext s
    refine SchwartzMap.ext fun t => ?_
    show deningerPoissonWeight s ((h : 𝓢(ℝ, ℂ)) + (g : 𝓢(ℝ, ℂ))) t
      = deningerPoissonWeight s (h : 𝓢(ℝ, ℂ)) t + deningerPoissonWeight s (g : 𝓢(ℝ, ℂ)) t
    exact deningerPoissonWeight_add s _ _ t
  map_smul' c h := by
    refine Subtype.ext ?_
    funext s
    refine SchwartzMap.ext fun t => ?_
    show deningerPoissonWeight s (c • (h : 𝓢(ℝ, ℂ))) t
      = c • deningerPoissonWeight s (h : 𝓢(ℝ, ℂ)) t
    rw [deningerPoissonWeight_smul, smul_eq_mul]

@[simp] theorem deningerPoissonLM_apply (h : DeningerMeyerCap) (s : ℤ) (t : ℝ) :
    ((deningerPoissonLM h : deningerRadialCompat) : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) s t
      = deningerPoissonWeight s (h : 𝓢(ℝ, ℂ)) t := rfl

end RHTower

end
