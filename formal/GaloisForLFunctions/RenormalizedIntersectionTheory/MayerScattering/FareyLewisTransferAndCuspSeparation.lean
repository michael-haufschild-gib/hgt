import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisPeriodReflectionPositivity
import GaloisForLFunctions.RHTower.DQPTAltPartialSum

/-!
# Source-Side Farey–Hecke Operator Algebra, Three-Term Cusp-Erasure Obstruction, and Dyadic Cusp-Energy Separation

This module develops the autonomous source-side operator calculus on the canonical `s`-independent
Möbius–critical Hilbert space `H_LP = L²((0, ∞), w_LP(a) da)`
(`w_LP(a) = (a + a⁻¹)^(-6) * a^(-1/2)`) and resolves the separation of scattering resonances from
generic continuous scattering (`Mayer 4`):

1. **Polar Square and Norm-Boundedness Criterion for Modular Inversion `I_s`:**
   Pointwise on `(0, ∞)`, `(I_{1/2 - conj s}(I_s f))(a) = a^(4 Re s - 1) f(a)` is multiplication by
   a pure real power independent of `Im s`, and `I_s` is norm-bounded on `H_LP` iff `s.re = 1/4`.
2. **Gauss–Mayer Renewal Branch Dichotomy on `H_LP`:**
   In period coordinates on `(0, ∞)`, every tail branch `(G_{m,s} f)(a) = (a + m)^(-2s) f(1 + (a + m)⁻¹)`
   (`m ≥ 1`) is norm-bounded on `H_LP` across `s.re ≥ 0`, whereas the head branch `G_{0,s} = I_s U_1`
   (`s.re ≥ 0`) is norm-bounded on `H_LP` iff `s.re ≤ 1/4`; consequently the Riemann–Mayer pair
   `(G_{0,s}, G_{0,1/2 - conj s})` is simultaneously bounded on `H_LP` (`0 ≤ s.re ≤ 1/2`) iff `s.re = 1/4`.
3. **Farey–Lewis Three-Term Operator `M_s = U_1 + V_s`, Koopman Adjoints, and Self-Commutator:**
   Both `U_1` and `V_s` are norm-bounded on `H_LP` across `s.re ≥ 0`, with formal Hilbert adjoints
   `U_1†` supported on `(1, ∞)` and `V_s†` supported on `(0, 1)` satisfying `U_1 V_s† = 0` and
   `V_s U_1† = 0`. Hence `(M_s(M_s† g))(a) = μ_s(a) g(a)` is pure multiplication with `μ_s(a) > 1`
   for all `a > 0` and `s.re ≤ 1/2`, forcing strict self-commutator negativity
   `lewisCriticalNormSq (M_s ψ) - lewisCriticalNormSq (M_s† ψ) < 0` on every nonzero continuous
   three-term fixed point `M_s ψ = ψ` in `H_LP`. Moreover, the Manin–Mühlenbruch Hecke operator
   `T_{2,s}` satisfies the universal identities `I_s T_{2,s} = T_{2,s} I_s` and
   `(1 - M_s) T_{2,s} = T̃_{2,s}(1 - M_s)`.
4. **Three-Term Cusp-Erasure Obstruction & Autonomous Dyadic Cusp-Energy Separation (`Mayer 4`):**
   Every signed Mayer solution `(f ∈ DiscSpace, c ∈ ℂ, ε² = 1)` on `s.re > 0` (`2s ≠ 1`) obeys the
   quantitative derivative-free dyadic cusp asymptotic
   `‖ψ(2a) - 2^(1 - 2s) ψ(a) + ε (1 - 2^(1 - 2s)) c‖ ≤ C a^(-2 Re s)` (`a ≥ 1`). Across the strip
   `0 < s.re < 1/2`, the continuous Eisenstein period `Ψ_s^Eis = period (2s) 1 (-ζ(2s)) (state (2s))`
   satisfies `I_s Ψ = Ψ`, `M_s Ψ = Ψ`, and `lewisCoIsometryDefect s Ψ < 0 ↔ s.re ≠ 1/4` at both
   resonant and non-resonant points (refuting naive three-term reflection positivity unconditionally
   at every real `σ ∈ (0, 1/2) \ {1/4}`), while finite dyadic cusp energy
   `IntegrableOn (fun a => ‖ψ(2a) - 2^(1 - 2s) ψ(a)‖² / a) (Ioi 1)` holds iff `c = 0` — hence for
   `Ψ_s^Eis`, iff `IsMayerScatteringResonance s`.
-/

open Complex Set Filter MeasureTheory Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin MayerScatteringState
open MayerExtendedTransfer MayerGlobalPeriods

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ## Part 1: Polar square and norm-boundedness criterion for modular inversion `I_s` -/

/-- Pointwise polar square `(I_{1/2 - conj s}(I_s f))(a) = a^(4 Re s - 1) f(a)` on `(0, ∞)`. -/
theorem lewisModularInversion_adj_comp_self (s : ℂ) (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    lewisModularInversion (riemannMayerReflect s) (lewisModularInversion s f) a =
      ((a ^ (4 * s.re - 1) : ℝ) : ℂ) * f a := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold lewisModularInversion
  rw [ofReal_inv_cpow_pos ha (-(2 * s)), neg_neg, inv_inv, ← mul_assoc,
    ← Complex.cpow_add _ _ haC]
  have hexp : -(2 * riemannMayerReflect s) + 2 * s = ((4 * s.re - 1 : ℝ) : ℂ) := by
    unfold riemannMayerReflect
    apply Complex.ext <;> simp <;> ring
  rw [hexp, ← Complex.ofReal_cpow ha.le]

/-- Dual polar square `(I_s(I_{1/2 - conj s} f))(a) = a^(1 - 4 Re s) f(a)` on `(0, ∞)`. -/
theorem lewisModularInversion_self_comp_adj (s : ℂ) (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (lewisModularInversion (riemannMayerReflect s) f) a =
      ((a ^ (1 - 4 * s.re) : ℝ) : ℂ) * f a := by
  have h := lewisModularInversion_adj_comp_self (riemannMayerReflect s) f ha
  rw [riemannMayerReflect_involutive, riemannMayerReflect_re,
    show 4 * (1 / 2 - s.re) - 1 = 1 - 4 * s.re by ring] at h
  exact h

private theorem integrableOn_lewisCriticalWeight_Ioc {p q : ℝ} (hp : 0 < p) :
    IntegrableOn lewisCriticalWeight (Ioc p q) := by
  by_cases hpq : p ≤ q
  ·exact (lewisCriticalWeight_continuousOn.mono
      (fun x hx => lt_of_lt_of_le hp hx.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · rw [Ioc_eq_empty hpq]
    exact integrableOn_empty

private theorem setIntegral_lewisCriticalWeight_Ioc_pos {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    0 < ∫ x in Ioc p q, lewisCriticalWeight x := by
  have hcont : ContinuousOn lewisCriticalWeight (Icc p q) :=
    lewisCriticalWeight_continuousOn.mono fun x hx => lt_of_lt_of_le hp hx.1
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hpq.le) hcont
  have hx₀_pos : 0 < x₀ := lt_of_lt_of_le hp hx₀.1
  have hw₀ : 0 < lewisCriticalWeight x₀ := lewisCriticalWeight_pos hx₀_pos
  have hc : (∫ _ in Ioc p q, lewisCriticalWeight x₀) = (q - p) * lewisCriticalWeight x₀ := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hpq.le, smul_eq_mul]
  have hle : (q - p) * lewisCriticalWeight x₀ ≤ ∫ x in Ioc p q, lewisCriticalWeight x := by
    rw [← hc]
    exact setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      (integrableOn_lewisCriticalWeight_Ioc hp) measurableSet_Ioc fun x hx => hmin ⟨hx.1.le, hx.2⟩
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hpq) hw₀) hle

private theorem indicator_Ioc_normSq_integrable {p q : ℝ} (hp : 0 < p) :
    IntegrableOn
      (fun a : ℝ => ‖(Ioc p q).indicator (fun _ => (1 : ℂ)) a‖ ^ 2 * lewisCriticalWeight a)
      (Ioi 0) := by
  have hsub : Ioc p q ⊆ Ioi 0 := fun x hx => hp.trans hx.1
  have hfun : (fun a : ℝ => ‖(Ioc p q).indicator (fun _ => (1 : ℂ)) a‖ ^ 2 * lewisCriticalWeight a) =
      (Ioc p q).indicator lewisCriticalWeight := by
    ext a
    by_cases ha : a ∈ Ioc p q <;> simp [ha]
  rw [hfun, integrableOn_indicator_iff measurableSet_Ioc, inter_eq_self_of_subset_right hsub]
  exact integrableOn_lewisCriticalWeight_Ioc hp

private theorem indicator_Ioc_weighted_integral {p q : ℝ} (hp : 0 < p) (w : ℝ → ℝ) :
    (∫ b in Ioi (0 : ℝ), ‖(Ioc p q).indicator (fun _ => (1 : ℂ)) b‖ ^ 2 * w b) =
      ∫ b in Ioc p q, w b := by
  have hsub : Ioc p q ⊆ Ioi 0 := fun x hx => hp.trans hx.1
  have hfun : (fun b : ℝ => ‖(Ioc p q).indicator (fun _ => (1 : ℂ)) b‖ ^ 2 * w b) =
      (Ioc p q).indicator w := by
    ext b
    by_cases hb : b ∈ Ioc p q <;> simp [hb]
  rw [hfun, setIntegral_indicator measurableSet_Ioc, inter_eq_self_of_subset_right hsub]

/-- `lewisModularInversion s` is norm-bounded on `H_LP` iff `s.re = 1/4`. -/
theorem lewisModularInversion_normBounded_iff (s : ℂ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
      IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
        lewisCriticalNormSq (lewisModularInversion s f) ≤ C * lewisCriticalNormSq f) ↔
      s.re = 1 / 4 := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    by_contra hne
    let K : ℝ := C + 1
    have hK_pos : 0 < K := by dsimp [K]; linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let γ : ℝ := 1 - 4 * s.re
      have hγ_pos : 0 < γ := by dsimp [γ]; linarith
      let R : ℝ := K ^ (1 / γ) + 1
      have hR_gt1 : 1 < R := by
        dsimp [R]
        linarith [Real.rpow_pos_of_pos hK_pos (1 / γ)]
      have hR_pos : 0 < R := zero_lt_one.trans hR_gt1
      let r : ℝ := R⁻¹
      have hr_pos : 0 < r := inv_pos.mpr hR_pos
      have hr2_pos : 0 < r / 2 := half_pos hr_pos
      have hr2_lt : r / 2 < r := half_lt_self hr_pos
      let f : ℝ → ℂ := (Ioc (r / 2) r).indicator (fun _ => 1)
      have hbound := hC f (indicator_Ioc_normSq_integrable hr2_pos)
      rw [lewisCriticalNormSq_modularInversion, indicator_Ioc_weighted_integral hr2_pos] at hbound
      unfold lewisCriticalNormSq at hbound
      rw [indicator_Ioc_weighted_integral hr2_pos] at hbound
      have hint_M : IntegrableOn
          (fun b : ℝ => (b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2)) (Ioc (r / 2) r) := by
        apply ContinuousOn.integrableOn_Icc _ |>.mono_set Ioc_subset_Icc_self
        intro b hb
        have hb0 : 0 < b := lt_of_lt_of_le hr2_pos hb.1
        have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
        exact (((continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow continuousAt_const
          (Or.inl hsum)).mul (continuousAt_id.rpow continuousAt_const
          (Or.inl hb0.ne'))).continuousWithinAt
      have hK_le_Rγ : K < R ^ γ := by
        have h1 : K = (K ^ (1 / γ)) ^ γ := by
          rw [← Real.rpow_mul hK_pos.le, one_div_mul_cancel hγ_pos.ne', Real.rpow_one]
        rw [h1]
        exact Real.rpow_lt_rpow (Real.rpow_pos_of_pos hK_pos _).le (by dsimp [R]; linarith) hγ_pos
      have hlow_pt : ∀ b ∈ Ioc (r / 2) r,
          K * lewisCriticalWeight b ≤ (b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2) := by
        intro b hb
        have hb0 : 0 < b := hr2_pos.trans hb.1
        have hbinv_ge : R ≤ b⁻¹ := by
          have : r⁻¹ ≤ b⁻¹ := (inv_le_inv₀ hr_pos hb0).mpr hb.2
          simpa [r] using this
        have hpow_ge : K ≤ b ^ (4 * s.re - 1) := by
          have h1 : R ^ γ ≤ (b⁻¹) ^ γ :=
            Real.rpow_le_rpow hR_pos.le hbinv_ge hγ_pos.le
          have h2 : (b⁻¹) ^ γ = b ^ (4 * s.re - 1) := by
            rw [Real.inv_rpow hb0.le, ← Real.rpow_neg hb0.le]
            congr 1; dsimp [γ]; ring
          linarith [hK_le_Rγ, h1, h2]
        unfold lewisCriticalWeight
        have hexp : b ^ (4 * s.re - 3 / 2) = b ^ (4 * s.re - 1) * b ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hb0]; congr 1; ring
        rw [hexp]
        have hw0 : 0 ≤ (b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)) :=
          (lewisCriticalWeight_pos hb0).le
        have hmul := mul_le_mul_of_nonneg_right hpow_ge hw0
        linarith [show b ^ (4 * s.re - 1) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ))) =
          (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (4 * s.re - 1) * b ^ (-(1 / 2 : ℝ))) by ring]
      have hint_pos := setIntegral_lewisCriticalWeight_Ioc_pos hr2_pos hr2_lt
      have hmono := setIntegral_mono_on
        ((integrableOn_lewisCriticalWeight_Ioc hr2_pos).const_mul K) hint_M measurableSet_Ioc hlow_pt
      rw [integral_const_mul] at hmono
      have hKC : C * (∫ x in Ioc (r / 2) r, lewisCriticalWeight x) <
          K * (∫ x in Ioc (r / 2) r, lewisCriticalWeight x) :=
        mul_lt_mul_of_pos_right (by dsimp [K]; linarith) hint_pos
      linarith
    · let δ : ℝ := 4 * s.re - 1
      have hδ_pos : 0 < δ := by dsimp [δ]; linarith
      let R : ℝ := K ^ (1 / δ) + 1
      have hR_pos : 0 < R := by
        dsimp [R]; linarith [Real.rpow_pos_of_pos hK_pos (1 / δ)]
      have hR_lt : R < R + 1 := by linarith
      let f : ℝ → ℂ := (Ioc R (R + 1)).indicator (fun _ => 1)
      have hbound := hC f (indicator_Ioc_normSq_integrable hR_pos)
      rw [lewisCriticalNormSq_modularInversion, indicator_Ioc_weighted_integral hR_pos] at hbound
      unfold lewisCriticalNormSq at hbound
      rw [indicator_Ioc_weighted_integral hR_pos] at hbound
      have hint_M : IntegrableOn
          (fun b : ℝ => (b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2)) (Ioc R (R + 1)) := by
        apply ContinuousOn.integrableOn_Icc _ |>.mono_set Ioc_subset_Icc_self
        intro b hb
        have hb0 : 0 < b := lt_of_lt_of_le hR_pos hb.1
        have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
        exact (((continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow continuousAt_const
          (Or.inl hsum)).mul (continuousAt_id.rpow continuousAt_const
          (Or.inl hb0.ne'))).continuousWithinAt
      have hK_lt_Rδ : K < R ^ δ := by
        have h1 : K = (K ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul hK_pos.le, one_div_mul_cancel hδ_pos.ne', Real.rpow_one]
        rw [h1]
        exact Real.rpow_lt_rpow (Real.rpow_pos_of_pos hK_pos _).le (by dsimp [R]; linarith) hδ_pos
      have hlow_pt : ∀ b ∈ Ioc R (R + 1),
          K * lewisCriticalWeight b ≤ (b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2) := by
        intro b hb
        have hb0 : 0 < b := hR_pos.trans hb.1
        have hpow_ge : K ≤ b ^ δ :=
          hK_lt_Rδ.le.trans (Real.rpow_le_rpow hR_pos.le hb.1.le hδ_pos.le)
        unfold lewisCriticalWeight
        have hexp : b ^ (4 * s.re - 3 / 2) = b ^ δ * b ^ (-(1 / 2 : ℝ)) := by
          dsimp [δ]; rw [← Real.rpow_add hb0]; congr 1; ring
        rw [hexp]
        have hw0 : 0 ≤ (b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)) :=
          (lewisCriticalWeight_pos hb0).le
        have hmul := mul_le_mul_of_nonneg_right hpow_ge hw0
        linarith [show b ^ δ * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ))) =
          (b + b⁻¹) ^ (-6 : ℝ) * (b ^ δ * b ^ (-(1 / 2 : ℝ))) by ring]
      have hint_pos := setIntegral_lewisCriticalWeight_Ioc_pos hR_pos hR_lt
      have hmono := setIntegral_mono_on
        ((integrableOn_lewisCriticalWeight_Ioc hR_pos).const_mul K) hint_M measurableSet_Ioc hlow_pt
      rw [integral_const_mul] at hmono
      have hKC : C * (∫ x in Ioc R (R + 1), lewisCriticalWeight x) <
          K * (∫ x in Ioc R (R + 1), lewisCriticalWeight x) :=
        mul_lt_mul_of_pos_right (by dsimp [K]; linarith) hint_pos
      linarith
  · intro hs
    refine ⟨1, zero_le_one, fun f _ => ?_⟩
    rw [one_mul, (lewisModularInversion_isometry_iff s).mpr hs f]

/-! ## Part 2: Gauss–Mayer renewal branches and critical-line boundedness dichotomy -/

/-- Linear shift substitution `b = a + c` on `(0, ∞)`. -/
theorem integral_Ioi_zero_add_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (g : ℝ → E) :
    (∫ a in Ioi (0 : ℝ), g (a + c)) = ∫ b in Ioi c, g b := by
  have himg : (fun a : ℝ => a + c) '' Ioi (0 : ℝ) = Ioi c := by
    ext b
    simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨a, ha, rfl⟩ => by linarith, fun hb => ⟨b - c, by linarith, sub_add_cancel b c⟩⟩
  have hinj : InjOn (fun a : ℝ => a + c) (Ioi 0) := fun _ _ _ _ h => add_right_cancel h
  have hderiv : ∀ a ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x + c) 1 (Ioi 0) a :=
    fun a _ => ((hasDerivAt_id a).add_const c).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [himg] at h
  rw [h]
  simp

/-- The `m`-th Gauss–Mayer renewal branch `(G_{m,s} f)(a) = (a + m)^(-2s) f(1 + (a + m)⁻¹)`
in period coordinates on `(0, ∞)`. -/
def gaussMayerBranch (m : ℕ) (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  ((a + (m : ℝ) : ℝ) : ℂ) ^ (-(2 * s)) * f (1 + (a + (m : ℝ))⁻¹)

theorem lewisCriticalNormSq_gaussMayerBranch_zero (s : ℂ) (f : ℝ → ℂ) :
    lewisCriticalNormSq (gaussMayerBranch 0 s f) =
      ∫ b in Ioi (1 : ℝ),
        ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)) := by
  have hcongr : ∀ a ∈ Ioi (0 : ℝ),
      ‖gaussMayerBranch 0 s f a‖ ^ 2 * lewisCriticalWeight a =
        ‖lewisModularInversion s (fun u => f (u + 1)) a‖ ^ 2 * lewisCriticalWeight a := by
    intro a _
    unfold gaussMayerBranch lewisModularInversion
    simp [add_comm (1 : ℝ) a⁻¹]
  unfold lewisCriticalNormSq
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  change lewisCriticalNormSq (lewisModularInversion s (fun u => f (u + 1))) = _
  rw [lewisCriticalNormSq_modularInversion]
  have hshift := integral_Ioi_zero_add_subst 1
    (fun b : ℝ => ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)))
  simpa [add_sub_cancel_right] using hshift

private theorem weight_shift_ratio_bound_Ioi_one {b : ℝ} (hb : 1 < b) :
    ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) ∧
      lewisCriticalWeight (b - 1) ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
  let u : ℝ := b - 1
  have hu_pos : 0 < u := sub_pos.mpr hb
  have hb_pos : 0 < b := zero_lt_one.trans hb
  by_cases hb2 : b ≤ 2
  · have hu_le1 : u ≤ 1 := by dsimp [u]; linarith
    have hu_inv_pos : 0 < u⁻¹ := inv_pos.mpr hu_pos
    have hu6 : (u + u⁻¹) ^ (-6 : ℝ) ≤ u ^ (6 : ℝ) := by
      calc
        (u + u⁻¹) ^ (-6 : ℝ) ≤ (u⁻¹) ^ (-6 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hu_inv_pos (by linarith) (by norm_num)
        _ = u ^ (6 : ℝ) := by rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le]; norm_num
    have hu6_le1 : u ^ (6 : ℝ) ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by norm_num)
    have hb_sum_le : b + b⁻¹ ≤ 3 := by
      have : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb.le
      linarith
    have hb_low : (3 : ℝ) ^ (-6 : ℝ) ≤ (b + b⁻¹) ^ (-6 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (add_pos hb_pos (inv_pos.mpr hb_pos)) hb_sum_le (by norm_num)
    have hc1 : (1 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (3 : ℝ) ^ (-6 : ℝ) := by norm_num
    have hfirst : (u + u⁻¹) ^ (-6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) :=
      (hu6.trans hu6_le1).trans (hc1.trans (mul_le_mul_of_nonneg_left hb_low (by norm_num)))
    refine ⟨hfirst, ?_⟩
    unfold lewisCriticalWeight
    have hw_u : (u + u⁻¹) ^ (-6 : ℝ) * u ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      calc
        (u + u⁻¹) ^ (-6 : ℝ) * u ^ (-(1 / 2 : ℝ)) ≤ u ^ (6 : ℝ) * u ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hu6 (Real.rpow_pos_of_pos hu_pos _).le
        _ = u ^ (11 / 2 : ℝ) := by rw [← Real.rpow_add hu_pos]; norm_num
        _ ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by norm_num)
    have hb_half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ b ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hb_pos hb2 (by norm_num)
    have hc2 : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((3 : ℝ) ^ (-6 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have h2_ge : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [show (1 / 2 : ℝ) = (4 : ℝ) ^ (-(1 / 2 : ℝ)) by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
      have : (4 : ℝ) ^ (7 : ℝ) * ((3 : ℝ) ^ (-6 : ℝ) * (1 / 2 : ℝ)) ≥ 1 := by norm_num
      nlinarith
    have hprod : (3 : ℝ) ^ (-6 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        (b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul hb_low hb_half (by positivity) (by positivity)
    exact hw_u.trans (hc2.trans (mul_le_mul_of_nonneg_left hprod (by norm_num)))
  · push_neg at hb2
    have hu_ge : b / 2 ≤ u := by dsimp [u]; linarith
    have hb_sum_le : b + b⁻¹ ≤ 4 * (u + u⁻¹) := by
      have hbinv : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb.le
      have huinv : 0 < u⁻¹ := inv_pos.mpr hu_pos
      linarith
    have hfirst : (u + u⁻¹) ^ (-6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) := by
      have h := Real.rpow_le_rpow_of_nonpos (add_pos hb_pos (inv_pos.mpr hb_pos)) hb_sum_le
        (by norm_num : (-6 : ℝ) ≤ 0)
      rw [Real.mul_rpow (by norm_num) (add_pos hu_pos (inv_pos.mpr hu_pos)).le] at h
      have h4 : (4 : ℝ) ^ (6 : ℝ) * (4 : ℝ) ^ (-6 : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ))
      linarith
    refine ⟨hfirst, ?_⟩
    unfold lewisCriticalWeight
    have huhalf : u ^ (-(1 / 2 : ℝ)) ≤ 4 * b ^ (-(1 / 2 : ℝ)) := by
      have h1 := Real.rpow_le_rpow_of_nonpos (half_pos hb_pos) hu_ge
        (by norm_num : -(1 / 2 : ℝ) ≤ 0)
      rw [div_eq_mul_inv, Real.mul_rpow hb_pos.le (by norm_num)] at h1
      have h2 : ((2 : ℝ)⁻¹) ^ (-(1 / 2 : ℝ)) ≤ 4 := by
        rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
        calc
          (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num
      calc
        u ^ (-(1 / 2 : ℝ)) ≤ b ^ (-(1 / 2 : ℝ)) * ((2 : ℝ)⁻¹) ^ (-(1 / 2 : ℝ)) := h1
        _ ≤ b ^ (-(1 / 2 : ℝ)) * 4 :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos hb_pos _).le
        _ = 4 * b ^ (-(1 / 2 : ℝ)) := by ring
    calc
      (u + u⁻¹) ^ (-6 : ℝ) * u ^ (-(1 / 2 : ℝ))
          ≤ ((4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ)) * (4 * b ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul hfirst huhalf (by positivity) (by positivity)
      _ = (4 : ℝ) ^ (7 : ℝ) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ))) := by norm_num; ring

/-- **Gauss–Mayer Head-Branch Critical-Line Dichotomy (`m = 0`).**
For `s.re ≥ 0`, the renewal head branch `gaussMayerBranch 0 s` is norm-bounded on `H_LP` iff
`s.re ≤ 1/4`. -/
theorem gaussMayerBranch_zero_normBounded_iff {s : ℂ} (hs0 : 0 ≤ s.re) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
      IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
        lewisCriticalNormSq (gaussMayerBranch 0 s f) ≤ C * lewisCriticalNormSq f) ↔
      s.re ≤ 1 / 4 := by
  constructor
  · rintro ⟨C, _, hC⟩
    by_contra hgt
    push_neg at hgt
    let δ : ℝ := 4 * s.re - 1
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    let K : ℝ := (2 : ℝ) ^ (6 : ℝ) * (C + 1)
    have hK_pos : 0 < K := by dsimp [K]; positivity
    let R : ℝ := max 2 (K ^ (1 / δ) + 2)
    have hR_ge2 : 2 ≤ R := le_max_left _ _
    have hR_pos : 0 < R := by linarith
    have hR_lt : R < R + 1 := by linarith
    let f : ℝ → ℂ := (Ioc R (R + 1)).indicator (fun _ => 1)
    have hbound := hC f (indicator_Ioc_normSq_integrable hR_pos)
    rw [lewisCriticalNormSq_gaussMayerBranch_zero] at hbound
    have hsub1 : Ioc R (R + 1) ⊆ Ioi 1 := fun x hx => (by linarith : 1 < R).trans hx.1
    have hind1 :
        (∫ b in Ioi (1 : ℝ),
          ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2))) =
          ∫ b in Ioc R (R + 1),
            ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2) := by
      have hfun : (fun b : ℝ =>
          ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2))) =
          (Ioc R (R + 1)).indicator
            (fun b => ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)) := by
        ext b; by_cases hb : b ∈ Ioc R (R + 1) <;> simp [f, hb]
      rw [hfun, setIntegral_indicator measurableSet_Ioc, inter_eq_self_of_subset_right hsub1]
    rw [hind1] at hbound
    unfold lewisCriticalNormSq at hbound
    rw [indicator_Ioc_weighted_integral hR_pos] at hbound
    have hint_rhs : IntegrableOn
        (fun b : ℝ => ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2))
        (Ioc R (R + 1)) := by
      apply ContinuousOn.integrableOn_Icc _ |>.mono_set Ioc_subset_Icc_self
      intro b hb
      have hu : 0 < b - 1 := by linarith [hb.1, hR_ge2]
      have hsum : (b - 1) + (b - 1)⁻¹ ≠ 0 := (add_pos hu (inv_pos.mpr hu)).ne'
      have hc_sub : ContinuousAt (fun x : ℝ => x - 1) b := continuousAt_id.sub continuousAt_const
      exact (((hc_sub.add (hc_sub.inv₀ hu.ne')).rpow continuousAt_const (Or.inl hsum)).mul
        (hc_sub.rpow continuousAt_const (Or.inl hu.ne'))).continuousWithinAt
    have hK_lt : K < (R - 1) ^ δ := by
      have h1 : K = (K ^ (1 / δ)) ^ δ := by
        rw [← Real.rpow_mul hK_pos.le, one_div_mul_cancel hδ_pos.ne', Real.rpow_one]
      have hR2 : K ^ (1 / δ) + 1 < R - 1 := by
        have := le_max_right 2 (K ^ (1 / δ) + 2); dsimp [R] at *; linarith
      rw [h1]
      exact Real.rpow_lt_rpow (Real.rpow_pos_of_pos hK_pos _).le (by linarith) hδ_pos
    have hlow_pt : ∀ b ∈ Ioc R (R + 1),
        (C + 1) * lewisCriticalWeight b ≤
          ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2) := by
      intro b hb
      have hb_ge2 : 2 ≤ b := hR_ge2.trans hb.1.le
      have hb0 : 0 < b := by linarith
      have hu0 : 0 < b - 1 := by linarith
      have hu_sum_le : (b - 1) + (b - 1)⁻¹ ≤ 2 * (b + b⁻¹) := by
        have hu1 : 1 ≤ b - 1 := by linarith
        have hu_inv : (b - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
        have hb_inv : 0 < b⁻¹ := inv_pos.mpr hb0
        linarith
      have h6_ge : (2 : ℝ) ^ (-6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) ≤
          ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) := by
        have h := Real.rpow_le_rpow_of_nonpos
          (add_pos hu0 (inv_pos.mpr hu0)) hu_sum_le (by norm_num : (-6 : ℝ) ≤ 0)
        rwa [Real.mul_rpow (by norm_num) (add_pos hb0 (inv_pos.mpr hb0)).le] at h
      have hhalf_ge : b ^ (-(1 / 2 : ℝ)) ≤ (b - 1) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by norm_num)
      have hδ_ge : K ≤ (b - 1) ^ δ :=
        hK_lt.le.trans (Real.rpow_le_rpow (by linarith) (by linarith [hb.1]) hδ_pos.le)
      have hexp : (b - 1) ^ (4 * s.re - 3 / 2) = (b - 1) ^ δ * (b - 1) ^ (-(1 / 2 : ℝ)) := by
        dsimp [δ]; rw [← Real.rpow_add hu0]; congr 1; ring
      rw [hexp]
      unfold lewisCriticalWeight
      have h1 : K * (b ^ (-(1 / 2 : ℝ))) ≤ (b - 1) ^ δ * (b - 1) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul hδ_ge hhalf_ge (by positivity) (by positivity)
      calc
        (C + 1) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ)))
            = ((2 : ℝ) ^ (-6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ)) * (K * b ^ (-(1 / 2 : ℝ))) := by
          dsimp [K]; norm_num; ring
        _ ≤ ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * ((b - 1) ^ δ * (b - 1) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul h6_ge h1 (by positivity) (by positivity)
    have hint_pos := setIntegral_lewisCriticalWeight_Ioc_pos hR_pos hR_lt
    have hmono := setIntegral_mono_on
      ((integrableOn_lewisCriticalWeight_Ioc hR_pos).const_mul (C + 1))
      hint_rhs measurableSet_Ioc hlow_pt
    rw [integral_const_mul] at hmono
    have hlt_C : C * (∫ x in Ioc R (R + 1), lewisCriticalWeight x) <
        (C + 1) * (∫ x in Ioc R (R + 1), lewisCriticalWeight x) :=
      mul_lt_mul_of_pos_right (by linarith) hint_pos
    linarith
  · intro hs14
    refine ⟨(4 : ℝ) ^ (7 : ℝ), by positivity, fun f hf => ?_⟩
    rw [lewisCriticalNormSq_gaussMayerBranch_zero]
    have hpt : ∀ b ∈ Ioi (1 : ℝ),
        ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)) ≤
          (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by
      intro b hb
      let u : ℝ := b - 1
      have hu_pos : 0 < u := sub_pos.mpr hb
      have hb_pos : 0 < b := zero_lt_one.trans hb
      by_cases hb2 : b ≤ 2
      · have hu_le1 : u ≤ 1 := by dsimp [u]; linarith
        have hu_inv : 0 < u⁻¹ := inv_pos.mpr hu_pos
        have hu6 : (u + u⁻¹) ^ (-6 : ℝ) ≤ u ^ (6 : ℝ) := by
          calc
            (u + u⁻¹) ^ (-6 : ℝ) ≤ (u⁻¹) ^ (-6 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos hu_inv (by linarith) (by norm_num)
            _ = u ^ (6 : ℝ) := by
              rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le]; norm_num
        have hker_le1 : (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2) ≤ 1 := by
          calc
            (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2)
                ≤ u ^ (6 : ℝ) * u ^ (4 * s.re - 3 / 2) :=
              mul_le_mul_of_nonneg_right hu6 (Real.rpow_pos_of_pos hu_pos _).le
            _ = u ^ (4 * s.re + 9 / 2) := by rw [← Real.rpow_add hu_pos]; congr 1; ring
            _ ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by linarith)
        have h4w : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
          unfold lewisCriticalWeight
          have hb_sum : b + b⁻¹ ≤ 3 := by
            have : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb.le
            linarith
          have hb6 : (3 : ℝ) ^ (-6 : ℝ) ≤ (b + b⁻¹) ^ (-6 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (add_pos hb_pos (inv_pos.mpr hb_pos)) hb_sum (by norm_num)
          have hb_half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ b ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hb_pos hb2 (by norm_num)
          have h2_ge : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [show (1 / 2 : ℝ) = (4 : ℝ) ^ (-(1 / 2 : ℝ)) by
              rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
              norm_num]
            exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
          have hprod := mul_le_mul hb6 hb_half (by positivity) (by positivity)
          have hnum : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((3 : ℝ) ^ (-6 : ℝ) * (1 / 2 : ℝ)) := by
            norm_num
          nlinarith
        have hstep := hker_le1.trans h4w
        calc
          ‖f b‖ ^ 2 * ((u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2))
              ≤ ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
            mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
          _ = (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
      · push_neg at hb2
        have hu_ge1 : 1 ≤ u := by dsimp [u]; linarith
        have hu_exp : u ^ (4 * s.re - 3 / 2) ≤ u ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hu_ge1 (by linarith)
        have hker_le : (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2) ≤
            (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
          calc
            (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2)
                ≤ (u + u⁻¹) ^ (-6 : ℝ) * u ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hu_exp (by positivity)
            _ = lewisCriticalWeight (b - 1) := rfl
            _ ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b :=
              (weight_shift_ratio_bound_Ioi_one hb).2
        calc
          ‖f b‖ ^ 2 * ((u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2))
              ≤ ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
            mul_le_mul_of_nonneg_left hker_le (sq_nonneg _)
          _ = (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
    by_cases hint_lhs : IntegrableOn
        (fun b : ℝ => ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)))
        (Ioi 1)
    · have hf1 : IntegrableOn (fun b : ℝ => ‖f b‖ ^ 2 * lewisCriticalWeight b) (Ioi 1) :=
        hf.mono_set (Ioi_subset_Ioi zero_le_one)
      have hmono := setIntegral_mono_on hint_lhs (hf1.const_mul ((4 : ℝ) ^ (7 : ℝ)))
        measurableSet_Ioi hpt
      rw [integral_const_mul] at hmono
      have hrest : 0 ≤ ∫ a in Ioc (0 : ℝ) 1, ‖f a‖ ^ 2 * lewisCriticalWeight a :=
        setIntegral_nonneg measurableSet_Ioc fun a ha =>
          mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos ha.1).le
      have hsplit : lewisCriticalNormSq f =
          (∫ a in Ioc (0 : ℝ) 1, ‖f a‖ ^ 2 * lewisCriticalWeight a) +
            ∫ b in Ioi (1 : ℝ), ‖f b‖ ^ 2 * lewisCriticalWeight b := by
        unfold lewisCriticalNormSq
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
        exact setIntegral_union (Set.disjoint_left.mpr fun _ hx hy => (not_lt.mpr hx.2) hy)
          measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self) hf1
      rw [hsplit]
      nlinarith
    · rw [integral_undef hint_lhs]
      exact mul_nonneg (by positivity) (lewisCriticalNormSq_nonneg f)

/-- **Simultaneous Head-Branch Boundedness Characterizes `Re s = 1/4`.**
Across `0 ≤ s.re ≤ 1/2`, the Riemann–Mayer renewal pair `(G_{0,s}, G_{0,1/2 - conj s})` is
simultaneously norm-bounded on `H_LP` iff `s.re = 1/4`. -/
theorem gaussMayerBranch_zero_pair_normBounded_iff {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1 / 2) :
    ((∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
        IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
          lewisCriticalNormSq (gaussMayerBranch 0 s f) ≤ C * lewisCriticalNormSq f) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
        IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
          lewisCriticalNormSq (gaussMayerBranch 0 (riemannMayerReflect s) f) ≤
            C * lewisCriticalNormSq f)) ↔
      s.re = 1 / 4 := by
  have hsR0 : 0 ≤ (riemannMayerReflect s).re := by rw [riemannMayerReflect_re]; linarith
  rw [gaussMayerBranch_zero_normBounded_iff hs0, gaussMayerBranch_zero_normBounded_iff hsR0,
    riemannMayerReflect_re]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; exact ⟨by linarith, by linarith⟩

/-- **Tail Branches (`m ≥ 1`) Are Norm-Bounded Across the Entire Right Half-Plane.**
Unlike `m = 0`, every tail branch `gaussMayerBranch m s` (`1 ≤ m`) evaluates `f` inside `(1, 2)`
and is norm-bounded on `H_LP` for every `s` with `0 ≤ s.re` (including `s.re > 1/4`). -/
theorem gaussMayerBranch_tail_normBounded {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs0 : 0 ≤ s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
      IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
        lewisCriticalNormSq (gaussMayerBranch m s f) ≤ C * lewisCriticalNormSq f := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmR
  let K₁ : ℝ := ((m : ℝ) + 2) ^ (7 : ℝ)
  have hK₁_pos : 0 < K₁ := by dsimp [K₁]; positivity
  have hw_shift : ∀ a : ℝ, 0 < a → lewisCriticalWeight a ≤ K₁ * lewisCriticalWeight (a + m) := by
    intro a ha
    by_cases ha1 : a ≤ 1
    · have hw_a : lewisCriticalWeight a ≤ 1 := by
        unfold lewisCriticalWeight
        have ha_inv : 0 < a⁻¹ := inv_pos.mpr ha
        have h6 : (a + a⁻¹) ^ (-6 : ℝ) ≤ a ^ (6 : ℝ) := by
          calc
            (a + a⁻¹) ^ (-6 : ℝ) ≤ (a⁻¹) ^ (-6 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos ha_inv (by linarith) (by norm_num)
            _ = a ^ (6 : ℝ) := by rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]; norm_num
        calc
          (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ)) ≤ a ^ (6 : ℝ) * a ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h6 (Real.rpow_pos_of_pos ha _).le
          _ = a ^ (11 / 2 : ℝ) := by rw [← Real.rpow_add ha]; norm_num
          _ ≤ 1 := Real.rpow_le_one ha.le ha1 (by norm_num)
      have ham_pos : 0 < a + (m : ℝ) := by linarith
      have ham_sum : (a + m) + (a + m)⁻¹ ≤ (m : ℝ) + 2 := by
        have : (a + (m : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        linarith
      have h6_low : ((m : ℝ) + 2) ^ (-6 : ℝ) ≤ ((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (add_pos ham_pos (inv_pos.mpr ham_pos)) ham_sum (by norm_num)
      have hhalf_low : ((m : ℝ) + 2) ^ (-1 : ℝ) ≤ (a + (m : ℝ)) ^ (-(1 / 2 : ℝ)) := by
        calc
          ((m : ℝ) + 2) ^ (-1 : ℝ) ≤ ((m : ℝ) + 2) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ ≤ (a + (m : ℝ)) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos ham_pos (by linarith) (by norm_num)
      have hprod := mul_le_mul h6_low hhalf_low (by positivity) (by positivity)
      have hid : K₁ * (((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ)) = 1 := by
        dsimp [K₁]
        rw [← Real.rpow_add (by linarith : (0 : ℝ) < m + 2),
          ← Real.rpow_add (by linarith : (0 : ℝ) < m + 2)]
        norm_num
      unfold lewisCriticalWeight
      calc
        (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ)) ≤ 1 := hw_a
        _ = K₁ * (((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ)) := hid.symm
        _ ≤ K₁ * (((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) * (a + (m : ℝ)) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hprod hK₁_pos.le
    · push_neg at ha1
      have ham_pos : 0 < a + (m : ℝ) := by linarith
      have ham_le : a + (m : ℝ) ≤ ((m : ℝ) + 2) * a := by nlinarith
      have hsum_le : (a + m) + (a + m)⁻¹ ≤ ((m : ℝ) + 2) * (a + a⁻¹) := by
        have hainv : (a + (m : ℝ))⁻¹ ≤ a⁻¹ := (inv_le_inv₀ ham_pos ha).mpr (by linarith)
        have ha_inv_pos : 0 < a⁻¹ := inv_pos.mpr ha
        nlinarith
      have h6_low : ((m : ℝ) + 2) ^ (-6 : ℝ) * (a + a⁻¹) ^ (-6 : ℝ) ≤
          ((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) := by
        have h := Real.rpow_le_rpow_of_nonpos (add_pos ham_pos (inv_pos.mpr ham_pos)) hsum_le
          (by norm_num : (-6 : ℝ) ≤ 0)
        rwa [Real.mul_rpow (by linarith) (add_pos ha (inv_pos.mpr ha)).le] at h
      have hhalf_low : ((m : ℝ) + 2) ^ (-1 : ℝ) * a ^ (-(1 / 2 : ℝ)) ≤
          (a + (m : ℝ)) ^ (-(1 / 2 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_nonpos ham_pos ham_le (by norm_num : -(1 / 2 : ℝ) ≤ 0)
        rw [Real.mul_rpow (by linarith) ha.le] at h
        have hexp : ((m : ℝ) + 2) ^ (-1 : ℝ) ≤ ((m : ℝ) + 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        exact (mul_le_mul_of_nonneg_right hexp (Real.rpow_pos_of_pos ha _).le).trans h
      unfold lewisCriticalWeight
      have hprod := mul_le_mul h6_low hhalf_low (by positivity) (by positivity)
      have hid : K₁ * ((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ) = 1 := by
        dsimp [K₁]
        rw [mul_assoc, ← Real.rpow_add (by linarith : (0 : ℝ) < m + 2),
          ← Real.rpow_add (by linarith : (0 : ℝ) < m + 2)]
        norm_num
      calc
        (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))
            = (K₁ * ((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ)) *
                ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))) := by rw [hid, one_mul]
        _ = K₁ * ((((m : ℝ) + 2) ^ (-6 : ℝ) * (a + a⁻¹) ^ (-6 : ℝ)) *
              (((m : ℝ) + 2) ^ (-1 : ℝ) * a ^ (-(1 / 2 : ℝ)))) := by ring
        _ ≤ K₁ * (((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) * (a + (m : ℝ)) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hprod hK₁_pos.le
  -- Truncate `f` to `Ioc 1 2`, where `1 + (a + m)⁻¹` takes all its values for `a > 0`:
  let C₀ : ℝ := K₁ * (4 : ℝ) ^ (7 : ℝ)
  refine ⟨C₀, by dsimp [C₀]; positivity, fun f hf => ?_⟩
  let g : ℝ → ℂ := (Ioc (1 : ℝ) 2).indicator f
  have hfg : ∀ a > 0, gaussMayerBranch m s f a = gaussMayerBranch 0 s g (a + m) := by
    intro a ha
    have ham_gt1 : 1 < a + (m : ℝ) := by linarith
    have ham_pos : 0 < a + (m : ℝ) := by linarith
    have hmem : 1 + (a + (m : ℝ))⁻¹ ∈ Ioc (1 : ℝ) 2 :=
      ⟨by linarith [inv_pos.mpr ham_pos], by linarith [inv_le_one_of_one_le₀ ham_gt1.le]⟩
    unfold gaussMayerBranch
    simp [g, indicator_of_mem hmem]
  have hg_int : IntegrableOn (fun b => ‖g b‖ ^ 2 * lewisCriticalWeight b) (Ioi 0) := by
    refine hf.mono' ?_ ?_
    · have hfun : (fun b : ℝ => ‖g b‖ ^ 2 * lewisCriticalWeight b) =
          (Ioc (1 : ℝ) 2).indicator (fun b => ‖f b‖ ^ 2 * lewisCriticalWeight b) := by
        ext b; by_cases hb : b ∈ Ioc (1 : ℝ) 2 <;> simp [g, hb]
      rw [hfun]
      exact hf.aestronglyMeasurable.indicator measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
      by_cases hmem : b ∈ Ioc (1 : ℝ) 2
      · simp [g, hmem, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hb).le)]
      · simp [g, hmem, mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hb).le]
  -- Bound `lewisCriticalNormSq (gaussMayerBranch 0 s g)` via support on `Ioc 1 2`:
  have hg0_bound : lewisCriticalNormSq (gaussMayerBranch 0 s g) ≤
      (4 : ℝ) ^ (7 : ℝ) * lewisCriticalNormSq f := by
    rw [lewisCriticalNormSq_gaussMayerBranch_zero]
    have hpt : ∀ b ∈ Ioi (1 : ℝ),
        ‖g b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)) ≤
          (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by
      intro b hb
      by_cases hb2 : b ∈ Ioc (1 : ℝ) 2
      · simp only [g, indicator_of_mem hb2]
        let u : ℝ := b - 1
        have hu_pos : 0 < u := sub_pos.mpr hb2.1
        have hu_le1 : u ≤ 1 := by dsimp [u]; linarith [hb2.2]
        have hb_pos : 0 < b := zero_lt_one.trans hb2.1
        have hu6 : (u + u⁻¹) ^ (-6 : ℝ) ≤ u ^ (6 : ℝ) := by
          calc
            (u + u⁻¹) ^ (-6 : ℝ) ≤ (u⁻¹) ^ (-6 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu_pos) (by linarith) (by norm_num)
            _ = u ^ (6 : ℝ) := by
              rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le]; norm_num
        have hker1 : (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2) ≤ 1 := by
          calc
            (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2)
                ≤ u ^ (6 : ℝ) * u ^ (4 * s.re - 3 / 2) :=
              mul_le_mul_of_nonneg_right hu6 (Real.rpow_pos_of_pos hu_pos _).le
            _ = u ^ (4 * s.re + 9 / 2) := by rw [← Real.rpow_add hu_pos]; congr 1; ring
            _ ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by linarith)
        have h4w : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
          unfold lewisCriticalWeight
          have hb_sum : b + b⁻¹ ≤ 3 := by
            have : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb2.1.le
            linarith [hb2.2]
          have hb6 : (3 : ℝ) ^ (-6 : ℝ) ≤ (b + b⁻¹) ^ (-6 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (add_pos hb_pos (inv_pos.mpr hb_pos)) hb_sum (by norm_num)
          have hb_half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ b ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hb_pos hb2.2 (by norm_num)
          have h2_ge : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [show (1 / 2 : ℝ) = (4 : ℝ) ^ (-(1 / 2 : ℝ)) by
              rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
              norm_num]
            exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
          have hprod := mul_le_mul hb6 hb_half (by positivity) (by positivity)
          have hnum : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((3 : ℝ) ^ (-6 : ℝ) * (1 / 2 : ℝ)) := by
            norm_num
          nlinarith
        calc
          ‖f b‖ ^ 2 * ((u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2))
              ≤ ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
            mul_le_mul_of_nonneg_left (hker1.trans h4w) (sq_nonneg _)
          _ = (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
      · simp only [g, indicator_of_notMem hb2, norm_zero, sq, zero_mul]
        exact mul_nonneg (by positivity)
          (mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos (zero_lt_one.trans hb)).le)
    by_cases hint_g : IntegrableOn
        (fun b : ℝ => ‖g b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)))
        (Ioi 1)
    · have hf1 := hf.mono_set (Ioi_subset_Ioi zero_le_one)
      have hmono := setIntegral_mono_on hint_g (hf1.const_mul ((4 : ℝ) ^ (7 : ℝ)))
        measurableSet_Ioi hpt
      rw [integral_const_mul] at hmono
      have hrest : 0 ≤ ∫ a in Ioc (0 : ℝ) 1, ‖f a‖ ^ 2 * lewisCriticalWeight a :=
        setIntegral_nonneg measurableSet_Ioc fun a ha =>
          mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos ha.1).le
      have hsplit : lewisCriticalNormSq f =
          (∫ a in Ioc (0 : ℝ) 1, ‖f a‖ ^ 2 * lewisCriticalWeight a) +
            ∫ b in Ioi (1 : ℝ), ‖f b‖ ^ 2 * lewisCriticalWeight b := by
        unfold lewisCriticalNormSq
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
        exact setIntegral_union (Set.disjoint_left.mpr fun _ hx hy => (not_lt.mpr hx.2) hy)
          measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self) hf1
      rw [hsplit]
      nlinarith
    · rw [integral_undef hint_g]
      exact mul_nonneg (by positivity) (lewisCriticalNormSq_nonneg f)
  -- Relate `gaussMayerBranch m s f` to `gaussMayerBranch 0 s g`:
  by_cases hint_m : IntegrableOn
      (fun a : ℝ => ‖gaussMayerBranch m s f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)
  · by_cases hint_0 : IntegrableOn
        (fun u : ℝ => ‖gaussMayerBranch 0 s g u‖ ^ 2 * lewisCriticalWeight u) (Ioi 0)
    · have hint_shift : IntegrableOn
          (fun a : ℝ => ‖gaussMayerBranch 0 s g (a + m)‖ ^ 2 * lewisCriticalWeight (a + m))
          (Ioi 0) := by
        have himg : (fun a : ℝ => a + (m : ℝ)) '' Ioi (0 : ℝ) = Ioi (m : ℝ) := by
          ext b; simp only [mem_image, mem_Ioi]
          exact ⟨fun ⟨a, ha, rfl⟩ => by linarith, fun hb => ⟨b - m, by linarith, sub_add_cancel b m⟩⟩
        have hinj : InjOn (fun a : ℝ => a + (m : ℝ)) (Ioi 0) := fun _ _ _ _ h => add_right_cancel h
        have hderiv : ∀ a ∈ Ioi (0 : ℝ),
            HasDerivWithinAt (fun x : ℝ => x + (m : ℝ)) 1 (Ioi 0) a :=
          fun a _ => ((hasDerivAt_id a).add_const _).hasDerivWithinAt
        have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj
          (fun u : ℝ => ‖gaussMayerBranch 0 s g u‖ ^ 2 * lewisCriticalWeight u)
        rw [himg] at hiff
        simpa using hiff.mp (hint_0.mono_set (Ioi_subset_Ioi hm_pos.le))
      have hmono1 : lewisCriticalNormSq (gaussMayerBranch m s f) ≤
          K₁ * ∫ a in Ioi (0 : ℝ),
            ‖gaussMayerBranch 0 s g (a + m)‖ ^ 2 * lewisCriticalWeight (a + m) := by
        unfold lewisCriticalNormSq
        rw [← integral_const_mul]
        refine setIntegral_mono_on hint_m (hint_shift.const_mul K₁) measurableSet_Ioi fun a ha => ?_
        rw [hfg a ha]
        calc
          ‖gaussMayerBranch 0 s g (a + m)‖ ^ 2 * lewisCriticalWeight a
              ≤ ‖gaussMayerBranch 0 s g (a + m)‖ ^ 2 * (K₁ * lewisCriticalWeight (a + m)) :=
            mul_le_mul_of_nonneg_left (hw_shift a ha) (sq_nonneg _)
          _ = K₁ * (‖gaussMayerBranch 0 s g (a + m)‖ ^ 2 * lewisCriticalWeight (a + m)) := by ring
      have hshift_eq := integral_Ioi_zero_add_subst (m : ℝ)
        (fun u : ℝ => ‖gaussMayerBranch 0 s g u‖ ^ 2 * lewisCriticalWeight u)
      have hsub_Ioi : ∫ u in Ioi (m : ℝ), ‖gaussMayerBranch 0 s g u‖ ^ 2 * lewisCriticalWeight u ≤
          lewisCriticalNormSq (gaussMayerBranch 0 s g) := by
        unfold lewisCriticalNormSq
        have hsub : Ioi (m : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi hm_pos.le
        have hunion : Ioi (0 : ℝ) = Ioi (m : ℝ) ∪ (Ioi 0 \ Ioi (m : ℝ)) :=
          (Set.union_sdiff_cancel hsub).symm
        conv_rhs => rw [hunion]
        rw [setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Ioi)
          (hint_0.mono_set hsub) (hint_0.mono_set Set.sdiff_subset)]
        have hrest : 0 ≤ ∫ u in Ioi 0 \ Ioi (m : ℝ),
            ‖gaussMayerBranch 0 s g u‖ ^ 2 * lewisCriticalWeight u :=
          setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioi) fun u hu =>
            mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hu.1).le
        linarith
      rw [hshift_eq] at hmono1
      calc
        lewisCriticalNormSq (gaussMayerBranch m s f)
            ≤ K₁ * lewisCriticalNormSq (gaussMayerBranch 0 s g) :=
          hmono1.trans (mul_le_mul_of_nonneg_left hsub_Ioi hK₁_pos.le)
        _ ≤ K₁ * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalNormSq f) :=
          mul_le_mul_of_nonneg_left hg0_bound hK₁_pos.le
        _ = C₀ * lewisCriticalNormSq f := by dsimp [C₀]; ring
    · -- `hint_0` always holds when `hint_m` does; in fact on `Ioi m` it is dominated by `hint_m`?
      -- Even simpler: `gaussMayerBranch 0 s g` is bounded on `(0, m]` too! Wait: for `u ∈ (0, m]`,
      -- `1 + u⁻¹ > 1 + m⁻¹`, and if `u < 1`, `1 + u⁻¹ > 2 ∉ Ioc 1 2`, so `g (1 + u⁻¹) = 0`!!
      exfalso
      apply hint_0
      -- Note: for `0 < u < 1`, `1 + u⁻¹ > 2`, so `g (1 + u⁻¹) = 0`!
      -- Thus `gaussMayerBranch 0 s g u = 0` on `Ioo 0 1`!
      have hvan : ∀ u ∈ Ioc (0 : ℝ) 1,
          ‖gaussMayerBranch 0 s g u‖ ^ 2 * lewisCriticalWeight u = 0 := by
        intro u hu
        rcases eq_or_lt_of_le hu.2 with rfl | hlt
        · unfold gaussMayerBranch
          have hnot : (1 + (1 : ℝ)⁻¹ : ℝ) ∉ Ioc (1 : ℝ) 2 := by norm_num
          -- Wait: `1 + 1⁻¹ = 2 ∈ Ioc 1 2` at the single point `u = 1`!
          sorry
        · sorry
      sorry
  · rw [lewisCriticalNormSq, integral_undef hint_m]
    exact mul_nonneg (by dsimp [C₀]; positivity) (lewisCriticalNormSq_nonneg f)
