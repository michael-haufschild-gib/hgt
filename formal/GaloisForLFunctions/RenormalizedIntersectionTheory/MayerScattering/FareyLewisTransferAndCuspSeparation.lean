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
   In period coordinates on `(0, ∞)`, every tail branch
   `(G_{m,s} f)(a) = (a + m)^(-2s) f(1 + (a + m)⁻¹)` (`m ≥ 1`) is norm-bounded on `H_LP` across
   `s.re ≥ 0`, whereas the head branch `G_{0,s} = I_s U_1` (`s.re ≥ 0`) is norm-bounded on `H_LP`
   iff `s.re ≤ 1/4`; consequently the Riemann–Mayer pair `(G_{0,s}, G_{0,1/2 - conj s})` is
   simultaneously bounded on `H_LP` (`0 ≤ s.re ≤ 1/2`) iff `s.re = 1/4`.
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
  · exact (lewisCriticalWeight_continuousOn.mono
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
  · rintro ⟨C, _, hC⟩
    by_contra hne
    let K : ℝ := C + 1
    have hK_pos : 0 < K := by dsimp [K]; linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let γ : ℝ := 1 - 4 * s.re
      have hγ_pos : 0 < γ := by dsimp [γ]; linarith
      let R : ℝ := K ^ (1 / γ) + 1
      have hR_gt1 : 1 < R := by
        dsimp [R]; linarith [Real.rpow_pos_of_pos hK_pos (1 / γ)]
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
      have hK_lt_Rγ : K < R ^ γ := by
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
          have h1 : R ^ γ ≤ (b⁻¹) ^ γ := Real.rpow_le_rpow hR_pos.le hbinv_ge hγ_pos.le
          have h2 : (b⁻¹) ^ γ = b ^ (4 * s.re - 1) := by
            rw [Real.inv_rpow hb0.le, ← Real.rpow_neg hb0.le]
            congr 1; dsimp [γ]; ring
          linarith [hK_lt_Rγ, h1, h2]
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
      have hR_pos : 0 < R := by dsimp [R]; linarith [Real.rpow_pos_of_pos hK_pos (1 / δ)]
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

private theorem two_neg_half_ge_half : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h4 : (1 / 2 : ℝ) = (4 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h4]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)

private theorem weight_shift_ratio_bound_Ioi_one {b : ℝ} (hb : 1 < b) :
    ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) ∧
      lewisCriticalWeight (b - 1) ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
  let u : ℝ := b - 1
  have hu_pos : 0 < u := sub_pos.mpr hb
  have hb_pos : 0 < b := zero_lt_one.trans hb
  by_cases hb2 : b ≤ 2
  · have hu_le1 : u ≤ 1 := by dsimp [u]; linarith
    have hu6 : (u + u⁻¹) ^ (-6 : ℝ) ≤ u ^ (6 : ℝ) := by
      calc
        (u + u⁻¹) ^ (-6 : ℝ) ≤ (u⁻¹) ^ (-6 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu_pos) (by linarith) (by norm_num)
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
    have hprod := mul_le_mul hb_low (two_neg_half_ge_half.trans hb_half) (by positivity) (by positivity)
    have hnum : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((3 : ℝ) ^ (-6 : ℝ) * (1 / 2 : ℝ)) := by norm_num
    have hc2 : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ))) :=
      hnum.trans (mul_le_mul_of_nonneg_left hprod (by norm_num))
    exact hw_u.trans hc2
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

private theorem one_le_four_pow_seven_mul_weight_Ioc_two {b : ℝ} (hb1 : 1 < b) (hb2 : b ≤ 2) :
    (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
  have hb_pos : 0 < b := zero_lt_one.trans hb1
  unfold lewisCriticalWeight
  have hb_sum : b + b⁻¹ ≤ 3 := by
    have : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1.le
    linarith
  have hb6 : (3 : ℝ) ^ (-6 : ℝ) ≤ (b + b⁻¹) ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (add_pos hb_pos (inv_pos.mpr hb_pos)) hb_sum (by norm_num)
  have hb_half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ b ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hb_pos hb2 (by norm_num)
  have hprod := mul_le_mul hb6 (two_neg_half_ge_half.trans hb_half) (by positivity) (by positivity)
  have hnum : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((3 : ℝ) ^ (-6 : ℝ) * (1 / 2 : ℝ)) := by norm_num
  exact hnum.trans (mul_le_mul_of_nonneg_left hprod (by norm_num))

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
        have hu_inv : (b - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
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
      have h1 : K * b ^ (-(1 / 2 : ℝ)) ≤ (b - 1) ^ δ * (b - 1) ^ (-(1 / 2 : ℝ)) :=
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
      by_cases hb2 : b ≤ 2
      · have hu_le1 : u ≤ 1 := by dsimp [u]; linarith
        have hu6 : (u + u⁻¹) ^ (-6 : ℝ) ≤ u ^ (6 : ℝ) := by
          calc
            (u + u⁻¹) ^ (-6 : ℝ) ≤ (u⁻¹) ^ (-6 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu_pos) (by linarith) (by norm_num)
            _ = u ^ (6 : ℝ) := by
              rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le]; norm_num
        have hker_le1 : (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2) ≤ 1 := by
          calc
            (u + u⁻¹) ^ (-6 : ℝ) * u ^ (4 * s.re - 3 / 2)
                ≤ u ^ (6 : ℝ) * u ^ (4 * s.re - 3 / 2) :=
              mul_le_mul_of_nonneg_right hu6 (Real.rpow_pos_of_pos hu_pos _).le
            _ = u ^ (4 * s.re + 9 / 2) := by rw [← Real.rpow_add hu_pos]; congr 1; ring
            _ ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by linarith)
        have hstep := hker_le1.trans (one_le_four_pow_seven_mul_weight_Ioc_two hb hb2)
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
    · have hf1 := hf.mono_set (Ioi_subset_Ioi zero_le_one)
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

/-- **Simultaneous Head-Branch Boundedness Characterizes `Re s = 1/4`.** -/
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

/-- **Tail Branches (`m ≥ 1`) Are Norm-Bounded Across `s.re ≥ 0`.** -/
theorem gaussMayerBranch_tail_normBounded {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs0 : 0 ≤ s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
      IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
        lewisCriticalNormSq (gaussMayerBranch m s f) ≤ C * lewisCriticalNormSq f := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmR
  let K₁ : ℝ := ((m : ℝ) + 2) ^ (7 : ℝ)
  have hK₁_pos : 0 < K₁ := by dsimp [K₁]; positivity
  let C₀ : ℝ := K₁ * (4 : ℝ) ^ (7 : ℝ)
  refine ⟨C₀, by dsimp [C₀]; positivity, fun f hf => ?_⟩
  by_cases hint_m : IntegrableOn
      (fun a : ℝ => ‖gaussMayerBranch m s f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)
  · let S : Set ℝ := Ioo (1 : ℝ) (1 + (m : ℝ)⁻¹)
    let ψ : ℝ → ℝ := fun b => (b - 1)⁻¹ - (m : ℝ)
    have hψ_img : ψ '' S = Ioi (0 : ℝ) := by
      ext a
      simp only [S, ψ, mem_image, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
        have hu_pos : 0 < b - 1 := sub_pos.mpr hb1
        have hu_lt : b - 1 < (m : ℝ)⁻¹ := by linarith
        have hgt : (m : ℝ) < (b - 1)⁻¹ := by
          have := (inv_lt_inv₀ (inv_pos.mpr hm_pos) hu_pos).mpr hu_lt
          simpa using this
        linarith
      · intro ha
        have ham_pos : 0 < a + (m : ℝ) := by linarith
        refine ⟨1 + (a + (m : ℝ))⁻¹, ⟨by linarith [inv_pos.mpr ham_pos], ?_⟩, ?_⟩
        · have : (a + (m : ℝ))⁻¹ < (m : ℝ)⁻¹ := (inv_lt_inv₀ ham_pos hm_pos).mpr (by linarith)
          linarith
        · simp [add_sub_cancel_left]
    have hψ_inj : InjOn ψ S := by
      intro b₁ hb₁ b₂ hb₂ heq
      dsimp [ψ] at heq
      have hinv : (b₁ - 1)⁻¹ = (b₂ - 1)⁻¹ := by linarith
      have hsub := inv_injective hinv
      linarith
    have hψ_deriv : ∀ b ∈ S, HasDerivWithinAt ψ (-((b - 1) ^ 2)⁻¹) S b := by
      intro b hb
      have hu : b - 1 ≠ 0 := (sub_pos.mpr hb.1).ne'
      have hd1 : HasDerivAt (fun x : ℝ => x - 1) 1 b := (hasDerivAt_id b).sub_const 1
      have hd2 : HasDerivAt (fun x : ℝ => (x - 1)⁻¹ - (m : ℝ)) (-((b - 1) ^ 2)⁻¹ * 1) b :=
        (hd1.inv_fun).sub_const (m : ℝ)
      rw [mul_one] at hd2
      exact hd2.hasDerivWithinAt
    let G : ℝ → ℝ := fun a => ‖gaussMayerBranch m s f a‖ ^ 2 * lewisCriticalWeight a
    have hint_S : IntegrableOn (fun b => |-((b - 1) ^ 2)⁻¹| • G (ψ b)) S := by
      have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hψ_deriv
        hψ_inj G
      rw [hψ_img] at hiff
      exact hiff.mp hint_m
    have heq_int : lewisCriticalNormSq (gaussMayerBranch m s f) =
        ∫ b in S, |-((b - 1) ^ 2)⁻¹| • G (ψ b) := by
      unfold lewisCriticalNormSq
      have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hψ_deriv hψ_inj G
      rw [hψ_img] at h
      exact h
    rw [heq_int]
    have hS_sub : S ⊆ Ioi 0 := fun b hb => zero_lt_one.trans hb.1
    have hf_S : IntegrableOn (fun b => C₀ * (‖f b‖ ^ 2 * lewisCriticalWeight b)) S :=
      (hf.mono_set hS_sub).const_mul C₀
    have hpt : ∀ b ∈ S,
        |-((b - 1) ^ 2)⁻¹| • G (ψ b) ≤ C₀ * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by
      intro b hb
      have hu_pos : 0 < b - 1 := sub_pos.mpr hb.1
      have ha_pos : 0 < ψ b := by
        rw [← mem_Ioi, ← hψ_img]; exact ⟨b, hb, rfl⟩
      have ham_eq : ψ b + (m : ℝ) = (b - 1)⁻¹ := by dsimp [ψ]; ring
      have hb_arg : 1 + (ψ b + (m : ℝ))⁻¹ = b := by rw [ham_eq, inv_inv]; ring
      have hgm : ‖gaussMayerBranch m s f (ψ b)‖ ^ 2 = (b - 1) ^ (4 * s.re) * ‖f b‖ ^ 2 := by
        unfold gaussMayerBranch
        rw [ham_eq, hb_arg, norm_mul, mul_pow,
          Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hu_pos)]
        have hre : (-(2 * s)).re = -2 * s.re := by simp
        rw [hre, Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le, ← Real.rpow_natCast,
          ← Real.rpow_mul hu_pos.le]
        congr 2; push_cast; ring
      -- Bound `lewisCriticalWeight (ψ b)` by `K₁ * lewisCriticalWeight ((b - 1)⁻¹)`:
      have hw_ψ : lewisCriticalWeight (ψ b) ≤ K₁ * lewisCriticalWeight (b - 1)⁻¹ := by
        let a := ψ b
        have ha : 0 < a := ha_pos
        rw [← ham_eq]
        by_cases ha1 : a ≤ 1
        · have hw_a : lewisCriticalWeight a ≤ 1 := by
            unfold lewisCriticalWeight
            have h6 : (a + a⁻¹) ^ (-6 : ℝ) ≤ a ^ (6 : ℝ) := by
              calc
                (a + a⁻¹) ^ (-6 : ℝ) ≤ (a⁻¹) ^ (-6 : ℝ) :=
                  Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ha) (by linarith) (by norm_num)
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
          have hhalf_low : ((m : ℝ) + 2) ^ (-1 : ℝ) ≤ (a + (m : ℝ)) ^ (-(1 / 2 : ℝ)) :=
            (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans
              (Real.rpow_le_rpow_of_nonpos ham_pos (by linarith) (by norm_num))
          have hprod := mul_le_mul h6_low hhalf_low (by positivity) (by positivity)
          have hid : K₁ * (((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ)) = 1 := by
            dsimp [K₁]
            rw [← Real.rpow_add (by linarith : (0 : ℝ) < m + 2),
              ← Real.rpow_add (by linarith : (0 : ℝ) < m + 2)]
            norm_num
          unfold lewisCriticalWeight
          exact hw_a.trans (hid.symm.trans (mul_le_mul_of_nonneg_left hprod hK₁_pos.le))
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
            exact (mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
              (Real.rpow_pos_of_pos ha _).le).trans h
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
      have habs : |-((b - 1) ^ 2)⁻¹| = (b - 1) ^ (-2 : ℝ) := by
        rw [abs_neg, abs_of_pos (by positivity), Real.rpow_neg hu_pos.le, Real.rpow_two]
      have hw_inv : (b - 1) ^ (-2 : ℝ) * lewisCriticalWeight (b - 1)⁻¹ =
          (b - 1) ^ (-1 : ℝ) * lewisCriticalWeight (b - 1) := by
        unfold lewisCriticalWeight
        rw [inv_inv, add_comm (b - 1)⁻¹ (b - 1), Real.inv_rpow hu_pos.le,
          ← Real.rpow_neg hu_pos.le, neg_neg]
        have h1 : (b - 1) ^ (-2 : ℝ) *
            (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (1 / 2 : ℝ)) =
            ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) *
              ((b - 1) ^ (-2 : ℝ) * (b - 1) ^ (1 / 2 : ℝ)) := by ring
        have h2 : (b - 1) ^ (-1 : ℝ) *
            (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ))) =
            ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) *
              ((b - 1) ^ (-1 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ))) := by ring
        rw [h1, h2, ← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]
        congr 2; norm_num
      have hu_le1 : b - 1 ≤ 1 := by
        have : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hmR
        linarith [hb.2]
      have hb_le2 : b ≤ 2 := by linarith
      have hu_ker1 : (b - 1) ^ (4 * s.re) * ((b - 1) ^ (-1 : ℝ) * lewisCriticalWeight (b - 1)) ≤ 1 := by
        unfold lewisCriticalWeight
        have hu6 : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (b - 1) ^ (6 : ℝ) := by
          calc
            ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ ((b - 1)⁻¹) ^ (-6 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu_pos) (by linarith) (by norm_num)
            _ = (b - 1) ^ (6 : ℝ) := by
              rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le]; norm_num
        calc
          (b - 1) ^ (4 * s.re) *
              ((b - 1) ^ (-1 : ℝ) * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ))))
              ≤ (b - 1) ^ (4 * s.re) *
                  ((b - 1) ^ (-1 : ℝ) * ((b - 1) ^ (6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hu6 (by positivity)
          _ = (b - 1) ^ (4 * s.re) * (b - 1) ^ (-1 : ℝ) * (b - 1) ^ (6 : ℝ) *
                (b - 1) ^ (-(1 / 2 : ℝ)) := by ring
          _ = (b - 1) ^ (4 * s.re + 9 / 2) := by
            rw [← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]
            congr 1; ring
          _ ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by linarith)
      have h4w := one_le_four_pow_seven_mul_weight_Ioc_two hb.1 hb_le2
      dsimp only [smul_eq_mul, G]
      rw [habs, hgm]
      calc
        (b - 1) ^ (-2 : ℝ) * (((b - 1) ^ (4 * s.re) * ‖f b‖ ^ 2) * lewisCriticalWeight (ψ b))
            ≤ (b - 1) ^ (-2 : ℝ) *
                (((b - 1) ^ (4 * s.re) * ‖f b‖ ^ 2) * (K₁ * lewisCriticalWeight (b - 1)⁻¹)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hw_ψ (by positivity)
        _ = K₁ * ‖f b‖ ^ 2 * ((b - 1) ^ (4 * s.re) *
              ((b - 1) ^ (-2 : ℝ) * lewisCriticalWeight (b - 1)⁻¹)) := by ring
        _ = K₁ * ‖f b‖ ^ 2 * ((b - 1) ^ (4 * s.re) *
              ((b - 1) ^ (-1 : ℝ) * lewisCriticalWeight (b - 1))) := by rw [hw_inv]
        _ ≤ K₁ * ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
          mul_le_mul_of_nonneg_left (hu_ker1.trans h4w) (by positivity)
        _ = C₀ * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by dsimp [C₀]; ring
    have hmono := setIntegral_mono_on hint_S hf_S measurableSet_Ioo hpt
    rw [integral_const_mul] at hmono
    have hsub_le : ∫ b in S, ‖f b‖ ^ 2 * lewisCriticalWeight b ≤ lewisCriticalNormSq f := by
      unfold lewisCriticalNormSq
      have hunion : Ioi (0 : ℝ) = S ∪ (Ioi 0 \ S) := (Set.union_sdiff_cancel hS_sub).symm
      conv_rhs => rw [hunion]
      rw [setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Ioo)
        (hf.mono_set hS_sub) (hf.mono_set Set.sdiff_subset)]
      have hrest : 0 ≤ ∫ b in Ioi 0 \ S, ‖f b‖ ^ 2 * lewisCriticalWeight b :=
        setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioo) fun b hb =>
          mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hb.1).le
      linarith
    exact hmono.trans (mul_le_mul_of_nonneg_left hsub_le (by dsimp [C₀]; positivity))
  · rw [lewisCriticalNormSq, integral_undef hint_m]
    exact mul_nonneg (by dsimp [C₀]; positivity) (lewisCriticalNormSq_nonneg f)

/-! ## Part 3: Farey–Lewis three-term operator `M_s = U_1 + V_s`, Koopman adjoints, and self-commutator -/

/-- Translation branch `(U_1 f)(a) = f(a + 1)` on `(0, ∞)`. -/
def lewisShift (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  f (a + 1)

/-- Parabolic Farey branch `(V_s f)(a) = (a + 1)^(-2s) f(a / (a + 1))` on `(0, ∞)`. -/
def lewisParabolic (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * f (a / (a + 1))

/-- Homogeneous Farey–Lewis three-term operator `M_s = U_1 + V_s` on `(0, ∞)`. -/
def lewisFarey (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  lewisShift f a + lewisParabolic s f a

/-- Formal `H_LP`-adjoint of `lewisShift`, supported on `(1, ∞)`. -/
def lewisShiftAdj (g : ℝ → ℂ) (b : ℝ) : ℂ :=
  if 1 < b then ((lewisCriticalWeight (b - 1) / lewisCriticalWeight b : ℝ) : ℂ) * g (b - 1) else 0

/-- Formal `H_LP`-adjoint of `lewisParabolic s`, supported on `(0, 1)`. -/
def lewisParabolicAdj (s : ℂ) (g : ℝ → ℂ) (c : ℝ) : ℂ :=
  if c ∈ Ioo (0 : ℝ) 1 then
    ((1 - c : ℝ) : ℂ) ^ (2 * (starRingEnd ℂ) s - 2) *
      ((lewisCriticalWeight (c / (1 - c)) / lewisCriticalWeight c : ℝ) : ℂ) * g (c / (1 - c))
  else 0

/-- Single-valued weighted Koopman adjoint `M_s† = U_1† + V_s†` of the Farey map. -/
def lewisFareyAdj (s : ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  lewisShiftAdj g x + lewisParabolicAdj s g x

/-- Diagonal multiplier `μ_s(a)` of `M_s M_s†` on `(0, ∞)`. -/
def lewisFareyMultiplier (s : ℂ) (a : ℝ) : ℝ :=
  lewisCriticalWeight a / lewisCriticalWeight (a + 1) +
    (a + 1) ^ (2 - 4 * s.re) * (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1)))

/-- Möbius change of variables `c = a / (a + 1)` mapping `(0, ∞)` onto `(0, 1)`. -/
theorem integral_Ioi_zero_mobius_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) :
    (∫ c in Ioo (0 : ℝ) 1, h c) = ∫ a in Ioi (0 : ℝ), ((a + 1) ^ (-2 : ℝ)) • h (a / (a + 1)) := by
  let φ : ℝ → ℝ := fun a => a / (a + 1)
  have himg : φ '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
    ext c
    simp only [φ, mem_image, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨div_pos ha (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
    · rintro ⟨hc0, hc1⟩
      have h1c : 0 < 1 - c := sub_pos.mpr hc1
      refine ⟨c / (1 - c), div_pos hc0 h1c, ?_⟩
      field_simp [h1c.ne']
      ring
  have hinj : InjOn φ (Ioi 0) := by
    intro a₁ ha₁ a₂ ha₂ heq
    dsimp [φ] at heq
    have h1 : a₁ + 1 ≠ 0 := by linarith [show 0 < a₁ from ha₁]
    have h2 : a₂ + 1 ≠ 0 := by linarith [show 0 < a₂ from ha₂]
    rw [div_eq_div_iff h1 h2] at heq
    linarith
  have hderiv : ∀ a ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (((a + 1) ^ 2)⁻¹) (Ioi 0) a := by
    intro a ha
    have ha1 : a + 1 ≠ 0 := by linarith [show 0 < a from ha]
    have hd := (hasDerivAt_id a).div ((hasDerivAt_id a).add_const 1) ha1
    have hval : (1 * (a + 1) - a * (1 + 0)) / (a + 1) ^ 2 = ((a + 1) ^ 2)⁻¹ := by
      field_simp [ha1]; ring
    exact (hval ▸ hd).hasDerivWithinAt
  have hint := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj h
  rw [himg] at hint
  rw [hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
  have ha1 : 0 < a + 1 := by linarith [show 0 < a from ha]
  have habs : |((a + 1) ^ 2)⁻¹| = (a + 1) ^ (-2 : ℝ) := by
    rw [abs_of_pos (by positivity), Real.rpow_neg ha1.le, Real.rpow_two]
  change |((a + 1) ^ 2)⁻¹| • h (a / (a + 1)) = ((a + 1) ^ (-2 : ℝ)) • h (a / (a + 1))
  rw [habs]

/-- Formal `H_LP`-adjointness `⟨U_1 f, g⟩_LP = ⟨f, U_1† g⟩_LP`. -/
theorem lewisCriticalInner_shift_adj (f g : ℝ → ℂ) :
    lewisCriticalInner (lewisShift f) g = lewisCriticalInner f (lewisShiftAdj g) := by
  unfold lewisCriticalInner lewisShift
  have hshift := integral_Ioi_zero_add_subst 1
    (fun b : ℝ => f b * (starRingEnd ℂ) (g (b - 1)) * (lewisCriticalWeight (b - 1) : ℂ))
  have hlhs : (∫ a in Ioi (0 : ℝ), f (a + 1) * (starRingEnd ℂ) (g a) * (lewisCriticalWeight a : ℂ)) =
      ∫ b in Ioi (1 : ℝ), f b * (starRingEnd ℂ) (g (b - 1)) * (lewisCriticalWeight (b - 1) : ℂ) := by
    simpa [add_sub_cancel_right] using hshift
  rw [hlhs]
  have hrhs_ind : (fun b : ℝ => f b * (starRingEnd ℂ) (lewisShiftAdj g b) * (lewisCriticalWeight b : ℂ)) =
      (Ioi (1 : ℝ)).indicator
        (fun b => f b * (starRingEnd ℂ) (g (b - 1)) * (lewisCriticalWeight (b - 1) : ℂ)) := by
    ext b
    by_cases hb : 1 < b
    · have hb0 : 0 < b := zero_lt_one.trans hb
      have hwb : (lewisCriticalWeight b : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (lewisCriticalWeight_pos hb0).ne'
      simp only [lewisShiftAdj, if_pos hb, mem_Ioi, indicator_of_mem hb, map_mul,
        Complex.conj_ofReal, Complex.ofReal_div]
      field_simp [hwb]
    · simp [lewisShiftAdj, hb, mem_Ioi]
  rw [hrhs_ind, setIntegral_indicator measurableSet_Ioi,
    inter_eq_self_of_subset_right (Ioi_subset_Ioi zero_le_one)]

/-- Formal `H_LP`-adjointness `⟨V_s f, g⟩_LP = ⟨f, V_s† g⟩_LP`. -/
theorem lewisCriticalInner_parabolic_adj (s : ℂ) (f g : ℝ → ℂ) :
    lewisCriticalInner (lewisParabolic s f) g = lewisCriticalInner f (lewisParabolicAdj s g) := by
  unfold lewisCriticalInner
  have hrhs_ind :
      (fun c : ℝ => f c * (starRingEnd ℂ) (lewisParabolicAdj s g c) * (lewisCriticalWeight c : ℂ)) =
      (Ioo (0 : ℝ) 1).indicator (fun c =>
        f c * (starRingEnd ℂ)
          (((1 - c : ℝ) : ℂ) ^ (2 * (starRingEnd ℂ) s - 2) *
            ((lewisCriticalWeight (c / (1 - c)) / lewisCriticalWeight c : ℝ) : ℂ) *
            g (c / (1 - c))) * (lewisCriticalWeight c : ℂ)) := by
    ext c
    by_cases hc : c ∈ Ioo (0 : ℝ) 1
    · simp [lewisParabolicAdj, hc]
    · simp [lewisParabolicAdj, hc]
  rw [hrhs_ind, setIntegral_indicator measurableSet_Ioo,
    inter_eq_self_of_subset_right Ioo_subset_Ioi_self, integral_Ioi_zero_mobius_subst]
  refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
  have ha0 : 0 < a := ha
  have ha1 : 0 < a + 1 := by linarith
  have ha1C : ((a + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha1.ne'
  let c : ℝ := a / (a + 1)
  have hc0 : 0 < c := div_pos ha0 ha1
  have h1c_eq : 1 - c = (a + 1)⁻¹ := by dsimp [c]; field_simp [ha1.ne']; ring
  have hc_div : c / (1 - c) = a := by dsimp [c]; rw [h1c_eq]; field_simp [ha1.ne']
  have hwc_ne : (lewisCriticalWeight c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lewisCriticalWeight_pos hc0).ne'
  have hconj_pow :
      (starRingEnd ℂ) (((1 - c : ℝ) : ℂ) ^ (2 * (starRingEnd ℂ) s - 2)) =
        ((a + 1 : ℝ) : ℂ) ^ (2 - 2 * s) := by
    rw [h1c_eq, ofReal_inv_cpow_pos ha1]
    have hconj_base : (starRingEnd ℂ) (((a + 1 : ℝ) : ℂ) ^ (-(2 * (starRingEnd ℂ) s - 2))) =
        ((a + 1 : ℝ) : ℂ) ^ ((starRingEnd ℂ) (-(2 * (starRingEnd ℂ) s - 2))) := by
      rw [Complex.cpow_def_of_ne_zero ha1C, Complex.cpow_def_of_ne_zero ha1C,
        ← Complex.ofReal_log ha1.le, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
    rw [hconj_base]
    congr 1
    simp only [map_neg, map_sub, map_mul, map_ofNat, Complex.conj_conj]
    ring
  have hjac_pow : (((a + 1) ^ (-2 : ℝ) : ℝ) : ℂ) * ((a + 1 : ℝ) : ℂ) ^ (2 - 2 * s) =
      ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) := by
    have hcast : (((a + 1) ^ (-2 : ℝ) : ℝ) : ℂ) = ((a + 1 : ℝ) : ℂ) ^ (-2 : ℂ) := by
      simpa using Complex.ofReal_cpow ha1.le (-2 : ℝ)
    rw [hcast, ← Complex.cpow_add _ _ ha1C]
    congr 1; ring
  dsimp only [lewisParabolic]
  rw [Complex.real_smul, map_mul, map_mul, hconj_pow, Complex.conj_ofReal, hc_div,
    Complex.ofReal_div]
  have hcancel : ((lewisCriticalWeight a : ℂ) / (lewisCriticalWeight c : ℂ)) *
      (lewisCriticalWeight c : ℂ) = (lewisCriticalWeight a : ℂ) := div_mul_cancel₀ _ hwc_ne
  calc
    ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * f c * (starRingEnd ℂ) (g a) * (lewisCriticalWeight a : ℂ)
        = ((((a + 1) ^ (-2 : ℝ) : ℝ) : ℂ) * ((a + 1 : ℝ) : ℂ) ^ (2 - 2 * s)) *
            f c * (starRingEnd ℂ) (g a) *
            (((lewisCriticalWeight a : ℂ) / (lewisCriticalWeight c : ℂ)) *
              (lewisCriticalWeight c : ℂ)) := by rw [hjac_pow, hcancel]
    _ = (((a + 1) ^ (-2 : ℝ) : ℝ) : ℂ) *
          (f c * (((a + 1 : ℝ) : ℂ) ^ (2 - 2 * s) *
            ((lewisCriticalWeight a : ℂ) / (lewisCriticalWeight c : ℂ)) *
            (starRingEnd ℂ) (g a)) * (lewisCriticalWeight c : ℂ)) := by ring

/-- Exact cross-branch annihilation `U_1 (V_s† g) = 0` on `(0, ∞)`. -/
theorem lewisShift_comp_parabolicAdj (s : ℂ) (g : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    lewisShift (lewisParabolicAdj s g) a = 0 := by
  unfold lewisShift lewisParabolicAdj
  have hnot : a + 1 ∉ Ioo (0 : ℝ) 1 := fun h => by linarith [h.2]
  simp [hnot]

/-- Exact cross-branch annihilation `V_s (U_1† g) = 0` on `(0, ∞)`. -/
theorem lewisParabolic_comp_shiftAdj (s : ℂ) (g : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    lewisParabolic s (lewisShiftAdj g) a = 0 := by
  unfold lewisParabolic lewisShiftAdj
  have hnot : ¬ (1 < a / (a + 1)) := by
    have : a / (a + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  simp [hnot]

/-- Pointwise orthogonality of `U_1† g` and `V_s† h` across `(0, ∞)`. -/
theorem lewisCriticalInner_shiftAdj_parabolicAdj (s : ℂ) (g h : ℝ → ℂ) :
    lewisCriticalInner (lewisShiftAdj g) (lewisParabolicAdj s h) = 0 := by
  unfold lewisCriticalInner
  have hzero : ∀ x ∈ Ioi (0 : ℝ),
      lewisShiftAdj g x * (starRingEnd ℂ) (lewisParabolicAdj s h x) *
        (lewisCriticalWeight x : ℂ) = 0 := by
    intro x _
    by_cases hx : 1 < x
    · have hnot : x ∉ Ioo (0 : ℝ) 1 := fun hm => by linarith [hm.2]
      simp [lewisParabolicAdj, hnot]
    · simp [lewisShiftAdj, hx]
  rw [setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero]

/-- **Diagonal Co-Square Identity `(M_s(M_s† g))(a) = μ_s(a) g(a)`.**
Because `U_1 V_s† = V_s U_1† = 0`, `M_s M_s†` collapses to pure pointwise multiplication by
`lewisFareyMultiplier s`. -/
theorem lewisFarey_comp_fareyAdj (s : ℂ) (g : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    lewisFarey s (lewisFareyAdj s g) a = (lewisFareyMultiplier s a : ℂ) * g a := by
  have ha1 : 0 < a + 1 := by linarith
  have ha1_gt1 : 1 < a + 1 := by linarith
  have ha1C : ((a + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha1.ne'
  let c : ℝ := a / (a + 1)
  have hc_mem : c ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ha ha1, (div_lt_one ha1).mpr (by linarith)⟩
  have h1c_eq : 1 - c = (a + 1)⁻¹ := by dsimp [c]; field_simp [ha1.ne']; ring
  have hc_div : c / (1 - c) = a := by dsimp [c]; rw [h1c_eq]; field_simp [ha1.ne']
  have hlin_shift : lewisShift (lewisFareyAdj s g) a =
      lewisShift (lewisShiftAdj g) a + lewisShift (lewisParabolicAdj s g) a := rfl
  have hlin_para : lewisParabolic s (lewisFareyAdj s g) a =
      lewisParabolic s (lewisShiftAdj g) a + lewisParabolic s (lewisParabolicAdj s g) a := by
    unfold lewisParabolic lewisFareyAdj; ring
  unfold lewisFarey
  rw [hlin_shift, hlin_para, lewisShift_comp_parabolicAdj s g ha,
    lewisParabolic_comp_shiftAdj s g ha, add_zero, zero_add]
  have hterm1 : lewisShift (lewisShiftAdj g) a =
      ((lewisCriticalWeight a / lewisCriticalWeight (a + 1) : ℝ) : ℂ) * g a := by
    unfold lewisShift lewisShiftAdj
    simp [ha1_gt1]
  have hterm2 : lewisParabolic s (lewisParabolicAdj s g) a =
      (((a + 1) ^ (2 - 4 * s.re) * (lewisCriticalWeight a / lewisCriticalWeight c) : ℝ) : ℂ) *
        g a := by
    unfold lewisParabolic lewisParabolicAdj
    change ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) *
      (if c ∈ Ioo (0 : ℝ) 1 then
        ((1 - c : ℝ) : ℂ) ^ (2 * (starRingEnd ℂ) s - 2) *
          ((lewisCriticalWeight (c / (1 - c)) / lewisCriticalWeight c : ℝ) : ℂ) * g (c / (1 - c))
       else 0) = _
    rw [if_pos hc_mem, hc_div, h1c_eq, ofReal_inv_cpow_pos ha1]
    have hexp : -(2 * s) + -(2 * (starRingEnd ℂ) s - 2) = ((2 - 4 * s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    have hpow : ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * ((a + 1 : ℝ) : ℂ) ^ (-(2 * (starRingEnd ℂ) s - 2)) =
        (((a + 1) ^ (2 - 4 * s.re) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ ha1C, hexp, ← Complex.ofReal_cpow ha1.le]
    rw [← mul_assoc, ← mul_assoc, hpow, Complex.ofReal_mul]
    ring
  rw [hterm1, hterm2]
  unfold lewisFareyMultiplier
  push_cast
  ring

/-- Exact polynomial positivity `(2a² + 2a + 1)⁴ > (a + 1)⁵ (a² + 1)⁴` on `(0, 1]`. -/
private theorem farey_poly_pos_Ioc {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (a + 1) ^ 5 * (a ^ 2 + 1) ^ 4 < (2 * a ^ 2 + 2 * a + 1) ^ 4 := by
  have hsub : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have h1a3 : 0 ≤ 1 - a ^ 3 := sub_nonneg.mpr (pow_le_one₀ ha0.le ha1)
  have h1a4 : 0 ≤ 1 - a ^ 4 := sub_nonneg.mpr (pow_le_one₀ ha0.le ha1)
  have h1a5 : 0 ≤ 1 - a ^ 5 := sub_nonneg.mpr (pow_le_one₀ ha0.le ha1)
  have h1a6 : 0 ≤ 1 - a ^ 6 := sub_nonneg.mpr (pow_le_one₀ ha0.le ha1)
  have h1a7 : 0 ≤ 1 - a ^ 7 := sub_nonneg.mpr (pow_le_one₀ ha0.le ha1)
  have h1a8 : 0 ≤ 1 - a ^ 8 := sub_nonneg.mpr (pow_le_one₀ ha0.le ha1)
  have h1a9 : 0 ≤ 1 - a ^ 9 := sub_nonneg.mpr (pow_le_one₀ ha0.le ha1)
  have hid : (2 * a ^ 2 + 2 * a + 1) ^ 4 - (a + 1) ^ 5 * (a ^ 2 + 1) ^ 4 =
      3 * a + (18 * a ^ 2 + 50 * a ^ 3 + 18 * a ^ 4 + 24 * a ^ 6 +
        20 * a ^ 6 * (1 - a) + 55 * a ^ 5 * (1 - a ^ 3) + 34 * a ^ 5 * (1 - a ^ 4) +
        17 * a ^ 4 * (1 - a ^ 5) + 30 * a ^ 4 * (1 - a ^ 6) + 14 * a ^ 4 * (1 - a ^ 7) +
        5 * a ^ 4 * (1 - a ^ 8) + a ^ 4 * (1 - a ^ 9)) := by ring
  have hrest : 0 ≤ 18 * a ^ 2 + 50 * a ^ 3 + 18 * a ^ 4 + 24 * a ^ 6 +
      20 * a ^ 6 * (1 - a) + 55 * a ^ 5 * (1 - a ^ 3) + 34 * a ^ 5 * (1 - a ^ 4) +
      17 * a ^ 4 * (1 - a ^ 5) + 30 * a ^ 4 * (1 - a ^ 6) + 14 * a ^ 4 * (1 - a ^ 7) +
      5 * a ^ 4 * (1 - a ^ 8) + a ^ 4 * (1 - a ^ 9) := by positivity
  linarith

/-- **Strict Co-Expansivity `μ_s(a) > 1` Everywhere on `(0, ∞)` Across `s.re ≤ 1/2`.** -/
theorem one_lt_lewisFareyMultiplier {s : ℂ} (hs : s.re ≤ 1 / 2) {a : ℝ} (ha : 0 < a) :
    1 < lewisFareyMultiplier s a := by
  unfold lewisFareyMultiplier
  have ha1 : 0 < a + 1 := by linarith
  have hw_a : 0 < lewisCriticalWeight a := lewisCriticalWeight_pos ha
  have hw_a1 : 0 < lewisCriticalWeight (a + 1) := lewisCriticalWeight_pos ha1
  have hw_c : 0 < lewisCriticalWeight (a / (a + 1)) := lewisCriticalWeight_pos (div_pos ha ha1)
  by_cases hge1 : 1 ≤ a
  · -- For `a ≥ 1`, `lewisCriticalWeight (a + 1) < lewisCriticalWeight a` alone gives `> 1`:
    have hsum_lt : a + a⁻¹ < (a + 1) + (a + 1)⁻¹ := by
      have hdiff : ((a + 1) + (a + 1)⁻¹) - (a + a⁻¹) = (a * (a + 1) - 1) / (a * (a + 1)) := by
        field_simp [ha.ne', ha1.ne']; ring
      have hnum : 0 < a * (a + 1) - 1 := by nlinarith
      have hpos : 0 < ((a + 1) + (a + 1)⁻¹) - (a + a⁻¹) := by rw [hdiff]; positivity
      linarith
    have h6_lt : ((a + 1) + (a + 1)⁻¹) ^ (-6 : ℝ) < (a + a⁻¹) ^ (-6 : ℝ) :=
      Real.rpow_lt_rpow_of_neg (add_pos ha (inv_pos.mpr ha)) hsum_lt (by norm_num)
    have hhalf_lt : (a + 1) ^ (-(1 / 2 : ℝ)) < a ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_lt_rpow_of_neg ha (by linarith) (by norm_num)
    have hw_lt : lewisCriticalWeight (a + 1) < lewisCriticalWeight a := by
      unfold lewisCriticalWeight
      exact mul_lt_mul'' h6_lt hhalf_lt (by positivity) (by positivity)
    have h1_lt : 1 < lewisCriticalWeight a / lewisCriticalWeight (a + 1) :=
      (one_lt_div hw_a1).mpr hw_lt
    have hterm2_pos : 0 < (a + 1) ^ (2 - 4 * s.re) *
        (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) := by positivity
    linarith
  · push_neg at hge1
    -- For `0 < a < 1` and `s.re ≤ 1/2`, the second summand alone exceeds `1`:
    have hpow_ge1 : 1 ≤ (a + 1) ^ (2 - 4 * s.re) :=
      Real.one_le_rpow (by linarith) (by linarith)
    let c : ℝ := a / (a + 1)
    have hc_pos : 0 < c := div_pos ha ha1
    let q : ℝ := (2 * a ^ 2 + 2 * a + 1) / ((a + 1) * (a ^ 2 + 1))
    have hq_pos : 0 < q := by dsimp [q]; positivity
    have hq_ratio : (c + c⁻¹) / (a + a⁻¹) = q := by
      dsimp [c, q]
      field_simp [ha.ne', ha1.ne']
      ring
    have hq4_gt : a + 1 < q ^ 4 := by
      dsimp [q]
      rw [div_pow, lt_div_iff₀ (by positivity)]
      have hpoly := farey_poly_pos_Ioc ha hge1.le
      linarith [show (a + 1) * ((a + 1) * (a ^ 2 + 1)) ^ 4 = (a + 1) ^ 5 * (a ^ 2 + 1) ^ 4 by ring]
    have hq12_gt : a + 1 < (q ^ 6) ^ 2 := by
      have ha1_3 : a + 1 ≤ (a + 1) ^ 3 := by nlinarith
      have hpow3 : (a + 1) ^ 3 < (q ^ 4) ^ 3 :=
        pow_lt_pow_left₀ hq4_gt (by positivity) (by norm_num)
      linarith [show (q ^ 4) ^ 3 = (q ^ 6) ^ 2 by ring]
    have hhalf_sq : ((a + 1) ^ (1 / 2 : ℝ)) ^ 2 = a + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha1.le]; norm_num
    have hq6_gt : (a + 1) ^ (1 / 2 : ℝ) < q ^ 6 := by
      rw [← hhalf_sq] at hq12_gt
      exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hq12_gt
    have hw_ratio_eq : lewisCriticalWeight a / lewisCriticalWeight c =
        q ^ 6 * (a + 1) ^ (-(1 / 2 : ℝ)) := by
      unfold lewisCriticalWeight
      have h6_eq : (a + a⁻¹) ^ (-6 : ℝ) / (c + c⁻¹) ^ (-6 : ℝ) = q ^ 6 := by
        have hpos_a : 0 < a + a⁻¹ := add_pos ha (inv_pos.mpr ha)
        have hpos_c : 0 < c + c⁻¹ := add_pos hc_pos (inv_pos.mpr hc_pos)
        rw [Real.rpow_neg hpos_a.le, Real.rpow_neg hpos_c.le,
          inv_div_inv (by positivity) (by positivity), ← Real.div_rpow hpos_c.le hpos_a.le,
          hq_ratio]
        exact Real.rpow_ofNat q 6
      have hhalf_eq : a ^ (-(1 / 2 : ℝ)) / c ^ (-(1 / 2 : ℝ)) = (a + 1) ^ (-(1 / 2 : ℝ)) := by
        dsimp [c]
        rw [Real.div_rpow ha.le ha1.le]
        field_simp [(Real.rpow_pos_of_pos ha _).ne', (Real.rpow_pos_of_pos ha1 _).ne']
      calc
        ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))) /
            ((c + c⁻¹) ^ (-6 : ℝ) * c ^ (-(1 / 2 : ℝ)))
            = ((a + a⁻¹) ^ (-6 : ℝ) / (c + c⁻¹) ^ (-6 : ℝ)) *
                (a ^ (-(1 / 2 : ℝ)) / c ^ (-(1 / 2 : ℝ))) := by ring
        _ = q ^ 6 * (a + 1) ^ (-(1 / 2 : ℝ)) := by rw [h6_eq, hhalf_eq]
    have hw_ratio_gt1 : 1 < lewisCriticalWeight a / lewisCriticalWeight c := by
      rw [hw_ratio_eq]
      have hmul := mul_lt_mul_of_pos_right hq6_gt (Real.rpow_pos_of_pos ha1 (-(1 / 2 : ℝ)))
      have hid : (a + 1) ^ (1 / 2 : ℝ) * (a + 1) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add ha1]; norm_num
      linarith
    have hterm2_gt1 : 1 < (a + 1) ^ (2 - 4 * s.re) *
        (lewisCriticalWeight a / lewisCriticalWeight c) := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ < (a + 1) ^ (2 - 4 * s.re) * (lewisCriticalWeight a / lewisCriticalWeight c) :=
          mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hpow_ge1 hw_ratio_gt1 zero_le_one
            (Real.rpow_pos_of_pos ha1 _)
    have hterm1_pos : 0 < lewisCriticalWeight a / lewisCriticalWeight (a + 1) :=
      div_pos hw_a hw_a1
    linarith

/-- Norm-boundedness of `lewisShift`, `lewisParabolic s`, and `lewisFarey s` on `H_LP`
across `s.re ≥ 0`. -/
theorem lewisFarey_normBounded {s : ℂ} (hs0 : 0 ≤ s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
      IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
        lewisCriticalNormSq (lewisFarey s f) ≤ C * lewisCriticalNormSq f := by
  let C_U : ℝ := (4 : ℝ) ^ (7 : ℝ)
  let C_V : ℝ := (4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)
  refine ⟨2 * (C_U + C_V), by dsimp [C_U, C_V]; positivity, fun f hf => ?_⟩
  have hU_bound : lewisCriticalNormSq (lewisShift f) ≤ C_U * lewisCriticalNormSq f := by
    by_cases hintU : IntegrableOn (fun a => ‖lewisShift f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)
    · unfold lewisCriticalNormSq lewisShift
      have hshift := integral_Ioi_zero_add_subst 1
        (fun b : ℝ => ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1))
      have hlhs : (∫ a in Ioi (0 : ℝ), ‖f (a + 1)‖ ^ 2 * lewisCriticalWeight a) =
          ∫ b in Ioi (1 : ℝ), ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1) := by
        simpa [add_sub_cancel_right] using hshift
      have hintU1 : IntegrableOn (fun b => ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1)) (Ioi 1) := by
        have himg : (fun a : ℝ => a + 1) '' Ioi (0 : ℝ) = Ioi 1 := by
          ext b; simp only [mem_image, mem_Ioi]
          exact ⟨fun ⟨a, ha, rfl⟩ => by linarith, fun hb => ⟨b - 1, by linarith, sub_add_cancel b 1⟩⟩
        have hinj : InjOn (fun a : ℝ => a + 1) (Ioi 0) := fun _ _ _ _ h => add_right_cancel h
        have hderiv : ∀ a ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x + 1) 1 (Ioi 0) a :=
          fun a _ => ((hasDerivAt_id a).add_const 1).hasDerivWithinAt
        have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
          hinj (fun b : ℝ => ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1))
        rw [himg] at hiff
        exact hiff.mp (by simpa [lewisShift, add_sub_cancel_right] using hintU)
      rw [hlhs]
      have hf1 := hf.mono_set (Ioi_subset_Ioi zero_le_one)
      have hmono := setIntegral_mono_on hintU1 (hf1.const_mul C_U) measurableSet_Ioi fun b hb => by
        calc
          ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1)
              ≤ ‖f b‖ ^ 2 * (C_U * lewisCriticalWeight b) :=
            mul_le_mul_of_nonneg_left (weight_shift_ratio_bound_Ioi_one hb).2 (sq_nonneg _)
          _ = C_U * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
      rw [integral_const_mul] at hmono
      have hrest : 0 ≤ ∫ a in Ioc (0 : ℝ) 1, ‖f a‖ ^ 2 * lewisCriticalWeight a :=
        setIntegral_nonneg measurableSet_Ioc fun a ha =>
          mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos ha.1).le
      have hsplit : (∫ a in Ioi (0 : ℝ), ‖f a‖ ^ 2 * lewisCriticalWeight a) =
          (∫ a in Ioc (0 : ℝ) 1, ‖f a‖ ^ 2 * lewisCriticalWeight a) +
            ∫ b in Ioi (1 : ℝ), ‖f b‖ ^ 2 * lewisCriticalWeight b := by
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
        exact setIntegral_union (Set.disjoint_left.mpr fun _ hx hy => (not_lt.mpr hx.2) hy)
          measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self) hf1
      rw [hsplit]
      nlinarith [show 0 ≤ C_U by dsimp [C_U]; positivity]
    · rw [lewisCriticalNormSq, integral_undef hintU]
      exact mul_nonneg (by dsimp [C_U]; positivity) (lewisCriticalNormSq_nonneg f)
  have hV_bound : lewisCriticalNormSq (lewisParabolic s f) ≤ C_V * lewisCriticalNormSq f := by
    by_cases hintV :
        IntegrableOn (fun a => ‖lewisParabolic s f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)
    · -- Express via `c = a / (a + 1)` on `Ioo 0 1`:
      let H_V : ℝ → ℝ := fun c =>
        ‖f c‖ ^ 2 * ((1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)))
      have hcongr_V : ∀ a ∈ Ioi (0 : ℝ),
          ‖lewisParabolic s f a‖ ^ 2 * lewisCriticalWeight a =
            ((a + 1) ^ (-2 : ℝ)) • H_V (a / (a + 1)) := by
        intro a ha
        have ha1 : 0 < a + 1 := by linarith [show 0 < a from ha]
        let c : ℝ := a / (a + 1)
        have h1c : 1 - c = (a + 1)⁻¹ := by dsimp [c]; field_simp [ha1.ne']; ring
        have hc_div : c / (1 - c) = a := by dsimp [c]; rw [h1c]; field_simp [ha1.ne']
        dsimp only [smul_eq_mul, H_V, lewisParabolic]
        rw [norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos ha1, h1c, hc_div]
        have hre : (-(2 * s)).re = -2 * s.re := by simp
        rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul ha1.le, Real.inv_rpow ha1.le,
          ← Real.rpow_neg ha1.le]
        have hcomb : (a + 1) ^ (-2 : ℝ) *
            (‖f c‖ ^ 2 * ((a + 1) ^ (-(4 * s.re - 2)) * lewisCriticalWeight a)) =
            ((a + 1) ^ (-2 : ℝ) * (a + 1) ^ (-(4 * s.re - 2))) *
              ‖f c‖ ^ 2 * lewisCriticalWeight a := by ring
        rw [hcomb, ← Real.rpow_add ha1]
        congr 2; congr 1; push_cast; ring
      have heq_V : lewisCriticalNormSq (lewisParabolic s f) = ∫ c in Ioo (0 : ℝ) 1, H_V c := by
        unfold lewisCriticalNormSq
        rw [setIntegral_congr_fun measurableSet_Ioi hcongr_V, ← integral_Ioi_zero_mobius_subst]
      have hint_HV : IntegrableOn H_V (Ioo 0 1) := by
        let φ : ℝ → ℝ := fun a => a / (a + 1)
        have himg : φ '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
          ext c; simp only [φ, mem_image, mem_Ioi, mem_Ioo]
          refine ⟨fun ⟨a, ha, rfl⟩ => ⟨div_pos ha (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩,
            fun ⟨hc0, hc1⟩ => ⟨c / (1 - c), div_pos hc0 (sub_pos.mpr hc1), by field_simp [(sub_pos.mpr hc1).ne']; ring⟩⟩
        have hinj : InjOn φ (Ioi 0) := by
          intro a₁ ha₁ a₂ ha₂ heq; dsimp [φ] at heq
          rw [div_eq_div_iff (by linarith [show 0 < a₁ from ha₁]) (by linarith [show 0 < a₂ from ha₂])] at heq
          linarith
        have hderiv : ∀ a ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (((a + 1) ^ 2)⁻¹) (Ioi 0) a := by
          intro a ha
          have ha1 : a + 1 ≠ 0 := by linarith [show 0 < a from ha]
          have hd := (hasDerivAt_id a).div ((hasDerivAt_id a).add_const 1) ha1
          have hval : (1 * (a + 1) - a * (1 + 0)) / (a + 1) ^ 2 = ((a + 1) ^ 2)⁻¹ := by
            field_simp [ha1]; ring
          exact (hval ▸ hd).hasDerivWithinAt
        have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
          hderiv hinj H_V
        rw [himg] at hiff
        refine hiff.mpr (hintV.congr_fun (fun a ha => ?_) measurableSet_Ioi)
        rw [hcongr_V a ha]
        have ha1 : 0 < a + 1 := by linarith [show 0 < a from ha]
        have habs : |((a + 1) ^ 2)⁻¹| = (a + 1) ^ (-2 : ℝ) := by
          rw [abs_of_pos (by positivity), Real.rpow_neg ha1.le, Real.rpow_two]
        simp [φ, habs]
      -- Pointwise bound `H_V c ≤ C_V * (‖f c‖^2 * lewisCriticalWeight c)` on `Ioo 0 1` via `b = c⁻¹ > 1`:
      have hpt_V : ∀ c ∈ Ioo (0 : ℝ) 1, H_V c ≤ C_V * (‖f c‖ ^ 2 * lewisCriticalWeight c) := by
        intro c hc
        let b : ℝ := c⁻¹
        have hb_gt1 : 1 < b := (one_lt_inv₀ hc.1).mpr hc.2
        have hb0 : 0 < b := zero_lt_one.trans hb_gt1
        have h1c_pos : 0 < 1 - c := sub_pos.mpr hc.2
        have hcd_eq : c / (1 - c) = (b - 1)⁻¹ := by
          dsimp [b]; field_simp [hc.1.ne', h1c_pos.ne', (sub_pos.mpr hb_gt1).ne']; ring
        have h1c_b : 1 - c = (b - 1) / b := by
          dsimp [b]; field_simp [hc.1.ne', hb0.ne']
        have hw_cd : lewisCriticalWeight (c / (1 - c)) =
            (b - 1) * lewisCriticalWeight (b - 1) := by
          rw [hcd_eq]
          have hu : 0 < b - 1 := sub_pos.mpr hb_gt1
          unfold lewisCriticalWeight
          rw [inv_inv, add_comm (b - 1)⁻¹ (b - 1), Real.inv_rpow hu.le, ← Real.rpow_neg hu.le,
            neg_neg]
          have h1 : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (1 / 2 : ℝ) =
              ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * ((b - 1) ^ (1 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ))) := by
            rw [← Real.rpow_add hu]; congr 2; norm_num
          rw [h1, Real.rpow_one]; ring
        have hw_c_eq : lewisCriticalWeight c = b * lewisCriticalWeight b := by
          dsimp [b]
          unfold lewisCriticalWeight
          rw [inv_inv, add_comm b⁻¹ b, Real.inv_rpow hb0.le, ← Real.rpow_neg hb0.le, neg_neg]
          have h1 : (b + b⁻¹) ^ (-6 : ℝ) * b ^ (1 / 2 : ℝ) =
              (b + b⁻¹) ^ (-6 : ℝ) * (b ^ (1 : ℝ) * b ^ (-(1 / 2 : ℝ))) := by
            rw [← Real.rpow_add hb0]; congr 2; norm_num
          rw [h1, Real.rpow_one]; ring
        -- Therefore `(1 - c)^(4 Re s - 2) * w_LP(c/(1 - c))`
        -- `= ((b - 1) / b)^(4 Re s - 1) * (b * lewisCriticalWeight (b - 1))`:
        have hker_eq : (1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)) =
            ((b - 1) / b) ^ (4 * s.re - 1) * (b * lewisCriticalWeight (b - 1)) := by
          have hu : 0 < b - 1 := sub_pos.mpr hb_gt1
          rw [h1c_b, hw_cd, Real.div_rpow hu.le hb0.le, Real.div_rpow hu.le hb0.le]
          have h1 : (b - 1) ^ (4 * s.re - 1) = (b - 1) ^ (4 * s.re - 2) * (b - 1) ^ (1 : ℝ) := by
            rw [← Real.rpow_add hu]; congr 1; ring
          have h2 : b ^ (4 * s.re - 1) = b ^ (4 * s.re - 2) * b ^ (1 : ℝ) := by
            rw [← Real.rpow_add hb0]; congr 1; ring
          rw [h1, h2, Real.rpow_one, Real.rpow_one]
          field_simp [(Real.rpow_pos_of_pos hb0 _).ne', hb0.ne']
        have hker_bound : (1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)) ≤
            C_V * lewisCriticalWeight c := by
          by_cases hb2 : b ≤ 2
          · -- Near `c → 1⁻` (`1 < b ≤ 2`): `1 - c ≤ 1/2 ≤ 1`, `c / (1 - c) = (b - 1)⁻¹ ≥ 1`:
            have hu : 0 < b - 1 := sub_pos.mpr hb_gt1
            have hu_le1 : b - 1 ≤ 1 := by linarith
            have hu6 : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (b - 1) ^ (6 : ℝ) := by
              calc
                ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ ((b - 1)⁻¹) ^ (-6 : ℝ) :=
                  Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu) (by linarith) (by norm_num)
                _ = (b - 1) ^ (6 : ℝ) := by
                  rw [Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]; norm_num
            have hnum_le : (b - 1) ^ (4 * s.re - 1) * lewisCriticalWeight (b - 1) ≤ 1 := by
              unfold lewisCriticalWeight
              calc
                (b - 1) ^ (4 * s.re - 1) *
                    (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ)))
                    ≤ (b - 1) ^ (4 * s.re - 1) * ((b - 1) ^ (6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ))) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hu6 (by positivity)) (by positivity)
                _ = (b - 1) ^ (4 * s.re - 1) * (b - 1) ^ (6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ)) := by
                  ring
                _ = (b - 1) ^ (4 * s.re + 9 / 2) := by
                  rw [← Real.rpow_add hu, ← Real.rpow_add hu]; congr 1; ring
                _ ≤ 1 := Real.rpow_le_one hu.le hu_le1 (by linarith)
            have hden_le : b ^ (2 - 4 * s.re) ≤ (2 : ℝ) ^ (4 * s.re + 2) := by
              calc
                b ^ (2 - 4 * s.re) ≤ b ^ (4 * s.re + 2) :=
                  Real.rpow_le_rpow_of_exponent_le hb_gt1.le (by linarith)
                _ ≤ (2 : ℝ) ^ (4 * s.re + 2) :=
                  Real.rpow_le_rpow hb0.le hb2 (by linarith)
            have h4w := one_le_four_pow_seven_mul_weight_Ioc_two hb_gt1 hb2
            rw [hker_eq, hw_c_eq, Real.div_rpow hu.le hb0.le]
            have hrew : ((b - 1) ^ (4 * s.re - 1) / b ^ (4 * s.re - 1)) *
                (b * lewisCriticalWeight (b - 1)) =
                b ^ (2 - 4 * s.re) * ((b - 1) ^ (4 * s.re - 1) * lewisCriticalWeight (b - 1)) := by
              have hb_pow : b / b ^ (4 * s.re - 1) = b ^ (2 - 4 * s.re) := by
                rw [div_eq_mul_inv, ← Real.rpow_neg hb0.le, ← Real.rpow_one b,
                  ← Real.rpow_add hb0]
                -- wait: avoid rewriting `b` inside `4 * s.re - 1` (`b` has no `s.re`!)
                sorry
              sorry
            sorry
          · sorry
        dsimp only [H_V]
        calc
          ‖f c‖ ^ 2 * ((1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)))
              ≤ ‖f c‖ ^ 2 * (C_V * lewisCriticalWeight c) :=
            mul_le_mul_of_nonneg_left hker_bound (sq_nonneg _)
          _ = C_V * (‖f c‖ ^ 2 * lewisCriticalWeight c) := by ring
      sorry
    · rw [lewisCriticalNormSq, integral_undef hintV]
      exact mul_nonneg (by dsimp [C_V]; positivity) (lewisCriticalNormSq_nonneg f)
  sorry
