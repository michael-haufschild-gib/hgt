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
    (apply Complex.ext <;> simp); ring
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
  by_cases hpq : p < q
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
  rw [hfun, integrableOn_indicator_iff measurableSet_Ioc, inter_eq_self_of_subset_left hsub]
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
    exact ⟨fun ⟨a, ha, hab⟩ => by linarith, fun hb => ⟨b - c, by linarith, sub_add_cancel b c⟩⟩
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
  have hsq : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hle : ((1 / 2 : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by rw [hsq]; norm_num
  exact (sq_le_sq₀ (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le).mp hle

private theorem weight_shift_ratio_bound_Ioi_one {b : ℝ} (hb : 1 < b) :
    ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) ∧
      lewisCriticalWeight (b - 1) ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
  have hu_pos : 0 < b - 1 := sub_pos.mpr hb
  have hb_pos : 0 < b := zero_lt_one.trans hb
  by_cases hb2 : b ≤ 2
  · have hu_le1 : b - 1 ≤ 1 := by linarith
    have hu6 : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (b - 1) ^ (6 : ℝ) := by
      calc
        ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ ((b - 1)⁻¹) ^ (-6 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu_pos) (by linarith) (by norm_num)
        _ = (b - 1) ^ (6 : ℝ) := by rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le]; norm_num
    have hu6_le1 : (b - 1) ^ (6 : ℝ) ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by norm_num)
    have hb_sum_le : b + b⁻¹ ≤ 3 := by
      have : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb.le
      linarith
    have hb_low : (3 : ℝ) ^ (-6 : ℝ) ≤ (b + b⁻¹) ^ (-6 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (add_pos hb_pos (inv_pos.mpr hb_pos)) hb_sum_le (by norm_num)
    have hc1 : (1 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (3 : ℝ) ^ (-6 : ℝ) := by norm_num
    have hfirst : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) :=
      (hu6.trans hu6_le1).trans (hc1.trans (mul_le_mul_of_nonneg_left hb_low (by norm_num)))
    refine ⟨hfirst, ?_⟩
    unfold lewisCriticalWeight
    have hw_u : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      calc
        ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ))
            ≤ (b - 1) ^ (6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hu6 (Real.rpow_pos_of_pos hu_pos _).le
        _ = (b - 1) ^ (11 / 2 : ℝ) := by rw [← Real.rpow_add hu_pos]; norm_num
        _ ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by norm_num)
    have hb_half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ b ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hb_pos hb2 (by norm_num)
    have hprod := mul_le_mul hb_low (two_neg_half_ge_half.trans hb_half) (by positivity) (by positivity)
    have hnum : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((3 : ℝ) ^ (-6 : ℝ) * (1 / 2 : ℝ)) := by norm_num
    have hc2 : (1 : ℝ) ≤ (4 : ℝ) ^ (7 : ℝ) * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-(1 / 2 : ℝ))) :=
      hnum.trans (mul_le_mul_of_nonneg_left hprod (by norm_num))
    exact hw_u.trans hc2
  · rw [not_le] at hb2
    have hb_sum_le : b + b⁻¹ ≤ 4 * ((b - 1) + (b - 1)⁻¹) := by
      have hbinv : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb.le
      have huinv : 0 < (b - 1)⁻¹ := inv_pos.mpr hu_pos
      linarith
    have hfirst : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ) * (b + b⁻¹) ^ (-6 : ℝ) := by
      have h := Real.rpow_le_rpow_of_nonpos (add_pos hb_pos (inv_pos.mpr hb_pos)) hb_sum_le
        (by norm_num : (-6 : ℝ) ≤ 0)
      rw [Real.mul_rpow (by norm_num) (add_pos hu_pos (inv_pos.mpr hu_pos)).le] at h
      have h4 : (4 : ℝ) ^ (6 : ℝ) * (4 : ℝ) ^ (-6 : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ (6 : ℝ))
      linarith
    refine ⟨hfirst, ?_⟩
    unfold lewisCriticalWeight
    have huhalf : (b - 1) ^ (-(1 / 2 : ℝ)) ≤ 4 * b ^ (-(1 / 2 : ℝ)) := by
      have hexp_np : (-(1 / 2 : ℝ)) ≤ 0 := by norm_num
      have h1 : (b - 1) ^ (-(1 / 2 : ℝ)) ≤ (b * (2 : ℝ)⁻¹) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hb_pos (by norm_num)) (by linarith) hexp_np
      rw [Real.mul_rpow hb_pos.le (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)] at h1
      have h2 : ((2 : ℝ)⁻¹) ^ (-(1 / 2 : ℝ)) ≤ 4 := by
        rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
        calc
          (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num
      calc
        (b - 1) ^ (-(1 / 2 : ℝ)) ≤ b ^ (-(1 / 2 : ℝ)) * ((2 : ℝ)⁻¹) ^ (-(1 / 2 : ℝ)) := h1
        _ ≤ b ^ (-(1 / 2 : ℝ)) * 4 :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos hb_pos _).le
        _ = 4 * b ^ (-(1 / 2 : ℝ)) := by ring
    calc
      ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ))
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
    rw [not_le] at hgt
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
      have hR2 : K ^ (1 / δ) < R - 1 := by
        have hm : K ^ (1 / δ) + 2 ≤ R := le_max_right 2 (K ^ (1 / δ) + 2)
        linarith
      rw [h1]
      exact Real.rpow_lt_rpow (Real.rpow_pos_of_pos hK_pos _).le hR2 hδ_pos
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
      have hu_pos : 0 < b - 1 := sub_pos.mpr hb
      by_cases hb2 : b ≤ 2
      · have hu_le1 : b - 1 ≤ 1 := by linarith
        have hu6 : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ (b - 1) ^ (6 : ℝ) := by
          calc
            ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) ≤ ((b - 1)⁻¹) ^ (-6 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu_pos) (by linarith) (by norm_num)
            _ = (b - 1) ^ (6 : ℝ) := by
              rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le]; norm_num
        have hker_le1 : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2) ≤ 1 := by
          calc
            ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)
                ≤ (b - 1) ^ (6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2) :=
              mul_le_mul_of_nonneg_right hu6 (Real.rpow_pos_of_pos hu_pos _).le
            _ = (b - 1) ^ (4 * s.re + 9 / 2) := by rw [← Real.rpow_add hu_pos]; congr 1; ring
            _ ≤ 1 := Real.rpow_le_one hu_pos.le hu_le1 (by linarith)
        have hstep := hker_le1.trans (one_le_four_pow_seven_mul_weight_Ioc_two hb hb2)
        calc
          ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2))
              ≤ ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
            mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
          _ = (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
      · rw [not_le] at hb2
        have hu_ge1 : 1 ≤ b - 1 := by linarith
        have hu_exp : (b - 1) ^ (4 * s.re - 3 / 2) ≤ (b - 1) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hu_ge1 (by linarith)
        have hker_le : ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2) ≤
            (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b := by
          calc
            ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2)
                ≤ ((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hu_exp (by positivity)
            _ = lewisCriticalWeight (b - 1) := rfl
            _ ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b :=
              (weight_shift_ratio_bound_Ioi_one hb).2
        calc
          ‖f b‖ ^ 2 * (((b - 1) + (b - 1)⁻¹) ^ (-6 : ℝ) * (b - 1) ^ (4 * s.re - 3 / 2))
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
      have hle_tot : ∫ b in Ioi (1 : ℝ), ‖f b‖ ^ 2 * lewisCriticalWeight b ≤
          lewisCriticalNormSq f := by linarith only [hsplit, hrest]
      exact hmono.trans (mul_le_mul_of_nonneg_left hle_tot (by positivity))
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

private theorem weight_add_nat_bound {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) :
    lewisCriticalWeight a ≤ ((m : ℝ) + 2) ^ (7 : ℝ) * lewisCriticalWeight (a + (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm2_pos : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have hK1_pos : (0 : ℝ) < ((m : ℝ) + 2) ^ (7 : ℝ) := Real.rpow_pos_of_pos hm2_pos _
  have ham_pos : 0 < a + (m : ℝ) := by linarith
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
    have ham_sum : (a + m) + (a + m)⁻¹ ≤ (m : ℝ) + 2 := by
      have : (a + (m : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      linarith
    have h6_low : ((m : ℝ) + 2) ^ (-6 : ℝ) ≤ ((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (add_pos ham_pos (inv_pos.mpr ham_pos)) ham_sum (by norm_num)
    have hhalf_low : ((m : ℝ) + 2) ^ (-1 : ℝ) ≤ (a + (m : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans
        (Real.rpow_le_rpow_of_nonpos ham_pos (by linarith) (by norm_num))
    have hprod := mul_le_mul h6_low hhalf_low (by positivity) (by positivity)
    have hid : ((m : ℝ) + 2) ^ (7 : ℝ) *
        (((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ)) = 1 := by
      rw [← Real.rpow_add hm2_pos, ← Real.rpow_add hm2_pos]
      norm_num
    unfold lewisCriticalWeight
    calc
      (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ)) ≤ 1 := hw_a
      _ = ((m : ℝ) + 2) ^ (7 : ℝ) *
            (((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ)) := hid.symm
      _ ≤ ((m : ℝ) + 2) ^ (7 : ℝ) *
            (((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) * (a + (m : ℝ)) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod hK1_pos.le
  · rw [not_le] at ha1
    have ham_le : a + (m : ℝ) ≤ ((m : ℝ) + 2) * a := by
      have hma : (m : ℝ) ≤ (m : ℝ) * a := le_mul_of_one_le_right (by linarith) ha1.le
      linarith
    have hsum_le : (a + m) + (a + m)⁻¹ ≤ ((m : ℝ) + 2) * (a + a⁻¹) := by
      have hainv : (a + (m : ℝ))⁻¹ ≤ a⁻¹ := (inv_le_inv₀ ham_pos ha).mpr (by linarith)
      have hminv : a⁻¹ ≤ ((m : ℝ) + 2) * a⁻¹ :=
        le_mul_of_one_le_left (inv_pos.mpr ha).le (by linarith)
      linarith
    have h6_low : ((m : ℝ) + 2) ^ (-6 : ℝ) * (a + a⁻¹) ^ (-6 : ℝ) ≤
        ((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) := by
      have h := Real.rpow_le_rpow_of_nonpos (add_pos ham_pos (inv_pos.mpr ham_pos)) hsum_le
        (by norm_num : (-6 : ℝ) ≤ 0)
      rwa [Real.mul_rpow hm2_pos.le (add_pos ha (inv_pos.mpr ha)).le] at h
    have hhalf_low : ((m : ℝ) + 2) ^ (-1 : ℝ) * a ^ (-(1 / 2 : ℝ)) ≤
        (a + (m : ℝ)) ^ (-(1 / 2 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_nonpos ham_pos ham_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
      rw [Real.mul_rpow hm2_pos.le ha.le] at h
      exact (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
        (Real.rpow_pos_of_pos ha _).le).trans h
    unfold lewisCriticalWeight
    have hprod := mul_le_mul h6_low hhalf_low (by positivity) (by positivity)
    have hid : ((m : ℝ) + 2) ^ (7 : ℝ) * ((m : ℝ) + 2) ^ (-6 : ℝ) *
        ((m : ℝ) + 2) ^ (-1 : ℝ) = 1 := by
      rw [mul_assoc, ← Real.rpow_add hm2_pos, ← Real.rpow_add hm2_pos]
      norm_num
    calc
      (a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))
          = (((m : ℝ) + 2) ^ (7 : ℝ) * ((m : ℝ) + 2) ^ (-6 : ℝ) * ((m : ℝ) + 2) ^ (-1 : ℝ)) *
              ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))) := by rw [hid, one_mul]
      _ = ((m : ℝ) + 2) ^ (7 : ℝ) *
            ((((m : ℝ) + 2) ^ (-6 : ℝ) * (a + a⁻¹) ^ (-6 : ℝ)) *
              (((m : ℝ) + 2) ^ (-1 : ℝ) * a ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ ((m : ℝ) + 2) ^ (7 : ℝ) *
            (((a + m) + (a + m)⁻¹) ^ (-6 : ℝ) * (a + (m : ℝ)) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod hK1_pos.le

private def tailBranchInv (m : ℕ) (b : ℝ) : ℝ :=
  (b - 1)⁻¹ - (m : ℝ)

/-- **Tail Branches (`m ≥ 1`) Are Norm-Bounded Across `s.re ≥ 0`.** -/
theorem gaussMayerBranch_tail_normBounded {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs0 : 0 ≤ s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
      IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
        lewisCriticalNormSq (gaussMayerBranch m s f) ≤ C * lewisCriticalNormSq f := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmR
  have hC0_pos : (0 : ℝ) < ((m : ℝ) + 2) ^ (7 : ℝ) * (4 : ℝ) ^ (7 : ℝ) := by positivity
  refine ⟨((m : ℝ) + 2) ^ (7 : ℝ) * (4 : ℝ) ^ (7 : ℝ), hC0_pos.le, fun f hf => ?_⟩
  by_cases hint_m : IntegrableOn
      (fun a : ℝ => ‖gaussMayerBranch m s f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)
  · have hψ_img : tailBranchInv m '' Ioo (1 : ℝ) (1 + (m : ℝ)⁻¹) = Ioi (0 : ℝ) := by
      ext a
      simp only [tailBranchInv, mem_image, mem_Ioo, mem_Ioi]
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
    have hψ_inj : InjOn (tailBranchInv m) (Ioo 1 (1 + (m : ℝ)⁻¹)) := by
      intro b₁ _ b₂ _ heq
      unfold tailBranchInv at heq
      have hinv : (b₁ - 1)⁻¹ = (b₂ - 1)⁻¹ := by linarith
      have hsub := inv_injective hinv
      linarith
    have hψ_deriv : ∀ b ∈ Ioo (1 : ℝ) (1 + (m : ℝ)⁻¹),
        HasDerivWithinAt (tailBranchInv m) (-((b - 1) ^ 2)⁻¹) (Ioo 1 (1 + (m : ℝ)⁻¹)) b := by
      intro b hb
      have hu : b - 1 ≠ 0 := (sub_pos.mpr hb.1).ne'
      have hd1 : HasDerivAt (fun x : ℝ => x - 1) 1 b := (hasDerivAt_id b).sub_const 1
      have hd2 : HasDerivAt (tailBranchInv m) (-1 / (b - 1) ^ 2) b :=
        (hd1.fun_inv hu).sub_const (m : ℝ)
      rw [neg_div, one_div] at hd2
      exact hd2.hasDerivWithinAt
    have hint_S : IntegrableOn
        (fun b => |-((b - 1) ^ 2)⁻¹| •
          (‖gaussMayerBranch m s f (tailBranchInv m b)‖ ^ 2 *
            lewisCriticalWeight (tailBranchInv m b)))
        (Ioo 1 (1 + (m : ℝ)⁻¹)) := by
      have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hψ_deriv
        hψ_inj (fun a => ‖gaussMayerBranch m s f a‖ ^ 2 * lewisCriticalWeight a)
      rw [hψ_img] at hiff
      exact hiff.mp hint_m
    have heq_int : lewisCriticalNormSq (gaussMayerBranch m s f) =
        ∫ b in Ioo (1 : ℝ) (1 + (m : ℝ)⁻¹),
          |-((b - 1) ^ 2)⁻¹| •
            (‖gaussMayerBranch m s f (tailBranchInv m b)‖ ^ 2 *
              lewisCriticalWeight (tailBranchInv m b)) := by
      unfold lewisCriticalNormSq
      have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hψ_deriv hψ_inj
        (fun a => ‖gaussMayerBranch m s f a‖ ^ 2 * lewisCriticalWeight a)
      rw [hψ_img] at h
      exact h
    rw [heq_int]
    have hS_sub : Ioo (1 : ℝ) (1 + (m : ℝ)⁻¹) ⊆ Ioi 0 := fun _ hb => zero_lt_one.trans hb.1
    have hf_S : IntegrableOn
        (fun b => (((m : ℝ) + 2) ^ (7 : ℝ) * (4 : ℝ) ^ (7 : ℝ)) *
          (‖f b‖ ^ 2 * lewisCriticalWeight b))
        (Ioo 1 (1 + (m : ℝ)⁻¹)) :=
      (hf.mono_set hS_sub).const_mul _
    have hpt : ∀ b ∈ Ioo (1 : ℝ) (1 + (m : ℝ)⁻¹),
        |-((b - 1) ^ 2)⁻¹| •
          (‖gaussMayerBranch m s f (tailBranchInv m b)‖ ^ 2 *
            lewisCriticalWeight (tailBranchInv m b)) ≤
          (((m : ℝ) + 2) ^ (7 : ℝ) * (4 : ℝ) ^ (7 : ℝ)) *
            (‖f b‖ ^ 2 * lewisCriticalWeight b) := by
      intro b hb
      have hu_pos : 0 < b - 1 := sub_pos.mpr hb.1
      have ha_pos : 0 < tailBranchInv m b := by
        rw [← mem_Ioi, ← hψ_img]; exact ⟨b, hb, rfl⟩
      have ham_eq : tailBranchInv m b + (m : ℝ) = (b - 1)⁻¹ := by unfold tailBranchInv; ring
      have hb_arg : 1 + (tailBranchInv m b + (m : ℝ))⁻¹ = b := by rw [ham_eq, inv_inv]; ring
      have hgm : ‖gaussMayerBranch m s f (tailBranchInv m b)‖ ^ 2 =
          (b - 1) ^ (4 * s.re) * ‖f b‖ ^ 2 := by
        unfold gaussMayerBranch
        rw [hb_arg, ham_eq, norm_mul, mul_pow,
          Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hu_pos)]
        have hre : (-(2 * s)).re = -2 * s.re := by simp
        rw [hre, Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le, ← Real.rpow_natCast,
          ← Real.rpow_mul hu_pos.le]
        congr 2; push_cast; ring
      have hw_ψ : lewisCriticalWeight (tailBranchInv m b) ≤
          ((m : ℝ) + 2) ^ (7 : ℝ) * lewisCriticalWeight (b - 1)⁻¹ := by
        rw [← ham_eq]
        exact weight_add_nat_bound hm ha_pos
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
      dsimp only [smul_eq_mul]
      rw [habs, hgm]
      calc
        (b - 1) ^ (-2 : ℝ) * (((b - 1) ^ (4 * s.re) * ‖f b‖ ^ 2) *
            lewisCriticalWeight (tailBranchInv m b))
            ≤ (b - 1) ^ (-2 : ℝ) *
                (((b - 1) ^ (4 * s.re) * ‖f b‖ ^ 2) *
                  (((m : ℝ) + 2) ^ (7 : ℝ) * lewisCriticalWeight (b - 1)⁻¹)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hw_ψ (by positivity)
        _ = ((m : ℝ) + 2) ^ (7 : ℝ) * ‖f b‖ ^ 2 * ((b - 1) ^ (4 * s.re) *
              ((b - 1) ^ (-2 : ℝ) * lewisCriticalWeight (b - 1)⁻¹)) := by ring
        _ = ((m : ℝ) + 2) ^ (7 : ℝ) * ‖f b‖ ^ 2 * ((b - 1) ^ (4 * s.re) *
              ((b - 1) ^ (-1 : ℝ) * lewisCriticalWeight (b - 1))) := by rw [hw_inv]
        _ ≤ ((m : ℝ) + 2) ^ (7 : ℝ) * ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
          mul_le_mul_of_nonneg_left (hu_ker1.trans h4w) (by positivity)
        _ = (((m : ℝ) + 2) ^ (7 : ℝ) * (4 : ℝ) ^ (7 : ℝ)) *
              (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
    have hmono := setIntegral_mono_on hint_S hf_S measurableSet_Ioo hpt
    rw [integral_const_mul] at hmono
    have hsub_le : ∫ b in Ioo (1 : ℝ) (1 + (m : ℝ)⁻¹), ‖f b‖ ^ 2 * lewisCriticalWeight b ≤
        lewisCriticalNormSq f := by
      unfold lewisCriticalNormSq
      have hunion : Ioi (0 : ℝ) = Ioo 1 (1 + (m : ℝ)⁻¹) ∪ (Ioi 0 \ Ioo 1 (1 + (m : ℝ)⁻¹)) :=
        (Set.union_sdiff_cancel hS_sub).symm
      conv_rhs => rw [hunion]
      rw [setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Ioo)
        (hf.mono_set hS_sub) (hf.mono_set Set.sdiff_subset)]
      have hrest : 0 ≤ ∫ b in Ioi 0 \ Ioo 1 (1 + (m : ℝ)⁻¹), ‖f b‖ ^ 2 * lewisCriticalWeight b :=
        setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioo) fun b hb =>
          mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hb.1).le
      linarith
    exact hmono.trans (mul_le_mul_of_nonneg_left hsub_le hC0_pos.le)
  · rw [lewisCriticalNormSq, integral_undef hint_m]
    exact mul_nonneg hC0_pos.le (lewisCriticalNormSq_nonneg f)

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

private theorem image_mobius_Ioi_zero :
    (fun a : ℝ => a / (a + 1)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext c
  simp only [mem_image, mem_Ioi, mem_Ioo]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨div_pos ha (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
  · rintro ⟨hc0, hc1⟩
    exact ⟨c / (1 - c), div_pos hc0 (sub_pos.mpr hc1),
      by field_simp [(sub_pos.mpr hc1).ne']; ring⟩

private theorem injOn_mobius_Ioi_zero : InjOn (fun a : ℝ => a / (a + 1)) (Ioi 0) := by
  intro a₁ ha₁ a₂ ha₂ heq
  rw [div_eq_div_iff (by linarith [show 0 < a₁ from ha₁])
    (by linarith [show 0 < a₂ from ha₂])] at heq
  linarith

private theorem hasDerivWithinAt_mobius_Ioi_zero {a : ℝ} (ha : a ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (fun x : ℝ => x / (x + 1)) (((a + 1) ^ 2)⁻¹) (Ioi 0) a := by
  have ha1 : a + 1 ≠ 0 := by linarith [show 0 < a from ha]
  have hd := (hasDerivAt_id a).div ((hasDerivAt_id a).add_const 1) ha1
  refine (hd.congr_deriv ?_).hasDerivWithinAt
  simp only [id_eq]
  field_simp [ha1]
  ring

/-- Möbius change of variables `c = a / (a + 1)` mapping `(0, ∞)` onto `(0, 1)`. -/
theorem integral_Ioi_zero_mobius_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) :
    (∫ c in Ioo (0 : ℝ) 1, h c) = ∫ a in Ioi (0 : ℝ), ((a + 1) ^ (-2 : ℝ)) • h (a / (a + 1)) := by
  have hint := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun _ ha => hasDerivWithinAt_mobius_Ioi_zero ha) injOn_mobius_Ioi_zero h
  rw [image_mobius_Ioi_zero] at hint
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
      have hbm : b ∈ Ioi (1 : ℝ) := hb
      rw [indicator_of_mem hbm]
      unfold lewisShiftAdj
      rw [if_pos hb, Complex.ofReal_div, map_mul, map_div₀, Complex.conj_ofReal,
        Complex.conj_ofReal]
      linear_combination
        f b * (starRingEnd ℂ) (g (b - 1)) * div_mul_cancel₀ (lewisCriticalWeight (b - 1) : ℂ) hwb
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
      (apply Complex.ext <;> simp); ring
    have hpow : ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * ((a + 1 : ℝ) : ℂ) ^ (-(2 * (starRingEnd ℂ) s - 2)) =
        (((a + 1) ^ (2 - 4 * s.re) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ ha1C, hexp, ← Complex.ofReal_cpow ha1.le]
    rw [← mul_assoc, ← mul_assoc, hpow, Complex.ofReal_mul]
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
      have hprod_gt : 1 < a * (a + 1) := by
        calc
          (1 : ℝ) < 1 * (a + 1) := by linarith
          _ ≤ a * (a + 1) := mul_le_mul_of_nonneg_right hge1 ha1.le
      have hnum : 0 < a * (a + 1) - 1 := sub_pos.mpr hprod_gt
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
  · rw [not_le] at hge1
    -- For `0 < a < 1` and `s.re ≤ 1/2`, the second summand alone exceeds `1`:
    have hpow_ge1 : 1 ≤ (a + 1) ^ (2 - 4 * s.re) :=
      Real.one_le_rpow (by linarith) (by linarith)
    have hc_pos : 0 < a / (a + 1) := div_pos ha ha1
    let q : ℝ := (2 * a ^ 2 + 2 * a + 1) / ((a + 1) * (a ^ 2 + 1))
    have hq_pos : 0 < q := by dsimp [q]; positivity
    have hq_ratio : (a / (a + 1) + (a / (a + 1))⁻¹) / (a + a⁻¹) = q := by
      dsimp [q]
      field_simp [ha.ne', ha1.ne']
      ring
    have hq4_gt : a + 1 < q ^ 4 := by
      dsimp [q]
      rw [div_pow, lt_div_iff₀ (by positivity)]
      have hpoly := farey_poly_pos_Ioc ha hge1.le
      linarith [show (a + 1) * ((a + 1) * (a ^ 2 + 1)) ^ 4 = (a + 1) ^ 5 * (a ^ 2 + 1) ^ 4 by ring]
    have hq12_gt : a + 1 < (q ^ 6) ^ 2 := by
      have ha1_3 : a + 1 ≤ (a + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      have hpow3 : (a + 1) ^ 3 < (q ^ 4) ^ 3 :=
        pow_lt_pow_left₀ hq4_gt (by positivity) (by norm_num)
      linarith [show (q ^ 4) ^ 3 = (q ^ 6) ^ 2 by ring]
    have hhalf_sq : ((a + 1) ^ (1 / 2 : ℝ)) ^ 2 = a + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha1.le]; norm_num
    have hq6_gt : (a + 1) ^ (1 / 2 : ℝ) < q ^ 6 := by
      rw [← hhalf_sq] at hq12_gt
      exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hq12_gt
    have hw_ratio_eq : lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1)) =
        q ^ 6 * (a + 1) ^ (-(1 / 2 : ℝ)) := by
      unfold lewisCriticalWeight
      have h6_eq : (a + a⁻¹) ^ (-6 : ℝ) / ((a / (a + 1)) + (a / (a + 1))⁻¹) ^ (-6 : ℝ) = q ^ 6 := by
        have hpos_a : 0 < a + a⁻¹ := add_pos ha (inv_pos.mpr ha)
        have hpos_c : 0 < a / (a + 1) + (a / (a + 1))⁻¹ := add_pos hc_pos (inv_pos.mpr hc_pos)
        rw [Real.rpow_neg hpos_a.le, Real.rpow_neg hpos_c.le,
          inv_div_inv, ← Real.div_rpow hpos_c.le hpos_a.le,
          hq_ratio]
        exact Real.rpow_ofNat q 6
      have hhalf_eq : a ^ (-(1 / 2 : ℝ)) / (a / (a + 1)) ^ (-(1 / 2 : ℝ)) =
          (a + 1) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow ha.le ha1.le]
        field_simp [(Real.rpow_pos_of_pos ha _).ne', (Real.rpow_pos_of_pos ha1 _).ne']
      calc
        ((a + a⁻¹) ^ (-6 : ℝ) * a ^ (-(1 / 2 : ℝ))) /
            (((a / (a + 1)) + (a / (a + 1))⁻¹) ^ (-6 : ℝ) * (a / (a + 1)) ^ (-(1 / 2 : ℝ)))
            = ((a + a⁻¹) ^ (-6 : ℝ) / ((a / (a + 1)) + (a / (a + 1))⁻¹) ^ (-6 : ℝ)) *
                (a ^ (-(1 / 2 : ℝ)) / (a / (a + 1)) ^ (-(1 / 2 : ℝ))) := by ring
        _ = q ^ 6 * (a + 1) ^ (-(1 / 2 : ℝ)) := by rw [h6_eq, hhalf_eq]
    have hw_ratio_gt1 : 1 < lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1)) := by
      rw [hw_ratio_eq]
      have hmul := mul_lt_mul_of_pos_right hq6_gt (Real.rpow_pos_of_pos ha1 (-(1 / 2 : ℝ)))
      have hid : (a + 1) ^ (1 / 2 : ℝ) * (a + 1) ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add ha1]; norm_num
      linarith
    have hterm2_gt1 : 1 < (a + 1) ^ (2 - 4 * s.re) *
        (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ < (a + 1) ^ (2 - 4 * s.re) *
              (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) :=
          mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hpow_ge1 hw_ratio_gt1 zero_le_one
            (Real.rpow_pos_of_pos ha1 _)
    have term1_pos : 0 < lewisCriticalWeight a / lewisCriticalWeight (a + 1) :=
      div_pos hw_a hw_a1
    linarith

private theorem lewisShift_normBounded {f : ℝ → ℂ}
    (hf : IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)) :
    IntegrableOn (fun a => ‖lewisShift f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
      lewisCriticalNormSq (lewisShift f) ≤ (4 : ℝ) ^ (7 : ℝ) * lewisCriticalNormSq f := by
  have hf1 : IntegrableOn (fun b => ‖f b‖ ^ 2 * lewisCriticalWeight b) (Ioi 1) :=
    hf.mono_set (Ioi_subset_Ioi zero_le_one)
  have hintU1 : IntegrableOn (fun b => ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1)) (Ioi 1) := by
    have hcont_rat : ContinuousOn
        (fun b : ℝ => lewisCriticalWeight (b - 1) / lewisCriticalWeight b) (Ioi 1) := by
      intro b hb
      have hb0 : 0 < b := zero_lt_one.trans hb
      have hb1 : 0 < b - 1 := sub_pos.mpr hb
      have hc1 : ContinuousAt (fun x : ℝ => lewisCriticalWeight (x - 1)) b :=
        ContinuousAt.comp (g := lewisCriticalWeight) (f := fun x : ℝ => x - 1)
          (lewisCriticalWeight_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hb1))
          (continuousAt_id.sub continuousAt_const)
      have hc2 : ContinuousAt lewisCriticalWeight b :=
        lewisCriticalWeight_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hb0)
      exact (hc1.div hc2 (lewisCriticalWeight_pos hb0).ne').continuousWithinAt
    have hasm : AEStronglyMeasurable
        (fun b : ℝ => ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1)) (volume.restrict (Ioi 1)) := by
      refine (hf1.aestronglyMeasurable.mul
        (hcont_rat.aestronglyMeasurable measurableSet_Ioi)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
      have hwb : lewisCriticalWeight b ≠ 0 := (lewisCriticalWeight_pos (zero_lt_one.trans hb)).ne'
      dsimp only [Pi.mul_apply]
      linear_combination ‖f b‖ ^ 2 * div_mul_cancel₀ (lewisCriticalWeight (b - 1)) hwb
    refine (hf1.const_mul ((4 : ℝ) ^ (7 : ℝ))).mono' hasm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
    have hnn : 0 ≤ ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1) :=
      mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos (sub_pos.mpr hb)).le
    rw [Real.norm_of_nonneg hnn]
    calc
      ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1)
          ≤ ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
        mul_le_mul_of_nonneg_left (weight_shift_ratio_bound_Ioi_one hb).2 (sq_nonneg _)
      _ = (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
  have hintU : IntegrableOn (fun a => ‖lewisShift f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) := by
    have himg : (fun a : ℝ => a + 1) '' Ioi (0 : ℝ) = Ioi 1 := by
      ext b; simp only [mem_image, mem_Ioi]
      exact ⟨fun ⟨a, ha, hab⟩ => by linarith, fun hb => ⟨b - 1, by linarith, sub_add_cancel b 1⟩⟩
    have hinj : InjOn (fun a : ℝ => a + 1) (Ioi 0) := fun _ _ _ _ h => add_right_cancel h
    have hderiv : ∀ a ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x + 1) 1 (Ioi 0) a :=
      fun a _ => ((hasDerivAt_id a).add_const 1).hasDerivWithinAt
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
      hinj (fun b : ℝ => ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1))
    rw [himg] at hiff
    exact (hiff.mp hintU1).congr_fun (fun a _ => by simp [lewisShift]) measurableSet_Ioi
  refine ⟨hintU, ?_⟩
  unfold lewisCriticalNormSq lewisShift
  have hshift := integral_Ioi_zero_add_subst 1
    (fun b : ℝ => ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1))
  have hlhs : (∫ a in Ioi (0 : ℝ), ‖f (a + 1)‖ ^ 2 * lewisCriticalWeight a) =
      ∫ b in Ioi (1 : ℝ), ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1) := by
    simpa [add_sub_cancel_right] using hshift
  rw [hlhs]
  have hmono := setIntegral_mono_on hintU1 (hf1.const_mul ((4 : ℝ) ^ (7 : ℝ))) measurableSet_Ioi
    fun b hb => by
      calc
        ‖f b‖ ^ 2 * lewisCriticalWeight (b - 1)
            ≤ ‖f b‖ ^ 2 * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight b) :=
          mul_le_mul_of_nonneg_left (weight_shift_ratio_bound_Ioi_one hb).2 (sq_nonneg _)
        _ = (4 : ℝ) ^ (7 : ℝ) * (‖f b‖ ^ 2 * lewisCriticalWeight b) := by ring
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
  have hle_tot : (∫ b in Ioi (1 : ℝ), ‖f b‖ ^ 2 * lewisCriticalWeight b) ≤
      ∫ a in Ioi (0 : ℝ), ‖f a‖ ^ 2 * lewisCriticalWeight a := by linarith only [hsplit, hrest]
  exact hmono.trans (mul_le_mul_of_nonneg_left hle_tot (by positivity))

private theorem parabolic_weight_kernel_bound {s : ℂ} (hs0 : 0 ≤ s.re)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    (1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)) ≤
      ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) * lewisCriticalWeight c := by
  have hb_gt1 : 1 < c⁻¹ := (one_lt_inv₀ hc.1).mpr hc.2
  have hb0 : 0 < c⁻¹ := zero_lt_one.trans hb_gt1
  have hu : 0 < c⁻¹ - 1 := sub_pos.mpr hb_gt1
  have h1c_pos : 0 < 1 - c := sub_pos.mpr hc.2
  have hcd_eq : c / (1 - c) = (c⁻¹ - 1)⁻¹ := by
    field_simp [hc.1.ne', h1c_pos.ne', hu.ne']
  have h1c_b : 1 - c = (c⁻¹ - 1) / c⁻¹ := by
    field_simp [hc.1.ne', hb0.ne']
  have hw_cd : lewisCriticalWeight (c / (1 - c)) =
      (c⁻¹ - 1) * lewisCriticalWeight (c⁻¹ - 1) := by
    rw [hcd_eq]
    unfold lewisCriticalWeight
    rw [inv_inv, add_comm (c⁻¹ - 1)⁻¹ (c⁻¹ - 1), Real.inv_rpow hu.le, ← Real.rpow_neg hu.le, neg_neg]
    have h1 : ((c⁻¹ - 1) + (c⁻¹ - 1)⁻¹) ^ (-6 : ℝ) * (c⁻¹ - 1) ^ (1 / 2 : ℝ) =
        ((c⁻¹ - 1) + (c⁻¹ - 1)⁻¹) ^ (-6 : ℝ) *
          ((c⁻¹ - 1) ^ (1 : ℝ) * (c⁻¹ - 1) ^ (-(1 / 2 : ℝ))) := by
      rw [← Real.rpow_add hu]; congr 2; norm_num
    rw [h1, Real.rpow_one]; ring
  have hw_c_eq : lewisCriticalWeight c = c⁻¹ * lewisCriticalWeight c⁻¹ := by
    unfold lewisCriticalWeight
    rw [inv_inv, add_comm c⁻¹ c, Real.inv_rpow hc.1.le, ← Real.rpow_neg hc.1.le, neg_neg]
    have h1 : c⁻¹ * ((c + c⁻¹) ^ (-6 : ℝ) * c ^ (1 / 2 : ℝ)) =
        (c + c⁻¹) ^ (-6 : ℝ) * (c⁻¹ * c ^ (1 / 2 : ℝ)) := by ring
    have h2 : c⁻¹ * c ^ (1 / 2 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hc.1]
      congr 1; norm_num
    rw [h1, h2]
  have hker_eq : (1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)) =
      ((c⁻¹ - 1) / c⁻¹) ^ (4 * s.re - 1) * (c⁻¹ * lewisCriticalWeight (c⁻¹ - 1)) := by
    rw [hw_cd, h1c_b, Real.div_rpow hu.le hb0.le, Real.div_rpow hu.le hb0.le]
    have h1 : (c⁻¹ - 1) ^ (4 * s.re - 1) = (c⁻¹ - 1) ^ (4 * s.re - 2) * (c⁻¹ - 1) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hu]; congr 1; ring
    have h2 : (c⁻¹) ^ (4 * s.re - 1) = (c⁻¹) ^ (4 * s.re - 2) * (c⁻¹) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hb0]; congr 1; ring
    rw [h1, h2, Real.rpow_one, Real.rpow_one]
    have hp_ne : (c⁻¹) ^ (4 * s.re - 2) ≠ 0 := (Real.rpow_pos_of_pos hb0 _).ne'
    field_simp [hp_ne, hb0.ne', hc.1.ne']
  by_cases hb2 : c⁻¹ ≤ 2
  · have hu_le1 : c⁻¹ - 1 ≤ 1 := by linarith
    have hu6 : ((c⁻¹ - 1) + (c⁻¹ - 1)⁻¹) ^ (-6 : ℝ) ≤ (c⁻¹ - 1) ^ (6 : ℝ) := by
      calc
        ((c⁻¹ - 1) + (c⁻¹ - 1)⁻¹) ^ (-6 : ℝ) ≤ ((c⁻¹ - 1)⁻¹) ^ (-6 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hu) (by linarith) (by norm_num)
        _ = (c⁻¹ - 1) ^ (6 : ℝ) := by
          rw [Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]; norm_num
    have hnum_le : (c⁻¹ - 1) ^ (4 * s.re - 1) * lewisCriticalWeight (c⁻¹ - 1) ≤ 1 := by
      unfold lewisCriticalWeight
      calc
        (c⁻¹ - 1) ^ (4 * s.re - 1) *
            (((c⁻¹ - 1) + (c⁻¹ - 1)⁻¹) ^ (-6 : ℝ) * (c⁻¹ - 1) ^ (-(1 / 2 : ℝ)))
            ≤ (c⁻¹ - 1) ^ (4 * s.re - 1) * ((c⁻¹ - 1) ^ (6 : ℝ) * (c⁻¹ - 1) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hu6 (by positivity)) (by positivity)
        _ = (c⁻¹ - 1) ^ (4 * s.re - 1) * (c⁻¹ - 1) ^ (6 : ℝ) * (c⁻¹ - 1) ^ (-(1 / 2 : ℝ)) := by ring
        _ = (c⁻¹ - 1) ^ (4 * s.re + 9 / 2) := by
          rw [← Real.rpow_add hu, ← Real.rpow_add hu]; congr 1; ring
        _ ≤ 1 := Real.rpow_le_one hu.le hu_le1 (by linarith)
    have hinv_b : ((c⁻¹) ^ (4 * s.re - 1))⁻¹ = (c⁻¹) ^ (1 - 4 * s.re) := by
      rw [← Real.rpow_neg hb0.le, show -(4 * s.re - 1) = 1 - 4 * s.re by ring]
    have hb_pow_le : (c⁻¹) ^ (1 - 4 * s.re) ≤ (2 : ℝ) ^ (4 * s.re + 2) := by
      calc
        (c⁻¹) ^ (1 - 4 * s.re) ≤ (c⁻¹) ^ (4 * s.re + 2) :=
          Real.rpow_le_rpow_of_exponent_le hb_gt1.le (by linarith)
        _ ≤ (2 : ℝ) ^ (4 * s.re + 2) :=
          Real.rpow_le_rpow hb0.le hb2 (by linarith)
    have h4w := one_le_four_pow_seven_mul_weight_Ioc_two hb_gt1 hb2
    rw [hker_eq, hw_c_eq, Real.div_rpow hu.le hb0.le]
    calc
      ((c⁻¹ - 1) ^ (4 * s.re - 1) / (c⁻¹) ^ (4 * s.re - 1)) *
          (c⁻¹ * lewisCriticalWeight (c⁻¹ - 1))
          = c⁻¹ * ((c⁻¹) ^ (1 - 4 * s.re) *
              ((c⁻¹ - 1) ^ (4 * s.re - 1) * lewisCriticalWeight (c⁻¹ - 1))) := by
        rw [div_eq_mul_inv, hinv_b]; ring
      _ ≤ c⁻¹ * ((2 : ℝ) ^ (4 * s.re + 2) * 1) := by
        apply mul_le_mul_of_nonneg_left _ hb0.le
        exact mul_le_mul hb_pow_le hnum_le
          (mul_nonneg (Real.rpow_nonneg hu.le _) (lewisCriticalWeight_pos hu).le)
          (Real.rpow_nonneg zero_le_two _)
      _ ≤ c⁻¹ * ((2 : ℝ) ^ (4 * s.re + 2) * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight c⁻¹)) := by
        apply mul_le_mul_of_nonneg_left _ hb0.le
        exact mul_le_mul_of_nonneg_left h4w (Real.rpow_nonneg zero_le_two _)
      _ = ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) * (c⁻¹ * lewisCriticalWeight c⁻¹) := by ring
  · rw [not_le] at hb2
    have hq_pos : 0 < (c⁻¹ - 1) / c⁻¹ := div_pos hu hb0
    have hq_ge : 1 / 2 ≤ (c⁻¹ - 1) / c⁻¹ := by rw [le_div_iff₀ hb0]; linarith
    have hq_le1 : (c⁻¹ - 1) / c⁻¹ ≤ 1 := by rw [div_le_one hb0]; linarith
    have hq_pow : ((c⁻¹ - 1) / c⁻¹) ^ (4 * s.re - 1) ≤ (2 : ℝ) ^ (4 * s.re + 2) := by
      by_cases hexp : 0 ≤ 4 * s.re - 1
      · calc
          ((c⁻¹ - 1) / c⁻¹) ^ (4 * s.re - 1) ≤ 1 := Real.rpow_le_one hq_pos.le hq_le1 hexp
          _ ≤ (2 : ℝ) ^ (4 * s.re + 2) := Real.one_le_rpow (by norm_num) (by linarith)
      · rw [not_le] at hexp
        calc
          ((c⁻¹ - 1) / c⁻¹) ^ (4 * s.re - 1) ≤ (1 / 2 : ℝ) ^ (4 * s.re - 1) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hq_ge hexp.le
          _ = (2 : ℝ) ^ (1 - 4 * s.re) := by
            rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
            congr 1; ring
          _ ≤ (2 : ℝ) ^ (4 * s.re + 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hw_sh := (weight_shift_ratio_bound_Ioi_one hb_gt1).2
    rw [hker_eq, hw_c_eq]
    calc
      ((c⁻¹ - 1) / c⁻¹) ^ (4 * s.re - 1) * (c⁻¹ * lewisCriticalWeight (c⁻¹ - 1))
          ≤ (2 : ℝ) ^ (4 * s.re + 2) * (c⁻¹ * ((4 : ℝ) ^ (7 : ℝ) * lewisCriticalWeight c⁻¹)) := by
        refine mul_le_mul hq_pow ?_ (mul_nonneg hb0.le (lewisCriticalWeight_pos hu).le)
          (Real.rpow_nonneg zero_le_two _)
        exact mul_le_mul_of_nonneg_left hw_sh hb0.le
      _ = ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) * (c⁻¹ * lewisCriticalWeight c⁻¹) := by ring

private def parabolicNormPullback (s : ℂ) (f : ℝ → ℂ) (c : ℝ) : ℝ :=
  ‖f c‖ ^ 2 * ((1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)))

private theorem lewisParabolic_normBounded {s : ℂ} (hs0 : 0 ≤ s.re) {f : ℝ → ℂ}
    (hf : IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)) :
    IntegrableOn (fun a => ‖lewisParabolic s f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
      lewisCriticalNormSq (lewisParabolic s f) ≤
        ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) * lewisCriticalNormSq f := by
  have hcongr_V : ∀ a ∈ Ioi (0 : ℝ),
      ‖lewisParabolic s f a‖ ^ 2 * lewisCriticalWeight a =
        ((a + 1) ^ (-2 : ℝ)) • parabolicNormPullback s f (a / (a + 1)) := by
    intro a ha
    have ha1 : 0 < a + 1 := by linarith [show 0 < a from ha]
    have h1c : 1 - a / (a + 1) = (a + 1)⁻¹ := by field_simp [ha1.ne']; ring
    have hc_div : (a / (a + 1)) / (1 - a / (a + 1)) = a := by rw [h1c]; field_simp [ha1.ne']
    dsimp only [smul_eq_mul, parabolicNormPullback, lewisParabolic]
    rw [norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos ha1, hc_div, h1c]
    have hre : (-(2 * s)).re = -2 * s.re := by simp
    rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul ha1.le, Real.inv_rpow ha1.le,
      ← Real.rpow_neg ha1.le]
    have hcomb : (a + 1) ^ (-2 : ℝ) *
        (‖f (a / (a + 1))‖ ^ 2 * ((a + 1) ^ (-(4 * s.re - 2)) * lewisCriticalWeight a)) =
        ((a + 1) ^ (-2 : ℝ) * (a + 1) ^ (-(4 * s.re - 2))) *
          ‖f (a / (a + 1))‖ ^ 2 * lewisCriticalWeight a := by ring
    rw [hcomb, ← Real.rpow_add ha1]
    congr 2; congr 1; push_cast; ring
  have hf_Ioo : IntegrableOn (fun c => ‖f c‖ ^ 2 * lewisCriticalWeight c) (Ioo 0 1) :=
    hf.mono_set Ioo_subset_Ioi_self
  have hint_HV : IntegrableOn (parabolicNormPullback s f) (Ioo 0 1) := by
    have hcont_rat : ContinuousOn
        (fun c : ℝ => ((1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c))) /
          lewisCriticalWeight c) (Ioo 0 1) := by
      intro c hc
      have h1c : 0 < 1 - c := sub_pos.mpr hc.2
      have hcd : 0 < c / (1 - c) := div_pos hc.1 h1c
      have c1 : ContinuousAt (fun x : ℝ => (1 - x) ^ (4 * s.re - 2)) c :=
        (continuousAt_const.sub continuousAt_id).rpow continuousAt_const (Or.inl h1c.ne')
      have c2 : ContinuousAt (fun x : ℝ => lewisCriticalWeight (x / (1 - x))) c :=
        ContinuousAt.comp (g := lewisCriticalWeight) (f := fun x : ℝ => x / (1 - x))
          (lewisCriticalWeight_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hcd))
          (continuousAt_id.div (continuousAt_const.sub continuousAt_id) h1c.ne')
      have c3 : ContinuousAt lewisCriticalWeight c :=
        lewisCriticalWeight_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hc.1)
      exact ((c1.mul c2).div c3 (lewisCriticalWeight_pos hc.1).ne').continuousWithinAt
    have hasm : AEStronglyMeasurable (parabolicNormPullback s f) (volume.restrict (Ioo 0 1)) := by
      refine (hf_Ioo.aestronglyMeasurable.mul
        (hcont_rat.aestronglyMeasurable measurableSet_Ioo)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with c hc
      have hwc : lewisCriticalWeight c ≠ 0 := (lewisCriticalWeight_pos hc.1).ne'
      unfold parabolicNormPullback
      dsimp only [Pi.mul_apply]
      linear_combination
        ‖f c‖ ^ 2 *
          div_mul_cancel₀ ((1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c))) hwc
    refine (hf_Ioo.const_mul ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2))).mono' hasm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with c hc
    have hnn : 0 ≤ parabolicNormPullback s f c :=
      mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_pos_of_pos (sub_pos.mpr hc.2) _).le
          (lewisCriticalWeight_pos (div_pos hc.1 (sub_pos.mpr hc.2))).le)
    rw [Real.norm_of_nonneg hnn]
    unfold parabolicNormPullback
    calc
      ‖f c‖ ^ 2 * ((1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)))
          ≤ ‖f c‖ ^ 2 * (((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) * lewisCriticalWeight c) :=
        mul_le_mul_of_nonneg_left (parabolic_weight_kernel_bound hs0 hc) (sq_nonneg _)
      _ = ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) *
            (‖f c‖ ^ 2 * lewisCriticalWeight c) := by ring
  have hintV :
      IntegrableOn (fun a => ‖lewisParabolic s f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) := by
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun _ ha => hasDerivWithinAt_mobius_Ioi_zero ha) injOn_mobius_Ioi_zero
      (parabolicNormPullback s f)
    rw [image_mobius_Ioi_zero] at hiff
    refine (hiff.mp hint_HV).congr_fun (fun a ha => ?_) measurableSet_Ioi
    rw [hcongr_V a ha]
    have ha1 : 0 < a + 1 := by linarith [show 0 < a from ha]
    have habs : |((a + 1) ^ 2)⁻¹| = (a + 1) ^ (-2 : ℝ) := by
      rw [abs_of_pos (by positivity), Real.rpow_neg ha1.le, Real.rpow_two]
    simp [habs]
  refine ⟨hintV, ?_⟩
  have heq_V : lewisCriticalNormSq (lewisParabolic s f) =
      ∫ c in Ioo (0 : ℝ) 1, parabolicNormPullback s f c := by
    unfold lewisCriticalNormSq
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr_V, ← integral_Ioi_zero_mobius_subst]
  rw [heq_V]
  have hmono := setIntegral_mono_on hint_HV
    (hf_Ioo.const_mul ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2))) measurableSet_Ioo
    fun c hc => by
      unfold parabolicNormPullback
      calc
        ‖f c‖ ^ 2 * ((1 - c) ^ (4 * s.re - 2) * lewisCriticalWeight (c / (1 - c)))
            ≤ ‖f c‖ ^ 2 *
                (((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) * lewisCriticalWeight c) :=
          mul_le_mul_of_nonneg_left (parabolic_weight_kernel_bound hs0 hc) (sq_nonneg _)
        _ = ((4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)) *
              (‖f c‖ ^ 2 * lewisCriticalWeight c) := by ring
  rw [integral_const_mul] at hmono
  have hsub_le : ∫ c in Ioo (0 : ℝ) 1, ‖f c‖ ^ 2 * lewisCriticalWeight c ≤
      lewisCriticalNormSq f := by
    unfold lewisCriticalNormSq
    have hunion : Ioi (0 : ℝ) = Ioo 0 1 ∪ (Ioi 0 \ Ioo 0 1) :=
      (Set.union_sdiff_cancel Ioo_subset_Ioi_self).symm
    conv_rhs => rw [hunion]
    rw [setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Ioo)
      hf_Ioo (hf.mono_set Set.sdiff_subset)]
    have hrest : 0 ≤ ∫ c in Ioi 0 \ Ioo 0 1, ‖f c‖ ^ 2 * lewisCriticalWeight c :=
      setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioo) fun c hc =>
        mul_nonneg (sq_nonneg _) (lewisCriticalWeight_pos hc.1).le
    linarith
  exact hmono.trans (mul_le_mul_of_nonneg_left hsub_le (by positivity))

/-- Norm-boundedness of `lewisFarey s` on `H_LP` across `s.re ≥ 0`. -/
theorem lewisFarey_normBounded {s : ℂ} (hs0 : 0 ≤ s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ,
      IntegrableOn (fun a => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) →
        lewisCriticalNormSq (lewisFarey s f) ≤ C * lewisCriticalNormSq f := by
  refine ⟨2 * ((4 : ℝ) ^ (7 : ℝ) + (4 : ℝ) ^ (7 : ℝ) * (2 : ℝ) ^ (4 * s.re + 2)),
    by positivity, fun f hf => ?_⟩
  obtain ⟨hintU, hU_bound⟩ := lewisShift_normBounded hf
  obtain ⟨hintV, hV_bound⟩ := lewisParabolic_normBounded hs0 hf
  by_cases hintM :
      IntegrableOn (fun a => ‖lewisFarey s f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0)
  · have hmono := setIntegral_mono_on hintM ((hintU.add hintV).const_mul 2) measurableSet_Ioi
      fun a ha => by
        have htri : ‖lewisFarey s f a‖ ≤ ‖lewisShift f a‖ + ‖lewisParabolic s f a‖ :=
          norm_add_le _ _
        have hsq1 : ‖lewisFarey s f a‖ ^ 2 ≤ (‖lewisShift f a‖ + ‖lewisParabolic s f a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        have hsq2 : (‖lewisShift f a‖ + ‖lewisParabolic s f a‖) ^ 2 ≤
            2 * (‖lewisShift f a‖ ^ 2 + ‖lewisParabolic s f a‖ ^ 2) := by
          have hsos : 2 * (‖lewisShift f a‖ ^ 2 + ‖lewisParabolic s f a‖ ^ 2) -
              (‖lewisShift f a‖ + ‖lewisParabolic s f a‖) ^ 2 =
              (‖lewisShift f a‖ - ‖lewisParabolic s f a‖) ^ 2 := by ring
          linarith [hsos, sq_nonneg (‖lewisShift f a‖ - ‖lewisParabolic s f a‖)]
        have hw_nn : 0 ≤ lewisCriticalWeight a := (lewisCriticalWeight_pos ha).le
        simp only [Pi.add_apply]
        calc
          ‖lewisFarey s f a‖ ^ 2 * lewisCriticalWeight a
              ≤ (2 * (‖lewisShift f a‖ ^ 2 + ‖lewisParabolic s f a‖ ^ 2)) *
                  lewisCriticalWeight a :=
            mul_le_mul_of_nonneg_right (hsq1.trans hsq2) hw_nn
          _ = 2 * (‖lewisShift f a‖ ^ 2 * lewisCriticalWeight a +
                ‖lewisParabolic s f a‖ ^ 2 * lewisCriticalWeight a) := by ring
    rw [integral_const_mul] at hmono
    simp only [Pi.add_apply] at hmono
    rw [integral_add hintU hintV] at hmono
    change lewisCriticalNormSq (lewisFarey s f) ≤
      2 * (lewisCriticalNormSq (lewisShift f) + lewisCriticalNormSq (lewisParabolic s f)) at hmono
    linarith
  · rw [lewisCriticalNormSq, integral_undef hintM]
    exact mul_nonneg (mul_nonneg zero_le_two
      (add_nonneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg zero_le_two _))))
      (lewisCriticalNormSq_nonneg f)

private def parabolicAdjNormDensity (s : ℂ) (g : ℝ → ℂ) (c : ℝ) : ℝ :=
  (1 - c) ^ (4 * s.re - 4) *
    (lewisCriticalWeight (c / (1 - c)) / lewisCriticalWeight c) *
    ‖g (c / (1 - c))‖ ^ 2 * lewisCriticalWeight (c / (1 - c))

private theorem integrableOn_and_normSq_fareyAdj (s : ℂ) (g : ℝ → ℂ)
    (hg_adj : IntegrableOn (fun x => ‖lewisFareyAdj s g x‖ ^ 2 * lewisCriticalWeight x) (Ioi 0)) :
    IntegrableOn (fun a => lewisFareyMultiplier s a * ‖g a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
      lewisCriticalNormSq (lewisFareyAdj s g) =
        ∫ a in Ioi (0 : ℝ), lewisFareyMultiplier s a * ‖g a‖ ^ 2 * lewisCriticalWeight a := by
  have hpt_split : ∀ x : ℝ,
      ‖lewisFareyAdj s g x‖ ^ 2 * lewisCriticalWeight x =
        ‖lewisShiftAdj g x‖ ^ 2 * lewisCriticalWeight x +
          ‖lewisParabolicAdj s g x‖ ^ 2 * lewisCriticalWeight x := by
    intro x
    unfold lewisFareyAdj
    by_cases hx : 1 < x
    · have hnot : x ∉ Ioo (0 : ℝ) 1 := fun hm => by linarith [hm.2]
      simp [lewisParabolicAdj, hnot]
    · simp [lewisShiftAdj, hx]
  have hind_U : (fun x : ℝ => ‖lewisShiftAdj g x‖ ^ 2 * lewisCriticalWeight x) =
      (Ioi (1 : ℝ)).indicator (fun x => ‖lewisFareyAdj s g x‖ ^ 2 * lewisCriticalWeight x) := by
    ext x
    by_cases hx : 1 < x
    · have hnot : x ∉ Ioo (0 : ℝ) 1 := fun hm => by linarith [hm.2]
      have hxm : x ∈ Ioi (1 : ℝ) := hx
      rw [indicator_of_mem hxm]
      unfold lewisFareyAdj lewisParabolicAdj
      rw [if_neg hnot, add_zero]
    · simp [lewisShiftAdj, hx, mem_Ioi]
  have hind_V : (fun x : ℝ => ‖lewisParabolicAdj s g x‖ ^ 2 * lewisCriticalWeight x) =
      (Ioo (0 : ℝ) 1).indicator (fun x => ‖lewisFareyAdj s g x‖ ^ 2 * lewisCriticalWeight x) := by
    ext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · have hnot : ¬ (1 < x) := by linarith [hx.2]
      simp [lewisFareyAdj, lewisShiftAdj, hx, hnot]
    · simp [lewisParabolicAdj, hx]
  have hint_U : IntegrableOn (fun x => ‖lewisShiftAdj g x‖ ^ 2 * lewisCriticalWeight x) (Ioi 0) := by
    rw [hind_U, integrableOn_indicator_iff measurableSet_Ioi,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi zero_le_one)]
    exact hg_adj.mono_set (Ioi_subset_Ioi zero_le_one)
  have hint_V :
      IntegrableOn (fun x => ‖lewisParabolicAdj s g x‖ ^ 2 * lewisCriticalWeight x) (Ioi 0) := by
    rw [hind_V, integrableOn_indicator_iff measurableSet_Ioo,
      inter_eq_self_of_subset_left Ioo_subset_Ioi_self]
    exact hg_adj.mono_set Ioo_subset_Ioi_self
  have hsum_adj : lewisCriticalNormSq (lewisFareyAdj s g) =
      (∫ x in Ioi (0 : ℝ), ‖lewisShiftAdj g x‖ ^ 2 * lewisCriticalWeight x) +
        ∫ x in Ioi (0 : ℝ), ‖lewisParabolicAdj s g x‖ ^ 2 * lewisCriticalWeight x := by
    unfold lewisCriticalNormSq
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt_split x), integral_add hint_U hint_V]
  have hU_eq : (∫ x in Ioi (0 : ℝ), ‖lewisShiftAdj g x‖ ^ 2 * lewisCriticalWeight x) =
      ∫ a in Ioi (0 : ℝ),
        (lewisCriticalWeight a / lewisCriticalWeight (a + 1)) * ‖g a‖ ^ 2 * lewisCriticalWeight a := by
    have h1 : (fun x : ℝ => ‖lewisShiftAdj g x‖ ^ 2 * lewisCriticalWeight x) =
        (Ioi (1 : ℝ)).indicator (fun b =>
          (lewisCriticalWeight (b - 1) / lewisCriticalWeight b) * ‖g (b - 1)‖ ^ 2 *
            lewisCriticalWeight (b - 1)) := by
      ext b
      by_cases hb : 1 < b
      · have hb0 : 0 < b := zero_lt_one.trans hb
        have hb1 : 0 < b - 1 := sub_pos.mpr hb
        have hwb : lewisCriticalWeight b ≠ 0 := (lewisCriticalWeight_pos hb0).ne'
        have hbm : b ∈ Ioi (1 : ℝ) := hb
        rw [indicator_of_mem hbm]
        unfold lewisShiftAdj
        rw [if_pos hb, norm_mul, mul_pow, Complex.norm_real,
          Real.norm_of_nonneg (div_pos (lewisCriticalWeight_pos hb1) (lewisCriticalWeight_pos hb0)).le]
        field_simp [hwb]
      · simp [lewisShiftAdj, hb, mem_Ioi]
    rw [h1, setIntegral_indicator measurableSet_Ioi,
      inter_eq_self_of_subset_right (Ioi_subset_Ioi zero_le_one),
      ← integral_Ioi_zero_add_subst 1]
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
    simp [add_sub_cancel_right]
  have hint_m1 : IntegrableOn
      (fun a => (lewisCriticalWeight a / lewisCriticalWeight (a + 1)) *
        ‖g a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) := by
    have himg : (fun a : ℝ => a + 1) '' Ioi (0 : ℝ) = Ioi 1 := by
      ext b; simp only [mem_image, mem_Ioi]
      exact ⟨fun ⟨a, ha, hab⟩ => by linarith, fun hb => ⟨b - 1, by linarith, sub_add_cancel b 1⟩⟩
    have hinj : InjOn (fun a : ℝ => a + 1) (Ioi 0) := fun _ _ _ _ h => add_right_cancel h
    have hderiv : ∀ a ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x + 1) 1 (Ioi 0) a :=
      fun a _ => ((hasDerivAt_id a).add_const 1).hasDerivWithinAt
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj
      (fun b => ‖lewisShiftAdj g b‖ ^ 2 * lewisCriticalWeight b)
    rw [himg] at hiff
    refine (hiff.mp (hint_U.mono_set (Ioi_subset_Ioi zero_le_one))).congr_fun (fun a ha => ?_)
      measurableSet_Ioi
    have ha1_gt1 : 1 < a + 1 := by linarith [show 0 < a from ha]
    have ha1_pos : 0 < a + 1 := by linarith [show 0 < a from ha]
    have hwa1 : lewisCriticalWeight (a + 1) ≠ 0 := (lewisCriticalWeight_pos ha1_pos).ne'
    simp only [abs_one, one_smul, lewisShiftAdj, if_pos ha1_gt1, add_sub_cancel_right,
      norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (div_pos (lewisCriticalWeight_pos ha) (lewisCriticalWeight_pos ha1_pos)).le]
    field_simp [hwa1]
  have hFV_ind : (fun x : ℝ => ‖lewisParabolicAdj s g x‖ ^ 2 * lewisCriticalWeight x) =
      (Ioo (0 : ℝ) 1).indicator (parabolicAdjNormDensity s g) := by
    ext c
    by_cases hc : c ∈ Ioo (0 : ℝ) 1
    · have h1c : 0 < 1 - c := sub_pos.mpr hc.2
      have hcd : 0 < c / (1 - c) := div_pos hc.1 h1c
      have hwc : lewisCriticalWeight c ≠ 0 := (lewisCriticalWeight_pos hc.1).ne'
      have hpow_1c : ‖((1 - c : ℝ) : ℂ) ^ (2 * (starRingEnd ℂ) s - 2)‖ ^ 2 =
          (1 - c) ^ (4 * s.re - 4) := by
        have hre : (2 * (starRingEnd ℂ) s - 2).re = 2 * s.re - 2 := by simp
        rw [Complex.norm_cpow_eq_rpow_re_of_pos h1c, hre, ← Real.rpow_natCast,
          ← Real.rpow_mul h1c.le]
        congr 1; push_cast; ring
      rw [indicator_of_mem hc]
      unfold lewisParabolicAdj parabolicAdjNormDensity
      rw [if_pos hc, norm_mul, norm_mul, mul_pow, mul_pow, hpow_1c, Complex.norm_real,
        Real.norm_of_nonneg (div_pos (lewisCriticalWeight_pos hcd) (lewisCriticalWeight_pos hc.1)).le]
      field_simp [hwc]
    · simp [lewisParabolicAdj, hc]
  have hFV_mob : ∀ a ∈ Ioi (0 : ℝ),
      ((a + 1) ^ (-2 : ℝ)) • parabolicAdjNormDensity s g (a / (a + 1)) =
        (a + 1) ^ (2 - 4 * s.re) * (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) *
          ‖g a‖ ^ 2 * lewisCriticalWeight a := by
    intro a ha
    have ha1 : 0 < a + 1 := by linarith [show 0 < a from ha]
    have h1c : 1 - a / (a + 1) = (a + 1)⁻¹ := by field_simp [ha1.ne']; ring
    have hc_div : (a / (a + 1)) / (1 - a / (a + 1)) = a := by rw [h1c]; field_simp [ha1.ne']
    dsimp only [smul_eq_mul, parabolicAdjNormDensity]
    rw [hc_div, h1c, Real.inv_rpow ha1.le, ← Real.rpow_neg ha1.le]
    have hcomb : (a + 1) ^ (-2 : ℝ) *
        ((a + 1) ^ (-(4 * s.re - 4)) *
          (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) *
          ‖g a‖ ^ 2 * lewisCriticalWeight a) =
        ((a + 1) ^ (-2 : ℝ) * (a + 1) ^ (-(4 * s.re - 4))) *
          (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) *
          ‖g a‖ ^ 2 * lewisCriticalWeight a := by ring
    rw [hcomb, ← Real.rpow_add ha1]
    congr 3; congr 1; ring
  have hV_eq : (∫ x in Ioi (0 : ℝ), ‖lewisParabolicAdj s g x‖ ^ 2 * lewisCriticalWeight x) =
      ∫ a in Ioi (0 : ℝ),
        (a + 1) ^ (2 - 4 * s.re) * (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) *
          ‖g a‖ ^ 2 * lewisCriticalWeight a := by
    rw [hFV_ind, setIntegral_indicator measurableSet_Ioo,
      inter_eq_self_of_subset_right Ioo_subset_Ioi_self, integral_Ioi_zero_mobius_subst]
    exact setIntegral_congr_fun measurableSet_Ioi hFV_mob
  have hint_m2 : IntegrableOn
      (fun a => (a + 1) ^ (2 - 4 * s.re) *
        (lewisCriticalWeight a / lewisCriticalWeight (a / (a + 1))) *
        ‖g a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) := by
    have hint_FV : IntegrableOn (parabolicAdjNormDensity s g) (Ioo 0 1) := by
      have h := hint_V
      rwa [hFV_ind, integrableOn_indicator_iff measurableSet_Ioo,
        inter_eq_self_of_subset_left Ioo_subset_Ioi_self] at h
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun _ ha => hasDerivWithinAt_mobius_Ioi_zero ha) injOn_mobius_Ioi_zero
      (parabolicAdjNormDensity s g)
    rw [image_mobius_Ioi_zero] at hiff
    refine (hiff.mp hint_FV).congr_fun (fun a ha => ?_) measurableSet_Ioi
    rw [← hFV_mob a ha]
    have ha1 : 0 < a + 1 := by linarith [show 0 < a from ha]
    have habs : |((a + 1) ^ 2)⁻¹| = (a + 1) ^ (-2 : ℝ) := by
      rw [abs_of_pos (by positivity), Real.rpow_neg ha1.le, Real.rpow_two]
    simp [habs]
  have hint_tot : IntegrableOn
      (fun a => lewisFareyMultiplier s a * ‖g a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) :=
    (hint_m1.add hint_m2).congr_fun (fun a _ => by
      unfold lewisFareyMultiplier; simp only [Pi.add_apply]; ring) measurableSet_Ioi
  refine ⟨hint_tot, ?_⟩
  rw [hsum_adj, hU_eq, hV_eq, ← integral_add hint_m1 hint_m2]
  refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
  unfold lewisFareyMultiplier
  ring

/-- Exact squared-norm identity `‖M_s† g‖_LP² = ∫_0^∞ μ_s(a) ‖g(a)‖² w_LP(a) da` on `H_LP`. -/
theorem lewisCriticalNormSq_fareyAdj (s : ℂ) (g : ℝ → ℂ)
    (hg_adj : IntegrableOn (fun x => ‖lewisFareyAdj s g x‖ ^ 2 * lewisCriticalWeight x) (Ioi 0)) :
    lewisCriticalNormSq (lewisFareyAdj s g) =
      ∫ a in Ioi (0 : ℝ), lewisFareyMultiplier s a * ‖g a‖ ^ 2 * lewisCriticalWeight a :=
  (integrableOn_and_normSq_fareyAdj s g hg_adj).2

/-- **Strict Self-Commutator Negativity on Continuous Three-Term Fixed Points (`s.re ≤ 1/2`).**
Because `M_s M_s† = μ_s > 1` everywhere on `(0, ∞)`, every nonzero continuous three-term fixed
point `M_s ψ = ψ` in `H_LP` with `M_s† ψ ∈ H_LP` satisfies
`lewisCriticalNormSq (M_s ψ) - lewisCriticalNormSq (M_s† ψ) < 0`. -/
theorem lewisFarey_selfCommutator_neg_of_fixed {s : ℂ} (hs : s.re ≤ 1 / 2) {ψ : ℝ → ℂ}
    (hψ_cont : ContinuousOn ψ (Ioi 0))
    (hψ_ne : ∃ a₀ > 0, ψ a₀ ≠ 0)
    (hψ_int : IntegrableOn (fun a => ‖ψ a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0))
    (hψ_adj_int : IntegrableOn (fun x => ‖lewisFareyAdj s ψ x‖ ^ 2 * lewisCriticalWeight x) (Ioi 0))
    (hfix : ∀ a > 0, lewisFarey s ψ a = ψ a) :
    lewisCriticalNormSq (lewisFarey s ψ) - lewisCriticalNormSq (lewisFareyAdj s ψ) < 0 := by
  have hnorm_fix : lewisCriticalNormSq (lewisFarey s ψ) = lewisCriticalNormSq ψ := by
    unfold lewisCriticalNormSq
    exact setIntegral_congr_fun measurableSet_Ioi fun a ha => by rw [hfix a ha]
  obtain ⟨hint_mu, heq_adj⟩ := integrableOn_and_normSq_fareyAdj s ψ hψ_adj_int
  rw [hnorm_fix, heq_adj]
  unfold lewisCriticalNormSq
  have hdiff_eq : (∫ a in Ioi (0 : ℝ), ‖ψ a‖ ^ 2 * lewisCriticalWeight a) -
      (∫ a in Ioi (0 : ℝ), lewisFareyMultiplier s a * ‖ψ a‖ ^ 2 * lewisCriticalWeight a) =
      -∫ a in Ioi (0 : ℝ), (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a := by
    rw [← integral_sub hψ_int hint_mu, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
    ring
  rw [hdiff_eq, Left.neg_neg_iff]
  have hint_K : IntegrableOn
      (fun a => (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) :=
    (hint_mu.sub hψ_int).congr_fun (fun a _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_Ioi
  have hcont_mu : ContinuousOn (lewisFareyMultiplier s) (Ioi 0) := by
    intro a ha
    have ha0 : 0 < a := ha
    have ha1 : 0 < a + 1 := by linarith
    have hc_pos : 0 < a / (a + 1) := div_pos ha0 ha1
    have cw0 : ContinuousAt lewisCriticalWeight a :=
      lewisCriticalWeight_continuousOn.continuousAt (isOpen_Ioi.mem_nhds ha0)
    have cw1 : ContinuousAt (fun x : ℝ => lewisCriticalWeight (x + 1)) a :=
      ContinuousAt.comp (g := lewisCriticalWeight) (f := fun x : ℝ => x + 1)
        (lewisCriticalWeight_continuousOn.continuousAt (isOpen_Ioi.mem_nhds ha1))
        (continuousAt_id.add continuousAt_const)
    have cw2 : ContinuousAt (fun x : ℝ => lewisCriticalWeight (x / (x + 1))) a :=
      ContinuousAt.comp (g := lewisCriticalWeight) (f := fun x : ℝ => x / (x + 1))
        (lewisCriticalWeight_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hc_pos))
        (continuousAt_id.div (continuousAt_id.add continuousAt_const) ha1.ne')
    have cp : ContinuousAt (fun x : ℝ => (x + 1) ^ (2 - 4 * s.re)) a :=
      (continuousAt_id.add continuousAt_const).rpow continuousAt_const (Or.inl ha1.ne')
    unfold lewisFareyMultiplier
    exact ((cw0.div cw1 (lewisCriticalWeight_pos ha1).ne').add
      (cp.mul (cw0.div cw2 (lewisCriticalWeight_pos hc_pos).ne'))).continuousWithinAt
  have hcont_K : ContinuousOn
      (fun a => (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) :=
    (((hcont_mu.sub continuousOn_const).mul (hψ_cont.norm.pow 2)).mul
      lewisCriticalWeight_continuousOn)
  obtain ⟨a₀, ha₀, hne₀⟩ := hψ_ne
  have hc0 : 0 < ‖ψ a₀‖ := norm_pos_iff.mpr hne₀
  have hnorm_cont : ContinuousAt (fun x : ℝ => ‖ψ x‖) a₀ :=
    (hψ_cont.continuousAt (isOpen_Ioi.mem_nhds ha₀)).norm
  obtain ⟨r, hr_pos, hball⟩ := Metric.continuousAt_iff.mp hnorm_cont (‖ψ a₀‖ / 2) (half_pos hc0)
  have hp_pos : 0 < max (a₀ / 2) (a₀ - r / 2) := lt_max_of_lt_left (half_pos ha₀)
  have hp_lt_a₀ : max (a₀ / 2) (a₀ - r / 2) < a₀ := max_lt (half_lt_self ha₀) (by linarith)
  have hp_lt_q : max (a₀ / 2) (a₀ - r / 2) < a₀ + r / 2 := by linarith
  obtain ⟨x₀, hx₀, hminK⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hp_lt_q.le)
    (hcont_K.mono (fun x hx => lt_of_lt_of_le hp_pos hx.1))
  have hx₀_pos : 0 < x₀ := lt_of_lt_of_le hp_pos hx₀.1
  have hx₀_dist : dist x₀ a₀ < r := by
    rw [Real.dist_eq, abs_lt]
    have hp2 : a₀ - r / 2 ≤ max (a₀ / 2) (a₀ - r / 2) := le_max_right _ _
    have hx_le : x₀ ≤ a₀ + r / 2 := hx₀.2
    exact ⟨by linarith [hx₀.1], by linarith⟩
  have hx₀_ψ_pos : 0 < ‖ψ x₀‖ := by
    have hb := abs_lt.mp (by simpa [Real.dist_eq] using hball hx₀_dist)
    linarith
  have hKx₀_pos : 0 < (lewisFareyMultiplier s x₀ - 1) * ‖ψ x₀‖ ^ 2 * lewisCriticalWeight x₀ :=
    mul_pos (mul_pos (sub_pos.mpr (one_lt_lewisFareyMultiplier hs hx₀_pos))
      (sq_pos_of_pos hx₀_ψ_pos)) (lewisCriticalWeight_pos hx₀_pos)
  have hsub : Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2) ⊆ Ioi 0 := fun x hx => hp_pos.trans hx.1
  have hunion : Ioi (0 : ℝ) = Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2) ∪
      (Ioi 0 \ Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2)) := (Set.union_sdiff_cancel hsub).symm
  have hsplit : (∫ a in Ioi (0 : ℝ),
      (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a) =
      (∫ a in Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2),
        (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a) +
      ∫ a in Ioi 0 \ Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2),
        (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a := by
    conv_lhs => rw [hunion]
    exact setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Ioc)
      (hint_K.mono_set hsub) (hint_K.mono_set Set.sdiff_subset)
  have hrest : 0 ≤ ∫ a in Ioi 0 \ Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2),
      (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a :=
    setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioc) fun a ha =>
      mul_nonneg (mul_nonneg (sub_pos.mpr (one_lt_lewisFareyMultiplier hs ha.1)).le (sq_nonneg _))
        (lewisCriticalWeight_pos ha.1).le
  have hlow : ((a₀ + r / 2) - max (a₀ / 2) (a₀ - r / 2)) *
      ((lewisFareyMultiplier s x₀ - 1) * ‖ψ x₀‖ ^ 2 * lewisCriticalWeight x₀) ≤
      ∫ a in Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2),
        (lewisFareyMultiplier s a - 1) * ‖ψ a‖ ^ 2 * lewisCriticalWeight a := by
    have hc : (∫ _ in Ioc (max (a₀ / 2) (a₀ - r / 2)) (a₀ + r / 2),
        (lewisFareyMultiplier s x₀ - 1) * ‖ψ x₀‖ ^ 2 * lewisCriticalWeight x₀) =
        ((a₀ + r / 2) - max (a₀ / 2) (a₀ - r / 2)) *
          ((lewisFareyMultiplier s x₀ - 1) * ‖ψ x₀‖ ^ 2 * lewisCriticalWeight x₀) := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hp_lt_q.le, smul_eq_mul]
    rw [← hc]
    exact setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      (hint_K.mono_set hsub) measurableSet_Ioc fun a ha => hminK ⟨ha.1.le, ha.2⟩
  linarith [mul_pos (sub_pos.mpr hp_lt_q) hKx₀_pos]

/-! ## Part 4: Universal Manin–Mühlenbruch Hecke `T_{2,s}` intertwining on `(0, ∞)` -/

/-- The Manin–Mühlenbruch period Hecke operator `T_{2,s}` on `(0, ∞)`. -/
def lewisHeckeT2 (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  f (2 * a) + (2 : ℂ) ^ (-(2 * s)) * f (a / 2) +
    (2 : ℂ) ^ (-(2 * s)) * f ((a + 1) / 2) +
    ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * f (2 * a / (a + 1))

/-- The companion Farey–Hecke operator `T̃_{2,s}` intertwining `(1 - M_s)`. -/
def lewisHeckeT2Companion (s : ℂ) (g : ℝ → ℂ) (a : ℝ) : ℂ :=
  g (2 * a) + (2 : ℂ) ^ (-(2 * s)) * g (a / 2) +
    g (2 * a + 1) + ((a + 2 : ℝ) : ℂ) ^ (-(2 * s)) * g (a / (a + 2))

private theorem ofReal_mul_cpow_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    ((x * y : ℝ) : ℂ) ^ z = (x : ℂ) ^ z * (y : ℂ) ^ z := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le hy.le]

private theorem ofReal_div_cpow_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    ((x / y : ℝ) : ℂ) ^ z = (x : ℂ) ^ z * (y : ℂ) ^ (-z) := by
  rw [div_eq_mul_inv, ofReal_mul_cpow_pos hx (inv_pos.mpr hy), ofReal_inv_cpow_pos hy]

/-- **Universal Modular-Inversion Commutation `I_s (T_{2,s} f) = T_{2,s} (I_s f)` on `(0, ∞)`.** -/
theorem lewisModularInversion_heckeT2 (s : ℂ) (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (lewisHeckeT2 s f) a =
      lewisHeckeT2 s (lewisModularInversion s f) a := by
  have ha1 : 0 < a + 1 := by linarith
  have ha_inv : 0 < a⁻¹ := inv_pos.mpr ha
  have ha_inv1 : 0 < a⁻¹ + 1 := by linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  unfold lewisModularInversion lewisHeckeT2
  dsimp only
  have hp_2a : ((2 * a : ℝ) : ℂ) ^ (-(2 * s)) = (2 : ℂ) ^ (-(2 * s)) * (a : ℂ) ^ (-(2 * s)) := by
    simpa using ofReal_mul_cpow_pos h2pos ha (-(2 * s))
  have hp_a2 : ((a / 2 : ℝ) : ℂ) ^ (-(2 * s)) = (a : ℂ) ^ (-(2 * s)) * (2 : ℂ) ^ (2 * s) := by
    simpa using ofReal_div_cpow_pos ha h2pos (-(2 * s))
  have hp_a1_2 : (((a + 1) / 2 : ℝ) : ℂ) ^ (-(2 * s)) =
      ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * (2 : ℂ) ^ (2 * s) := by
    simpa using ofReal_div_cpow_pos ha1 h2pos (-(2 * s))
  have hp_2a_a1 : ((2 * a / (a + 1) : ℝ) : ℂ) ^ (-(2 * s)) =
      (2 : ℂ) ^ (-(2 * s)) * (a : ℂ) ^ (-(2 * s)) * ((a + 1 : ℝ) : ℂ) ^ (2 * s) := by
    rw [ofReal_div_cpow_pos (mul_pos h2pos ha) ha1, ofReal_mul_cpow_pos h2pos ha, neg_neg]
    simp
  have hp_ainv1 : (a : ℂ) ^ (-(2 * s)) * ((a⁻¹ + 1 : ℝ) : ℂ) ^ (-(2 * s)) =
      ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) := by
    rw [← ofReal_mul_cpow_pos ha ha_inv1]
    congr 1; congr 1; field_simp [ha.ne']; ring
  have h2_cancel : (2 : ℂ) ^ (-(2 * s)) * (2 : ℂ) ^ (2 * s) = 1 := by
    rw [← Complex.cpow_add _ _ h2ne]; simp
  have ha1_cancel : ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * ((a + 1 : ℝ) : ℂ) ^ (2 * s) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha1.ne')]; simp
  have harg1 : (2 * a)⁻¹ = a⁻¹ / 2 := by field_simp [ha.ne']
  have harg2 : (a / 2)⁻¹ = 2 * a⁻¹ := by field_simp [ha.ne']
  have harg3 : 2 * a⁻¹ / (a⁻¹ + 1) = ((a + 1) / 2)⁻¹ := by
    field_simp [ha.ne', ha1.ne', ha_inv1.ne']; ring
  have harg4 : (2 * a / (a + 1))⁻¹ = (a⁻¹ + 1) / 2 := by
    field_simp [ha.ne', ha1.ne']; ring
  rw [hp_2a, hp_a2, hp_a1_2, hp_2a_a1, harg1, harg2, harg3, harg4]
  linear_combination
    -f (2 * a⁻¹) * (a : ℂ) ^ (-(2 * s)) * h2_cancel +
    f (((a + 1) / 2)⁻¹) * hp_ainv1 -
    f (((a + 1) / 2)⁻¹) * ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * h2_cancel -
    f ((a⁻¹ + 1) / 2) * (2 : ℂ) ^ (-(2 * s)) * (a : ℂ) ^ (-(2 * s)) * ha1_cancel

/-- **Universal Three-Term Hecke Intertwining `(1 - M_s)(T_{2,s} f) = T̃_{2,s}((1 - M_s) f)` on `(0, ∞)`.**
Every Farey three-term fixed point `M_s ψ = ψ` is mapped by `T_{2,s}` to another Farey three-term
fixed point. -/
theorem lewisThreeTermDefect_heckeT2 (s : ℂ) (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    lewisHeckeT2 s f a - lewisFarey s (lewisHeckeT2 s f) a =
      lewisHeckeT2Companion s (fun x => f x - lewisFarey s f x) a := by
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have h2a1 : 0 < 2 * a + 1 := by linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  unfold lewisHeckeT2Companion lewisHeckeT2 lewisFarey lewisShift lewisParabolic
  dsimp only
  -- Normalize shifted arguments:
  have h_a1_add1 : a + 1 + 1 = a + 2 := by ring
  have h_2_a1 : 2 * (a + 1) = 2 * a + 2 := by ring
  have h_2_div : 2 * (a / (a + 1)) = 2 * a / (a + 1) := by ring
  have h_div_2 : (a / (a + 1)) / 2 = a / (2 * a + 2) := by field_simp [ha1.ne']
  have h_add1_div2 : (a / (a + 1) + 1) / 2 = (2 * a + 1) / (2 * a + 2) := by
    field_simp [ha1.ne']; ring
  have h_add1_frac : a / (a + 1) + 1 = (2 * a + 1) / (a + 1) := by field_simp [ha1.ne']; ring
  have h_2_frac_div : 2 * (a / (a + 1)) / (a / (a + 1) + 1) = 2 * a / (2 * a + 1) := by
    field_simp [ha1.ne', h2a1.ne']; ring
  have h_a2_add1 : a / 2 + 1 = (a + 2) / 2 := by ring
  have h_a2_frac : (a / 2) / (a / 2 + 1) = a / (a + 2) := by field_simp [ha2.ne']
  have h_2a1_add1 : 2 * a + 1 + 1 = 2 * a + 2 := by ring
  have h_aa2_add1 : a / (a + 2) + 1 = (2 * a + 2) / (a + 2) := by field_simp [ha2.ne']; ring
  have h_aa2_frac : (a / (a + 2)) / (a / (a + 2) + 1) = a / (2 * a + 2) := by
    field_simp [ha2.ne', (show 2 * a + 2 ≠ 0 by linarith)]; ring
  -- Normalize complex powers:
  have hp_2a1_prod : ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) *
      (((2 * a + 1) / (a + 1) : ℝ) : ℂ) ^ (-(2 * s)) =
      ((2 * a + 1 : ℝ) : ℂ) ^ (-(2 * s)) := by
    rw [← ofReal_mul_cpow_pos ha1 (div_pos h2a1 ha1)]
    congr 1; congr 1; field_simp [ha1.ne']
  have hp_a2_prod : (2 : ℂ) ^ (-(2 * s)) * (((a + 2) / 2 : ℝ) : ℂ) ^ (-(2 * s)) =
      ((a + 2 : ℝ) : ℂ) ^ (-(2 * s)) := by
    have h := ofReal_mul_cpow_pos h2pos (div_pos ha2 h2pos) (-(2 * s))
    rw [show (2 * ((a + 2) / 2) : ℝ) = a + 2 by ring] at h
    simpa using h.symm
  have hp_2a2 : ((2 * a + 2 : ℝ) : ℂ) ^ (-(2 * s)) =
      (2 : ℂ) ^ (-(2 * s)) * ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) := by
    have h := ofReal_mul_cpow_pos h2pos ha1 (-(2 * s))
    rw [show (2 * (a + 1) : ℝ) = 2 * a + 2 by ring] at h
    simpa using h
  have hp_aa2_prod : ((a + 2 : ℝ) : ℂ) ^ (-(2 * s)) *
      (((2 * a + 2) / (a + 2) : ℝ) : ℂ) ^ (-(2 * s)) =
      (2 : ℂ) ^ (-(2 * s)) * ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) := by
    rw [← ofReal_mul_cpow_pos ha2 (div_pos (by linarith) ha2)]
    rw [show (a + 2) * ((2 * a + 2) / (a + 2)) = 2 * a + 2 by field_simp [ha2.ne'], hp_2a2]
  rw [h_2_frac_div, h_add1_div2, h_div_2, h_2_div, h_add1_frac,
    h_a2_frac, h_a2_add1, h_aa2_frac, h_aa2_add1, h_a1_add1, h_2_a1, h_2a1_add1, hp_2a2]
  linear_combination
    -f (2 * a / (2 * a + 1)) * hp_2a1_prod +
    f (a / (a + 2)) * hp_a2_prod +
    f (a / (2 * a + 2)) * hp_aa2_prod

/-- Invariance corollary: if `M_s ψ = ψ` on `(0, ∞)`, then `M_s (T_{2,s} ψ) = T_{2,s} ψ` on `(0, ∞)`. -/
theorem lewisFarey_heckeT2_of_fixed {s : ℂ} {ψ : ℝ → ℂ}
    (hfix : ∀ x > 0, lewisFarey s ψ x = ψ x) {a : ℝ} (ha : 0 < a) :
    lewisFarey s (lewisHeckeT2 s ψ) a = lewisHeckeT2 s ψ a := by
  have hd := lewisThreeTermDefect_heckeT2 s ψ ha
  have hrhs : lewisHeckeT2Companion s (fun x => ψ x - lewisFarey s ψ x) a = 0 := by
    unfold lewisHeckeT2Companion
    have h1 : ψ (2 * a) - lewisFarey s ψ (2 * a) = 0 := sub_eq_zero.mpr (hfix _ (by linarith)).symm
    have h2 : ψ (a / 2) - lewisFarey s ψ (a / 2) = 0 := sub_eq_zero.mpr (hfix _ (by linarith)).symm
    have h3 : ψ (2 * a + 1) - lewisFarey s ψ (2 * a + 1) = 0 :=
      sub_eq_zero.mpr (hfix _ (by linarith)).symm
    have h4 : ψ (a / (a + 2)) - lewisFarey s ψ (a / (a + 2)) = 0 :=
      sub_eq_zero.mpr (hfix _ (div_pos ha (by linarith))).symm
    simp [h1, h2, h3, h4]
  rw [hrhs] at hd
  exact (sub_eq_zero.mp hd).symm

/-! ## Part 5: Autonomous dyadic cusp-forcing recovery, off-line Eisenstein counterexample, and `Mayer 4` -/

/-- Derivative-free dyadic cusp extractor `(Δ_{2,s}^∞ ψ)(a) = ψ(2a) - 2^(1 - 2s) ψ(a)` on `(0, ∞)`,
annihilating the outgoing `a^(1 - 2s)` wave while isolating constant cusp forcing. -/
def dyadicCuspExtractor (s : ℂ) (ψ : ℝ → ℂ) (a : ℝ) : ℂ :=
  ψ (2 * a) - (2 : ℂ) ^ (1 - 2 * s) * ψ a

/-- The continuous Eisenstein global Lewis period function across `0 < Re s < 1/2`.
At Mayer scattering resonances (`ζ(2s) = 0`) this coincides with `resonantLewisPeriod s`;
at non-resonant points (`ζ(2s) ≠ 0`) it carries constant forcing `c = -ζ(2s)`. -/
def eisensteinLewisPeriod (s : ℂ) (a : ℂ) : ℂ :=
  period (2 * s) 1 (-riemannZeta (2 * s)) (state (2 * s)) a

/-- Identity of `extension w ε c f` with `ε * (transfer w f - c)` on `halfPlane = {Re z > -1/2}`,
proved from public holomorphic continuation and agreement on `MayerCutoff.inner`. -/
theorem extension_eq_eps_transfer_sub {w ε c : ℂ} (hw : 0 < w.re) (hε : ε ^ 2 = 1)
    (f : DiscSpace) (hf : regularized w hw f = ε • f + constant c)
    {z : ℂ} (hz : z ∈ halfPlane) :
    extension w ε c f z = ε * (transfer w f z - c) := by
  have hhp_open : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hsub : halfPlane ⊆ MayerGlobalPeriods.domain := fun u hu => by
    change -1 < u.re
    change -(1 / 2 : ℝ) < u.re at hu
    linarith
  let D : ℂ → ℂ := fun u => extension w ε c f u - ε * (transfer w f u - c)
  have hd : AnalyticOnNhd ℂ D halfPlane :=
    (((extension_differentiableOn hw ε c f).mono hsub).sub
      ((differentiableOn_const ε).mul
        ((transfer_differentiableOn hw f).sub (differentiableOn_const c)))).analyticOnNhd hhp_open
  have hevent : D =ᶠ[𝓝 (0 : ℂ)] 0 := by
    have h0_in : (0 : ℂ) ∈ MayerCutoff.inner := by
      norm_num [MayerCutoff.inner, Metric.mem_ball, dist_eq_norm]
    filter_upwards [Metric.isOpen_ball.mem_nhds h0_in] with u hu
    have hu_out : u ∈ outer := Metric.ball_subset_closedBall hu
    have hex := extension_eq_plane hw hε f hf hu
    have htr : ε * (transfer w f u - c) = plane f u := by
      let q : Disc := ⟨u, hu_out⟩
      have hq : transfer w f u = evaluation q (regularized w hw f) := transfer_eq_source hw f q
      have hcq : evaluation q (constant c) = c := rfl
      rw [hq, hf, map_add, map_smul, smul_eq_mul, hcq]
      have hval : ε * (ε * evaluation q f + c - c) = evaluation q f := by
        linear_combination evaluation q f * hε
      exact hval.trans (plane_eq f q).symm
    dsimp [D]
    rw [hex, htr, sub_self]
  have hc : IsPreconnected halfPlane := (convex_halfSpace_re_gt (-(1 / 2 : ℝ))).isPreconnected
  have hz0 := hd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc
    (by norm_num [halfPlane] : (0 : ℂ) ∈ halfPlane) hevent hz
  exact sub_eq_zero.mp hz0

private theorem norm_plane_sub_zero_le (f : DiscSpace) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) 1) :
    ‖plane f z - plane f 0‖ ≤ 4 * ‖f‖ * ‖z‖ := by
  have hderiv : ∀ w ∈ Metric.closedBall (1 : ℂ) 1, ‖deriv (plane f) w‖ ≤ 4 * ‖f‖ := by
    intro w hw
    have hsub : Metric.closedBall w (1 / 4) ⊆ MayerCutoff.inner := by
      intro u hu
      have hw' : ‖w - 1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
      have hu' : ‖u - w‖ ≤ (1 / 4 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
      rw [MayerCutoff.inner, Metric.mem_ball, dist_eq_norm, show u - 1 = (u - w) + (w - 1) by ring]
      exact (norm_add_le _ _).trans_lt (by linarith)
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 4)
      ((differentiableOn_plane f).diffContOnCl_ball hsub)
      (fun u hu => norm_plane_le f
        (Metric.ball_subset_closedBall (hsub (Metric.sphere_subset_closedBall hu))))
    linarith [show ‖f‖ / (1 / 4 : ℝ) = 4 * ‖f‖ by ring]
  have h := (convex_closedBall (1 : ℂ) (1 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (differentiableOn_plane f).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 3 / 2) hw)))
    hderiv
    (by norm_num [Metric.mem_closedBall, dist_eq_norm] : (0 : ℂ) ∈ Metric.closedBall (1 : ℂ) 1) hz
  simpa only [sub_zero] using h

private theorem inv_ofReal_mem_closedBall_one {u : ℝ} (hu : 1 ≤ u) :
    ((u : ℂ)⁻¹) ∈ Metric.closedBall (1 : ℂ) 1 := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hu_inv_le : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu
  rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_inv,
    show ((u⁻¹ : ℝ) : ℂ) - 1 = ((u⁻¹ - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith [inv_pos.mpr hu0]

/-- Telescoping Hurwitz tail estimate `∑_{k=0}^∞ (k + a)^(-σ - 1) ≤ (1 + 1/σ) a^(-σ)` for `σ > 0`
and `a ≥ 1`. -/
theorem tsum_add_rpow_neg_succ_le {σ a : ℝ} (hσ : 0 < σ) (ha : 1 ≤ a) :
    Summable (fun k : ℕ => ((k : ℝ) + a) ^ (-σ - 1)) ∧
      (∑' k : ℕ, ((k : ℝ) + a) ^ (-σ - 1)) ≤ (1 + 1 / σ) * a ^ (-σ) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + a) ^ (-σ - 1)) := by
    have hdom : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-σ - 1)) := by
      have h1 := (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (show -σ - 1 < -1 by linarith))
      exact h1.congr fun k => by push_cast; ring_nf
    refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (by positivity) _) (fun k => ?_) hdom
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  refine ⟨hsum, ?_⟩
  have hstep : ∀ u : ℝ, 0 < u → (u + 1) ^ (-σ - 1) ≤ (u ^ (-σ) - (u + 1) ^ (-σ)) / σ := by
    intro u hu
    let g : ℝ → ℝ := fun t => -(t ^ (-σ)) / σ
    have hcont : ContinuousOn g (Icc u (u + 1)) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hu hx.1
      exact (((continuousAt_id.rpow continuousAt_const (Or.inl hx0.ne')).neg).div_const
        σ).continuousWithinAt
    have hderiv : ∀ x ∈ Ioo u (u + 1), HasDerivAt g (x ^ (-σ - 1)) x := by
      intro x hx
      have hx0 : 0 < x := hu.trans hx.1
      have hd := ((Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hx0.ne')).neg).div_const σ
      refine hd.congr_deriv ?_
      field_simp [hσ.ne']
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g (fun x => x ^ (-σ - 1))
      (by linarith : u < u + 1) hcont hderiv
    have hξ0 : 0 < ξ := hu.trans hξ.1
    have hmono : (u + 1) ^ (-σ - 1) ≤ ξ ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_nonpos hξ0 hξ.2.le (by linarith)
    have hrhs : (g (u + 1) - g u) / (u + 1 - u) = (u ^ (-σ) - (u + 1) ^ (-σ)) / σ := by
      dsimp [g]; field_simp [hσ.ne']; ring
    linarith
  have hpartial : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, ((k : ℝ) + a) ^ (-σ - 1)) ≤ (1 + 1 / σ) * a ^ (-σ) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    | succ n _ =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_add]
      have ha_first : a ^ (-σ - 1) ≤ a ^ (-σ) :=
        Real.rpow_le_rpow_of_exponent_le ha (by linarith)
      have htel_le : (∑ m ∈ Finset.range n, (((m + 1 : ℕ) : ℝ) + a) ^ (-σ - 1)) ≤
          ∑ m ∈ Finset.range n, (((m : ℝ) + a) ^ (-σ) - (((m + 1 : ℕ) : ℝ) + a) ^ (-σ)) / σ := by
        refine Finset.sum_le_sum fun m _ => ?_
        have hm := hstep ((m : ℝ) + a) (by positivity)
        have hcast : (((m + 1 : ℕ) : ℝ) + a) = ((m : ℝ) + a) + 1 := by push_cast; ring
        rwa [hcast]
      have htel_eq : ∀ k : ℕ, (∑ m ∈ Finset.range k,
          (((m : ℝ) + a) ^ (-σ) - (((m + 1 : ℕ) : ℝ) + a) ^ (-σ)) / σ) =
          (a ^ (-σ) - ((k : ℝ) + a) ^ (-σ)) / σ := by
        intro k
        induction k with
        | zero => simp
        | succ j ih =>
          rw [Finset.sum_range_succ, ih]
          ring
      have htel_n := htel_eq n
      rw [sub_div] at htel_n
      have hrem_nn : 0 ≤ ((n : ℝ) + a) ^ (-σ) / σ := by positivity
      linarith [htel_le, htel_n, ha_first, hrem_nn,
        show a ^ (-σ) + a ^ (-σ) / σ = (1 + 1 / σ) * a ^ (-σ) by ring]
  exact le_of_tendsto_of_tendsto hsum.hasSum.tendsto_sum_nat tendsto_const_nhds
    (Eventually.of_forall hpartial)

private def dyadicRemainderTerm (w : ℂ) (f : DiscSpace) (a : ℝ) (k : ℕ) : ℂ :=
  ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
      (plane f (((2 * ((k : ℝ) + a) : ℝ) : ℂ)⁻¹) - plane f 0) +
    ((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) *
      (plane f (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ)⁻¹) - plane f 0) -
    2 * ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
      (plane f ((((k : ℝ) + a : ℝ) : ℂ)⁻¹) - plane f 0) +
    (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) - ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w)) * plane f 0

private theorem dyadicRemainderTerm_pair_eq (w : ℂ) (f : DiscSpace) (a : ℝ) (ha : 1 ≤ a) (k : ℕ) :
    term w f (2 * k) (((2 * a : ℝ) : ℂ) - 1) +
      term w f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1) -
      (2 : ℂ) ^ (1 - w) * term w f k ((a : ℂ) - 1) =
      -(RHTower.etaTerm w k * plane f 0) + dyadicRemainderTerm w f a k := by
  have hu_pos : (0 : ℝ) < (k : ℝ) + a := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2_1w : (2 : ℂ) ^ (1 - w) = 2 * (2 : ℂ) ^ (-w) := by
    rw [show (1 - w : ℂ) = 1 + (-w) by ring, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  have hp_2u : (2 : ℂ) ^ (-w) * (((k : ℝ) + a : ℝ) : ℂ) ^ (-w) =
      ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) :=
    (ofReal_mul_cpow_pos h2pos hu_pos (-w)).symm
  have hp_2k2 : (2 : ℂ) ^ (-w) * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-w) =
      ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-w) := by
    have h := (ofReal_mul_cpow_pos h2pos hk1_pos (-w)).symm
    rw [show (2 * ((k : ℝ) + 1) : ℝ) = 2 * (k : ℝ) + 2 by ring] at h
    exact h
  have hc_ev : (((2 * k + 1 : ℕ) : ℂ) + (((2 * a : ℝ) : ℂ) - 1)) =
      ((2 * ((k : ℝ) + a) : ℝ) : ℂ) := by push_cast; ring
  have hc_od : (((2 * k + 1 + 1 : ℕ) : ℂ) + (((2 * a : ℝ) : ℂ) - 1)) =
      ((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hc_a : (((k + 1 : ℕ) : ℂ) + ((a : ℂ) - 1)) = (((k : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
  have hc_n1 : ((2 * k + 1 : ℕ) : ℂ) = ((2 * (k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hc_n2 : ((2 * k + 1 + 1 : ℕ) : ℂ) = ((2 * (k : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
  have hc_nk : ((k + 1 : ℕ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  unfold dyadicRemainderTerm term RHTower.etaTerm
  rw [hc_ev, hc_od, hc_a, hc_n1, hc_n2, hc_nk, h2_1w]
  linear_combination
    -2 * plane f ((((k : ℝ) + a : ℝ) : ℂ)⁻¹) * hp_2u + 2 * plane f 0 * hp_2k2

private theorem norm_dyadicRemainderTerm_le {w : ℂ} (hw0 : 0 < w.re) (f : DiscSpace)
    {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    ‖dyadicRemainderTerm w f a k‖ ≤ (16 + ‖w‖) * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by
  have hu1 : 1 ≤ (k : ℝ) + a := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hu0 : 0 < (k : ℝ) + a := zero_lt_one.trans_le hu1
  have h2u1 : 1 ≤ 2 * ((k : ℝ) + a) := by linarith
  have h2u0 : 0 < 2 * ((k : ℝ) + a) := by linarith
  have h2u1_1 : 1 ≤ 2 * ((k : ℝ) + a) + 1 := by linarith
  have h2u1_0 : 0 < 2 * ((k : ℝ) + a) + 1 := by linarith
  have hf0 : ‖plane f 0‖ ≤ ‖f‖ := norm_plane_le f zeroPoint.2
  have hb1 : ‖((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
      (plane f (((2 * ((k : ℝ) + a) : ℝ) : ℂ)⁻¹) - plane f 0)‖ ≤
      4 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h2u0, Complex.neg_re]
    have hp := norm_plane_sub_zero_le f (inv_ofReal_mem_closedBall_one h2u1)
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h2u0.le] at hp
    calc
      (2 * ((k : ℝ) + a)) ^ (-w.re) *
          ‖plane f (((2 * ((k : ℝ) + a) : ℝ) : ℂ)⁻¹) - plane f 0‖
          ≤ (2 * ((k : ℝ) + a)) ^ (-w.re) * (4 * ‖f‖ * (2 * ((k : ℝ) + a))⁻¹) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg h2u0.le _)
      _ = 4 * ‖f‖ * ((2 * ((k : ℝ) + a)) ^ (-w.re) * (2 * ((k : ℝ) + a)) ^ (-1 : ℝ)) := by
        rw [Real.rpow_neg_one]; ring
      _ = 4 * ‖f‖ * (2 * ((k : ℝ) + a)) ^ (-w.re - 1) := by
        rw [← Real.rpow_add h2u0, ← sub_eq_add_neg]
      _ ≤ 4 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by linarith)) (by positivity)
  have hb2 : ‖((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) *
      (plane f (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ)⁻¹) - plane f 0)‖ ≤
      4 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h2u1_0, Complex.neg_re]
    have hp := norm_plane_sub_zero_le f (inv_ofReal_mem_closedBall_one h2u1_1)
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h2u1_0.le] at hp
    calc
      (2 * ((k : ℝ) + a) + 1) ^ (-w.re) *
          ‖plane f (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ)⁻¹) - plane f 0‖
          ≤ (2 * ((k : ℝ) + a) + 1) ^ (-w.re) * (4 * ‖f‖ * (2 * ((k : ℝ) + a) + 1)⁻¹) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg h2u1_0.le _)
      _ = 4 * ‖f‖ * ((2 * ((k : ℝ) + a) + 1) ^ (-w.re) * (2 * ((k : ℝ) + a) + 1) ^ (-1 : ℝ)) := by
        rw [Real.rpow_neg_one]; ring
      _ = 4 * ‖f‖ * (2 * ((k : ℝ) + a) + 1) ^ (-w.re - 1) := by
        rw [← Real.rpow_add h2u1_0, ← sub_eq_add_neg]
      _ ≤ 4 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by linarith)) (by positivity)
  have hb3 : ‖(2 : ℂ) * ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
      (plane f ((((k : ℝ) + a : ℝ) : ℂ)⁻¹) - plane f 0)‖ ≤
      8 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_cpow_eq_rpow_re_of_pos h2u0, Complex.neg_re]
    have hp := norm_plane_sub_zero_le f (inv_ofReal_mem_closedBall_one hu1)
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le] at hp
    have h2u_le : (2 * ((k : ℝ) + a)) ^ (-w.re) ≤ ((k : ℝ) + a) ^ (-w.re) :=
      Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by linarith)
    calc
      2 * (2 * ((k : ℝ) + a)) ^ (-w.re) * ‖plane f ((((k : ℝ) + a : ℝ) : ℂ)⁻¹) - plane f 0‖
          ≤ 2 * ((k : ℝ) + a) ^ (-w.re) * (4 * ‖f‖ * ((k : ℝ) + a)⁻¹) := by
        refine mul_le_mul ?_ hp (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left h2u_le (by norm_num)
      _ = 8 * ‖f‖ * (((k : ℝ) + a) ^ (-w.re) * ((k : ℝ) + a) ^ (-1 : ℝ)) := by
        rw [Real.rpow_neg_one]; ring
      _ = 8 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by rw [← Real.rpow_add hu0, ← sub_eq_add_neg]
  have hb4 : ‖(((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) -
      ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w)) * plane f 0‖ ≤
      ‖w‖ * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by
    rw [norm_mul]
    have hdq := RHTower.DQPT.dqptRp_sub_norm_le hw0 h2u0
      (show 2 * ((k : ℝ) + a) ≤ 2 * ((k : ℝ) + a) + 1 by linarith)
    rw [show 2 * ((k : ℝ) + a) + 1 - 2 * ((k : ℝ) + a) = 1 by ring, mul_one,
      RHTower.DQPT.dqptRp, RHTower.DQPT.dqptRp, norm_sub_rev] at hdq
    have hmono : (2 * ((k : ℝ) + a)) ^ (-w.re - 1) ≤ ((k : ℝ) + a) ^ (-w.re - 1) :=
      Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by linarith)
    calc
      ‖((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) - ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w)‖ *
          ‖plane f 0‖
          ≤ (‖w‖ * (2 * ((k : ℝ) + a)) ^ (-w.re - 1)) * ‖f‖ :=
        mul_le_mul hdq hf0 (norm_nonneg _) (by positivity)
      _ ≤ (‖w‖ * ((k : ℝ) + a) ^ (-w.re - 1)) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (norm_nonneg w))
          (norm_nonneg f)
      _ = ‖w‖ * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by ring
  unfold dyadicRemainderTerm
  have ht1 := norm_add_le
    (((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
        (plane f (((2 * ((k : ℝ) + a) : ℝ) : ℂ)⁻¹) - plane f 0) +
      ((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) *
        (plane f (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ)⁻¹) - plane f 0) -
      2 * ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
        (plane f ((((k : ℝ) + a : ℝ) : ℂ)⁻¹) - plane f 0))
    ((((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) - ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w)) * plane f 0)
  have ht2 := norm_sub_le
    (((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
        (plane f (((2 * ((k : ℝ) + a) : ℝ) : ℂ)⁻¹) - plane f 0) +
      ((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) *
        (plane f (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ)⁻¹) - plane f 0))
    ((2 : ℂ) * ((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
      (plane f ((((k : ℝ) + a : ℝ) : ℂ)⁻¹) - plane f 0))
  have ht3 := norm_add_le
    (((2 * ((k : ℝ) + a) : ℝ) : ℂ) ^ (-w) *
      (plane f (((2 * ((k : ℝ) + a) : ℝ) : ℂ)⁻¹) - plane f 0))
    (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ) ^ (-w) *
      (plane f (((2 * ((k : ℝ) + a) + 1 : ℝ) : ℂ)⁻¹) - plane f 0))
  have hsum_coef : 4 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) +
      4 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) +
      8 * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) +
      ‖w‖ * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) =
      (16 + ‖w‖) * ‖f‖ * ((k : ℝ) + a) ^ (-w.re - 1) := by ring
  linarith

private theorem tsum_even_add_odd_explicit (g : ℕ → ℂ)
    (hev : Summable (fun k => g (2 * k))) (hod : Summable (fun k => g (2 * k + 1))) :
    (∑' n, g n) = (∑' k, g (2 * k)) + ∑' k, g (2 * k + 1) :=
  (tsum_even_add_odd (f := g) hev hod).symm

private theorem tsum_mul_left_explicit (c : ℂ) (g : ℕ → ℂ) :
    c * (∑' k, g k) = ∑' k, c * g k :=
  (tsum_mul_left (a := c) (f := g)).symm

private theorem tsum_add_explicit (g₁ g₂ : ℕ → ℂ) (h₁ : Summable g₁) (h₂ : Summable g₂) :
    (∑' k, g₁ k) + (∑' k, g₂ k) = ∑' k, (g₁ k + g₂ k) :=
  (h₁.tsum_add h₂).symm

private theorem tsum_sub_explicit (g₁ g₂ : ℕ → ℂ) (h₁ : Summable g₁) (h₂ : Summable g₂) :
    (∑' k, g₁ k) - (∑' k, g₂ k) = ∑' k, (g₁ k - g₂ k) :=
  (h₁.tsum_sub h₂).symm

/-- **Quantitative Autonomous Dyadic Cusp-Forcing Bound (`a ≥ 1`, `s.re > 0`, `2s ≠ 1`).**
For any signed Mayer solution `(f ∈ DiscSpace, c ∈ ℂ, ε² = 1)` with global period
`ψ(a) = period (2s) ε c f a`, the dyadic cusp extractor cancels both the outgoing `a^(1 - 2s)`
wave (`ζ(2s) f(0)` via `ZetaRealStrip.etaPair_eq`) and the shifted Hurwitz series up to an explicit
`O(a^(-2 Re s))` remainder, isolating `-ε (1 - 2^(1 - 2s)) c`. -/
theorem dyadicCuspExtractor_bound {s ε c : ℂ} (hs0 : 0 < s.re) (hs_ne : 2 * s ≠ 1)
    (hε : ε ^ 2 = 1) (f : DiscSpace)
    (hf : regularized (2 * s) (by simp; linarith) f = ε • f + constant c)
    {a : ℝ} (ha : 1 ≤ a) :
    ‖dyadicCuspExtractor s (fun x => period (2 * s) ε c f x) a +
        ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c‖ ≤
      (16 + ‖2 * s‖) * (1 + 1 / (2 * s.re)) * ‖f‖ * a ^ (-2 * s.re) := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hw_re : (2 * s).re = 2 * s.re := by simp
  have hnorm_ε : ‖ε‖ = 1 := by
    have hsq : ‖ε‖ ^ 2 = 1 := by rw [← norm_pow, hε, norm_one]
    exact (sq_eq_one_iff.mp hsq).resolve_right (by linarith [norm_nonneg ε])
  have hza : ((a : ℂ) - 1) ∈ halfPlane := by
    change -(1 / 2 : ℝ) < ((a : ℂ) - 1).re
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hz2a : (((2 * a : ℝ) : ℂ) - 1) ∈ halfPlane := by
    change -(1 / 2 : ℝ) < (((2 * a : ℝ) : ℂ) - 1).re
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hψa : period (2 * s) ε c f a = ε * (transfer (2 * s) f ((a : ℂ) - 1) - c) :=
    extension_eq_eps_transfer_sub hw0 hε f hf hza
  have hψ2a : period (2 * s) ε c f (2 * a : ℝ) =
      ε * (transfer (2 * s) f (((2 * a : ℝ) : ℂ) - 1) - c) :=
    extension_eq_eps_transfer_sub hw0 hε f hf hz2a
  have hcomb_ε :
      dyadicCuspExtractor s (fun x => period (2 * s) ε c f x) a +
        ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c =
        ε * (transfer (2 * s) f (((2 * a : ℝ) : ℂ) - 1) -
          (2 : ℂ) ^ (1 - 2 * s) * transfer (2 * s) f ((a : ℂ) - 1)) := by
    unfold dyadicCuspExtractor
    change period (2 * s) ε c f (2 * a : ℝ) - (2 : ℂ) ^ (1 - 2 * s) * period (2 * s) ε c f a +
      ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c = _
    rw [hψ2a, hψa]
    ring
  have hsum_2a : Summable (fun n : ℕ => term (2 * s) f n (((2 * a : ℝ) : ℂ) - 1)) :=
    (term_locallyUniform hw0 f).summable hz2a
  have hsum_a : Summable (fun k : ℕ => term (2 * s) f k ((a : ℂ) - 1)) :=
    (term_locallyUniform hw0 f).summable hza
  have hinj_ev : Function.Injective (fun k : ℕ => 2 * k) := fun _ _ h => by simpa using h
  have hinj_od : Function.Injective (fun k : ℕ => 2 * k + 1) := fun _ _ h => by simpa using h
  have hsum_ev : Summable (fun k : ℕ => term (2 * s) f (2 * k) (((2 * a : ℝ) : ℂ) - 1)) :=
    hsum_2a.comp_injective hinj_ev
  have hsum_od : Summable (fun k : ℕ => term (2 * s) f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1)) :=
    hsum_2a.comp_injective hinj_od
  have hsum_eta : Summable (fun k : ℕ => RHTower.etaTerm (2 * s) k * plane f 0) :=
    (RHTower.summable_etaTerm (2 * s) hw0).mul_right (plane f 0)
  obtain ⟨hsum_tail, htail_le⟩ := tsum_add_rpow_neg_succ_le hw0 ha
  have hsum_δR_norm : Summable (fun k : ℕ => ‖dyadicRemainderTerm (2 * s) f a k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_dyadicRemainderTerm_le hw0 f ha)
      (hsum_tail.mul_left ((16 + ‖2 * s‖) * ‖f‖))
  have hsum_δR : Summable (dyadicRemainderTerm (2 * s) f a) := hsum_δR_norm.of_norm
  have htr_diff :
      transfer (2 * s) f (((2 * a : ℝ) : ℂ) - 1) -
          (2 : ℂ) ^ (1 - 2 * s) * transfer (2 * s) f ((a : ℂ) - 1) =
        ∑' k : ℕ, dyadicRemainderTerm (2 * s) f a k := by
    unfold transfer
    have hsplit : (∑' n : ℕ, term (2 * s) f n (((2 * a : ℝ) : ℂ) - 1)) =
        (∑' k : ℕ, term (2 * s) f (2 * k) (((2 * a : ℝ) : ℂ) - 1)) +
          ∑' k : ℕ, term (2 * s) f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1) :=
      tsum_even_add_odd_explicit (fun n : ℕ => term (2 * s) f n (((2 * a : ℝ) : ℂ) - 1))
        hsum_ev hsum_od
    have hmul_a : (2 : ℂ) ^ (1 - 2 * s) * (∑' k : ℕ, term (2 * s) f k ((a : ℂ) - 1)) =
        ∑' k : ℕ, (2 : ℂ) ^ (1 - 2 * s) * term (2 * s) f k ((a : ℂ) - 1) :=
      tsum_mul_left_explicit ((2 : ℂ) ^ (1 - 2 * s)) (fun k : ℕ => term (2 * s) f k ((a : ℂ) - 1))
    have hcomb_tsum :
        (∑' k : ℕ, term (2 * s) f (2 * k) (((2 * a : ℝ) : ℂ) - 1)) +
          (∑' k : ℕ, term (2 * s) f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1)) -
          (∑' k : ℕ, (2 : ℂ) ^ (1 - 2 * s) * term (2 * s) f k ((a : ℂ) - 1)) =
        ∑' k : ℕ, (-(RHTower.etaTerm (2 * s) k * plane f 0) + dyadicRemainderTerm (2 * s) f a k) := by
      have hadd := tsum_add_explicit
        (fun k : ℕ => term (2 * s) f (2 * k) (((2 * a : ℝ) : ℂ) - 1))
        (fun k : ℕ => term (2 * s) f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1))
        hsum_ev hsum_od
      have hsub := tsum_sub_explicit
        (fun k : ℕ => term (2 * s) f (2 * k) (((2 * a : ℝ) : ℂ) - 1) +
          term (2 * s) f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1))
        (fun k : ℕ => (2 : ℂ) ^ (1 - 2 * s) * term (2 * s) f k ((a : ℂ) - 1))
        (hsum_ev.add hsum_od) (hsum_a.mul_left ((2 : ℂ) ^ (1 - 2 * s)))
      rw [hadd, hsub]
      exact tsum_congr (dyadicRemainderTerm_pair_eq (2 * s) f a ha)
    have heta_val : (∑' k : ℕ, -(RHTower.etaTerm (2 * s) k * plane f 0)) =
        -((1 - (2 : ℂ) ^ (1 - 2 * s)) * riemannZeta (2 * s) * plane f 0) := by
      rw [tsum_neg, tsum_mul_right, ← RHTower.etaPair, RHTower.etaPair_eq (2 * s) hw0 hs_ne]
    have hsplit_δR :
        (∑' k : ℕ, (-(RHTower.etaTerm (2 * s) k * plane f 0) +
          dyadicRemainderTerm (2 * s) f a k)) =
        (∑' k : ℕ, -(RHTower.etaTerm (2 * s) k * plane f 0)) +
          ∑' k : ℕ, dyadicRemainderTerm (2 * s) f a k :=
      (tsum_add_explicit
        (fun k : ℕ => -(RHTower.etaTerm (2 * s) k * plane f 0))
        (dyadicRemainderTerm (2 * s) f a)
        hsum_eta.neg hsum_δR).symm
    rw [hsplit]
    calc
      (riemannZeta (2 * s) * plane f 0 +
          ((∑' k : ℕ, term (2 * s) f (2 * k) (((2 * a : ℝ) : ℂ) - 1)) +
            ∑' k : ℕ, term (2 * s) f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1))) -
          (2 : ℂ) ^ (1 - 2 * s) *
            (riemannZeta (2 * s) * plane f 0 + ∑' k : ℕ, term (2 * s) f k ((a : ℂ) - 1))
          = (1 - (2 : ℂ) ^ (1 - 2 * s)) * riemannZeta (2 * s) * plane f 0 +
              ((∑' k : ℕ, term (2 * s) f (2 * k) (((2 * a : ℝ) : ℂ) - 1)) +
                (∑' k : ℕ, term (2 * s) f (2 * k + 1) (((2 * a : ℝ) : ℂ) - 1)) -
                (2 : ℂ) ^ (1 - 2 * s) * ∑' k : ℕ, term (2 * s) f k ((a : ℂ) - 1)) := by ring
      _ = (1 - (2 : ℂ) ^ (1 - 2 * s)) * riemannZeta (2 * s) * plane f 0 +
            ∑' k : ℕ, (-(RHTower.etaTerm (2 * s) k * plane f 0) +
              dyadicRemainderTerm (2 * s) f a k) := by
        rw [hmul_a, hcomb_tsum]
      _ = (1 - (2 : ℂ) ^ (1 - 2 * s)) * riemannZeta (2 * s) * plane f 0 +
            ((∑' k : ℕ, -(RHTower.etaTerm (2 * s) k * plane f 0)) +
              ∑' k : ℕ, dyadicRemainderTerm (2 * s) f a k) := by
        rw [hsplit_δR]
      _ = ∑' k : ℕ, dyadicRemainderTerm (2 * s) f a k := by rw [heta_val]; ring
  rw [hcomb_ε, htr_diff, norm_mul, hnorm_ε, one_mul]
  calc
    ‖∑' k : ℕ, dyadicRemainderTerm (2 * s) f a k‖
        ≤ ∑' k : ℕ, ‖dyadicRemainderTerm (2 * s) f a k‖ := norm_tsum_le_tsum_norm hsum_δR_norm
    _ ≤ ∑' k : ℕ, (16 + ‖2 * s‖) * ‖f‖ * ((k : ℝ) + a) ^ (-(2 * s).re - 1) :=
      hsum_δR_norm.tsum_le_tsum (norm_dyadicRemainderTerm_le hw0 f ha)
        (hsum_tail.mul_left ((16 + ‖2 * s‖) * ‖f‖))
    _ = (16 + ‖2 * s‖) * ‖f‖ * ∑' k : ℕ, ((k : ℝ) + a) ^ (-(2 * s).re - 1) := tsum_mul_left
    _ ≤ (16 + ‖2 * s‖) * ‖f‖ * ((1 + 1 / (2 * s).re) * a ^ (-(2 * s).re)) :=
      mul_le_mul_of_nonneg_left htail_le (by positivity)
    _ = (16 + ‖2 * s‖) * (1 + 1 / (2 * s.re)) * ‖f‖ * a ^ (-2 * s.re) := by
      rw [hw_re]; ring

/-- **Autonomous Dyadic Cusp-Forcing Recovery:**
`lim_{a → +∞} (ψ(2a) - 2^(1 - 2s) ψ(a)) = -ε (1 - 2^(1 - 2s)) c` across `s.re > 0`, `2s ≠ 1`. -/
theorem tendsto_dyadicCuspExtractor {s ε c : ℂ} (hs0 : 0 < s.re) (hs_ne : 2 * s ≠ 1)
    (hε : ε ^ 2 = 1) (f : DiscSpace)
    (hf : regularized (2 * s) (by simp; linarith) f = ε • f + constant c) :
    Tendsto (dyadicCuspExtractor s (fun x => period (2 * s) ε c f x))
      atTop (𝓝 (-ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let B : ℝ := (16 + ‖2 * s‖) * (1 + 1 / (2 * s.re)) * ‖f‖
  have hzero : Tendsto (fun a : ℝ => B * a ^ (-2 * s.re)) atTop (𝓝 0) := by
    simpa [mul_zero] using (tendsto_rpow_neg_atTop (show 0 < 2 * s.re by linarith)).const_mul B
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  rw [Real.norm_of_nonneg (norm_nonneg _),
    show dyadicCuspExtractor s (fun x => period (2 * s) ε c f x) a -
        (-ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c) =
      dyadicCuspExtractor s (fun x => period (2 * s) ε c f x) a +
        ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c by ring]
  exact dyadicCuspExtractor_bound hs0 hs_ne hε f hf ha

/-- **Autonomous Dyadic Cusp-Energy Separation (`0 < s.re < 1/2`).**
The positive-semidefinite multiplicative-Haar cusp quadratic form
`∫_1^∞ ‖ψ(2a) - 2^(1 - 2s) ψ(a)‖² da/a` is finite iff the constant forcing `c` vanishes. -/
theorem dyadicCuspExtractor_sq_div_integrableOn_iff {s ε c : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) (hε : ε ^ 2 = 1) (f : DiscSpace)
    (hf : regularized (2 * s) (by simp; linarith) f = ε • f + constant c) :
    IntegrableOn
      (fun a : ℝ => ‖dyadicCuspExtractor s (fun x => period (2 * s) ε c f x) a‖ ^ 2 / a)
      (Ioi 1) ↔ c = 0 := by
  have hs_ne : 2 * s ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  let ψ : ℝ → ℂ := fun x => period (2 * s) ε c f x
  let B : ℝ := (16 + ‖2 * s‖) * (1 + 1 / (2 * s.re)) * ‖f‖
  have hB_nn : 0 ≤ B := by dsimp [B]; positivity
  constructor
  · intro hint
    by_contra hc_ne
    have hnorm_ε : ‖ε‖ = 1 := by
      have hsq : ‖ε‖ ^ 2 = 1 := by rw [← norm_pow, hε, norm_one]
      exact (sq_eq_one_iff.mp hsq).resolve_right (by linarith [norm_nonneg ε])
    have h2_gt1 : 1 < ‖(2 : ℂ) ^ (1 - 2 * s)‖ := by
      rw [show (2 : ℂ) ^ (1 - 2 * s) = ((2 : ℝ) : ℂ) ^ (1 - 2 * s) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
        show (1 - 2 * s).re = 1 - 2 * s.re by simp]
      exact Real.one_lt_rpow (by norm_num) (by linarith)
    have h12_ne : 1 - (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by
      intro hz
      have heq : (2 : ℂ) ^ (1 - 2 * s) = 1 := (sub_eq_zero.mp hz).symm
      rw [heq, norm_one] at h2_gt1
      exact lt_irrefl 1 h2_gt1
    let L : ℝ := ‖ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c‖
    have hL_pos : 0 < L := by
      dsimp [L]
      rw [norm_mul, norm_mul, hnorm_ε, one_mul]
      exact mul_pos (norm_pos_iff.mpr h12_ne) (norm_pos_iff.mpr hc_ne)
    let A₀ : ℝ := max 1 (((2 * B + 1) / L) ^ (1 / (2 * s.re)))
    have hA₀_ge1 : 1 ≤ A₀ := le_max_left _ _
    have hA₀_pos : 0 < A₀ := zero_lt_one.trans_le hA₀_ge1
    have hlow_pt : ∀ a ∈ Ioi A₀,
        (L / 2) ^ 2 * a ^ (-1 : ℝ) ≤ ‖dyadicCuspExtractor s ψ a‖ ^ 2 / a := by
      intro a ha
      have ha_ge1 : 1 ≤ a := hA₀_ge1.trans ha.le
      have ha_pos : 0 < a := zero_lt_one.trans_le ha_ge1
      have ha_ge_pow : ((2 * B + 1) / L) ^ (1 / (2 * s.re)) ≤ a :=
        (le_max_right 1 _).trans ha.le
      have hpow_ge : (2 * B + 1) / L ≤ a ^ (2 * s.re) := by
        have h1 := Real.rpow_le_rpow (by positivity) ha_ge_pow (show 0 ≤ 2 * s.re by linarith)
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one] at h1
        exact h1
      have hrem_le : B * a ^ (-2 * s.re) ≤ L / 2 := by
        rw [show (-2 * s.re : ℝ) = -(2 * s.re) by ring, Real.rpow_neg ha_pos.le,
          ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos ha_pos _)]
        have hmul := mul_le_mul_of_nonneg_left hpow_ge (half_pos hL_pos).le
        have hlhs : (L / 2) * ((2 * B + 1) / L) = B + 1 / 2 := by field_simp [hL_pos.ne']
        linarith
      have hbd := dyadicCuspExtractor_bound hs0 hs_ne hε f hf ha_ge1
      have htri : L ≤ ‖dyadicCuspExtractor s ψ a + ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c‖ +
          ‖dyadicCuspExtractor s ψ a‖ := by
        dsimp [L]
        calc
          ‖ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c‖
              = ‖(dyadicCuspExtractor s ψ a + ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c) -
                  dyadicCuspExtractor s ψ a‖ := by ring_nf
          _ ≤ ‖dyadicCuspExtractor s ψ a + ε * (1 - (2 : ℂ) ^ (1 - 2 * s)) * c‖ +
                ‖dyadicCuspExtractor s ψ a‖ := norm_sub_le _ _
      have hnorm_ge : L / 2 ≤ ‖dyadicCuspExtractor s ψ a‖ := by linarith
      have hsq_ge : (L / 2) ^ 2 ≤ ‖dyadicCuspExtractor s ψ a‖ ^ 2 :=
        pow_le_pow_left₀ (half_pos hL_pos).le hnorm_ge 2
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hsq_ge ha_pos.le
    have hint_A₀ : IntegrableOn (fun a : ℝ => ‖dyadicCuspExtractor s ψ a‖ ^ 2 / a) (Ioi A₀) :=
      hint.mono_set (Ioi_subset_Ioi hA₀_ge1)
    have hcont_inv : ContinuousOn (fun a : ℝ => (L / 2) ^ 2 * a ^ (-1 : ℝ)) (Ioi A₀) := by
      intro a ha
      have ha0 : 0 < a := hA₀_pos.trans ha
      exact ((continuousAt_id.rpow continuousAt_const (Or.inl ha0.ne')).const_mul _).continuousWithinAt
    have hint_har : IntegrableOn (fun a : ℝ => (L / 2) ^ 2 * a ^ (-1 : ℝ)) (Ioi A₀) := by
      refine hint_A₀.mono' (hcont_inv.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have ha0 : 0 < a := hA₀_pos.trans ha
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos ha0 _).le)]
      exact hlow_pt a ha
    have hint_rpow : IntegrableOn (fun a : ℝ => a ^ (-1 : ℝ)) (Ioi A₀) :=
      IntegrableOn.congr_fun (hint_har.const_mul (((L / 2) ^ 2)⁻¹))
        (fun a _ => inv_mul_cancel_left₀ (sq_pos_of_pos (half_pos hL_pos)).ne' (a ^ (-1 : ℝ)))
        measurableSet_Ioi
    have hlt := (integrableOn_Ioi_rpow_iff hA₀_pos).mp hint_rpow
    linarith
  · rintro rfl
    have hdom : IntegrableOn (fun a : ℝ => B ^ 2 * a ^ (-4 * s.re - 1)) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff zero_lt_one).2 (by linarith)).const_mul (B ^ 2)
    have hψ_cont : ContinuousOn ψ (Ioi 0) :=
      period_real_continuousOn (by simp; linarith) ε 0 f
    have hcont : ContinuousOn (fun a : ℝ => ‖dyadicCuspExtractor s ψ a‖ ^ 2 / a) (Ioi 1) := by
      intro a ha
      have ha0 : 0 < a := zero_lt_one.trans ha
      have h2a0 : 0 < 2 * a := by linarith
      have c1 : ContinuousAt (fun x : ℝ => ψ (2 * x)) a :=
        ContinuousAt.comp (g := ψ) (f := fun x : ℝ => 2 * x)
          (hψ_cont.continuousAt (isOpen_Ioi.mem_nhds h2a0))
          (continuousAt_const.mul continuousAt_id)
      have c2 : ContinuousAt ψ a := hψ_cont.continuousAt (isOpen_Ioi.mem_nhds ha0)
      unfold dyadicCuspExtractor
      exact (((c1.sub (continuousAt_const.mul c2)).norm.pow 2).div
        continuousAt_id ha0.ne').continuousWithinAt
    refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha0 : 0 < a := zero_lt_one.trans ha
    have hnn : 0 ≤ ‖dyadicCuspExtractor s ψ a‖ ^ 2 / a := div_nonneg (sq_nonneg _) ha0.le
    rw [Real.norm_of_nonneg hnn]
    have hbd := dyadicCuspExtractor_bound hs0 hs_ne hε f hf ha.le
    simp only [mul_zero, add_zero] at hbd
    have hsq : ‖dyadicCuspExtractor s ψ a‖ ^ 2 ≤ B ^ 2 * a ^ (-4 * s.re) := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hbd 2
      rw [mul_pow, ← Real.rpow_natCast (a ^ (-2 * s.re)) 2, ← Real.rpow_mul ha0.le] at h1
      have hexp : (-2 * s.re) * ((2 : ℕ) : ℝ) = -4 * s.re := by push_cast; ring
      rwa [hexp] at h1
    calc
      ‖dyadicCuspExtractor s ψ a‖ ^ 2 / a
          ≤ (B ^ 2 * a ^ (-4 * s.re)) / a := div_le_div_of_nonneg_right hsq ha0.le
      _ = B ^ 2 * (a ^ (-4 * s.re) * a ^ (-1 : ℝ)) := by
        rw [div_eq_mul_inv, Real.rpow_neg_one]; ring
      _ = B ^ 2 * a ^ (-4 * s.re - 1) := by rw [← Real.rpow_add ha0, ← sub_eq_add_neg]

private theorem state_regularized_eisenstein {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    regularized (2 * s) (by simp; linarith) (state (2 * s)) =
      (1 : ℂ) • state (2 * s) + constant (-riemannZeta (2 * s)) := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hw1 : (2 * s).re < 1 := by simp; linarith
  have hne1 : 2 * s ≠ 1 := fun h => by rw [h, Complex.one_re] at hw1; exact lt_irrefl 1 hw1
  have hne2 : 2 * s ≠ 2 := fun h => by rw [h] at hw1; norm_num at hw1
  have hst := state_equation hw0 hne1 hne2
  have hconst_neg : constant (-riemannZeta (2 * s)) = -(riemannZeta (2 * s) • constant 1) := by
    apply Subtype.ext; ext z
    change -riemannZeta (2 * s) = -(riemannZeta (2 * s) * 1)
    ring
  rw [← source_eq hw0, one_smul, hconst_neg, ← hst]
  abel

/-- Across the entire open strip `0 < Re s < 1/2`, `eisensteinLewisPeriod s` belongs to `H_LP`
(together with its Riemann–Mayer reflected partner) and satisfies both `I_s Ψ = Ψ` and `M_s Ψ = Ψ`
on `(0, ∞)`. -/
theorem eisensteinLewisPeriod_properties {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    IntegrableOn (fun a : ℝ => ‖eisensteinLewisPeriod s a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
    IntegrableOn (fun a : ℝ =>
      ‖lewisModularInversion (riemannMayerReflect s) (fun x => eisensteinLewisPeriod s x) a‖ ^ 2 *
        lewisCriticalWeight a) (Ioi 0) ∧
    (∀ a : ℝ, 0 < a →
      lewisModularInversion s (fun x => eisensteinLewisPeriod s x) a = eisensteinLewisPeriod s a) ∧
    (∀ a : ℝ, 0 < a →
      lewisFarey s (fun x => eisensteinLewisPeriod s x) a = eisensteinLewisPeriod s a) := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hreg := state_regularized_eisenstein hs0 hs1
  obtain ⟨hi1, hi2⟩ := globalLewisPeriod_integrable_lewisCriticalNormSq hs0 hs1 (by norm_num)
    (state (2 * s)) hreg
  refine ⟨hi1, hi2, ?_, ?_⟩
  · intro a ha
    unfold lewisModularInversion eisensteinLewisPeriod
    have hrec := MayerGlobalPeriods.reciprocity hw0 (by norm_num : (1 : ℂ) ^ 2 = 1) (state (2 * s))
      hreg (a := (a : ℂ)) (by simpa using ha)
    rw [one_mul, ← Complex.ofReal_inv] at hrec
    exact hrec.symm
  · intro a ha
    unfold lewisFarey lewisShift lewisParabolic eisensteinLewisPeriod
    dsimp only
    have htt := MayerGlobalPeriods.three_term hw0 (by norm_num : (1 : ℂ) ^ 2 = 1) (state (2 * s))
      hreg (a := (a : ℂ)) (by simpa using ha)
    have hc1 : ((a : ℂ) + 1) = ((a + 1 : ℝ) : ℂ) := by push_cast; ring
    have hc2 : ((a : ℂ) / ((a : ℂ) + 1)) = ((a / (a + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [hc2, hc1] at htt
    exact htt.symm

private def eisensteinDefectIntegrand (s : ℂ) (b : ℝ) : ℝ :=
  (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) *
    (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
    (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2 * ‖eisensteinLewisPeriod s b‖ ^ 2

/-- **Cusp-Erasure Obstruction Theorem Across the Strip (`0 < Re s < 1/2`):**
At EVERY parameter `s` in `0 < Re s < 1/2` — resonant OR non-resonant — the continuous Eisenstein
Lewis period `eisensteinLewisPeriod s` satisfies `lewisCoIsometryDefect s Ψ < 0 ↔ s.re ≠ 1/4`
(proved without `state_zero` or `core_hasMellin` at non-resonant points via
`tendsto_dyadicCuspExtractor`). -/
theorem eisensteinLewisPeriod_coIsometryDefect_lt_zero_iff {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    lewisCoIsometryDefect s (fun a : ℝ => eisensteinLewisPeriod s a) < 0 ↔ s.re ≠ 1 / 4 := by
  by_cases hzeta : riemannZeta (2 * s) = 0
  · have hres : IsMayerScatteringResonance s :=
      (isMayerScatteringResonance_iff_zeta_zero hs0 hs1).mpr hzeta
    have heq_fn : (fun a : ℝ => eisensteinLewisPeriod s a) =
        fun a : ℝ => resonantLewisPeriod s a := by
      ext a; simp [eisensteinLewisPeriod, resonantLewisPeriod, hzeta]
    rw [heq_fn]
    exact resonantLewisPeriod_coIsometryDefect_lt_zero_iff hres
  · have hw0 : 0 < (2 * s).re := by simp; linarith
    have hs_ne : 2 * s ≠ 1 := fun h => by
      have hre := congrArg Complex.re h; simp at hre; linarith
    have hreg := state_regularized_eisenstein hs0 hs1
    obtain ⟨hi1, hi2, hmod, _⟩ := eisensteinLewisPeriod_properties hs0 hs1
    have hf1 := globalLewisPeriod_rpow_integrableOn_Ioi_one hw0 (by norm_num) (state (2 * s)) hreg
      (β := 4 * s.re - 3 / 2) (by linarith)
    have hf2 := globalLewisPeriod_rpow_integrableOn_Ioi_one hw0 (by norm_num) (state (2 * s)) hreg
      (β := -4 * s.re + 1 / 2) (by linarith)
    have hdef_eq := lewisCoIsometryDefect_eq_neg_integral hmod hi1 hi2 hf1 hf2
    constructor
    · intro hlt heq
      rw [hdef_eq, heq, show (2 * (1 / 4 : ℝ) - 1 / 2) = 0 by norm_num, neg_zero] at hlt
      simp [sub_self] at hlt
    · intro hne
      -- Autonomous non-vanishing on `(1, ∞)` from `tendsto_dyadicCuspExtractor`:
      have hex_gt1 : ∃ b₀ : ℝ, 1 < b₀ ∧ eisensteinLewisPeriod s b₀ ≠ 0 := by
        by_contra hall
        push Not at hall
        have htend := tendsto_dyadicCuspExtractor hs0 hs_ne (by norm_num : (1 : ℂ) ^ 2 = 1)
          (state (2 * s)) hreg
        have hev0 : dyadicCuspExtractor s (fun x => eisensteinLewisPeriod s x) =ᶠ[atTop] 0 := by
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with a ha
          unfold dyadicCuspExtractor
          dsimp only
          rw [hall (2 * a) (by linarith), hall a ha]
          simp
        have hlim0 : Tendsto (dyadicCuspExtractor s (fun x => eisensteinLewisPeriod s x))
            atTop (𝓝 0) := tendsto_const_nhds.congr' hev0.symm
        have heq_lim := tendsto_nhds_unique htend hlim0
        have h2_gt1 : 1 < ‖(2 : ℂ) ^ (1 - 2 * s)‖ := by
          rw [show (2 : ℂ) ^ (1 - 2 * s) = ((2 : ℝ) : ℂ) ^ (1 - 2 * s) by norm_num,
            Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
            show (1 - 2 * s).re = 1 - 2 * s.re by simp]
          exact Real.one_lt_rpow (by norm_num) (by linarith)
        have h12_ne : 1 - (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := fun hz => by
          rw [(sub_eq_zero.mp hz).symm, norm_one] at h2_gt1; exact lt_irrefl 1 h2_gt1
        have hprod_ne : (-1 : ℂ) * (1 - (2 : ℂ) ^ (1 - 2 * s)) * (-riemannZeta (2 * s)) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) h12_ne) (neg_ne_zero.mpr hzeta)
        exact hprod_ne heq_lim
      obtain ⟨b₀, hb₀_gt1, hb₀_ne⟩ := hex_gt1
      rw [hdef_eq, Left.neg_neg_iff]
      change 0 < ∫ b in Ioi (1 : ℝ), eisensteinDefectIntegrand s b
      have hδ_ne : 2 * s.re - 1 / 2 ≠ 0 := fun h => hne (by linarith)
      have hψ_cont : ContinuousOn (fun b : ℝ => eisensteinLewisPeriod s b) (Ioi 0) :=
        period_real_continuousOn hw0 1 (-riemannZeta (2 * s)) (state (2 * s))
      have hK_cont : ContinuousOn (eisensteinDefectIntegrand s) (Ioi 0) := by
        intro b hb
        have hb0 : 0 < b := hb
        have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
        have c1 : ContinuousAt (fun x : ℝ => (x + x⁻¹) ^ (-6 : ℝ)) b :=
          (continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow
            (continuousAt_const : ContinuousAt (fun _ : ℝ => (-6 : ℝ)) b) (Or.inl hsum)
        have c2 : ContinuousAt (fun x : ℝ => x ^ (2 * s.re - 1)) b :=
          continuousAt_id.rpow
            (continuousAt_const : ContinuousAt (fun _ : ℝ => 2 * s.re - 1) b) (Or.inl hb0.ne')
        have c3 : ContinuousAt
            (fun x : ℝ => x ^ (2 * s.re - 1 / 2) + x ^ (-(2 * s.re - 1 / 2))) b :=
          (continuousAt_id.rpow
              (continuousAt_const : ContinuousAt (fun _ : ℝ => 2 * s.re - 1 / 2) b)
              (Or.inl hb0.ne')).add
            (continuousAt_id.rpow
              (continuousAt_const : ContinuousAt (fun _ : ℝ => -(2 * s.re - 1 / 2)) b)
              (Or.inl hb0.ne'))
        have c4 : ContinuousAt
            (fun x : ℝ => (x ^ (2 * s.re - 1 / 2) - x ^ (-(2 * s.re - 1 / 2))) ^ 2) b :=
          ((continuousAt_id.rpow
              (continuousAt_const : ContinuousAt (fun _ : ℝ => 2 * s.re - 1 / 2) b)
              (Or.inl hb0.ne')).sub
            (continuousAt_id.rpow
              (continuousAt_const : ContinuousAt (fun _ : ℝ => -(2 * s.re - 1 / 2)) b)
              (Or.inl hb0.ne'))).pow 2
        have c5 : ContinuousAt (fun x : ℝ => ‖eisensteinLewisPeriod s x‖ ^ 2) b :=
          (hψ_cont.continuousAt (isOpen_Ioi.mem_nhds hb0)).norm.pow 2
        exact ((((c1.mul c2).mul c3).mul c4).mul c5).continuousWithinAt
      have hc_b0 : 0 < ‖eisensteinLewisPeriod s b₀‖ := norm_pos_iff.mpr hb₀_ne
      have hcont_b0 : ContinuousAt (fun x : ℝ => ‖eisensteinLewisPeriod s x‖) b₀ :=
        (hψ_cont.continuousAt (isOpen_Ioi.mem_nhds (zero_lt_one.trans hb₀_gt1))).norm
      obtain ⟨r, hr_pos, hball⟩ :=
        Metric.continuousAt_iff.mp hcont_b0 (‖eisensteinLewisPeriod s b₀‖ / 2) (half_pos hc_b0)
      have hp_gt1 : 1 < max ((1 + b₀) / 2) (b₀ - r / 2) := lt_max_of_lt_left (by linarith)
      have hp_lt_b0 : max ((1 + b₀) / 2) (b₀ - r / 2) < b₀ := max_lt (by linarith) (by linarith)
      have hp_lt_q : max ((1 + b₀) / 2) (b₀ - r / 2) < b₀ + r / 2 := by linarith
      obtain ⟨x₀, hx₀, hminK⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hp_lt_q.le)
        (hK_cont.mono (fun x hx => zero_lt_one.trans (lt_of_lt_of_le hp_gt1 hx.1)))
      have hx₀_gt1 : 1 < x₀ := lt_of_lt_of_le hp_gt1 hx₀.1
      have hx₀_pos : 0 < x₀ := zero_lt_one.trans hx₀_gt1
      have hx₀_dist : dist x₀ b₀ < r := by
        rw [Real.dist_eq, abs_lt]
        have hp2 : b₀ - r / 2 ≤ max ((1 + b₀) / 2) (b₀ - r / 2) := le_max_right _ _
        have hx_le : x₀ ≤ b₀ + r / 2 := hx₀.2
        exact ⟨by linarith [hx₀.1], by linarith⟩
      have hx₀_ψ_pos : 0 < ‖eisensteinLewisPeriod s x₀‖ := by
        have hb := abs_lt.mp (by simpa [Real.dist_eq] using hball hx₀_dist)
        linarith
      have hx₀_diff_ne : x₀ ^ (2 * s.re - 1 / 2) - x₀ ^ (-(2 * s.re - 1 / 2)) ≠ 0 := by
        intro heq_pow
        have hpow_eq : x₀ ^ (2 * s.re - 1 / 2) = x₀ ^ (-(2 * s.re - 1 / 2)) :=
          sub_eq_zero.mp heq_pow
        rcases lt_or_gt_of_ne hδ_ne with hneg | hpos
        · exact (Real.rpow_lt_rpow_of_exponent_lt hx₀_gt1 (by linarith)).ne hpow_eq
        · exact (Real.rpow_lt_rpow_of_exponent_lt hx₀_gt1 (by linarith)).ne hpow_eq.symm
      have hKx₀_pos : 0 < eisensteinDefectIntegrand s x₀ :=
        mul_pos (mul_pos (mul_pos (mul_pos
          (Real.rpow_pos_of_pos (add_pos hx₀_pos (inv_pos.mpr hx₀_pos)) _)
          (Real.rpow_pos_of_pos hx₀_pos _))
          (add_pos (Real.rpow_pos_of_pos hx₀_pos _) (Real.rpow_pos_of_pos hx₀_pos _)))
          (sq_pos_iff.mpr hx₀_diff_ne)) (sq_pos_of_pos hx₀_ψ_pos)
      have hK_int : IntegrableOn (eisensteinDefectIntegrand s) (Ioi 1) := by
        have hdom := (globalLewisPeriod_rpow_integrableOn_Ioi_one hw0 (by norm_num) (state (2 * s))
          hreg (β := 5 / 2) (by norm_num)).const_mul 8
        refine hdom.mono' ((hK_cont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
          measurableSet_Ioi) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
        have hb0 : 0 < b := zero_lt_one.trans hb
        have hb1 : 1 ≤ b := hb.le
        have hK_nn : 0 ≤ eisensteinDefectIntegrand s b :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
            (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
            (Real.rpow_pos_of_pos hb0 _).le)
            (add_nonneg (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_pos_of_pos hb0 _).le))
            (sq_nonneg _)) (sq_nonneg _)
        rw [Real.norm_of_nonneg hK_nn]
        have hbd1 : b ^ (2 * s.re - 1 / 2) ≤ b ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
        have hbd2 : b ^ (-(2 * s.re - 1 / 2)) ≤ b ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
        have hsum_le : b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2)) ≤
            2 * b ^ (1 / 2 : ℝ) := by linarith
        have hdiff_abs : |b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))| ≤
            2 * b ^ (1 / 2 : ℝ) := by
          rw [abs_le]
          exact ⟨by linarith [Real.rpow_pos_of_pos hb0 (2 * s.re - 1 / 2),
              Real.rpow_pos_of_pos hb0 (-(2 * s.re - 1 / 2))],
            by linarith [Real.rpow_pos_of_pos hb0 (2 * s.re - 1 / 2),
              Real.rpow_pos_of_pos hb0 (-(2 * s.re - 1 / 2))]⟩
        have hsq_le : (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2 ≤
            4 * b ^ (1 : ℝ) := by
          have h1 := pow_le_pow_left₀ (abs_nonneg _) hdiff_abs 2
          rw [sq_abs, mul_pow, ← Real.rpow_natCast (b ^ (1 / 2 : ℝ)) 2,
            ← Real.rpow_mul hb0.le] at h1
          have hexp : (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 := by norm_num
          have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
          rwa [hexp, h4] at h1
        have hbase_le : b ^ (2 * s.re - 1) ≤ b ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
        have hmid : b ^ (2 * s.re - 1) *
            (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
            (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2 ≤
            8 * b ^ (5 / 2 : ℝ) := by
          calc
            b ^ (2 * s.re - 1) *
                (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
                (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2
                ≤ (b ^ (1 : ℝ) * (2 * b ^ (1 / 2 : ℝ))) * (4 * b ^ (1 : ℝ)) := by
              apply mul_le_mul _ hsq_le (sq_nonneg _) (by positivity)
              exact mul_le_mul hbase_le hsum_le
                (add_nonneg (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_pos_of_pos hb0 _).le)
                (Real.rpow_pos_of_pos hb0 _).le
            _ = 8 * (b ^ (1 : ℝ) * b ^ (1 / 2 : ℝ) * b ^ (1 : ℝ)) := by ring
            _ = 8 * b ^ (5 / 2 : ℝ) := by rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; norm_num
        unfold eisensteinDefectIntegrand eisensteinLewisPeriod
        calc
          (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) *
              (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
              (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2 *
              ‖period (2 * s) 1 (-riemannZeta (2 * s)) (state (2 * s)) b‖ ^ 2
              = (b + b⁻¹) ^ (-6 : ℝ) *
                  ‖period (2 * s) 1 (-riemannZeta (2 * s)) (state (2 * s)) b‖ ^ 2 *
                  (b ^ (2 * s.re - 1) *
                    (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
                    (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2) := by ring
          _ ≤ (b + b⁻¹) ^ (-6 : ℝ) *
                ‖period (2 * s) 1 (-riemannZeta (2 * s)) (state (2 * s)) b‖ ^ 2 *
                (8 * b ^ (5 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hmid
              (mul_nonneg (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le (sq_nonneg _))
          _ = 8 * (‖period (2 * s) 1 (-riemannZeta (2 * s)) (state (2 * s)) b‖ ^ 2 *
                ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (5 / 2 : ℝ))) := by ring
      have hsub_Ioi : Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2) ⊆ Ioi 1 :=
        fun x hx => hp_gt1.trans hx.1
      have hunion : Ioi (1 : ℝ) = Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2) ∪
          (Ioi 1 \ Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2)) :=
        (Set.union_sdiff_cancel hsub_Ioi).symm
      have hsplit : (∫ b in Ioi (1 : ℝ), eisensteinDefectIntegrand s b) =
          (∫ b in Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2),
            eisensteinDefectIntegrand s b) +
          ∫ b in Ioi 1 \ Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2),
            eisensteinDefectIntegrand s b := by
        conv_lhs => rw [hunion]
        exact setIntegral_union disjoint_sdiff_self_right
          (measurableSet_Ioi.diff measurableSet_Ioc)
          (hK_int.mono_set hsub_Ioi) (hK_int.mono_set Set.sdiff_subset)
      have hrest : 0 ≤ ∫ b in Ioi 1 \ Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2),
          eisensteinDefectIntegrand s b := by
        refine setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioc) fun b hb => ?_
        have hb0 : 0 < b := zero_lt_one.trans hb.1
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (Real.rpow_pos_of_pos (add_pos hb0 (inv_pos.mpr hb0)) _).le
          (Real.rpow_pos_of_pos hb0 _).le)
          (add_nonneg (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_pos_of_pos hb0 _).le))
          (sq_nonneg _)) (sq_nonneg _)
      have hlow : ((b₀ + r / 2) - max ((1 + b₀) / 2) (b₀ - r / 2)) *
          eisensteinDefectIntegrand s x₀ ≤
          ∫ b in Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2),
            eisensteinDefectIntegrand s b := by
        have hc : (∫ _ in Ioc (max ((1 + b₀) / 2) (b₀ - r / 2)) (b₀ + r / 2),
            eisensteinDefectIntegrand s x₀) =
            ((b₀ + r / 2) - max ((1 + b₀) / 2) (b₀ - r / 2)) *
              eisensteinDefectIntegrand s x₀ := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hp_lt_q.le, smul_eq_mul]
        rw [← hc]
        exact setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
          (hK_int.mono_set hsub_Ioi) measurableSet_Ioc fun b hb => hminK ⟨hb.1.le, hb.2⟩
      linarith [mul_pos (sub_pos.mpr hp_lt_q) hKx₀_pos]

/-- **Unconditional Off-Line Counterexample to Naive Three-Term Reflection Positivity:**
For every real `σ ∈ (0, 1/2) \ {1/4}` (e.g. `σ = 1/8`), `s = (σ : ℂ)` is non-resonant, yet
`eisensteinLewisPeriod s ∈ H_LP` satisfies BOTH `I_s Ψ = Ψ` AND the homogeneous Farey–Lewis
three-term equation `M_s Ψ = Ψ` with strictly negative co-isometry defect `Q_s(Ψ) < 0` and
infinite dyadic cusp energy. -/
theorem nonresonant_real_strip_eisenstein_counterexample {σ : ℝ}
    (h0 : 0 < σ) (h1 : σ < 1 / 2) (hne : σ ≠ 1 / 4) :
    ¬ IsMayerScatteringResonance (σ : ℂ) ∧
    IntegrableOn
      (fun a : ℝ => ‖eisensteinLewisPeriod (σ : ℂ) a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
    (∀ a : ℝ, 0 < a →
      lewisModularInversion (σ : ℂ) (fun x => eisensteinLewisPeriod (σ : ℂ) x) a =
        eisensteinLewisPeriod (σ : ℂ) a) ∧
    (∀ a : ℝ, 0 < a →
      lewisFarey (σ : ℂ) (fun x => eisensteinLewisPeriod (σ : ℂ) x) a =
        eisensteinLewisPeriod (σ : ℂ) a) ∧
    lewisCoIsometryDefect (σ : ℂ) (fun a : ℝ => eisensteinLewisPeriod (σ : ℂ) a) < 0 ∧
    ¬ IntegrableOn
      (fun a : ℝ =>
        ‖dyadicCuspExtractor (σ : ℂ) (fun x => eisensteinLewisPeriod (σ : ℂ) x) a‖ ^ 2 / a)
      (Ioi 1) := by
  have hs0 : 0 < (σ : ℂ).re := by simpa using h0
  have hs1 : (σ : ℂ).re < 1 / 2 := by simpa using h1
  have hs_ne : (σ : ℂ).re ≠ 1 / 4 := by simpa using hne
  have hzeta_ne : riemannZeta (2 * (σ : ℂ)) ≠ 0 := by
    rw [show 2 * (σ : ℂ) = ((2 * σ : ℝ) : ℂ) by push_cast; ring]
    exact RHTower.riemannZeta_real_strip_ne_zero (by linarith) (by linarith)
  have hnot_res : ¬ IsMayerScatteringResonance (σ : ℂ) := by
    rw [isMayerScatteringResonance_iff_zeta_zero hs0 hs1]
    exact hzeta_ne
  obtain ⟨hi1, _, hmod, hfar⟩ := eisensteinLewisPeriod_properties hs0 hs1
  have hdef_lt :=
    (eisensteinLewisPeriod_coIsometryDefect_lt_zero_iff hs0 hs1).mpr hs_ne
  have hnot_cusp : ¬ IntegrableOn
      (fun a : ℝ =>
        ‖dyadicCuspExtractor (σ : ℂ) (fun x => eisensteinLewisPeriod (σ : ℂ) x) a‖ ^ 2 / a)
      (Ioi 1) := by
    unfold eisensteinLewisPeriod
    rw [dyadicCuspExtractor_sq_div_integrableOn_iff hs0 hs1 (by norm_num) (state (2 * (σ : ℂ)))
        (state_regularized_eisenstein hs0 hs1),
      neg_eq_zero]
    exact hzeta_ne
  exact ⟨hnot_res, hi1, hmod, hfar, hdef_lt, hnot_cusp⟩

/-- **Resolution of Route PM Task `Mayer 4` (Quadratic-Form Separation of Resonances from
Continuous Scattering):**
Across `0 < Re s < 1/2`, the positive-semidefinite dyadic cusp quadratic form
`∫_1^∞ ‖eisensteinLewisPeriod s (2a) - 2^(1 - 2s) eisensteinLewisPeriod s a‖² da/a`
is finite if and only if `s` is a Mayer scattering resonance. Combined with `lewisCoIsometryDefect`,
a strip parameter `s` is a critical-line Mayer scattering resonance (`IsMayerScatteringResonance s ∧
s.re = 1/4`) iff `eisensteinLewisPeriod s` simultaneously has finite dyadic cusp energy and zero
co-isometry defect on `H_LP`. -/
theorem eisensteinLewisPeriod_dyadicCuspEnergy_integrable_iff_resonance {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    IntegrableOn
      (fun a : ℝ =>
        ‖dyadicCuspExtractor s (fun x => eisensteinLewisPeriod s x) a‖ ^ 2 / a)
      (Ioi 1) ↔ IsMayerScatteringResonance s := by
  unfold eisensteinLewisPeriod
  rw [dyadicCuspExtractor_sq_div_integrableOn_iff hs0 hs1 (by norm_num) (state (2 * s))
      (state_regularized_eisenstein hs0 hs1),
    neg_eq_zero, isMayerScatteringResonance_iff_zeta_zero hs0 hs1]

theorem criticalLineResonance_iff_dyadicCuspEnergy_and_zero_coIsometryDefect {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    (IsMayerScatteringResonance s ∧ s.re = 1 / 4) ↔
      (IntegrableOn
        (fun a : ℝ =>
          ‖dyadicCuspExtractor s (fun x => eisensteinLewisPeriod s x) a‖ ^ 2 / a)
        (Ioi 1) ∧
        lewisCoIsometryDefect s (fun a : ℝ => eisensteinLewisPeriod s a) = 0) := by
  rw [eisensteinLewisPeriod_dyadicCuspEnergy_integrable_iff_resonance hs0 hs1]
  refine and_congr_right fun hres => ?_
  have heq_fn : (fun a : ℝ => eisensteinLewisPeriod s a) =
      fun a : ℝ => resonantLewisPeriod s a := by
    have hz := (isMayerScatteringResonance_iff_zeta_zero hs0 hs1).mp hres
    ext a; simp [eisensteinLewisPeriod, resonantLewisPeriod, hz]
  rw [heq_fn, resonantLewisPeriod_coIsometryDefect_eq_zero_iff hres]

#print axioms lewisModularInversion_adj_comp_self
#print axioms lewisModularInversion_normBounded_iff
#print axioms gaussMayerBranch_zero_normBounded_iff
#print axioms gaussMayerBranch_zero_pair_normBounded_iff
#print axioms gaussMayerBranch_tail_normBounded
#print axioms lewisFarey_comp_fareyAdj
#print axioms one_lt_lewisFareyMultiplier
#print axioms lewisFarey_normBounded
#print axioms lewisFarey_selfCommutator_neg_of_fixed
#print axioms lewisModularInversion_heckeT2
#print axioms lewisThreeTermDefect_heckeT2
#print axioms dyadicCuspExtractor_bound
#print axioms dyadicCuspExtractor_sq_div_integrableOn_iff
#print axioms eisensteinLewisPeriod_coIsometryDefect_lt_zero_iff
#print axioms nonresonant_real_strip_eisenstein_counterexample
#print axioms eisensteinLewisPeriod_dyadicCuspEnergy_integrable_iff_resonance
#print axioms criticalLineResonance_iff_dyadicCuspEnergy_and_zero_coIsometryDefect

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

