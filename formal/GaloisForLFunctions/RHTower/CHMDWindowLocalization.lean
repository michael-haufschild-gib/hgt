import GaloisForLFunctions.RHTower.CHMDWindowFourierTail
import GaloisForLFunctions.RHTower.CHMDFarFieldEnergy
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# Localizing the arithmetic Doob energy to a window

A smooth cutoff `χ_R` (equal to `1` on `|x| ≤ R+1`, supported in `|x| < R+2`) turns a compact `C²`
test `v` of the arithmetic Doob graph into the compactly supported function `χ_R v` whose
archimedean Lévy form is controlled by the archimedean jump energy of `v` and its mass:

`Q(χ_R v) ≤ C_R (J_arch(v) + ‖v‖²_μ)`.

On the window the Doob weights `Θ(x)Θ(x+t)` are bounded below, which converts the Doob jump energy
into the flat Lévy form for jumps of length at most `1`; the commutator with the cutoff is of order
`t²` by the Lipschitz bound; jumps longer than `1` cost at most four times the window mass, and
`t²` is at least `1` there, so a single majorant `ω(t)(J_t(v)/m² + c t² ‖v‖²_μ)` works.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## The smooth window cutoff -/

/-- The smooth cutoff: `1` on `|x| ≤ R + 1`, supported in `|x| < R + 2`, values in `[0, 1]`. -/
def windowBump (R : ℝ) (hR : 0 ≤ R) : ContDiffBump (0 : ℝ) :=
  ⟨R + 1, R + 2, by linarith, by linarith⟩

theorem windowBump_eq_one {R : ℝ} (hR : 0 ≤ R) {x : ℝ} (hx : |x| ≤ R + 1) :
    windowBump R hR x = 1 :=
  (windowBump R hR).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact hx)

theorem windowBump_eq_zero {R : ℝ} (hR : 0 ≤ R) {x : ℝ} (hx : R + 2 ≤ |x|) :
    windowBump R hR x = 0 :=
  (windowBump R hR).zero_of_le_dist (by
    rw [dist_zero_right, Real.norm_eq_abs]
    exact hx)

theorem windowBump_nonneg (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : 0 ≤ windowBump R hR x :=
  (windowBump R hR).nonneg

theorem windowBump_le_one (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : windowBump R hR x ≤ 1 :=
  (windowBump R hR).le_one

theorem windowBump_sq_le_one (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : windowBump R hR x ^ 2 ≤ 1 := by
  have h0 := windowBump_nonneg R hR x
  have h1 := windowBump_le_one R hR x
  nlinarith

theorem contDiff_windowBump (R : ℝ) (hR : 0 ≤ R) : ContDiff ℝ 2 (windowBump R hR) :=
  (windowBump R hR).contDiff

theorem hasCompactSupport_windowBump (R : ℝ) (hR : 0 ≤ R) :
    HasCompactSupport (windowBump R hR) :=
  (windowBump R hR).hasCompactSupport

theorem abs_lt_of_windowBump_ne_zero {R : ℝ} (hR : 0 ≤ R) {x : ℝ} (h : windowBump R hR x ≠ 0) :
    |x| < R + 2 := by
  by_contra hc
  rw [not_lt] at hc
  exact h (windowBump_eq_zero hR hc)

/-- The windowed test `χ_R v`. -/
def windowTest (R : ℝ) (hR : 0 ≤ R) (v : ℝ → ℝ) (x : ℝ) : ℝ := windowBump R hR x * v x

theorem contDiff_windowTest (R : ℝ) (hR : 0 ≤ R) {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (windowTest R hR v) :=
  (contDiff_windowBump R hR).mul hv

theorem hasCompactSupport_windowTest (R : ℝ) (hR : 0 ≤ R) {v : ℝ → ℝ}
    (hvc : HasCompactSupport v) : HasCompactSupport (windowTest R hR v) :=
  hvc.mul_left

theorem windowTest_eq_of_le {R : ℝ} (hR : 0 ≤ R) (v : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ R + 1) :
    windowTest R hR v x = v x := by
  unfold windowTest
  rw [windowBump_eq_one hR hx, one_mul]

/-! ## Window constants -/

theorem exists_theta_window_lower {a : ℝ} (ha : 0 ≤ a) :
    ∃ m : ℝ, 0 < m ∧ ∀ y, |y| ≤ a → m ≤ riemannKernelReal y := by
  obtain ⟨x₀, _, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (-a) a) ⟨0, by
    rw [mem_Icc]; constructor <;> linarith⟩ continuous_riemannKernelReal.continuousOn
  exact ⟨riemannKernelReal x₀, riemannKernelReal_pos x₀, fun y hy =>
    isMinOn_iff.mp hmin y (by rw [mem_Icc]; exact abs_le.mp hy)⟩

theorem exists_mass_window_lower {a : ℝ} (ha : 0 ≤ a) :
    ∃ m : ℝ, 0 < m ∧ ∀ y, |y| ≤ a → m ≤ massDensity y := by
  obtain ⟨x₀, _, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (-a) a) ⟨0, by
    rw [mem_Icc]; constructor <;> linarith⟩ continuous_massDensity.continuousOn
  exact ⟨massDensity x₀, massDensity_pos x₀, fun y hy =>
    isMinOn_iff.mp hmin y (by rw [mem_Icc]; exact abs_le.mp hy)⟩

theorem hasCompactSupport_sq {v : ℝ → ℝ} (hvc : HasCompactSupport v) :
    HasCompactSupport fun y => v y ^ 2 := by
  have h := hvc.mul_left (f := v)
  have he : (fun y => v y ^ 2) = v * v := by
    funext y
    simp [pow_two]
  rw [he]
  exact h

theorem integrable_sq_of_compact {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable fun y => v y ^ 2 :=
  (hv.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hvc)

/-- The flat mass of `v` on the window `|y| ≤ a`. -/
def flatWindowMass (a : ℝ) (v : ℝ → ℝ) : ℝ := ∫ y in Icc (-a) a, v y ^ 2

theorem flatWindowMass_le {a m : ℝ} (hm0 : 0 < m) (hm : ∀ y, |y| ≤ a → m ≤ massDensity y)
    {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    flatWindowMass a v ≤ (∫ x, v x ^ 2 ∂massMeasure) / m := by
  rw [integral_mass, le_div_iff₀ hm0]
  unfold flatWindowMass
  have hint : Integrable fun x => massDensity x * v x ^ 2 :=
    (continuous_massDensity.mul (hv.pow 2)).integrable_of_hasCompactSupport
      (hasCompactSupport_sq hvc).mul_left
  calc (∫ y in Icc (-a) a, v y ^ 2) * m = ∫ y in Icc (-a) a, v y ^ 2 * m :=
        (integral_mul_const _ _).symm
    _ ≤ ∫ y in Icc (-a) a, massDensity y * v y ^ 2 := by
        refine setIntegral_mono_on ((integrable_sq_of_compact hv hvc).mul_const m).integrableOn
          hint.integrableOn measurableSet_Icc fun y hy => ?_
        have := hm y (abs_le.mpr (mem_Icc.mp hy))
        nlinarith [sq_nonneg (v y)]
    _ ≤ ∫ y, massDensity y * v y ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun y =>
          mul_nonneg (massDensity_pos y).le (sq_nonneg _))

/-- The square of `v` restricted to the window `|y| ≤ a`. -/
def windowSq (a : ℝ) (v : ℝ → ℝ) : ℝ → ℝ := (Icc (-a) a).indicator fun y => v y ^ 2

theorem windowSq_nonneg (a : ℝ) (v : ℝ → ℝ) (y : ℝ) : 0 ≤ windowSq a v y := by
  unfold windowSq
  exact Set.indicator_nonneg (fun y _ => sq_nonneg _) y

theorem sq_le_windowSq {a : ℝ} (v : ℝ → ℝ) {y : ℝ} (hy : |y| ≤ a) : v y ^ 2 ≤ windowSq a v y := by
  unfold windowSq
  rw [Set.indicator_of_mem (mem_Icc.mpr (abs_le.mp hy))]

theorem integrable_windowSq (a : ℝ) {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (windowSq a v) :=
  (integrable_sq_of_compact hv hvc).indicator measurableSet_Icc

theorem integral_windowSq (a : ℝ) (v : ℝ → ℝ) : ∫ y, windowSq a v y = flatWindowMass a v :=
  integral_indicator measurableSet_Icc

theorem windowTest_sq_le_windowSq {R : ℝ} (hR : 0 ≤ R) (v : ℝ → ℝ) (u : ℝ) :
    windowTest R hR v u ^ 2 ≤ windowSq (R + 3) v u := by
  by_cases hχ : windowBump R hR u = 0
  · unfold windowTest
    rw [hχ, zero_mul, zero_pow two_ne_zero]
    exact windowSq_nonneg _ _ _
  · have hu := abs_lt_of_windowBump_ne_zero hR hχ
    calc windowTest R hR v u ^ 2 = windowBump R hR u ^ 2 * v u ^ 2 := by
          unfold windowTest
          ring
      _ ≤ 1 * v u ^ 2 := mul_le_mul_of_nonneg_right (windowBump_sq_le_one R hR u) (sq_nonneg _)
      _ = v u ^ 2 := one_mul _
      _ ≤ windowSq (R + 3) v u := sq_le_windowSq v (by linarith)

theorem sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ## The localization inequality -/

/-- **Localization.** For every window radius `R` there is `C_R` such that every compact `C²` test
`v` satisfies `Q(χ_R v) ≤ C_R (J_arch(v) + ‖v‖²_μ)`. -/
theorem exists_window_levyForm_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v →
      levyForm (windowTest R hR v) ≤
        C * (phiDoobArchJumpEnergy v + ∫ x, v x ^ 2 ∂massMeasure) := by
  obtain ⟨m, hm0, hm⟩ := exists_theta_window_lower (a := R + 3) (by linarith)
  obtain ⟨m', hm'0, hm'⟩ := exists_mass_window_lower (a := R + 3) (by linarith)
  obtain ⟨L, hL⟩ := compact_source_lipschitz (contDiff_windowBump R hR)
    (hasCompactSupport_windowBump R hR)
  have hLip : ∀ x y, |windowBump R hR x - windowBump R hR y| ≤ (L : ℝ) * |x - y| := fun x y => by
    have h := hL.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at h
  have hsq : IntegrableOn (fun t => archLevyDensity t * t ^ 2) (Ioi 0) :=
    CHMDLightCone.integrableOn_archLevyDensity_mul_sq.congr_fun (fun t ht => by
      simp only
      rw [abs_of_pos (archLevyDensity_pos ht)]) measurableSet_Ioi
  set A₂ : ℝ := ∫ t in Ioi (0 : ℝ), archLevyDensity t * t ^ 2 with hA₂
  have hA₂0 : 0 ≤ A₂ := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (archLevyDensity_pos ht).le (sq_nonneg _)
  set c : ℝ := (2 * (L : ℝ) ^ 2 + 4) / m' with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨2 / m ^ 2 + A₂ * c, by positivity, fun v hv hvc => ?_⟩
  have hvC := hv.continuous
  set g := windowTest R hR v with hg_def
  have hg2 : ContDiff ℝ 2 g := contDiff_windowTest R hR hv
  have hgc : HasCompactSupport g := hasCompactSupport_windowTest R hR hvc
  set V := ∫ x, v x ^ 2 ∂massMeasure with hV
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  set J := phiDoobArchJumpEnergy v with hJ
  have hJ0 : 0 ≤ J := phiDoobArchJumpEnergy_nonneg v
  have hW : flatWindowMass (R + 3) v ≤ V / m' := flatWindowMass_le hm'0 hm' hvC hvc
  have hLHS := (levyForm_eq_fourier hg2 hgc).1
  have hJt : IntegrableOn (fun t => archLevyDensity t * ∫ x, phiDoobArchShiftJump v t x) (Ioi 0) :=
    (markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy hv hvc).1
  set G : ℝ → ℝ := fun t => 2 / m ^ 2 * (archLevyDensity t * ∫ x, phiDoobArchShiftJump v t x) +
    archLevyDensity t * t ^ 2 * (c * V) with hG_def
  have hG : IntegrableOn G (Ioi 0) := (hJt.const_mul _).add (hsq.mul_const _)
  have hW0 : Integrable (windowSq (R + 3) v) := integrable_windowSq _ hvC hvc
  have hcV : 4 * (V / m') ≤ c * V := by
    have h1 : c * V = 4 * (V / m') + 2 * (L : ℝ) ^ 2 * V / m' := by
      rw [hc]
      ring
    have h2 : 0 ≤ 2 * (L : ℝ) ^ 2 * V / m' := by positivity
    linarith
  -- the pointwise majorant
  have hpt : ∀ t ∈ Ioi (0 : ℝ), archLevyDensity t * ∫ u, (g u - g (u + t)) ^ 2 ≤ G t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hω := archLevyDensity_pos ht'
    have hJt0 : 0 ≤ ∫ x, phiDoobArchShiftJump v t x := integral_phiDoobArchShiftJump_nonneg v t
    have hWt : Integrable fun u => windowSq (R + 3) v (u + t) := hW0.comp_add_right t
    have hWt_int : ∫ u, windowSq (R + 3) v (u + t) = flatWindowMass (R + 3) v := by
      rw [integral_add_right_eq_self (windowSq (R + 3) v) t, integral_windowSq]
    have hPJ := integrable_shift_jump hvC hvc t
    have hI : (∫ u, (g u - g (u + t)) ^ 2) ≤
        2 / m ^ 2 * (∫ x, phiDoobArchShiftJump v t x) + t ^ 2 * (c * V) := by
      rcases le_or_lt t 1 with ht1 | ht1
      · -- short jumps
        have hpt' : ∀ u, (g u - g (u + t)) ^ 2 ≤ 2 / m ^ 2 * phiDoobArchShiftJump v t u +
            2 * (L : ℝ) ^ 2 * t ^ 2 * windowSq (R + 3) v (u + t) := by
          intro u
          have hPJ0 := phiDoobArchShiftJump_nonneg v t u
          have hWu := windowSq_nonneg (R + 3) v (u + t)
          by_cases hu : |u + t| ≤ R + 3
          · have hWle := sq_le_windowSq (a := R + 3) v hu
            have hsplit : g u - g (u + t) = windowBump R hR u * (v u - v (u + t)) +
                (windowBump R hR u - windowBump R hR (u + t)) * v (u + t) := by
              simp only [hg_def, windowTest]
              ring
            have hA : (windowBump R hR u * (v u - v (u + t))) ^ 2 ≤
                1 / m ^ 2 * phiDoobArchShiftJump v t u := by
              by_cases hχ : windowBump R hR u = 0
              · rw [hχ, zero_mul, zero_pow two_ne_zero]
                positivity
              · have hu2 : |u| < R + 2 := abs_lt_of_windowBump_ne_zero hR hχ
                have hΘ1 := hm u (by linarith)
                have hΘ2 := hm (u + t) hu
                have hm2 : m ^ 2 ≤ riemannKernelReal u * riemannKernelReal (u + t) := by
                  rw [pow_two]
                  exact mul_le_mul hΘ1 hΘ2 hm0.le (riemannKernelReal_pos u).le
                have h1le : 1 ≤ riemannKernelReal u * riemannKernelReal (u + t) / m ^ 2 :=
                  (one_le_div (by positivity)).mpr hm2
                unfold phiDoobArchShiftJump
                calc (windowBump R hR u * (v u - v (u + t))) ^ 2
                    = windowBump R hR u ^ 2 * (v u - v (u + t)) ^ 2 := by ring
                  _ ≤ 1 * (v u - v (u + t)) ^ 2 :=
                      mul_le_mul_of_nonneg_right (windowBump_sq_le_one R hR u) (sq_nonneg _)
                  _ ≤ (riemannKernelReal u * riemannKernelReal (u + t) / m ^ 2) *
                      (v u - v (u + t)) ^ 2 := mul_le_mul_of_nonneg_right h1le (sq_nonneg _)
                  _ = 1 / m ^ 2 * (riemannKernelReal u * riemannKernelReal (u + t) *
                      (v u - v (u + t)) ^ 2) := by ring
            have hB : ((windowBump R hR u - windowBump R hR (u + t)) * v (u + t)) ^ 2 ≤
                (L : ℝ) ^ 2 * t ^ 2 * windowSq (R + 3) v (u + t) := by
              have hl := hLip u (u + t)
              rw [show u - (u + t) = -t by ring, abs_neg, abs_of_pos ht'] at hl
              have h1 : (windowBump R hR u - windowBump R hR (u + t)) ^ 2 ≤ ((L : ℝ) * t) ^ 2 := by
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) hl 2
              calc ((windowBump R hR u - windowBump R hR (u + t)) * v (u + t)) ^ 2
                  = (windowBump R hR u - windowBump R hR (u + t)) ^ 2 * v (u + t) ^ 2 := by ring
                _ ≤ ((L : ℝ) * t) ^ 2 * v (u + t) ^ 2 :=
                    mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
                _ ≤ ((L : ℝ) * t) ^ 2 * windowSq (R + 3) v (u + t) :=
                    mul_le_mul_of_nonneg_left hWle (by positivity)
                _ = (L : ℝ) ^ 2 * t ^ 2 * windowSq (R + 3) v (u + t) := by ring
            rw [hsplit]
            calc (windowBump R hR u * (v u - v (u + t)) +
                  (windowBump R hR u - windowBump R hR (u + t)) * v (u + t)) ^ 2
                ≤ 2 * (windowBump R hR u * (v u - v (u + t))) ^ 2 +
                  2 * ((windowBump R hR u - windowBump R hR (u + t)) * v (u + t)) ^ 2 :=
                  sq_add_le_two _ _
              _ ≤ 2 * (1 / m ^ 2 * phiDoobArchShiftJump v t u) +
                  2 * ((L : ℝ) ^ 2 * t ^ 2 * windowSq (R + 3) v (u + t)) := by
                  linarith
              _ = 2 / m ^ 2 * phiDoobArchShiftJump v t u +
                  2 * (L : ℝ) ^ 2 * t ^ 2 * windowSq (R + 3) v (u + t) := by ring
          · have hu' : R + 3 < |u + t| := lt_of_not_ge hu
            have hχ2 : windowBump R hR (u + t) = 0 := windowBump_eq_zero hR (by linarith)
            have hχ1 : windowBump R hR u = 0 := by
              apply windowBump_eq_zero hR
              have h := abs_sub_abs_le_abs_sub (u + t) u
              rw [show u + t - u = t by ring, abs_of_pos ht'] at h
              linarith
            have h0 : g u - g (u + t) = 0 := by
              simp only [hg_def, windowTest]
              rw [hχ1, hχ2]
              ring
            rw [h0, zero_pow two_ne_zero]
            positivity
        calc (∫ u, (g u - g (u + t)) ^ 2)
            ≤ ∫ u, 2 / m ^ 2 * phiDoobArchShiftJump v t u +
                2 * (L : ℝ) ^ 2 * t ^ 2 * windowSq (R + 3) v (u + t) :=
              integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
                ((hPJ.const_mul _).add (hWt.const_mul _)) (Eventually.of_forall hpt')
          _ = 2 / m ^ 2 * (∫ x, phiDoobArchShiftJump v t x) +
                2 * (L : ℝ) ^ 2 * t ^ 2 * flatWindowMass (R + 3) v := by
              rw [integral_add (hPJ.const_mul _) (hWt.const_mul _), integral_const_mul,
                integral_const_mul, hWt_int]
          _ ≤ 2 / m ^ 2 * (∫ x, phiDoobArchShiftJump v t x) + t ^ 2 * (c * V) := by
              have h1 : 2 * (L : ℝ) ^ 2 * t ^ 2 * flatWindowMass (R + 3) v ≤
                  2 * (L : ℝ) ^ 2 * t ^ 2 * (V / m') :=
                mul_le_mul_of_nonneg_left hW (by positivity)
              have h2 : 2 * (L : ℝ) ^ 2 * t ^ 2 * (V / m') ≤ t ^ 2 * (c * V) := by
                have h3 : t ^ 2 * (c * V) = 2 * (L : ℝ) ^ 2 * t ^ 2 * (V / m') +
                    t ^ 2 * (4 / m' * V) := by
                  rw [hc]
                  ring
                have h4 : 0 ≤ t ^ 2 * (4 / m' * V) := by positivity
                linarith
              linarith
      · -- long jumps
        have hpt' : ∀ u, (g u - g (u + t)) ^ 2 ≤
            2 * windowSq (R + 3) v u + 2 * windowSq (R + 3) v (u + t) := by
          intro u
          have h1 := windowTest_sq_le_windowSq hR v u
          have h2 := windowTest_sq_le_windowSq hR v (u + t)
          calc (g u - g (u + t)) ^ 2 = (g u + -g (u + t)) ^ 2 := by ring
            _ ≤ 2 * g u ^ 2 + 2 * (-g (u + t)) ^ 2 := sq_add_le_two _ _
            _ = 2 * windowTest R hR v u ^ 2 + 2 * windowTest R hR v (u + t) ^ 2 := by
                simp only [hg_def]
                ring
            _ ≤ 2 * windowSq (R + 3) v u + 2 * windowSq (R + 3) v (u + t) := by linarith
        have ht2 : 1 ≤ t ^ 2 := by nlinarith
        calc (∫ u, (g u - g (u + t)) ^ 2)
            ≤ ∫ u, 2 * windowSq (R + 3) v u + 2 * windowSq (R + 3) v (u + t) :=
              integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
                ((hW0.const_mul 2).add (hWt.const_mul 2)) (Eventually.of_forall hpt')
          _ = 4 * flatWindowMass (R + 3) v := by
              rw [integral_add (hW0.const_mul 2) (hWt.const_mul 2), integral_const_mul,
                integral_const_mul, hWt_int, integral_windowSq]
              ring
          _ ≤ 4 * (V / m') := by linarith
          _ ≤ 1 * (c * V) := by linarith
          _ ≤ t ^ 2 * (c * V) := mul_le_mul_of_nonneg_right ht2 (mul_nonneg hc0 hV0)
          _ ≤ 2 / m ^ 2 * (∫ x, phiDoobArchShiftJump v t x) + t ^ 2 * (c * V) := by
              have : 0 ≤ 2 / m ^ 2 * (∫ x, phiDoobArchShiftJump v t x) :=
                mul_nonneg (by positivity) hJt0
              linarith
    calc archLevyDensity t * ∫ u, (g u - g (u + t)) ^ 2
        ≤ archLevyDensity t * (2 / m ^ 2 * (∫ x, phiDoobArchShiftJump v t x) + t ^ 2 * (c * V)) :=
          mul_le_mul_of_nonneg_left hI hω.le
      _ = G t := by
          simp only [hG_def]
          ring
  have h1 : levyForm g ≤ ∫ t in Ioi (0 : ℝ), G t := by
    unfold levyForm
    exact setIntegral_mono_on hLHS hG measurableSet_Ioi hpt
  have h2 : (∫ t in Ioi (0 : ℝ), G t) = 2 / m ^ 2 * J + A₂ * (c * V) := by
    simp only [hG_def]
    rw [integral_add (hJt.const_mul _) (hsq.mul_const _), integral_const_mul, integral_mul_const]
  calc levyForm g ≤ ∫ t in Ioi (0 : ℝ), G t := h1
    _ = 2 / m ^ 2 * J + A₂ * (c * V) := h2
    _ ≤ (2 / m ^ 2 + A₂ * c) * (J + V) := by
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / m ^ 2) hV0,
          mul_nonneg (mul_nonneg hA₂0 hc0) hJ0]

end RHTower.CHMDPolar
