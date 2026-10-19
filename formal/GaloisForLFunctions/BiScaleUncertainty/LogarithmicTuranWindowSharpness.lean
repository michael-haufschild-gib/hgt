import GaloisForLFunctions.BiScaleUncertainty.LogarithmicTuranWindowLaw
import GaloisForLFunctions.BiScaleUncertainty.FiniteSpectralEnvelopeRealization
import GaloisForLFunctions.BiScaleUncertainty.SquareRootDensityPoleInvisibility

/-!
# The logarithmic Beurling–Turán window law is attained

`LogarithmicTuranWindowLaw` proves `|∫_0^{(M+1)δ} h| ≤ 12δ(4 + log(M+1)) h(0)` whenever
`h(mδ) = 0` for `1 ≤ m ≤ M`. The logarithm is the true order: for every `M` and `δ` there is a
compact `C²` source with these zeros and

`∫_0^{(M+1)δ} h ≥ (δ/4π) log(M + 2) h(0)`.

**Quarter-shifted spectrum.** With `A = (M+1)δ` and `ω_k = 2π(k + 1/4)/A`, the mixture
`C(x) = (M+1)⁻¹ Σ_{k ≤ M} cos(ω_k x)` vanishes at every `mδ`, `1 ≤ m ≤ M`: the telescoping
`2 sin(θ/2) cos((k+1/4)θ) = sin((k+3/4)θ) - sin((k-1/4)θ)` at `θ = 2πm/(M+1)` closes because
`(M+1)θ ∈ 2πℤ`. The quarter shift makes every atom contribute with the same sign to the window:
`∫_0^A cos(ω_k x) dx = sin(2π(k+1/4))/ω_k = A/(2π(k+1/4))`, so `∫_0^A C` is a harmonic sum.
A wide envelope `φ` (the corpus bump stretched by `R`) has `h_φ(0) - h_φ(x) ≤ M|x|` uniformly in `R`
while `h_φ(0)` grows like `R`, so the source realizing `h_φ(x) C(x)` exactly on `[-A, A]`
(`exists_scalar_spectral_envelope`) keeps a definite fraction of the harmonic sum.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. The quarter-shifted cosine mixture -/

/-- Atoms `((M+1)⁻¹, 2π(k + 1/4)/A)`, `k ≤ M`. -/
def quarterAtoms (M : ℕ) (A : ℝ) : List (ℝ × ℝ) :=
  (List.range (M + 1)).map fun k : ℕ => (((M : ℝ) + 1)⁻¹, 2 * Real.pi * ((k : ℝ) + 1 / 4) / A)

private theorem list_sum_map_range {β : Type*} [AddCommMonoid β] (g : ℕ → β) (n : ℕ) :
    ((List.range n).map g).sum = ∑ k ∈ Finset.range n, g k := by
  induction n with
  | zero => rw [List.range_zero, List.map_nil, List.sum_nil, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
      List.map_singleton, List.sum_singleton]

theorem cosineMixture_quarterAtoms (M : ℕ) (A x : ℝ) :
    cosineMixture (quarterAtoms M A) x = ((M : ℝ) + 1)⁻¹ *
      ∑ k ∈ Finset.range (M + 1), Real.cos (2 * Real.pi * ((k : ℝ) + 1 / 4) / A * x) := by
  unfold cosineMixture quarterAtoms
  rw [List.map_map, Finset.mul_sum]
  exact list_sum_map_range (β := ℝ) (fun k : ℕ => ((M : ℝ) + 1)⁻¹ *
    Real.cos (2 * Real.pi * ((k : ℝ) + 1 / 4) / A * x)) (M + 1)

theorem quarterAtoms_weights_nonneg (M : ℕ) (A : ℝ) : ∀ p ∈ quarterAtoms M A, 0 ≤ p.1 := by
  intro p hp
  unfold quarterAtoms at hp
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
  positivity

theorem cosineMixture_quarterAtoms_zero (M : ℕ) (A : ℝ) :
    cosineMixture (quarterAtoms M A) 0 = 1 := by
  rw [cosineMixture_quarterAtoms]
  simp only [mul_zero, Real.cos_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  field_simp

theorem abs_cosineMixture_quarterAtoms_le (M : ℕ) (A x : ℝ) :
    |cosineMixture (quarterAtoms M A) x| ≤ 1 := by
  rw [cosineMixture_quarterAtoms, abs_mul, abs_of_pos (by positivity)]
  have h : |∑ k ∈ Finset.range (M + 1), Real.cos (2 * Real.pi * ((k : ℝ) + 1 / 4) / A * x)| ≤
      (M : ℝ) + 1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _k ∈ Finset.range (M + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => Real.abs_cos_le_one _
      _ = (M : ℝ) + 1 := by simp
  calc
    _ ≤ ((M : ℝ) + 1)⁻¹ * ((M : ℝ) + 1) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := by field_simp

/-- **Quarter-shifted cancellation:** `Σ_{k ≤ M} cos((k + 1/4) 2πm/(M+1)) = 0` for `1 ≤ m ≤ M`. -/
theorem sum_cos_quarter_eq_zero {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    ∑ k ∈ Finset.range (M + 1),
      Real.cos (((k : ℝ) + 1 / 4) * (2 * Real.pi * m / ((M : ℝ) + 1))) = 0 := by
  set θ : ℝ := 2 * Real.pi * m / ((M : ℝ) + 1) with hθ
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hsin : Real.sin (θ / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < m := by exact_mod_cast hm1
      rw [hθ]; positivity
    · rw [hθ, show 2 * Real.pi * m / ((M : ℝ) + 1) / 2 = Real.pi * (m / ((M : ℝ) + 1)) by ring]
      have : (m : ℝ) / ((M : ℝ) + 1) < 1 := by
        rw [div_lt_one hM1]; have : (m : ℝ) ≤ M := by exact_mod_cast hmM
        linarith
      nlinarith [Real.pi_pos]
  have htel : ∀ k : ℕ, 2 * Real.sin (θ / 2) * Real.cos (((k : ℝ) + 1 / 4) * θ) =
      Real.sin ((((k + 1 : ℕ) : ℝ) - 1 / 4) * θ) - Real.sin (((k : ℝ) - 1 / 4) * θ) := by
    intro k
    rw [Real.sin_sub_sin]
    push_cast
    ring_nf
  have hsum : 2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range (M + 1),
      Real.cos (((k : ℝ) + 1 / 4) * θ) = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => htel k,
      Finset.sum_range_sub (fun k : ℕ => Real.sin (((k : ℝ) - 1 / 4) * θ))]
    have hend : (((M + 1 : ℕ) : ℝ) - 1 / 4) * θ = -(1 / 4 * θ) + (m : ℕ) * (2 * Real.pi) := by
      rw [hθ]; push_cast; field_simp; ring
    rw [hend, Real.sin_add_nat_mul_two_pi]
    push_cast
    rw [show ((0 : ℝ) - 1 / 4) * θ = -(1 / 4 * θ) by ring]
    ring
  have h2 : 2 * Real.sin (θ / 2) ≠ 0 := mul_ne_zero two_ne_zero hsin
  exact (mul_eq_zero.mp hsum).resolve_left h2

/-- The mixture vanishes at every interior node `mδ` of the window `A = (M+1)δ`. -/
theorem cosineMixture_quarterAtoms_node {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M) {δ : ℝ}
    (hδ : 0 < δ) :
    cosineMixture (quarterAtoms M (((M : ℝ) + 1) * δ)) ((m : ℝ) * δ) = 0 := by
  rw [cosineMixture_quarterAtoms]
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have e : ∀ k : ℕ, 2 * Real.pi * ((k : ℝ) + 1 / 4) / (((M : ℝ) + 1) * δ) * ((m : ℝ) * δ) =
      ((k : ℝ) + 1 / 4) * (2 * Real.pi * m / ((M : ℝ) + 1)) := by
    intro k; field_simp
  simp only [e]
  rw [sum_cos_quarter_eq_zero hm1 hmM, mul_zero]

/-- The window integral of the mixture is a harmonic sum. -/
theorem integral_cosineMixture_quarterAtoms (M : ℕ) {A : ℝ} (hA : 0 < A) :
    ∫ x in (0 : ℝ)..A, cosineMixture (quarterAtoms M A) x =
      ((M : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (M + 1), A / (2 * Real.pi * ((k : ℝ) + 1 / 4)) := by
  simp only [cosineMixture_quarterAtoms]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hω : 2 * Real.pi * ((k : ℝ) + 1 / 4) / A ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hω, integral_cos, mul_zero,
      Real.sin_zero, sub_zero, smul_eq_mul]
    have hs : Real.sin (2 * Real.pi * ((k : ℝ) + 1 / 4) / A * A) = 1 := by
      rw [show 2 * Real.pi * ((k : ℝ) + 1 / 4) / A * A = Real.pi / 2 + (k : ℕ) * (2 * Real.pi) by
        field_simp; ring, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
    rw [hs, mul_one, inv_div]
  · intro k _
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- `Σ_{k ≤ M} 1/(k + 1/4) ≥ log(M + 2)`. -/
theorem log_le_sum_inv_quarter (M : ℕ) :
    Real.log ((M : ℝ) + 2) ≤ ∑ k ∈ Finset.range (M + 1), 1 / ((k : ℝ) + 1 / 4) := by
  have h1 := log_add_one_le_harmonic (M + 1)
  have h2 : (harmonic (M + 1) : ℝ) = ∑ k ∈ Finset.range (M + 1), 1 / ((k : ℝ) + 1) := by
    rw [harmonic]; push_cast; refine Finset.sum_congr rfl fun k _ => ?_; rw [one_div]
  have h3 : ∑ k ∈ Finset.range (M + 1), 1 / ((k : ℝ) + 1) ≤
      ∑ k ∈ Finset.range (M + 1), 1 / ((k : ℝ) + 1 / 4) :=
    Finset.sum_le_sum fun k _ => one_div_le_one_div_of_le (by positivity) (by linarith)
  have h4 : ((M + 1 + 1 : ℕ) : ℝ) = (M : ℝ) + 2 := by push_cast; ring
  rw [h4] at h1
  linarith

/-! ### 2. A wide envelope -/

/-- The corpus bump stretched by `R`. -/
abbrev wideBump (R : ℝ) : ℝ → ℝ := sourceRescale pairBump R⁻¹

/-- **The window law is attained.** For every `M` and `δ > 0` there is a compact `C²` source
with `h(mδ) = 0` for `1 ≤ m ≤ M` and `∫_0^{(M+1)δ} h ≥ (δ/4π) log(M + 2) h(0)`. -/
theorem exists_source_log_window_lower (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℝ → ℝ, ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ 0 < autocorr k 0 ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr k ((m : ℝ) * δ) = 0) ∧
      δ / (4 * Real.pi) * Real.log ((M : ℝ) + 2) * autocorr k 0 ≤
        ∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), autocorr k x := by
  set A : ℝ := ((M : ℝ) + 1) * δ with hA
  have hA0 : 0 < A := by positivity
  have hAcast : (((M + 1 : ℕ) : ℝ) * δ) = A := by rw [hA]; push_cast; ring
  obtain ⟨Mb, hMb, hinc⟩ := exists_autocorr_increment_linear_bound contDiff_pairBump
    hasCompactSupport_pairBump
  have hb0 := autocorr_pairBump_zero_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogM : Real.log 2 ≤ Real.log ((M : ℝ) + 2) :=
    Real.log_le_log two_pos (by have := Nat.cast_nonneg (α := ℝ) M; linarith)
  set R : ℝ := max 1 (2 * Real.pi * Mb * A ^ 2 / (δ * autocorr pairBump 0 * Real.log 2)) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hRbig : 2 * Real.pi * Mb * A ^ 2 / (δ * autocorr pairBump 0 * Real.log 2) ≤ R :=
    le_max_right _ _
  have hφ : ContDiff ℝ 2 (wideBump R) := contDiff_sourceRescale contDiff_pairBump _
  have hφc : HasCompactSupport (wideBump R) :=
    hasCompactSupport_sourceRescale hasCompactSupport_pairBump (inv_pos.mpr hR0)
  have hφx : ∀ x, autocorr (wideBump R) x = R * autocorr pairBump (R⁻¹ * x) := by
    intro x; rw [autocorr_sourceRescale pairBump (inv_pos.mpr hR0), inv_inv]
  have hφ0 : autocorr (wideBump R) 0 = R * autocorr pairBump 0 := by rw [hφx, mul_zero]
  have hφinc : ∀ x, autocorr (wideBump R) 0 - autocorr (wideBump R) x ≤ Mb * |x| := by
    intro x
    rw [hφ0, hφx, ← mul_sub]
    have := hinc (R⁻¹ * x)
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR0)] at this
    calc
      R * (autocorr pairBump 0 - autocorr pairBump (R⁻¹ * x)) ≤ R * (Mb * (R⁻¹ * |x|)) :=
        mul_le_mul_of_nonneg_left this hR0.le
      _ = Mb * |x| := by field_simp
  obtain ⟨k, hk, hkc, hloc, -⟩ := exists_scalar_spectral_envelope (quarterAtoms M A)
    (r := 2) le_rfl hφ hφc (quarterAtoms_weights_nonneg M A) A
  have hk0 : autocorr k 0 = R * autocorr pairBump 0 := by
    rw [hloc 0 (by rw [abs_zero]; exact hA0.le), cosineMixture_quarterAtoms_zero, mul_one, hφ0]
  refine ⟨k, hk, hkc, by rw [hk0]; positivity, fun m hm1 hmM => ?_, ?_⟩
  · have hmA : |(m : ℝ) * δ| ≤ A := by
      rw [abs_of_nonneg (by positivity), hA]
      have : (m : ℝ) ≤ M := by exact_mod_cast hmM
      nlinarith
    rw [hloc _ hmA, cosineMixture_quarterAtoms_node hm1 hmM hδ, mul_zero]
  · rw [hAcast]
    have hcongr : ∫ x in (0 : ℝ)..A, autocorr k x =
        ∫ x in (0 : ℝ)..A, autocorr (wideBump R) x * cosineMixture (quarterAtoms M A) x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hA0.le] at hx
      exact hloc x (by rw [abs_of_nonneg hx.1]; exact hx.2)
    rw [hcongr]
    set C : ℝ → ℝ := cosineMixture (quarterAtoms M A) with hC
    have hCc : Continuous C := by
      have e : C = fun x => ((M : ℝ) + 1)⁻¹ *
          ∑ k ∈ Finset.range (M + 1), Real.cos (2 * Real.pi * ((k : ℝ) + 1 / 4) / A * x) :=
        funext (cosineMixture_quarterAtoms M A)
      rw [e]
      fun_prop
    have hφcont : Continuous (autocorr (wideBump R)) := continuous_autocorr hφ hφc
    have hsplit : ∫ x in (0 : ℝ)..A, autocorr (wideBump R) x * C x =
        autocorr (wideBump R) 0 * (∫ x in (0 : ℝ)..A, C x) -
          ∫ x in (0 : ℝ)..A, (autocorr (wideBump R) 0 - autocorr (wideBump R) x) * C x := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun x _ => ?_
        ring
      · exact (continuous_const.mul hCc).intervalIntegrable _ _
      · exact ((continuous_const.sub hφcont).mul hCc).intervalIntegrable _ _
    have herr : ∫ x in (0 : ℝ)..A, (autocorr (wideBump R) 0 - autocorr (wideBump R) x) * C x ≤
        Mb * A ^ 2 / 2 := by
      have hle : ∀ x ∈ Icc (0 : ℝ) A,
          (autocorr (wideBump R) 0 - autocorr (wideBump R) x) * C x ≤ Mb * x := by
        intro x hx
        have h1 := hφinc x
        rw [abs_of_nonneg hx.1] at h1
        have h2 := abs_cosineMixture_quarterAtoms_le M A x
        have h3 : 0 ≤ autocorr (wideBump R) 0 - autocorr (wideBump R) x :=
          autocorr_sub_nonneg hφc hφ.continuous x
        calc
          _ ≤ |(autocorr (wideBump R) 0 - autocorr (wideBump R) x) * C x| := le_abs_self _
          _ = (autocorr (wideBump R) 0 - autocorr (wideBump R) x) * |C x| := by
            rw [abs_mul, abs_of_nonneg h3]
          _ ≤ (autocorr (wideBump R) 0 - autocorr (wideBump R) x) * 1 :=
            mul_le_mul_of_nonneg_left h2 h3
          _ ≤ Mb * x := by linarith
      calc
        _ ≤ ∫ x in (0 : ℝ)..A, Mb * x :=
          intervalIntegral.integral_mono_on hA0.le
            (((continuous_const.sub hφcont).mul hCc).intervalIntegrable _ _)
            ((continuous_const.mul continuous_id).intervalIntegrable _ _) hle
        _ = Mb * A ^ 2 / 2 := by
          rw [intervalIntegral.integral_const_mul, integral_id]; ring
    have hmain : δ / (2 * Real.pi) * Real.log ((M : ℝ) + 2) ≤ ∫ x in (0 : ℝ)..A, C x := by
      rw [hC, integral_cosineMixture_quarterAtoms M hA0]
      have hsum := log_le_sum_inv_quarter M
      have e : ((M : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (M + 1), A / (2 * Real.pi * ((k : ℝ) + 1 / 4)) =
          δ / (2 * Real.pi) * ∑ k ∈ Finset.range (M + 1), 1 / ((k : ℝ) + 1 / 4) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hA]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    have hRb : Mb * A ^ 2 / 2 ≤
        δ / (4 * Real.pi) * Real.log ((M : ℝ) + 2) * (R * autocorr pairBump 0) := by
      have hden : 0 < δ * autocorr pairBump 0 * Real.log 2 := by positivity
      have h1 : 2 * Real.pi * Mb * A ^ 2 ≤ R * (δ * autocorr pairBump 0 * Real.log 2) := by
        rwa [div_le_iff₀ hden] at hRbig
      have h2 : δ / (4 * Real.pi) * Real.log 2 * (R * autocorr pairBump 0) ≤
          δ / (4 * Real.pi) * Real.log ((M : ℝ) + 2) * (R * autocorr pairBump 0) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogM (by positivity)) (by positivity)
      have h3 : Mb * A ^ 2 / 2 = (2 * Real.pi * Mb * A ^ 2) / (4 * Real.pi) := by
        field_simp; ring
      have h4 : R * (δ * autocorr pairBump 0 * Real.log 2) / (4 * Real.pi) =
          δ / (4 * Real.pi) * Real.log 2 * (R * autocorr pairBump 0) := by ring
      rw [h3]
      have := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
      linarith
    rw [hsplit, hk0]
    have h5 : autocorr (wideBump R) 0 * ∫ x in (0 : ℝ)..A, C x =
        R * autocorr pairBump 0 * ∫ x in (0 : ℝ)..A, C x := by rw [hφ0]
    have hpos : 0 ≤ R * autocorr pairBump 0 := by positivity
    have := mul_le_mul_of_nonneg_left hmain hpos
    have e2 : R * autocorr pairBump 0 * (δ / (2 * Real.pi) * Real.log ((M : ℝ) + 2)) =
        2 * (δ / (4 * Real.pi) * Real.log ((M : ℝ) + 2) * (R * autocorr pairBump 0)) := by
      field_simp; ring
    linarith

/-- **Two-sided logarithmic order.** On sources with `h(mδ) = 0`, `1 ≤ m ≤ M`, the best constant
in `∫_0^{(M+1)δ} h ≤ c_M δ h(0)` lies between `log(M + 2)/(4π)` and `12(4 + log(M + 1))`. -/
theorem log_window_two_sided (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
        (∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * δ) = 0) →
        ∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), autocorr f x ≤
          12 * δ * (4 + Real.log ((M + 1 : ℕ) : ℝ)) * autocorr f 0) ∧
      ∃ k : ℝ → ℝ, ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ 0 < autocorr k 0 ∧
        (∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr k ((m : ℝ) * δ) = 0) ∧
        δ / (4 * Real.pi) * Real.log ((M : ℝ) + 2) * autocorr k 0 ≤
          ∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), autocorr k x :=
  ⟨fun _ hf hfc hz =>
    (le_abs_self _).trans (abs_integral_autocorr_le_log_of_arithmetic_zeros hf hfc hδ M hz),
    exists_source_log_window_lower M hδ⟩

end

end GaloisForLFunctions.BiScaleUncertainty
