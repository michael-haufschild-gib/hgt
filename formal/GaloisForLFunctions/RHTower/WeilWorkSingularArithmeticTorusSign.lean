import GaloisForLFunctions.RHTower.WeilConeNotchBochnerLaw
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuous torus densities of actual notch kernels

A continuous density whose Fourier coefficients equal an actual limiting notch
kernel has nonpositive real part. Only the symmetric part of the kernel enters
its real quadratic form. This module does not assert that a general source
has such a density, nor does it supply the C49 Euler-density identity.
-/

open MeasureTheory Filter Topology

namespace RHTower.WeilSingularArithmetic

variable {d : Type*} [Fintype d]

private theorem continuous_torusQuadratic (V : C(UnitAddTorus d, ℝ)) :
    Continuous (fun Q : C(UnitAddTorus d, ℂ) => ∫ x, V x * ‖Q x‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro Q₀
  apply continuousAt_of_dominated (bound := fun _ => ‖V‖ * (‖Q₀‖ + 1) ^ 2)
  · exact Filter.Eventually.of_forall fun Q =>
      (V.continuous.mul (Q.continuous.norm.pow 2)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds Q₀ (by norm_num : (0 : ℝ) < 1)] with Q hQ
    apply Filter.Eventually.of_forall
    intro x
    have hQ' : ‖Q - Q₀‖ < 1 := by simpa [dist_eq_norm] using hQ
    have hnorm : ‖Q x‖ ≤ ‖Q₀‖ + 1 := by
      calc
        ‖Q x‖ ≤ ‖Q‖ := Q.norm_coe_le_norm x
        _ ≤ ‖Q - Q₀‖ + ‖Q₀‖ := norm_le_norm_sub_add Q Q₀
        _ ≤ ‖Q₀‖ + 1 := by linarith
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (V.norm_coe_le_norm x) (sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hnorm)
      (sq_nonneg _) (norm_nonneg _)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun x =>
      (continuous_const.mul ((continuous_eval_const x).norm.pow 2)).continuousAt

/-- A continuous real torus density is nonpositive if all squared character
polynomials have nonpositive integral against it. -/
theorem nonpos_of_torusQuadratic_nonpos (V : C(UnitAddTorus d, ℝ))
    (hQ : ∀ Q ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d))),
      (∫ x, V x * ‖Q x‖ ^ 2) ≤ 0) : ∀ x, V x ≤ 0 := by
  have hclosed : IsClosed {Q : C(UnitAddTorus d, ℂ) | (∫ x, V x * ‖Q x‖ ^ 2) ≤ 0} :=
    isClosed_le (continuous_torusQuadratic V) continuous_const
  have hclosure := closure_minimal hQ hclosed
  rw [← Submodule.topologicalClosure_coe, UnitAddTorus.span_mFourier_closure_eq_top] at hclosure
  let Q : C(UnitAddTorus d, ℂ) :=
    ⟨fun x => (max (V x) 0 : ℝ), Complex.continuous_ofReal.comp (V.continuous.max continuous_const)⟩
  have hQle : (∫ x, V x * ‖Q x‖ ^ 2) ≤ 0 := hclosure (Submodule.mem_top)
  have hnonneg : ∀ x, 0 ≤ V x * ‖Q x‖ ^ 2 := by
    intro x
    by_cases hx : 0 ≤ V x
    · exact mul_nonneg hx (sq_nonneg _)
    · simp [Q, max_eq_right (le_of_not_ge hx)]
  have hzero : (∫ x, V x * ‖Q x‖ ^ 2) = 0 :=
    le_antisymm hQle (integral_nonneg hnonneg)
  have hc : Continuous fun x => V x * ‖Q x‖ ^ 2 :=
    V.continuous.mul (Q.continuous.norm.pow 2)
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hzero
  have heq := (hc.ae_eq_iff_eq volume continuous_const).1 hae
  intro x
  by_contra hx
  have hpos : 0 < V x := lt_of_not_ge hx
  have hz := congrFun heq x
  have hqp : 0 < ‖Q x‖ ^ 2 := by
    simp only [Q, ContinuousMap.coe_mk, max_eq_left hpos.le, Complex.norm_real,
      Real.norm_of_nonneg hpos.le]
    positivity
  exact (ne_of_gt (mul_pos hpos hqp)) hz

private theorem torusQuadratic_eq (V : C(UnitAddTorus d, ℝ))
    (K : (d → ℤ) → ℝ)
    (hK : ∀ a b, (∫ x, (V x : ℂ) * UnitAddTorus.mFourier (a - b) x) = K (a - b))
    (A : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    (∫ x, V x * ‖∑ a ∈ A, c a * UnitAddTorus.mFourier a x‖ ^ 2) =
      (∑ a ∈ A, ∑ b ∈ A, (c a).re * (c b).re * K (a - b)) +
      (∑ a ∈ A, ∑ b ∈ A, (c a).im * (c b).im * K (a - b)) := by
  let Q (x : UnitAddTorus d) := ∑ a ∈ A, c a * UnitAddTorus.mFourier a x
  let T (a b : d → ℤ) (x : UnitAddTorus d) :=
    (c a * starRingEnd ℂ (c b)) * ((V x : ℂ) * UnitAddTorus.mFourier (a - b) x)
  have hTc (a b : d → ℤ) : Continuous (T a b) :=
    continuous_const.mul ((Complex.continuous_ofReal.comp V.continuous).mul
      (UnitAddTorus.mFourier (a - b)).continuous)
  have hTi (a b : d → ℤ) : Integrable (T a b) :=
    (hTc a b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (x : UnitAddTorus d) :
      (V x : ℂ) * (Q x * starRingEnd ℂ (Q x)) = ∑ a ∈ A, ∑ b ∈ A, T a b x := by
    simp only [Q, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [T, sub_eq_add_neg, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_neg]
    ring
  have hsum : (∫ x, (V x : ℂ) * (Q x * starRingEnd ℂ (Q x))) =
      ∑ a ∈ A, ∑ b ∈ A, (c a * starRingEnd ℂ (c b)) * (K (a - b) : ℂ) := by
    simp_rw [hpoint]
    rw [integral_finsetSum A (fun a _ => integrable_finsetSum A (fun b _ => hTi a b))]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum A (fun b _ => hTi a b)]
    apply Finset.sum_congr rfl
    intro b hb
    exact (integral_const_mul _ _).trans (congrArg _ (hK a b))
  have hcQ : Continuous Q := by unfold Q; fun_prop
  have hi : Integrable (fun x => (V x : ℂ) * (Q x * starRingEnd ℂ (Q x))) :=
    ((Complex.continuous_ofReal.comp V.continuous).mul (hcQ.mul hcQ.star)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq := (integral_re hi).trans (congrArg Complex.re hsum)
  change (∫ x, ((V x : ℂ) * (Q x * starRingEnd ℂ (Q x))).re) = _ at heq
  simp only [Complex.mul_conj, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, ← Complex.sq_norm] at heq
  dsimp only [Q] at heq
  rw [heq]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, sub_zero]
  simp only [mul_neg, sub_neg_eq_add, add_mul, Finset.sum_add_distrib]

/-- The real Fourier matrix suffices: complex coefficients split into their
real and imaginary quadratic forms. -/
theorem nonpos_of_real_fourier_quadratic (V : C(UnitAddTorus d, ℝ))
    (K : (d → ℤ) → ℝ)
    (hK : ∀ a b, (∫ x, (V x : ℂ) * UnitAddTorus.mFourier (a - b) x) = K (a - b))
    (hQ : ∀ (A : Finset (d → ℤ)) (c : (d → ℤ) → ℝ),
      ∑ a ∈ A, ∑ b ∈ A, c a * c b * K (a - b) ≤ 0) : ∀ x, V x ≤ 0 := by
  apply nonpos_of_torusQuadratic_nonpos
  intro Q hQspan
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hQspan
  have h := torusQuadratic_eq V K hK c.support c
  simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  rw [h]
  exact add_nonpos (hQ _ (fun a => (c a).re)) (hQ _ (fun a => (c a).im))

/-- Taking the real part symmetrizes a real-valued Fourier coefficient sequence. -/
theorem integral_re_density_character (U : C(UnitAddTorus d, ℂ))
    (K : (d → ℤ) → ℝ)
    (hK : ∀ g, (∫ x, U x * UnitAddTorus.mFourier g x) = K g) (g : d → ℤ) :
    (∫ x, ((U x).re : ℂ) * UnitAddTorus.mFourier g x) =
      ((K g + K (-g)) / 2 : ℝ) := by
  have hi : Integrable (fun x => U x * UnitAddTorus.mFourier g x) :=
    (U.continuous.mul (UnitAddTorus.mFourier g).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hci : Integrable (fun x => starRingEnd ℂ (U x) * UnitAddTorus.mFourier g x) :=
    (U.continuous.star.mul (UnitAddTorus.mFourier g).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hconj : (∫ x, starRingEnd ℂ (U x) * UnitAddTorus.mFourier g x) = (K (-g) : ℂ) := by
    calc
      _ = ∫ x, starRingEnd ℂ (U x * UnitAddTorus.mFourier (-g) x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by simp [map_mul, UnitAddTorus.mFourier_neg]
      _ = starRingEnd ℂ (∫ x, U x * UnitAddTorus.mFourier (-g) x) := integral_conj
      _ = _ := by rw [hK]; simp
  calc
    _ = (∫ x, (U x * UnitAddTorus.mFourier g x +
        starRingEnd ℂ (U x) * UnitAddTorus.mFourier g x) / 2) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [← add_mul, Complex.add_conj]
      push_cast
      ring
    _ = ((∫ x, U x * UnitAddTorus.mFourier g x) +
        (∫ x, starRingEnd ℂ (U x) * UnitAddTorus.mFourier g x)) / 2 := by
      rw [integral_div, integral_add hi hci]
    _ = _ := by rw [hK, hconj]; push_cast; rfl

omit [Fintype d] in
/-- A real quadratic form is unchanged by symmetrizing its translation kernel. -/
theorem quadratic_symmetrize (K : (d → ℤ) → ℝ)
    (A : Finset (d → ℤ)) (c : (d → ℤ) → ℝ) :
    (∑ a ∈ A, ∑ b ∈ A, c a * c b * ((K (a - b) + K (-(a - b))) / 2)) =
      ∑ a ∈ A, ∑ b ∈ A, c a * c b * K (a - b) := by
  have hswap : (∑ a ∈ A, ∑ b ∈ A, c a * c b * K (-(a - b))) =
      ∑ a ∈ A, ∑ b ∈ A, c a * c b * K (a - b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [neg_sub]
    ring
  simp only [← mul_div_assoc, mul_add, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hswap]
  ring

/-- An actual notch kernel with a continuous density has nonpositive real part.
The Fourier identity is explicit; this theorem does not construct such a density. -/
theorem re_density_nonpos_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam)
    (hd : PrimeSmallDeviation.NotchSmall (WeilOneSided.coneDeviation lam))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Γ : (P → ℤ) → ℝ)
    (hΓ : ∀ g, Tendsto (WeilAbscissa.gcdHarmonicSum P (WeilOneSided.coneDeviation lam) g)
      atTop (𝓝 (Γ g)))
    (U : C(UnitAddTorus P, ℂ))
    (hU : ∀ g, (∫ x, U x * UnitAddTorus.mFourier (-g) x) =
      (WeilAbscissa.twistGramWeight g * Γ g : ℝ)) : ∀ x, (U x).re ≤ 0 := by
  let K (g : P → ℤ) := WeilAbscissa.twistGramWeight g * Γ g
  let V : C(UnitAddTorus P, ℝ) := ⟨fun x => (U x).re, Complex.continuous_re.comp U.continuous⟩
  apply nonpos_of_real_fourier_quadratic V (fun g => (K g + K (-g)) / 2)
  · intro a b
    have hU' : ∀ g, (∫ x, U x * UnitAddTorus.mFourier g x) = (K (-g) : ℂ) :=
      fun g => by simpa only [neg_neg] using hU (-g)
    have h := integral_re_density_character U (fun g => K (-g)) hU' (a - b)
    simpa only [V, ContinuousMap.coe_mk, neg_neg, add_comm] using h
  · intro A c
    rw [quadratic_symmetrize]
    have h := WeilAbscissa.notchBochner_le hW hd hP A c hΓ
    simpa only [K, mul_assoc] using h

end RHTower.WeilSingularArithmetic
