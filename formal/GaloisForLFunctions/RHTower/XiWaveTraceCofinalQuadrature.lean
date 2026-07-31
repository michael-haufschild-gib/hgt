import GaloisForLFunctions.RHTower.WaveTraceLandauRecurrence
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.CCMRectangularTwoEdge
import GaloisForLFunctions.RHTower.XiCentralHankelDeterminantCriterion

/-!
# The Xi zero ordinates as a wave spectrum

The centered spectral coordinates of the Xi divisor form an admissible wave spectrum: they are
conjugation stable, bounded away from the origin, confined to the critical strip in horizontal
width, and inverse-square summable. Their squares are infinite and none of them is purely
imaginary, because the Xi divisor has no real point.

Consequently the cofinal convex recurrence law applies verbatim to the Xi zero wave traces.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Uniform lower bound for the height of a Xi zero. -/
def xiHeightLowerBound : ℝ := Classical.choose exists_xiDivisorSupport_abs_im_lower_bound

theorem xiHeightLowerBound_pos : 0 < xiHeightLowerBound :=
  (Classical.choose_spec exists_xiDivisorSupport_abs_im_lower_bound).1

theorem xiHeightLowerBound_le (ρ : XiDivisorSupport) :
    xiHeightLowerBound ≤ |((ρ : ℂ)).im| :=
  (Classical.choose_spec exists_xiDivisorSupport_abs_im_lower_bound).2 ρ

theorem norm_xiSpectralPointSupport (ρ : XiDivisorSupport) :
    ‖xiSpectralPointSupport ρ‖ = ‖(ρ : ℂ) - 1 / 2‖ := by
  rw [xiSpectralPointSupport, norm_mul, norm_neg, Complex.norm_I, mul_one]

theorem re_xiSpectralPointSupport (ρ : XiDivisorSupport) :
    (xiSpectralPointSupport ρ).re = (ρ : ℂ).im := by
  rw [xiSpectralPointSupport]
  simp [Complex.mul_re]

theorem im_xiSpectralPointSupport (ρ : XiDivisorSupport) :
    (xiSpectralPointSupport ρ).im = 1 / 2 - (ρ : ℂ).re := by
  rw [xiSpectralPointSupport]
  simp [Complex.mul_im]

/-- The Xi zero ordinates as an admissible wave spectrum. -/
def xiWaveSpectrum : WaveSpectrum XiDivisorSupport where
  gamma := xiSpectralPointSupport
  invol := Function.Involutive.toPerm
    (fun ρ : XiDivisorSupport => (⟨1 - (starRingEnd ℂ) (ρ : ℂ),
      mem_xi_divisor_support_of_eq_zero (by
        rw [xi_one_sub, xi_conj, xi_eq_zero_of_mem_divisor_support ρ, map_zero])⟩ :
        XiDivisorSupport))
    (by
      intro ρ
      apply Subtype.ext
      simp only [map_sub, map_one, Complex.conj_conj]
      ring)
  gamma_invol := by
    intro ρ
    show ((1 - (starRingEnd ℂ) (ρ : ℂ)) - 1 / 2) * (-Complex.I) =
      (starRingEnd ℂ) (((ρ : ℂ) - 1 / 2) * (-Complex.I))
    simp only [map_mul, map_sub, map_neg, Complex.conj_I, map_one, map_div₀, map_ofNat]
    ring
  lower := xiHeightLowerBound
  lower_pos := xiHeightLowerBound_pos
  lower_le := by
    intro ρ
    rw [norm_xiSpectralPointSupport]
    have h2 : |((ρ : ℂ) - 1 / 2).im| ≤ ‖(ρ : ℂ) - 1 / 2‖ := Complex.abs_im_le_norm _
    have h3 : ((ρ : ℂ) - 1 / 2).im = (ρ : ℂ).im := by simp
    rw [h3] at h2
    exact le_trans (xiHeightLowerBound_le ρ) h2
  width := 1 / 2
  width_nonneg := by norm_num
  im_le := by
    intro ρ
    rw [im_xiSpectralPointSupport]
    have hstrip := xi_divisor_support_re_mem_open_unit ρ
    rw [abs_le]
    constructor <;> linarith [hstrip.1, hstrip.2]
  summable_inv_sq := by
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
      xi_zero_multiplicity_centered_inv_sq_summable
    have hnorm : ‖xiSpectralPointSupport ρ‖ = ‖(ρ : ℂ) - 1 / 2‖ :=
      norm_xiSpectralPointSupport ρ
    have hne : (ρ : ℂ) ≠ 1 / 2 := xi_divisor_support_ne_half ρ
    have hpos : (0 : ℝ) < ‖(ρ : ℂ) - 1 / 2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hone : (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast xi_divisor_pos_on_support ρ
    rw [hnorm, inv_pow, ← one_div]
    exact div_le_div_of_nonneg_right hone (by positivity) |>.trans_eq rfl

/-! ## The three divisor hypotheses -/

theorem xiWaveSpectrum_locallyFinite : xiWaveSpectrum.IsLocallyFiniteSpectrum := by
  intro R
  classical
  set D := MeromorphicOn.divisor xi Set.univ with hD
  have hLF : LocallyFiniteSupport D.toFun := Function.locallyFinsupp.locallyFiniteSupport D
  apply Set.Finite.of_finite_image _ (Subtype.val_injective.injOn)
  apply Set.Finite.subset
    (hLF.finite_inter_support_of_isCompact (isCompact_closedBall ((1 : ℂ) / 2) R))
  rintro z ⟨ρ, hρ, rfl⟩
  refine ⟨?_, ρ.2⟩
  have hnorm : ‖xiSpectralPointSupport ρ‖ = ‖(ρ : ℂ) - 1 / 2‖ :=
    norm_xiSpectralPointSupport ρ
  have hle : ‖(ρ : ℂ) - 1 / 2‖ ≤ R := by
    have hthis : ‖xiSpectralPointSupport ρ‖ ≤ R := hρ
    rwa [hnorm] at hthis
  simpa [Metric.mem_closedBall, Complex.dist_eq] using hle

theorem xiWaveSpectrum_re_ne_zero (ρ : XiDivisorSupport) :
    (xiWaveSpectrum.gamma ρ).re ≠ 0 := by
  show (xiSpectralPointSupport ρ).re ≠ 0
  rw [re_xiSpectralPointSupport]
  exact xi_divisor_support_im_ne_zero ρ

theorem xiWaveSpectrum_squares_infinite :
    (Set.range fun ρ : XiDivisorSupport => xiWaveSpectrum.gamma ρ ^ 2).Infinite := by
  have hEq : (fun ρ : XiDivisorSupport => xiWaveSpectrum.gamma ρ ^ 2) =
      fun ρ : XiDivisorSupport => (xiCentralReciprocalSquare (ρ : ℂ))⁻¹ := by
    funext ρ
    show (((ρ : ℂ) - 1 / 2) * (-Complex.I)) ^ 2 = (-(((ρ : ℂ) - 1 / 2)⁻¹) ^ 2)⁻¹
    have hI : (-Complex.I) ^ 2 = -1 := by
      rw [neg_pow, Complex.I_sq]
      norm_num
    rw [mul_pow, hI, inv_neg, inv_pow, inv_inv]
    ring
  have himg : (Set.range fun ρ : XiDivisorSupport => (xiCentralReciprocalSquare (ρ : ℂ))⁻¹) =
      (fun x : ℂ => x⁻¹) ''
        (Set.range fun ρ : XiDivisorSupport => xiCentralReciprocalSquare (ρ : ℂ)) := by
    rw [← Set.range_comp]
    rfl
  rw [hEq, himg]
  exact xiCentralReciprocalSquare_range_infinite.image (Set.injOn_of_injective inv_injective)

/-! ## The Xi specialization -/

/-- **Cofinal convex recurrence of the Xi zero wave traces.** After every time, at most `K + 1`
distinct later times carry a positive probability weight annihilating the first `K` regularized
wave traces of the Xi divisor exactly. No Riemann hypothesis, simplicity, or rational
independence premise is used. -/
theorem exists_cofinal_positive_quadrature_xiWaveTrace (K : ℕ) (T : ℝ) :
    ∃ (nodes : Finset ℝ) (w : ℝ → ℝ),
      nodes.Nonempty ∧
      nodes.card ≤ K + 1 ∧
      (∀ t ∈ nodes, T < t) ∧
      (∀ t ∈ nodes, 0 < w t) ∧
      (∑ t ∈ nodes, w t) = 1 ∧
      ∀ j : Fin K,
        (∑ t ∈ nodes, w t * xiWaveSpectrum.realWaveTrace (Polynomial.X ^ (j : ℕ)) t) = 0 :=
  exists_cofinal_positive_quadrature_of_no_imaginary xiWaveSpectrum
    xiWaveSpectrum_locallyFinite xiWaveSpectrum_re_ne_zero xiWaveSpectrum_squares_infinite K T

/-- Both strict signs are assumed cofinally by every nonzero polynomial Xi wave trace. -/
theorem exists_neg_and_pos_xiWaveTrace {P : Polynomial ℝ} (hP : P ≠ 0) (T : ℝ) :
    (∃ t, T < t ∧ xiWaveSpectrum.realWaveTrace P t < 0) ∧
      ∃ t, T < t ∧ 0 < xiWaveSpectrum.realWaveTrace P t :=
  ⟨cofinalWaveSignEscape xiWaveSpectrum xiWaveSpectrum_locallyFinite
      xiWaveSpectrum_re_ne_zero xiWaveSpectrum_squares_infinite P hP T,
    exists_pos_realWaveTrace xiWaveSpectrum xiWaveSpectrum_locallyFinite
      xiWaveSpectrum_re_ne_zero xiWaveSpectrum_squares_infinite hP T⟩

end

end RHTower
