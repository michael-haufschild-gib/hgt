import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTwistedMomentHasPolynomialDerivatives
import GaloisForLFunctions.RHTower.ZetaThinStripWeylBound
import GaloisForLFunctions.RHTower.PrimeMassLowerBound
import Mathlib.MeasureTheory.Measure.Real

/-!
# Edge bounds for the mollified detector taper

Positive-order taper derivatives live on the two transition intervals.
Their integral bounds therefore use the transition width, independently
of the plateau length. A thin-strip Weyl bound controls the actual fields.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem taper_jet_off_edges (j : ℕ) {p q η t : ℝ} (hη : 0 < η)
    (ht : t ∉ Icc (p - η) p ∪ Icc q (q + η)) :
    iteratedDeriv (j + 1) (blockWindowC p q η) t = 0 := by
  by_cases hfull : t ∈ Icc (p - η) (q + η)
  · have hp : p < t := lt_of_not_ge (fun h => ht (Or.inl ⟨hfull.1, h⟩))
    have hq : t < q := lt_of_not_ge (fun h => ht (Or.inr ⟨h, hfull.2⟩))
    have he : blockWindowC p q η =ᶠ[𝓝 t] (fun _ => (1 : ℂ)) := by
      filter_upwards [Ioo_mem_nhds hp hq] with u hu
      simp only [blockWindowC, blockWindow_eq_one hη hu.1.le hu.2.le, Complex.ofReal_one]
    rw [he.iteratedDeriv_eq, iteratedDeriv_const, if_neg (Nat.succ_ne_zero j)]
  · exact iteratedDeriv_blockWindowC_eq_zero (j + 1) hη hfull

/-- Every positive taper derivative has an edge-length integral bound. -/
theorem integral_norm_taper_jet_le (j : ℕ) (p q : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ t, ‖iteratedDeriv (j + 1) (blockWindowC p q η) t‖) ≤
      2 * η * (blockWindowConst (j + 1) / η ^ (j + 1)) := by
  let E := Icc (p - η) p ∪ Icc q (q + η)
  have hE : MeasurableSet E := measurableSet_Icc.union measurableSet_Icc
  have hcompact : IsCompact E := isCompact_Icc.union isCompact_Icc
  have hmeasure : volume.real E ≤ 2 * η := by
    calc
      _ ≤ volume.real (Icc (p - η) p) + volume.real (Icc q (q + η)) := measureReal_union_le _ _
      _ = _ := by
        rw [Real.volume_real_Icc_of_le (by linarith only [hη]),
          Real.volume_real_Icc_of_le (by linarith only [hη])]
        ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := E)
    (fun t ht => by rw [taper_jet_off_edges j hη ht, norm_zero])]
  calc
    _ ≤ ∫ _ : ℝ in E, blockWindowConst (j + 1) / η ^ (j + 1) :=
      setIntegral_mono_on (integrable_iteratedDeriv_blockWindowC (j + 1) hη).norm.integrableOn
        (integrableOn_const hcompact.measure_lt_top.ne) hE
        (fun t _ => norm_iteratedDeriv_blockWindowC_le (j + 1) p q hη t)
    _ = volume.real E * (blockWindowConst (j + 1) / η ^ (j + 1)) := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hmeasure
      (div_nonneg (blockWindowConst_nonneg _) (pow_nonneg hη.le _))

/-- A pointwise field bound on the taper support controls every positive-order edge pairing. -/
theorem abs_integral_taper_jet_mul_le (j : ℕ) {p q η A : ℝ}
    (hη : 0 < η) (hA : 0 ≤ A) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (p - η) (q + η), |f t| ≤ A) :
    |∫ t, iteratedDeriv (j + 1) (blockWindow p q η) t * f t| ≤
      2 * η * (blockWindowConst (j + 1) / η ^ (j + 1)) * A := by
  have he (t : ℝ) : ‖iteratedDeriv (j + 1) (blockWindowC p q η) t‖ =
      |iteratedDeriv (j + 1) (blockWindow p q η) t| := by
    rw [iteratedDeriv_blockWindowC, Complex.norm_real, Real.norm_eq_abs]
  have hb (t : ℝ) : ‖iteratedDeriv (j + 1) (blockWindow p q η) t * f t‖ ≤
      ‖iteratedDeriv (j + 1) (blockWindowC p q η) t‖ * A := by
    rw [Real.norm_eq_abs, abs_mul, ← he]
    by_cases ht : t ∈ Icc (p - η) (q + η)
    · exact mul_le_mul_of_nonneg_left (hf t ht) (norm_nonneg _)
    · rw [iteratedDeriv_blockWindowC_eq_zero (j + 1) hη ht]
      simp only [norm_zero, zero_mul, le_refl]
  have hh := norm_integral_le_of_norm_le
    ((integrable_iteratedDeriv_blockWindowC (j + 1) hη).norm.mul_const A)
    (Eventually.of_forall hb)
  rw [Real.norm_eq_abs, integral_mul_const] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (integral_norm_taper_jet_le j p q hη) hA)

/-- Critical-line normalization gives the square-root length bound on the displaced line. -/
theorem norm_displaced_edPoly_le_sqrt_length {N : ℕ} {w : ℕ → ℝ} {K d : ℝ}
    (hK : 0 ≤ K) (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ K * (n : ℝ) ^ (-d)) (t : ℝ) :
    ‖edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) (displacedLinePt d t)‖ ≤
      2 * K * Real.sqrt N := by
  refine (norm_edPoly_le (fun n => (w n : ℂ)) (fun n hn => (Finset.mem_Icc.mp hn).1) _).trans ?_
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, K * (1 / Real.sqrt n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [Complex.norm_real, Real.norm_eq_abs, displacedLinePt_re]
      calc
        _ ≤ (K * (n : ℝ) ^ (-d)) * (n : ℝ) ^ (-(1 / 2 - d)) :=
          mul_le_mul_of_nonneg_right (hw n hn) (Real.rpow_nonneg hn0.le _)
        _ = K * (1 / Real.sqrt n) := by
          rw [mul_assoc, ← Real.rpow_add hn0,
            show -d + -(1 / 2 - d) = -(1 / 2 : ℝ) by ring,
            Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow, one_div]
    _ = K * ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt n := by rw [Finset.mul_sum]
    _ ≤ K * (2 * Real.sqrt N) := mul_le_mul_of_nonneg_left (RHTower.sum_one_div_sqrt_le N) hK
    _ = _ := by ring

/-- The actual mollified field has Weyl growth times square-root mollifier length. -/
theorem exists_twistedMomentField_thin_strip_bound :
    ∃ r C : ℝ, 0 < r ∧ r < 1 / 2 ∧ 0 < C ∧
      ∀ (N : ℕ) (w : ℕ → ℝ) (K d t : ℝ), 0 ≤ K → |d| ≤ r → 8 ≤ |t| →
        (∀ n ∈ Finset.Icc 1 N, |w n| ≤ K * (n : ℝ) ^ (-d)) →
        ‖twistedMomentField N w (d : ℂ) t‖ ≤ C * K * Real.sqrt N * |t| ^ (3 / 16 : ℝ) := by
  obtain ⟨r, hr, hrhalf, C, hC, hζ⟩ := exists_norm_zeta_thin_strip_le_weyl
    (by norm_num : (0 : ℝ) < 1 / 48)
  refine ⟨r, 2 * C, hr, hrhalf, by positivity, fun N w K d t hK hd ht hw => ?_⟩
  have he : (1 / 2 : ℂ) - (d : ℂ) + (t : ℂ) * I = displacedLinePt d t := by
    simp only [displacedLinePt, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
  have hz := hζ (displacedLinePt d t)
    (by simpa only [displacedLinePt_re, sub_sub_cancel_left, abs_neg] using hd)
    (by simpa only [displacedLinePt_im] using ht)
  rw [displacedLinePt_im] at hz
  norm_num only [show (1 / 6 : ℝ) + 1 / 48 = 3 / 16 by norm_num] at hz
  unfold twistedMomentField
  rw [he, norm_mul]
  have hm := norm_displaced_edPoly_le_sqrt_length hK hw t
  exact (mul_le_mul hz hm (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The two literal taper terms have square-root-length times Weyl-square bounds.
The first has no transition-width cost, and the second gains its reciprocal. -/
theorem exists_actual_mollified_taper_bounds :
    ∃ r C : ℝ, 0 < r ∧ r < 1 / 2 ∧ 0 < C ∧
      ∀ (p q η d K L : ℝ) (N : ℕ) (w v : ℕ → ℝ),
        0 < η → p ≤ q → 8 ≤ p - η → |d| ≤ r → 0 ≤ K → 0 ≤ L →
        (∀ n ∈ Finset.Icc 1 N, |w n| ≤ K * (n : ℝ) ^ (-d)) →
        (∀ n ∈ Finset.Icc 1 N, |v n| ≤ L * (n : ℝ) ^ (-d)) →
        |∫ t, iteratedDeriv 1 (blockWindow p q η) t *
          (twistedMomentField N w (d : ℂ) t * conj (twistedMomentField N v (d : ℂ) t)).im| ≤
            2 * blockWindowConst 1 * C ^ 2 * K * L * N * (q + η) ^ (3 / 8 : ℝ) ∧
        |∫ t, iteratedDeriv 2 (blockWindow p q η) t *
          ‖twistedMomentField N w (d : ℂ) t‖ ^ 2| ≤
            2 * blockWindowConst 2 * C ^ 2 * K ^ 2 * N * (q + η) ^ (3 / 8 : ℝ) / η := by
  obtain ⟨r, C, hr, hrhalf, hC, hfield⟩ := exists_twistedMomentField_thin_strip_bound
  refine ⟨r, C, hr, hrhalf, hC, fun p q η d K L N w v hη hpq hp hd hK hL hw hv => ?_⟩
  have hqη : 0 < q + η := by linarith only [hp, hpq, hη]
  let A : ℝ := C * Real.sqrt N * (q + η) ^ (3 / 16 : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hA2 : A ^ 2 = C ^ 2 * (N : ℝ) * (q + η) ^ (3 / 8 : ℝ) := by
    have he : ((q + η) ^ (3 / 16 : ℝ)) ^ 2 = (q + η) ^ (3 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hqη.le]
      norm_num
    dsimp only [A]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), he]
  have hbound (a : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
      (ha : ∀ n ∈ Finset.Icc 1 N, |a n| ≤ D * (n : ℝ) ^ (-d))
      (t : ℝ) (ht : t ∈ Icc (p - η) (q + η)) :
      ‖twistedMomentField N a (d : ℂ) t‖ ≤ D * A := by
    have ht8 : 8 ≤ t := hp.trans ht.1
    have ht0 : 0 ≤ t := by linarith only [ht8]
    have hh := hfield N a D d t hD hd (by simpa only [abs_of_nonneg ht0] using ht8) ha
    rw [abs_of_nonneg ht0] at hh
    calc
      _ ≤ C * D * Real.sqrt N * (q + η) ^ (3 / 16 : ℝ) := hh.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0 ht.2 (by norm_num)) (by positivity))
      _ = _ := by dsimp only [A]; ring
  have hmixed (t : ℝ) (ht : t ∈ Icc (p - η) (q + η)) :
      |(twistedMomentField N w (d : ℂ) t * conj (twistedMomentField N v (d : ℂ) t)).im| ≤
        K * L * A ^ 2 := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (hbound w K hK hw t ht) (hbound v L hL hv t ht)
      (norm_nonneg _) (mul_nonneg hK hA)).trans_eq (by ring)
  have hsquare (t : ℝ) (ht : t ∈ Icc (p - η) (q + η)) :
      |‖twistedMomentField N w (d : ℂ) t‖ ^ 2| ≤ K ^ 2 * A ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hbound w K hK hw t ht) 2).trans_eq (by ring)
  constructor
  · have hh := abs_integral_taper_jet_mul_le 0 hη (by positivity : 0 ≤ K * L * A ^ 2) hmixed
    refine hh.trans_eq ?_
    rw [hA2]
    norm_num only [Nat.zero_add, pow_one]
    field_simp [hη.ne'] <;> ring
  · have hh := abs_integral_taper_jet_mul_le 1 hη (by positivity : 0 ≤ K ^ 2 * A ^ 2) hsquare
    refine hh.trans_eq ?_
    rw [hA2]
    norm_num only [Nat.reduceAdd]
    field_simp [hη.ne'] <;> ring

/-- Both taper contributions are `O(T^(7/8))` up to square-root mollifier length. -/
theorem exists_actual_mollified_taper_power_bound :
    ∃ r C : ℝ, 0 < r ∧ r < 1 / 2 ∧ 0 < C ∧
      ∀ (T q η d : ℝ) (N : ℕ) (w v : ℕ → ℝ),
        16 ≤ T → T ≤ q → q ≤ 2 * T → 1 ≤ η → η ≤ T / 2 → |d| ≤ r →
        (N : ℝ) ≤ T ^ (1 / 2 : ℝ) →
        (∀ n ∈ Finset.Icc 1 N, |w n| ≤ (n : ℝ) ^ (-d)) →
        (∀ n ∈ Finset.Icc 1 N, |v n| ≤ (n : ℝ) ^ (-d)) →
        |∫ t, iteratedDeriv 1 (blockWindow T q η) t *
          (twistedMomentField N w (d : ℂ) t * conj (twistedMomentField N v (d : ℂ) t)).im| ≤
            C * T ^ (7 / 8 : ℝ) ∧
        |∫ t, iteratedDeriv 2 (blockWindow T q η) t *
          ‖twistedMomentField N w (d : ℂ) t‖ ^ 2| ≤ C * T ^ (7 / 8 : ℝ) := by
  obtain ⟨r, C, hr, hrhalf, hC, hbound⟩ := exists_actual_mollified_taper_bounds
  let D : ℝ := 2 * (blockWindowConst 1 + blockWindowConst 2 + 1) * C ^ 2 *
    (3 : ℝ) ^ (3 / 8 : ℝ)
  have h₁ := blockWindowConst_nonneg 1
  have h₂ := blockWindowConst_nonneg 2
  have hD : 0 < D := by
    dsimp only [D]
    have hsum : 0 < blockWindowConst 1 + blockWindowConst 2 + 1 := by linarith only [h₁, h₂]
    positivity
  refine ⟨r, D, hr, hrhalf, hD, fun T q η d N w v hT hq hq2 hη hηT hd hN hw hv => ?_⟩
  have hT0 : 0 < T := by linarith only [hT]
  have hη0 : 0 < η := zero_lt_one.trans_le hη
  have hqη : 0 ≤ q + η := by linarith only [hT, hq, hη]
  have hpower : (N : ℝ) * (q + η) ^ (3 / 8 : ℝ) ≤
      (3 : ℝ) ^ (3 / 8 : ℝ) * T ^ (7 / 8 : ℝ) := by
    have hq3 : q + η ≤ 3 * T := by linarith only [hq2, hηT, hT]
    calc
      _ ≤ T ^ (1 / 2 : ℝ) * (3 * T) ^ (3 / 8 : ℝ) :=
        mul_le_mul hN (Real.rpow_le_rpow hqη hq3 (by norm_num))
          (Real.rpow_nonneg hqη _) (Real.rpow_nonneg hT0.le _)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hT0.le]
        calc
          _ = (3 : ℝ) ^ (3 / 8 : ℝ) * (T ^ (1 / 2 : ℝ) * T ^ (3 / 8 : ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hT0]; norm_num
  obtain ⟨hb₁, hb₂⟩ := hbound T q η d 1 1 N w v hη0 hq
    (by linarith only [hT, hηT]) hd zero_le_one zero_le_one
    (by simpa only [one_mul] using hw) (by simpa only [one_mul] using hv)
  simp only [mul_one, one_pow] at hb₁ hb₂
  have hterm (j : ℕ) (hj : blockWindowConst j ≤ blockWindowConst 1 + blockWindowConst 2 + 1) :
      2 * blockWindowConst j * C ^ 2 * N * (q + η) ^ (3 / 8 : ℝ) ≤ D * T ^ (7 / 8 : ℝ) := by
    have hj0 := blockWindowConst_nonneg j
    calc
      _ = (2 * blockWindowConst j * C ^ 2) * ((N : ℝ) * (q + η) ^ (3 / 8 : ℝ)) := by ring
      _ ≤ (2 * blockWindowConst j * C ^ 2) *
          ((3 : ℝ) ^ (3 / 8 : ℝ) * T ^ (7 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ (2 * (blockWindowConst 1 + blockWindowConst 2 + 1) * C ^ 2) *
          ((3 : ℝ) ^ (3 / 8 : ℝ) * T ^ (7 / 8 : ℝ)) := by gcongr
      _ = _ := by dsimp only [D]; ring
  refine ⟨hb₁.trans (hterm 1 (by linarith only [h₂])), hb₂.trans ?_⟩
  refine (div_le_self (by positivity) hη).trans (hterm 2 (by linarith only [h₁]))

end GaloisForLFunctions.MultiscaleMollifiedZetaField
