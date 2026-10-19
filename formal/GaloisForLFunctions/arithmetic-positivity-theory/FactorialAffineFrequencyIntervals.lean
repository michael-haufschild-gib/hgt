import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialAffineClockResonance
import GaloisForLFunctions.HTGeometry.OneSubCosKernelIntegral
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram

/-! Exact energy for the affine-clock error layers. For each harmonic, the native
frequency intervals are disjoint across source scales. The existing scalar cosine
integral and complex Gram identity give an exact diagonal energy formula. -/

open MeasureTheory Set Filter
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

private def cosineDefectKernel (a v : ℝ) : ℝ := (1 - Real.cos (a * v)) / v ^ 2

private theorem cosineDefectKernel_eq {a : ℝ} (ha : a ≠ 0) (v : ℝ) :
    cosineDefectKernel a v = a ^ 2 * oneSubCosKernel (a * v) := by
  unfold cosineDefectKernel oneSubCosKernel
  by_cases hv : v = 0
  · simp [hv]
  · field_simp

private theorem cosineDefectKernel_integrable (a : ℝ) :
    Integrable (cosineDefectKernel a) := by
  by_cases ha : a = 0
  · subst a
    change Integrable (fun v : ℝ => (1 - Real.cos (0 * v)) / v ^ 2)
    simp
  · have h := (integrable_oneSubCosKernel.comp_mul_left' ha).const_mul (a ^ 2)
    exact h.congr (Eventually.of_forall fun v => (cosineDefectKernel_eq ha v).symm)

private theorem cosineDefectKernel_integral (a : ℝ) :
    (∫ v, cosineDefectKernel a v) = Real.pi * |a| := by
  by_cases ha : a = 0
  · simp [ha, cosineDefectKernel]
  · simp_rw [cosineDefectKernel_eq ha]
    rw [integral_const_mul, Measure.integral_comp_mul_left,
      integral_oneSubCosKernel, smul_eq_mul, abs_inv]
    have h : a ^ 2 * |a|⁻¹ = |a| := by
      rw [← sq_abs, pow_two, mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), mul_one]
    calc a ^ 2 * (|a|⁻¹ * Real.pi) = (a ^ 2 * |a|⁻¹) * Real.pi := by ring
         _ = Real.pi * |a| := by rw [h]; ring

private def cosineShell (a b v : ℝ) : ℝ :=
  (Real.cos (a * v) - Real.cos (b * v)) / v

private theorem cosineShell_mul (a b c d v : ℝ) :
    cosineShell a b v * cosineShell c d v =
      (-(cosineDefectKernel (a-c) v) - cosineDefectKernel (a+c) v +
        cosineDefectKernel (a-d) v + cosineDefectKernel (a+d) v +
        cosineDefectKernel (b-c) v + cosineDefectKernel (b+c) v -
        cosineDefectKernel (b-d) v - cosineDefectKernel (b+d) v) / 2 := by
  unfold cosineShell cosineDefectKernel
  by_cases hv : v = 0
  · simp [hv]
  · simp only [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    field_simp
    ring

private theorem cosineShell_mul_integrable (a b c d : ℝ) :
    Integrable fun v => cosineShell a b v * cosineShell c d v := by
  have h := (((((((cosineDefectKernel_integrable (a-c)).neg.sub
    (cosineDefectKernel_integrable (a+c))).add
    (cosineDefectKernel_integrable (a-d))).add
    (cosineDefectKernel_integrable (a+d))).add
    (cosineDefectKernel_integrable (b-c))).add
    (cosineDefectKernel_integrable (b+c))).sub
    (cosineDefectKernel_integrable (b-d))).sub
    (cosineDefectKernel_integrable (b+d))
  exact (h.div_const 2).congr (Eventually.of_forall fun v =>
    (cosineShell_mul a b c d v).symm)

private theorem cosineShell_mul_integral {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (∫ v, cosineShell a b v * cosineShell c d v) =
      Real.pi / 2 * (|a-d| + |b-c| - |a-c| - |b-d|) := by
  simp_rw [cosineShell_mul]
  rw [integral_div]
  rw [integral_sub, integral_sub, integral_add, integral_add, integral_add,
    integral_add, integral_sub, integral_neg]
  · simp only [cosineDefectKernel_integral]
    rw [abs_of_nonneg (add_nonneg ha hc), abs_of_nonneg (add_nonneg ha hd),
      abs_of_nonneg (add_nonneg hb hc), abs_of_nonneg (add_nonneg hb hd)]
    ring
  all_goals apply_rules [Integrable.add, Integrable.sub, Integrable.neg,
    cosineDefectKernel_integrable]

private theorem cosineShell_diagonal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ v, cosineShell a b v * cosineShell a b v) = Real.pi * (b-a) := by
  rw [cosineShell_mul_integral ha (ha.trans hab) ha (ha.trans hab)]
  rw [sub_self, sub_self, abs_zero, abs_of_nonpos (sub_nonpos.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  ring

private theorem cosineShell_orthogonal {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∫ v, cosineShell a b v * cosineShell c d v) = 0 := by
  rw [cosineShell_mul_integral ha (ha.trans hab) (ha.trans (hab.trans hbc))
    (ha.trans (hab.trans (hbc.trans hcd)))]
  rw [abs_of_nonpos (sub_nonpos.mpr (hab.trans (hbc.trans hcd))),
    abs_of_nonpos (sub_nonpos.mpr hbc),
    abs_of_nonpos (sub_nonpos.mpr (hab.trans hbc)),
    abs_of_nonpos (sub_nonpos.mpr (hbc.trans hcd))]
  ring

private theorem cosineShell_gram {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hsep : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) (c : ι → ℂ) :
    Integrable (fun v => ‖∑ i, c i * (cosineShell (a i) (b i) v : ℂ)‖ ^ 2) ∧
    (∫ v, ‖∑ i, c i * (cosineShell (a i) (b i) v : ℂ)‖ ^ 2) =
      Real.pi * ∑ i, (b i-a i) * ‖c i‖ ^ 2 := by
  let f : ι → ℝ → ℂ := fun i v => (cosineShell (a i) (b i) v : ℂ)
  let z : ι → ℂ := fun i => (starRingEnd ℂ) (c i)
  have hp (i j : ι) : Integrable (fun v => f i v * (starRingEnd ℂ) (f j v)) := by
    exact (cosineShell_mul_integrable (a i) (b i) (a j) (b j)).ofReal.congr
      (Eventually.of_forall fun v => by simp [f])
  have hc (v : ℝ) : complexFeatureCombination f z v =
      ∑ i, c i * (cosineShell (a i) (b i) v : ℂ) := by
    simp [complexFeatureCombination, z, f]
  have hint : Integrable (fun v => complexFeatureCombination f z v *
      (starRingEnd ℂ) (complexFeatureCombination f z v)) := by
    simp_rw [complexFeatureCombination_mul_conj]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hp i j).const_mul _
  have hsquare : ∀ v, complexFeatureCombination f z v *
      (starRingEnd ℂ) (complexFeatureCombination f z v) =
      ((‖∑ i, c i * (cosineShell (a i) (b i) v : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [hc, Complex.mul_conj, ← Complex.sq_norm]
  refine ⟨hint.re.congr (Eventually.of_forall fun v => by
    change (complexFeatureCombination f z v *
      (starRingEnd ℂ) (complexFeatureCombination f z v)).re = _
    rw [hsquare]; rfl), ?_⟩
  have hGram (i j : ι) : complexFeatureGram volume f i j =
      if i = j then ((Real.pi * (b i-a i) : ℝ) : ℂ) else 0 := by
    unfold complexFeatureGram
    simp only [f, Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal]
    by_cases hij : i = j
    · subst j
      simp [cosineShell_diagonal (ha i) (hab i)]
    · simp only [hij, ↓reduceIte]
      rcases hsep i j hij with h | h
      · rw [cosineShell_orthogonal (ha i) (hab i) h (hab j)]
        simp
      · have he : (fun v => cosineShell (a i) (b i) v * cosineShell (a j) (b j) v) =
            fun v => cosineShell (a j) (b j) v * cosineShell (a i) (b i) v := by
          funext v; ring
        rw [he, cosineShell_orthogonal (ha j) (hab j) h (hab i)]
        simp
  apply Complex.ofReal_inj.mp
  rw [← integral_complex_ofReal]
  calc (∫ v, ((‖∑ i, c i * (cosineShell (a i) (b i) v : ℂ)‖ ^ 2 : ℝ) : ℂ))
      = ∫ v, complexFeatureCombination f z v *
          (starRingEnd ℂ) (complexFeatureCombination f z v) := by
        exact integral_congr_ae (Eventually.of_forall fun v => (hsquare v).symm)
    _ = star z ⬝ᵥ (complexFeatureGram volume f).mulVec z :=
      (complexFeatureGram_quadratic volume f hp z).symm
    _ = ((Real.pi * ∑ i, (b i-a i) * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def,
        hGram, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
        z, Complex.conj_conj]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      calc _ = ((Real.pi * (b i-a i) : ℝ) : ℂ) *
              (c i * (starRingEnd ℂ) (c i)) := by push_cast; ring
        _ = _ := by rw [Complex.mul_conj, ← Complex.sq_norm]; push_cast; ring

/-- The full finite source combination in one harmonic of the affine-clock error. -/
def factorialAffineHarmonicError (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) (v : ℝ) : ℂ :=
  ∑ n ∈ S, b n * ((Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n+1) * v)) -
    Real.cos (2 * Real.pi * k * ((((n+1 : ℕ) : ℝ) + 1/12) * v)) : ℝ) : ℂ)

private theorem factorialAffineHarmonicError_energy (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) :
    Integrable (fun v => ‖factorialAffineHarmonicError S b k v‖ ^ 2 / v ^ 2) ∧
    (∫ v, ‖factorialAffineHarmonicError S b k v‖ ^ 2 / v ^ 2) =
      2 * Real.pi ^ 2 * k * ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 := by
  classical
  let a : S → ℝ := fun n => 2 * Real.pi * k * factorialShiftedFreq (n.val+1)
  let d : S → ℝ := fun n => 2 * Real.pi * k * (((n.val+1 : ℕ) : ℝ) + 1/12)
  have hbase (n : ℕ) := factorialShiftedFreq_sub_self_bounds (N := n+1) (by omega)
  have ha (i : S) : 0 ≤ a i := by
    dsimp [a]
    exact mul_nonneg (by positivity) (factorialShiftedFreq_pos (by omega)).le
  have had (i : S) : a i ≤ d i := by
    dsimp [a, d]
    exact mul_le_mul_of_nonneg_left (by linarith [(hbase i.val).2]) (by positivity)
  have horder (i j : S) (hij : i.val < j.val) : d i ≤ a j := by
    have hnat : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hij
    dsimp [a, d]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hlo := (hbase j.val).1
    push_cast at hlo ⊢
    linarith
  have hsep (i j : S) (hij : i ≠ j) : d i ≤ a j ∨ d j ≤ a i := by
    have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hv with h | h
    · exact Or.inl (horder i j h)
    · exact Or.inr (horder j i h)
  have hg := cosineShell_gram a d ha had hsep (fun i : S => b i.val)
  have hsum (v : ℝ) : (∑ i : S, b i.val * (cosineShell (a i) (d i) v : ℂ)) =
      factorialAffineHarmonicError S b k v / (v : ℂ) := by
    dsimp only [a, d]
    rw [Finset.sum_coe_sort S (fun n : ℕ => b n *
      (cosineShell (2*Real.pi*k*factorialShiftedFreq (n+1))
        (2*Real.pi*k*(((n+1 : ℕ) : ℝ)+1/12)) v : ℂ))]
    unfold factorialAffineHarmonicError
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [cosineShell, a, d]
    push_cast
    simp only [mul_assoc, mul_div_assoc]
  have hnorm (v : ℝ) : ‖∑ i : S, b i.val * (cosineShell (a i) (d i) v : ℂ)‖ ^ 2 =
      ‖factorialAffineHarmonicError S b k v‖ ^ 2 / v ^ 2 := by
    rw [hsum, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hmass : Real.pi * (∑ i : S, (d i-a i) * ‖b i.val‖ ^ 2) =
      2 * Real.pi ^ 2 * k * ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 := by
    dsimp only [a, d]
    rw [Finset.sum_coe_sort S (fun n : ℕ =>
      (2*Real.pi*k*(((n+1 : ℕ) : ℝ)+1/12) -
        2*Real.pi*k*factorialShiftedFreq (n+1)) * ‖b n‖^2)]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [a, d, factorialAffineDefect]
    ring
  exact ⟨hg.1.congr (Eventually.of_forall hnorm),
    (integral_congr_ae (Eventually.of_forall hnorm)).symm.trans (hg.2.trans hmass)⟩

/-- Division by physical time removes the apparent singularity in the energy integral. -/
theorem integrable_factorialAffineHarmonicError_div_sq
    (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) :
    Integrable (fun v => ‖factorialAffineHarmonicError S b k v‖ ^ 2 / v ^ 2) :=
  (factorialAffineHarmonicError_energy S b k).1

/-- Disjoint exact frequency intervals diagonalize each native affine-error layer. -/
theorem integral_factorialAffineHarmonicError_div_sq
    (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) :
    (∫ v, ‖factorialAffineHarmonicError S b k v‖ ^ 2 / v ^ 2) =
      2 * Real.pi ^ 2 * k * ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 :=
  (factorialAffineHarmonicError_energy S b k).2

/-- The critical physical half-line has at most half the whole-line shell energy. -/
theorem critical_factorialAffineHarmonicError_le
    (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) :
    (∫ v in Ioi (1 : ℝ), ‖factorialAffineHarmonicError S b k v‖ ^ 2 / v ^ 2) ≤
      Real.pi ^ 2 * k * ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 := by
  let q : ℝ → ℝ := fun v => ‖factorialAffineHarmonicError S b k v‖ ^ 2 / v ^ 2
  have hi : Integrable q := integrable_factorialAffineHarmonicError_div_sq S b k
  have he (v : ℝ) : q (-v) = q v := by
    simp [q, factorialAffineHarmonicError, mul_neg]
  have hn : (∫ v in Iic (0 : ℝ), q v) = ∫ v in Ioi (0 : ℝ), q v := by
    simpa only [he, neg_zero] using integral_comp_neg_Iic 0 q
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hi.integrableOn hi.integrableOn
  rw [hn, integral_factorialAffineHarmonicError_div_sq] at hsplit
  have hhalf : (∫ v in Ioi (0 : ℝ), q v) =
      Real.pi ^ 2 * k * ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 := by
    linarith
  change (∫ v in Ioi (1 : ℝ), q v) ≤ _
  rw [← hhalf]
  exact integral_mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl)
    (Eventually.of_forall fun v => div_nonneg (sq_nonneg _) (sq_nonneg _)) hi.integrableOn

end
end GaloisForLFunctions.ArithmeticPositivityTheory
