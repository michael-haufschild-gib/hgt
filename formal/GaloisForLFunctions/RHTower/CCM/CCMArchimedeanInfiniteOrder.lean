import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanQuantizedTraceClass
import GaloisForLFunctions.RHTower.HermiteL2ClosedSpan
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.SmoothWeight
import GaloisForLFunctions.HTGeometry.SchwartzSmoothMultiplierApproximation
import GaloisForLFunctions.HTGeometry.SchwartzSupL2Bound
import GaloisForLFunctions.RHTower.TraceNormLimit

/-!
# Infinite-order CCM quantized differential

This file proves the full `quantsmooth` lemma from Connes--Consani: for every Schwartz symbol,
the approximation numbers of the literal quantized differential `[H, M_f]` decrease faster than
every integral power. The proof constructs the paper's smooth cutoff Hankel operator, controls all
oscillator powers by Hilbert--Schmidt operators, identifies its positive compression with the
actual CCM Hankel crossblock, and transports rapid decay through the literal block algebra.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap

namespace RHTower

open GaloisForLFunctions

/-! ## Smooth half-line cutoff and one-sided translated-Schwartz decay -/

/-- Source cutoff: zero on `(-∞,-1]` and one on `[0,∞)`. -/
def ccmSmoothHalflineCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1)

theorem ccmSmoothHalflineCutoff_eq_zero {x : ℝ} (hx : x ≤ -1) :
    ccmSmoothHalflineCutoff x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem ccmSmoothHalflineCutoff_eq_one {x : ℝ} (hx : 0 ≤ x) :
    ccmSmoothHalflineCutoff x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem ccmSmoothHalflineCutoff_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) ccmSmoothHalflineCutoff := by
  exact Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

theorem exists_bound_iteratedDeriv_ccmSmoothHalflineCutoff (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |iteratedDeriv j ccmSmoothHalflineCutoff x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_iteratedDeriv_smoothTransition j
  refine ⟨C, hC, fun x => ?_⟩
  have hshift := congrFun
    (iteratedDeriv_comp_add_const j Real.smoothTransition 1) x
  simpa [ccmSmoothHalflineCutoff] using hshift ▸ hbound (x + 1)

theorem ccmSmoothHalflineCutoff_hasTemperateGrowth :
    Function.HasTemperateGrowth ccmSmoothHalflineCutoff := by
  refine ⟨ccmSmoothHalflineCutoff_contDiff, fun n => ?_⟩
  obtain ⟨C, hC, hbound⟩ := exists_bound_iteratedDeriv_ccmSmoothHalflineCutoff n
  refine ⟨0, C, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, pow_zero, mul_one]
  exact hbound x

theorem ccmSmoothHalflineCutoffC_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun x : ℝ => (ccmSmoothHalflineCutoff x : ℂ)) := by
  exact Function.HasTemperateGrowth.comp Function.Complex.hasTemperateGrowth_ofReal
    ccmSmoothHalflineCutoff_hasTemperateGrowth

/-- Cutoff translated Schwartz function `x ↦ φ(x) g(x+y)`. -/
def ccmCutoffTranslate (g : 𝓢(ℝ, ℂ)) (y : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (ccmSmoothHalflineCutoff x : ℂ))
    (SchwartzMap.translateCLM ℂ y g)

@[simp] theorem ccmCutoffTranslate_apply (g : 𝓢(ℝ, ℂ)) (y x : ℝ) :
    ccmCutoffTranslate g y x =
      (ccmSmoothHalflineCutoff x : ℂ) * g (x + y) := by
  rw [ccmCutoffTranslate,
    SchwartzMap.smulLeftCLM_apply_apply ccmSmoothHalflineCutoffC_hasTemperateGrowth,
    smul_eq_mul, SchwartzMap.translateCLM_apply]

/-- One-sided decay of every translated Schwartz derivative, with enough room for a polynomial
weight in the output coordinate. -/
theorem ccm_shifted_schwartz_deriv_decay
    (g : 𝓢(ℝ, ℂ)) (a q n r : ℕ) (hr : r ≤ n)
    {x y : ℝ} (hx : -1 ≤ x) (hy : -1 ≤ y) :
    |x| ^ a * ‖iteratedDeriv r g (x + y)‖ ≤
      6 ^ (a + q) *
        ((Finset.Iic (a + q, n)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) g *
        (y + 2)⁻¹ ^ q := by
  let z : ℝ := x + y
  let A : ℝ := 3 + z
  let Y : ℝ := y + 2
  let G : ℝ := ((Finset.Iic (a + q, n)).sup
    (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) g
  have hA : 0 < A := by dsimp [A, z]; linarith
  have hY : 0 < Y := by dsimp [Y]; linarith
  have hG : 0 ≤ G := apply_nonneg _ _
  have hxA : |x| ≤ A := by
    dsimp [A, z]
    rw [abs_le]
    constructor <;> linarith
  have hYA : Y ≤ A := by dsimp [Y, A, z]; linarith
  have hAz : A ≤ 3 * (1 + |z|) := by
    dsimp [A]
    nlinarith [le_abs_self z, abs_nonneg z]
  have hbase := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (a + q, n)) (k := a + q) (n := r)
      le_rfl hr g z
  rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hbase
  have hweighted :
      |x| ^ a * Y ^ q * ‖iteratedDeriv r g z‖ ≤ 6 ^ (a + q) * G := by
    calc
      |x| ^ a * Y ^ q * ‖iteratedDeriv r g z‖ ≤
          A ^ a * A ^ q * ‖iteratedDeriv r g z‖ := by gcongr
      _ = A ^ (a + q) * ‖iteratedDeriv r g z‖ := by rw [pow_add]
      _ ≤ (3 * (1 + |z|)) ^ (a + q) * ‖iteratedDeriv r g z‖ := by gcongr
      _ = 3 ^ (a + q) *
          ((1 + |z|) ^ (a + q) * ‖iteratedDeriv r g z‖) := by rw [mul_pow]; ring
      _ ≤ 3 ^ (a + q) * (2 ^ (a + q) * G) := by gcongr
      _ = 6 ^ (a + q) * G := by
        rw [show 3 ^ (a + q) * (2 ^ (a + q) * G) =
          (3 ^ (a + q) * 2 ^ (a + q)) * G by ring, ← mul_pow]
        norm_num
  rw [inv_pow]
  apply (le_div_iff₀ (pow_pos hY q)).2
  simpa [z, Y, mul_assoc, mul_left_comm, mul_comm] using hweighted

/-- Every fixed Schwartz seminorm of the cutoff translate decays faster than any requested
power of the translation parameter on the source half-line. -/
theorem exists_ccmCutoffTranslate_seminorm_decay
    (g : 𝓢(ℝ, ℂ)) (a n q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, -1 ≤ y →
      SchwartzMap.seminorm ℂ a n (ccmCutoffTranslate g y) ≤
        C * (y + 2)⁻¹ ^ q := by
  choose D hD hDbound using exists_bound_iteratedDeriv_ccmSmoothHalflineCutoff
  let E : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * D i
  let G : ℝ := ((Finset.Iic (a + q, n)).sup
    (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) g
  let C : ℝ := E * (6 ^ (a + q) * G)
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hD i)
  have hG : 0 ≤ G := apply_nonneg _ _
  have hC : 0 ≤ C := mul_nonneg hE (mul_nonneg (by positivity) hG)
  refine ⟨C, hC, fun y hy => ?_⟩
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) a n
  · exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr (by linarith)) q)
  · intro x
    by_cases hx : x < -1
    · have heq : (ccmCutoffTranslate g y : ℝ → ℂ) =ᶠ[nhds x]
          (fun _ => (0 : ℂ)) := by
        filter_upwards [Iio_mem_nhds hx] with t ht
        rw [ccmCutoffTranslate_apply,
          ccmSmoothHalflineCutoff_eq_zero (le_of_lt ht), Complex.ofReal_zero, zero_mul]
      have hzero : iteratedDeriv n (ccmCutoffTranslate g y : ℝ → ℂ) x = 0 := by
        rw [heq.iteratedDeriv_eq n, iteratedDeriv_const]
        split_ifs <;> simp
      rw [hzero, norm_zero, mul_zero]
      exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr (by linarith)) q)
    · have hx' : -1 ≤ x := le_of_not_gt hx
      have hformula : iteratedDeriv n (ccmCutoffTranslate g y : ℝ → ℂ) x =
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℂ) *
              iteratedDeriv i (fun t => (ccmSmoothHalflineCutoff t ^ 1 : ℂ)) x *
                iteratedDeriv (n - i) (SchwartzMap.translateCLM ℂ y g) x := by
        rw [show (ccmCutoffTranslate g y : ℝ → ℂ) =
            fun t => (ccmSmoothHalflineCutoff t : ℂ) *
              (SchwartzMap.translateCLM ℂ y g) t by
          funext t
          exact ccmCutoffTranslate_apply g y t]
        simpa using SchwartzMap.iteratedDeriv_real_pow_mul_schwartz_eq_sum
          ccmSmoothHalflineCutoff ccmSmoothHalflineCutoff_contDiff
            (SchwartzMap.translateCLM ℂ y g) 1 n x
      rw [hformula]
      calc
        |x| ^ a * ‖∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℂ) *
              iteratedDeriv i (fun t => (ccmSmoothHalflineCutoff t ^ 1 : ℂ)) x *
                iteratedDeriv (n - i) (SchwartzMap.translateCLM ℂ y g) x‖
            ≤ |x| ^ a * ∑ i ∈ Finset.range (n + 1),
                ‖(n.choose i : ℂ) *
                  iteratedDeriv i (fun t => (ccmSmoothHalflineCutoff t ^ 1 : ℂ)) x *
                    iteratedDeriv (n - i) (SchwartzMap.translateCLM ℂ y g) x‖ := by
              gcongr
              exact norm_sum_le _ _
        _ ≤ |x| ^ a * ∑ i ∈ Finset.range (n + 1),
              ((n.choose i : ℝ) * D i) *
                ‖iteratedDeriv (n - i) g (x + y)‖ := by
            gcongr with i hi
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            have hcut : iteratedDeriv i
                (fun t => (ccmSmoothHalflineCutoff t ^ 1 : ℂ)) x =
                ((iteratedDeriv i ccmSmoothHalflineCutoff x : ℝ) : ℂ) := by
              simpa using SchwartzMap.iteratedDeriv_ofReal
                ccmSmoothHalflineCutoff ccmSmoothHalflineCutoff_contDiff i x
            rw [hcut, Complex.norm_real]
            have htrans : iteratedDeriv (n - i)
                (SchwartzMap.translateCLM ℂ y g : ℝ → ℂ) x =
                iteratedDeriv (n - i) g (x + y) := by
              change iteratedDeriv (n - i) (fun t => g (t + y)) x = _
              exact congrFun (iteratedDeriv_comp_add_const (n - i) g y) x
            rw [htrans]
            gcongr
            exact hDbound i x
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              ((n.choose i : ℝ) * D i) *
                (6 ^ (a + q) * G * (y + 2)⁻¹ ^ q) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro i hi
            have hdecay := ccm_shifted_schwartz_deriv_decay g a q n (n - i)
              (Nat.sub_le n i) hx' hy
            calc
              |x| ^ a * (((n.choose i : ℝ) * D i) *
                  ‖iteratedDeriv (n - i) g (x + y)‖) =
                  ((n.choose i : ℝ) * D i) *
                    (|x| ^ a * ‖iteratedDeriv (n - i) g (x + y)‖) := by ring
              _ ≤ ((n.choose i : ℝ) * D i) *
                  (6 ^ (a + q) * G * (y + 2)⁻¹ ^ q) := by
                exact mul_le_mul_of_nonneg_left (by simpa [G, mul_assoc] using hdecay)
                  (mul_nonneg (by positivity) (hD i))
        _ = C * (y + 2)⁻¹ ^ q := by
            simp only [← Finset.sum_mul, E, C]
            ring

/-! ## Oscillator-applied cutoff kernels -/

theorem ccmSmoothHalflineCutoff_nonneg (x : ℝ) :
    0 ≤ ccmSmoothHalflineCutoff x :=
  Real.smoothTransition.nonneg _

theorem ccmSmoothHalflineCutoff_le_one (x : ℝ) :
    ccmSmoothHalflineCutoff x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- A concrete `L²` bound by finitely many Schwartz seminorms. -/
theorem ccm_norm_toLp_sq_le_schwartzSup (w : 𝓢(ℝ, ℂ)) :
    ‖w.toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      4 * Real.pi *
        (((Finset.Iic (1, 0)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) w) ^ 2 := by
  let S : ℝ := ((Finset.Iic (1, 0)).sup
    (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) w
  have hS : 0 ≤ S := apply_nonneg _ _
  rw [GaloisForLFunctions.norm_toLp_sq_eq_integral]
  calc
    (∫ x : ℝ, ‖w x‖ ^ 2) ≤
        ∫ x : ℝ, (4 * S ^ 2) * (1 + x ^ 2)⁻¹ := by
      apply integral_mono
      · exact (memLp_two_iff_integrable_sq_norm w.continuous.aestronglyMeasurable).mp
          (SchwartzMap.memLp w 2 volume)
      · exact integrable_inv_one_add_sq.const_mul _
      · intro x
        let A : ℝ := 1 + |x|
        have hA : 0 < A := by dsimp [A]; linarith [abs_nonneg x]
        have hbase := SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℂ) (m := (1, 0)) (k := 1) (n := 0)
            le_rfl le_rfl w x
        rw [Real.norm_eq_abs, norm_iteratedFDeriv_zero] at hbase
        have hnorm : ‖w x‖ ≤ 2 * S * A⁻¹ := by
          have hdiv : ‖w x‖ ≤ (2 * S) / A :=
            (le_div_iff₀ hA).2 (by
              simpa only [A, S, pow_one, Prod.fst, Prod.snd, mul_comm] using hbase)
          simpa [div_eq_mul_inv, mul_assoc] using hdiv
        have hsq : ‖w x‖ ^ 2 ≤ (2 * S * A⁻¹) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (by positivity) hS)
            (inv_nonneg.mpr hA.le))).2 hnorm
        have hden : 1 + x ^ 2 ≤ A ^ 2 := by
          dsimp [A]
          nlinarith [sq_abs x, abs_nonneg x]
        calc
          ‖w x‖ ^ 2 ≤ (2 * S * A⁻¹) ^ 2 := hsq
          _ = (4 * S ^ 2) * (A ^ 2)⁻¹ := by
            rw [show (A ^ 2)⁻¹ = A⁻¹ ^ 2 by rw [inv_pow]]
            ring
          _ ≤ (4 * S ^ 2) * (1 + x ^ 2)⁻¹ := by gcongr
    _ = 4 * Real.pi * S ^ 2 := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
      ring
    _ = _ := rfl

/-- Continuity of a Schwartz operator gives a finite-seminorm bound on any selected output
seminorm. -/
theorem ccm_exists_bound_seminorm_comp
    (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      SchwartzMap.seminorm ℂ p 0 (T f) ≤
        C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  set q : Seminorm ℂ 𝓢(ℝ, ℂ) :=
    (SchwartzMap.seminorm ℂ p 0).comp
      (T : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ)) with hq
  have hcont : Continuous q := by
    have hbase : Continuous (SchwartzMap.seminorm ℂ p 0 : 𝓢(ℝ, ℂ) → ℝ) :=
      (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (p, 0)
    exact hbase.comp T.continuous
  obtain ⟨K, C, _, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hcont
  refine ⟨K, (C : ℝ), NNReal.coe_nonneg C, fun f => ?_⟩
  have h := hC f
  rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h
  exact h

/-- Finite target families admit one finite source-seminorm bound after a continuous Schwartz
operator. -/
theorem ccm_exists_bound_finsetSup_comp
    (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (L : Finset (ℕ × ℕ)) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      (L.sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2)) (T f) ≤
        C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  classical
  have htarget : Continuous
      (((L.sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) : Seminorm ℂ 𝓢(ℝ, ℂ))) :
        𝓢(ℝ, ℂ) → ℝ) := by
    induction L using Finset.induction_on with
    | empty =>
        change Continuous (fun _ : 𝓢(ℝ, ℂ) => (0 : ℝ))
        exact continuous_const
    | @insert p L hp ih =>
        rw [Finset.sup_insert]
        exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm p).max ih
  set q : Seminorm ℂ 𝓢(ℝ, ℂ) :=
    (L.sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2)).comp
      (T : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ)) with hq
  have hcont : Continuous q := htarget.comp T.continuous
  obtain ⟨K, C, _, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hcont
  refine ⟨K, (C : ℝ), NNReal.coe_nonneg C, fun f => ?_⟩
  have h := hC f
  rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h
  exact h

theorem ccm_finsetSup_schwartzSeminorm_le_sum
    (K : Finset (ℕ × ℕ)) (f : 𝓢(ℝ, ℂ)) :
    (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤
      ∑ p ∈ K, SchwartzMap.seminorm ℂ p.1 p.2 f := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | @insert p K hp ih =>
      rw [Finset.sup_insert, Finset.sum_insert hp]
      change max (SchwartzMap.seminorm ℂ p.1 p.2 f)
          ((K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) ≤ _
      apply max_le
      · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      · exact ih.trans (le_add_of_nonneg_left (apply_nonneg _ _))

theorem exists_ccmCutoffTranslate_finsetSup_decay
    (g : 𝓢(ℝ, ℂ)) (K : Finset (ℕ × ℕ)) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, -1 ≤ y →
      (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (ccmCutoffTranslate g y) ≤
        C * (y + 2)⁻¹ ^ q := by
  choose C hC hbound using fun p : ℕ × ℕ =>
    exists_ccmCutoffTranslate_seminorm_decay g p.1 p.2 q
  let D : ℝ := ∑ p ∈ K, C p
  have hD : 0 ≤ D := Finset.sum_nonneg fun p _ => hC p
  refine ⟨D, hD, fun y hy => ?_⟩
  calc
    (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (ccmCutoffTranslate g y) ≤
        ∑ p ∈ K, SchwartzMap.seminorm ℂ p.1 p.2 (ccmCutoffTranslate g y) :=
      ccm_finsetSup_schwartzSeminorm_le_sum K _
    _ ≤ ∑ p ∈ K, C p * (y + 2)⁻¹ ^ q := by
      gcongr with p hp
      exact hbound p y hy
    _ = D * (y + 2)⁻¹ ^ q := by rw [Finset.sum_mul]

/-- The kernel slice after applying the `k`-th oscillator power in the output variable. -/
def ccmOscillatedCutoffSlice (g : 𝓢(ℝ, ℂ)) (k : ℕ) (y : ℝ) : SoninL2 :=
  (ccmSmoothHalflineCutoff y : ℂ) •
    ((GaloisForLFunctions.hamiltonianPowCLM k) (ccmCutoffTranslate g y)).toLp 2 volume

theorem continuous_ccmOscillatedCutoffSlice (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Continuous (ccmOscillatedCutoffSlice g k) := by
  have horbit : Continuous (fun y : ℝ => SchwartzMap.translateCLM ℂ y g) :=
    continuous_ccmTranslateOrbit g
  have hcut : Continuous (fun y : ℝ => ccmCutoffTranslate g y) :=
    (SchwartzMap.smulLeftCLM ℂ
      (fun x : ℝ => (ccmSmoothHalflineCutoff x : ℂ))).continuous.comp horbit
  have hosc : Continuous (fun y : ℝ =>
      (GaloisForLFunctions.hamiltonianPowCLM k) (ccmCutoffTranslate g y)) :=
    (GaloisForLFunctions.hamiltonianPowCLM k).continuous.comp hcut
  have hlp : Continuous (fun y : ℝ =>
      ((GaloisForLFunctions.hamiltonianPowCLM k)
        (ccmCutoffTranslate g y)).toLp 2 volume) :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).continuous.comp hosc
  exact (Complex.continuous_ofReal.comp
    (Real.smoothTransition.continuous.comp (continuous_id.add continuous_const))).smul hlp

theorem ccmOscillatedCutoffSlice_memLp (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    MemLp (ccmOscillatedCutoffSlice g k) 2 (volume : Measure ℝ) := by
  obtain ⟨K, B, hB, hbound⟩ :=
    ccm_exists_bound_finsetSup_comp (GaloisForLFunctions.hamiltonianPowCLM k)
      (Finset.Iic (1, 0))
  obtain ⟨D, hD, hdecay⟩ :=
    exists_ccmCutoffTranslate_finsetSup_decay g K 1
  let M : ℝ := 4 * Real.pi * (B * D) ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmajor : Integrable (fun y : ℝ =>
      M * (1 + (y + 1) ^ 2)⁻¹) := by
    have h := integrable_inv_one_add_sq.comp_add_left 1
    have h' : Integrable (fun y : ℝ => (1 + (y + 1) ^ 2)⁻¹) := by
      simpa [add_comm] using h
    exact h'.const_mul M
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_ccmOscillatedCutoffSlice g k).aestronglyMeasurable).mpr ?_
  refine Integrable.mono' hmajor
    ((continuous_ccmOscillatedCutoffSlice g k).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hy : -1 ≤ y
  · have hphi : ‖(ccmSmoothHalflineCutoff y : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ccmSmoothHalflineCutoff_nonneg y)]
      exact ccmSmoothHalflineCutoff_le_one y
    have hsemi := hbound (ccmCutoffTranslate g y)
    have hsup := hdecay y hy
    have hsemi' : ((Finset.Iic (1, 0)).sup
        (fun p => SchwartzMap.seminorm ℂ p.1 p.2))
          (GaloisForLFunctions.hamiltonianPowCLM k (ccmCutoffTranslate g y)) ≤
          B * (D * (y + 2)⁻¹) := by
      simpa only [pow_one] using hsemi.trans (mul_le_mul_of_nonneg_left hsup hB)
    have hlp := ccm_norm_toLp_sq_le_schwartzSup
      (GaloisForLFunctions.hamiltonianPowCLM k (ccmCutoffTranslate g y))
    have hslice : ‖ccmOscillatedCutoffSlice g k y‖ ^ 2 ≤
        4 * Real.pi * (B * (D * (y + 2)⁻¹)) ^ 2 := by
      rw [ccmOscillatedCutoffSlice, norm_smul, mul_pow]
      calc
        ‖(ccmSmoothHalflineCutoff y : ℂ)‖ ^ 2 *
            ‖(GaloisForLFunctions.hamiltonianPowCLM k
              (ccmCutoffTranslate g y)).toLp 2 volume‖ ^ 2 ≤
            1 ^ 2 * ‖(GaloisForLFunctions.hamiltonianPowCLM k
              (ccmCutoffTranslate g y)).toLp 2 volume‖ ^ 2 := by gcongr
        _ ≤ 4 * Real.pi *
            (((Finset.Iic (1, 0)).sup
              (fun p => SchwartzMap.seminorm ℂ p.1 p.2))
            (GaloisForLFunctions.hamiltonianPowCLM k
                (ccmCutoffTranslate g y))) ^ 2 := by
          simpa only [one_pow, one_mul] using hlp
        _ ≤ 4 * Real.pi * (B * (D * (y + 2)⁻¹)) ^ 2 := by gcongr
    have hden : (y + 2)⁻¹ ^ 2 ≤ (1 + (y + 1) ^ 2)⁻¹ := by
      have hp : 0 < y + 2 := by linarith
      rw [inv_pow]
      apply (inv_le_inv₀ (pow_pos hp 2)
        (by positivity : 0 < 1 + (y + 1) ^ 2)).2
      nlinarith [sq_nonneg (y + 1)]
    calc
      ‖ccmOscillatedCutoffSlice g k y‖ ^ 2 ≤
          4 * Real.pi * (B * (D * (y + 2)⁻¹)) ^ 2 := hslice
      _ = M * ((y + 2)⁻¹ ^ 2) := by dsimp [M]; ring
      _ ≤ M * (1 + (y + 1) ^ 2)⁻¹ := by gcongr
  · have hy' : y ≤ -1 := le_of_not_ge hy
    rw [ccmOscillatedCutoffSlice,
      ccmSmoothHalflineCutoff_eq_zero hy', Complex.ofReal_zero, zero_smul,
      norm_zero, zero_pow (by omega)]
    exact mul_nonneg hM (inv_nonneg.mpr (by positivity))

/-- Bochner `L²` field of oscillator-applied cutoff slices. -/
def ccmOscillatedCutoffField (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Lp SoninL2 2 (volume : Measure ℝ) :=
  (ccmOscillatedCutoffSlice_memLp g k).toLp (ccmOscillatedCutoffSlice g k)

/-- Hilbert--Schmidt operator with kernel `φ(y) H_x^k(φ(x)g(x+y))`. -/
def ccmOscillatedCutoffOperator (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    SoninL2 →L[ℂ] SoninL2 :=
  l2Synthesis volume (ccmOscillatedCutoffField g k)

theorem ccmOscillatedCutoffOperator_isHilbertSchmidt (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (ccmOscillatedCutoffOperator g k).IsHilbertSchmidt :=
  l2Synthesis_isHilbertSchmidt volume (ccmOscillatedCutoffField g k)

/-- Approximation numbers decay faster than every inverse integral power. -/
def IsInfinitesimalOfInfiniteOrder (T : SoninL2 →L[ℂ] SoninL2) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    approxNumber T n ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)⁻¹

/-- Rapid approximation-number decay implies Schatten-one membership.  This closes the
operator-ideal implication used implicitly in the source phrase “infinitesimal of arbitrary
order (and in particular trace class)”. -/
theorem IsInfinitesimalOfInfiniteOrder.memSchattenClass_one
    {T : SoninL2 →L[ℂ] SoninL2}
    (hT : IsInfinitesimalOfInfiniteOrder T) :
    MemSchattenClass 1 T := by
  obtain ⟨C, hC, hbound⟩ := hT 2
  have hbase : Summable (fun n : ℕ =>
      ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa only [one_div] using h
  have hmajor : Summable (fun n : ℕ =>
      C * ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
    hbase.mul_left C
  unfold MemSchattenClass
  simpa only [Real.rpow_one] using
    Summable.of_nonneg_of_le
      (fun n => approxNumber_nonneg T n) hbound hmajor

/-- Span of the first `N` vectors of a naturally indexed Hilbert basis. -/
def ccmFiniteBasisSubspace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (N : ℕ) :
    Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun i : Fin N => b i)

noncomputable instance ccmFiniteBasisSubspace_finiteDimensional
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) (N : ℕ) :
    FiniteDimensional ℂ (ccmFiniteBasisSubspace b N) := by
  unfold ccmFiniteBasisSubspace
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem ccmFiniteBasisSubspace_finrank_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) (N : ℕ) :
    Module.finrank ℂ (ccmFiniteBasisSubspace b N) ≤ N := by
  classical
  unfold ccmFiniteBasisSubspace
  have horth : Orthonormal ℂ (fun i : Fin N => b (i : ℕ)) := by
    convert b.orthonormal.comp (fun i : Fin N => (i : ℕ))
        (by intro i j h; exact Fin.ext h) using 1
    funext i
    rfl
  rw [finrank_span_eq_card horth.linearIndependent, Fintype.card_fin]

theorem ccm_basis_mem_finiteSubspace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) (N i : ℕ) (hi : i < N) :
    b i ∈ ccmFiniteBasisSubspace b N := by
  apply Submodule.subset_span
  exact ⟨⟨i, hi⟩, rfl⟩

theorem ccm_basis_mem_finiteSubspace_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) (N i : ℕ) (hi : N ≤ i) :
    b i ∈ (ccmFiniteBasisSubspace b N)ᗮ := by
  classical
  refine (Submodule.mem_orthogonal' _ _).2 fun y hy => ?_
  refine Submodule.span_induction
    (p := fun y _ => inner ℂ (b i) y = (0 : ℂ)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨j, rfl⟩
    rw [orthonormal_iff_ite.mp b.orthonormal i j]
    have hne : i ≠ (j : ℕ) := ne_of_gt (j.isLt.trans_le hi)
    rw [if_neg hne]
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [inner_smul_right, hx, mul_zero]

theorem ccm_basis_complement_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (N i : ℕ) :
    (1 - (ccmFiniteBasisSubspace b N).starProjection) (b i) =
      if i < N then 0 else b i := by
  by_cases hi : i < N
  · rw [if_pos hi, sub_apply, one_apply_eq_self,
      Submodule.starProjection_eq_self_iff.mpr (ccm_basis_mem_finiteSubspace b N i hi)]
    simp
  · have horth : b i ∈ (ccmFiniteBasisSubspace b N)ᗮ :=
      ccm_basis_mem_finiteSubspace_orthogonal b N i (Nat.le_of_not_gt hi)
    have hproj : (ccmFiniteBasisSubspace b N).starProjection (b i) = 0 :=
      Submodule.eq_starProjection_of_mem_orthogonal
        (ccmFiniteBasisSubspace b N).zero_mem (by simpa using horth)
    rw [if_neg hi, sub_apply, one_apply_eq_self, hproj, sub_zero]

/-- Uniform bounds on all output oscillator powers force rapid approximation-number decay. -/
theorem infinitesimalOfInfiniteOrder_of_hermiteCoefficientSmoothing
    (T : SoninL2 →L[ℂ] SoninL2)
    (hT : ∀ k : ℕ, ∃ S : SoninL2 →L[ℂ] SoninL2,
      ∀ j : ℕ, ∀ x : SoninL2,
        (2 * Real.pi * (2 * j + 1)) ^ k *
            ‖inner ℂ (hermiteL2HilbertBasis j) (T x)‖ ≤
          ‖inner ℂ (hermiteL2HilbertBasis j) (S x)‖) :
    IsInfinitesimalOfInfiniteOrder T := by
  intro k
  obtain ⟨S, hS⟩ := hT k
  refine ⟨‖S‖ * (2 * Real.pi)⁻¹ ^ k, mul_nonneg (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr (by positivity)) _), ?_⟩
  intro N
  let V : Submodule ℂ SoninL2 :=
    ccmFiniteBasisSubspace hermiteL2HilbertBasis N
  let P : SoninL2 →L[ℂ] SoninL2 := V.starProjection
  let F : SoninL2 →L[ℂ] SoninL2 := P ∘L T
  have hF : HasRankLE F N := by
    refine ⟨V, inferInstance, ?_, ?_⟩
    · simpa [V] using ccmFiniteBasisSubspace_finrank_le
        hermiteL2HilbertBasis N
    · intro x
      exact V.starProjection_apply_mem (T x)
  refine (approxNumber_le T N F hF).trans ?_
  have hnorm : ‖T - F‖ ≤
      (2 * Real.pi * (2 * N + 1))⁻¹ ^ k * ‖S‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr (by positivity)) _) (norm_nonneg _)) ?_
    intro x
    let Q : SoninL2 →L[ℂ] SoninL2 := 1 - P
    have hdiff : (T - F) x = Q (T x) := by
      simp [F, Q, P]
    rw [hdiff]
    have hparseQ := HilbertBasis.tsum_norm_inner_sq hermiteL2HilbertBasis (Q (T x))
    have hparseS := HilbertBasis.tsum_norm_inner_sq hermiteL2HilbertBasis (S x)
    have hQself : ContinuousLinearMap.adjoint Q = Q := by
      have hPadj : ContinuousLinearMap.adjoint P = P := by
        simpa [P, ContinuousLinearMap.star_eq_adjoint] using
          (isSelfAdjoint_starProjection V).star_eq
      simp only [Q, ContinuousLinearMap.adjoint.map_sub,
        ContinuousLinearMap.adjoint_one, hPadj]
    have hterm : ∀ j : ℕ,
        ‖inner ℂ (hermiteL2HilbertBasis j) (Q (T x))‖ ^ 2 ≤
          ((2 * Real.pi * (2 * N + 1))⁻¹ ^ k) ^ 2 *
            ‖inner ℂ (hermiteL2HilbertBasis j) (S x)‖ ^ 2 := by
      intro j
      by_cases hj : j < N
      · have hQb : Q (hermiteL2HilbertBasis j) = 0 := by
          simpa [Q, P, V, hj] using
            ccm_basis_complement_projection hermiteL2HilbertBasis
              N j
        have hinner : inner ℂ (hermiteL2HilbertBasis j) (Q (T x)) = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_left Q (T x)
            (hermiteL2HilbertBasis j), hQself, hQb, inner_zero_left]
        rw [hinner, norm_zero, zero_pow (by omega)]
        positivity
      · have hNj : N ≤ j := Nat.le_of_not_gt hj
        have hQb : Q (hermiteL2HilbertBasis j) = hermiteL2HilbertBasis j := by
          simpa [Q, P, V, hj] using
            ccm_basis_complement_projection hermiteL2HilbertBasis
              N j
        have hinner : inner ℂ (hermiteL2HilbertBasis j) (Q (T x)) =
            inner ℂ (hermiteL2HilbertBasis j) (T x) := by
          rw [← ContinuousLinearMap.adjoint_inner_left Q (T x)
            (hermiteL2HilbertBasis j), hQself, hQb]
        rw [hinner]
        have hbase : 0 < 2 * Real.pi * (2 * N + 1) := by positivity
        have hmono : 2 * Real.pi * (2 * N + 1) ≤
            2 * Real.pi * (2 * j + 1) := by
          gcongr
        have hsm := hS j x
        have hscaled :
            (2 * Real.pi * (2 * N + 1)) ^ k *
                ‖inner ℂ (hermiteL2HilbertBasis j) (T x)‖ ≤
              ‖inner ℂ (hermiteL2HilbertBasis j) (S x)‖ := by
          exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hmono k)
            (norm_nonneg _)).trans hsm
        have hcoef : ‖inner ℂ (hermiteL2HilbertBasis j) (T x)‖ ≤
            (2 * Real.pi * (2 * N + 1))⁻¹ ^ k *
              ‖inner ℂ (hermiteL2HilbertBasis j) (S x)‖ := by
          have hdiv : ‖inner ℂ (hermiteL2HilbertBasis j) (T x)‖ ≤
              ‖inner ℂ (hermiteL2HilbertBasis j) (S x)‖ /
                (2 * Real.pi * (2 * N + 1)) ^ k :=
            (le_div_iff₀ (pow_pos hbase k)).2 (by simpa [mul_comm] using hscaled)
          rw [div_eq_mul_inv, ← inv_pow] at hdiv
          simpa [mul_comm] using hdiv
        simpa [mul_pow] using
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg (by positivity) _)
            (norm_nonneg _))).2 hcoef
    have hsum := Summable.tsum_le_tsum hterm
      (hermiteL2HilbertBasis.summable_norm_inner_sq (Q (T x)))
      ((hermiteL2HilbertBasis.summable_norm_inner_sq (S x)).mul_left _)
    rw [hparseQ, tsum_mul_left, hparseS] at hsum
    have hSnorm : ‖S x‖ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
    have hsquare : ‖Q (T x)‖ ^ 2 ≤
        (((2 * Real.pi * (2 * N + 1))⁻¹ ^ k) * ‖S‖ * ‖x‖) ^ 2 := by
      calc
        ‖Q (T x)‖ ^ 2 ≤
            ((2 * Real.pi * (2 * N + 1))⁻¹ ^ k) ^ 2 * ‖S x‖ ^ 2 := hsum
        _ ≤ ((2 * Real.pi * (2 * N + 1))⁻¹ ^ k) ^ 2 *
            (‖S‖ * ‖x‖) ^ 2 := by gcongr
        _ = (((2 * Real.pi * (2 * N + 1))⁻¹ ^ k) * ‖S‖ * ‖x‖) ^ 2 := by ring
    have hright : 0 ≤
        (2 * Real.pi * (2 * N + 1))⁻¹ ^ k * ‖S‖ * ‖x‖ :=
      mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
        (norm_nonneg S)) (norm_nonneg x)
    nlinarith [norm_nonneg (Q (T x)), hright]
  refine hnorm.trans ?_
  have hpi : 0 < 2 * Real.pi := by positivity
  have hden : (2 * Real.pi * (2 * N + 1))⁻¹ ^ k ≤
      (2 * Real.pi)⁻¹ ^ k * (((N + 1 : ℕ) : ℝ) ^ k)⁻¹ := by
    rw [mul_inv, mul_pow, inv_pow, inv_pow]
    gcongr
    norm_cast
    omega
  calc
    (2 * Real.pi * (2 * N + 1))⁻¹ ^ k * ‖S‖ ≤
        ((2 * Real.pi)⁻¹ ^ k * (((N + 1 : ℕ) : ℝ) ^ k)⁻¹) * ‖S‖ := by gcongr
    _ = (‖S‖ * (2 * Real.pi)⁻¹ ^ k) * (((N + 1 : ℕ) : ℝ) ^ k)⁻¹ := by ring

/-! ## Oscillator coefficients of the cutoff kernel operator -/

theorem conjSLM_hermiteSchwartz (j : ℕ) :
    SchwartzMap.conjSLM (GaloisForLFunctions.hermiteSchwartz j) =
      GaloisForLFunctions.hermiteSchwartz j := by
  ext x
  rw [SchwartzMap.conjSLM_apply]
  change star (((GaloisForLFunctions.hermitePoly j).eval x *
    GaloisForLFunctions.gaussReal x : ℝ) : ℂ) =
      (((GaloisForLFunctions.hermitePoly j).eval x *
        GaloisForLFunctions.gaussReal x : ℝ) : ℂ)
  simp

theorem inner_hermiteL2_hamiltonianPowCLM
    (j k : ℕ) (u : 𝓢(ℝ, ℂ)) :
    inner ℂ (hermiteL2 j)
        ((GaloisForLFunctions.hamiltonianPowCLM k u).toLp 2 volume) =
      (2 * (Real.pi : ℂ) * (2 * j + 1)) ^ k *
        inner ℂ (hermiteL2 j) (u.toLp 2 volume) := by
  unfold hermiteL2
  calc
    inner ℂ ((GaloisForLFunctions.hermiteSchwartz j).toLp 2 volume)
        ((GaloisForLFunctions.hamiltonianPowCLM k u).toLp 2 volume) =
        GaloisForLFunctions.schwartzPair
          (GaloisForLFunctions.hermiteSchwartz j)
          (GaloisForLFunctions.hamiltonianPowCLM k u) := by
      rw [GaloisForLFunctions.schwartzPair_eq_inner,
        conjSLM_hermiteSchwartz]
    _ = GaloisForLFunctions.schwartzPair
          (GaloisForLFunctions.hamiltonianPowCLM k u)
          (GaloisForLFunctions.hermiteSchwartz j) :=
      GaloisForLFunctions.schwartzPair_comm _ _
    _ = (2 * (Real.pi : ℂ) * (2 * j + 1)) ^ k *
          GaloisForLFunctions.schwartzPair u
            (GaloisForLFunctions.hermiteSchwartz j) := by
      simpa only [GaloisForLFunctions.hamiltonianPowCLM_apply] using
        GaloisForLFunctions.schwartzPair_hermiteSchwartz_hamiltonian_iterate k j u
    _ = (2 * (Real.pi : ℂ) * (2 * j + 1)) ^ k *
          GaloisForLFunctions.schwartzPair
            (GaloisForLFunctions.hermiteSchwartz j) u := by
      rw [GaloisForLFunctions.schwartzPair_comm u]
    _ = (2 * (Real.pi : ℂ) * (2 * j + 1)) ^ k *
        inner ℂ ((GaloisForLFunctions.hermiteSchwartz j).toLp 2 volume)
          (u.toLp 2 volume) := by
      rw [GaloisForLFunctions.schwartzPair_eq_inner,
        conjSLM_hermiteSchwartz]

theorem inner_hermiteL2HilbertBasis_hamiltonianPowCLM
    (j k : ℕ) (u : 𝓢(ℝ, ℂ)) :
    inner ℂ (hermiteL2HilbertBasis j)
        ((GaloisForLFunctions.hamiltonianPowCLM k u).toLp 2 volume) =
      (2 * (Real.pi : ℂ) * (2 * j + 1)) ^ k *
        inner ℂ (hermiteL2HilbertBasis j) (u.toLp 2 volume) := by
  simp only [hermiteL2HilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [hermiteL2Unit, inner_smul_left,
    inner_hermiteL2_hamiltonianPowCLM, inner_smul_left]
  ring

theorem inner_ccmOscillatedCutoffOperator
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (v h : SoninL2) :
    inner ℂ h (ccmOscillatedCutoffOperator g k v) =
      ∫ y, v y * inner ℂ h (ccmOscillatedCutoffSlice g k y) := by
  have hint : Integrable (fun y =>
      v y • ccmOscillatedCutoffField g k y) (volume : Measure ℝ) := by
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp (ccmOscillatedCutoffField g k)).smul (Lp.memLp v))
  have hfield : (ccmOscillatedCutoffField g k : ℝ → SoninL2) =ᵐ[volume]
      ccmOscillatedCutoffSlice g k := by
    simpa [ccmOscillatedCutoffField] using
      (ccmOscillatedCutoffSlice_memLp g k).coeFn_toLp
  rw [ccmOscillatedCutoffOperator, l2Synthesis_apply]
  calc
    inner ℂ h (∫ y, v y • ccmOscillatedCutoffField g k y) =
        ∫ y, inner ℂ h (v y • ccmOscillatedCutoffField g k y) :=
      (integral_inner (𝕜 := ℂ) hint h).symm
    _ = ∫ y, v y * inner ℂ h (ccmOscillatedCutoffSlice g k y) := by
      apply integral_congr_ae
      filter_upwards [hfield] with y hy
      rw [hy, inner_smul_right]

theorem inner_hermiteL2HilbertBasis_ccmOscillatedCutoffSlice
    (g : 𝓢(ℝ, ℂ)) (j k : ℕ) (y : ℝ) :
    inner ℂ (hermiteL2HilbertBasis j)
        (ccmOscillatedCutoffSlice g k y) =
      (2 * (Real.pi : ℂ) * (2 * j + 1)) ^ k *
        inner ℂ (hermiteL2HilbertBasis j)
          (ccmOscillatedCutoffSlice g 0 y) := by
  rw [ccmOscillatedCutoffSlice, inner_smul_right,
    inner_hermiteL2HilbertBasis_hamiltonianPowCLM]
  rw [ccmOscillatedCutoffSlice, inner_smul_right]
  simp only [GaloisForLFunctions.hamiltonianPowCLM,
    ContinuousLinearMap.id_apply]
  ring

theorem inner_hermiteL2HilbertBasis_ccmOscillatedCutoffOperator
    (g : 𝓢(ℝ, ℂ)) (j k : ℕ) (v : SoninL2) :
    inner ℂ (hermiteL2HilbertBasis j)
        (ccmOscillatedCutoffOperator g k v) =
      (2 * (Real.pi : ℂ) * (2 * j + 1)) ^ k *
        inner ℂ (hermiteL2HilbertBasis j)
          (ccmOscillatedCutoffOperator g 0 v) := by
  rw [inner_ccmOscillatedCutoffOperator,
    inner_ccmOscillatedCutoffOperator, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [inner_hermiteL2HilbertBasis_ccmOscillatedCutoffSlice]
  ring

theorem ccmOscillatedCutoffOperator_coefficient_smoothing
    (g : 𝓢(ℝ, ℂ)) (j k : ℕ) (v : SoninL2) :
    (2 * Real.pi * (2 * j + 1)) ^ k *
        ‖inner ℂ (hermiteL2HilbertBasis j)
          (ccmOscillatedCutoffOperator g 0 v)‖ ≤
      ‖inner ℂ (hermiteL2HilbertBasis j)
          (ccmOscillatedCutoffOperator g k v)‖ := by
  have hop := inner_hermiteL2HilbertBasis_ccmOscillatedCutoffOperator g j k v
  have hnorm := congrArg norm hop
  rw [norm_mul, norm_pow] at hnorm
  have hcast : (2 * (Real.pi : ℂ) * (2 * j + 1)) =
      ((2 * Real.pi * (2 * j + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at hnorm
  exact hnorm.ge

/-- The source cutoff operator has characteristic values decreasing faster than every power. -/
theorem ccmOscillatedCutoffOperator_isInfinitesimalOfInfiniteOrder
    (g : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder (ccmOscillatedCutoffOperator g 0) := by
  apply infinitesimalOfInfiniteOrder_of_hermiteCoefficientSmoothing
  intro k
  exact ⟨ccmOscillatedCutoffOperator g k,
    ccmOscillatedCutoffOperator_coefficient_smoothing g (k := k)⟩

/-! ## Exact recovery of the published positive Hankel operator -/

theorem inner_ccmPositiveProjection_ccmOscillatedCutoffSlice_zero
    (g h : 𝓢(ℝ, ℂ)) {y : ℝ} (hy : 0 ≤ y) :
    inner ℂ (ccmPositiveHalfLineProjection (h.toLp 2 volume))
        (ccmOscillatedCutoffSlice g 0 y) =
      ∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure := by
  have hp : (((ccmPositiveHalfLineProjection (h.toLp 2 volume) : SoninL2) :
      ℝ → ℂ) =ᵐ[volume]
        (Ici 0).indicator fun x => (h.toLp 2 volume) x) := by
    simpa [ccmPositiveHalfLineProjection] using
      indicatorCutoff_ae (Ici 0) measurableSet_Ici (h.toLp 2 volume)
  have hh := SchwartzMap.coeFn_toLp h 2 volume
  have hu := SchwartzMap.coeFn_toLp (ccmCutoffTranslate g y) 2 volume
  rw [ccmOscillatedCutoffSlice,
    ccmSmoothHalflineCutoff_eq_one hy, Complex.ofReal_one, one_smul]
  simp only [GaloisForLFunctions.hamiltonianPowCLM,
    ContinuousLinearMap.id_apply]
  rw [MeasureTheory.L2.inner_def, ccmPositiveMeasure,
    ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [hp, hh, hu] with x hpx hhx hux
  rw [hpx, hux]
  by_cases hx : 0 ≤ x
  · have hxmem : x ∈ Ici (0 : ℝ) := hx
    rw [indicator_of_mem hxmem]
    rw [hhx]
    rw [indicator_of_mem hxmem]
    simp only [RCLike.inner_apply, ccmCutoffTranslate_apply,
      ccmSmoothHalflineCutoff_eq_one hx, Complex.ofReal_one, one_mul]
  · have hx' : x ∉ Ici 0 := hx
    rw [indicator_of_notMem hx', indicator_of_notMem hx']
    simp

/-- Full-line smooth cutoff operator compressed to the positive half-line. -/
def ccmPositiveCutoffCompression (g : 𝓢(ℝ, ℂ)) :
    SoninL2 →L[ℂ] SoninL2 :=
  ccmPositiveHalfLineProjection ∘L
    ccmOscillatedCutoffOperator g 0 ∘L
      ccmPositiveHalfLineProjection

theorem inner_ccmPositiveCutoffCompression_schwartz
    (f g h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 volume)
        (ccmPositiveCutoffCompression g (f.toLp 2 volume)) =
      ∫ y, f y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
  have hf := SchwartzMap.coeFn_toLp f 2 volume
  have hpf : (((ccmPositiveHalfLineProjection (f.toLp 2 volume) : SoninL2) :
      ℝ → ℂ) =ᵐ[volume]
        (Ici 0).indicator fun y => (f.toLp 2 volume) y) := by
    simpa [ccmPositiveHalfLineProjection] using
      indicatorCutoff_ae (Ici 0) measurableSet_Ici (f.toLp 2 volume)
  rw [ccmPositiveCutoffCompression,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left ccmPositiveHalfLineProjection,
    adjoint_ccmPositiveHalfLineProjection,
    inner_ccmOscillatedCutoffOperator, ccmPositiveMeasure,
    ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [hpf, hf] with y hpfy hfy
  rw [hpfy]
  by_cases hy : 0 ≤ y
  · have hymem : y ∈ Ici (0 : ℝ) := hy
    rw [indicator_of_mem hymem, hfy,
      inner_ccmPositiveProjection_ccmOscillatedCutoffSlice_zero g h hy]
    rw [indicator_of_mem hymem]
    rw [ccmPositiveMeasure]
  · have hy' : y ∉ Ici 0 := hy
    rw [indicator_of_notMem hy', indicator_of_notMem hy']
    simp

/-- The smooth-cutoff operator used in the source proof compresses exactly to the actual
positive-quadrant Hankel operator, not merely to an abstract operator with a similar kernel. -/
theorem ccmPositiveCutoffCompression_eq_ccmPositiveHankel (g : 𝓢(ℝ, ℂ)) :
    ccmPositiveCutoffCompression g = ccmPositiveHankel g := by
  apply ContinuousLinearMap.ext
  intro v
  let p : SoninL2 → Prop := fun v =>
    ccmPositiveCutoffCompression g v = ccmPositiveHankel g v
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) v
  · exact isClosed_eq (ccmPositiveCutoffCompression g).continuous
      (ccmPositiveHankel g).continuous
  · intro f
    apply sub_eq_zero.mp
    refine DenseRange.eq_zero_of_inner_right ℂ
      (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) ?_
    intro h
    rw [inner_sub_right]
    change inner ℂ (h.toLp 2 volume)
        (ccmPositiveCutoffCompression g (f.toLp 2 volume)) -
      inner ℂ (h.toLp 2 volume)
        (ccmPositiveHankel g (f.toLp 2 volume)) = 0
    rw [inner_ccmPositiveCutoffCompression_schwartz,
      inner_ccmPositiveHankel_schwartz, sub_self]

/-! ## Rapid approximation-number ideal algebra -/

theorem IsInfinitesimalOfInfiniteOrder.comp_left
    {T : SoninL2 →L[ℂ] SoninL2}
    (hT : IsInfinitesimalOfInfiniteOrder T)
    (A : SoninL2 →L[ℂ] SoninL2) :
    IsInfinitesimalOfInfiniteOrder (A ∘L T) := by
  intro k
  obtain ⟨C, hC, hbound⟩ := hT k
  refine ⟨‖A‖ * C, mul_nonneg (norm_nonneg A) hC, fun n => ?_⟩
  calc
    approxNumber (A ∘L T) n ≤ ‖A‖ * approxNumber T n :=
      approxNumber_comp_le_left A T n
    _ ≤ ‖A‖ * (C * (((n + 1 : ℕ) : ℝ) ^ k)⁻¹) := by
      gcongr
      exact hbound n
    _ = (‖A‖ * C) * (((n + 1 : ℕ) : ℝ) ^ k)⁻¹ := by ring

theorem IsInfinitesimalOfInfiniteOrder.comp_right
    {T : SoninL2 →L[ℂ] SoninL2}
    (hT : IsInfinitesimalOfInfiniteOrder T)
    (B : SoninL2 →L[ℂ] SoninL2) :
    IsInfinitesimalOfInfiniteOrder (T ∘L B) := by
  intro k
  obtain ⟨C, hC, hbound⟩ := hT k
  refine ⟨C * ‖B‖, mul_nonneg hC (norm_nonneg B), fun n => ?_⟩
  calc
    approxNumber (T ∘L B) n ≤ approxNumber T n * ‖B‖ :=
      approxNumber_comp_le_right T B n
    _ ≤ (C * (((n + 1 : ℕ) : ℝ) ^ k)⁻¹) * ‖B‖ := by
      gcongr
      exact hbound n
    _ = (C * ‖B‖) * (((n + 1 : ℕ) : ℝ) ^ k)⁻¹ := by ring

theorem approxNumber_adjoint (T : SoninL2 →L[ℂ] SoninL2) (n : ℕ) :
    approxNumber (ContinuousLinearMap.adjoint T) n = approxNumber T n := by
  exact rectApproxNumber_adjoint T n

theorem IsInfinitesimalOfInfiniteOrder.adjoint
    {T : SoninL2 →L[ℂ] SoninL2}
    (hT : IsInfinitesimalOfInfiniteOrder T) :
    IsInfinitesimalOfInfiniteOrder (ContinuousLinearMap.adjoint T) := by
  intro k
  obtain ⟨C, hC, hbound⟩ := hT k
  exact ⟨C, hC, fun n => by rw [approxNumber_adjoint]; exact hbound n⟩

theorem IsInfinitesimalOfInfiniteOrder.smul
    {T : SoninL2 →L[ℂ] SoninL2}
    (hT : IsInfinitesimalOfInfiniteOrder T) (c : ℂ) :
    IsInfinitesimalOfInfiniteOrder (c • T) := by
  intro k
  obtain ⟨C, hC, hbound⟩ := hT k
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun n => ?_⟩
  rw [approxNumber_smul]
  calc
    ‖c‖ * approxNumber T n ≤
        ‖c‖ * (C * (((n + 1 : ℕ) : ℝ) ^ k)⁻¹) := by
      gcongr
      exact hbound n
    _ = (‖c‖ * C) * (((n + 1 : ℕ) : ℝ) ^ k)⁻¹ := by ring

theorem IsInfinitesimalOfInfiniteOrder.add
    {S T : SoninL2 →L[ℂ] SoninL2}
    (hS : IsInfinitesimalOfInfiniteOrder S)
    (hT : IsInfinitesimalOfInfiniteOrder T) :
    IsInfinitesimalOfInfiniteOrder (S + T) := by
  intro k
  obtain ⟨CS, hCS, hSbound⟩ := hS k
  obtain ⟨CT, hCT, hTbound⟩ := hT k
  let C : ℝ := (CS + CT) * 2 ^ k
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun n => ?_⟩
  let q : ℕ := n / 2
  have hqq : q + q ≤ n := by
    dsimp [q]
    omega
  have hscaleNat : n + 1 ≤ 2 * (q + 1) := by
    dsimp [q]
    omega
  have hqpos : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hbase : (((q + 1 : ℕ) : ℝ))⁻¹ ≤
      2 * (((n + 1 : ℕ) : ℝ))⁻¹ := by
    have hfrac : (1 : ℝ) / ((q + 1 : ℕ) : ℝ) ≤
        2 / ((n + 1 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hqpos hnpos).2
      norm_num
      exact_mod_cast hscaleNat
    simpa only [one_div, div_eq_mul_inv, one_mul] using hfrac
  have hdecay : ((((q + 1 : ℕ) : ℝ) ^ k)⁻¹) ≤
      2 ^ k * ((((n + 1 : ℕ) : ℝ) ^ k)⁻¹) := by
    rw [← inv_pow, ← inv_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase k
  calc
    approxNumber (S + T) n ≤ approxNumber (S + T) (q + q) :=
      approxNumber_antitone (S + T) hqq
    _ ≤ approxNumber S q + approxNumber T q :=
      approxNumber_add_le S T q q
    _ ≤ CS * ((((q + 1 : ℕ) : ℝ) ^ k)⁻¹) +
        CT * ((((q + 1 : ℕ) : ℝ) ^ k)⁻¹) :=
      add_le_add (hSbound q) (hTbound q)
    _ = (CS + CT) * ((((q + 1 : ℕ) : ℝ) ^ k)⁻¹) := by ring
    _ ≤ (CS + CT) *
        (2 ^ k * ((((n + 1 : ℕ) : ℝ) ^ k)⁻¹)) := by
      gcongr
    _ = C * ((((n + 1 : ℕ) : ℝ) ^ k)⁻¹) := by
      dsimp [C]
      ring

theorem IsInfinitesimalOfInfiniteOrder.neg
    {T : SoninL2 →L[ℂ] SoninL2}
    (hT : IsInfinitesimalOfInfiniteOrder T) :
    IsInfinitesimalOfInfiniteOrder (-T) := by
  simpa only [neg_one_smul] using hT.smul (-1 : ℂ)

theorem IsInfinitesimalOfInfiniteOrder.sub
    {S T : SoninL2 →L[ℂ] SoninL2}
    (hS : IsInfinitesimalOfInfiniteOrder S)
    (hT : IsInfinitesimalOfInfiniteOrder T) :
    IsInfinitesimalOfInfiniteOrder (S - T) := by
  rw [sub_eq_add_neg]
  exact hS.add hT.neg

theorem ccmPositiveHankel_isInfinitesimalOfInfiniteOrder (g : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder (ccmPositiveHankel g) := by
  have h := ((ccmOscillatedCutoffOperator_isInfinitesimalOfInfiniteOrder g).comp_right
    ccmPositiveHalfLineProjection).comp_left ccmPositiveHalfLineProjection
  rw [← ccmPositiveCutoffCompression_eq_ccmPositiveHankel g]
  exact h

theorem ccmPositiveFourierHankelBlock_isInfinitesimalOfInfiniteOrder
    (f : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder (ccmPositiveFourierHankelBlock f) := by
  rw [ccmPositiveFourierHankelBlock_eq_ccmPositiveHankel]
  exact ccmPositiveHankel_isInfinitesimalOfInfiniteOrder
    (FourierTransform.fourierInv f)

theorem ccmTimeUpperCrossBlock_isInfinitesimalOfInfiniteOrder
    (f : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder (ccmTimeUpperCrossBlock f) := by
  rw [ccmTimeUpperCrossBlock_eq_positiveBlock_comp_reflection]
  exact (ccmPositiveFourierHankelBlock_isInfinitesimalOfInfiniteOrder f).comp_right
    l2Reflection

theorem ccmTimeLowerCrossBlock_isInfinitesimalOfInfiniteOrder
    (f : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder (ccmTimeLowerCrossBlock f) := by
  have h := (ccmTimeUpperCrossBlock_isInfinitesimalOfInfiniteOrder
    (SchwartzMap.conjSLM f)).adjoint
  rw [adjoint_ccmTimeUpperCrossBlock_conj] at h
  exact h

theorem ccmHardyUpperCrossBlock_isInfinitesimalOfInfiniteOrder
    (f : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder
      (ccmHardyProjection * ccmSchwartzMultiplier f *
        (1 - ccmHardyProjection)) := by
  rw [ccmHardyUpperCrossBlock_eq_fourierConjugate]
  exact ((ccmTimeUpperCrossBlock_isInfinitesimalOfInfiniteOrder f).comp_left
    fourierUnitary.toLinearIsometry.toContinuousLinearMap).comp_right
      fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap

theorem ccmHardyLowerCrossBlock_isInfinitesimalOfInfiniteOrder
    (f : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder
      ((1 - ccmHardyProjection) * ccmSchwartzMultiplier f *
        ccmHardyProjection) := by
  rw [ccmHardyLowerCrossBlock_eq_fourierConjugate]
  exact ((ccmTimeLowerCrossBlock_isInfinitesimalOfInfiniteOrder f).comp_left
    fourierUnitary.toLinearIsometry.toContinuousLinearMap).comp_right
      fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap

theorem ccmHardyCrossBlockDifference_isInfinitesimalOfInfiniteOrder
    (f : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder
      (ccmHardyProjection * ccmSchwartzMultiplier f *
          (1 - ccmHardyProjection) -
        (1 - ccmHardyProjection) * ccmSchwartzMultiplier f *
          ccmHardyProjection) :=
  (ccmHardyUpperCrossBlock_isInfinitesimalOfInfiniteOrder f).sub
    (ccmHardyLowerCrossBlock_isInfinitesimalOfInfiniteOrder f)

/-- **Connes--Consani `quantsmooth`, full infinite-order statement.** For every Schwartz symbol,
the literal quantized differential has approximation numbers decreasing faster than every
integral power, with no analytic premise or added axiom. -/
theorem ccmQuantizedDifferential_isInfinitesimalOfInfiniteOrder
    (f : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder (ccmQuantizedDifferential f) := by
  rw [ccmQuantizedDifferential_eq_two_smul_crossBlocks]
  exact (ccmHardyCrossBlockDifference_isInfinitesimalOfInfiniteOrder f).smul 2

end RHTower
