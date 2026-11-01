import GaloisForLFunctions.EdgeHodgeTheory.EdgeBelowOneNinth
import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeOfTheCompleteWeilFamily
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGevreyWindow
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold

/-!
# The edge is a crossing

At a fixed horizon the complete Weil family is a continuous path of symmetric matrices in the
overlap. Positivity fails first through a degenerate form, never by a jump: **at the edge the
complete Weil form is positive semidefinite and has a zero mode.**

* **Continuity in the overlap** (`continuousAt_weilQuad_atomicTest`,
  `continuousAt_completeWeilEnergy`, `continuousAt_completeWeilMatrix_apply`): atoms of nearby
  widths differ by `O(|1/w − 1/w₀|)` uniformly with a common Lipschitz bound and support, so Weil's
  form of the atomic tests moves continuously (EAHT's two-sided perturbation bound); polarization
  turns continuity of the quadratic forms into continuity of the entries.
* **Strict positivity is open** (`eventually_nonneg_of_pos`): positivity on the compact unit
  sphere persists in a neighbourhood of the overlap.
* **The crossing theorem** (`crossing_of_firstFailure`, `edge_is_a_crossing`): if positivity first
  fails at a finite overlap `e > 1`, the form at `e` is positive semidefinite (limit from the left)
  and not positive definite (otherwise positivity would persist beyond `e`).
* **Without RH the edge is a zero mode** (`frequently_zero_mode_in_window_of_not_rh`): for the
  tilted spline, infinitely often the complete Weil form has a zero mode at an overlap in
  `[(log N)^α, 2(log N)^β]` at which it is still positive semidefinite.

So the edge is an equation, not an estimate: it is a root of the lowest eigenvalue of the overlap
flow, the first overlap at which a zero mode appears.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace ENNReal

namespace GaloisForLFunctions.EdgeHodgeTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory

/-! ### Quadratic forms of continuous families of symmetric matrices -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form of a real matrix as a double sum. -/
theorem inner_toEuclideanLin_eq_sum (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪Matrix.toEuclideanLin A x, x⟫ = ∑ i, ∑ j, x i * A i j * x j := by
  simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem inner_toEuclideanLin_smul (A : Matrix ι ι ℝ) (t : ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪Matrix.toEuclideanLin A (t • x), t • x⟫ = t ^ 2 * ⟪Matrix.toEuclideanLin A x, x⟫ := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Joint continuity of the quadratic form in the parameter and the vector. -/
theorem continuousAt_quad {A : ℝ → Matrix ι ι ℝ} {c₀ : ℝ}
    (hA : ∀ i j, ContinuousAt (fun c => A c i j) c₀) (x : EuclideanSpace ℝ ι) :
    ContinuousAt (fun z : ℝ × EuclideanSpace ℝ ι => ⟪Matrix.toEuclideanLin (A z.1) z.2, z.2⟫)
      (c₀, x) := by
  simp only [inner_toEuclideanLin_eq_sum]
  unfold ContinuousAt
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  have hi : Continuous fun z : ℝ × EuclideanSpace ℝ ι => z.2 i :=
    (PiLp.continuous_apply 2 _ i).comp continuous_snd
  have hj : Continuous fun z : ℝ × EuclideanSpace ℝ ι => z.2 j :=
    (PiLp.continuous_apply 2 _ j).comp continuous_snd
  exact (hi.continuousAt.mul ((hA i j).comp_of_eq continuousAt_fst rfl)).mul hj.continuousAt

/-- **Strict positivity is open in the parameter.** -/
theorem eventually_nonneg_of_pos {A : ℝ → Matrix ι ι ℝ} {c₀ : ℝ}
    (hA : ∀ i j, ContinuousAt (fun c => A c i j) c₀)
    (hpos : ∀ x : EuclideanSpace ℝ ι, x ≠ 0 → 0 < ⟪Matrix.toEuclideanLin (A c₀) x, x⟫) :
    ∀ᶠ c in 𝓝 c₀, ∀ x : EuclideanSpace ℝ ι, 0 ≤ ⟪Matrix.toEuclideanLin (A c) x, x⟫ := by
  have hK := isCompact_sphere (0 : EuclideanSpace ℝ ι) 1
  have hev : ∀ᶠ c in 𝓝 c₀, ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1,
      0 < ⟪Matrix.toEuclideanLin (A c) y, y⟫ := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy; exact zero_ne_one hy
    exact (continuousAt_quad hA y).eventually (lt_mem_nhds (hpos y hy0))
  filter_upwards [hev] with c hc x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set y := ‖x‖⁻¹ • x
    have hy : y ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hxy : x = ‖x‖ • y := by simp [y, smul_smul, mul_inv_cancel₀ hn.ne']
    rw [hxy, inner_toEuclideanLin_smul]
    exact mul_nonneg (sq_nonneg _) (hc y hy).le

/-- **The crossing theorem.** If positivity first fails at `e > 1` and the family is continuous at
`e`, the form at `e` is positive semidefinite and has a zero mode. -/
theorem crossing_of_firstFailure {A : ℝ → Matrix ι ι ℝ} {e : ℝ} (he : 1 < e)
    (hedge : firstFailure
      (fun c => ∀ x : EuclideanSpace ℝ ι, 0 ≤ ⟪Matrix.toEuclideanLin (A c) x, x⟫) =
        ENNReal.ofReal e)
    (hA : ∀ i j, ContinuousAt (fun c => A c i j) e) :
    (∀ x : EuclideanSpace ℝ ι, 0 ≤ ⟪Matrix.toEuclideanLin (A e) x, x⟫) ∧
      ∃ x : EuclideanSpace ℝ ι, x ≠ 0 ∧ ⟪Matrix.toEuclideanLin (A e) x, x⟫ = 0 := by
  have hbelow := ofReal_le_firstFailure_iff.mp hedge.ge
  have hpsd : ∀ x : EuclideanSpace ℝ ι, 0 ≤ ⟪Matrix.toEuclideanLin (A e) x, x⟫ := by
    intro x
    have hcont : ContinuousAt (fun c => ⟪Matrix.toEuclideanLin (A c) x, x⟫) e := by
      simp only [inner_toEuclideanLin_eq_sum]
      unfold ContinuousAt
      exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        (tendsto_const_nhds.mul (hA i j)).mul tendsto_const_nhds
    have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioo 1 e))
    haveI : (𝓝[Set.Ioo 1 e] e).NeBot := right_nhdsWithin_Ioo_neBot he
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun c hc =>
      hbelow c hc.1.le hc.2 x)
  refine ⟨hpsd, ?_⟩
  by_contra hno
  push Not at hno
  have hpos : ∀ x : EuclideanSpace ℝ ι, x ≠ 0 → 0 < ⟪Matrix.toEuclideanLin (A e) x, x⟫ :=
    fun x hx => lt_of_le_of_ne (hpsd x) (Ne.symm (hno x hx))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nonneg_of_pos hA hpos)
  have habove : ENNReal.ofReal (e + δ) ≤ firstFailure
      (fun c => ∀ x : EuclideanSpace ℝ ι, 0 ≤ ⟪Matrix.toEuclideanLin (A c) x, x⟫) := by
    refine ofReal_le_firstFailure_iff.mpr fun c hc hcδ => ?_
    rcases lt_or_ge c e with hce | hce
    · exact hbelow c hc hce
    · exact hball (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
  rw [hedge, ENNReal.ofReal_le_ofReal_iff (by linarith)] at habove
  linarith

theorem quad_single_add_sub (A : Matrix ι ι ℝ) (i j : ι) :
    ⟪Matrix.toEuclideanLin A (EuclideanSpace.single i 1 + EuclideanSpace.single j 1),
        EuclideanSpace.single i 1 + EuclideanSpace.single j 1⟫ -
      ⟪Matrix.toEuclideanLin A (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫ -
      ⟪Matrix.toEuclideanLin A (EuclideanSpace.single j 1), EuclideanSpace.single j 1⟫ =
      A i j + A j i := by
  simp only [inner_toEuclideanLin_eq_sum, PiLp.add_apply, PiLp.single_apply]
  simp [add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- **Polarization.** Symmetric matrices whose quadratic forms are continuous at `c₀` for every
vector have continuous entries at `c₀`. -/
theorem continuousAt_apply_of_quad {A : ℝ → Matrix ι ι ℝ} {c₀ : ℝ}
    (hsym : ∀ c, Matrix.IsHermitian (A c))
    (hQ : ∀ x : EuclideanSpace ℝ ι, ContinuousAt (fun c => ⟪Matrix.toEuclideanLin (A c) x, x⟫) c₀)
    (i j : ι) : ContinuousAt (fun c => A c i j) c₀ := by
  have h : (fun c => A c i j) = fun c =>
      (⟪Matrix.toEuclideanLin (A c) (EuclideanSpace.single i 1 + EuclideanSpace.single j 1),
          EuclideanSpace.single i 1 + EuclideanSpace.single j 1⟫ -
        ⟪Matrix.toEuclideanLin (A c) (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫ -
        ⟪Matrix.toEuclideanLin (A c) (EuclideanSpace.single j 1), EuclideanSpace.single j 1⟫) /
          2 := by
    funext c
    rw [quad_single_add_sub]
    have := (hsym c).apply i j
    simp only [star_trivial] at this
    rw [this]
    ring
  rw [h]
  exact (((hQ _).sub (hQ _)).sub (hQ _)).div_const 2

end Generic

/-! ### Continuity of the complete Weil family in the overlap -/

section Continuity

variable {φ : ℝ → ℝ}

/-- An atom vanishes off `[0, w]`. -/
theorem atomDilate_eq_zero (hφ : Admissible φ) {w u : ℝ} (hw : 0 < w)
    (hu : u < 0 ∨ w < u) : atomDilate φ w u = 0 := by
  unfold atomDilate
  refine hφ.supp _ fun h => ?_
  obtain ⟨h0, h1⟩ := h
  rcases hu with hu | hu
  · have : u / w < 0 := div_neg_of_neg_of_pos hu hw
    linarith
  · have : 1 < u / w := (one_lt_div hw).mpr hu
    linarith

/-- Atoms of nearby widths are uniformly close. -/
theorem abs_atomDilate_sub_le (hφ : Admissible φ) {L : ℝ}
    (hL : ∀ u v, |φ u - φ v| ≤ L * |u - v|) {w w₀ : ℝ} (hw : 0 < w) (hw₀ : 0 < w₀)
    (hww : w ≤ 2 * w₀) (u : ℝ) :
    |atomDilate φ w u - atomDilate φ w₀ u| ≤ L * (2 * w₀) * |1 / w - 1 / w₀| := by
  have hL0 : 0 ≤ L := by
    have := hL 1 0
    rw [sub_zero, abs_one, mul_one] at this
    exact (abs_nonneg _).trans this
  by_cases hu : 0 ≤ u ∧ u ≤ 2 * w₀
  · have h := hL (u / w) (u / w₀)
    have e : u / w - u / w₀ = u * (1 / w - 1 / w₀) := by ring
    rw [e, abs_mul, abs_of_nonneg hu.1] at h
    calc |atomDilate φ w u - atomDilate φ w₀ u| = |φ (u / w) - φ (u / w₀)| := rfl
      _ ≤ L * (u * |1 / w - 1 / w₀|) := h
      _ ≤ L * (2 * w₀ * |1 / w - 1 / w₀|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _)) hL0
      _ = L * (2 * w₀) * |1 / w - 1 / w₀| := by ring
  · have hu' : u < 0 ∨ 2 * w₀ < u := by
      by_contra h; push Not at h; exact hu ⟨h.1, h.2⟩
    rw [atomDilate_eq_zero hφ hw (hu'.imp id fun h => by linarith),
      atomDilate_eq_zero hφ hw₀ (hu'.imp id fun h => by linarith), sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hL0 (by linarith)) (abs_nonneg _)

/-- An atom of width `w` is Lipschitz with constant `L/w`. -/
theorem abs_atomDilate_sub_le_lip {L : ℝ} (hL : ∀ u v, |φ u - φ v| ≤ L * |u - v|) {w : ℝ}
    (hw : 0 < w) (u v : ℝ) :
    |atomDilate φ w u - atomDilate φ w v| ≤ L / w * |u - v| := by
  have h := hL (u / w) (v / w)
  rw [show u / w - v / w = (u - v) / w by ring, abs_div, abs_of_pos hw] at h
  calc |atomDilate φ w u - atomDilate φ w v| = |φ (u / w) - φ (v / w)| := rfl
    _ ≤ L * (|u - v| / w) := h
    _ = L / w * |u - v| := by ring

/-- The atomic tests of widths up to `2w₀` vanish beyond `log N + 2w₀`. -/
theorem supportedIn_atomicTest_atomDilate (hφ : Admissible φ) (N : ℕ) (y : ℕ → ℝ) {w w₀ : ℝ}
    (hw : 0 < w) (hww : w ≤ 2 * w₀) :
    SupportedIn (Real.log N + 2 * w₀) (atomicTest N y (atomDilate φ w)) := by
  intro u hu
  unfold atomicTest
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn1 := Finset.mem_Icc.mp hn
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hn1.2)
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rw [atomDilate_eq_zero hφ hw, mul_zero]
  rcases lt_abs.mp hu with h | h
  · right; linarith
  · left; linarith

/-- **Weil's form of the atomic tests is continuous in the width.** -/
theorem continuousAt_weilQuad_atomicTest (hφ : Admissible φ) (N : ℕ) (y : ℕ → ℝ) {w₀ : ℝ}
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun w => weilQuad (atomicTest N y (atomDilate φ w))) w₀ := by
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hφ.supp u hu
  obtain ⟨-, -, L, -, -, -, hL⟩ := exists_test_constants hφ.contDiff hφc
  set S : ℝ := ∑ n ∈ Icc 1 N, |y n| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set R' : ℝ := Real.log N + 2 * w₀ with hR'def
  have hR' : 0 ≤ R' := by have := Real.log_natCast_nonneg N; positivity
  set F := atomicTest N y (atomDilate φ w₀) with hFdef
  have hF2 : ContDiff ℝ 2 F := contDiff_atomicTest (atomDilate_facts hφ.contDiff hφ.supp hw₀).1 N y
  have hFR : SupportedIn R' F := supportedIn_atomicTest_atomDilate hφ N y hw₀ (by linarith)
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -R') (b := R')) fun u hu => hFR u (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact hu)
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro w hw
  set e : ℕ → ℝ := fun n => S * (L * (2 * w₀) * |1 / w n - 1 / w₀|) with hedef
  set LD : ℝ := S * (L * (3 / w₀)) with hLD
  set Dn : ℕ → ℝ → ℝ := fun n u => atomicTest N y (atomDilate φ (w n)) u - F u with hDn
  have hinv : Tendsto (fun n => 1 / w n) atTop (𝓝 (1 / w₀)) := by
    simpa only [one_div] using hw.inv₀ hw₀.ne'
  have he : Tendsto e atTop (𝓝 0) := by
    have := (((hinv.sub_const (1 / w₀)).abs).const_mul (L * (2 * w₀))).const_mul S
    simpa only [sub_self, abs_zero, mul_zero] using this
  have hV : Tendsto (fun n => synthLevy R' (e n) LD 1) atTop (𝓝 0) :=
    tendsto_synthLevy_of (LD := fun _ => LD) (k := fun _ => 1) (a := LD) he (by simp) (by simp)
  have hwe : ∀ᶠ n in atTop, w n ∈ Set.Ioo (w₀ / 2) (2 * w₀) :=
    hw (Ioo_mem_nhds (by linarith) (by linarith))
  have hD : ∀ᶠ n in atTop, ContDiff ℝ 2 (Dn n) ∧ SupportedIn R' (Dn n) ∧
      (∀ u, |Dn n u| ≤ e n) ∧ (∀ u v, |Dn n u - Dn n v| ≤ LD * |u - v|) ∧ (1 : ℝ) ≤ 1 := by
    filter_upwards [hwe] with n ⟨hn1, hn2⟩
    have hwn : 0 < w n := by linarith
    have hG := contDiff_atomicTest (atomDilate_facts hφ.contDiff hφ.supp hwn).1 N y
    have hGR := supportedIn_atomicTest_atomDilate hφ N y hwn hn2.le
    -- the difference as one sum over the atoms
    have hsum : ∀ u, Dn n u = ∑ m ∈ Icc 1 N,
        y m * (atomDilate φ (w n) (u - Real.log m) - atomDilate φ w₀ (u - Real.log m)) := by
      intro u
      simp only [hDn, hFdef, atomicTest, ← Finset.sum_sub_distrib, mul_sub]
    refine ⟨hG.sub hF2, fun u hu => ?_, fun u => ?_, fun u v => ?_, le_rfl⟩
    · simp only [hDn, hGR u hu, hFR u hu, sub_zero]
    · rw [hsum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      show _ ≤ S * (L * (2 * w₀) * |1 / w n - 1 / w₀|)
      rw [hS, Finset.sum_mul]
      refine Finset.sum_le_sum fun m _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_atomDilate_sub_le hφ hL hwn hw₀ hn2.le _) (abs_nonneg _)
    · rw [hsum, hsum, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      show _ ≤ S * (L * (3 / w₀)) * |u - v|
      rw [hS, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun m _ => ?_
      have hL0 : 0 ≤ L := by
        have := hL 1 0
        rw [sub_zero, abs_one, mul_one] at this
        exact (abs_nonneg _).trans this
      have h1 := abs_atomDilate_sub_le_lip hL hwn (u - Real.log m) (v - Real.log m)
      have h2 := abs_atomDilate_sub_le_lip hL hw₀ (u - Real.log m) (v - Real.log m)
      rw [show u - Real.log m - (v - Real.log m) = u - v by ring] at h1 h2
      have hinvn : 1 / w n ≤ 2 / w₀ := by
        rw [div_le_div_iff₀ hwn hw₀]; linarith
      have hsplit : y m * (atomDilate φ (w n) (u - Real.log m) -
            atomDilate φ w₀ (u - Real.log m)) -
          y m * (atomDilate φ (w n) (v - Real.log m) - atomDilate φ w₀ (v - Real.log m)) =
          y m * ((atomDilate φ (w n) (u - Real.log m) - atomDilate φ (w n) (v - Real.log m)) -
            (atomDilate φ w₀ (u - Real.log m) - atomDilate φ w₀ (v - Real.log m))) := by ring
      rw [hsplit, abs_mul]
      have habs : |(atomDilate φ (w n) (u - Real.log m) - atomDilate φ (w n) (v - Real.log m)) -
          (atomDilate φ w₀ (u - Real.log m) - atomDilate φ w₀ (v - Real.log m))| ≤
          L * (3 / w₀) * |u - v| := by
        refine (abs_sub _ _).trans ?_
        have hLw : L / w n ≤ L * (2 / w₀) := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinvn hL0
        have : L / w n * |u - v| + L / w₀ * |u - v| ≤ L * (3 / w₀) * |u - v| := by
          have hrw : L * (3 / w₀) = L * (2 / w₀) + L / w₀ := by ring
          rw [hrw, add_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hLw (abs_nonneg _)) le_rfl
        linarith
      calc |y m| * |(atomDilate φ (w n) (u - Real.log m) - atomDilate φ (w n) (v - Real.log m)) -
            (atomDilate φ w₀ (u - Real.log m) - atomDilate φ w₀ (v - Real.log m))|
          ≤ |y m| * (L * (3 / w₀) * |u - v|) := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
        _ = |y m| * (L * (3 / w₀)) * |u - v| := by ring
  have key := EffectiveArithmeticHodgeTheory.tendsto_weilQuad_add hF2 hFc hFR hR'
    (Dn := Dn) (e := e) (LD := fun _ => LD) (k := fun _ => 1) hD he hV
  refine key.congr fun n => ?_
  simp only [Function.comp, hDn]
  congr 1
  funext u
  ring

/-- **The complete Weil energy is continuous in the overlap.** -/
theorem continuousAt_completeWeilEnergy (hφ : Admissible φ) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ContinuousAt (fun c => completeWeilEnergy φ c N x) c₀ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ContinuousAt (fun c : ℝ => c / N) c₀ := continuousAt_id.div_const _
  have hf : ContinuousAt (fun c => weilQuad (atomicTest N (primeHorizonExtension x)
      (atomDilate φ (c / N))) / (c / N * ∫ u, φ u ^ 2)) c₀ := by
    have h2 := (continuousAt_weilQuad_atomicTest hφ N (primeHorizonExtension x)
      (div_pos hc₀ hN0)).comp_of_eq h1 rfl
    exact h2.div (h1.mul continuousAt_const) (mul_pos (div_pos hc₀ hN0) hφ.sq_pos).ne'
  refine hf.congr ?_
  filter_upwards [lt_mem_nhds hc₀] with c hc
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ.contDiff hφ.supp hc hN,
    integral_atomDilate_sq (div_pos hc hN0)]

/-- **The entries of the complete Weil matrix are continuous in the overlap.** -/
theorem continuousAt_completeWeilMatrix_apply (hφ : Admissible φ) {N : ℕ} (hN : 1 ≤ N) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (i j : PrimeHorizonIndex N) :
    ContinuousAt (fun c => completeWeilMatrix φ c N i j) c₀ :=
  continuousAt_apply_of_quad (fun c => completeWeilMatrix_isHermitian φ c N)
    (fun x => continuousAt_completeWeilEnergy hφ hN x hc₀) i j

end Continuity

/-! ### The edge is a crossing -/

/-- **The edge is a crossing.** If the edge of an admissible profile at a horizon `N ≥ 1` is a finite
overlap `e > 1`, then at `e` the complete Weil form is positive semidefinite and has a zero mode. -/
theorem edge_is_a_crossing {φ : ℝ → ℝ} (hφ : Admissible φ) {N : ℕ} (hN : 1 ≤ N) {e : ℝ}
    (he : 1 < e) (hedge : edge φ N = ENNReal.ofReal e) :
    PositiveAt φ e N ∧
      ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 ∧ completeWeilEnergy φ e N x = 0 :=
  crossing_of_firstFailure (A := fun c => completeWeilMatrix φ c N) he hedge
    (continuousAt_completeWeilMatrix_apply hφ hN (by linarith))

/-- **Without RH the edge is a zero mode.** For `0 < α < 1/9` and `β > 1/4`, infinitely often the
complete Weil form of the tilted spline has a zero mode at an overlap `c ∈ [(log N)^α, 2(log N)^β]`
at which it is still positive semidefinite. -/
theorem frequently_zero_mode_in_window_of_not_rh (hRH : ¬ RiemannHypothesis) {α β : ℝ}
    (hα : 0 < α) (hα' : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent)
    (hβ : 1 / 4 < β) :
    ∃ᶠ N : ℕ in atTop, ∃ c : ℝ, Real.log N ^ α ≤ c ∧ c ≤ 2 * Real.log N ^ β ∧
      PositiveAt tiltedUnitSpline c N ∧
      ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 ∧
        completeWeilEnergy tiltedUnitSpline c N x = 0 := by
  have hlog : Tendsto (fun N : ℕ => Real.log N ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ((frequently_edge_mem_window_of_not_riemannHypothesis_below_one_ninth hRH hα hα' hβ).and_eventually
    ((hlog.eventually_gt_atTop 1).and (eventually_ge_atTop 1))).mono
      fun N ⟨⟨hlow, hup⟩, h1, hN⟩ => ?_
  have hne : edge tiltedUnitSpline N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  set e := (edge tiltedUnitSpline N).toReal with he
  have hedge : edge tiltedUnitSpline N = ENNReal.ofReal e := (ENNReal.ofReal_toReal hne).symm
  have hlowe : Real.log N ^ α ≤ e := by
    rw [hedge] at hlow
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hlow
  have hupe : e ≤ 2 * Real.log N ^ β := by
    rw [hedge] at hup
    have hpos : 0 ≤ 2 * Real.log N ^ β := by
      have := Real.log_natCast_nonneg N; positivity
    exact (ENNReal.ofReal_le_ofReal_iff hpos).mp hup
  obtain ⟨hpsd, hzero⟩ := edge_is_a_crossing admissible_tiltedUnitSpline hN (by linarith) hedge
  exact ⟨e, hlowe, hupe, hpsd, hzero⟩

end GaloisForLFunctions.EdgeHodgeTheory

#print axioms GaloisForLFunctions.EdgeHodgeTheory.frequently_zero_mode_in_window_of_not_rh
