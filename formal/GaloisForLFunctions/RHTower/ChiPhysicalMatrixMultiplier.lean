import GaloisForLFunctions.RHTower.ChiPhysicalStationaryKernel
import GaloisForLFunctions.RHTower.ChiDegreeTwoRootMatrix
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Complete physical degree-two stationary matrices

Fourier inversion of the actual smooth logarithmic window expresses its pair weight
as an integrable mixture of separate row and column phases. These preserve coefficient
energy, so the full integer root matrix retains cancellation under its physical saddle
amplitude. Exact factorization keeps the conductor phase and the full stationary main.
-/

noncomputable section
open Complex MeasureTheory Set Filter FourierTransform
open scoped Topology ContDiff FourierTransform
namespace GaloisForLFunctions.RHTower

private def multiplierPhase (u x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * u * x : ℝ) : ℂ) * I)

private theorem norm_multiplierPhase (u x : ℝ) : ‖multiplierPhase u x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

private theorem continuous_multiplierPhase (x : ℝ) : Continuous (fun u => multiplierPhase u x) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    ((continuous_const.mul continuous_id).mul_const x)).mul continuous_const)

private theorem multiplierPhase_add (u x y : ℝ) :
    multiplierPhase u (x + y) = multiplierPhase u x * multiplierPhase u y := by
  unfold multiplierPhase
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem schwartz_multiplier_representation (h : SchwartzMap ℝ ℂ) (x : ℝ) :
    h x = ∫ u : ℝ, (𝓕 h) u * multiplierPhase u x := by
  have hf : (𝓕⁻ (𝓕 (h : ℝ → ℂ))) x = h x :=
    congrFun (h.continuous.fourierInv_fourier_eq h.integrable (𝓕 h).integrable) x
  rw [Real.fourierInv_eq'] at hf
  simpa only [SchwartzMap.fourier_coe, real_inner_comm, RCLike.inner_apply,
    conj_trivial, smul_eq_mul, multiplierPhase, mul_comm, mul_assoc] using hf.symm

private theorem integrable_multiplierPhase (h : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun u : ℝ => (𝓕 h) u * multiplierPhase u x) :=
  (𝓕 h).integrable.mul_bdd (continuous_multiplierPhase x).aestronglyMeasurable
    (Eventually.of_forall fun u => (norm_multiplierPhase u x).le)

/-- A smooth compact logarithmic weight acts through an exact integrable mixture of separate
row and column phases. Thus cancellation is preserved before any coefficient restriction. -/
theorem norm_schwartz_weighted_matrix_form_le
    {ι κ : Type*} (S : Finset ι) (T : Finset κ) (M : ι → κ → ℂ)
    (h : SchwartzMap ℝ ℂ) {B : ℝ}
    (hbase : ∀ (c : ι → ℂ) (d : κ → ℂ),
      ‖∑ i ∈ S, ∑ j ∈ T, c i * d j * M i j‖ ≤
        B * Real.sqrt (∑ i ∈ S, ‖c i‖ ^ 2) * Real.sqrt (∑ j ∈ T, ‖d j‖ ^ 2))
    (x : ι → ℝ) (y : κ → ℝ) (z : ℝ) (c : ι → ℂ) (d : κ → ℂ) :
    ‖∑ i ∈ S, ∑ j ∈ T, c i * d j * M i j * h (x i + y j + z)‖ ≤
      (∫ u : ℝ, ‖(𝓕 h) u‖) * B *
        Real.sqrt (∑ i ∈ S, ‖c i‖ ^ 2) * Real.sqrt (∑ j ∈ T, ‖d j‖ ^ 2) := by
  let E := B * Real.sqrt (∑ i ∈ S, ‖c i‖ ^ 2) * Real.sqrt (∑ j ∈ T, ‖d j‖ ^ 2)
  let F : ℝ → ℂ := fun u => ∑ i ∈ S, ∑ j ∈ T,
    (c i * d j * M i j) * ((𝓕 h) u * multiplierPhase u (x i + y j + z))
  have hi (i : ι) (j : κ) : Integrable (fun u : ℝ =>
      (c i * d j * M i j) * ((𝓕 h) u * multiplierPhase u (x i + y j + z))) :=
    (integrable_multiplierPhase h (x i + y j + z)).const_mul _
  have hintegral : (∫ u : ℝ, F u) =
      ∑ i ∈ S, ∑ j ∈ T, c i * d j * M i j * h (x i + y j + z) := by
    unfold F
    rw [integral_finsetSum S (fun i _ => integrable_finsetSum T (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum T (fun j _ => hi i j)]
    simp_rw [integral_const_mul, ← schwartz_multiplier_representation]
  have hpoint (u : ℝ) : ‖F u‖ ≤ ‖(𝓕 h) u‖ * E := by
    let c' : ι → ℂ := fun i => c i * multiplierPhase u (x i)
    let d' : κ → ℂ := fun j => d j * multiplierPhase u (y j)
    have hc (i : ι) : ‖c' i‖ = ‖c i‖ := by simp only [c', norm_mul, norm_multiplierPhase, mul_one]
    have hd (j : κ) : ‖d' j‖ = ‖d j‖ := by simp only [d', norm_mul, norm_multiplierPhase, mul_one]
    have hb := hbase c' d'
    simp_rw [hc, hd] at hb
    have hfactor : F u = (𝓕 h) u * multiplierPhase u z *
        (∑ i ∈ S, ∑ j ∈ T, c' i * d' j * M i j) := by
      dsimp [F, c', d']
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [multiplierPhase_add, multiplierPhase_add]
      ring
    rw [hfactor, norm_mul, norm_mul, norm_multiplierPhase, mul_one]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  rw [← hintegral]
  have hh := norm_integral_le_of_norm_le (μ := volume) ((𝓕 h).integrable.norm.mul_const E)
    (Eventually.of_forall hpoint)
  apply hh.trans_eq
  rw [integral_mul_const]
  dsimp [E]
  ring

/-- The actual physical stationary amplitude in logarithmic saddle coordinates. -/
def physicalLogWindow (u : ℝ) : ℂ :=
  ((Real.exp (u / 2) * bagPhysicalHeightWindow (Real.exp u) : ℝ) : ℂ)

theorem contDiff_physicalLogWindow : ContDiff ℝ ∞ physicalLogWindow :=
  Complex.ofRealCLM.contDiff.comp
    (((contDiff_id.div_const 2).exp).mul (bagPhysicalHeightWindow.contDiff.comp Real.contDiff_exp))

theorem hasCompactSupport_physicalLogWindow : HasCompactSupport physicalLogWindow := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) (Real.log 2)) isCompact_Icc
  intro u hu
  have hw : bagPhysicalHeightWindow (Real.exp u) = 0 := by
    apply bagPhysicalHeightWindow.zero_of_le_dist
    change (1 / 2 : ℝ) ≤ dist (Real.exp u) (3 / 2 : ℝ)
    rw [Real.dist_eq]
    by_cases hu0 : u < 0
    · have he : Real.exp u ≤ 1 := by simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hu0.le)
      linarith [neg_le_abs (Real.exp u - 3 / 2)]
    · have hu2 : Real.log 2 < u := by
        by_contra hh
        exact hu ⟨le_of_not_gt hu0, le_of_not_gt hh⟩
      have he : 2 ≤ Real.exp u := by
        simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using (Real.exp_le_exp.mpr hu2.le)
      linarith [le_abs_self (Real.exp u - 3 / 2)]
  simp [physicalLogWindow, hw]

/-- Source-built Schwartz amplitude; its Fourier L1 budget is finite without an extra premise. -/
def physicalLogWindowSchwartz : SchwartzMap ℝ ℂ :=
  hasCompactSupport_physicalLogWindow.toSchwartzMap contDiff_physicalLogWindow

/-- The exact Fourier budget paid by the actual smooth physical matrix weight. -/
def physicalLogWindowFourierBudget : ℝ := ∫ u : ℝ, ‖(𝓕 physicalLogWindowSchwartz) u‖

theorem physicalLogWindowFourierBudget_nonneg : 0 ≤ physicalLogWindowFourierBudget :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- The complete integer root-phase kernel underlying the physical degree-two main. -/
def physicalRootKernel (N r s : ℕ) : ℂ :=
  Complex.exp (((4 * Real.pi * Real.sqrt ((N : ℝ) + r) *
    Real.sqrt ((N : ℝ) + s) : ℝ) : ℂ) * I)

/-- The source full-row energy theorem gives the complete bilinear root-matrix bound. -/
theorem norm_physicalRootKernel_form_le {N : ℕ} (hN : 1 ≤ N) (c d : ℕ → ℂ) :
    ‖∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
      c r * d s * physicalRootKernel N r s‖ ≤
      Real.sqrt (16 * (N : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ))) *
        Real.sqrt (∑ r ∈ Finset.range (N + 1), ‖c r‖ ^ 2) *
        Real.sqrt (∑ s ∈ Finset.range (N + 1), ‖d s‖ ^ 2) := by
  let V := ∑ r ∈ Finset.range (N + 1),
    c r • _root_.RHTower.chiDegreeTwoRootRow N ((N : ℝ) + r)
  have hv (s : Fin (N + 1)) : V s =
      ∑ r ∈ Finset.range (N + 1), c r * physicalRootKernel N r s := by
    simp [V, WithLp.ofLp_sum, WithLp.ofLp_smul, _root_.RHTower.chiDegreeTwoRootRow,
      physicalRootKernel, Finset.sum_apply]
  have heq : (∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
      c r * d s * physicalRootKernel N r s) = ∑ s : Fin (N + 1), V s * d s := by
    simp_rw [hv, Finset.sum_mul]
    rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => ∑ r ∈ Finset.range (N + 1),
      c r * physicalRootKernel N r s * d s) (N + 1), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hV : ‖V‖ ≤ Real.sqrt (16 * (N : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ))) *
      Real.sqrt (∑ r ∈ Finset.range (N + 1), ‖c r‖ ^ 2) := by
    have h := Real.sqrt_le_sqrt (_root_.RHTower.norm_sum_smul_chiDegreeTwoRootRow_sq_le hN c)
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity)] at h
    exact h
  rw [heq]
  calc
    ‖∑ s : Fin (N + 1), V s * d s‖ ≤ ∑ s : Fin (N + 1), ‖V s‖ * ‖d s‖ := by
      simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset (Fin (N + 1))) (fun s => V s * d s)
    _ ≤ Real.sqrt (∑ s : Fin (N + 1), ‖V s‖ ^ 2) *
        Real.sqrt (∑ s : Fin (N + 1), ‖d s‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖V‖ * Real.sqrt (∑ s ∈ Finset.range (N + 1), ‖d s‖ ^ 2) := by
      rw [← EuclideanSpace.norm_eq, Fin.sum_univ_eq_sum_range (fun s : ℕ => ‖d s‖ ^ 2) (N + 1)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hV (Real.sqrt_nonneg _)

/-- The actual physical logarithmic amplitude preserves the complete root-matrix cancellation.
The Fourier budget is constructed from the fixed height window, not supplied as a hypothesis. -/
theorem norm_physicalLogWindow_root_form_le {N : ℕ} (hN : 1 ≤ N)
    (z : ℝ) (c d : ℕ → ℂ) :
    ‖∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
      c r * d s * physicalRootKernel N r s *
        physicalLogWindow (Real.log ((N : ℝ) + r) / 2 +
          Real.log ((N : ℝ) + s) / 2 + z)‖ ≤
      physicalLogWindowFourierBudget *
        Real.sqrt (16 * (N : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ))) *
        Real.sqrt (∑ r ∈ Finset.range (N + 1), ‖c r‖ ^ 2) *
        Real.sqrt (∑ s ∈ Finset.range (N + 1), ‖d s‖ ^ 2) := by
  exact norm_schwartz_weighted_matrix_form_le (Finset.range (N + 1)) (Finset.range (N + 1))
    (physicalRootKernel N) physicalLogWindowSchwartz (norm_physicalRootKernel_form_le hN)
    (fun r => Real.log ((N : ℝ) + r) / 2) (fun s => Real.log ((N : ℝ) + s) / 2) z c d

private theorem physicalLogWindow_log {x : ℝ} (hx : 0 < x) :
    physicalLogWindow (Real.log x) =
      ((Real.sqrt x * bagPhysicalHeightWindow x : ℝ) : ℂ) := by
  unfold physicalLogWindow
  rw [Real.exp_log hx, ← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]

/-- Exact factorization of the physical degree-two main into its universal phase,
physical scale and actual logarithmic window. -/
theorem physicalChiStationaryMain_two_eq {T a : ℝ} (hT : 0 < T) (ha : 0 < a) :
    physicalChiStationaryMain T a 2 =
      Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) * (Real.sqrt (Real.pi * T) : ℂ) *
        physicalLogWindow (Real.log (a / T)) * Complex.exp (((2 * a : ℝ) : ℂ) * I) := by
  have ha' : a * Real.sqrt (2 * Real.pi / (2 * a)) = Real.sqrt (Real.pi * a) := by
    calc
      _ = Real.sqrt (a ^ 2) * Real.sqrt (2 * Real.pi / (2 * a)) := by rw [Real.sqrt_sq ha.le]
      _ = Real.sqrt (a ^ 2 * (2 * Real.pi / (2 * a))) := (Real.sqrt_mul (sq_nonneg a) _).symm
      _ = _ := by congr 1; field_simp
  have hT' : Real.sqrt (Real.pi * T) * Real.sqrt (a / T) = Real.sqrt (Real.pi * a) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hphase : _root_.RHTower.bourgainOscillation (Real.pi / 4) ^ (2 : ℤ) *
      Complex.exp (I * (((2 * a - Real.pi / 4 : ℝ) : ℂ))) =
      Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) * Complex.exp (((2 * a : ℝ) : ℂ) * I) := by
    simp only [_root_.RHTower.bourgainOscillation, zpow_ofNat, pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [physicalLogWindow_log (div_pos ha hT)]
  unfold physicalChiStationaryMain
  norm_num only [Int.cast_ofNat]
  have haC := congrArg (fun x : ℝ => (x : ℂ)) ha'
  have hTC := congrArg (fun x : ℝ => (x : ℂ)) hT'
  push_cast at haC hTC ⊢
  calc
    _ = (_root_.RHTower.bourgainOscillation (Real.pi / 4) ^ (2 : ℤ) *
        Complex.exp (I * (((2 * a - Real.pi / 4 : ℝ) : ℂ)))) *
        ((a : ℂ) * (Real.sqrt (2 * Real.pi / (2 * a)) : ℂ)) *
        (bagPhysicalHeightWindow (a / T) : ℂ) := by push_cast; ring
    _ = _ := by rw [hphase, haC, ← hTC]; push_cast; ring

private theorem physicalRoot_log_coordinate {T p q : ℝ} (hT : 0 < T)
    (hp : 0 < p) (hq : 0 < q) :
    Real.log (2 * Real.pi * Real.sqrt p * Real.sqrt q / T) =
      Real.log p / 2 + Real.log q / 2 + Real.log (2 * Real.pi / T) := by
  have heq : 2 * Real.pi * Real.sqrt p * Real.sqrt q / T =
      (2 * Real.pi / T) * (Real.sqrt p * Real.sqrt q) := by ring
  rw [heq, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_sqrt hp.le, Real.log_sqrt hq.le]
  ring

/-- Full physical main as an exactly weighted root kernel, with no deleted matrix entries. -/
theorem physicalChiStationaryMain_root_eq {T : ℝ} (hT : 0 < T) {N : ℕ}
    (hN : 1 ≤ N) (r s : ℕ) :
    physicalChiStationaryMain T
      (2 * Real.pi * Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s)) 2 =
      (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) * (Real.sqrt (Real.pi * T) : ℂ)) *
        (physicalRootKernel N r s * physicalLogWindow
          (Real.log ((N : ℝ) + r) / 2 + Real.log ((N : ℝ) + s) / 2 +
            Real.log (2 * Real.pi / T))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr : 0 < (N : ℝ) + r := by positivity
  have hNs : 0 < (N : ℝ) + s := by positivity
  rw [physicalChiStationaryMain_two_eq hT (by positivity), physicalRoot_log_coordinate hT hNr hNs]
  have harg : 2 * (2 * Real.pi * Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s)) =
      4 * Real.pi * Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s) := by ring
  rw [harg]
  unfold physicalRootKernel
  ring

/-- The complete physical degree-two stationary matrix retains root cancellation under the
actual pair-dependent saddle amplitude. All coefficients, including arbitrary zero masks, remain. -/
theorem norm_physicalChiStationaryMain_root_form_le {T : ℝ} (hT : 0 < T) {N : ℕ}
    (hN : 1 ≤ N) (c d : ℕ → ℂ) :
    ‖∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1), c r * d s *
      physicalChiStationaryMain T
        (2 * Real.pi * Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s)) 2‖ ≤
      Real.sqrt (Real.pi * T) * physicalLogWindowFourierBudget *
        Real.sqrt (16 * (N : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ))) *
        Real.sqrt (∑ r ∈ Finset.range (N + 1), ‖c r‖ ^ 2) *
        Real.sqrt (∑ s ∈ Finset.range (N + 1), ‖d s‖ ^ 2) := by
  simp_rw [physicalChiStationaryMain_root_eq hT hN]
  have heq (r s : ℕ) (v : ℂ) : c r * d s *
      (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) * (Real.sqrt (Real.pi * T) : ℂ) * v) =
      (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) * (Real.sqrt (Real.pi * T) : ℂ)) *
        (c r * d s * v) := by ring
  simp_rw [heq, ← Finset.mul_sum]
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hb := norm_physicalLogWindow_root_form_le hN (Real.log (2 * Real.pi / T)) c d
  simp only [mul_assoc] at hb ⊢
  exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

end GaloisForLFunctions.RHTower
