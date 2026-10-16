import GaloisForLFunctions.RHTower.DeningerMeyerHasseFlowCoefficients
import Mathlib.Analysis.Normed.Group.Tannery

/-! # The full original Meyer flow on its faithful Hilbert completion

The scalar diagonal and the bounded Hasse evolution retain every Jordan slot.
Their product extends the literal dilation action on all original source
classes. Strong continuity uses a square-summable envelope, not norm continuity
of the unbounded-frequency diagonal.
-/

noncomputable section
open Complex Set Filter Topology

namespace RHTower

private theorem continuous_varying_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℝ → E →L[ℂ] E) (hA : ∀ x, Continuous (fun t => A t x))
    (b : ℝ → ℝ) (hb : Continuous b) (hbound : ∀ t x, ‖A t x‖ ≤ b t*‖x‖)
    (v : ℝ → E) (hv : Continuous v) : Continuous (fun t => A t (v t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have he0 : Tendsto (fun s => ‖v s-v t‖) (𝓝 t) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using ((hv.tendsto t).sub_const (v t)).norm
  have hd0 : Tendsto (fun s => ‖A s (v t)-A t (v t)‖) (𝓝 t) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using ((hA (v t)).tendsto t |>.sub_const (A t (v t))).norm
  have hz : Tendsto (fun s => b s*‖v s-v t‖ + ‖A s (v t)-A t (v t)‖)
      (𝓝 t) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_add] using ((hb.tendsto t).mul he0).add hd0
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro s
  have hsplit : A s (v s)-A t (v t) = A s (v s-v t)+(A s (v t)-A t (v t)) := by
    rw [map_sub]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (_root_.add_le_add (hbound s _) le_rfl)

private theorem hasse_flow_character_bound (t : ℝ) (q : DeningerArithmeticJetCoordinate) :
    ‖Complex.exp ((t : ℂ)*(q.1 : ℂ))‖ ≤ Real.exp |t| := by
  rw [Complex.norm_exp, Complex.re_ofReal_mul]
  apply Real.exp_le_exp.mpr
  have hr := xi_divisor_support_re_mem_open_unit q.1
  have h := mul_le_mul_of_nonneg_right (le_abs_self t) hr.1.le
  nlinarith [abs_nonneg t]

def deningerHasseDiagonalFlow (t : ℝ) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  xiDivisorDiagonal (fun q => Complex.exp ((t : ℂ)*(q.1 : ℂ)))
    (Real.exp_pos _).le (hasse_flow_character_bound t)

@[simp] theorem deningerHasseDiagonalFlow_apply (t : ℝ) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerHasseDiagonalFlow t x q = Complex.exp ((t : ℂ)*(q.1 : ℂ))*x q := rfl

theorem norm_deningerHasseDiagonalFlow_apply (t : ℝ) (x : DeningerArithmeticJetHilbert) :
    ‖deningerHasseDiagonalFlow t x‖ ≤ Real.exp |t| * ‖x‖ := by
  calc
    _ ≤ ‖(Real.exp |t| : ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num)
      intro q
      change ‖Complex.exp ((t : ℂ)*(q.1 : ℂ))*x q‖ ≤ ‖(Real.exp |t| : ℂ)*x q‖
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (hasse_flow_character_bound t q) (norm_nonneg _)
    _ = _ := by simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

private theorem hasse_tendsto_of_dominated {α : Type*} {l : Filter α}
    {F : α → DeningerArithmeticJetHilbert} {g : DeningerArithmeticJetHilbert}
    {b : DeningerArithmeticJetCoordinate → ℝ}
    (hsum : Summable (fun q => b q^2))
    (hF : ∀ᶠ a in l, ∀ q, ‖F a q‖ ≤ b q) (hg : ∀ q, ‖g q‖ ≤ b q)
    (hpoint : ∀ q, Tendsto (fun a => F a q) l (𝓝 (g q))) : Tendsto F l (𝓝 g) := by
  have hpointSq (q : DeningerArithmeticJetCoordinate) :
      Tendsto (fun a => ‖F a q-g q‖^2) l (𝓝 (0 : ℝ)) := by
    simpa using (((hpoint q).sub_const (g q)).norm.pow 2)
  have hbound : ∀ᶠ a in l, ∀ q, ‖‖F a q-g q‖^2‖ ≤ 4*b q^2 := by
    filter_upwards [hF] with a ha q
    have hb0 := (norm_nonneg (g q)).trans (hg q)
    have hh : ‖F a q-g q‖ ≤ 2*b q := (norm_sub_le _ _).trans (by linarith [ha q,hg q])
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (F a q-g q)]
  have htot := tendsto_tsum_of_dominated_convergence (hsum.mul_left 4) hpointSq hbound
  have heq (a : α) : (∑' q, ‖F a q-g q‖^2) = ‖F a-g‖^2 := by
    symm
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (F a-g)
  have hnorm : Tendsto (fun a => ‖F a-g‖^2) l (𝓝 (0 : ℝ)) := by
    simpa only [heq,tsum_zero] using htot
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hnorm.sqrt

theorem continuous_deningerHasseDiagonalFlow_orbit (x : DeningerArithmeticJetHilbert) :
    Continuous (fun t => deningerHasseDiagonalFlow t x) := by
  rw [continuous_iff_continuousAt]
  intro t
  let C := Real.exp (|t|+1)
  have hs : Summable (fun q : DeningerArithmeticJetCoordinate => ‖x q‖^2) := by
    simpa using Memℓp.summable (by norm_num : 0 < (2 : ENNReal).toReal) (lp.memℓp x)
  apply hasse_tendsto_of_dominated (b := fun q => C*‖x q‖)
  · simpa only [mul_pow] using hs.mul_left (C^2)
  · have he : ∀ᶠ s in 𝓝 t, |s| < |t|+1 :=
      (continuous_abs.tendsto t).eventually (gt_mem_nhds (by linarith))
    filter_upwards [he] with s hs q
    rw [deningerHasseDiagonalFlow_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((hasse_flow_character_bound s q).trans (Real.exp_le_exp.mpr hs.le)) (norm_nonneg _)
  · intro q
    rw [deningerHasseDiagonalFlow_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((hasse_flow_character_bound t q).trans (Real.exp_le_exp.mpr (by linarith)))
      (norm_nonneg _)
  · intro q
    simp only [deningerHasseDiagonalFlow_apply]
    exact (by fun_prop : Continuous (fun s : ℝ => Complex.exp ((s : ℂ)*(q.1 : ℂ))*x q)).tendsto t

/-- The full source flow, without semisimplifying the repeated-zero blocks. -/
def deningerMeyerHilbertFlow (t : ℝ) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  (deningerHasseDiagonalFlow t).comp (deningerHasseShiftEvolution t)

@[simp] theorem deningerMeyerHilbertFlow_apply (t : ℝ) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertFlow t x q = Complex.exp ((t : ℂ)*(q.1 : ℂ))*
      ∑ k ∈ Finset.range (q.2.val+1),
        (t : ℂ)^k/(k.factorial : ℂ)*x (deningerHasseLower q k) := by
  simp only [deningerMeyerHilbertFlow, ContinuousLinearMap.comp_apply,
    deningerHasseDiagonalFlow_apply, deningerHasseShiftEvolution_apply]

theorem deningerMeyerHilbertFlow_source (t : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHilbertFlow t (deningerMeyerHasseHilbertLM u) =
      deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyFlow t u) := by
  apply lp.ext
  funext q
  rw [deningerMeyerHilbertFlow_apply]
  exact (deningerMeyerHasseJet_flow t u q).symm

/-- A continuous local operator budget, independent of all zero multiplicities. -/
def deningerMeyerHilbertFlowBound (t : ℝ) : ℝ :=
  Real.exp |t| * ‖deningerHasseShiftEvolution t‖

theorem continuous_deningerMeyerHilbertFlowBound : Continuous deningerMeyerHilbertFlowBound :=
  (Real.continuous_exp.comp continuous_abs).mul continuous_deningerHasseShiftEvolution.norm

theorem norm_deningerMeyerHilbertFlow_apply (t : ℝ) (x : DeningerArithmeticJetHilbert) :
    ‖deningerMeyerHilbertFlow t x‖ ≤ deningerMeyerHilbertFlowBound t*‖x‖ := by
  change ‖deningerHasseDiagonalFlow t (deningerHasseShiftEvolution t x)‖ ≤
    (Real.exp |t| * ‖deningerHasseShiftEvolution t‖)*‖x‖
  rw [mul_assoc]
  have hb := mul_le_mul_of_nonneg_left ((deningerHasseShiftEvolution t).le_opNorm x)
    (Real.exp_pos |t|).le
  exact (norm_deningerHasseDiagonalFlow_apply t (deningerHasseShiftEvolution t x)).trans hb

theorem continuous_deningerMeyerHilbertFlow_orbit (x : DeningerArithmeticJetHilbert) :
    Continuous (fun t => deningerMeyerHilbertFlow t x) := by
  exact continuous_varying_apply deningerHasseDiagonalFlow continuous_deningerHasseDiagonalFlow_orbit
    (fun t => Real.exp |t|) (Real.continuous_exp.comp continuous_abs)
    norm_deningerHasseDiagonalFlow_apply (fun t => deningerHasseShiftEvolution t x)
    (((ContinuousLinearMap.apply ℂ DeningerArithmeticJetHilbert) x).continuous.comp
      continuous_deningerHasseShiftEvolution)

theorem deningerHasseCLM_ext_source {A B : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert}
    (h : ∀ u, A (deningerMeyerHasseHilbertLM u) = B (deningerMeyerHasseHilbertLM u)) : A = B := by
  apply ContinuousLinearMap.ext
  intro x
  exact (closure_minimal (by rintro y ⟨u, rfl⟩; exact h u)
    (isClosed_eq A.continuous B.continuous)) (deningerMeyerHasseHilbertLM_dense x)

theorem deningerMeyerHilbertFlow_zero : deningerMeyerHilbertFlow 0 = 1 := by
  apply deningerHasseCLM_ext_source
  intro u
  simp only [deningerMeyerHilbertFlow_source, deningerMeyerStrongLogCohomologyFlow_zero,
    one_apply_eq_self]

theorem deningerMeyerHilbertFlow_add (s t : ℝ) :
    deningerMeyerHilbertFlow (s+t) = (deningerMeyerHilbertFlow s).comp (deningerMeyerHilbertFlow t) := by
  apply deningerHasseCLM_ext_source
  intro u
  simp only [ContinuousLinearMap.comp_apply, deningerMeyerHilbertFlow_source,
    deningerMeyerStrongLogCohomologyFlow_add]

end RHTower
