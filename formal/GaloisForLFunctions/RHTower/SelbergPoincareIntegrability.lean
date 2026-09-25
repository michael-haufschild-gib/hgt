import GaloisForLFunctions.RHTower.SelbergPoincareUnfolding
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral

open MeasureTheory UpperHalfPlane ModularGroup Set
open scoped MatrixGroups Pointwise

/-!
# Integrability of the unfolded Poincaré integrand

`y^σ e^{-cy}` (`σ > 1`, `c > 0`) is integrable on the unit strip (chart + Gamma integral) and, being
translation invariant, on the width-`N` strip (`maj_integrableOn_stripN`). Hence the unfolding identity holds
unconditionally for `m ≥ 1`, `Re s > 1` and continuous bounded `Γ(N)`-invariant `g` (`poincare_unfold'`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincareIntegrability

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SelbergPoincareUnfolding

/-- The height majorant `y^σ e^{-cy}`. -/
noncomputable def maj (σ c : ℝ) (z : ℍ) : ℂ := ((z.im ^ σ * Real.exp (-c * z.im) : ℝ) : ℂ)

theorem maj_integrableOn_strip {σ c : ℝ} (hσ : 1 < σ) (hc : 0 < c) :
    IntegrableOn (maj σ c) modularStrip volume := by
  rw [integrableOn_modularStrip_iff]
  have h1 : IntegrableOn (fun y : ℝ => y ^ (σ - 2) * Real.exp (-c * y ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl hc
  have h1' : Integrable (fun y : ℝ => ((y ^ (σ - 2) * Real.exp (-c * y) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := by
    have := h1.ofReal (𝕜 := ℂ)
    refine this.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_))
    simp [Real.rpow_one]
  have h2 : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ico (0 : ℝ) 1)) :=
    integrable_const _
  have hprod := h1'.mul_prod h2
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine hprod.congr ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ico) (fun p hp => ?_)
  have hy : (0 : ℝ) < p.1 := hp.1
  have him : (ofComplex (⟨p.2, p.1⟩ : ℂ)).im = p.1 := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]; rfl
  simp only [stripChartIntegrand, maj, him, mul_one, Complex.real_smul]
  push_cast
  rw [Real.rpow_sub hy, Real.rpow_two]
  push_cast
  field_simp

theorem maj_T_zpow (σ c : ℝ) (j : ℤ) (z : ℍ) : maj σ c (T ^ j • z) = maj σ c z := by
  simp only [maj]
  rw [show (T ^ j • z).im = z.im by
    rw [← UpperHalfPlane.coe_im, modular_T_zpow_smul]; simp]

theorem maj_integrableOn_stripN {σ c : ℝ} (hσ : 1 < σ) (hc : 0 < c) (N : ℕ) :
    IntegrableOn (maj σ c) (stripN N) volume := by
  have hT : ∀ j : ℕ, IntegrableOn (maj σ c) ((T ^ (j : ℤ)) • modularStrip) volume := by
    intro j
    rw [IntegrableOn, ← image_smul, ← ((measurePreserving_smul (T ^ (j : ℤ)) volume).restrict_image_emb
      (measurableEmbedding_const_smul _) modularStrip).integrable_comp_emb
      (measurableEmbedding_const_smul _)]
    have : (maj σ c ∘ fun x => T ^ (j : ℤ) • x) = maj σ c := by
      funext z; exact maj_T_zpow σ c j z
    rw [this]
    exact maj_integrableOn_strip hσ hc
  have hsub : stripN N ⊆ ⋃ j ∈ Finset.range N, (T ^ (j : ℤ)) • modularStrip := by
    intro z hz
    have hz' : 0 ≤ z.re ∧ z.re < N := hz
    set j := ⌊z.re⌋₊
    have hj : j < N := by
      have := Nat.floor_lt hz'.1 |>.mpr hz'.2; exact_mod_cast this
    refine mem_biUnion (Finset.mem_range.mpr hj) ⟨T ^ (-(j : ℤ)) • z, ?_, by simp [smul_smul]⟩
    simp only [modularStrip, mem_setOf_eq, re_T_zpow_smul]
    have h0 := Nat.floor_le hz'.1
    have h1 := Nat.lt_floor_add_one z.re
    push_cast
    constructor <;> linarith
  exact (integrableOn_finset_iUnion.mpr (fun j _ => hT j)).mono_set hsub

/-- A function dominated by `C y^σ e^{-cy}` (`σ > 1`, `c > 0`) is integrable on the strip. -/
theorem integrableOn_stripN_of_le {σ c C : ℝ} (hσ : 1 < σ) (hc : 0 < c) (N : ℕ) {F : ℍ → ℂ}
    (hFm : AEStronglyMeasurable F (volume.restrict (stripN N)))
    (hF : ∀ z, ‖F z‖ ≤ C * (z.im ^ σ * Real.exp (-c * z.im))) :
    IntegrableOn F (stripN N) volume := by
  refine Integrable.mono' ((maj_integrableOn_stripN hσ hc N).norm.const_mul C) hFm
    (Filter.Eventually.of_forall (fun z => ?_))
  refine (hF z).trans (le_of_eq ?_)
  simp only [maj, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

open GaloisForLFunctions.RHTower.SelbergPoincare CongruenceSubgroup GaloisForLFunctions.RHTower.SarnakXuePretrace

theorem term_one (N m : ℕ) (s : ℂ) (z : ℍ) :
    term N m s z 1 = ((z.im : ℂ)) ^ s * Complex.exp (2 * Real.pi * Complex.I * m * (z : ℂ) / N) := by
  simp [term]

theorem norm_term_one (N m : ℕ) (s : ℂ) (z : ℍ) :
    ‖term N m s z 1‖ = z.im ^ s.re * Real.exp (-(2 * Real.pi * m / N) * z.im) := by
  rw [term_one, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos, Complex.norm_exp]
  congr 2
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  · field_simp

theorem continuous_term_one (N m : ℕ) (s : ℂ) : Continuous (fun z : ℍ => term N m s z 1) := by
  simp_rw [term_one]
  refine Continuous.mul ?_ (by fun_prop)
  exact Continuous.cpow (by fun_prop) continuous_const
    (fun z => Complex.ofReal_mem_slitPlane.mpr z.im_pos)

/-- **Unfolding, unconditional form.** For `N ≥ 3`, `m ≥ 1`, `Re s > 1` and a continuous bounded
`Γ(N)`-invariant `g`: `∫_{cellP} P_m(z,s) g(z) dμ = ∫_{strip} y^s e(mz/N) g(z) dμ`. -/
theorem poincare_unfold' (N : ℕ) [NeZero N] (hN : 3 ≤ N) {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 < s.re)
    {g : ℍ → ℂ} (hgc : Continuous g) {B : ℝ} (hgb : ∀ z, ‖g z‖ ≤ B)
    (hg : ∀ (γ : Gamma N) z, g ((γ : SL(2, ℤ)) • z) = g z) :
    ∫ z in cellP N, poincare N m s z * g z = ∫ z in stripN N, term N m s z 1 * g z := by
  apply poincare_unfold N hN m s hg
  have hc : 0 < 2 * Real.pi * m / N := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  apply integrableOn_stripN_of_le hs hc N (C := B)
  · exact ((continuous_term_one N m s).mul hgc).aestronglyMeasurable
  · intro z
    rw [norm_mul, norm_term_one]
    have := hgb z
    have h0 : 0 ≤ z.im ^ s.re * Real.exp (-(2 * Real.pi * m / N) * z.im) := by
      have := Real.rpow_nonneg z.im_pos.le s.re; positivity
    nlinarith [norm_nonneg (g z)]

end GaloisForLFunctions.RHTower.SelbergPoincareIntegrability
