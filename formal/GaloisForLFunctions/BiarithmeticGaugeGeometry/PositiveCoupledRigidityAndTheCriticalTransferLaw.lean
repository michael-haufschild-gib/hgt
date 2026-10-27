import GaloisForLFunctions.BiarithmeticGaugeGeometry.PositivePrimeMassDeformationsAreRigidOffTheCriticalLine
import GaloisForLFunctions.BiarithmeticGaugeGeometry.TheAbelGramLawOfPositiveDeformations
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.HTGeometry.OrderOneEntireQuotient
import GaloisForLFunctions.HTGeometry.EntireLogarithm
import GaloisForLFunctions.HTGeometry.EntireQuotientNormalForm

/-!
# Positive Coupled Rigidity and the Critical Transfer Law

A positive prime-mass deformation of `ζ_γ` inside `HeightCoupledSystem 2 1 1 γ` adds a nonnegative
measure `ν` to the prime side: `−F'/F + ζ_γ'/ζ_γ = 𝓛ν`. Off the critical line such deformations
keep every zero of `Λ_γ`, and they never raise the central order. This module determines what
they can do on the critical line and shows that, at constant central order, they do nothing.

* **Critical transfer law (`abs_criticalTransfer_le_centralDrop`).** If `ξ` has no off-critical zero
  at ordinate `γ`, then at every height `t`
  `|ord_{½+it} Λ_γ − ord_{½+it} Λ| ≤ ord_{½} Λ_γ − ord_{½} Λ`.
  The jump `(σ − ½)(Λ_γ'/Λ_γ − Λ'/Λ)(σ + it) → ord_{½+it} Λ_γ − ord_{½+it} Λ` is the Abel limit
  of `(σ − ½) 𝓛ν(σ + it)`, whose modulus is at most `(σ − ½) 𝓛ν(σ)`. A holomorphic perturbation
  on `Re s > σ_E`, `σ_E < ½`, is allowed.
* **Critical Gram law (`criticalJump_isEvenPosDef`).** The jump function
  `t ↦ ord_{½+it} Λ_γ − ord_{½+it} Λ` is even positive definite: it is the pointwise limit of the
  positive-definite cosine transforms `(σ − ½) ∫ e^{−σu} cos(tu) dν`.
* **Positive rigidity (`positiveDeformation_trivial_of_central_le`).** If moreover the central
  order does not drop, then `ν` vanishes on `(0, ∞)` and `F = K ζ_γ` with `K ∈ ℝ^×`. Every zero of
  `Λ_γ` is kept, so `Λ/Λ_γ` is zero-free of order one, `Λ = K e^{Bs} Λ_γ` (Hadamard), and
  `𝓛ν ≡ −B` forces `ν = 0` on `(0, ∞)`.
* **Classification (`positiveCoupledRigid_iff`).** `ζ_γ` admits no nontrivial positive prime-mass
  deformation iff `ξ` has no zero on the horizontal line `Im s = γ`. Critical zeros are split
  outward by `W_β` (a rational, hence positive, deformation: `isPositiveMassDeformation_of_rational`);
  off-critical zeros are contracted. Rigidity holds unconditionally at `γ = 0` and at every
  ordinate carrying no zero.
* **Chiral dichotomy (`riemannHypothesis_iff_forall_positiveChiral`).** RH holds iff at every
  height every positive deformation is trivial or strictly lowers the central order.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry
  HTGeometry EntireQuotient
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace complexLaplace_ofReal)

/-! ## §1. Rational deformations are positive -/

/-- `W_β(s) = ((s − ½)² + β²)/(s − ½)²` is the rational multiplier with a double pole at `½` and
simple zeros at `½ ± iβ`. -/
theorem criticalSplitMultiplier_eq_rationalMultiplier (β : ℝ) (s : ℂ) :
    criticalSplitMultiplier β s =
      rationalMultiplier ![1 / 2, 1 / 2 + (β : ℂ) * I, 1 / 2 - (β : ℂ) * I] ![-2, 1, 1] s := by
  have hq : (s - (1 / 2 + (β : ℂ) * I)) * (s - (1 / 2 - (β : ℂ) * I)) =
      (s - 1 / 2) ^ 2 + (β : ℂ) ^ 2 := by
    ring_nf; rw [I_sq]; ring
  simp only [rationalMultiplier, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zpow_one, zpow_neg,
    criticalSplitMultiplier]
  rw [mul_assoc, hq, div_eq_inv_mul]
  norm_cast

/-- **Rational deformations are positive.** A rational deformation of `ζ_γ` inside
`HeightCoupledSystem 2 1 1 γ` is a positive prime-mass deformation: by the lattice sieve the
multiplier's `−R'/R` is the Laplace transform of its nonnegative polar scale weight. -/
theorem isPositiveMassDeformation_of_rational {γ : ℝ} {F Λ : ℂ → ℂ}
    (h : IsRationalCoupledDeformation γ F Λ) : IsPositiveMassDeformation γ F Λ := by
  obtain ⟨hHC, n, z, m, hF⟩ := h
  have hHC0 := zeta_mem_heightCoupledSystem γ
  obtain ⟨a, hSa, habs, hpd⟩ := rationalDeformation_lattice_data
    (abscissaOfAbsConv_heightCoupledVonMangoldt_le_one γ) hHC0.diffOn_F hHC0.ne_zero_F
    (fun s hs => neg_logDeriv_heightCoupledF_eq_LSeries γ hs) hHC.posDef_neg_logDeriv hF
  set S := Finset.univ.image z
  set c := multiplierWeight z m
  have hw : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t := fun t ht =>
    polarScaleWeight_nonneg_of_lattice_posDef (heightCoupledVonMangoldt_nonneg γ) hSa habs
      (fun σ hσ => (hpd σ hσ).posDef) ht
  have hσS : ∀ w ∈ S, c w ≠ 0 → w.re ≤ a := fun w hw _ => hSa w hw
  have hsym : ∀ s : ℂ, a < s.re → polarSum S c s = ∑ w ∈ S, (c w : ℂ) / (s - conj w) :=
    fun s hs => polarSum_eq_reflected_of_even hSa hσS (polarSum_re_even_of_lattice_even hpd) hs
  set wd : ℝ → ℝ := polarScaleWeight S c
  have hwc : Continuous wd := by simp only [wd]; unfold polarScaleWeight; fun_prop
  have hreal : ∀ σ : ℝ, a < σ →
      polarSum S c (σ : ℂ) = ((∫ t in Ioi (0 : ℝ), wd t * Real.exp (-σ * t) : ℝ) : ℂ) := by
    intro σ hσ
    have hint := integral_polarScaleWeight_cos_mul_exp hσS hsym hσ 0
    simp only [zero_mul, Real.cos_zero, mul_one, Complex.ofReal_zero, add_zero] at hint
    have him : (polarSum S c (σ : ℂ)).im = 0 := by
      have h1 := conj_polarSum_conj S c (σ : ℂ)
      rw [Complex.conj_ofReal, ← hsym _ (by simpa using hσ)] at h1
      exact Complex.conj_eq_iff_im.mp h1
    apply Complex.ext
    · rw [Complex.ofReal_re, ← hint]
    · rw [him, Complex.ofReal_im]
  have hlap : ∀ σ : ℝ, a < σ → _ := fun σ (hσ : a < σ) =>
    laplace_withDensity hwc hw (integrableOn_polarScaleWeight_mul_exp hσS hσ (fun _ => 1)
      continuous_const (fun _ => by simp) |>.congr_fun (fun t _ => by simp only [mul_one]; rfl)
      measurableSet_Ioi)
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨hHC, _, max a 1 + 1, (hlap _ (by linarith [le_max_left a 1])).1, fun σ hσ => ?_⟩
  have hσa : a < σ := by linarith [le_max_left a 1]
  have hσ1 : 1 < (σ : ℂ).re := by simp only [Complex.ofReal_re]; linarith [le_max_right a 1]
  have hsz : ∀ i, (σ : ℂ) ≠ z i := fun i h => by
    have := hSa (z i) (Finset.mem_image_of_mem z (Finset.mem_univ i))
    rw [← h, Complex.ofReal_re] at this
    linarith
  have hRan := rationalMultiplier_analyticAt z m hsz
  have hRne : rationalMultiplier z m σ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (sub_ne_zero.mpr (hsz i))
  have hζd : DifferentiableAt ℂ (heightCoupledF riemannZeta γ) (σ : ℂ) :=
    (hHC0.diffOn_F _ hσ1).differentiableAt (hU.mem_nhds hσ1)
  have hev : F =ᶠ[𝓝 (σ : ℂ)] fun s => heightCoupledF riemannZeta γ s * rationalMultiplier z m s :=
    Filter.eventually_of_mem (hU.mem_nhds hσ1) fun w hw => hF w hw
  have hlogF : logDeriv F σ =
      logDeriv (fun s => heightCoupledF riemannZeta γ s * rationalMultiplier z m s) σ := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlogF, logDeriv_mul _ (hHC0.ne_zero_F _ hσ1) hRne hζd hRan.differentiableAt,
    (hlap σ hσa).2, ← hreal σ hσa, ← neg_logDeriv_rationalMultiplier z m hsz]
  ring

/-- **Critical zeros admit nontrivial positive deformations.** If `ξ(½ + iγ) = 0`, the outward
splitting `ζ_γ W_β` is a positive prime-mass deformation that is not a multiple of `ζ_γ`. -/
theorem exists_nontrivial_positiveDeformation_of_xi_critical_zero {γ : ℝ}
    (hxi : RHTower.xi (1 / 2 + (γ : ℂ) * I) = 0) :
    ∃ F Λ : ℂ → ℂ, IsPositiveMassDeformation γ F Λ ∧
      ¬ (∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s) := by
  obtain ⟨Λβ, hHC, -, hnot⟩ := exists_criticalSplit_deformation_of_xi_zero hxi one_ne_zero
  refine ⟨_, Λβ, isPositiveMassDeformation_of_rational ⟨hHC, 3,
    ![1 / 2, 1 / 2 + ((1 : ℝ) : ℂ) * I, 1 / 2 - ((1 : ℝ) : ℂ) * I], ![-2, 1, 1],
    fun s _ => ?_⟩, hnot⟩
  show heightCoupledF riemannZeta γ s * criticalSplitMultiplier 1 s = _
  rw [criticalSplitMultiplier_eq_rationalMultiplier]

/-! ## §2. The critical transfer and Gram laws -/

/-- Without off-critical zeros at ordinate `γ`, a perturbed positive deformation satisfies the
Landau–Wronskian relation on `Re z > ½`, with integrable Laplace kernel there. -/
theorem perturbedDeformation_rel_of_offCritical_free {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    (∀ z : ℂ, (1 / 2 : ℝ) < z.re → Λ z ≠ 0 →
      heightCoupledΛ (fun s => 2 * RHTower.xi s) γ z ≠ 0 →
      logDeriv (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) z - logDeriv Λ z =
        complexLaplace ν z + E z) ∧
    (∀ z : ℂ, (1 / 2 : ℝ) < z.re →
      Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨c, -, -, hanchor, hrel, hint⟩ :=
    positiveDeformation_orders_and_anchor_of_perturbation hHC hconv hE hagree
  have hc : c ≤ 1 / 2 := by
    by_contra hgt
    push Not at hgt
    have hz := (hanchor (by linarith) (by linarith)).1
    have := hoff c (xi_add_eq_zero_of_heightCoupledΛ_real_zero hz)
    linarith
  exact ⟨fun z hz => hrel z (lt_of_le_of_lt (max_le hc hσE.le) hz),
    fun z hz => hint z (lt_of_le_of_lt hc hz)⟩

/-- **Abel limits on the critical line.** For a perturbed positive deformation without off-critical
zeros at ordinate `γ`, `(σ − ½) 𝓛ν(σ + it)` tends to the jump
`ord_{½+it} Λ_γ − ord_{½+it} Λ` as `σ ↓ ½`. -/
theorem tendsto_abel_complexLaplace {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) (t : ℝ) :
    Tendsto (fun σ : ℝ => ((σ - 1 / 2 : ℝ) : ℂ) * complexLaplace ν ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ)
          (1 / 2 + (t : ℂ) * I)).toNat : ℂ) -
        (analyticOrderAt Λ (1 / 2 + (t : ℂ) * I)).toNat)) := by
  obtain ⟨hrel, -⟩ := perturbedDeformation_rel_of_offCritical_free hoff hHC hconv hσE hE hagree
  have hHC0 := zeta_mem_heightCoupledSystem γ
  have h := tendsto_abel_of_rel hHC.entire_Λ hHC0.entire_Λ hHC.orderAt_ne_top hHC0.orderAt_ne_top
    hrel (tendsto_sub_mul_of_differentiableOn hσE hE) t
  rwa [show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by norm_num] at h

/-- **Critical transfer law.** If `ξ` has no off-critical zero at ordinate `γ`, a perturbed positive
deformation moves at most as many zeros at any critical height as it removes from the centre:
`|ord_{½+it} Λ_γ − ord_{½+it} Λ| ≤ ord_{½} Λ_γ − ord_{½} Λ`. -/
theorem abs_criticalTransfer_le_centralDrop {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) (t : ℝ) :
    |((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ)
          (1 / 2 + (t : ℂ) * I)).toNat : ℝ) - (analyticOrderAt Λ (1 / 2 + (t : ℂ) * I)).toNat| ≤
      ((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat : ℝ) -
        (analyticOrderAt Λ (1 / 2)).toNat := by
  obtain ⟨hrel, -⟩ := perturbedDeformation_rel_of_offCritical_free hoff hHC hconv hσE hE hagree
  have hHC0 := zeta_mem_heightCoupledSystem γ
  have h := abs_jump_le_of_rel hHC.entire_Λ hHC0.entire_Λ hHC.orderAt_ne_top hHC0.orderAt_ne_top
    hrel (tendsto_sub_mul_of_differentiableOn hσE hE) t
  rwa [show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by norm_num] at h

/-- **Critical Gram law.** If `ξ` has no off-critical zero at ordinate `γ`, the critical jump
`t ↦ ord_{½+it} Λ_γ − ord_{½+it} Λ` of a perturbed positive deformation is even positive definite;
its value at `0` is the central drop. -/
theorem criticalJump_isEvenPosDef {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    IsEvenPosDef fun t : ℝ =>
      ((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ)
          (1 / 2 + (t : ℂ) * I)).toNat : ℝ) - (analyticOrderAt Λ (1 / 2 + (t : ℂ) * I)).toNat := by
  obtain ⟨hrel, hint⟩ :=
    perturbedDeformation_rel_of_offCritical_free hoff hHC hconv hσE hE hagree
  have hHC0 := zeta_mem_heightCoupledSystem γ
  have h := jump_isEvenPosDef_of_rel hHC.entire_Λ hHC0.entire_Λ hHC.orderAt_ne_top
    hHC0.orderAt_ne_top hrel (tendsto_sub_mul_of_differentiableOn hσE hE) hint
  simp only [show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by norm_num] at h
  exact h

/-! ## §3. Divisor rigidity and positive rigidity -/



/-- Two order-one entire functions with the same divisor, the second with finite orders, differ by
`K e^{Bs}`, `K ≠ 0`. -/
theorem exists_eq_const_mul_exp_mul_of_orders_eq {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfo : OrderOneEnvelope f) (hgo : OrderOneEnvelope g)
    (hgtop : ∀ z, analyticOrderAt g z ≠ ⊤)
    (hord : ∀ z, analyticOrderAt f z = analyticOrderAt g z) :
    ∃ K B : ℂ, K ≠ 0 ∧ ∀ z, f z = K * Complex.exp (B * z) * g z := by
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  have hftop : ∀ z, analyticOrderAt f z ≠ ⊤ := fun z => by rw [hord z]; exact hgtop z
  have hne : ∀ {h : ℂ → ℂ}, (∀ z, analyticOrderAt h z ≠ ⊤) → ∃ z, h z ≠ 0 := by
    intro h htop
    by_contra hall
    push Not at hall
    exact htop 0 (analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall hall))
  obtain ⟨z₀, hz₀⟩ := hne hgtop
  have hQa := entireQuotient_analytic hfa hga hftop hord
  have hQne := entireQuotient_ne_zero hfa hga hftop hord
  have hfac : ∀ z, f z = entireQuotient f g z * g z := fun z =>
    (congrFun (entireQuotient_mul hfa hga hftop hord hz₀) z).symm
  have hQo : OrderOneEnvelope (entireQuotient f g) :=
    OrderOneEnvelope.of_entire_quotient hga hfa hQa ⟨z₀, hz₀⟩ (hne hftop) hQne hfac hgo hfo
  obtain ⟨C, hC, hCb⟩ := hQo.subquadratic
  obtain ⟨B, hB⟩ := exists_linear_of_ne_zero_of_growth (fun z => (hQa z (mem_univ z)).differentiableAt)
    hQne (by norm_num) (by norm_num) hC hCb
  exact ⟨entireQuotient f g 0, B, hQne 0, fun z => by rw [hfac z, hB z]⟩

/-- An entire function nonvanishing at one point has finite order everywhere. -/
theorem analyticOrderAt_ne_top_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hz₀ : f z₀ ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  have hfa : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
  exact hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₀)
    (mem_univ z) (by rw [(hf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hz₀]; exact ENat.zero_ne_top)

/-- **Divisor rigidity for symmetric real functions of order one.** Two entire functions of order
one, symmetric under `s ↦ 1 − s` and real, with the same divisor, the second nonvanishing on
`Re s > 1`, are proportional by a nonzero real constant: the zero-free quotient is `K e^{Bs}`, the
symmetry kills `B`, and the reality makes `K` real. -/
theorem eq_real_const_mul_of_orders_eq {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hΛ₀ : Differentiable ℂ Λ₀) (hΛo : OrderOneEnvelope Λ) (hΛ₀o : OrderOneEnvelope Λ₀)
    (hsym : ∀ s, Λ (1 - s) = Λ s) (hsym₀ : ∀ s, Λ₀ (1 - s) = Λ₀ s)
    (hconj : ∀ s, Λ (starRingEnd ℂ s) = starRingEnd ℂ (Λ s))
    (hconj₀ : ∀ s, Λ₀ (starRingEnd ℂ s) = starRingEnd ℂ (Λ₀ s))
    (hne₀ : ∀ s : ℂ, 1 < s.re → Λ₀ s ≠ 0)
    (hord : ∀ w : ℂ, analyticOrderAt Λ w = analyticOrderAt Λ₀ w) :
    ∃ K : ℝ, K ≠ 0 ∧ ∀ s, Λ s = K * Λ₀ s := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  obtain ⟨Q, B, hQ, hfac⟩ := exists_eq_const_mul_exp_mul_of_orders_eq hΛ hΛ₀ hΛo hΛ₀o
    (analyticOrderAt_ne_top_of_ne_zero hΛ₀ (hne₀ 2 h2)) hord
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  -- symmetry: `e^{B(1 − 2s)} = 1` on `Re s > 1`, so `B = 0`
  have hone : ∀ s : ℂ, 1 < s.re → Complex.exp (B * (1 - 2 * s)) = 1 := by
    intro s hs
    have h1 := hfac (1 - s)
    rw [hsym s, hsym₀ s, hfac s] at h1
    have h2' : Complex.exp (B * s) = Complex.exp (B * (1 - s)) :=
      mul_left_cancel₀ hQ (mul_right_cancel₀ (hne₀ s hs) h1)
    rw [show B * (1 - 2 * s) = B * (1 - s) - B * s by ring, Complex.exp_sub, ← h2',
      div_self (Complex.exp_ne_zero _)]
  have hB : B = 0 := by
    have hlin : HasDerivAt (fun s : ℂ => B * (1 - 2 * s)) (B * (-2)) 2 := by
      have h := (((hasDerivAt_id (2 : ℂ)).const_mul 2).const_sub 1).const_mul B
      simp only [id, mul_one] at h
      convert h using 1
    have hc : HasDerivAt (fun s : ℂ => Complex.exp (B * (1 - 2 * s))) 0 2 :=
      (hasDerivAt_const (2 : ℂ) (1 : ℂ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hU.mem_nhds h2) fun s hs => hone s hs)
    have h := hlin.cexp.unique hc
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · norm_num at h
  have hfac0 : ∀ s, Λ s = Q * Λ₀ s := fun s => by
    rw [hfac s, hB, zero_mul, Complex.exp_zero, mul_one]
  -- reality at the real point `2` makes `Q` real
  have hQreal : starRingEnd ℂ Q = Q := by
    have hc2 : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
    have hΛr : starRingEnd ℂ (Λ 2) = Λ 2 := by rw [← hconj, hc2]
    have hΛ₀r : starRingEnd ℂ (Λ₀ 2) = Λ₀ 2 := by rw [← hconj₀, hc2]
    have h3 := congrArg (starRingEnd ℂ) (hfac0 2)
    rw [map_mul, hΛr, hΛ₀r, hfac0 2] at h3
    exact (mul_right_cancel₀ (hne₀ 2 h2) h3).symm
  have hQK : Q = ((Q.re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp hQreal).symm
  exact ⟨Q.re, fun h => hQ (by rw [hQK, h, Complex.ofReal_zero]), fun s => by
    rw [hfac0 s, ← hQK]⟩

/-- `Λ_γ` does not vanish on `Re s > 1`. -/
theorem heightCoupledΛ_ne_zero_of_one_lt_re (γ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    heightCoupledΛ (fun s => 2 * RHTower.xi s) γ s ≠ 0 := by
  have h : ∀ w : ℂ, 1 < w.re → (2 : ℂ) * RHTower.xi w ≠ 0 := fun w hw =>
    mul_ne_zero two_ne_zero (RHTower.xi_ne_zero_of_one_lt_re hw)
  simp only [heightCoupledΛ]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (h s hs)) (h _ (by simpa using hs)))
    (h _ (by simpa using hs))

/-- A nonnegative measure whose real Laplace transform takes the same value at two points of
convergence carries no mass on `(0, ∞)`. -/
theorem measure_Ioi_eq_zero_of_laplaceReal_eq {ν : Measure ℝ} {σ₂ σ₃ : ℝ} (h23 : σ₂ < σ₃)
    (hi2 : Integrable (fun u : ℝ => Real.exp (-σ₂ * u)) (ν.restrict (Ioi (0 : ℝ))))
    (hi3 : Integrable (fun u : ℝ => Real.exp (-σ₃ * u)) (ν.restrict (Ioi (0 : ℝ))))
    (heq : laplaceReal ν σ₂ = laplaceReal ν σ₃) : ν (Ioi 0) = 0 := by
  have hsub : ∫ u in Ioi (0 : ℝ), (Real.exp (-σ₂ * u) - Real.exp (-σ₃ * u)) ∂ν = 0 := by
    rw [integral_sub hi2 hi3]
    unfold laplaceReal at heq
    linarith
  have hnn : 0 ≤ᵐ[ν.restrict (Ioi (0 : ℝ))] fun u => Real.exp (-σ₂ * u) - Real.exp (-σ₃ * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : (0 : ℝ) < u := hu
    have : -σ₃ * u ≤ -σ₂ * u := by nlinarith
    simp only [Pi.zero_apply, sub_nonneg]
    exact Real.exp_le_exp.mpr this
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn (hi2.sub hi3)).mp hsub
  have hfalse : ∀ᵐ u ∂(ν.restrict (Ioi (0 : ℝ))), False := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with u hu hmem
    have hu' : (0 : ℝ) < u := hmem
    have h1 : -σ₃ * u < -σ₂ * u := by nlinarith
    have h2 := Real.exp_lt_exp.mpr h1
    simp only [Pi.zero_apply] at hu
    linarith
  have h0 := ae_iff.mp hfalse
  simp only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply_univ] at h0
  exact h0

/-- Without off-critical zeros at `γ`, a perturbed positive deformation that does not lower the
central order has exactly the divisor of `Λ_γ`: off the line by off-line rigidity, on it by the
critical transfer law. -/
theorem perturbedDeformation_orders_eq_of_central_le {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ)
    (hcent : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat ≤
      (analyticOrderAt Λ (1 / 2)).toNat) :
    ∀ w : ℂ, analyticOrderAt Λ w =
      analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  obtain ⟨hoffl, hcen⟩ := perturbedDeformation_offLine_rigid hoff hHC hconv hσE hE hagree
  have hordnat : ∀ w : ℂ, (analyticOrderAt Λ w).toNat =
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w).toNat := by
    intro w
    by_cases hw : w.re = 1 / 2
    · have hwe : w = 1 / 2 + (w.im : ℂ) * I := Complex.ext (by simp [hw]) (by simp)
      have h := abs_criticalTransfer_le_centralDrop hoff hHC hconv hσE hE hagree w.im
      rw [← hwe] at h
      have hc : ((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ)
          (1 / 2)).toNat : ℝ) = (analyticOrderAt Λ (1 / 2)).toNat := by
        exact_mod_cast le_antisymm hcent hcen
      rw [hc, sub_self] at h
      have := abs_nonpos_iff.mp h
      exact_mod_cast (sub_eq_zero.mp this).symm
    · rw [hoffl w hw]
  intro w
  rw [← ENat.coe_toNat (hHC.orderAt_ne_top w), ← ENat.coe_toNat (hHC0.orderAt_ne_top w),
    hordnat w]

/-- **Divisor rigidity of the coupled class.** A member of `HeightCoupledSystem 2 1 1 γ` whose
completion has the divisor of `Λ_γ` is a nonzero real multiple of `ζ_γ`: the zero-free order-one
quotient is `K e^{Bs}`, symmetry under `s ↦ 1 − s` kills `B`, and conjugation symmetry makes `K`
real (`eq_real_const_mul_of_orders_eq`). -/
theorem eq_const_mul_of_orders_eq {γ : ℝ} {F Λ : ℂ → ℂ} (hHC : HeightCoupledSystem 2 1 1 γ F Λ)
    (hord : ∀ w : ℂ, analyticOrderAt Λ w =
      analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w) :
    ∃ K : ℝ, K ≠ 0 ∧ (∀ s, Λ s = K * heightCoupledΛ (fun s => 2 * RHTower.xi s) γ s) ∧
      ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ with hΛγ
  obtain ⟨K, hK0, hK⟩ := eq_real_const_mul_of_orders_eq hHC.entire_Λ hHC0.entire_Λ
    hHC.orderOne_Λ hHC0.orderOne_Λ hHC.sym_Λ hHC0.sym_Λ hHC.conj_Λ hHC0.conj_Λ
    (fun s hs => heightCoupledΛ_ne_zero_of_one_lt_re γ hs) hord
  refine ⟨K, hK0, hK, fun s hs => ?_⟩
  -- cancel the common archimedean factor on `Re s > 1`
  have hP : (s * (s - 1)) ^ 2 * shiftedPolePoly γ s ^ 1 * coupledGamma γ 1 s ≠ 0 := by
    intro h
    apply heightCoupledΛ_ne_zero_of_one_lt_re γ hs
    rw [← hΛγ, hHC0.completed_eq s hs, h, zero_mul]
  refine mul_left_cancel₀ hP ?_
  rw [← hHC.completed_eq s hs, hK s, hHC0.completed_eq s hs]
  ring

/-- **Positive rigidity.** If `ξ` has no off-critical zero at ordinate `γ` and a positive
prime-mass deformation `(F, Λ)` of `ζ_γ` does not lower the central vanishing order, then `ν`
carries no mass on `(0, ∞)` and `F = K ζ_γ`, `Λ = K Λ_γ` for a real `K ≠ 0`. -/
theorem positiveDeformation_trivial_of_central_le {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤)
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ))
    (hcent : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat ≤
      (analyticOrderAt Λ (1 / 2)).toNat) :
    ν (Ioi 0) = 0 ∧ ∃ K : ℝ, K ≠ 0 ∧
      (∀ s, Λ s = K * heightCoupledΛ (fun s => 2 * RHTower.xi s) γ s) ∧
      ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  have hagreeE : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + (fun _ => (0 : ℂ)) σ := fun σ hσ => by
    rw [hagree σ hσ, add_zero]
  have hE0 : DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) {s : ℂ | (0 : ℝ) < s.re} :=
    differentiableOn_const 0
  obtain ⟨K, hK0, hΛK, hFK⟩ := eq_const_mul_of_orders_eq hHC
    (perturbedDeformation_orders_eq_of_central_le hoff hHC hconv (by norm_num) hE0 hagreeE hcent)
  refine ⟨?_, K, hK0, hΛK, hFK⟩
  obtain ⟨c, -, -, -, -, hint⟩ :=
    positiveDeformation_orders_and_anchor_of_perturbation hHC hconv hE0 hagreeE
  -- `𝓛ν = 0` right of all abscissae, since `F'/F = ζ_γ'/ζ_γ` there
  set M : ℝ := max σ₁ (max c 1) with hM
  have hlap0 : ∀ σ : ℝ, M < σ → laplaceReal ν σ = 0 := by
    intro σ hσ
    have hσ₁ : σ₁ < σ := lt_of_le_of_lt (le_max_left _ _) hσ
    have hσ1 : 1 < (σ : ℂ).re := by
      simp only [Complex.ofReal_re]
      exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hσ
    have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : F =ᶠ[𝓝 (σ : ℂ)] fun s => (K : ℂ) * heightCoupledF riemannZeta γ s :=
      Filter.eventually_of_mem (hU.mem_nhds hσ1) fun w hw => hFK w hw
    have hlog : logDeriv F σ = logDeriv (heightCoupledF riemannZeta γ) σ := by
      rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, ← logDeriv_apply,
        logDeriv_const_mul _ _ (by exact_mod_cast hK0)]
    have h := hagree σ hσ₁
    rw [hlog, neg_add_cancel] at h
    exact_mod_cast h.symm
  have hIσ : ∀ σ : ℝ, M < σ →
      Integrable (fun u : ℝ => Real.exp (-σ * u)) (ν.restrict (Ioi (0 : ℝ))) := by
    intro σ hσ
    have hcσ : c < (σ : ℂ).re := by
      simp only [Complex.ofReal_re]
      exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hσ
    refine (hint (σ : ℂ) hcσ).norm.congr (ae_of_all _ fun u => ?_)
    dsimp only
    rw [Complex.norm_exp]
    congr 1
    simp
  exact measure_Ioi_eq_zero_of_laplaceReal_eq (by linarith : M + 1 < M + 2)
    (hIσ _ (by linarith)) (hIσ _ (by linarith))
    ((hlap0 _ (by linarith)).trans (hlap0 _ (by linarith)).symm)

/-! ## §4. Classification -/

/-- **Positive coupled rigidity at `γ`**: every positive prime-mass deformation of `ζ_γ` is a
nonzero real multiple of `ζ_γ` on `Re s > 1`. -/
def PositiveCoupledRigid (γ : ℝ) : Prop :=
  ∀ F Λ : ℂ → ℂ, IsPositiveMassDeformation γ F Λ →
    ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s

/-- **Positive chirality at `γ`**: every positive prime-mass deformation of `ζ_γ` is trivial or
strictly lowers the central vanishing order. -/
def PositiveChiral (γ : ℝ) : Prop :=
  ∀ F Λ : ℂ → ℂ, IsPositiveMassDeformation γ F Λ →
    (∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s) ∨
      (analyticOrderAt Λ (1 / 2)).toNat <
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat

/-- A member proportional to `ζ_γ` on `Re s > 1` has the central order of `Λ_γ`. -/
theorem centralOrder_eq_of_eq_const_mul {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {K : ℝ} (hK0 : K ≠ 0)
    (hK : ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s) :
    analyticOrderAt Λ (1 / 2) =
      analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2) := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ
  have hagree : ∀ s : ℂ, 1 < s.re → Λ s = (K : ℂ) * Λγ s := by
    intro s hs
    rw [hHC.completed_eq s hs, hHC0.completed_eq s hs, hK s hs]
    ring
  have heq : EqOn Λ (fun s => (K : ℂ) * Λγ s) univ := by
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact hHC.analyticOnNhd_univ.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const.mul hHC0.analyticOnNhd_univ)
      isPreconnected_univ (mem_univ (2 : ℂ))
      (Filter.eventually_of_mem (hU.mem_nhds (by norm_num)) fun s hs => hagree s hs)
  have hfun : Λ = fun s => (K : ℂ) * Λγ s := funext fun s => heq (mem_univ s)
  have hconst : analyticOrderAt (fun _ : ℂ => (K : ℂ)) (1 / 2 : ℂ) = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by exact_mod_cast hK0)
  rw [hfun, show (fun s => (K : ℂ) * Λγ s) = (fun _ : ℂ => (K : ℂ)) * Λγ from rfl,
    analyticOrderAt_mul analyticAt_const (hHC0.entire_Λ.analyticAt _), hconst, zero_add]

/-- An off-critical zero of `ξ` at ordinate `γ` gives a quartet point `½ + a + iγ`,
`0 < a < ½`. -/
theorem exists_quartet_point_of_offCritical_zero {γ x : ℝ}
    (hx : RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0) (hne : x ≠ 1 / 2) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧ RHTower.xi (1 / 2 + a + γ * I) = 0 := by
  have hpos := RHTower.xi_zero_re_pos hx
  have hlt := RHTower.xi_zero_re_lt_one hx
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero] at hpos hlt
  rcases lt_or_gt_of_ne hne with hx' | hx'
  · have h1 : RHTower.xi (1 - ((x : ℂ) + (γ : ℂ) * I)) = 0 := by
      rw [RHTower.xi_one_sub]; exact hx
    have hc : (1 / 2 : ℂ) + ((1 / 2 - x : ℝ) : ℂ) + (γ : ℂ) * I =
        conj (1 - ((x : ℂ) + (γ : ℂ) * I)) := Complex.ext (by simp; ring) (by simp)
    refine ⟨1 / 2 - x, by linarith, by linarith, ?_⟩
    rw [hc]
    have h2 : 2 * RHTower.xi (conj (1 - ((x : ℂ) + (γ : ℂ) * I))) = 0 := by
      rw [completedPositiveSystem_riemannZeta.conj_Λ]; simp [h1]
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  · refine ⟨x - 1 / 2, by linarith, by linarith, ?_⟩
    rw [show (1 / 2 : ℂ) + ((x - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I = (x : ℂ) + (γ : ℂ) * I by
      push_cast; ring]
    exact hx

/-- **Classification of positive rigidity.** `ζ_γ` admits no nontrivial positive prime-mass
deformation iff `ξ` has no zero on the horizontal line `Im s = γ`. -/
theorem positiveCoupledRigid_iff (γ : ℝ) :
    PositiveCoupledRigid γ ↔ ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) ≠ 0 := by
  constructor
  · intro hrig x hx
    by_cases hx2 : x = 1 / 2
    · subst hx2
      obtain ⟨F, Λ, hdef, hnot⟩ := exists_nontrivial_positiveDeformation_of_xi_critical_zero
        (γ := γ) (by simpa using hx)
      exact hnot (hrig F Λ hdef)
    · have hγ : γ ≠ 0 := by
        rintro rfl
        exact RHTower.xi_ne_zero_of_real x (by simpa using hx)
      obtain ⟨a, ha0, ha1, hxa⟩ := exists_quartet_point_of_offCritical_zero hx hx2
      obtain ⟨F, Λ, hdef, hord⟩ := exists_positiveDeformation_above_ceiling hγ ha0 ha1 hxa
      obtain ⟨K, hK0, hK⟩ := hrig F Λ hdef
      rw [centralOrder_eq_of_eq_const_mul hdef.1 hK0 hK] at hord
      omega
  · intro hfree F Λ ⟨hHC, ν, σ₁, hconv, hagree⟩
    have hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2 :=
      fun x hx => absurd hx (hfree x)
    have hc0 : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat = 0 := by
      have hne : heightCoupledΛ (fun s => 2 * RHTower.xi s) γ ((1 / 2 : ℝ) : ℂ) ≠ 0 := fun h =>
        hfree _ (xi_add_eq_zero_of_heightCoupledΛ_real_zero h)
      have hhalf : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
      rw [hhalf] at hne
      rw [((zeta_mem_heightCoupledSystem γ).entire_Λ.analyticAt _).analyticOrderAt_eq_zero.mpr hne]
      rfl
    obtain ⟨-, K, hK0, -, hK⟩ :=
      positiveDeformation_trivial_of_central_le hoff hHC hconv hagree (by rw [hc0]; exact Nat.zero_le _)
    exact ⟨K, hK0, hK⟩

/-- Positive rigidity holds unconditionally at height `0`. -/
theorem positiveCoupledRigid_zero : PositiveCoupledRigid 0 :=
  (positiveCoupledRigid_iff 0).mpr fun x => by simpa using RHTower.xi_ne_zero_of_real x

/-- Positive rigidity fails at infinitely many heights (every critical ordinate). -/
theorem exists_gt_not_positiveCoupledRigid (T : ℝ) :
    ∃ γ : ℝ, T < γ ∧ ¬ PositiveCoupledRigid γ := by
  obtain ⟨γ, hγ_gt, h2xi⟩ :=
    completedPositiveSystem_one_critical_zeros completedPositiveSystem_riemannZeta (max T 0)
  have hxi : RHTower.xi (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) = 0 := by
    rcases mul_eq_zero.mp h2xi with h2 | hz
    · norm_num at h2
    · simpa using hz
  exact ⟨γ, lt_of_le_of_lt (le_max_left T 0) hγ_gt,
    fun h => (positiveCoupledRigid_iff γ).mp h _ hxi⟩

/-- **Positive chirality is the horizontal off-critical-free line.** -/
theorem positiveChiral_iff (γ : ℝ) :
    PositiveChiral γ ↔ ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2 := by
  constructor
  · intro hch x hx
    by_contra hx2
    have hγ : γ ≠ 0 := by
      rintro rfl
      exact RHTower.xi_ne_zero_of_real x (by simpa using hx)
    obtain ⟨a, ha0, ha1, hxa⟩ := exists_quartet_point_of_offCritical_zero hx hx2
    obtain ⟨F, Λ, hdef, hord⟩ := exists_positiveDeformation_above_ceiling hγ ha0 ha1 hxa
    rcases hch F Λ hdef with ⟨K, hK0, hK⟩ | hlt
    · rw [centralOrder_eq_of_eq_const_mul hdef.1 hK0 hK] at hord
      omega
    · omega
  · intro hoff F Λ ⟨hHC, ν, σ₁, hconv, hagree⟩
    rcases lt_or_ge (analyticOrderAt Λ (1 / 2)).toNat
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat with
      hlt | hge
    · exact Or.inr hlt
    · obtain ⟨-, K, hK0, -, hK⟩ := positiveDeformation_trivial_of_central_le hoff hHC hconv hagree hge
      exact Or.inl ⟨K, hK0, hK⟩

/-- **RH is positive chirality at every height.** -/
theorem riemannHypothesis_iff_forall_positiveChiral :
    RiemannHypothesis ↔ ∀ γ : ℝ, PositiveChiral γ := by
  rw [riemannHypothesis_iff_forall_positiveCentralVanishingCeiling]
  constructor
  · intro h γ
    rw [positiveChiral_iff]
    intro x hx
    by_contra hx2
    have hγ : γ ≠ 0 := by
      rintro rfl
      exact RHTower.xi_ne_zero_of_real x (by simpa using hx)
    obtain ⟨a, ha0, ha1, hxa⟩ := exists_quartet_point_of_offCritical_zero hx hx2
    exact (positiveCentralVanishingCeiling_iff hγ).mp (h γ hγ) a ha0 ha1 hxa
  · intro h γ _
    exact positiveCentralVanishingCeiling_of_offCritical_free ((positiveChiral_iff γ).mp (h γ))

end GaloisForLFunctions.BiarithmeticGaugeGeometry
