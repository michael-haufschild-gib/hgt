import GaloisForLFunctions.SelbergClass.DegreeOne.DirichletEulerLog
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne
import GaloisForLFunctions.RHTower.DirichletCompletedLConjugate
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62RootNumberNorm
import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import GaloisForLFunctions.RHTower.DirichletLStripBounds
import GaloisForLFunctions.RHTower.SelbergClass.Full
import GaloisForLFunctions.HTGeometry.OrderOneEnvelopeRootDivision
import GaloisForLFunctions.RHTower.Reflection

/-!
# Shifted primitive Dirichlet L-functions are Selberg-class elements

For a primitive character `χ` modulo `N` and real `θ`, with `θ = 0` when `N = 1`, the function
`L(s + iθ, χ)` is an element of the Selberg class of degree one, conductor `N` and internal shift `θ`
(`exists_selberg_dirichlet`).  Its Gamma presentation is

`(N/π)^{s/2} Γ((s + iθ + d)/2)`,   `d ∈ {0, 1}` the parity of `χ`,

and its root number is the root number of `χ` times `(N/π)^{−iθ}`.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-! ### Growth -/

theorem growth_of_orderOneEnvelope {f : ℂ → ℂ} (hf : OrderOneEnvelope f) :
    ∃ A B ρ : ℝ, 0 < A ∧ 0 < B ∧ 0 ≤ ρ ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := by
  obtain ⟨C, hC, hbound⟩ := hf
  refine ⟨Real.exp (2 * C), 2 * C, 2, Real.exp_pos _, by positivity, by norm_num, fun z => ?_⟩
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + ‖z‖)
  have hmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg hC.le (by positivity : (0 : ℝ) ≤ 1 + ‖z‖))
  have hexp : orderOneWeight C z ≤ 2 * C + 2 * C * ‖z‖ ^ 2 := by
    unfold orderOneWeight
    nlinarith only [hmul, mul_nonneg hC.le (sq_nonneg (1 - ‖z‖))]
  rw [Real.rpow_two]
  calc ‖f z‖ ≤ Real.exp (orderOneWeight C z) := hbound z
    _ ≤ Real.exp (2 * C + 2 * C * ‖z‖ ^ 2) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (2 * C) * Real.exp (2 * C * ‖z‖ ^ 2) := Real.exp_add _ _

/-- `1/Γ_ℝ` is of order one. -/
theorem orderOneEnvelope_inv_Gammaℝ : OrderOneEnvelope (fun x : ℂ => (Gammaℝ x)⁻¹) := by
  have hpow : OrderOneEnvelope (fun x : ℂ => (π : ℂ) ^ (x / 2)) := by
    refine (orderOneEnvelope_exp_mul (Complex.log (π : ℂ) / 2)).congr fun s => ?_
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    congr 1
    ring
  have hrec : OrderOneEnvelope (fun x : ℂ => GaloisForLFunctions.reciprocalGammaEntire (x / 2)) :=
    (RHTower.orderOneEnvelope_reciprocalGammaEntire.comp_affine (1 / 2) 0).congr
      fun s => by
        congr 1
        ring
  refine (hpow.mul hrec).congr fun x => ?_
  rw [Complex.Gammaℝ_def, mul_inv, GaloisForLFunctions.reciprocalGammaEntire]
  congr 1
  rw [neg_div, Complex.cpow_neg, inv_inv]

theorem orderOneEnvelope_LFunction {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hN : N ≠ 1) : OrderOneEnvelope (DirichletCharacter.LFunction χ) := by
  obtain ⟨d, _, hd⟩ := gammaFactor_eq_Gammaℝ χ
  refine ((completedLFunction_orderOneEnvelope hχ).mul
    (orderOneEnvelope_inv_Gammaℝ.comp_affine 1 (d : ℂ))).congr fun s => ?_
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN), hd, one_mul,
    div_eq_mul_inv]

/-- `(s − 1)ζ(s)` is of order one. -/
theorem orderOneEnvelope_zetaPoleUnit : OrderOneEnvelope RHTower.zetaPoleUnit := by
  let Z : ℂ → ℂ := fun s => RHTower.riemannXi s * (π : ℂ) ^ (s / 2) *
    GaloisForLFunctions.reciprocalGammaEntire (s / 2 + 1)
  have hZd : Differentiable ℂ Z := by
    have hpow : Differentiable ℂ (fun s : ℂ => (π : ℂ) ^ (s / 2)) :=
      (differentiable_id.div_const 2).const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hrec : Differentiable ℂ (fun s : ℂ =>
        GaloisForLFunctions.reciprocalGammaEntire (s / 2 + 1)) :=
      Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const 2).add_const 1)
    exact (RHTower.differentiable_riemannXi.mul hpow).mul hrec
  have hZeq : ∀ {s : ℂ}, s ≠ 1 → Z s = (s - 1) * riemannZeta s := by
    intro s hs
    have hnum : (s - 1) * (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) =
        2 * RHTower.riemannXi s := by
      rw [RHTower.riemannXi]
      field_simp [sub_ne_zero.mpr hs.symm]
      ring
    have hpi : (π : ℂ) ^ (-s / 2) = ((π : ℂ) ^ (s / 2))⁻¹ := by
      rw [neg_div, Complex.cpow_neg]
    rw [riemannZeta_eq_mul_completedRiemannZeta₀, ← mul_div_assoc, hnum, hpi]
    simp only [Z, GaloisForLFunctions.reciprocalGammaEntire, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hZP : Z = RHTower.zetaPoleUnit := by
    have hZ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hZd
    have hP := Complex.analyticOnNhd_univ_iff_differentiable.mpr RHTower.differentiable_zetaPoleUnit
    apply hZ.eq_of_eventuallyEq hP (z₀ := (2 : ℂ))
    filter_upwards [isOpen_compl_singleton.mem_nhds (by norm_num : (2 : ℂ) ≠ 1)] with s hs
    exact (hZeq hs).trans (RHTower.zetaPoleUnit_of_ne hs).symm
  have hpow : OrderOneEnvelope (fun s : ℂ => (π : ℂ) ^ (s / 2)) := by
    refine (orderOneEnvelope_exp_mul (Complex.log (π : ℂ) / 2)).congr fun s => ?_
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    congr 1
    ring
  have hrec : OrderOneEnvelope (fun s : ℂ => GaloisForLFunctions.reciprocalGammaEntire (s / 2 + 1)) :=
    (RHTower.orderOneEnvelope_reciprocalGammaEntire.comp_affine (1 / 2) 1).congr
      fun s => by rw [one_div_mul_eq_div]
  rw [← hZP]
  exact (RHTower.orderOneEnvelope_riemannXi.mul hpow).mul hrec

/-! ### The Gamma presentation -/

/-- `½ log(N/π)`. -/
def halfLog (N : ℕ) : ℝ := (Real.log N - Real.log π) / 2

/-- The Gamma presentation of `L(s + iθ, χ)`, with parity `d` and root number `ω`. -/
def shiftGammaData (N : ℕ) (d θ : ℝ) (hd : 0 ≤ d) (ω : ℂ) (hω : ‖ω‖ = 1) : SelbergGammaData where
  Q := Real.exp (halfLog N)
  Q_pos := Real.exp_pos _
  rank := 1
  lambda := fun _ => 1 / 2
  lambda_pos := fun _ => by norm_num
  mu := fun _ => ((d : ℂ) + I * (θ : ℂ)) / 2
  mu_re_nonneg := fun _ => by
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    simp only [zero_mul, one_mul, sub_self, add_zero]
    positivity
  rootNumber := ω
  rootNumber_norm := hω

/-- The elementary factor relating the presentation to `Γ_ℝ`. -/
def shiftExp (N : ℕ) (d θ : ℝ) (s : ℂ) : ℂ :=
  cexp ((halfLog N : ℂ) * s + (Real.log π : ℂ) * ((s + I * (θ : ℂ) + d) / 2))

theorem gammaFactor_shift (N : ℕ) (d θ : ℝ) (hd : 0 ≤ d) (ω : ℂ) (hω : ‖ω‖ = 1) (s : ℂ) :
    (shiftGammaData N d θ hd ω hω).gammaFactor s =
      shiftExp N d θ s * Gammaℝ (s + I * (θ : ℂ) + d) := by
  change ((Real.exp (halfLog N) : ℝ) : ℂ) ^ s *
    (∏ _j : Fin 1, Complex.Gamma (((1 / 2 : ℝ) : ℂ) * s + ((d : ℂ) + I * (θ : ℂ)) / 2)) = _
  simp only [Fin.prod_univ_one]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have harg : ((1 / 2 : ℝ) : ℂ) * s + ((d : ℂ) + I * (θ : ℂ)) / 2 = (s + I * (θ : ℂ) + d) / 2 := by
    push_cast
    ring
  rw [harg, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr
    (Real.exp_pos _).ne'), ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, shiftExp,
    Complex.cpow_def_of_ne_zero hπ, ← Complex.ofReal_log Real.pi_pos.le, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

theorem shiftGammaData_degree (N : ℕ) (d θ : ℝ) (hd : 0 ≤ d) (ω : ℂ) (hω : ‖ω‖ = 1) :
    (shiftGammaData N d θ hd ω hω).degree = 1 := by
  change 2 * (∑ _j : Fin 1, (1 / 2 : ℝ)) = 1
  norm_num

theorem shiftGammaData_conductor {N : ℕ} (hN : 0 < N) (d θ : ℝ) (hd : 0 ≤ d) (ω : ℂ)
    (hω : ‖ω‖ = 1) : (shiftGammaData N d θ hd ω hω).conductor = N := by
  rw [SelbergGammaData.conductor, shiftGammaData_degree]
  change (2 * π) ^ (1 : ℝ) * Real.exp (halfLog N) ^ 2 *
    (∏ _j : Fin 1, (1 / 2 : ℝ) ^ (2 * (1 / 2 : ℝ))) = _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have he : Real.exp (halfLog N) ^ 2 = N / π := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * halfLog N = Real.log N - Real.log π by
      unfold halfLog
      push_cast
      ring, Real.exp_sub, Real.exp_log hNR, Real.exp_log Real.pi_pos]
  simp only [Real.rpow_one, Fin.prod_univ_one]
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  rw [he]
  field_simp [Real.pi_ne_zero]

theorem shiftGammaData_internalShift (N : ℕ) (d θ : ℝ) (hd : 0 ≤ d) (ω : ℂ) (hω : ‖ω‖ = 1) :
    (shiftGammaData N d θ hd ω hω).internalShift = θ := by
  rw [SelbergGammaData.internalShift, shiftGammaData_degree]
  change (2 / (1 : ℝ)) * (∑ _j : Fin 1, ((d : ℂ) + I * (θ : ℂ)) / 2).im = θ
  simp
  ring

/-- The root number of a primitive character has norm one. -/
theorem norm_rootNumber_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : ‖DirichletCharacter.rootNumber χ‖ = 1 := by
  rcases eq_or_ne χ 1 with h1 | h1
  · have hN : N = 1 := by
      have hc := (DirichletCharacter.isPrimitive_def χ).mp hχ
      rw [h1, DirichletCharacter.conductor_one] at hc
      exact hc.symm
    subst hN
    rw [DirichletCharacter.rootNumber_modOne]
    simp
  · exact cglLemma62_primitive_rootNumber_norm_one
      ⟨⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩, χ, h1, hχ⟩

/-! ### The functional equation -/

section FunctionalEquation

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {d θ : ℝ}

theorem star_shiftExp (N : ℕ) (d θ : ℝ) (s : ℂ) :
    star (shiftExp N d θ (1 - star s)) =
      cexp ((halfLog N : ℂ) * (1 - s) + (Real.log π : ℂ) * ((1 - s - I * (θ : ℂ) + d) / 2)) := by
  unfold shiftExp
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_add, map_mul, map_sub, map_one, map_div₀, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_conj, map_ofNat]
  ring

omit [NeZero N] in
/-- The elementary factors match across the functional equation. -/
theorem functional_identity (hN : N ≠ 0) (d θ : ℝ) (s ε Λ₁ Λ₂ : ℂ)
    (hfe : Λ₁ = (N : ℂ) ^ ((1 - (s + I * (θ : ℂ))) - 1 / 2) * ε * Λ₂) :
    shiftExp N d θ s * Λ₁ = (ε * cexp (-(2 * I * (θ : ℂ) * (halfLog N : ℂ)))) *
      (star (shiftExp N d θ (1 - star s)) * Λ₂) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [hfe, star_shiftExp, Complex.cpow_def_of_ne_zero hNc, ← Complex.natCast_log]
  have hexp : shiftExp N d θ s * cexp ((Real.log N : ℂ) * ((1 - (s + I * (θ : ℂ))) - 1 / 2)) =
      cexp (-(2 * I * (θ : ℂ) * (halfLog N : ℂ))) *
        cexp ((halfLog N : ℂ) * (1 - s) + (Real.log π : ℂ) * ((1 - s - I * (θ : ℂ) + d) / 2)) := by
    unfold shiftExp
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold halfLog
    push_cast
    ring
  linear_combination (ε * Λ₂) * hexp

theorem completed_eq_shift {hd0 : 0 ≤ d} {ω : ℂ} {hω : ‖ω‖ = 1}
    (hd : ∀ s, DirichletCharacter.gammaFactor χ s = Gammaℝ (s + (d : ℂ)))
    {A : SelbergAnalyticContinuation}
    (hval : ∀ s, s ≠ 1 → A.value s = DirichletCharacter.LFunction χ (s + I * (θ : ℂ))) {s : ℂ}
    (hs1 : s ≠ 1) (hs2 : s + I * (θ : ℂ) ≠ 0 ∨ N ≠ 1) (hΓ : Gammaℝ (s + I * (θ : ℂ) + d) ≠ 0) :
    selbergCompletedValue (shiftGammaData N d θ hd0 ω hω) A s =
      shiftExp N d θ s * DirichletCharacter.completedLFunction χ (s + I * (θ : ℂ)) := by
  rw [selbergCompletedValue, gammaFactor_shift, hval s hs1,
    DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ hs2, hd]
  field_simp

theorem Gammaℝ_ne_zero_of_reciprocal {z : ℂ}
    (hz : GaloisForLFunctions.reciprocalGammaEntire (z / 2) ≠ 0) : Gammaℝ z ≠ 0 := by
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr
    Real.pi_ne_zero))) fun h => hz ?_
  simp only [GaloisForLFunctions.reciprocalGammaEntire, h, inv_zero]

/-- **The functional equation of `L(s + iθ, χ)` in Selberg form.** -/
theorem functionalEquation_shift (hχ : χ.IsPrimitive) (hθ : N = 1 → θ = 0) (hd0 : 0 ≤ d)
    (hd : ∀ s, DirichletCharacter.gammaFactor χ s = Gammaℝ (s + (d : ℂ))) {ω : ℂ}
    (hω : ‖ω‖ = 1)
    (hωeq : ω = DirichletCharacter.rootNumber χ * cexp (-(2 * I * (θ : ℂ) * (halfLog N : ℂ))))
    {A : SelbergAnalyticContinuation}
    (hval : ∀ s, s ≠ 1 → A.value s = DirichletCharacter.LFunction χ (s + I * (θ : ℂ)))
    (hconj : ∀ z, star (DirichletCharacter.completedLFunction χ z) =
      DirichletCharacter.completedLFunction χ⁻¹ (star z)) :
    selbergCompletedValue (shiftGammaData N d θ hd0 ω hω) A =ᶠ[codiscrete ℂ]
      fun s => (shiftGammaData N d θ hd0 ω hω).rootNumber *
        selbergConjugateReflection (selbergCompletedValue (shiftGammaData N d θ hd0 ω hω) A) s := by
  let g : ℂ → ℂ := fun s => GaloisForLFunctions.reciprocalGammaEntire ((s + I * (θ : ℂ) + d) / 2) *
    GaloisForLFunctions.reciprocalGammaEntire ((1 - (s + I * (θ : ℂ)) + d) / 2)
  have hdR : Differentiable ℂ GaloisForLFunctions.reciprocalGammaEntire :=
    Complex.differentiable_one_div_Gamma
  have hg : AnalyticOnNhd ℂ g univ := by
    refine Complex.analyticOnNhd_univ_iff_differentiable.mpr (Differentiable.mul ?_ ?_)
    · exact hdR.comp (by fun_prop)
    · exact hdR.comp (by fun_prop)
  have hgzero : ¬ Set.EqOn g 0 univ := by
    intro h
    have hre : (0 : ℝ) < ((1 / 2 + (d : ℂ)) / 2).re := by
      simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re]
      norm_num
      positivity
    have hΓ := Complex.Gamma_ne_zero_of_re_pos hre
    have hpoint : g (1 / 2 - I * (θ : ℂ)) ≠ 0 := by
      dsimp only [g, GaloisForLFunctions.reciprocalGammaEntire]
      have e1 : (1 / 2 - I * (θ : ℂ) + I * (θ : ℂ) + d) / 2 = (1 / 2 + (d : ℂ)) / 2 := by ring
      have e2 : (1 - (1 / 2 - I * (θ : ℂ) + I * (θ : ℂ)) + d) / 2 = (1 / 2 + (d : ℂ)) / 2 := by ring
      rw [e1, e2]
      exact mul_ne_zero (inv_ne_zero hΓ) (inv_ne_zero hΓ)
    exact hpoint (h (mem_univ _))
  have hgood : ∀ᶠ s in codiscrete ℂ, g s ≠ 0 :=
    (hg.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left hgzero
  have hzero : (singleton (0 : ℂ))ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨isClosed_singleton, subsingleton_singleton.isDiscrete⟩
  have hone : (singleton (1 : ℂ))ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨isClosed_singleton, subsingleton_singleton.isDiscrete⟩
  filter_upwards [hgood, hzero, hone] with s hgs hs0 hs1
  have hs0' : s ≠ 0 := hs0
  have hs1' : s ≠ 1 := hs1
  have hΓs : Gammaℝ (s + I * (θ : ℂ) + d) ≠ 0 :=
    Gammaℝ_ne_zero_of_reciprocal (mul_ne_zero_iff.mp hgs).1
  -- the reflected Gamma factor
  have hΓr : Gammaℝ (1 - star s + I * (θ : ℂ) + d) ≠ 0 := by
    refine Gammaℝ_ne_zero_of_reciprocal ?_
    have h2 := (mul_ne_zero_iff.mp hgs).2
    simp only [GaloisForLFunctions.reciprocalGammaEntire] at h2 ⊢
    have hG : Complex.Gamma ((1 - (s + I * (θ : ℂ)) + d) / 2) ≠ 0 :=
      fun h0 => h2 (by rw [h0, inv_zero])
    have hc : (1 - star s + I * (θ : ℂ) + d) / 2 =
        (starRingEnd ℂ) ((1 - (s + I * (θ : ℂ)) + d) / 2) := by
      simp only [map_div₀, map_add, map_sub, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal,
        map_ofNat, Complex.star_def]
      ring
    rw [hc, Complex.Gamma_conj]
    exact inv_ne_zero ((map_ne_zero _).mpr hG)
  have hcond1 : s + I * (θ : ℂ) ≠ 0 ∨ N ≠ 1 := by
    by_cases hN : N = 1
    · left
      rw [hθ hN]
      simpa using hs0'
    · exact Or.inr hN
  have hcond2 : 1 - star s + I * (θ : ℂ) ≠ 0 ∨ N ≠ 1 := by
    by_cases hN : N = 1
    · left
      rw [hθ hN]
      simp only [Complex.ofReal_zero, mul_zero, add_zero]
      intro h
      apply hs1'
      have h1 : star s = 1 := (sub_eq_zero.mp h).symm
      have h2 := congrArg star h1
      simpa using h2
    · exact Or.inr hN
  have hr1 : 1 - star s ≠ 1 := by
    intro h
    apply hs0'
    have h1 : star s = 0 := by linear_combination -h
    simpa using h1
  change _ = ω * _
  rw [selbergConjugateReflection, completed_eq_shift hd hval hr1 hcond2 hΓr,
    completed_eq_shift hd hval hs1' hcond1 hΓs, star_mul', hconj]
  have hstar : star (1 - star s + I * (θ : ℂ)) = 1 - (s + I * (θ : ℂ)) := by
    simp only [star_add, star_sub, star_one, star_mul', Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [hstar, hωeq]
  refine functional_identity (NeZero.ne N) d θ s _ _ _ ?_
  have h := hχ.completedLFunction_one_sub (1 - (s + I * (θ : ℂ)))
  rwa [sub_sub_cancel] at h

end FunctionalEquation

/-! ### The class element -/

/-- A shifted primitive L-function with a continuation is a Selberg-class element. -/
theorem exists_selberg_of_continuation {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {θ : ℝ}
    (hχ : χ.IsPrimitive) (hθ : N = 1 → θ = 0) (A : SelbergAnalyticContinuation)
    (hval : ∀ s, s ≠ 1 → A.value s = DirichletCharacter.LFunction χ (s + I * (θ : ℂ)))
    (hconj : ∀ z, star (DirichletCharacter.completedLFunction χ z) =
      DirichletCharacter.completedLFunction χ⁻¹ (star z)) :
    ∃ G : RHTower.SelbergClass, G.coeff = dirichletCoeff χ θ ∧ G.gammaData.degree = 1 ∧
      G.gammaData.conductor = N ∧ G.gammaData.internalShift = θ := by
  obtain ⟨d, hd01, hd⟩ := gammaFactor_eq_Gammaℝ χ
  have hd0 : 0 ≤ d := by
    rcases hd01 with rfl | rfl <;> norm_num
  have hω : ‖DirichletCharacter.rootNumber χ * cexp (-(2 * I * (θ : ℂ) * (halfLog N : ℂ)))‖ = 1 := by
    rw [norm_mul, norm_rootNumber_of_primitive hχ, one_mul, Complex.norm_exp]
    simp
  have hne : ∀ s : ℂ, 1 < s.re → s ≠ 1 := by
    intro s hs h
    rw [h] at hs
    simp at hs
  refine ⟨{ toExtendedSelbergClass :=
              { coeff := dirichletCoeff χ θ
                coeff_ne_zero := ?_
                lSeriesSummable := fun _ hs => lSeriesSummable_dirichletCoeff χ θ hs
                continuation := A
                lSeries_eq_value := fun s hs => by
                  rw [lSeries_dirichletCoeff χ θ hs, hval s (hne s hs)]
                gammaData := shiftGammaData N d θ hd0 _ hω
                functionalEquation :=
                  functionalEquation_shift hχ hθ hd0 hd hω rfl hval hconj }
            coeff_one := ?_
            ramanujan := ?_
            eulerLogCoeff := dirichletLogCoeff χ θ
            eulerLogCoeff_primePower := ?_
            eulerTheta := 0
            eulerTheta_lt_half := by norm_num
            eulerLogBound := ?_
            eulerLogSummable := fun _ hs => lSeriesSummable_dirichletLogCoeff χ θ hs
            eulerProduct := fun s hs => by
              rw [exp_lSeries_dirichletLogCoeff χ θ hs, hval s (hne s hs)] },
    rfl, shiftGammaData_degree N d θ hd0 _ hω,
    shiftGammaData_conductor (Nat.pos_of_ne_zero (NeZero.ne N)) d θ hd0 _ hω,
    shiftGammaData_internalShift N d θ hd0 _ hω⟩
  · intro h
    have h1 := congrArg (fun f : ArithmeticFunction ℂ => f 1) h
    simp [dirichletCoeff_of_ne_zero χ θ one_ne_zero] at h1
  · simp [dirichletCoeff_of_ne_zero χ θ one_ne_zero]
  · intro ε hε
    refine ⟨1, one_pos, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [one_mul]
    exact (norm_dirichletCoeff_le χ θ n).trans (Real.one_le_rpow hn1 hε.le)
  · intro n hn
    obtain ⟨p, k, hp, hk, rfl⟩ :=
      (isPrimePow_nat_iff n).mp (isPrimePow_of_dirichletLogCoeff_ne_zero χ θ hn)
    exact ⟨p, k, hp, hk, rfl⟩
  · refine ⟨1, one_pos, fun n _ => ?_⟩
    simpa using norm_dirichletLogCoeff_le χ θ n

theorem completedRiemannZeta₀_conj' (s : ℂ) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ completedRiemannZeta₀ ∘ (starRingEnd ℂ) with hg
  have hgd : Differentiable ℂ g := fun z => by
    have := (differentiable_completedZeta₀ ((starRingEnd ℂ) z)).conj_conj
    rwa [Complex.conj_conj] at this
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : completedRiemannZeta₀ =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    simp only [hg, Function.comp_apply]
    rw [RHTower.completedRiemannZeta₀_conj_of_one_lt hz, Complex.conj_conj]
  have hall := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun z _ => differentiable_completedZeta₀.analyticAt z) (fun z _ => hgd.analyticAt z)
    isPreconnected_univ (Set.mem_univ 2) heq
  have h := hall (Set.mem_univ ((starRingEnd ℂ) s))
  simp only [hg, Function.comp_apply, Complex.conj_conj] at h
  exact h

theorem completedRiemannZeta_conj' (s : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq, completedRiemannZeta₀_conj']
  simp [map_sub]

/-- **`L(s + iθ, χ)` is in the Selberg class** for `χ` primitive modulo `N` and `θ` real, with `θ = 0`
when `N = 1`.  It has degree one, conductor `N` and internal shift `θ`. -/
theorem exists_selberg_dirichlet {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {θ : ℝ}
    (hχ : χ.IsPrimitive) (hθ : N = 1 → θ = 0) :
    ∃ G : RHTower.SelbergClass, G.coeff = dirichletCoeff χ θ ∧ G.gammaData.degree = 1 ∧
      G.gammaData.conductor = N ∧ G.gammaData.internalShift = θ := by
  rcases eq_or_ne N 1 with rfl | hN
  · have hθ0 := hθ rfl
    subst hθ0
    obtain ⟨A₁, B₁, ρ₁, hA₁, hB₁, hρ₁, hg₁⟩ := growth_of_orderOneEnvelope orderOneEnvelope_zetaPoleUnit
    refine exists_selberg_of_continuation hχ hθ
      ⟨1, ⟨RHTower.zetaPoleUnit, Complex.analyticOnNhd_univ_iff_differentiable.mpr
        RHTower.differentiable_zetaPoleUnit, A₁, B₁, ρ₁, hA₁, hB₁, hρ₁, hg₁⟩⟩ ?_ ?_
    · intro s hs
      have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
      simp only [SelbergAnalyticContinuation.value, pow_one, Complex.ofReal_zero, mul_zero, add_zero,
        DirichletCharacter.LFunction_modOne_eq]
      change RHTower.zetaPoleUnit s / (s - 1) = _
      rw [RHTower.zetaPoleUnit_of_ne hs]
      field_simp
    · intro z
      simp only [DirichletCharacter.completedLFunction_modOne_eq, Complex.star_def]
      exact (completedRiemannZeta_conj' z).symm
  · have hχ1 : χ ≠ 1 := by
      intro h
      apply hN
      have hc := (DirichletCharacter.isPrimitive_def χ).mp hχ
      rw [h, DirichletCharacter.conductor_one] at hc
      exact hc.symm
    have henv := (orderOneEnvelope_LFunction hχ1 hN).comp_affine 1 (I * (θ : ℂ))
    obtain ⟨A₁, B₁, ρ₁, hA₁, hB₁, hρ₁, hg₁⟩ := growth_of_orderOneEnvelope henv
    have hdiff : Differentiable ℂ (fun s : ℂ => DirichletCharacter.LFunction χ (1 * s + I * (θ : ℂ))) :=
      (DirichletCharacter.differentiable_LFunction hχ1).comp (by fun_prop)
    refine exists_selberg_of_continuation hχ hθ
      ⟨0, ⟨_, Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff,
        A₁, B₁, ρ₁, hA₁, hB₁, hρ₁, hg₁⟩⟩ ?_ ?_
    · intro s _
      simp only [SelbergAnalyticContinuation.value, pow_zero, div_one]
      rw [one_mul]
    · intro z
      exact conj_completedLFunction hχ1 z

end GaloisForLFunctions.SelbergClass.DegreeOne
