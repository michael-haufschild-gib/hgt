import GaloisForLFunctions.RHTower.DeBruijnLocalPairLawMonotonicity
import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion

/-!
# Slice Taylor positivity along the de Bruijn–Newman flow

Let `H_λ(z) = ∫ Φ(u) e^{λu²} e^{izu} du` (`riemannHeat λ`), so `H_0 = Ξ`.  The horizontal slice of
`H_λ` at height `t` is `x ↦ H_λ(t − ix) H_λ(t + ix)`, which for real `x` is `|H_λ(t + ix)|²`.  For
`λ = 0` nonnegativity of all its Taylor coefficients at every height is the Riemann hypothesis
(`riemannHypothesis_iff_xiSliceCoeff_nonneg`).

**Cone criterion for order-one functions** (`nonnegTaylorAtZero_slice_of_cone`).  Let `f` be
entire, even, real on `ℝ`, with `f(0) ≠ 0` and an order-one envelope.  If every zero `ζ` of `f`
satisfies `(Im ζ)² ≤ (Re ζ − t)²`, then every Taylor coefficient of the slice of `f` at height `t`
is nonnegative.  The Hadamard product `f = f(0) Π E₁(z/ζ)` is grouped into conjugation orbits:
a real zero contributes `e^{2t/ζ}((ζ − t)² + x²)/ζ²`, a conjugate pair contributes a positive
multiple of `x⁴ + 2((Re ζ − t)² − (Im ζ)²)x² + |ζ − t|⁴`.

**Large heights** (`exists_nonnegTaylorAtZero_riemannHeat_slice`).  For every `λ > 0` there is
`X₀` such that the slice of `H_λ` has nonnegative Taylor coefficients at every height `|t| ≥ X₀`.
The non-real zeros of `H_λ` lie in `|Re ζ| < X₁`, `(Im ζ)² ≤ ¼` (Ki–Kim–Lee), so beyond `X₁ + 1`
every zero is outside the cone.

**The Riemann hypothesis** (`riemannHypothesis_iff_forall_nonnegTaylorAtZero_riemannHeat_slice`).
RH holds iff for every `λ > 0` the slice of `H_λ` has nonnegative Taylor coefficients at every
height.  The reverse direction passes through vertical monotonicity of `|H_λ|`.

So along the flow, slice positivity holds at all large heights for every positive heat time, and
the Riemann hypothesis is the statement that the exceptional height window is empty for every
`λ > 0`.  This is the all-order strengthening of the vertical monotonicity law
(`exists_monotoneOn_norm_riemannHeat_vertical`).
-/

open Complex Filter Topology Set
open scoped ComplexOrder
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower.DeBruijn

noncomputable section

variable {f : ℂ → ℂ}

/-- **Monotonicity from Taylor positivity.**  If all Taylor coefficients of an entire `g` at `0`
are nonnegative, then `Re g` is nondecreasing on `[0, ∞)`. -/
theorem re_le_re_of_nonnegTaylorAtZero {g : ℂ → ℂ} (hg : NonnegTaylorAtZero g) {y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (h12 : y₁ ≤ y₂) : (g y₁).re ≤ (g y₂).re := by
  have hs1 := Complex.hasSum_re (Complex.hasSum_taylorSeries_of_entire hg.1 0 (y₁ : ℂ))
  have hs2 := Complex.hasSum_re (Complex.hasSum_taylorSeries_of_entire hg.1 0 (y₂ : ℂ))
  refine hasSum_le (fun n => ?_) hs1 hs2
  have hd := hg.2 n
  have hdre : 0 ≤ (iteratedDeriv n g 0).re := (Complex.nonneg_iff.mp hd).1
  have hdim : (iteratedDeriv n g 0).im = 0 := ((Complex.nonneg_iff.mp hd).2).symm
  have key : ∀ y : ℝ, ((n.factorial : ℂ)⁻¹ • ((y : ℂ) - 0) ^ n • iteratedDeriv n g 0).re =
      (n.factorial : ℝ)⁻¹ * y ^ n * (iteratedDeriv n g 0).re := by
    intro y
    have hdreal : iteratedDeriv n g 0 = ((iteratedDeriv n g 0).re : ℂ) :=
      Complex.ext (by simp) (by simp [hdim])
    rw [smul_eq_mul, smul_eq_mul, sub_zero]
    conv_lhs => rw [hdreal]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul,
      show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [key, key]
  have hpow : y₁ ^ n ≤ y₂ ^ n := pow_le_pow_left₀ hy₁ h12 n
  have hfac : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hfac) hdre

/-- **Cone criterion for the slice of an even real order-one entire function.**  If every zero
`ζ` of `f` satisfies `(Im ζ)² ≤ (Re ζ − t)²`, then `x ↦ f(t − ix) f(t + ix)` has nonnegative
Taylor coefficients at `0`. -/
theorem nonnegTaylorAtZero_slice_of_cone {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {t : ℝ} (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 ≤ (ζ.re - t) ^ 2) :
    NonnegTaylorAtZero (fun x => f ((t : ℂ) - I * x) * f ((t : ℂ) + I * x)) := by
  classical
  set a := zeroCopyPoint f with hadef
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hf hf0
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hford := analyticOrderAt_ne_top_of_ne_zero hf hf0
  have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven hbound
  set P := OrderOneHadamard.hadamardProduct f with hPdef
  have hPan := OrderOneHadamard.hadamardProduct_analytic hf hf0 hsum
  have hPcont : Continuous P :=
    continuous_iff_continuousAt.mpr fun z => (hPan z (Set.mem_univ z)).continuousAt
  have hPdiff : Differentiable ℂ P := fun z => (hPan z (Set.mem_univ z)).differentiableAt
  have hP : TendstoLocallyUniformlyOn (fun S z => ∏ q ∈ S, weierstrassE1 (z / a q)) P atTop
      Set.univ := canonicalProductE1Indexed_hasProdLocallyUniformlyOn a hane hsum
  set φm : ℂ → ℂ := fun x => (t : ℂ) - I * x with hφm
  set φp : ℂ → ℂ := fun x => (t : ℂ) + I * x with hφp
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  -- the conjugation involution on zero copies
  set τ := zeroCopyConj hf hconj with hτ
  have haτ : ∀ q, a (τ q) = (starRingEnd ℂ) (a q) := zeroCopyPoint_conj hf hconj
  have haτs : ∀ q, a (τ.symm q) = (starRingEnd ℂ) (a q) := by
    intro q
    have h := haτ (τ.symm q)
    rw [Equiv.apply_symm_apply] at h
    rw [h, Complex.conj_conj]
  let σ : ZeroCopy f → ZeroCopy f := fun q =>
    if 0 < (a q).im then τ q else if (a q).im < 0 then τ.symm q else q
  have haσ : ∀ q, a (σ q) = (starRingEnd ℂ) (a q) := by
    intro q
    simp only [σ]
    split_ifs with h1 h2
    · exact haτ q
    · exact haτs q
    · have him : (a q).im = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      exact (Complex.conj_eq_iff_im.mpr him).symm
  have hσσ : ∀ q, σ (σ q) = q := by
    intro q
    by_cases h1 : 0 < (a q).im
    · have hσq : σ q = τ q := if_pos h1
      have h2 : (a (τ q)).im < 0 := by rw [haτ, Complex.conj_im]; linarith
      have h3 : ¬ 0 < (a (τ q)).im := not_lt.mpr h2.le
      rw [hσq]
      simp only [σ, if_neg h3, if_pos h2, Equiv.symm_apply_apply]
    · by_cases h2 : (a q).im < 0
      · have hσq : σ q = τ.symm q := by simp only [σ, if_neg h1, if_pos h2]
        have h3 : 0 < (a (τ.symm q)).im := by rw [haτs, Complex.conj_im]; linarith
        rw [hσq]
        simp only [σ, if_pos h3, Equiv.apply_symm_apply]
      · have hσq : σ q = q := by simp only [σ, if_neg h1, if_neg h2]
        rw [hσq, hσq]
  -- conjugation-closed truncations
  let c : Finset (ZeroCopy f) → Finset (ZeroCopy f) := fun S => S ∪ S.image σ
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ q ∈ c S, σ q ∈ c S := by
    intro S q hq
    simp only [c, Finset.mem_union, Finset.mem_image] at hq ⊢
    rcases hq with hq | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩
    · left
      rw [hσσ]
      exact hb
  have hmul' := RHTower.tendstoLocallyUniformlyOn_comp_index hmul hc
  set F : ZeroCopy f → ℂ → ℂ := fun q x =>
    weierstrassE1 (φm x / a q) * weierstrassE1 (φp x / a q) with hF
  have hfix : ∀ q, σ q = q → NonnegTaylorAtZero (F q) := by
    intro q hq
    have him : (a q).im = 0 := by
      have h := congrArg Complex.im (haσ q)
      rw [hq, Complex.conj_im] at h
      linarith
    have hz : a q = (((a q).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hγ : (a q).re ≠ 0 := by
      intro h0
      apply hane q
      rw [hz, h0, Complex.ofReal_zero]
    simp only [hF, hφm, hφp]
    rw [hz]
    exact nonnegTaylorAtZero_slice_pair hγ
  have hpair : ∀ q, σ q ≠ q → NonnegTaylorAtZero (F q * F (σ q)) := by
    intro q _
    set α : ℝ := (a q).re with hα
    set β : ℝ := (a q).im with hβ
    have hz : a q = (α : ℂ) + β * I := (Complex.re_add_im (a q)).symm
    have hz0 : (α : ℂ) + β * I ≠ 0 := by rw [← hz]; exact hane q
    have hzσ : a (σ q) = starRingEnd ℂ ((α : ℂ) + β * I) := by rw [haσ, hz]
    have e : F q * F (σ q) = fun x =>
        ((Real.exp (4 * t * α / (α ^ 2 + β ^ 2)) / (α ^ 2 + β ^ 2) ^ 2 : ℝ) : ℂ) *
          (x ^ 4 + ((2 * ((α - t) ^ 2 - β ^ 2) : ℝ) : ℂ) * x ^ 2 +
            ((((α - t) ^ 2 + β ^ 2) ^ 2 : ℝ) : ℂ)) := by
      funext x
      simp only [Pi.mul_apply, hF, hzσ, hφm, hφp]
      rw [hz]
      exact weierstrassE1_slice_reflectionPair hz0 x
    rw [e]
    have hsq : β ^ 2 ≤ (α - t) ^ 2 := hloc (a q) (apply_zeroCopyPoint hf q)
    exact nonnegTaylorAtZero_quartic (by positivity) (by nlinarith) (by positivity)
  have hfin : ∀ S : Finset (ZeroCopy f), NonnegTaylorAtZero
      (((fun S z => ∏ q ∈ S, weierstrassE1 (z / a q)) (c S) ∘ φm) *
        ((fun S z => ∏ q ∈ S, weierstrassE1 (z / a q)) (c S) ∘ φp)) := by
    intro S
    have e : (((fun S z => ∏ q ∈ S, weierstrassE1 (z / a q)) (c S) ∘ φm) *
        ((fun S z => ∏ q ∈ S, weierstrassE1 (z / a q)) (c S) ∘ φp)) =
        fun x => ∏ q ∈ c S, F q x := by
      funext x
      simp only [Pi.mul_apply, Function.comp_apply, hF]
      rw [Finset.prod_mul_distrib]
    rw [e]
    exact nonnegTaylorAtZero_prod_of_involution σ hσσ F hfix hpair (c S) (hclosed S)
  have hlim : NonnegTaylorAtZero ((P ∘ φm) * (P ∘ φp)) :=
    NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
      ((hPdiff.comp (by rw [hφm]; fun_prop)).mul (hPdiff.comp (by rw [hφp]; fun_prop))) hmul'
  have hf0real : 0 ≤ f 0 * f 0 := by
    have h := hconj 0
    rw [map_zero] at h
    have him : (f 0).im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    rw [Complex.nonneg_iff]
    constructor
    · simp only [Complex.mul_re, him, mul_zero, sub_zero]
      exact mul_self_nonneg _
    · simp [Complex.mul_im, him]
  have e : (fun x => f ((t : ℂ) - I * x) * f ((t : ℂ) + I * x)) =
      (fun _ => f 0 * f 0) * ((P ∘ φm) * (P ∘ φp)) := by
    funext x
    simp only [Pi.mul_apply, Function.comp_apply, hφm, hφp]
    rw [hfac ((t : ℂ) - I * x), hfac ((t : ℂ) + I * x)]
    ring
  rw [e]
  exact (nonnegTaylorAtZero_const hf0real).mul hlim

/-- The cone criterion for the de Bruijn–Newman deformation, `λ ≥ 0`. -/
theorem nonnegTaylorAtZero_riemannHeat_slice_of_cone {lam t : ℝ} (hlam : 0 ≤ lam)
    (hloc : ∀ ζ, riemannHeat lam ζ = 0 → ζ.im ^ 2 ≤ (ζ.re - t) ^ 2) :
    NonnegTaylorAtZero (fun x => riemannHeat lam ((t : ℂ) - I * x) *
      riemannHeat lam ((t : ℂ) + I * x)) := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq hlam).exists_envelope
  exact nonnegTaylorAtZero_slice_of_cone hC (riemannHeat_analytic hlam) (riemannHeat_zero_ne hlam)
    (riemannHeat_neg hlam) (riemannHeat_conj hlam) hbound hloc

/-- **Slice positivity at all large heights along the flow.**  For every `λ > 0` there is `X₀`
such that `x ↦ H_λ(t − ix) H_λ(t + ix)` has nonnegative Taylor coefficients at `0` for every
height `|t| ≥ X₀`. -/
theorem exists_nonnegTaylorAtZero_riemannHeat_slice {lam : ℝ} (hlam : 0 < lam) :
    ∃ X₀ : ℝ, ∀ t : ℝ, X₀ ≤ |t| →
      NonnegTaylorAtZero (fun x => riemannHeat lam ((t : ℂ) - I * x) *
        riemannHeat lam ((t : ℂ) + I * x)) := by
  obtain ⟨X₁, hX₁⟩ := exists_riemannHeat_zeros_real hlam
  refine ⟨|X₁| + 1, fun t ht => nonnegTaylorAtZero_riemannHeat_slice_of_cone hlam.le
    fun ζ hζ => ?_⟩
  by_cases him : ζ.im = 0
  · rw [him]; nlinarith [sq_nonneg (ζ.re - t)]
  have hre : |ζ.re| < X₁ := by
    by_contra h
    exact him (hX₁ ζ hζ (not_lt.mp h))
  have him2 : ζ.im ^ 2 ≤ 1 / 4 :=
    (riemannHeat_zeros_im_sq_le hlam hζ).trans (max_le (by linarith) (by norm_num))
  have hdist : 1 ≤ |ζ.re - t| := by
    have h1 := abs_sub_abs_le_abs_sub t ζ.re
    rw [abs_sub_comm] at h1
    linarith [le_abs_self X₁]
  have : 1 ≤ (ζ.re - t) ^ 2 := by nlinarith [sq_abs (ζ.re - t), abs_nonneg (ζ.re - t)]
  linarith

/-- Slice Taylor positivity at height `t` makes `|H_λ(t + iy)|` nondecreasing on `y ≥ 0`. -/
theorem monotoneOn_norm_riemannHeat_of_nonnegTaylorAtZero {lam t : ℝ} (hlam : 0 ≤ lam)
    (h : NonnegTaylorAtZero (fun x => riemannHeat lam ((t : ℂ) - I * x) *
      riemannHeat lam ((t : ℂ) + I * x))) :
    MonotoneOn (fun y : ℝ => ‖riemannHeat lam ((t : ℂ) + I * y)‖) (Ici 0) := by
  have hsq : ∀ y : ℝ, (riemannHeat lam ((t : ℂ) - I * y) * riemannHeat lam ((t : ℂ) + I * y)).re =
      ‖riemannHeat lam ((t : ℂ) + I * y)‖ ^ 2 := by
    intro y
    have hc : (t : ℂ) - I * y = (starRingEnd ℂ) ((t : ℂ) + I * y) := by
      apply Complex.ext <;> simp
    rw [hc, riemannHeat_conj hlam, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  intro y₁ hy₁ y₂ _ h12
  have hle := re_le_re_of_nonnegTaylorAtZero h (mem_Ici.mp hy₁) h12
  rw [hsq, hsq] at hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

/-- **The Riemann hypothesis as slice positivity along the flow.**  RH holds iff for every heat
time `λ > 0` and every height `t`, `x ↦ H_λ(t − ix) H_λ(t + ix)` has nonnegative Taylor
coefficients at `0`. -/
theorem riemannHypothesis_iff_forall_nonnegTaylorAtZero_riemannHeat_slice :
    RiemannHypothesis ↔ ∀ lam : ℝ, 0 < lam → ∀ t : ℝ,
      NonnegTaylorAtZero (fun x => riemannHeat lam ((t : ℂ) - I * x) *
        riemannHeat lam ((t : ℂ) + I * x)) := by
  constructor
  · intro hRH lam hlam t
    rw [riemannHypothesis_iff_newmanConstant_eq_zero] at hRH
    have hmem := (mem_realRootedTimes_iff hlam.le).mpr (by rw [hRH]; exact hlam.le)
    exact nonnegTaylorAtZero_riemannHeat_slice_of_cone hlam.le fun ζ hζ => by
      rw [hmem.2 ζ hζ]; nlinarith [sq_nonneg (ζ.re - t)]
  · intro h
    exact riemannHypothesis_iff_forall_monotoneOn_norm_riemannHeat.mpr fun lam hlam t =>
      monotoneOn_norm_riemannHeat_of_nonnegTaylorAtZero hlam.le (h lam hlam t)

end

end RHTower.DeBruijn
