import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCone

/-!
# Zero-free strips are horizontal absolute monotonicity

For real `x` the slice product `g_t(x) = ξ(½ + x + it)·ξ(½ − x + it)` equals `|ξ(½ + x + it)|²`.
For `x₀ ≥ 0` call `g_t` *absolutely monotone from `x₀`* when every Taylor coefficient of `g_t` at
`x₀` is nonnegative (`XiHorizontalAbsMono x₀ t`); then `σ ↦ |ξ(σ + it)|²` and all its derivatives
are nonnegative and nondecreasing on `[½ + x₀, ∞)`.

**Strip criterion** (`forall_abs_re_sub_half_le_iff_forall_horizontalAbsMono`).  For `x₀ ≥ 0`, every
zero `ρ` of `ξ` satisfies `|Re ρ − ½| ≤ x₀` if and only if `g_t` is absolutely monotone from `x₀`
at every height `t`.  At `x₀ = 0` this is the slice Taylor-positivity form of RH.  In general,
`sup_t` of the absolute-monotonicity abscissa equals `Θ = sup Re ρ`.

* `⟹`: each zero contributes, in the shifted variable `u = x − x₀`, a product of quadratics
  `(u + x₀ ∓ c)² + (γ − t)²` with `c = |Re ρ − ½|`.  These have nonnegative coefficients exactly when
  `c ≤ x₀`, with no dependence on the height distance `γ − t`.  Nonnegative Taylor coefficients are
  closed under products and locally uniform limits of the Hadamard product.
* `⟸`: at the height `t = Im ρ` the slice vanishes at `x = c`.  If `c > x₀`, nonnegative Taylor
  coefficients at `x₀` force all of them to vanish, contradicting `g_t(1) ≠ 0`.

Unconditionally every zero has `|Re ρ − ½| < ½`, so `|ξ(σ + it)|²` is absolutely monotone on
`σ ≥ 1` at every height (`horizontalAbsMono_half`).
-/

open Complex Filter Topology
open scoped ComplexOrder Nat

namespace RHTower

noncomputable section

/-- Absolute monotonicity of the slice at height `t` from the abscissa `½ + x₀`: every Taylor
coefficient of `x ↦ ξ(½ + x + it) ξ(½ − x + it)` at `x₀` is nonnegative. -/
def XiHorizontalAbsMono (x₀ t : ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)

/-- A real quadratic with nonnegative coefficients has nonnegative Taylor coefficients at `0`. -/
theorem nonnegTaylorAtZero_quadratic {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    NonnegTaylorAtZero (fun u : ℂ => (α : ℂ) + (β : ℂ) * u ^ 1 + (γ : ℂ) * u ^ 2) := by
  refine ⟨by fun_prop, fun n => ?_⟩
  have hc0 : ContDiffAt ℂ n (fun _ : ℂ => (α : ℂ)) 0 := contDiffAt_const
  have hc1 : ContDiffAt ℂ n (fun u : ℂ => (β : ℂ) * u ^ 1) 0 := by fun_prop
  have hc2 : ContDiffAt ℂ n (fun u : ℂ => (γ : ℂ) * u ^ 2) 0 := by fun_prop
  rw [iteratedDeriv_fun_add (hc0.add hc1) hc2, iteratedDeriv_fun_add hc0 hc1, iteratedDeriv_const,
    iteratedDeriv_const_mul_field (β : ℂ) (fun u : ℂ => u ^ 1),
    iteratedDeriv_const_mul_field (γ : ℂ) (fun u : ℂ => u ^ 2), iteratedDeriv_fun_pow_zero,
    iteratedDeriv_fun_pow_zero]
  have h0 : (0 : ℂ) ≤ (α : ℂ) := Complex.zero_le_real.mpr hα
  have h1 : (0 : ℂ) ≤ (β : ℂ) := Complex.zero_le_real.mpr hβ
  have h2 : (0 : ℂ) ≤ (γ : ℂ) := Complex.zero_le_real.mpr hγ
  refine add_nonneg (add_nonneg ?_ (mul_nonneg h1 ?_)) (mul_nonneg h2 ?_) <;> split_ifs <;>
    first | exact h0 | exact le_rfl | exact Nat.cast_nonneg _

/-- **Strip ⟹ absolute monotonicity.**  If every zero copy satisfies `|Re ρ − ½| ≤ x₀`, then the
slice at every height is absolutely monotone from `x₀`. -/
theorem horizontalAbsMono_of_abs_re_sub_half_le {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hzero : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ x₀) (t : ℝ) :
    XiHorizontalAbsMono x₀ t := by
  classical
  set φm : ℂ → ℂ := fun u => (t : ℂ) - I * ((x₀ : ℂ) + u) with hφm
  set φp : ℂ → ℂ := fun u => (t : ℂ) + I * ((x₀ : ℂ) + u) with hφp
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPcont : Continuous xiCanonicalProduct :=
    continuous_iff_continuousAt.mpr fun z =>
      (xiCanonicalProduct_analytic z (Set.mem_univ z)).continuousAt
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  let c : Finset XiZeroCopy → Finset XiZeroCopy := fun S => S ∪ S.image lagPartner
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ a ∈ c S, lagPartner a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · left
      rw [lagPartner_lagPartner]
      exact hb
  have hmul' := tendstoLocallyUniformlyOn_comp_index hmul hc
  set f : XiZeroCopy → ℂ → ℂ := fun q u =>
    weierstrassE1 (φm u / xiSpectralPoint q) * weierstrassE1 (φp u / xiSpectralPoint q) with hf
  have hfix : ∀ q, lagPartner q = q → NonnegTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1 : ℂ).re = 1 / 2 :=
      (lagPartner_fst_eq_iff q).mp (congrArg (fun r => (r.1 : ℂ)) hq)
    have hz : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]
      simp
    have hγ : (q.1 : ℂ).im ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hz, h0, Complex.ofReal_zero]
    set γ := (q.1 : ℂ).im
    have e : f q = fun u : ℂ =>
        ((Real.exp (2 * t / γ) * (γ - t) ^ 2 / γ ^ 2 + Real.exp (2 * t / γ) / γ ^ 2 * x₀ ^ 2 : ℝ) :
          ℂ) + ((2 * (Real.exp (2 * t / γ) / γ ^ 2) * x₀ : ℝ) : ℂ) * u ^ 1 +
        ((Real.exp (2 * t / γ) / γ ^ 2 : ℝ) : ℂ) * u ^ 2 := by
      funext u
      simp only [hf, hz, hφm, hφp]
      rw [weierstrassE1_slice_pair hγ ((x₀ : ℂ) + u)]
      push_cast
      ring
    rw [e]
    exact nonnegTaylorAtZero_quadratic (by positivity) (by positivity) (by positivity)
  have hpair : ∀ q, lagPartner q ≠ q → NonnegTaylorAtZero (f q * f (lagPartner q)) := by
    intro q _
    set a : ℝ := (q.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q
    have hzσ : xiSpectralPoint (lagPartner q) = starRingEnd ℂ ((a : ℂ) + cc * I) := by
      rw [xiSpectralPoint_lagPartner, hz]
    have hcc_le : |cc| ≤ x₀ := by
      have h := hzero q
      rw [hcc, show (1 / 2 : ℝ) - (q.1 : ℂ).re = -((q.1 : ℂ).re - 1 / 2) by ring, abs_neg]
      exact h
    have hlo : 0 ≤ x₀ - cc := by linarith [le_abs_self cc]
    have hhi : 0 ≤ x₀ + cc := by linarith [neg_abs_le cc]
    have e : f q * f (lagPartner q) =
        (fun _ : ℂ => ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) / (a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ)) *
          ((fun u : ℂ => ((((x₀ - cc) ^ 2 + (a - t) ^ 2 : ℝ)) : ℂ) +
              ((2 * (x₀ - cc) : ℝ) : ℂ) * u ^ 1 + ((1 : ℝ) : ℂ) * u ^ 2) *
            (fun u : ℂ => ((((x₀ + cc) ^ 2 + (a - t) ^ 2 : ℝ)) : ℂ) +
              ((2 * (x₀ + cc) : ℝ) : ℂ) * u ^ 1 + ((1 : ℝ) : ℂ) * u ^ 2)) := by
      funext u
      simp only [Pi.mul_apply, hf, hz, hzσ, hφm, hφp]
      rw [weierstrassE1_slice_reflectionPair hz0 ((x₀ : ℂ) + u)]
      push_cast
      ring
    rw [e]
    refine (nonnegTaylorAtZero_const (Complex.zero_le_real.mpr (by positivity))).mul
      ((nonnegTaylorAtZero_quadratic (by positivity) (by positivity) zero_le_one).mul
        (nonnegTaylorAtZero_quadratic (by positivity) (by positivity) zero_le_one))
  have hfin : ∀ S : Finset XiZeroCopy, NonnegTaylorAtZero
      (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) := by
    intro S
    have e : (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) =
        fun x => ∏ q ∈ c S, f q x := by
      funext x
      simp only [Pi.mul_apply, Function.comp_apply, hf]
      rw [Finset.prod_mul_distrib]
    rw [e]
    have hone : NonnegTaylorAtZero (fun _ : ℂ => (1 : ℂ)) := nonnegTaylorAtZero_const zero_le_one
    exact prod_of_involution_of_mul hone (fun _ _ hf hg => hf.mul hg) lagPartner
      lagPartner_lagPartner f hfix hpair (c S) (hclosed S)
  have hlim : NonnegTaylorAtZero ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) :=
    NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
      ((hPdiff.comp (by rw [hφm]; fun_prop)).mul (hPdiff.comp (by rw [hφp]; fun_prop))) hmul'
  have e : (fun u => xiSliceProduct t ((x₀ : ℂ) + u)) = (fun _ => XiC 0 * XiC 0) *
      ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) := by
    funext u
    rw [xiSliceProduct_eq_XiC]
    have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
      simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
    simp only [Pi.mul_apply, Function.comp_apply, hφm, hφp]
    rw [hX ((t : ℂ) - I * ((x₀ : ℂ) + u)), hX ((t : ℂ) + I * ((x₀ : ℂ) + u))]
    ring
  have hshift := (nonnegTaylorAtZero_const zero_le_XiC_zero_mul_self).mul hlim
  rw [← e] at hshift
  intro n
  have h := hshift.2 n
  rw [iteratedDeriv_comp_const_add n (xiSliceProduct t) (x₀ : ℂ)] at h
  simpa only [add_zero] using h

/-- The slice does not vanish at `x = 1`: both factors lie in `Re s = 3/2`. -/
theorem xiSliceProduct_one_ne_zero (t : ℝ) : xiSliceProduct t 1 ≠ 0 := by
  unfold xiSliceProduct
  have hnz : ∀ s : ℂ, s.re = 3 / 2 → xi s ≠ 0 := by
    intro s hs
    have hre : 0 < s.re := by rw [hs]; norm_num
    have h1 : s ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hs
      norm_num at hs
    rw [Ne, xi_eq_zero_iff hre h1]
    exact riemannZeta_ne_zero_of_one_lt_re (by rw [hs]; norm_num)
  refine mul_ne_zero (hnz _ (by simp; norm_num)) ?_
  rw [show (1 / 2 - 1 + (t : ℂ) * I) = 1 - (1 / 2 + 1 - (t : ℂ) * I) by ring, xi_one_sub]
  exact hnz _ (by simp; norm_num)

/-- **Absolute monotonicity at one height excludes the zeros at that height beyond `x₀`.**  If the
slice at height `Im ρ` is absolutely monotone from `x₀`, then `|Re ρ − ½| ≤ x₀`. -/
theorem abs_re_sub_half_le_of_horizontalAbsMono_at {x₀ : ℝ} (q : XiZeroCopy)
    (hq : XiHorizontalAbsMono x₀ (q.1 : ℂ).im) : |(q.1 : ℂ).re - 1 / 2| ≤ x₀ := by
  set ρ : ℂ := (q.1 : ℂ) with hρdef
  set t : ℝ := ρ.im with ht
  set c : ℝ := |ρ.re - 1 / 2| with hcdef
  have hρ0 : xi ρ = 0 := xi_eq_zero_of_mem_divisor_support q.1
  have hvan : xiSliceProduct t (c : ℂ) = 0 := by
    unfold xiSliceProduct
    rcases le_or_gt (1 / 2) ρ.re with hle | hlt
    · apply mul_eq_zero_of_left
      have hc' : c = ρ.re - 1 / 2 := abs_of_nonneg (by linarith)
      have : (1 / 2 + (c : ℂ) + (t : ℂ) * I) = ρ := by
        rw [hc']
        apply Complex.ext
        · simp
        · simp [ht]
      rw [this]
      exact hρ0
    · apply mul_eq_zero_of_right
      have hc' : c = -(ρ.re - 1 / 2) := abs_of_neg (by linarith)
      have : (1 / 2 - (c : ℂ) + (t : ℂ) * I) = ρ := by
        rw [hc']
        apply Complex.ext
        · simp
        · simp [ht]
      rw [this]
      exact hρ0
  by_contra hgt
  push Not at hgt
  have hdiff := differentiable_xiSliceProduct t
  have hsum := Complex.hasSum_taylorSeries_of_entire hdiff (x₀ : ℂ) (c : ℂ)
  rw [hvan] at hsum
  set T : ℕ → ℂ := fun n => ((n ! : ℂ))⁻¹ • ((c : ℂ) - x₀) ^ n •
    iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) with hT
  have hTreal : ∀ n, T n = (((T n).re : ℝ) : ℂ) ∧ 0 ≤ (T n).re := by
    intro n
    have hD := hq n
    set D := iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) with hDdef
    have hDre : D = ((D.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [(Complex.nonneg_iff.mp hD).2.symm]
    have hDnn : 0 ≤ D.re := (Complex.nonneg_iff.mp hD).1
    have hT' : T n = ((n ! : ℂ))⁻¹ * (((c : ℂ) - x₀) ^ n * D) := by
      simp only [hT, smul_eq_mul, hDdef]
    have hform : T n = ((((n ! : ℝ))⁻¹ * (c - x₀) ^ n * D.re : ℝ) : ℂ) := by
      rw [hT']
      nth_rewrite 1 [hDre]
      push_cast
      ring
    have hnn : 0 ≤ ((n ! : ℝ))⁻¹ * (c - x₀) ^ n * D.re := by
      have : 0 ≤ c - x₀ := by linarith
      positivity
    rw [hform, Complex.ofReal_re]
    exact ⟨rfl, hnn⟩
  have hsumre : HasSum (fun n => (T n).re) 0 := by
    have := hsum.mapL Complex.reCLM
    simpa using this
  have hzero := (hasSum_zero_iff_of_nonneg fun n => (hTreal n).2).mp hsumre
  have hDzero : ∀ n, iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) = 0 := by
    intro n
    have hTn : T n = 0 := by
      have h0 := congrFun hzero n
      simp only [Pi.zero_apply] at h0
      rw [(hTreal n).1, h0, Complex.ofReal_zero]
    rw [hT] at hTn
    simp only [smul_eq_mul] at hTn
    have hfac : ((n ! : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (Nat.factorial_pos n).ne')
    have hpow : ((c : ℂ) - x₀) ^ n ≠ 0 := by
      apply pow_ne_zero
      rw [sub_ne_zero]
      intro h'
      have := congrArg Complex.re h'
      simp only [Complex.ofReal_re] at this
      linarith
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hTn).resolve_left hfac)).resolve_left hpow
  have hone := Complex.hasSum_taylorSeries_of_entire hdiff (x₀ : ℂ) 1
  simp only [hDzero, smul_zero] at hone
  exact xiSliceProduct_one_ne_zero t (hone.unique hasSum_zero)

/-- **Absolute monotonicity ⟹ strip.**  If the slice at every height is absolutely monotone from
`x₀`, then every zero copy satisfies `|Re ρ − ½| ≤ x₀`. -/
theorem abs_re_sub_half_le_of_horizontalAbsMono {x₀ : ℝ} (h : ∀ t, XiHorizontalAbsMono x₀ t)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ x₀ :=
  abs_re_sub_half_le_of_horizontalAbsMono_at q (h _)

/-- **Strip criterion.**  For `x₀ ≥ 0`, every zero of `ξ` satisfies `|Re ρ − ½| ≤ x₀` iff at every
height `t` the slice `|ξ(½ + x + it)|²` is absolutely monotone from `x₀`. -/
theorem forall_abs_re_sub_half_le_iff_forall_horizontalAbsMono {x₀ : ℝ} (hx₀ : 0 ≤ x₀) :
    (∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ x₀) ↔ ∀ t : ℝ, XiHorizontalAbsMono x₀ t :=
  ⟨fun h t => horizontalAbsMono_of_abs_re_sub_half_le hx₀ h t,
    fun h q => abs_re_sub_half_le_of_horizontalAbsMono h q⟩

/-- **Unconditional absolute monotonicity on `σ ≥ 1`.**  At every height `t`, all Taylor
coefficients of `x ↦ ξ(½ + x + it) ξ(½ − x + it)` at `x = ½` are nonnegative. -/
theorem horizontalAbsMono_half (t : ℝ) : XiHorizontalAbsMono (1 / 2) t := by
  refine horizontalAbsMono_of_abs_re_sub_half_le (by norm_num) (fun q => ?_) t
  have h := xiZeroCopy_re_mem_open_unit q
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

end

end RHTower
