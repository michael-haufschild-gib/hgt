import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheOrdersOfARayClassLFunctionAreTheMultiplicitiesOfItsConfiguration
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction

/-!
# In a factorization of a Dedekind zeta function every prime of a modulus divides the conductor

Let `M` and `K` be number fields and `ψ_i`, `i ∈ ι` finite, ray class characters of `K` modulo
`𝔪_i` with

  `ζ_M(s) = Π_i L(s, ψ_i)`   for `Re s > 1`.

**Theorem** (`dvd_heckeFiniteConductor_of_dedekindZeta_eq_prod`). Every prime dividing `𝔪_i`
divides the conductor of `ψ_i`.

Proof. Let `ψ'_i` be the primitive character of `ψ_i`, `Ξ_i` its entire completion, `γ_i` its
Gamma factor, `P_i` its pole factor and `c_i(s) = N_i^{s/2}`. For `Re s > 1`

  `L(s, ψ_i) = L(s, ψ'_i) R_i(s)`,  `R_i(s) = Π_{v | 𝔪_i} (1 − ψ'_i(v) N v^{−s})`,

so with `E_M(s) = (s − 1) ζ_M(s)`, entire,

  `E_M(s) Π_i P_i(s) c_i(s) = (s − 1) Π_i γ_i(s)^{−1} Ξ_i(s) R_i(s)`.

Both sides are entire: the identity holds on `ℂ`. If `v | 𝔪_i` does not divide the conductor,
`z = ψ'_i(v)` has `|z| = 1` and `R_i(s₀) = 0` at a point `s₀` with `Re s₀ = 0`, `Im s₀ > 0`
(`exists_conductorEulerFactor_eq_zero`). The factors `P_i c_i` do not vanish at `s₀`, so
`E_M(s₀) = 0`. But `Ξ_M / γ_M = s c_M E_M`, the Gamma factor is finite and non-zero off the real
axis (`heckeGammaFactor_ne_zero_of_im_ne_zero`), and the completion `Ξ_M` has no zero on
`Re s ≤ 0`: it has none on `Re s ≥ 1` and satisfies the functional equation
(`heckeXi_ne_zero_of_one_le_re`, `heckeXi_ne_zero_of_re_le_zero`).
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions IsDedekindDomain

/-! ### A zero of an Euler factor on the imaginary axis -/

theorem mul_neg_div_mul_I (ℓ a p : ℂ) (hℓ : ℓ ≠ 0) :
    ℓ * -((a + 2 * p) / ℓ * I) = -(a * I) - 2 * p * I := by
  field_simp
  ring

/-- For `|z| = 1` and `N ≥ 2` the Euler factor `1 − z N^{−s}` vanishes at a point of the
imaginary axis in the upper half-plane: `s = i (arg z + 2π) / log N`. -/
theorem exists_re_eq_zero_one_sub_mul_cpow_eq_zero {z : ℂ} (hz : ‖z‖ = 1) {N : ℕ}
    (hN : 2 ≤ N) : ∃ s : ℂ, s.re = 0 ∧ 0 < s.im ∧ 1 - z * (N : ℂ) ^ (-s) = 0 := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlogC : ((Real.log N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog.ne'
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
  have hθ : 0 < (Complex.arg z + 2 * Real.pi) / Real.log N :=
    div_pos (by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]) hlog
  have hz' : Complex.exp (Complex.arg z * Complex.I) = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rwa [hz, Complex.ofReal_one, one_mul] at h
  refine ⟨(((Complex.arg z + 2 * Real.pi) / Real.log N : ℝ) : ℂ) * Complex.I, ?_, ?_, ?_⟩
  · rw [Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  · rw [Complex.mul_I_im, Complex.ofReal_re]
    exact hθ
  · have hexp : (N : ℂ) ^ (-((((Complex.arg z + 2 * Real.pi) / Real.log N : ℝ) : ℂ) *
        Complex.I)) = Complex.exp (-(Complex.arg z * Complex.I) - 2 * Real.pi * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero hN0, ← Complex.natCast_log]
      congr 1
      rw [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
      exact mul_neg_div_mul_I _ _ _ hlogC
    rw [hexp, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one, Complex.exp_neg, hz',
      mul_inv_cancel₀ hz0, sub_self]

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-! ### The Gamma factor and the pole factor off the real axis -/

/-- **The Gamma factor is finite and non-zero off the real axis**: the poles of `Γ_ℝ` are real. -/
theorem heckeGammaFactor_ne_zero_of_im_ne_zero (ψ : HeckeCharacter 𝔪) {s : ℂ}
    (hs : s.im ≠ 0) : heckeGammaFactor 𝔪 ψ s ≠ 0 := by
  have hr : ∀ e : ℕ, Complex.Gammaℝ (s + (e : ℂ)) ≠ 0 := fun e h => by
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    have him : s.im = 0 := by simpa using congrArg Complex.im hn
    exact hs him
  have hc : Complex.Gammaℂ s ≠ 0 := by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (by simpa using hr 0) (by simpa using hr 1)
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hr _) (pow_ne_zero _ hc)

theorem heckePoleFactor_ne_zero_of_im_ne_zero (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : s.im ≠ 0) :
    heckePoleFactor 𝔪 ψ s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => hs (by rw [h, Complex.zero_im])
  have hs1 : s - 1 ≠ 0 := fun h => hs (by rw [sub_eq_zero.mp h, Complex.one_im])
  rw [heckePoleFactor]
  split_ifs
  · exact mul_ne_zero hs0 hs1
  · exact one_ne_zero

theorem differentiable_heckePoleFactor (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckePoleFactor 𝔪 ψ) := by
  by_cases h : ψ = 1
  · rw [heckePoleFactor_of_eq_one h]
    exact differentiable_id.mul (differentiable_id.sub_const 1)
  · rw [heckePoleFactor_of_ne_one h]
    exact differentiable_const _

/-! ### No zero of the completion outside the open critical strip -/

/-- **The completion does not vanish on `Re s ≥ 1`.** -/
theorem heckeXi_ne_zero_of_one_le_re (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 ≤ s.re) :
    heckeXi 𝔪 ψ s ≠ 0 := by
  have hs0 : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  by_cases hψ : ψ = 1
  · subst hψ
    by_cases hs1 : s = 1
    · rw [hs1]
      exact heckeXi_one_ne_zero 𝔪 1
    · intro h
      have h1 := heckeXi_one_mul_gamma_inv 𝔪 s
      rw [h, mul_zero, heckePoleCleared_eq 𝔪 1 hs1] at h1
      have hs0' : s ≠ 0 := fun h0 => by
        rw [h0, Complex.zero_re] at hs0
        exact lt_irrefl _ hs0
      exact (mul_ne_zero (mul_ne_zero hs0' (heckeCompletionFactor_ne_zero 𝔪 s))
        (mul_ne_zero (sub_ne_zero.mpr hs1)
          (heckeLFunction_ne_zero_of_one_le_re 𝔪 1 hs (Or.inr hs1)))) h1.symm
  · rw [Ne, heckeXi_eq_zero_iff 𝔪 hψ hs0]
    exact heckeLFunction_ne_zero_of_one_le_re 𝔪 ψ hs (Or.inl hψ)

/-- **The completion of a primitive character does not vanish on `Re s ≤ 0`**, by the
functional equation. -/
theorem heckeXi_ne_zero_of_re_le_zero (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : s.re ≤ 0) : heckeXi 𝔪 ψ s ≠ 0 := by
  have hFE := heckeXi_one_sub 𝔪 ψ hψ (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  exact mul_ne_zero (heckeRootNumber_ne_zero 𝔪 ψ hψ)
    (heckeXi_ne_zero_of_one_le_re 𝔪 ψ⁻¹ (by
      rw [Complex.sub_re, Complex.one_re]
      linarith))

/-! ### The Euler factors at the modulus -/

/-- `R_ψ(s) = Π_{v | 𝔪} (1 − ψ'(v) N v^{−s})`, `ψ'` the primitive character of `ψ`: the Euler
factors by which `L(s, ψ)` and `L(s, ψ')` differ. -/
def conductorEulerFactor (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
    (1 - heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))

theorem differentiable_conductorEulerFactor (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (conductorEulerFactor 𝔪 ψ) := by
  show Differentiable ℂ fun s : ℂ => ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
    (1 - heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
  exact Differentiable.fun_finsetProd fun v _ => (differentiable_const _).sub
    ((differentiable_const _).mul (differentiable_id.neg.const_cpow (Or.inl
      (Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)))))

/-- **A prime of the modulus outside the conductor gives a zero of `R_ψ` on the imaginary
axis**, off the real axis. -/
theorem exists_conductorEulerFactor_eq_zero (ψ : HeckeCharacter 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.fin)
    (hc : ¬ v.asIdeal ∣ heckeFiniteConductor 𝔪 ψ) :
    ∃ s : ℂ, s.re = 0 ∧ 0 < s.im ∧ conductorEulerFactor 𝔪 ψ s = 0 := by
  have hm : idealUnit v.ne_bot ∈ idealGroup (conductorModulus 𝔪 ψ) := by
    intro w hw
    rw [coe_idealUnit]
    exact FractionalIdeal.count_maximal_coprime K w (fun h => hc (h.symm ▸ hw))
  have hz : ‖heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal‖ = 1 := by
    rw [heckeValue_of_mem _ _ v.ne_bot hm]
    exact norm_char_eq_one _ _
  have hN : 2 ≤ Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h =>
      v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    omega
  obtain ⟨s, hre, him, hs⟩ := exists_re_eq_zero_one_sub_mul_cpow_eq_zero hz hN
  exact ⟨s, hre, him, Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).mpr hv) hs⟩

/-- The entire function `γ'(s)^{−1} Ξ'(s) R_ψ(s)`, `Ξ'` and `γ'` the completion and the Gamma
factor of the primitive character of `ψ`. -/
def rayClassEntire (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  (heckeGammaFactor (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s)⁻¹ *
    heckeXi (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s * conductorEulerFactor 𝔪 ψ s

theorem differentiable_rayClassEntire (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (rayClassEntire 𝔪 ψ) :=
  ((differentiable_heckeGammaFactor_inv _ _).mul (differentiable_heckeXi _ _)).mul
    (differentiable_conductorEulerFactor 𝔪 ψ)

/-- On `Re s > 1`: `γ'(s)^{−1} Ξ'(s) R_ψ(s) = P'(s) c'(s) L(s, ψ)`. -/
theorem rayClassEntire_eq (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    rayClassEntire 𝔪 ψ s =
      heckePoleFactor (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s *
        heckeCompletionFactor (conductorModulus 𝔪 ψ) s * heckeL 𝔪 ψ s := by
  have hγ := heckeGammaFactor_ne_zero (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
    (zero_lt_one.trans hs)
  rw [rayClassEntire, heckeXi_eq _ _ hs, heckeL_eq_heckeL_primitiveHecke_mul 𝔪 ψ hs]
  have hR : conductorEulerFactor 𝔪 ψ s = ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
      (1 - heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := rfl
  rw [hR]
  generalize (∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
    (1 - heckeValue (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) v.asIdeal *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) = R
  generalize heckeGammaFactor (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s = γ at hγ ⊢
  field_simp

/-! ### The theorem -/

/-- **In a factorization of a Dedekind zeta function into ray class `L`-series every prime of
a modulus divides the conductor.** If `ζ_M(s) = Π_i L(s, ψ_i)` for `Re s > 1`, with `ψ_i` a ray
class character modulo `𝔪_i` of a number field `K`, then every prime dividing `𝔪_i` divides the
conductor of `ψ_i`. -/
theorem dvd_heckeFiniteConductor_of_dedekindZeta_eq_prod (M : Type*) [Field M] [NumberField M]
    {ι : Type*} [Fintype ι] (𝔪 : ι → Modulus K) (ψ : ∀ i, HeckeCharacter (𝔪 i))
    (h : ∀ s : ℂ, 1 < s.re → dedekindZeta M s = ∏ i, heckeL (𝔪 i) (ψ i) s)
    (i : ι) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ (𝔪 i).fin) :
    v.asIdeal ∣ heckeFiniteConductor (𝔪 i) (ψ i) := by
  by_contra hc
  obtain ⟨s₀, hre, him, hzero⟩ := exists_conductorEulerFactor_eq_zero (𝔪 i) (ψ i) hv hc
  -- the two entire functions
  have hF : AnalyticOnNhd ℂ (fun s => heckePoleCleared (trivialModulus M) 1 s *
      ∏ j, (heckePoleFactor (conductorModulus (𝔪 j) (ψ j)) (primitiveHecke (𝔪 j) (ψ j)) s *
        heckeCompletionFactor (conductorModulus (𝔪 j) (ψ j)) s)) univ := fun z _ =>
    ((differentiable_heckePoleCleared (trivialModulus M) 1).mul
      (Differentiable.fun_finsetProd fun j _ => (differentiable_heckePoleFactor _ _).mul
        (differentiable_heckeCompletionFactor _))).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s => (s - 1) * ∏ j, rayClassEntire (𝔪 j) (ψ j) s) univ :=
    fun z _ => ((differentiable_id.sub_const 1).mul
      (Differentiable.fun_finsetProd fun j _ => differentiable_rayClassEntire _ _)).analyticAt z
  -- they agree on `Re s > 1`
  have he : (fun s => heckePoleCleared (trivialModulus M) 1 s *
      ∏ j, (heckePoleFactor (conductorModulus (𝔪 j) (ψ j)) (primitiveHecke (𝔪 j) (ψ j)) s *
        heckeCompletionFactor (conductorModulus (𝔪 j) (ψ j)) s)) =ᶠ[𝓝 (2 : ℂ)]
      fun s => (s - 1) * ∏ j, rayClassEntire (𝔪 j) (ψ j) s := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hprod : ∏ j, rayClassEntire (𝔪 j) (ψ j) z =
        (∏ j, (heckePoleFactor (conductorModulus (𝔪 j) (ψ j)) (primitiveHecke (𝔪 j) (ψ j)) z *
          heckeCompletionFactor (conductorModulus (𝔪 j) (ψ j)) z)) *
            ∏ j, heckeL (𝔪 j) (ψ j) z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => rayClassEntire_eq (𝔪 j) (ψ j) hz'
    rw [hprod, heckePoleCleared_eq_heckeL (trivialModulus M) 1 hz', heckeL_trivialModulus_one,
      h z hz']
    ring
  have hEq : heckePoleCleared (trivialModulus M) 1 s₀ *
      ∏ j, (heckePoleFactor (conductorModulus (𝔪 j) (ψ j)) (primitiveHecke (𝔪 j) (ψ j)) s₀ *
        heckeCompletionFactor (conductorModulus (𝔪 j) (ψ j)) s₀) =
      (s₀ - 1) * ∏ j, rayClassEntire (𝔪 j) (ψ j) s₀ :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_univ (mem_univ _) he (mem_univ s₀)
  -- the right side vanishes at `s₀`
  have hi : rayClassEntire (𝔪 i) (ψ i) s₀ = 0 := by rw [rayClassEntire, hzero, mul_zero]
  have hG0 : ∏ j, rayClassEntire (𝔪 j) (ψ j) s₀ = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [hG0, mul_zero] at hEq
  rcases mul_eq_zero.mp hEq with hE | hP
  · -- `E_M(s₀) = 0` gives a zero of the completion of `ζ_M` on `Re s = 0`
    have h1 := heckeXi_one_mul_gamma_inv (trivialModulus M) s₀
    rw [hE, mul_zero] at h1
    exact mul_ne_zero
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_im_ne_zero (trivialModulus M) 1 him.ne'))
      (heckeXi_ne_zero_of_re_le_zero (trivialModulus M) 1
        (heckeFiniteConductor_trivialModulus M 1) hre.le) h1
  · obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hP
    exact mul_ne_zero (heckePoleFactor_ne_zero_of_im_ne_zero _ _ him.ne')
      (heckeCompletionFactor_ne_zero _ s₀) hj

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
