import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheZerosOfARayClassLFunctionAreTheZerosOfItsPrimitiveCharacter
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexOfAVirtualConfigurationCountsItsZerosAndItsPoles

/-!
# The orders of a ray class `L`-function are the multiplicities of its configuration

Let `ψ` be a ray class character modulo `𝔪` of a number field, primitive or not, trivial or not,
`ψ'` its primitive character, `Ξ` the entire completion of `ψ'` and `Z_ψ` its configuration
(`rayClassZeros`). Put

  `E_ψ(s) = (s − 1) L(s, ψ)`  (`heckePoleCleared`),

an entire function: `L(s, ψ) = R(s) + κ / (s − 1)` with `R` entire.

**Theorem** (`analyticOrderNatAt_heckePoleCleared`). For `Re ρ > 0`,

  `ord_ρ E_ψ = m_{Z_ψ}(ρ) + [ρ = 1][ψ ≠ 1]`.

So the order of `L(s, ψ)` at a point `ρ ≠ 1` right of `0` is the multiplicity of `ρ` in the
configuration, and `1` is not a point of the configuration (`one_notMem_rayClassZeros`).

Proof. With `c` the conductor factor and `γ` the Gamma factor, without zeros in `Re s > 0` and
with `1/γ` entire: `c E_ψ = (s − 1) Ξ / γ` for a character `ψ ≠ 1` (`ψ` in place of `ψ'`), and
`Ξ / γ = s c E_ψ` for `ψ = 1`, on `Re s > 1` and so on `ℂ`. And `E_ψ = E_{ψ'} M` with `M` the
Euler factors of `ψ'` at the primes of `𝔪`, without zeros in `Re s > 0`. Orders add. At `1`:
`E_ψ(1) = κ ≠ 0` for `ψ = 1`, and `L(1, ψ) ≠ 0` for `ψ ≠ 1`.
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions HTGeometry IsDedekindDomain

/-! ### Orders of products -/

/-- The order of a product is the sum of the orders. -/
theorem analyticOrderAt_fun_mul {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) :
    analyticOrderAt (fun s => f s * g s) z = analyticOrderAt f z + analyticOrderAt g z :=
  analyticOrderAt_mul hf hg

/-- A factor without zero at the point does not change the order. -/
theorem analyticOrderAt_fun_mul_of_ne_zero {u g : ℂ → ℂ} {z : ℂ} (hu : AnalyticAt ℂ u z)
    (hu0 : u z ≠ 0) (hg : AnalyticAt ℂ g z) :
    analyticOrderAt (fun s => u s * g s) z = analyticOrderAt g z := by
  rw [analyticOrderAt_fun_mul hu hg, hu.analyticOrderAt_eq_zero.mpr hu0, zero_add]

/-- The order of `s − 1`: one at `1`, zero elsewhere. -/
theorem analyticOrderAt_sub_one (z : ℂ) :
    analyticOrderAt (fun s : ℂ => s - 1) z = if z = 1 then 1 else 0 := by
  have ha : AnalyticAt ℂ (fun s : ℂ => s - 1) z := analyticAt_id.sub analyticAt_const
  split_ifs with h
  · subst h
    have h1 := (analyticAt_id (𝕜 := ℂ) (z := 1)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero
      (by simp)
    simpa using h1
  · exact ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr h)

/-- An entire function with a value `≠ 0` has finite order at every point. -/
theorem analyticOrderAt_ne_top_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) {w : ℂ}
    (hw : f w ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  exact (han.exists_analyticOrderAt_ne_top_iff_forall isConnected_univ).mp
    ⟨⟨w, mem_univ w⟩, by
      rw [(han w (mem_univ w)).analyticOrderAt_eq_zero.mpr hw]
      exact ENat.zero_ne_top⟩ ⟨z, mem_univ z⟩

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-! ### The `L`-function with its pole cleared -/

/-- `E_ψ(s) = (s − 1) L(s, ψ)`, with the value `κ` at `1`: an entire function. -/
def heckePoleCleared (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  (s - 1) * heckeEntireRegularPart 𝔪 ψ s + heckeThetaPoleCoefficient 𝔪 ψ

theorem differentiable_heckePoleCleared (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckePoleCleared 𝔪 ψ) :=
  ((differentiable_id.sub_const 1).mul (differentiable_heckeEntireRegularPart 𝔪 ψ)).add_const _

theorem heckePoleCleared_eq (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : s ≠ 1) :
    heckePoleCleared 𝔪 ψ s = (s - 1) * heckeLFunction 𝔪 ψ s := by
  have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [heckePoleCleared, heckeLFunction, mul_add, mul_div_cancel₀ _ hn]

theorem heckePoleCleared_one (ψ : HeckeCharacter 𝔪) :
    heckePoleCleared 𝔪 ψ 1 = heckeThetaPoleCoefficient 𝔪 ψ := by
  rw [heckePoleCleared, sub_self, zero_mul, zero_add]

theorem ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  rw [Complex.one_re] at hs
  exact lt_irrefl _ hs

theorem heckePoleCleared_eq_heckeL (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckePoleCleared 𝔪 ψ s = (s - 1) * heckeL 𝔪 ψ s := by
  rw [heckePoleCleared_eq 𝔪 ψ (ne_one_of_one_lt_re hs), heckeLFunction_eq_heckeL 𝔪 ψ hs]

/-- For a nontrivial character `E_ψ = (s − 1) L(s, ψ)` at every point. -/
theorem heckePoleCleared_of_ne_one {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) (s : ℂ) :
    heckePoleCleared 𝔪 ψ s = (s - 1) * heckeLFunction 𝔪 ψ s := by
  rw [heckePoleCleared, heckeLFunction, heckeThetaPoleCoefficient_eq_zero 𝔪 hψ, zero_div,
    add_zero, add_zero]

theorem heckePoleCleared_two_ne_zero (ψ : HeckeCharacter 𝔪) : heckePoleCleared 𝔪 ψ 2 ≠ 0 := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  rw [heckePoleCleared_eq_heckeL 𝔪 ψ h2]
  exact mul_ne_zero (by norm_num) (heckeL_ne_zero 𝔪 ψ h2)

theorem analyticOrderAt_heckePoleCleared_ne_top (ψ : HeckeCharacter 𝔪) (z : ℂ) :
    analyticOrderAt (heckePoleCleared 𝔪 ψ) z ≠ ⊤ :=
  analyticOrderAt_ne_top_of_differentiable (differentiable_heckePoleCleared 𝔪 ψ)
    (heckePoleCleared_two_ne_zero 𝔪 ψ) z

/-! ### The completion -/

/-- For `ψ ≠ 1`: `c(s) E_ψ(s) = (1/γ(s)) (s − 1) Ξ_ψ(s)`. -/
theorem completionFactor_mul_heckePoleCleared {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) (s : ℂ) :
    heckeCompletionFactor 𝔪 s * heckePoleCleared 𝔪 ψ s =
      (heckeGammaFactor 𝔪 ψ s)⁻¹ * ((s - 1) * heckeXi 𝔪 ψ s) := by
  rw [heckePoleCleared_of_ne_one 𝔪 hψ, heckeXi_of_ne_one hψ, heckeCompletedLFunction,
    ← heckeGammaCompletedLFunction_mul_gamma_inv 𝔪 hψ s]
  ring

/-- For the trivial character: `Ξ(s) / γ(s) = s c(s) E(s)`. -/
theorem heckeXi_one_mul_gamma_inv (s : ℂ) :
    (heckeGammaFactor 𝔪 1 s)⁻¹ * heckeXi 𝔪 1 s =
      s * heckeCompletionFactor 𝔪 s * heckePoleCleared 𝔪 1 s := by
  have hf : AnalyticOnNhd ℂ (fun z => (heckeGammaFactor 𝔪 1 z)⁻¹ * heckeXi 𝔪 1 z) univ :=
    fun z _ => ((differentiable_heckeGammaFactor_inv 𝔪 1).mul
      (differentiable_heckeXi 𝔪 1)).analyticAt z
  have hg : AnalyticOnNhd ℂ
      (fun z => z * heckeCompletionFactor 𝔪 z * heckePoleCleared 𝔪 1 z) univ :=
    fun z _ => ((differentiable_id.mul (differentiable_heckeCompletionFactor 𝔪)).mul
      (differentiable_heckePoleCleared 𝔪 1)).analyticAt z
  have he : (fun z => (heckeGammaFactor 𝔪 1 z)⁻¹ * heckeXi 𝔪 1 z) =ᶠ[𝓝 (2 : ℂ)]
      fun z => z * heckeCompletionFactor 𝔪 z * heckePoleCleared 𝔪 1 z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hγ := heckeGammaFactor_ne_zero 𝔪 (1 : HeckeCharacter 𝔪) (zero_lt_one.trans hz')
    rw [heckeXi_eq 𝔪 1 hz', heckePoleFactor_of_eq_one rfl, heckePoleCleared_eq_heckeL 𝔪 1 hz']
    field_simp
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) he
    (mem_univ s)

/-- **The completion does not vanish at `1`**, for every ray class character. -/
theorem heckeXi_one_ne_zero (ψ : HeckeCharacter 𝔪) : heckeXi 𝔪 ψ 1 ≠ 0 := by
  by_cases hψ : ψ = 1
  · subst hψ
    intro h
    have h1 := heckeXi_one_mul_gamma_inv 𝔪 (1 : ℂ)
    rw [h, mul_zero, one_mul, heckePoleCleared_one, heckeThetaPoleCoefficient_one] at h1
    exact (mul_ne_zero (heckeCompletionFactor_ne_zero 𝔪 1)
      (by exact_mod_cast (heckeDensity_pos 𝔪).ne')) h1.symm
  · rw [Ne, heckeXi_eq_zero_iff 𝔪 hψ (by simp)]
    exact heckeLFunction_one_ne_zero 𝔪 hψ

/-- **The order of `E_ψ` through the completion of `ψ`**, for `Re ρ > 0`. -/
theorem analyticOrderAt_heckePoleCleared_eq_heckeXi (ψ : HeckeCharacter 𝔪) {ρ : ℂ}
    (hρ : 0 < ρ.re) :
    analyticOrderAt (heckePoleCleared 𝔪 ψ) ρ =
      analyticOrderAt (heckeXi 𝔪 ψ) ρ + if ψ ≠ 1 ∧ ρ = 1 then 1 else 0 := by
  have hE := (differentiable_heckePoleCleared 𝔪 ψ).analyticAt ρ
  have hXi := (differentiable_heckeXi 𝔪 ψ).analyticAt ρ
  have hc := (differentiable_heckeCompletionFactor 𝔪).analyticAt ρ
  have hγ := (differentiable_heckeGammaFactor_inv 𝔪 ψ).analyticAt ρ
  have hγ0 : (heckeGammaFactor 𝔪 ψ ρ)⁻¹ ≠ 0 := inv_ne_zero (heckeGammaFactor_ne_zero 𝔪 ψ hρ)
  have hsub : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := analyticAt_id.sub analyticAt_const
  by_cases hψ : ψ = 1
  · subst hψ
    have hid : (fun s => (heckeGammaFactor 𝔪 1 s)⁻¹ * heckeXi 𝔪 1 s) =
        fun s => s * heckeCompletionFactor 𝔪 s * heckePoleCleared 𝔪 1 s :=
      funext (heckeXi_one_mul_gamma_inv 𝔪)
    have h1 := analyticOrderAt_fun_mul_of_ne_zero hγ hγ0 hXi
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      rw [Complex.zero_re] at hρ
      exact lt_irrefl _ hρ
    have h2 := analyticOrderAt_fun_mul_of_ne_zero (analyticAt_id.mul hc)
      (show ρ * heckeCompletionFactor 𝔪 ρ ≠ 0 from
        mul_ne_zero hρ0 (heckeCompletionFactor_ne_zero 𝔪 ρ)) hE
    rw [if_neg fun h => h.1 rfl, add_zero, ← h1, hid]
    exact h2.symm
  · have hid : (fun s => heckeCompletionFactor 𝔪 s * heckePoleCleared 𝔪 ψ s) =
        fun s => (heckeGammaFactor 𝔪 ψ s)⁻¹ * ((s - 1) * heckeXi 𝔪 ψ s) :=
      funext (completionFactor_mul_heckePoleCleared 𝔪 hψ)
    have h1 := analyticOrderAt_fun_mul_of_ne_zero hc (heckeCompletionFactor_ne_zero 𝔪 ρ) hE
    have h2 := analyticOrderAt_fun_mul_of_ne_zero hγ hγ0 (hsub.mul hXi)
    have h3 := analyticOrderAt_fun_mul hsub hXi
    rw [← h1, hid]
    refine h2.trans (h3.trans ?_)
    rw [analyticOrderAt_sub_one, add_comm]
    by_cases h1ρ : ρ = 1
    · rw [if_pos h1ρ, if_pos ⟨hψ, h1ρ⟩]
    · rw [if_neg h1ρ, if_neg fun h => h1ρ h.2]

/-! ### The primitive character and the configuration -/

/-- `E_ψ = E_{ψ'} M`, with `M` the Euler factors of the primitive character `ψ'` at the primes
of the modulus. -/
theorem heckePoleCleared_eq_primitiveHecke_mul (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckePoleCleared 𝔪 ψ s =
      heckePoleCleared (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s *
        modulusEulerFactor 𝔪 ψ s := by
  have hf : AnalyticOnNhd ℂ (heckePoleCleared 𝔪 ψ) univ := fun z _ =>
    (differentiable_heckePoleCleared 𝔪 ψ).analyticAt z
  have hg : AnalyticOnNhd ℂ (fun z => heckePoleCleared (conductorModulus 𝔪 ψ)
      (primitiveHecke 𝔪 ψ) z * modulusEulerFactor 𝔪 ψ z) univ := fun z _ =>
    ((differentiable_heckePoleCleared (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)).mul
      (differentiable_modulusEulerFactor 𝔪 ψ)).analyticAt z
  have he : heckePoleCleared 𝔪 ψ =ᶠ[𝓝 (2 : ℂ)] fun z =>
      heckePoleCleared (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) z *
        modulusEulerFactor 𝔪 ψ z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    rw [heckePoleCleared_eq_heckeL 𝔪 ψ hz', heckePoleCleared_eq_heckeL _ _ hz', mul_assoc]
    exact congrArg ((z - 1) * ·) (heckeL_eq_heckeL_primitiveHecke_mul 𝔪 ψ hz')
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) he
    (mem_univ s)

/-- The multiplicity of a point in the configuration of a primitive character is the order of
its completion. -/
theorem extMult_heckeZeros (ψ : HeckeCharacter 𝔪) (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (ρ : ℂ) :
    (extMult (heckeZeros 𝔪 ψ hψ) ρ : ℕ∞) =
      analyticOrderAt (heckeXi 𝔪 ψ) ρ := by
  have htop : analyticOrderAt (heckeXi 𝔪 ψ) ρ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_differentiable (differentiable_heckeXi 𝔪 ψ)
      (heckeXi_two_ne_zero 𝔪 ψ) ρ
  unfold extMult
  by_cases h : heckeXi 𝔪 ψ ρ = 0
  · rw [if_pos (show ρ ∈ (heckeZeros 𝔪 ψ hψ).carrier from h)]
    exact ENat.coe_toNat htop
  · rw [if_neg (show ρ ∉ (heckeZeros 𝔪 ψ hψ).carrier from h),
      ((differentiable_heckeXi 𝔪 ψ).analyticAt ρ).analyticOrderAt_eq_zero.mpr h]
    rfl

/-- **The point `1` is not in the configuration of a ray class character.** -/
theorem one_notMem_rayClassZeros (ψ : HeckeCharacter 𝔪) :
    (1 : ℂ) ∉ (rayClassZeros 𝔪 ψ).carrier :=
  fun h => heckeXi_one_ne_zero (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) h

/-- **The orders of `E_ψ(s) = (s − 1) L(s, ψ)` are the multiplicities of the configuration**:
for `Re ρ > 0`, `ord_ρ E_ψ = m_{Z_ψ}(ρ) + [ρ = 1][ψ ≠ 1]`. -/
theorem analyticOrderNatAt_heckePoleCleared (ψ : HeckeCharacter 𝔪) {ρ : ℂ} (hρ : 0 < ρ.re) :
    analyticOrderNatAt (heckePoleCleared 𝔪 ψ) ρ =
      extMult (rayClassZeros 𝔪 ψ) ρ +
        if ψ ≠ 1 ∧ ρ = 1 then 1 else 0 := by
  have hE := (differentiable_heckePoleCleared (conductorModulus 𝔪 ψ)
    (primitiveHecke 𝔪 ψ)).analyticAt ρ
  have hM := (differentiable_modulusEulerFactor 𝔪 ψ).analyticAt ρ
  -- the Euler factors at the modulus have order zero
  have h1 : analyticOrderAt (heckePoleCleared 𝔪 ψ) ρ =
      analyticOrderAt (heckePoleCleared (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)) ρ := by
    have hid : heckePoleCleared 𝔪 ψ = fun s => modulusEulerFactor 𝔪 ψ s *
        heckePoleCleared (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ) s :=
      funext fun s => (heckePoleCleared_eq_primitiveHecke_mul 𝔪 ψ s).trans (mul_comm _ _)
    rw [hid]
    exact analyticOrderAt_fun_mul_of_ne_zero hM (modulusEulerFactor_ne_zero 𝔪 ψ hρ) hE
  have h2 := analyticOrderAt_heckePoleCleared_eq_heckeXi (conductorModulus 𝔪 ψ)
    (primitiveHecke 𝔪 ψ) hρ
  have h3 := extMult_heckeZeros (conductorModulus 𝔪 ψ) (primitiveHecke 𝔪 ψ)
    (heckeFiniteConductor_primitiveHecke 𝔪 ψ) ρ
  have hiff : (primitiveHecke 𝔪 ψ ≠ 1 ∧ ρ = 1) ↔ (ψ ≠ 1 ∧ ρ = 1) :=
    and_congr_left fun _ => not_congr (primitiveHecke_eq_one_iff 𝔪 ψ)
  have h4 : analyticOrderAt (heckePoleCleared 𝔪 ψ) ρ =
      ((extMult (rayClassZeros 𝔪 ψ) ρ +
        (if ψ ≠ 1 ∧ ρ = 1 then 1 else 0) : ℕ) : ℕ∞) := by
    rw [h1, h2, ← h3, if_congr hiff rfl rfl, Nat.cast_add]
    congr 1
    split_ifs <;> rfl
  rw [analyticOrderNatAt, h4]
  rfl

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
