import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheLogarithmicDerivativeOfAHeckeLSeriesRunsOverThePowersOfThePrimeIdeals
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCompletedFunctionOfAPrimitiveHeckeCharacterHasOrderOne
import GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsAreInverseHeckeValues
import GaloisForLFunctions.RHTower.WeilFunctionalLineIntegral
import Zeta23.ThmE.FullLineChiProof
import Zeta23.RvM.Fold

/-!
# The logarithmic derivative of a completed Hecke function: poles, Gamma factors, prime ideals

For a ray class character `ψ` of a number field the entire completion is

`Ξ_ψ(s) = P_ψ(s) N^{s/2} Π_{v real} Γ_ℝ(s + κ_v) Γ_ℂ(s)^{r₂} L(s, ψ)`   (`heckeXi`, `heckeXi_eq`),

with `P_ψ = s(s − 1)` for the trivial character and `P_ψ = 1` otherwise.

* **Reflection** (`heckeXi_one_sub`): `Ξ_ψ(1 − s) = W Ξ_{ψ⁻¹}(s)` for a primitive `ψ`.
* **Conjugation** (`heckeXi_inv_conj`): `Ξ_{ψ⁻¹}(s̄) = conj Ξ_ψ(s)`: the values of `ψ⁻¹` are the
  conjugates of those of `ψ`, and the Gamma and conductor factors are real on the real axis.
* **Order one** (`exists_orderOne_heckeXi`), no zero on `Re s > 1` (`heckeXi_ne_zero`).
* **Logarithmic derivative** (`logDeriv_heckeXi`): on `Re s > 1`,
  `Ξ'/Ξ(s) = m_ψ (1/s + 1/(s − 1)) + G_ψ(s) − Σ_n Λ_ψ(n) n^{−s}`, `m_ψ` the order of the pole
  (`heckePole`), `G_ψ` the logarithmic derivative of the conductor and Gamma factors
  (`heckeArch`), holomorphic on `Re s > 0` with logarithmic growth on `1/2 ≤ Re s ≤ 3/2`.
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical nonZeroDivisors ComplexConjugate

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens
open RHTower.WeilLineIntegral

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-! ### The entire completion -/

/-- The entire completion of `L(s, ψ)`: the completed function, its two poles cleared by
`s(s − 1)` for the trivial character. -/
def heckeXi (ψ : HeckeCharacter 𝔪) : ℂ → ℂ :=
  if ψ = 1 then heckePoleClearedCompletion 𝔪 ψ else heckeCompletedLFunction 𝔪 ψ

/-- The order of the pole of `L(s, ψ)` at `1`. -/
def heckePole (ψ : HeckeCharacter 𝔪) : ℂ := if ψ = 1 then 1 else 0

/-- The polynomial that clears the poles. -/
def heckePoleFactor (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ := if ψ = 1 then s * (s - 1) else 1

variable {𝔪}

theorem heckeXi_of_eq_one {ψ : HeckeCharacter 𝔪} (h : ψ = 1) :
    heckeXi 𝔪 ψ = heckePoleClearedCompletion 𝔪 ψ := if_pos h

theorem heckeXi_of_ne_one {ψ : HeckeCharacter 𝔪} (h : ψ ≠ 1) :
    heckeXi 𝔪 ψ = heckeCompletedLFunction 𝔪 ψ := if_neg h

theorem heckePoleFactor_of_eq_one {ψ : HeckeCharacter 𝔪} (h : ψ = 1) :
    heckePoleFactor 𝔪 ψ = fun z : ℂ => z * (z - 1) := by
  funext z
  rw [heckePoleFactor, if_pos h]

theorem heckePoleFactor_of_ne_one {ψ : HeckeCharacter 𝔪} (h : ψ ≠ 1) :
    heckePoleFactor 𝔪 ψ = fun _ : ℂ => (1 : ℂ) := by
  funext z
  rw [heckePoleFactor, if_neg h]

theorem hecke_inv_eq_one_iff {ψ : HeckeCharacter 𝔪} : ψ⁻¹ = 1 ↔ ψ = 1 := by
  constructor
  · intro h
    by_contra h1
    exact inv_ne_one_of_ne_one 𝔪 h1 h
  · rintro rfl
    apply MonoidHom.ext
    intro g
    change ((1 : HeckeCharacter 𝔪) g)⁻¹ = (1 : HeckeCharacter 𝔪) g
    simp

variable (𝔪)

/-- **The completion on `Re s > 1`.** -/
theorem heckeXi_eq (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeXi 𝔪 ψ s = heckePoleFactor 𝔪 ψ s *
      (heckeCompletionFactor 𝔪 s * heckeGammaFactor 𝔪 ψ s * heckeL 𝔪 ψ s) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [Complex.one_re] at hs
    linarith
  by_cases h : ψ = 1
  · rw [heckeXi_of_eq_one h, heckePoleFactor_of_eq_one h,
      heckePoleClearedCompletion_eq 𝔪 ψ hs0 hs1, heckeCompletedLFunction_eq 𝔪 ψ hs]
  · rw [heckeXi_of_ne_one h, heckePoleFactor_of_ne_one h, one_mul,
      heckeCompletedLFunction_eq 𝔪 ψ hs]

theorem differentiable_heckeXi (ψ : HeckeCharacter 𝔪) : Differentiable ℂ (heckeXi 𝔪 ψ) := by
  by_cases h : ψ = 1
  · rw [heckeXi_of_eq_one h]
    exact differentiable_heckePoleClearedCompletion 𝔪 ψ
  · rw [heckeXi_of_ne_one h]
    exact differentiable_heckeCompletedLFunction 𝔪 h

/-- **Reflection.** -/
theorem heckeXi_one_sub (ψ : HeckeCharacter 𝔪) (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (s : ℂ) : heckeXi 𝔪 ψ (1 - s) = heckeRootNumber 𝔪 ψ * heckeXi 𝔪 ψ⁻¹ s := by
  by_cases h : ψ = 1
  · rw [heckeXi_of_eq_one h, heckeXi_of_eq_one (hecke_inv_eq_one_iff.mpr h)]
    exact heckePoleClearedCompletion_reflection 𝔪 ψ hψ s
  · rw [heckeXi_of_ne_one h, heckeXi_of_ne_one (inv_ne_one_of_ne_one 𝔪 h)]
    exact heckeCompletedLFunction_reflection_entire 𝔪 hψ h s

/-- **Order one.** -/
theorem exists_orderOne_heckeXi (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖heckeXi 𝔪 ψ s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  by_cases h : ψ = 1
  · rw [heckeXi_of_eq_one h]
    exact exists_orderOne_heckePoleClearedCompletion 𝔪 ψ hψ
  · rw [heckeXi_of_ne_one h]
    exact exists_orderOne_heckeCompletedLFunction 𝔪 hψ h

theorem heckePoleFactor_ne_zero (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckePoleFactor 𝔪 ψ s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Complex.zero_re] at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [heckePoleFactor]
  split_ifs
  · exact mul_ne_zero hs0 hs1
  · exact one_ne_zero

/-- **No zero right of `1`.** -/
theorem heckeXi_ne_zero (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeXi 𝔪 ψ s ≠ 0 := by
  rw [heckeXi_eq 𝔪 ψ hs]
  exact mul_ne_zero (heckePoleFactor_ne_zero 𝔪 ψ hs)
    (mul_ne_zero (mul_ne_zero (heckeCompletionFactor_ne_zero 𝔪 s)
      (heckeGammaFactor_ne_zero 𝔪 ψ (by linarith))) (heckeL_ne_zero 𝔪 ψ hs))

/-! ### Conjugation -/

/-- The values of the inverse character are the conjugates. -/
theorem heckeValue_inv_eq_conj (ψ : HeckeCharacter 𝔪) (I : Ideal (𝓞 K)) :
    heckeValue 𝔪 ψ⁻¹ I = conj (heckeValue 𝔪 ψ I) := by
  rw [heckeValue_inv]
  by_cases h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := h
    rw [heckeValue_of_mem 𝔪 ψ hI hm]
    exact Complex.inv_eq_conj (norm_char_eq_one ψ _)
  · rw [heckeValue_of_not_mem 𝔪 ψ h, inv_zero, map_zero]

theorem heckeCoeff_inv (ψ : HeckeCharacter 𝔪) (n : ℕ) :
    heckeCoeff 𝔪 ψ⁻¹ n = conj (heckeCoeff 𝔪 ψ n) := by
  rw [heckeCoeff, heckeCoeff, map_sum]
  exact Finset.sum_congr rfl fun I _ => heckeValue_inv_eq_conj 𝔪 ψ I

theorem heckeL_inv_conj (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeL 𝔪 ψ⁻¹ (conj s) = conj (heckeL 𝔪 ψ s) := by
  show LSeries (heckeCoeff 𝔪 ψ⁻¹) (conj s) = conj (LSeries (heckeCoeff 𝔪 ψ) s)
  unfold LSeries
  have hstar : (starRingEnd ℂ) (∑' n, LSeries.term (heckeCoeff 𝔪 ψ) s n) =
      ∑' n, star (LSeries.term (heckeCoeff 𝔪 ψ) s n) := tsum_star
  rw [hstar]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Ne.symm Real.pi_ne_zero
    have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
      have h := Complex.cpow_conj (n : ℂ) s harg
      rwa [Complex.conj_natCast] at h
    simp only [LSeries.term, hn.ne', if_false, star_div₀]
    rw [heckeCoeff_inv 𝔪 ψ n]
    simp only [← starRingEnd_apply]
    rw [hpow]

theorem heckeCompletionFactor_conj (s : ℂ) :
    heckeCompletionFactor 𝔪 (conj s) = conj (heckeCompletionFactor 𝔪 s) := by
  have harg : ((heckeCompletionNorm 𝔪 : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Ne.symm Real.pi_ne_zero
  have h := Complex.cpow_conj ((heckeCompletionNorm 𝔪 : ℕ) : ℂ) (s / 2) harg
  rw [Complex.conj_natCast] at h
  rw [heckeCompletionFactor, heckeCompletionFactor, ← h]
  congr 1
  rw [map_div₀, map_ofNat]

theorem heckeGammaFactor_conj (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeGammaFactor 𝔪 ψ (conj s) = conj (heckeGammaFactor 𝔪 ψ s) := by
  have hC : ∀ z : ℂ, Complex.Gammaℂ (conj z) = conj (Complex.Gammaℂ z) := fun z => by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one, ← Complex.Gammaℝ_mul_Gammaℝ_add_one z, map_mul,
      ← Zeta23.RvM.Gammaℝ_conj, ← Zeta23.RvM.Gammaℝ_conj, map_add, map_one]
  unfold heckeGammaFactor
  rw [map_mul, map_prod, map_pow, hC]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Zeta23.RvM.Gammaℝ_conj, map_add, Complex.conj_natCast]

theorem heckePole_inv (ψ : HeckeCharacter 𝔪) : heckePole 𝔪 ψ⁻¹ = heckePole 𝔪 ψ := by
  unfold heckePole
  by_cases h : ψ = 1
  · rw [if_pos h, if_pos (hecke_inv_eq_one_iff.mpr h)]
  · rw [if_neg h, if_neg (inv_ne_one_of_ne_one 𝔪 h)]

theorem heckePoleFactor_inv_conj (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckePoleFactor 𝔪 ψ⁻¹ (conj s) = conj (heckePoleFactor 𝔪 ψ s) := by
  unfold heckePoleFactor
  by_cases h : ψ = 1
  · rw [if_pos h, if_pos (hecke_inv_eq_one_iff.mpr h), map_mul, map_sub, map_one]
  · rw [if_neg h, if_neg (inv_ne_one_of_ne_one 𝔪 h), map_one]

theorem heckeXi_inv_conj_of_one_lt_re (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeXi 𝔪 ψ⁻¹ (conj s) = conj (heckeXi 𝔪 ψ s) := by
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  rw [heckeXi_eq 𝔪 ψ⁻¹ hs', heckeXi_eq 𝔪 ψ hs, map_mul, map_mul, map_mul,
    heckeCompletionFactor_conj, heckeGammaFactor_inv, heckeGammaFactor_conj, heckeL_inv_conj,
    heckePoleFactor_inv_conj]

/-- **Conjugation.** `Ξ_{ψ⁻¹}(s̄) = conj Ξ_ψ(s)`. -/
theorem heckeXi_inv_conj (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeXi 𝔪 ψ⁻¹ (conj s) = conj (heckeXi 𝔪 ψ s) := by
  have h1 : AnalyticOnNhd ℂ (heckeXi 𝔪 ψ) univ :=
    (differentiable_heckeXi 𝔪 ψ).differentiableOn.analyticOnNhd isOpen_univ
  have h2 : AnalyticOnNhd ℂ (fun z => conj (heckeXi 𝔪 ψ⁻¹ (conj z))) univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) isOpen_univ
    have hd : DifferentiableAt ℂ (heckeXi 𝔪 ψ⁻¹) (conj z) := differentiable_heckeXi 𝔪 ψ⁻¹ _
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have hagree : (fun z => conj (heckeXi 𝔪 ψ⁻¹ (conj z))) =ᶠ[𝓝 (2 : ℂ)] heckeXi 𝔪 ψ := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    rw [heckeXi_inv_conj_of_one_lt_re 𝔪 ψ hz, Complex.conj_conj]
  have heq := h2.eqOn_of_preconnected_of_eventuallyEq h1 isPreconnected_univ
    (mem_univ (2 : ℂ)) hagree (mem_univ s)
  have hc := congrArg (starRingEnd ℂ) heq
  simpa using hc

/-! ### The archimedean term -/

/-- The logarithmic derivative of the conductor and Gamma factors of `L(s, ψ)`:
`½ log N + Σ_{v real} (Γ_ℝ'/Γ_ℝ)(s + κ_v) + r₂ ((Γ_ℝ'/Γ_ℝ)(s) + (Γ_ℝ'/Γ_ℝ)(s + 1))`. -/
def heckeArch (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  ((Real.log (heckeCompletionNorm 𝔪 : ℝ) : ℝ) : ℂ) / 2 +
    (∑ v : {v : InfinitePlace K // v.IsReal},
      logDeriv (Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat) s) +
    (InfinitePlace.nrComplexPlaces K : ℂ) *
      (logDeriv (Zeta23.ThmE.archChi 1 0) s + logDeriv (Zeta23.ThmE.archChi 1 1) s)

theorem heckeArch_inv (ψ : HeckeCharacter 𝔪) : heckeArch 𝔪 ψ⁻¹ = heckeArch 𝔪 ψ := by
  funext s
  simp only [heckeArch, heckeCoordinateParity_inv]

theorem archChi_one (κ : ℕ) (s : ℂ) : Zeta23.ThmE.archChi 1 κ s = Complex.Gammaℝ (s + κ) := by
  rw [Zeta23.ThmE.archChi, Nat.cast_one, Complex.one_cpow, one_mul]

theorem heckeGammaFactor_eq_archChi (ψ : HeckeCharacter 𝔪) :
    heckeGammaFactor 𝔪 ψ = fun s =>
      (∏ v : {v : InfinitePlace K // v.IsReal},
        Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat s) *
      (Zeta23.ThmE.archChi 1 0 s * Zeta23.ThmE.archChi 1 1 s) ^ InfinitePlace.nrComplexPlaces K := by
  funext s
  rw [heckeGammaFactor, ← Complex.Gammaℝ_mul_Gammaℝ_add_one]
  simp only [archChi_one, Nat.cast_zero, add_zero, Nat.cast_one]

theorem differentiableAt_archChi_one (κ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Zeta23.ThmE.archChi 1 κ) s :=
  (Zeta23.ThmE.archChi_differentiableOn 1 κ s hs).differentiableAt
    (Zeta23.RvM.isOpen_rightHalfPlane.mem_nhds hs)

/-- The logarithmic derivative of the Gamma product. -/
theorem logDeriv_heckeGammaFactor (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (heckeGammaFactor 𝔪 ψ) s =
      (∑ v : {v : InfinitePlace K // v.IsReal},
        logDeriv (Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat) s) +
      (InfinitePlace.nrComplexPlaces K : ℂ) *
        (logDeriv (Zeta23.ThmE.archChi 1 0) s + logDeriv (Zeta23.ThmE.archChi 1 1) s) := by
  have hd : ∀ κ : ℕ, DifferentiableAt ℂ (Zeta23.ThmE.archChi 1 κ) s := fun κ =>
    differentiableAt_archChi_one κ hs
  have hne : ∀ κ : ℕ, Zeta23.ThmE.archChi 1 κ s ≠ 0 := fun κ =>
    Zeta23.ThmE.archChi_ne_zero 1 κ hs
  have hprod_d : DifferentiableAt ℂ (fun z => ∏ v : {v : InfinitePlace K // v.IsReal},
      Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat z) s :=
    DifferentiableAt.fun_finsetProd fun v _ => hd _
  have hprod_ne : (∏ v : {v : InfinitePlace K // v.IsReal},
      Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => hne _
  have hpair_d : DifferentiableAt ℂ
      (fun z => Zeta23.ThmE.archChi 1 0 z * Zeta23.ThmE.archChi 1 1 z) s := (hd 0).mul (hd 1)
  have hpair_ne : Zeta23.ThmE.archChi 1 0 s * Zeta23.ThmE.archChi 1 1 s ≠ 0 :=
    mul_ne_zero (hne 0) (hne 1)
  have e1 := logDeriv_mul
    (f := fun z => ∏ v : {v : InfinitePlace K // v.IsReal},
      Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat z)
    (g := fun z => (Zeta23.ThmE.archChi 1 0 z * Zeta23.ThmE.archChi 1 1 z) ^
      InfinitePlace.nrComplexPlaces K) s hprod_ne (pow_ne_zero _ hpair_ne) hprod_d
    (hpair_d.fun_pow _)
  have e2 := logDeriv_prod (s := Finset.univ)
    (f := fun (v : {v : InfinitePlace K // v.IsReal}) =>
      Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat) (x := s)
    (fun v _ => hne _) (fun v _ => hd _)
  have e3 := logDeriv_fun_pow hpair_d (InfinitePlace.nrComplexPlaces K)
  have e4 := logDeriv_mul (f := Zeta23.ThmE.archChi 1 0) (g := Zeta23.ThmE.archChi 1 1) s
    (hne 0) (hne 1) (hd 0) (hd 1)
  rw [heckeGammaFactor_eq_archChi, e1, e2, e3, e4]

/-- The logarithmic derivative of the conductor factor. -/
theorem logDeriv_heckeCompletionFactor (s : ℂ) :
    logDeriv (heckeCompletionFactor 𝔪) s =
      ((Real.log (heckeCompletionNorm 𝔪 : ℝ) : ℝ) : ℂ) / 2 := by
  have hN0 : ((heckeCompletionNorm 𝔪 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (heckeCompletionNorm_pos 𝔪).ne'
  have hd : HasDerivAt (fun z : ℂ => ((heckeCompletionNorm 𝔪 : ℕ) : ℂ) ^ (z / 2))
      (((heckeCompletionNorm 𝔪 : ℕ) : ℂ) ^ (s / 2) *
        Complex.log ((heckeCompletionNorm 𝔪 : ℕ) : ℂ) * (1 / 2)) s :=
    ((hasDerivAt_id s).div_const 2).const_cpow (Or.inl hN0)
  have hfun : heckeCompletionFactor 𝔪 =
      fun z : ℂ => ((heckeCompletionNorm 𝔪 : ℕ) : ℂ) ^ (z / 2) := rfl
  have hne : ((heckeCompletionNorm 𝔪 : ℕ) : ℂ) ^ (s / 2) ≠ 0 := heckeCompletionFactor_ne_zero 𝔪 s
  rw [logDeriv_apply, hfun, hd.deriv, Complex.natCast_log]
  show _ / (((heckeCompletionNorm 𝔪 : ℕ) : ℂ) ^ (s / 2)) = _
  rw [div_eq_iff hne]
  ring

/-- The logarithmic derivative of the polynomial that clears the poles. -/
theorem logDeriv_heckePoleFactor (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (heckePoleFactor 𝔪 ψ) s = heckePole 𝔪 ψ * gPair 0 s := by
  by_cases h : ψ = 1
  · have hs0 : s ≠ 0 := by
      rintro rfl
      rw [Complex.zero_re] at hs
      linarith
    have hs1 : s - 1 ≠ 0 := by
      intro h'
      have := congrArg Complex.re h'
      rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hd : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
      (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
    rw [heckePoleFactor_of_eq_one h, logDeriv_apply, hd.deriv, heckePole, if_pos h, gPair]
    show (1 * (s - 1) + s * 1) / (s * (s - 1)) = 1 * (1 / (s - 0) + 1 / (s - (1 - 0)))
    rw [sub_zero, sub_zero, div_add_div _ _ hs0 hs1]
    exact (one_mul _).symm
  · rw [heckePoleFactor_of_ne_one h, logDeriv_const, heckePole, if_neg h, zero_mul]

theorem differentiableAt_heckePoleFactor (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    DifferentiableAt ℂ (heckePoleFactor 𝔪 ψ) s := by
  by_cases h : ψ = 1
  · rw [heckePoleFactor_of_eq_one h]
    exact differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  · rw [heckePoleFactor_of_ne_one h]
    exact differentiableAt_const _

/-! ### The logarithmic derivative -/

/-- **The logarithmic derivative of the completion on `Re s > 1`**: the pole pair, the
archimedean term, and the series over the powers of the prime ideals. -/
theorem logDeriv_heckeXi (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (heckeXi 𝔪 ψ) s =
      heckePole 𝔪 ψ * gPair 0 s + heckeArch 𝔪 ψ s - LSeries (heckeMangoldt 𝔪 ψ) s := by
  have hs0 : 0 < s.re := by linarith
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : heckeXi 𝔪 ψ =ᶠ[𝓝 s] fun z => heckePoleFactor 𝔪 ψ z *
      (heckeCompletionFactor 𝔪 z * heckeGammaFactor 𝔪 ψ z * heckeL 𝔪 ψ z) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact heckeXi_eq 𝔪 ψ hz
  have hld : logDeriv (heckeXi 𝔪 ψ) s = logDeriv (fun z => heckePoleFactor 𝔪 ψ z *
      (heckeCompletionFactor 𝔪 z * heckeGammaFactor 𝔪 ψ z * heckeL 𝔪 ψ z)) s := by
    have h1 := hev.deriv_eq
    have h2 : heckeXi 𝔪 ψ s = heckePoleFactor 𝔪 ψ s *
        (heckeCompletionFactor 𝔪 s * heckeGammaFactor 𝔪 ψ s * heckeL 𝔪 ψ s) := heckeXi_eq 𝔪 ψ hs
    simp only [logDeriv_apply]
    rw [h1, h2]
  have hPd := differentiableAt_heckePoleFactor 𝔪 ψ s
  have hPne := heckePoleFactor_ne_zero 𝔪 ψ hs
  have hFd : DifferentiableAt ℂ (heckeCompletionFactor 𝔪) s :=
    differentiable_heckeCompletionFactor 𝔪 s
  have hFne := heckeCompletionFactor_ne_zero 𝔪 s
  have hGd : DifferentiableAt ℂ (heckeGammaFactor 𝔪 ψ) s := by
    rw [heckeGammaFactor_eq_archChi]
    exact (DifferentiableAt.fun_finsetProd fun v _ => differentiableAt_archChi_one _ hs0).mul
      (((differentiableAt_archChi_one 0 hs0).mul (differentiableAt_archChi_one 1 hs0)).fun_pow _)
  have hGne := heckeGammaFactor_ne_zero 𝔪 ψ hs0
  have habs : LSeries.abscissaOfAbsConv (heckeCoeff 𝔪 ψ) < s.re :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lSeriesSummable_heckeCoeff 𝔪 ψ (by simpa using hy)) (by exact_mod_cast hs)
  have hLd : DifferentiableAt ℂ (heckeL 𝔪 ψ) s := (LSeries_hasDerivAt habs).differentiableAt
  have hLne := heckeL_ne_zero 𝔪 ψ hs
  have e1 := logDeriv_mul (f := heckePoleFactor 𝔪 ψ)
    (g := fun z => heckeCompletionFactor 𝔪 z * heckeGammaFactor 𝔪 ψ z * heckeL 𝔪 ψ z) s hPne
    (mul_ne_zero (mul_ne_zero hFne hGne) hLne) hPd ((hFd.mul hGd).mul hLd)
  have e2 := logDeriv_mul
    (f := fun z => heckeCompletionFactor 𝔪 z * heckeGammaFactor 𝔪 ψ z) (g := heckeL 𝔪 ψ) s
    (mul_ne_zero hFne hGne) hLne (hFd.mul hGd) hLd
  have e3 := logDeriv_mul (f := heckeCompletionFactor 𝔪) (g := heckeGammaFactor 𝔪 ψ) s
    hFne hGne hFd hGd
  rw [hld, e1, e2, e3, logDeriv_heckePoleFactor 𝔪 ψ hs, logDeriv_heckeCompletionFactor,
    logDeriv_heckeGammaFactor 𝔪 ψ hs0, logDeriv_heckeL 𝔪 ψ hs, heckeArch]
  ring

/-! ### The archimedean term is holomorphic with logarithmic growth -/

theorem differentiableAt_heckeArch (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (heckeArch 𝔪 ψ) s := by
  have hd : ∀ κ : ℕ, DifferentiableAt ℂ (logDeriv (Zeta23.ThmE.archChi 1 κ)) s := fun κ =>
    Zeta23.ThmE.differentiableAt_logDeriv_archChi 1 κ hs
  have h : DifferentiableAt ℂ (fun z : ℂ =>
      ((Real.log (heckeCompletionNorm 𝔪 : ℝ) : ℝ) : ℂ) / 2 +
        (∑ v : {v : InfinitePlace K // v.IsReal},
          logDeriv (Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat) z) +
        (InfinitePlace.nrComplexPlaces K : ℂ) *
          (logDeriv (Zeta23.ThmE.archChi 1 0) z + logDeriv (Zeta23.ThmE.archChi 1 1) z)) s :=
    ((differentiableAt_const _).add (DifferentiableAt.fun_sum fun v _ => hd _)).add
      ((differentiableAt_const _).mul ((hd 0).add (hd 1)))
  exact h

/-- **Logarithmic growth of the archimedean term** on `1/2 ≤ Re s ≤ 3/2`. -/
theorem exists_norm_heckeArch_le (ψ : HeckeCharacter 𝔪) :
    ∃ CG : ℝ, 0 < CG ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖heckeArch 𝔪 ψ (σ + t * I)‖ ≤ CG * Real.log (2 + |t|) := by
  obtain ⟨C₀, hC₀, h₀⟩ := Zeta23.ThmE.norm_logDeriv_archChi_le 1 0 (by norm_num)
  obtain ⟨C₁, hC₁, h₁⟩ := Zeta23.ThmE.norm_logDeriv_archChi_le 1 1 le_rfl
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlN : 0 ≤ Real.log (heckeCompletionNorm 𝔪 : ℝ) :=
    Real.log_nonneg (one_le_heckeCompletionNorm 𝔪)
  set r₁ : ℕ := Fintype.card {v : InfinitePlace K // v.IsReal} with hr₁
  set r₂ : ℕ := InfinitePlace.nrComplexPlaces K with hr₂
  refine ⟨Real.log (heckeCompletionNorm 𝔪 : ℝ) / 2 / Real.log 2 + r₁ * (C₀ + C₁) +
    r₂ * (C₀ + C₁) + 1, by positivity, fun σ t h1 h2 => ?_⟩
  have hL : Real.log 2 ≤ Real.log (2 + |t|) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have hL0 : 0 ≤ Real.log (2 + |t|) := hl2.le.trans hL
  have hκ : ∀ κ : ℕ, κ ≤ 1 → ‖logDeriv (Zeta23.ThmE.archChi 1 κ) (σ + t * I)‖ ≤
      (C₀ + C₁) * Real.log (2 + |t|) := by
    intro κ hκ
    interval_cases κ
    · exact (h₀ σ t h1 h2).trans (mul_le_mul_of_nonneg_right (by linarith) hL0)
    · exact (h₁ σ t h1 h2).trans (mul_le_mul_of_nonneg_right (by linarith) hL0)
  have hconst : ‖((Real.log (heckeCompletionNorm 𝔪 : ℝ) : ℝ) : ℂ) / 2‖ ≤
      Real.log (heckeCompletionNorm 𝔪 : ℝ) / 2 / Real.log 2 * Real.log (2 + |t|) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlN, Complex.norm_ofNat,
      div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  have hsum : ‖∑ v : {v : InfinitePlace K // v.IsReal},
      logDeriv (Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat)
        (σ + t * I)‖ ≤ r₁ * ((C₀ + C₁) * Real.log (2 + |t|)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun v _ => hκ _ (Bool.toNat_le _)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpair : ‖(InfinitePlace.nrComplexPlaces K : ℂ) *
      (logDeriv (Zeta23.ThmE.archChi 1 0) (σ + t * I) +
        logDeriv (Zeta23.ThmE.archChi 1 1) (σ + t * I))‖ ≤
      r₂ * ((C₀ + C₁) * Real.log (2 + |t|)) := by
    rw [norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (Nat.cast_nonneg _)
    have := h₀ σ t h1 h2
    have := h₁ σ t h1 h2
    linarith
  rw [heckeArch]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hconst hsum)) hpair)).trans ?_
  nlinarith [hL0]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
