import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.AFunctionOfOrderOneWithAFunctionalEquationHasWeilsExplicitFormula
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheZerosOfAFunctionOfOrderOneWithAReflectionFormATemperedConfiguration
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheLogarithmicDerivativeOfACompletedHeckeFunctionIsItsPolesItsGammaFactorsAndItsPrimeIdeals
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros

/-!
# The zeros of a Hecke L-function satisfy Weil's explicit formula

Let `ψ` be a primitive ray class character of a number field `K`: a character of the ideals of
`K`, for the trivial character the Dedekind zeta function of `K`. No hypothesis is made on `K`
over `ℚ`.

* **The configuration** (`heckeZeros`, `temperedConfig_heckeZeros`). The zeros of the entire
  completion with their orders are a tempered zero configuration: they lie in the closed strip,
  are closed under `ρ ↦ 1 − ρ̄`, and `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞`.
* **The explicit formula** (`W_heckeZeros_eq`). For `f, g ∈ C²_c` and `k = f ⋆ g̃`,

  `Σ_ρ m_ρ ĥ_f(γ_ρ) conj ĥ_g(conj γ_ρ) = m_ψ (H_k(0) + H_k(1)) + (1/2π) ∫ k̂(t) S_ψ(t) dt
      − Σ_n n^{−1/2} (Λ_ψ(n) k(log n) + conj Λ_ψ(n) k(−log n))`,

  `Λ_ψ(n) = Σ_{N𝔭^k = n} ψ(𝔭)^k log N𝔭` the contacts of the ideals of norm `n`, `m_ψ` the order of
  the pole, and `S_ψ` the real symbol of the places at infinity and of the conductor
  (`heckeSymbol`): `log N` plus one digamma term for each real place, with its parity, and two
  for each complex place.
* **The index law** (`exists_le_negIndex_heckeGram_iff`,
  `forall_negIndex_heckeGram_eq_zero_iff`). Weil's form of `ψ` has `n` negative squares on some
  family of `n` tests iff the completion has at least `n` distinct zeros to the right of the
  critical line; it has none iff all zeros are on the line.
-/

noncomputable section

open Complex Filter Topology Set NumberField MeasureTheory
open scoped Classical nonZeroDivisors ComplexConjugate

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens HTGeometry
open Zeta23 Zeta23.WeilEF
open RHTower.WeilLineIntegral
open GaloisForLFunctions.EntireZeroDivisor

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-! ### The configuration of the zeros -/

theorem heckeRootNumber_ne_zero (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) : heckeRootNumber 𝔪 ψ ≠ 0 := by
  intro h
  have h1 := norm_heckeRootNumber 𝔪 ψ hψ
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem heckeXi_two_ne_zero (ψ : HeckeCharacter 𝔪) : heckeXi 𝔪 ψ 2 ≠ 0 :=
  heckeXi_ne_zero 𝔪 ψ (by norm_num)

/-- The zeros of the completion lie in the closed critical strip. -/
theorem heckeXi_strip (ψ : HeckeCharacter 𝔪) (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ}
    (hs : heckeXi 𝔪 ψ s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    have h' : s.re < 0 := lt_of_not_ge h
    have h1 : 1 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hFE := heckeXi_one_sub 𝔪 ψ hψ (1 - s)
    rw [sub_sub_cancel, hs] at hFE
    exact (mul_ne_zero (heckeRootNumber_ne_zero 𝔪 ψ hψ) (heckeXi_ne_zero 𝔪 ψ⁻¹ h1)) hFE.symm
  · by_contra h
    exact heckeXi_ne_zero 𝔪 ψ (lt_of_not_ge h) hs

/-- The orders of the zeros are invariant under `ρ ↦ 1 − ρ̄`. -/
theorem analyticOrderAt_heckeXi_reflect (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (ρ : ℂ) :
    analyticOrderAt (heckeXi 𝔪 ψ) (reflect ρ) = analyticOrderAt (heckeXi 𝔪 ψ) ρ :=
  analyticOrderAt_reflect_of_dual (heckeRootNumber_ne_zero 𝔪 ψ hψ) (differentiable_heckeXi 𝔪 ψ⁻¹)
    (heckeXi_one_sub 𝔪 ψ hψ) (heckeXi_inv_conj 𝔪 ψ) ρ

/-- **The zeros of `L(s, ψ)` in the critical strip, with their multiplicities.** -/
def heckeZeros (ψ : HeckeCharacter 𝔪) (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) : ZeroConfig :=
  zerosConfig (heckeXi 𝔪 ψ) (differentiable_heckeXi 𝔪 ψ) (heckeXi_two_ne_zero 𝔪 ψ)
    (fun _ hs => heckeXi_strip 𝔪 ψ hψ hs) (analyticOrderAt_heckeXi_reflect 𝔪 ψ hψ)

/-- **The zeros of a Hecke `L`-function are a tempered configuration.** -/
theorem temperedConfig_heckeZeros (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    SquareRootThreshold.TemperedConfig (heckeZeros 𝔪 ψ hψ) := by
  obtain ⟨C, hC, hb⟩ := exists_orderOne_heckeXi 𝔪 ψ hψ
  exact temperedConfig_zerosConfig (differentiable_heckeXi 𝔪 ψ) (heckeXi_two_ne_zero 𝔪 ψ)
    (fun _ hs => heckeXi_strip 𝔪 ψ hψ hs) (analyticOrderAt_heckeXi_reflect 𝔪 ψ hψ) hC hb

/-- For a nontrivial character the zeros of the completion right of `0` are the zeros of the
`L`-function. -/
theorem heckeXi_eq_zero_iff {ψ : HeckeCharacter 𝔪} (h1 : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    heckeXi 𝔪 ψ s = 0 ↔ heckeLFunction 𝔪 ψ s = 0 := by
  have hG := heckeGammaFactor_ne_zero 𝔪 ψ hs
  have hF := heckeCompletionFactor_ne_zero 𝔪 s
  rw [heckeXi_of_ne_one h1, heckeCompletedLFunction,
    ← heckeGammaCompletedLFunction_mul_gamma_inv 𝔪 h1 s]
  constructor
  · intro h
    rw [(mul_eq_zero.mp h).resolve_left hF, zero_mul]
  · intro h
    rw [(mul_eq_zero.mp h).resolve_right (inv_ne_zero hG), mul_zero]

/-! ### The test and the symbol -/

/-- The transform of `f ⋆ g̃` decays to fourth order on vertical strips. -/
theorem exists_norm_Hfn_weilTest_le {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, |σ - 1 / 2| ≤ M →
      ‖Hfn (EF.weilTest f g) (σ + t * I)‖ ≤ C / (1 + t ^ 2) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := RHTower.WeilLineAnyAbscissa.norm_Hfn_le_wide hf hfc M
  obtain ⟨C₂, hC₂0, hC₂⟩ := RHTower.WeilLineAnyAbscissa.norm_Hfn_le_wide hg hgc M
  refine ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, fun σ t hσ => ?_⟩
  have hfac : Hfn (EF.weilTest f g) (σ + t * I) =
      Hfn f (σ + t * I) * (starRingEnd ℂ) (Hfn g (((1 - σ : ℝ) : ℂ) + t * I)) := by
    unfold Hfn
    rw [EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc]
    congr 3
    rw [map_div₀, Complex.conj_I, map_sub, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast
    field_simp
    ring
  have hσ' : |(1 - σ) - 1 / 2| ≤ M := by
    rw [show (1 - σ) - 1 / 2 = -(σ - 1 / 2) by ring, abs_neg]
    exact hσ
  rw [hfac, norm_mul, Complex.norm_conj, pow_two, ← div_mul_div_comm]
  exact mul_le_mul (hC₁ σ t hσ) (hC₂ (1 - σ) t hσ') (norm_nonneg _)
    (div_nonneg hC₁0 (by positivity))

/-- **The symbol of the places at infinity and of the conductor**: the archimedean term of the
explicit formula on the critical line. -/
def heckeSymbol (ψ : HeckeCharacter 𝔪) (t : ℝ) : ℝ :=
  Real.log (heckeCompletionNorm 𝔪 : ℝ) +
    (∑ v : {v : InfinitePlace K // v.IsReal},
      2 * Real.pi * Zeta23.ThmE.muq (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat 1 t) +
    (InfinitePlace.nrComplexPlaces K : ℝ) *
      (2 * Real.pi * Zeta23.ThmE.muq 0 1 t + 2 * Real.pi * Zeta23.ThmE.muq 1 1 t)

/-- The archimedean term on the critical line is the real symbol. -/
theorem heckeArch_bracket (ψ : HeckeCharacter 𝔪) (t : ℝ) :
    heckeArch 𝔪 ψ (1 / 2 + t * I) + heckeArch 𝔪 ψ (1 / 2 - t * I) =
      ((heckeSymbol 𝔪 ψ t : ℝ) : ℂ) := by
  have hb : ∀ κ : ℕ, κ ≤ 1 →
      logDeriv (Zeta23.ThmE.archChi 1 κ) (1 / 2 + t * I) +
        logDeriv (Zeta23.ThmE.archChi 1 κ) (1 / 2 - t * I) =
          ((2 * Real.pi * Zeta23.ThmE.muq κ 1 t : ℝ) : ℂ) := fun κ hκ =>
    Zeta23.ThmE.archChi_bracket 1 κ hκ le_rfl t
  have hsum : (∑ v : {v : InfinitePlace K // v.IsReal},
        logDeriv (Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat)
          (1 / 2 + t * I)) +
      (∑ v : {v : InfinitePlace K // v.IsReal},
        logDeriv (Zeta23.ThmE.archChi 1 (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat)
          (1 / 2 - t * I)) =
      ∑ v : {v : InfinitePlace K // v.IsReal},
        ((2 * Real.pi *
          Zeta23.ThmE.muq (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat 1 t : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hb _ (Bool.toNat_le _)
  have h0 := hb 0 (by norm_num)
  have h1 := hb 1 le_rfl
  have hR : ((heckeSymbol 𝔪 ψ t : ℝ) : ℂ) =
      ((Real.log (heckeCompletionNorm 𝔪 : ℝ) : ℝ) : ℂ) +
        (∑ v : {v : InfinitePlace K // v.IsReal},
          ((2 * Real.pi *
            Zeta23.ThmE.muq (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat 1 t : ℝ) : ℂ)) +
        (InfinitePlace.nrComplexPlaces K : ℂ) *
          (((2 * Real.pi * Zeta23.ThmE.muq 0 1 t : ℝ) : ℂ) +
            ((2 * Real.pi * Zeta23.ThmE.muq 1 1 t : ℝ) : ℂ)) := by
    rw [heckeSymbol]
    norm_cast
  rw [heckeArch, heckeArch, hR]
  linear_combination hsum + (InfinitePlace.nrComplexPlaces K : ℂ) * h0 +
    (InfinitePlace.nrComplexPlaces K : ℂ) * h1

/-- The contacts of the inverse character are the conjugates. -/
theorem heckeMangoldt_inv (ψ : HeckeCharacter 𝔪) (n : ℕ) :
    heckeMangoldt 𝔪 ψ⁻¹ n = conj (heckeMangoldt 𝔪 ψ n) := by
  rw [heckeMangoldt, heckeMangoldt, map_sum]
  refine Finset.sum_congr rfl fun pk _ => ?_
  rw [map_mul, map_pow, Complex.conj_ofReal, heckeValue_inv_eq_conj]

/-! ### The explicit formula -/

/-- **Weil's explicit formula for a Hecke `L`-function.** -/
theorem W_heckeZeros_eq (ψ : HeckeCharacter 𝔪) (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    (heckeZeros 𝔪 ψ hψ).W f g =
      heckePole 𝔪 ψ * (Hfn (EF.weilTest f g) 0 + Hfn (EF.weilTest f g) 1) +
        (1 / (2 * Real.pi) : ℂ) *
          (∫ t : ℝ, paperFT (EF.weilTest f g) t * ((heckeSymbol 𝔪 ψ t : ℝ) : ℂ)) -
        ∑' n : ℕ, heckeMangoldt 𝔪 ψ n / Real.sqrt n * EF.weilTest f g (Real.log n) -
        ∑' n : ℕ, conj (heckeMangoldt 𝔪 ψ n) / Real.sqrt n * EF.weilTest f g (-Real.log n) := by
  obtain ⟨C, hC, hb⟩ := exists_orderOne_heckeXi 𝔪 ψ hψ
  have hkd : ContDiff ℝ 2 (EF.weilTest f g) := EF.weilTest_contDiff hf hg.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f g) := EF.weilTest_hasCompactSupport hfc hgc
  obtain ⟨D, -, hD⟩ := exists_norm_Hfn_weilTest_le hf hfc hg hgc (3 / 2)
  have hre : ∀ t : ℝ, 1 < (((3 / 2 : ℝ) : ℂ) + t * I).re := fun t => by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
  have hre0 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    norm_num
  have h := hasSum_zeros_explicit (E := heckeXi 𝔪 ψ) (E' := heckeXi 𝔪 ψ⁻¹)
    (differentiable_heckeXi 𝔪 ψ) hC hb (heckeRootNumber_ne_zero 𝔪 ψ hψ)
    (heckeXi_one_sub 𝔪 ψ hψ) (fun s hs => heckeXi_ne_zero 𝔪 ψ hs)
    (fun s hs => heckeXi_ne_zero 𝔪 ψ⁻¹ hs)
    (m := heckePole 𝔪 ψ) (G := heckeArch 𝔪 ψ) (a := heckeMangoldt 𝔪 ψ)
    (a' := heckeMangoldt 𝔪 ψ⁻¹)
    (fun s hs => differentiableAt_heckeArch 𝔪 ψ hs) (exists_norm_heckeArch_le 𝔪 ψ)
    (c := 3 / 2) (by norm_num) le_rfl
    (lSeriesSummable_heckeMangoldt 𝔪 ψ hre0) (lSeriesSummable_heckeMangoldt 𝔪 ψ⁻¹ hre0)
    (fun t => logDeriv_heckeXi 𝔪 ψ (hre t))
    (fun t => by rw [logDeriv_heckeXi 𝔪 ψ⁻¹ (hre t), heckePole_inv, heckeArch_inv])
    hkd hkc
    (fun σ t h1 h2 => hD σ t (abs_le.mpr ⟨by linarith, by linarith⟩))
  have hW := W_zerosConfig_eq (differentiable_heckeXi 𝔪 ψ) (heckeXi_two_ne_zero 𝔪 ψ)
    (fun _ hs => heckeXi_strip 𝔪 ψ hψ hs) (analyticOrderAt_heckeXi_reflect 𝔪 ψ hψ)
    hf.continuous hg.continuous hfc hgc h
  have hint : (fun t : ℝ => paperFT (EF.weilTest f g) t *
      (heckeArch 𝔪 ψ (1 / 2 + t * I) + heckeArch 𝔪 ψ (1 / 2 - t * I))) =
      fun t : ℝ => paperFT (EF.weilTest f g) t * ((heckeSymbol 𝔪 ψ t : ℝ) : ℂ) :=
    funext fun t => by rw [heckeArch_bracket]
  have hprime : (fun n : ℕ => heckeMangoldt 𝔪 ψ⁻¹ n / Real.sqrt n *
      EF.weilTest f g (-Real.log n)) =
      fun n : ℕ => conj (heckeMangoldt 𝔪 ψ n) / Real.sqrt n * EF.weilTest f g (-Real.log n) :=
    funext fun n => by rw [heckeMangoldt_inv]
  rw [hint, hprime] at hW
  exact hW

/-! ### The index law -/

/-- **The Hodge index of a Hecke character.** Weil's form of `ψ` has `n` negative squares on
some family of `n` tests iff the completion of `L(s, ψ)` has at least `n` distinct zeros to the
right of the critical line. -/
theorem exists_le_negIndex_heckeGram_iff (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (heckeZeros 𝔪 ψ hψ) f)) ↔
      (n : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros (heckeZeros 𝔪 ψ hψ)).encard :=
  ArithmeticCastelnuovoSeveri.pontryagin_law _ (temperedConfig_heckeZeros 𝔪 ψ hψ) n

/-- No zero to the right of the line iff all zeros are on the line. -/
theorem rightZeros_heckeZeros_eq_empty_iff (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    ArithmeticCastelnuovoSeveri.rightZeros (heckeZeros 𝔪 ψ hψ) = ∅ ↔
      ∀ ρ : ℂ, heckeXi 𝔪 ψ ρ = 0 → ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : reflect ρ ∈ ArithmeticCastelnuovoSeveri.rightZeros (heckeZeros 𝔪 ψ hψ) := by
        show reflect ρ ∈ (heckeZeros 𝔪 ψ hψ).carrier ∧ 1 / 2 < (reflect ρ).re
        refine ⟨(heckeZeros 𝔪 ψ hψ).reflect_mem ρ hρ, ?_⟩
        rw [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      rw [h] at hmem
      exact (Set.mem_empty_iff_false _).mp hmem
    · have hmem : ρ ∈ ArithmeticCastelnuovoSeveri.rightZeros (heckeZeros 𝔪 ψ hψ) := by
        show ρ ∈ (heckeZeros 𝔪 ψ hψ).carrier ∧ 1 / 2 < ρ.re
        exact ⟨hρ, hgt⟩
      rw [h] at hmem
      exact (Set.mem_empty_iff_false _).mp hmem
  · intro h
    refine Set.eq_empty_of_forall_notMem fun ρ hmem => ?_
    have hmem' : ρ ∈ (heckeZeros 𝔪 ψ hψ).carrier ∧ 1 / 2 < ρ.re := hmem
    have := h ρ hmem'.1
    linarith [hmem'.2]

/-- **Castelnuovo and Severi for a Hecke character.** Weil's form of `ψ` has no negative square
on any family of tests iff all zeros of the completion of `L(s, ψ)` are on the critical line. -/
theorem forall_negIndex_heckeGram_eq_zero_iff (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (heckeZeros 𝔪 ψ hψ) f) = 0) ↔
      ∀ ρ : ℂ, heckeXi 𝔪 ψ ρ = 0 → ρ.re = 1 / 2 := by
  rw [← rightZeros_heckeZeros_eq_empty_iff 𝔪 ψ hψ]
  constructor
  · intro h
    by_contra hne
    have h1 : ((1 : ℕ) : ℕ∞) ≤
        (ArithmeticCastelnuovoSeveri.rightZeros (heckeZeros 𝔪 ψ hψ)).encard := by
      rw [Nat.cast_one, Set.one_le_encard_iff_nonempty]
      exact Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨f, hf, hfc, hle⟩ := (exists_le_negIndex_heckeGram_iff 𝔪 ψ hψ 1).mpr h1
    rw [h 1 f hf hfc] at hle
    exact absurd hle (by norm_num)
  · intro h n f hf hfc
    have hle := ArithmeticCastelnuovoSeveri.negIndex_zeroGram_le_of_tempered _
      (temperedConfig_heckeZeros 𝔪 ψ hψ) f hf hfc
    rw [h, Set.encard_empty] at hle
    exact Nat.eq_zero_of_le_zero (by exact_mod_cast hle)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
