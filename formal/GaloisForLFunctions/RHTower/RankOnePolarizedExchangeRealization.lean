import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeCoherentKernel
import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeModularGain

/-!
# Exchange geometrizability of the rank-one modular family

Composition coherence of the polarized modular family, the single square identity at degree two,
triviality of the gain at degree two, and zero modular weight are one and the same condition.  A
categorical realization of the multiplication monoid whose matrix shadow is the polarized modular
family therefore exists only at zero weight, and for a centred spectral gain of weight `w` only on
the purity line.
-/

namespace RHTower

noncomputable section

open CategoryTheory

/-- **The rank-one exchange horizon, in four equivalent forms.** -/
theorem exchangeTransport_modularGain_tfae (θ : ℝ) :
    List.TFAE
      [∀ m n : ℕ+, exchangeTransport (modularGain θ) m * exchangeTransport (modularGain θ) n =
          exchangeTransport (modularGain θ) (m * n),
        exchangeTransport (modularGain θ) 2 * exchangeTransport (modularGain θ) 2 =
          exchangeTransport (modularGain θ) 4,
        modularGain θ 2 = 1,
        θ = 0] := by
  tfae_have 1 ↔ 4 := exchangeTransport_modularGain_mul_iff θ
  tfae_have 2 ↔ 4 := exchangeTransport_modularGain_two_sq_iff θ
  tfae_have 3 ↔ 4 := modularGain_two_eq_one_iff θ
  tfae_finish

/-- **A polarized modular realization forces zero modular weight.**  If the polarized modular family
is the matrix shadow of a functorial realization of the multiplication monoid, the weight is zero. -/
theorem eq_zero_of_factors {𝒰 : Type*} [Category 𝒰] {θ : ℝ}
    (F : SingleObj ℕ+ ⥤ 𝒰) (R : 𝒰 ⥤ SingleObj (Matrix (Fin 2) (Fin 2) ℝ))
    (hR : ∀ n : ℕ+, R.map (F.map (SingleObj.toEnd ℕ+ n)) =
      exchangeTransport (modularGain θ) n) : θ = 0 :=
  (modularGain_eq_one_iff θ).1 (eq_one_of_factors F R hR)

/-- **A polarized spectral realization forces the purity line.** -/
theorem re_eq_of_factors {𝒰 : Type*} [Category 𝒰] {w : ℝ} {s : ℂ}
    (F : SingleObj ℕ+ ⥤ 𝒰) (R : 𝒰 ⥤ SingleObj (Matrix (Fin 2) (Fin 2) ℝ))
    (hR : ∀ n : ℕ+, R.map (F.map (SingleObj.toEnd ℕ+ n)) =
      exchangeTransport (spectralGain w s) n) : s.re = w / 2 := by
  have hzero : 2 * s.re - w = 0 := eq_zero_of_factors F R hR
  linarith

end

end RHTower
