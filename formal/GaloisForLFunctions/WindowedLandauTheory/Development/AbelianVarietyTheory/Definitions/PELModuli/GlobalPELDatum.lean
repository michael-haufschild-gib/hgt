import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.TensorProduct.Basic

/-! PEL data for generic fibres and their base rings. -/

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.Gen

/-- The CM field, involutive order, lattice, and complex signature of a PEL datum. -/
structure GDatum where
  F : Type
  [fld : Field F]
  [nf : NumberField F]
  [cm : IsCMField F]
  bar : 𝓞 F ≃+* 𝓞 F
  bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F)
  ω : 𝓞 F
  tr : ℤ
  nm : ℤ
  tr_eq : ω + bar ω = (tr : 𝓞 F)
  nm_eq : ω * bar ω = (nm : 𝓞 F)
  disc_neg : tr ^ 2 - 4 * nm < 0
  O : Type
  [rng : Ring O]
  [alg : Algebra (𝓞 F) O]
  freeO : Module.Free ℤ O
  finO : Module.Finite ℤ O
  m : ℕ
  m_pos : 0 < m
  rankO : Module.finrank ℤ O = m ^ 2 * Module.finrank ℚ F
  central : ∀ x : O, (∀ y, x * y = y * x) → ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c
  star : O ≃+* Oᵐᵒᵖ
  star_star : ∀ x, (star (star x).unop).unop = x
  star_F : ∀ c : 𝓞 F, star (algebraMap (𝓞 F) O c) = MulOpposite.op (algebraMap (𝓞 F) O (bar c))

  splitSome : ∃ (q : ℕ) (_ : Fact q.Prime),
    Nonempty ((O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 F] Matrix (Fin m) (Fin m) (𝓞 F ⊗[ℤ] ℤ_[q]))
  La : Type
  [acg : AddCommGroup La]
  [modO : Module O La]
  freeLa : Module.Free ℤ La
  finLa : Module.Finite ℤ La
  n : ℕ
  n_pos : 1 ≤ n
  rankLa : Module.finrank ℤ La = m * n * Module.finrank ℚ F
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  nondeg : Function.Injective EF
  adj : ∀ (b : O) x y, EF (b • x) y = EF x ((star b).unop • y)
  a : ℕ
  ρc : ℂ
  ρc_root : ρc ^ 2 - tr * ρc + nm = 0
  tau : Fin a ↪ (F →+* ℂ)
  tau_ω : ∀ i, tau i (ω : F) = ρc
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    (∀ (b : O) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) → J ∘ₗ A = A ∘ₗ J) ∧
    ∀ (c : 𝓞 F) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (algebraMap (𝓞 F) O c • x)) →
      let S : ℂ := (m : ℂ) * (∑ i, tau i (c : F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : F →+* ℂ => τ (ω : F) = (starRingEnd ℂ) ρc), (n : ℂ) * τ (c : F) -
        ∑ i, (starRingEnd ℂ) (tau i (c : F)))
      LinearMap.trace ℝ _ A = 2 * S.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * S.im

attribute [instance] GDatum.fld GDatum.nf GDatum.cm GDatum.rng GDatum.alg GDatum.acg GDatum.modO

/-- The quadratic root and pairwise comaximal embeddings over a rational base ring. -/
structure GBase (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] where
  ρ : R
  ρ_root : ρ ^ 2 - G.tr * ρ + G.nm = 0
  t : Fin G.a → (𝓞 G.F →+* R)
  t_ω : ∀ i, t i G.ω = ρ
  comax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤

/-- The chosen complex embeddings give a base over the complex numbers. -/
instance nonempty_gBase_complex (G : GDatum) : Nonempty (GBase G ℂ) := ⟨{
  ρ := G.ρc
  ρ_root := G.ρc_root
  t i := (G.tau i).comp (algebraMap (𝓞 G.F) G.F)
  t_ω i := G.tau_ω i
  comax i j hij := by
    have hne : (G.tau i).comp (algebraMap (𝓞 G.F) G.F) ≠ (G.tau j).comp (algebraMap (𝓞 G.F) G.F) := fun h =>
      hij (G.tau.injective (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 G.F)) h))
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hne
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨x, rfl⟩)
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hx)) }⟩

variable {G : GDatum} {R₁ R₂ : Type}
  [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂]

def GBase.IsMap (β : R₁ →+* R₂) (gb₁ : GBase G R₁) (gb₂ : GBase G R₂) : Prop :=
  gb₂.ρ = β gb₁.ρ ∧ ∀ i, gb₂.t i = β.comp (gb₁.t i)

def GBase.map (β : R₁ →+* R₂) (gb : GBase G R₁) : GBase G R₂ where
  ρ := β gb.ρ
  ρ_root := by simpa using congrArg β gb.ρ_root
  t i := β.comp (gb.t i)
  t_ω i := by rw [RingHom.comp_apply, gb.t_ω]
  comax i j hij := by
    have h := congrArg (Ideal.map β) (gb.comax i j hij)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    simpa [Function.comp_def] using h

theorem GBase.isMap_map (β : R₁ →+* R₂) (gb : GBase G R₁) : GBase.IsMap β gb (gb.map β) :=
  ⟨rfl, fun _ => rfl⟩

end GlobalTheory.UPel.HT.Gen
