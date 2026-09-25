import GaloisForLFunctions.RHTower.OrdinateInjectivity

/-!
# The hypothesis is the vanishing of a Galois norm

Genus theory computes the invariants of a `ℤ/2`-module from local ramification data, and everything
in it is phrased through the **norm** `N = 1 + σ` of the Galois action: the Tate groups are
`Ĥ⁰ = ker(σ−1)/im N` and `Ĥ¹ = ker N/im(σ−1)`, and Chevalley's ambiguous class number formula
computes the first from ramification.  This module puts the hypothesis into exactly that coordinate.

Over `𝔽₂` the two eigen-conditions collapse — `σ − 1 = σ + 1 = N` — so `N² = 0` and the module is a
two-term complex whose cohomology is the single Tate group.  On the mod-`2` divisor module of `ξ`,
with `σ` the Hermitian reflection `ρ ↦ 1 − conj ρ`:

  `RiemannHypothesis ↔ the Galois norm is identically zero`.

Equivalently: the differential of the Tate complex vanishes, so its cohomology is the whole module.
This is the genus-theoretic coordinate of `ReflectionTateParity` / `OrdinateInjectivity`, and it is
the object Chevalley's formula would compute.  Nothing here is an estimate.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The Hermitian reflection on the divisor support -/

/-- The Hermitian reflection `ρ ↦ 1 − conj ρ` on the divisor support. -/
def supportPartner : XiDivisorSupport ≃ XiDivisorSupport :=
  xiZeroConjEquiv.trans xiZeroReflectEquiv

theorem supportPartner_coe (ρ : XiDivisorSupport) :
    ((supportPartner ρ : XiDivisorSupport) : ℂ) = 1 - (starRingEnd ℂ) (ρ : ℂ) := by
  change (xiZeroReflectEquiv (xiZeroConjEquiv ρ) : ℂ) = _
  rw [xiZeroReflectEquiv_apply]
  rfl

theorem supportPartner_involutive : Function.Involutive supportPartner := by
  intro ρ
  apply Subtype.ext
  rw [supportPartner_coe, supportPartner_coe, map_sub, map_one, Complex.conj_conj]
  ring

theorem supportPartner_eq_self_iff (ρ : XiDivisorSupport) :
    supportPartner ρ = ρ ↔ (ρ : ℂ).re = 1 / 2 := by
  rw [Subtype.ext_iff, supportPartner_coe]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

/-- **The hypothesis is the triviality of the reflection on the divisor support.** -/
theorem riemannHypothesis_iff_supportPartner_eq_id :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, supportPartner ρ = ρ := by
  constructor
  · intro hRH ρ
    have hpos : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
      have := xi_divisor_pos_on_support ρ
      omega
    have := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH ⟨ρ, ⟨0, hpos⟩⟩
    exact (supportPartner_eq_self_iff ρ).mpr this
  · intro h
    exact riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase
      fun q => (supportPartner_eq_self_iff q.1).mp (h q.1)

/-! ## The Galois norm of the reflection -/

/-- The Galois norm `N = 1 + σ` of the Hermitian reflection, on mod-`2` divisor functions. -/
def divisorNorm (f : XiDivisorSupport → ZMod 2) : XiDivisorSupport → ZMod 2 :=
  fun ρ => f ρ + f (supportPartner ρ)

theorem divisorNorm_add (f g : XiDivisorSupport → ZMod 2) :
    divisorNorm (f + g) = divisorNorm f + divisorNorm g := by
  funext ρ; unfold divisorNorm; simp only [Pi.add_apply]; ring

theorem divisorNorm_zero : divisorNorm 0 = 0 := by
  funext ρ; unfold divisorNorm; simp

/-- **The Tate differential squares to zero**: over `𝔽₂` the norm and `σ − 1` coincide, so the
mod-`2` divisor module is a two-term complex with differential `N`. -/
theorem divisorNorm_divisorNorm (f : XiDivisorSupport → ZMod 2) :
    divisorNorm (divisorNorm f) = 0 := by
  funext ρ
  simp only [Pi.zero_apply]
  have h : divisorNorm (divisorNorm f) ρ
      = (f ρ + f (supportPartner ρ))
        + (f (supportPartner ρ) + f (supportPartner (supportPartner ρ))) := rfl
  rw [h, supportPartner_involutive ρ]
  have e : (f ρ + f (supportPartner ρ)) + (f (supportPartner ρ) + f ρ)
      = (f ρ + f (supportPartner ρ)) + (f ρ + f (supportPartner ρ)) := by ring
  rw [e]
  exact CharTwo.add_self_eq_zero _

/-- The norm of the indicator of a point detects whether that point is fixed. -/
theorem divisorNorm_indicator_self (ρ : XiDivisorSupport) :
    divisorNorm (fun x => if x = ρ then (1 : ZMod 2) else 0) ρ
      = 1 + (if supportPartner ρ = ρ then (1 : ZMod 2) else 0) := by
  unfold divisorNorm
  simp

/-- **The hypothesis is the vanishing of the Galois norm.** -/
theorem riemannHypothesis_iff_divisorNorm_eq_zero :
    RiemannHypothesis ↔ ∀ f : XiDivisorSupport → ZMod 2, divisorNorm f = 0 := by
  classical
  rw [riemannHypothesis_iff_supportPartner_eq_id]
  constructor
  · intro h f
    funext ρ
    unfold divisorNorm
    rw [h ρ]
    exact CharTwo.add_self_eq_zero _
  · intro h ρ
    by_contra hne
    have := congrFun (h (fun x => if x = ρ then (1 : ZMod 2) else 0)) ρ
    rw [divisorNorm_indicator_self ρ, if_neg hne] at this
    simp at this

/-- Equivalently: the Tate complex of the divisor has vanishing differential, so its cohomology is
the whole module. -/
theorem riemannHypothesis_iff_divisorNorm_eq_zero_fun :
    RiemannHypothesis ↔ divisorNorm = 0 := by
  rw [riemannHypothesis_iff_divisorNorm_eq_zero]
  constructor
  · intro h; funext f; exact h f
  · intro h f; exact congrFun h f

end

end RHTower
