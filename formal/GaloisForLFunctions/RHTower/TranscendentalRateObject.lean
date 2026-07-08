import GaloisForLFunctions.RHTower.SeamClockSelection
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# A seam object with no arithmetic and no functional equation

The seam objects of `SeamClockSelection` all carry the prime-rate lattice `⟨log p⟩`, so their weld
rests on unique factorization — arithmetic.  Here the rate family is genuinely non-arithmetic: the
powers `{θ^n}` of a transcendental real `θ`.  Their `ℤ`-linear independence comes from *transcendence*
— no nonzero polynomial vanishes at `θ` — not from factorization, so the weld it feeds is transcendental
in origin.  Taking `θ` to be a concrete Liouville number makes the object fully explicit.

The object's own structure supplies the selecting constraint, and it is not a functional equation.  Its
frequencies obey the multiplicative recurrence `λ_{n+1} = θ·λ_n`, so the map that carries the `n`-th
generator to the `(n+1)`-th scales the clock parameter by `θ`: the constraint is the Mahler scaling
`s ↦ θ·s`.  Its linear part is `θ ≠ 1`, so — by the coherent-clock criterion — it selects a clock, but
at `0`, not `1/2`.  Nothing here is a reflection; the answer to "does a coherent clock exist" is read
off the object's self-similarity, and no functional equation hands you `1/2`.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- **Powers of a transcendental are `ℤ`-linearly independent.**  For `θ` transcendental over `ℤ`, the
family `{θ^n}` has no nonzero integer-polynomial relation — the evaluation `aeval θ` is injective, so it
carries the monomial basis of `ℤ[X]` to an independent family.  This is the transcendence-sourced
independence input that a non-arithmetic rate family needs, replacing unique factorization. -/
theorem transc_pow_indepZ {θ : ℝ} (hθ : Transcendental ℤ θ) :
    LinearIndependent ℤ (fun n : ℕ => θ ^ n) := by
  have hinj : Function.Injective (aeval θ : ℤ[X] →ₐ[ℤ] ℝ) := transcendental_iff_injective.mp hθ
  have hmap := (Polynomial.basisMonomials ℤ).linearIndependent.map'
    (aeval θ : ℤ[X] →ₐ[ℤ] ℝ).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  simp only [Function.comp_def, AlgHom.toLinearMap_apply, Polynomial.coe_basisMonomials,
    aeval_monomial, map_one, one_mul] at hmap
  exact hmap

/-- A concrete transcendental: the Liouville number `∑ 2^{-k!}`. -/
def liouvilleConst : ℝ := liouvilleNumber 2

theorem liouvilleConst_transcendental : Transcendental ℤ liouvilleConst := by
  simpa [liouvilleConst] using transcendental_liouvilleNumber (m := 2) (by norm_num)

theorem liouvilleConst_irrational : Irrational liouvilleConst :=
  (liouville_liouvilleNumber (m := 2) (by norm_num)).irrational

/-- The scaling constant of the object's constraint is not `1` (it is irrational). -/
theorem liouvilleConst_ne_one : (liouvilleConst : ℂ) ≠ 1 := by
  have h : liouvilleConst ≠ 1 := fun h => liouvilleConst_irrational (h ▸ ⟨1, by norm_num⟩)
  exact_mod_cast h

/-- The seam object with no arithmetic and no functional equation: rate family `{θ^n}` for the
Liouville constant `θ`, and the Mahler self-similarity `s ↦ θ·s` (`selLin = θ`, `selConst = 0`) as its
selecting constraint. -/
def liouvilleRateObject : SeamObject ℕ :=
  ⟨fun n => liouvilleConst ^ n, transc_pow_indepZ liouvilleConst_transcendental,
   (liouvilleConst : ℂ), 0⟩

/-- The frequency recurrence `λ_{n+1} = θ·λ_n` — the multiplicative self-similarity that *is* the
object's selecting constraint (its implementation on the clock parameter is `s ↦ θ·s`). -/
theorem liouvilleRate_recurrence (n : ℕ) :
    liouvilleRateObject.rate (n + 1) = liouvilleConst * liouvilleRateObject.rate n := by
  show liouvilleConst ^ (n + 1) = liouvilleConst * liouvilleConst ^ n
  ring

/-- The object has an infinite-rank weld — sourced from transcendence, not factorization: its weld
classes `{weldClass (θ^n)}` are `ℤ`-linearly independent. -/
theorem liouvilleObject_weld_nontrivial (c : ℕ →₀ ℤ)
    (h : c.sum (fun n z => z • weldClassHom (liouvilleConst ^ n)) = 0) : c = 0 :=
  liouvilleRateObject.weld_nontrivial c h

/-- Its clock covector is free: for any assignment of a time value to each frequency there is exactly
one covector on the rate lattice realizing it. -/
theorem liouvilleObject_clock_covector_free (t : ℕ → ℝ) :
    ∃! τ : Submodule.span ℤ (Set.range liouvilleRateObject.rate) →ₗ[ℤ] ℝ,
      ∀ n, τ ⟨liouvilleRateObject.rate n, Submodule.subset_span ⟨n, rfl⟩⟩ = t n :=
  liouvilleRateObject.clock_covector_free t

/-- **A coherent clock exists — with no functional equation.**  The Mahler self-similarity `s ↦ θ·s`
has linear part `θ ≠ 1`, so it selects exactly one clock locus. -/
theorem liouvilleObject_has_clock :
    ∃! s, affineSelect liouvilleRateObject.selLin liouvilleRateObject.selConst s = s :=
  liouvilleRateObject.clock_selected liouvilleConst_ne_one

/-- The selected clock sits at `0`, not `1/2`: the location is the scaling's fixed point, read off the
object's own self-similarity, not handed down by a reflection. -/
theorem liouvilleObject_clock_at_zero :
    affineSelect liouvilleRateObject.selLin liouvilleRateObject.selConst 0 = 0 := by
  show affineSelect (liouvilleConst : ℂ) 0 0 = 0
  unfold affineSelect; ring

end RHTower
end GaloisForLFunctions
