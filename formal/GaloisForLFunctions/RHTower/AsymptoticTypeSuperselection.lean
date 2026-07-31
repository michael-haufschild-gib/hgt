import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesJetStability
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Asymptotic-type superselection

This module isolates the universal asymptotic law behind the prime-valuation reflection fracture.
An all-orders-flat source germ and a nonzero finite-grade target germ are different asymptotic
species.  Their exact scalar sewing cost, and therefore the norm of every exact bounded linear
sewing family in arbitrary normed spaces, dominates every inverse power of the reference scale.

No arithmetic, dimensional, rank, or matrix hypothesis enters the theorem.  Arithmetic
applications supply concrete germs on the two sides of the abstract fracture.
-/

open Filter Asymptotics

namespace RHTower

noncomputable section

variable {α : Type*}

/-- An exact scalar sewing from an all-orders-flat germ to a finite-grade germ has cost beyond
every finite inverse order of the reference scale. -/
theorem reesEssentialSewingCost_beyondEveryFiniteOrder
    (l : Filter α) (a f g : α → ℝ) (d K : ℕ)
    (ha : ∀ᶠ x in l, a x ≠ 0)
    (hf : ∀ᶠ x in l, f x ≠ 0)
    (hflat : ReesAllOrdersFlat l a f)
    (hfinite : g =Θ[l] fun x => a x ^ d) :
    (fun x => (a x)⁻¹ ^ K) =o[l]
      (fun x => g x / f x) := by
  have hsmall :
      f =o[l] (fun x => a x ^ (K + d)) :=
    hflat (K + d)
  have hinv :
      (fun x => (a x ^ (K + d))⁻¹) =o[l]
        (fun x => (f x)⁻¹) :=
    hsmall.inv_rev (hf.mono fun x hfx hzero => (hfx hzero).elim)
  have hmul :
      (fun x => g x * (a x ^ (K + d))⁻¹) =o[l]
        (fun x => g x * (f x)⁻¹) :=
    (isBigO_refl g l).mul_isLittleO hinv
  have hgrade :
      (fun x => g x * (a x ^ (K + d))⁻¹) =Θ[l]
        (fun x => (a x)⁻¹ ^ K) := by
    apply (hfinite.mul (isTheta_refl
      (fun x => (a x ^ (K + d))⁻¹) l)).trans_eventuallyEq
    filter_upwards [ha] with x hx
    simp only [pow_add, mul_inv, inv_pow]
    calc
      a x ^ d * ((a x ^ K)⁻¹ * (a x ^ d)⁻¹) =
          (a x ^ d * (a x ^ d)⁻¹) * (a x ^ K)⁻¹ := by ring
      _ = (a x ^ K)⁻¹ := by
        rw [mul_inv_cancel₀ (pow_ne_zero d hx), one_mul]
  simpa only [div_eq_mul_inv] using
    hgrade.symm.trans_isLittleO hmul

/-- Universal operator form of asymptotic-type superselection.  If an exact bounded linear
operator family sends an all-orders-flat germ to a nonzero finite-grade germ, its full operator
norm has an essential scale singularity: it dominates every finite inverse Rees order. -/
theorem reesExactSewingOperatorNorm_beyondEveryFiniteOrder
    {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (l : Filter α) (a : α → ℝ) (f : α → E) (g : α → F)
    (d : ℕ) (R : α → (E →L[ℝ] F))
    (ha : ∀ᶠ x in l, a x ≠ 0)
    (hf : ∀ᶠ x in l, f x ≠ 0)
    (hflat : ReesAllOrdersFlat l a f)
    (hfinite : (fun x => ‖g x‖) =Θ[l] fun x => a x ^ d)
    (hsew : (fun x => R x (f x)) = g)
    (K : ℕ) :
    (fun x => (a x)⁻¹ ^ K) =o[l]
      (fun x => ‖R x‖) := by
  have hcost :=
    reesEssentialSewingCost_beyondEveryFiniteOrder
      l a (fun x => ‖f x‖) (fun x => ‖g x‖)
      d K ha
      (hf.mono fun x hfx =>
        (norm_ne_zero_iff : ‖f x‖ ≠ (0 : ℝ) ↔ f x ≠ 0).2 hfx)
      (fun N => (hflat N).norm_left) hfinite
  have hratio :
      (fun x => ‖g x‖ / ‖f x‖) =O[l]
        (fun x => ‖R x‖) := by
    apply IsBigO.of_bound 1
    filter_upwards [hf] with x hfx
    have hfpos : 0 < ‖f x‖ := norm_pos_iff.mpr hfx
    have hop := (R x).le_opNorm (f x)
    rw [congrFun hsew x] at hop
    have hdiv : ‖g x‖ / ‖f x‖ ≤ ‖R x‖ :=
      (div_le_iff₀ hfpos).2 hop
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) hfpos.le),
      abs_norm, one_mul] using hdiv
  exact hcost.trans_isBigO hratio

end

end RHTower
