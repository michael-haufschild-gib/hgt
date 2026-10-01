import GaloisForLFunctions.RHTower.SteinhausOriginalFiniteLocalTarget
import GaloisForLFunctions.RHTower.SteinhausChannelEuclideanFrame
import Mathlib.Data.Fintype.EquivFin


open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

private theorem sum_enum {F : Type*} [AddCommMonoid F] (S : Finset ℕ) (f : ℕ → F) :
    (∑ i : Fin S.card, f (S.equivFin.symm i).val) = ∑ p ∈ S, f p :=
  (S.equivFin.symm.sum_comp (fun p : S => f p)).trans (Finset.sum_coe_sort S f)

/-- The original local target law with its literal finite coordinate set and sums. -/
theorem measureReal_originalSteinhausFinsetLocalTarget_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : Finset ℕ) (a : ℕ → E) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hframe : ∀ w : E, c * ‖w‖ ^ 2 ≤ ∑ p ∈ S, ‖inner ℂ (a p) w‖ ^ 2)
    (v : E) (hsmall : ∀ p ∈ S, ‖a p‖ * ‖v‖ / c ≤ 1 / 2)
    (henergy : (∑ p ∈ S, ‖a p‖ ^ 2) ≤ r ^ 2 / 2) :
    (1 / 4 : ℝ) * Real.exp (-2 * ‖v‖ ^ 2 / c) ≤
      steinhausMeasure.real {ω | ‖(∑ p ∈ S, charFactor 1 (ω p) • a p) - v‖ < r} := by
  let p : Fin S.card → ℕ := fun i => (S.equivFin.symm i).val
  have hp : Function.Injective p := Subtype.val_injective.comp S.equivFin.symm.injective
  have hf (w : E) : c * ‖w‖ ^ 2 ≤ ∑ i : Fin S.card, ‖inner ℂ (a (p i)) w‖ ^ 2 := by
    exact (hframe w).trans_eq (sum_enum S (fun q => ‖inner ℂ (a q) w‖ ^ 2)).symm
  have hm (i : Fin S.card) : ‖a (p i)‖ * ‖v‖ / c ≤ 1 / 2 :=
    hsmall _ (S.equivFin.symm i).property
  have he : (∑ i : Fin S.card, ‖a (p i)‖ ^ 2) ≤ r ^ 2 / 2 := by
    exact (sum_enum S (fun q => ‖a q‖ ^ 2)).trans_le henergy
  have h := measureReal_originalSteinhausFiniteLocalTarget_ge p hp (fun i => a (p i))
    hc hr hf v hm he
  have hs (ω : Omega) : (∑ i : Fin S.card, charFactor 1 (ω (p i)) • a (p i)) =
      ∑ q ∈ S, charFactor 1 (ω q) • a q :=
    sum_enum S (fun q => charFactor 1 (ω q) • a q)
  simpa only [hs] using h

/-- A literal finite channel matrix reaches every admissible target under the original law. -/
theorem measureReal_originalSteinhausChannelLocalTarget_ge {J : ℕ} (hJ : 0 < J)
    (S : Finset ℕ) (a : ℕ → Fin J → ℂ) {H L C r : ℝ} (hH : 0 < H) (hL : 0 ≤ L)
    (hr : 0 < r)
    (hlower : ∀ u : Fin J → ℂ, H * ‖u‖ ^ 2 ≤ ∑ p ∈ S, ‖∑ j, a p j * u j‖ ^ 2)
    (hdot : ∀ p ∈ S, ∀ u : Fin J → ℂ, ‖∑ j, a p j * u j‖ ≤ L * ‖u‖)
    (hupper : ∀ u : Fin J → ℂ, (∑ p ∈ S, ‖∑ j, a p j * u j‖ ^ 2) ≤ C * ‖u‖ ^ 2)
    (v : EuclideanSpace ℂ (Fin J))
    (hsmall : L * ‖v‖ / (H / J) ≤ 1 / 2) (henergy : (J : ℝ) * C ≤ r ^ 2 / 2) :
    (1 / 4 : ℝ) * Real.exp (-2 * ‖v‖ ^ 2 / (H / J)) ≤
      steinhausMeasure.real {ω |
        ‖(∑ p ∈ S, charFactor 1 (ω p) • (WithLp.toLp 2 (a p) : EuclideanSpace ℂ (Fin J))) - v‖ < r} := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hc : 0 < H / (J : ℝ) := div_pos hH hJR
  refine measureReal_originalSteinhausFinsetLocalTarget_ge S
    (fun p => (WithLp.toLp 2 (a p) : EuclideanSpace ℂ (Fin J))) hc hr ?_ v ?_ ?_
  · intro w
    have hl (u : Fin J → ℂ) : H * ‖u‖ ^ 2 ≤ ∑ p : S, ‖∑ j, a p j * u j‖ ^ 2 := by
      exact (hlower u).trans_eq
        (Finset.sum_coe_sort S (fun p => ‖∑ j, a p j * u j‖ ^ 2)).symm
    have h := steinhausEuclideanFrame_lower hJ (fun p : S => a p) hH.le hl w
    exact h.trans_eq (Finset.sum_coe_sort S
      (fun p => ‖inner ℂ (WithLp.toLp 2 (a p) : EuclideanSpace ℂ (Fin J)) w‖ ^ 2))
  · intro p hp
    have ha := norm_steinhausEuclideanColumn_le (a p) hL (hdot p hp)
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (norm_nonneg v)) hc.le).trans hsmall
  · have hu (u : Fin J → ℂ) : (∑ p : S, ‖∑ j, a p j * u j‖ ^ 2) ≤ C * ‖u‖ ^ 2 := by
      exact (Finset.sum_coe_sort S (fun p => ‖∑ j, a p j * u j‖ ^ 2)).trans_le (hupper u)
    have h := steinhausEuclideanFrame_energy_upper (fun p : S => a p) C hu
    have hs : (∑ p ∈ S, ‖(WithLp.toLp 2 (a p) : EuclideanSpace ℂ (Fin J))‖ ^ 2) ≤ J * C := by
      exact (Finset.sum_coe_sort S
        (fun p => ‖(WithLp.toLp 2 (a p) : EuclideanSpace ℂ (Fin J))‖ ^ 2)).symm.trans_le h
    exact hs.trans henergy

end RHTower
