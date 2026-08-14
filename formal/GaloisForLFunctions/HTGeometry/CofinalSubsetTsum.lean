import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Sums over a cofinal family of subsets converge to the full sum

If a family of subsets of the index type eventually contains every finite set, the sub-sums of an
absolutely summable family converge to the full sum.  This is the analytic content of "cofinal
completion": a directed system of finite prime sets exhausts the integers, so the corresponding
sub-sums converge.

* `HTGeometry.tendsto_tsum_subtype_of_cofinal`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace HTGeometry

variable {ι α : Type*} {f : ι → ℂ}

/-- The tail of an absolutely summable family over the complement of a set containing a prescribed
finite set is dominated by the tail over that finite set. -/
theorem norm_tsum_compl_le {F : Finset ι} {A : Set ι} (hFA : (F : Set ι) ⊆ A)
    (hf : Summable fun i => ‖f i‖) :
    ‖∑' i : (Aᶜ : Set ι), f i‖ ≤ ∑' i : ((F : Set ι)ᶜ : Set ι), ‖f i‖ := by
  classical
  have hsub : (Aᶜ : Set ι) ⊆ ((F : Set ι)ᶜ : Set ι) := fun x hx hxF => hx (hFA hxF)
  calc ‖∑' i : (Aᶜ : Set ι), f i‖ ≤ ∑' i : (Aᶜ : Set ι), ‖f i‖ :=
        norm_tsum_le_tsum_norm (hf.subtype _)
    _ ≤ ∑' i : ((F : Set ι)ᶜ : Set ι), ‖f i‖ := by
        refine Summable.tsum_le_tsum_of_inj
          (fun i : (Aᶜ : Set ι) => (⟨(i : ι), hsub i.2⟩ : ((F : Set ι)ᶜ : Set ι)))
          (by
            intro x y hxy
            apply Subtype.ext
            simpa using hxy)
          (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hf.subtype _) (hf.subtype _)

/-- **Cofinal sub-sums converge.**  If every finite set is eventually contained in `A a`, then the
sums over `A a` converge to the full sum. -/
theorem tendsto_tsum_subtype_of_cofinal {l : Filter α} {A : α → Set ι}
    (hf : Summable fun i => ‖f i‖)
    (hcof : ∀ F : Finset ι, ∀ᶠ a in l, (F : Set ι) ⊆ A a) :
    Tendsto (fun a => ∑' i : (A a : Set ι), f i) l (𝓝 (∑' i, f i)) := by
  classical
  have hsum : Summable f := hf.of_norm
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpartial : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖f i‖) atTop (𝓝 (∑' i, ‖f i‖)) :=
    hf.hasSum
  have hev : ∀ᶠ s : Finset ι in atTop, (∑' i, ‖f i‖) - ∑ i ∈ s, ‖f i‖ < ε := by
    have := (Metric.tendsto_nhds.1 hpartial) ε hε
    filter_upwards [this] with s hs
    have := abs_lt.1 (by simpa [Real.dist_eq] using hs)
    linarith [this.1]
  obtain ⟨F, hF⟩ := hev.exists
  have hcompl : (∑' i : ((F : Set ι)ᶜ : Set ι), ‖f i‖) = (∑' i, ‖f i‖) - ∑ i ∈ F, ‖f i‖ := by
    have := hf.sum_add_tsum_compl (s := F)
    linarith [this]
  filter_upwards [hcof F] with a ha
  have hsplit : (∑' i : (A a : Set ι), f i) + ∑' i : ((A a)ᶜ : Set ι), f i = ∑' i, f i :=
    Summable.tsum_add_tsum_compl (hsum.subtype _) (hsum.subtype _)
  have hbound : ‖∑' i : ((A a)ᶜ : Set ι), f i‖ ≤ ∑' i : ((F : Set ι)ᶜ : Set ι), ‖f i‖ :=
    norm_tsum_compl_le ha hf
  rw [dist_eq_norm]
  have hdiff : (∑' i : (A a : Set ι), f i) - ∑' i, f i = -∑' i : ((A a)ᶜ : Set ι), f i := by
    linear_combination hsplit
  rw [hdiff, norm_neg]
  rw [hcompl] at hbound
  linarith

end HTGeometry
