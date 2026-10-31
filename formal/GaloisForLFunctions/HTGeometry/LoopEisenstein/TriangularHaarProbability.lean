import GaloisForLFunctions.HTGeometry.InfiniteProductFiniteHead
import Mathlib.MeasureTheory.Group.Measure

/-!
# Triangular translations preserve countable product probability

Every coordinate is translated by a measurable function of the strictly
earlier coordinates. Finite products are preserved by successive skew
translations. Equality on finite coordinate cylinders gives preservation
of the countable product probability, without an ambient infinite Haar law.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open MeasureTheory Set
noncomputable section
variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd G]
variable (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddRightInvariant]

/-- The strictly earlier coordinates of a finite tuple. -/
def strictPrefix {N : ℕ} (i : Fin N) (x : Fin N → G) : Fin i.val → G :=
  fun j => x ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- Finite triangular translation, with no dependence on the current coordinate in the shift. -/
def triangularFinite (φ : ∀ n : ℕ, (Fin n → G) → G) (N : ℕ) (x : Fin N → G) : Fin N → G :=
  fun i => x i + φ i.val (strictPrefix i x)

/-- Countable triangular translation. -/
def triangularSequence (φ : ∀ n : ℕ, (Fin n → G) → G) (x : ℕ → G) : ℕ → G :=
  fun n => x n + φ n (fun i => x i.val)

private def headLastEquiv (N : ℕ) : (Fin (N + 1) → G) ≃ᵐ (Fin N → G) × G :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => G) (Fin.last N)).trans
    (MeasurableEquiv.prodComm (α := G) (β := Fin N → G))

private theorem headLastEquiv_head (N : ℕ) (x : Fin (N + 1) → G) (i : Fin N) :
    (headLastEquiv N x).1 i = x i.castSucc := by
  change x ((Fin.last N).succAbove i) = x i.castSucc
  rw [Fin.succAbove_last]

private theorem headLastEquiv_last (N : ℕ) (x : Fin (N + 1) → G) :
    (headLastEquiv N x).2 = x (Fin.last N) := rfl

private theorem measurePreserving_headLastEquiv (N : ℕ) :
    MeasurePreserving (headLastEquiv (G := G) N) (Measure.pi (fun _ : Fin (N + 1) => μ))
      ((Measure.pi (fun _ : Fin N => μ)).prod μ) :=
  Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) (Fin.last N))

/-- Every finite triangular translation preserves product Haar probability. -/
theorem measurePreserving_triangularFinite
    (φ : ∀ n : ℕ, (Fin n → G) → G) (hφ : ∀ n, Measurable (φ n)) (N : ℕ) :
    MeasurePreserving (triangularFinite φ N) (Measure.pi (fun _ : Fin N => μ))
      (Measure.pi (fun _ : Fin N => μ)) := by
  induction N with
  | zero =>
    have he : triangularFinite φ 0 = id := by funext x i; exact Fin.elim0 i
    rw [he]
    exact MeasurePreserving.id _
  | succ N ih =>
    let e := headLastEquiv (G := G) N
    have he := measurePreserving_headLastEquiv μ N
    let f : (Fin N → G) × G → (Fin N → G) × G :=
      fun p => (triangularFinite φ N p.1, p.2 + φ N p.1)
    have hf : MeasurePreserving f ((Measure.pi (fun _ : Fin N => μ)).prod μ)
        ((Measure.pi (fun _ : Fin N => μ)).prod μ) := by
      apply ih.skew_product (measurable_snd.add ((hφ N).comp measurable_fst))
      exact Filter.Eventually.of_forall fun x => (measurePreserving_add_right μ (φ N x)).map_eq
    have hconj (x : Fin (N + 1) → G) : e (triangularFinite φ (N + 1) x) = f (e x) := by
      apply Prod.ext
      · funext i
        change (headLastEquiv N (triangularFinite φ (N + 1) x)).1 i =
          triangularFinite φ N (headLastEquiv N x).1 i
        rw [headLastEquiv_head]
        simp only [triangularFinite, strictPrefix, headLastEquiv_head]
      · change (headLastEquiv N (triangularFinite φ (N + 1) x)).2 =
          (headLastEquiv N x).2 + φ N (headLastEquiv N x).1
        rw [headLastEquiv_last, headLastEquiv_last]
        change x (Fin.last N) + φ N (fun i => x ⟨i.val, lt_trans i.isLt (Fin.last N).isLt⟩) = _
        congr 1
        funext i
        exact (headLastEquiv_head N x i).symm
    have hfun : triangularFinite φ (N + 1) = e.symm ∘ f ∘ e := by
      funext x
      apply e.injective
      exact (hconj x).trans (e.apply_symm_apply _).symm
    rw [hfun]
    exact (MeasurePreserving.symm e he).comp (hf.comp he)

theorem measurable_triangularSequence (φ : ∀ n : ℕ, (Fin n → G) → G)
    (hφ : ∀ n, Measurable (φ n)) : Measurable (triangularSequence φ) :=
  measurable_pi_lambda _ fun n =>
    (measurable_pi_apply n).add ((hφ n).comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.val))

private theorem triangularSequence_head (φ : ∀ n : ℕ, (Fin n → G) → G) (N : ℕ) :
    countableProductHead N ∘ triangularSequence φ =
      triangularFinite φ N ∘ countableProductHead N := by
  funext x i
  rfl

/-- Every finite marginal of the translated countable law is the original finite product law. -/
theorem map_triangularSequence_head (φ : ∀ n : ℕ, (Fin n → G) → G)
    (hφ : ∀ n, Measurable (φ n)) (N : ℕ) :
    Measure.map (countableProductHead N)
      (Measure.map (triangularSequence φ) (Measure.infinitePi (fun _ : ℕ => μ))) =
        Measure.pi (fun _ : Fin N => μ) := by
  have hh : Measurable (countableProductHead (α := G) N) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  rw [Measure.map_map hh (measurable_triangularSequence φ hφ), triangularSequence_head,
    ← Measure.map_map (measurePreserving_triangularFinite μ φ hφ N).measurable hh,
    map_countableProductHead_infinitePi]
  exact (measurePreserving_triangularFinite μ φ hφ N).map_eq

/-- Triangular translations preserve the actual countable product probability. -/
theorem measurePreserving_triangularSequence
    (φ : ∀ n : ℕ, (Fin n → G) → G) (hφ : ∀ n, Measurable (φ n)) :
    MeasurePreserving (triangularSequence φ) (Measure.infinitePi (fun _ : ℕ => μ))
      (Measure.infinitePi (fun _ : ℕ => μ)) := by
  refine ⟨measurable_triangularSequence φ hφ, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  let N := s.sup id + 1
  have hn (i : ℕ) (hi : i ∈ s) : i < N := by
    have h := Finset.le_sup (f := id) hi
    change i ≤ s.sup id at h
    omega
  let A : Set (Fin N → G) := {x | ∀ i : Fin N, i.val ∈ s → x i ∈ t i.val}
  have hA : MeasurableSet A := by
    change MeasurableSet (⋂ i : Fin N, ⋂ _ : i.val ∈ s,
      (fun x : Fin N → G => x i) ⁻¹' t i.val)
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (ht i.val).preimage (measurable_pi_apply i)
  have hpre : countableProductHead N ⁻¹' A = (s : Set ℕ).pi t := by
    ext x
    constructor
    · intro h i hi
      exact h ⟨i, hn i hi⟩ hi
    · intro h i hi
      exact h i.val hi
  have hh : Measurable (countableProductHead (α := G) N) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hm := map_triangularSequence_head μ φ hφ N
  have ho := map_countableProductHead_infinitePi μ N
  have he := congrArg (fun ν : Measure (Fin N → G) => ν A) (hm.trans ho.symm)
  rw [Measure.map_apply hh hA, Measure.map_apply hh hA, hpre] at he
  rw [he]
  exact Measure.infinitePi_pi _ (fun i _ => ht i)

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.measurePreserving_triangularSequence
