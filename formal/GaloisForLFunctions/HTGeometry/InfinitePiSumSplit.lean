import Mathlib.Probability.ProductMeasure

/-!
# Splitting an infinite product law into two independent blocks

An infinite product of probability laws indexed by a sum type is the product of the two block
laws, and a countable index set splits into a finite head and the remaining tail.  Both statements
are obtained from the characterization of the product measure by its values on finite rectangles.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Block splitting of an infinite product law.** -/
theorem map_sumPiEquivProdPi_infinitePi {α β : Type*} {X : α ⊕ β → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    Measure.map (MeasurableEquiv.sumPiEquivProdPi X).symm
        ((Measure.infinitePi (fun a => μ (Sum.inl a))).prod
          (Measure.infinitePi (fun b => μ (Sum.inr b))))
      = Measure.infinitePi μ := by
  classical
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  have hmeas : MeasurableSet ((s : Set (α ⊕ β)).pi t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable hmeas]
  have hpre : (MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' ((s : Set (α ⊕ β)).pi t)
      = ((s.toLeft : Set α).pi (fun a => t (Sum.inl a))) ×ˢ
        ((s.toRight : Set β).pi (fun b => t (Sum.inr b))) := by
    ext p
    constructor
    · intro hp
      constructor
      · intro a ha
        exact hp (Sum.inl a) (by simpa using Finset.mem_toLeft.1 ha)
      · intro b hb
        exact hp (Sum.inr b) (by simpa using Finset.mem_toRight.1 hb)
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | inl a => exact h1 a (by simpa using Finset.mem_toLeft.2 (by simpa using hi))
      | inr b => exact h2 b (by simpa using Finset.mem_toRight.2 (by simpa using hi))
  rw [hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun a _ => ht (Sum.inl a)),
    Measure.infinitePi_pi _ (fun b _ => ht (Sum.inr b)),
    ← Finset.prod_disjSum s.toLeft s.toRight (fun i => μ i (t i)),
    Finset.toLeft_disjSum_toRight]

/-- The equivalence splitting `ℕ` into its first `N` values and the rest. -/
def natHeadTailEquiv (N : ℕ) : ℕ ≃ Fin N ⊕ ℕ where
  toFun n := if h : n < N then Sum.inl ⟨n, h⟩ else Sum.inr (n - N)
  invFun := Sum.elim (fun i : Fin N => (i : ℕ)) (fun k => k + N)
  left_inv n := by
    by_cases h : n < N
    · simp [h]
    · simp only [h, dif_neg, Sum.elim_inr, not_false_eq_true]
      omega
  right_inv := by
    rintro (i | k)
    · simp only [Sum.elim_inl, dif_pos i.isLt]
    · have h : ¬ (k + N < N) := by omega
      simp only [Sum.elim_inr, dif_neg h]
      congr 1
      omega

@[simp]
theorem natHeadTailEquiv_symm_inl (N : ℕ) (i : Fin N) :
    (natHeadTailEquiv N).symm (Sum.inl i) = (i : ℕ) := rfl

@[simp]
theorem natHeadTailEquiv_symm_inr (N : ℕ) (k : ℕ) :
    (natHeadTailEquiv N).symm (Sum.inr k) = k + N := rfl

/-- **Head–tail splitting of a countable product law.**  The first `N` coordinates and the rest are
independent, with the finite product law on the head. -/
theorem map_headTail_infinitePi {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (N : ℕ) :
    Measure.map (fun x : ℕ → Y => ((fun i : Fin N => x (i : ℕ)), fun k : ℕ => x (k + N)))
        (Measure.infinitePi (fun _ : ℕ => μ))
      = (Measure.pi (fun _ : Fin N => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ)) := by
  classical
  set e : ℕ ≃ Fin N ⊕ ℕ := natHeadTailEquiv N with he
  set X : Fin N ⊕ ℕ → Type _ := fun _ => Y with hX
  have hsplit := map_sumPiEquivProdPi_infinitePi (X := X) (fun _ => μ)
  have hcongr : Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Y) e.symm)
      (Measure.infinitePi (fun i : Fin N ⊕ ℕ => μ)) = Measure.infinitePi (fun _ : ℕ => μ) :=
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) e.symm
  have hcomp : (fun x : ℕ → Y => ((fun i : Fin N => x (i : ℕ)), fun k : ℕ => x (k + N)))
      = (MeasurableEquiv.sumPiEquivProdPi X) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Y) e.symm).symm := by
    funext x
    rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.sumPiEquivProdPi X).measurable
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Y) e.symm).symm.measurable]
  have h1 : Measure.map (MeasurableEquiv.piCongrLeft (fun _ : ℕ => Y) e.symm).symm
      (Measure.infinitePi (fun _ : ℕ => μ))
      = Measure.infinitePi (fun _ : Fin N ⊕ ℕ => μ) := by
    rw [← hcongr]
    exact MeasurableEquiv.map_symm_map _
  rw [h1, ← hsplit, MeasurableEquiv.map_map_symm, Measure.infinitePi_eq_pi]

end

end GaloisForLFunctions.HTGeometry
