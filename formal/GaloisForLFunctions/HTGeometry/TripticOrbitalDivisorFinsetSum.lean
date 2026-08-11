import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorLinearity

/-!
# The orbital divisor of a finite sum of sources

Additivity of the orbital divisor is conditional on finite orbit support, so it propagates through a
finite sum only together with that support.  Both are proved by the same induction: the support of a
sum is contained in the union of the supports, and on that union the unrestricted sums split.

* `FiniteOrbitSupport`;
* `finiteOrbitSupport_finsetSum`, `meromorphicOn_finsetSum`;
* `additiveOrbitalDivisorAt_finsetSum`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A source whose boundary coefficients are nonzero at only finitely many points of an orbit. -/
def FiniteOrbitSupport (F : ℂ → ℂ) (σ p : ℂ) (ℓ : ℤ) : Prop :=
  {m : ℤ | laurentCoeff (fun w ↦ F (w + σ) - F w) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite

theorem meromorphicOn_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hm : ∀ i ∈ s, MeromorphicOn (f i) (Set.univ : Set ℂ)) :
    MeromorphicOn (∑ i ∈ s, f i) (Set.univ : Set ℂ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact fun z _ ↦ (analyticAt_const (x := z)).meromorphicAt
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact fun z _ ↦ (hm i (Finset.mem_insert_self i s) z (Set.mem_univ z)).add
        (ih (fun j hj ↦ hm j (Finset.mem_insert_of_mem hj)) z (Set.mem_univ z))

theorem finiteOrbitSupport_add {F G : ℂ → ℂ} {σ p : ℂ} {ℓ : ℤ}
    (hFm : MeromorphicOn F (Set.univ : Set ℂ)) (hGm : MeromorphicOn G (Set.univ : Set ℂ))
    (hF : FiniteOrbitSupport F σ p ℓ) (hG : FiniteOrbitSupport G σ p ℓ) :
    FiniteOrbitSupport (F + G) σ p ℓ := by
  refine (hF.union hG).subset fun m hm ↦ ?_
  simp only [Set.mem_setOf_eq, Set.mem_union] at hm ⊢
  by_contra hcon
  push Not at hcon
  apply hm
  have hFa : MeromorphicAt (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) :=
    (meromorphicAt_comp_add.mpr (hFm _ (Set.mem_univ _))).sub (hFm _ (Set.mem_univ _))
  have hGa : MeromorphicAt (fun z ↦ G (z + σ) - G z) (p + (m : ℂ) * σ) :=
    (meromorphicAt_comp_add.mpr (hGm _ (Set.mem_univ _))).sub (hGm _ (Set.mem_univ _))
  have hsplit : laurentCoeff (fun z ↦ (F + G) (z + σ) - (F + G) z) (p + (m : ℂ) * σ) ℓ
      = laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ
        + laurentCoeff (fun z ↦ G (z + σ) - G z) (p + (m : ℂ) * σ) ℓ := by
    rw [← laurentCoeff_add hFa hGa]
    congr 1
    funext z
    simp only [Pi.add_apply]
    ring
  rw [hsplit, hcon.1, hcon.2, add_zero]

theorem finiteOrbitSupport_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {σ p : ℂ} {ℓ : ℤ}
    (hm : ∀ i ∈ s, MeromorphicOn (f i) (Set.univ : Set ℂ))
    (hs : ∀ i ∈ s, FiniteOrbitSupport (f i) σ p ℓ) :
    FiniteOrbitSupport (∑ i ∈ s, f i) σ p ℓ := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hzero : ∀ m : ℤ, laurentCoeff (fun w : ℂ ↦ (∑ i ∈ (∅ : Finset ι), f i) (w + σ)
          - (∑ i ∈ (∅ : Finset ι), f i) w) (p + (m : ℂ) * σ) ℓ = 0 := by
        intro m
        have hfun : (fun w : ℂ ↦ (∑ i ∈ (∅ : Finset ι), f i) (w + σ)
            - (∑ i ∈ (∅ : Finset ι), f i) w) = fun _ : ℂ ↦ (0 : ℂ) * (1 : ℂ) := by
          funext w
          simp
        rw [hfun, laurentCoeff_const_mul (analyticAt_const (x := p + (m : ℂ) * σ)).meromorphicAt,
          zero_mul]
      exact Set.Finite.subset Set.finite_empty fun m hm ↦ absurd (hzero m) hm
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact finiteOrbitSupport_add (hm i (Finset.mem_insert_self i s))
        (meromorphicOn_finsetSum s f fun j hj ↦ hm j (Finset.mem_insert_of_mem hj))
        (hs i (Finset.mem_insert_self i s))
        (ih (fun j hj ↦ hm j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hs j (Finset.mem_insert_of_mem hj)))

/-- **The orbital divisor of a finite sum of sources with finite orbit support.** -/
theorem additiveOrbitalDivisorAt_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    {σ p : ℂ} {ℓ : ℤ}
    (hm : ∀ i ∈ s, MeromorphicOn (f i) (Set.univ : Set ℂ))
    (hs : ∀ i ∈ s, FiniteOrbitSupport (f i) σ p ℓ) :
    additiveOrbitalDivisorAt (∑ i ∈ s, f i) σ p ℓ
      = ∑ i ∈ s, additiveOrbitalDivisorAt (f i) σ p ℓ := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have hfun : (fun z : ℂ ↦ (0 : ℂ → ℂ) (z + σ) - (0 : ℂ → ℂ) z) = fun _ : ℂ ↦ (0 : ℂ) := by
        funext z
        simp
      rw [additiveOrbitalDivisorAt, hfun]
      have hz : ∀ m : ℤ, laurentCoeff (fun _ : ℂ ↦ (0 : ℂ)) (p + (m : ℂ) * σ) ℓ = 0 := by
        intro m
        have hcongr : (fun _ : ℂ ↦ (0 : ℂ)) = fun z : ℂ ↦ (0 : ℂ) * (1 : ℂ) := by
          funext z
          ring
        rw [hcongr, laurentCoeff_const_mul (analyticAt_const (x := p + (m : ℂ) * σ)).meromorphicAt,
          zero_mul]
      rw [finsum_congr hz, finsum_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        additiveOrbitalDivisorAt_add (hm i (Finset.mem_insert_self i s))
          (meromorphicOn_finsetSum s f fun j hj ↦ hm j (Finset.mem_insert_of_mem hj))
          (hs i (Finset.mem_insert_self i s))
          (finiteOrbitSupport_finsetSum s f (fun j hj ↦ hm j (Finset.mem_insert_of_mem hj))
            (fun j hj ↦ hs j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj ↦ hm j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hs j (Finset.mem_insert_of_mem hj))]

end

end GaloisForLFunctions.HTGeometry
