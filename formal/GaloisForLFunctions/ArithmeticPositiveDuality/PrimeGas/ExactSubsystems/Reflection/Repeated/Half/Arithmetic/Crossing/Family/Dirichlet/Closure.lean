import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Implication

/-! # Least blind spectra and exact interpolation of thermal observations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Set Finset

/-- All positive tests forced by a single reading. -/
def consequences (t : ℝ) : Set ℝ := {u | 0<u ∧ Forces t u}

private theorem self_mem {t : ℝ} (ht : 0<t) : t ∈ consequences t :=
  ⟨ht,fun _ _ h => h⟩

theorem consequences_subset {S : Set ℝ} {t : ℝ} (h : Attainable S) (mem : t ∈ S) :
    consequences t ⊆ S := by
  obtain ⟨n,a,asym,rfl⟩ := h
  exact fun u hu => ⟨hu.1,hu.2 n a mem.2.1,asym⟩

/-- Finitely many rival readings can be removed by intersecting with a
separating spectrum for each of them. -/
private theorem remove_orders {t : ℝ} (ht : 0<t) (F : Finset ℝ)
    (bad : ∀ u ∈ F, 0<u ∧ ¬Forces t u) (S : Set ℝ) (hs : Attainable S) (mem : t ∈ S) :
    ∃ A, Attainable A ∧ t ∈ A ∧ A ⊆ S ∧ ∀ u ∈ F, u ∉ A := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨S,hs,mem,Subset.rfl,fun u hu => (notMem_empty u hu).elim⟩
  | insert u F _ ih =>
    obtain ⟨A,ha,ta,sub,gone⟩ := ih (fun v hv => bad v (mem_insert_of_mem hv))
    obtain ⟨pos,no⟩ := bad u (mem_insert_self _ _)
    have failure := mt (forces_sets ht pos).mpr no
    push Not at failure
    obtain ⟨B,hb,tb,ub⟩ := failure
    refine ⟨A ∩ B,(attainable_union_inter ha hb).2,⟨ta,tb⟩,fun _ h => sub h.1,?_⟩
    intro v hv h
    rcases mem_insert.mp hv with rfl | inF
    · exact ub h.2
    · exact gone v inF h.1

/-- Among all false positives containing a resonant order, the intersection of
every possible blind set is itself the exact blind set of one finite spectrum. -/
theorem least_spectrum {t : ℝ} (ht : 0<t) (res : Resonant t) : Attainable (consequences t) := by
  classical
  obtain ⟨S,hs,ts⟩ := (contains_resonant ht).mpr res
  let finite := attainable_finite hs
  let F := finite.toFinset.filter (fun u => ¬Forces t u)
  have positive {u : ℝ} (hu : u ∈ S) : 0<u := by
    obtain ⟨_,_,_,rfl⟩ := hs
    exact hu.1
  have bad (u : ℝ) (hu : u ∈ F) : 0<u ∧ ¬Forces t u := by
    obtain ⟨mem,no⟩ := mem_filter.mp hu
    exact ⟨positive (finite.mem_toFinset.mp mem),no⟩
  obtain ⟨A,ha,ta,sub,gone⟩ := remove_orders ht F bad S hs ts
  have eq : A=consequences t := Set.Subset.antisymm (fun u hu => by
    refine ⟨positive (sub hu),?_⟩
    by_contra no
    exact gone u (mem_filter.mpr ⟨finite.mem_toFinset.mpr (sub hu),no⟩) hu) (consequences_subset ha ta)
  exact eq ▸ ha

/-- Joining the least spectra gives a spectrum with precisely the forced
readings of a finite resonant schedule. -/
theorem least_schedule (T : Finset ℝ) (ok : ∀ t ∈ T, 0<t ∧ Resonant t) :
    Attainable (⋃ t ∈ T, consequences t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Set.biUnion_empty_finset] using attainable_empty
  | insert t T _ ih =>
    have ht := ok t (mem_insert_self _ _)
    have rest := ih (fun u hu => ok u (mem_insert_of_mem hu))
    change Attainable (⋃ u ∈ (↑(insert t T) : Set ℝ), consequences u)
    rw [Finset.coe_insert,Set.biUnion_insert]
    exact (attainable_union_inter (least_spectrum ht.1 ht.2) rest).1

/-- A finite collection is the full blind set of a physical spectrum iff its
members are positive resonances and it is closed under every forced reading. -/
theorem full_blind_set_iff (S : Set ℝ) :
    Attainable S ↔ S.Finite ∧ ∀ t ∈ S, 0<t ∧ Resonant t ∧ consequences t ⊆ S := by
  classical
  constructor
  · intro hs
    refine ⟨attainable_finite hs,fun t mem => ?_⟩
    have ht : 0<t := by obtain ⟨_,_,_,rfl⟩ := hs; exact mem.1
    exact ⟨ht,(contains_resonant ht).mp ⟨S,hs,mem⟩,consequences_subset hs mem⟩
  · rintro ⟨finite,closed⟩
    have comp := least_schedule finite.toFinset (fun t ht =>
      ⟨(closed t (finite.mem_toFinset.mp ht)).1,(closed t (finite.mem_toFinset.mp ht)).2.1⟩)
    have eq : (⋃ t ∈ finite.toFinset, consequences t)=S := by
      apply Set.Subset.antisymm
      · exact iUnion_subset fun t => iUnion_subset fun ht => (closed t (finite.mem_toFinset.mp ht)).2.2
      · exact fun t ht => mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨finite.mem_toFinset.mpr ht,self_mem (closed t ht).1⟩⟩
    rwa [eq] at comp

/-- A finite list of positive readings and any collection of demanded
detections can be realized exactly when each reading is resonant and forces
none of the detections. The forbidden set may be infinite. -/
theorem interpolation_iff (T : Finset ℝ) (pos : ∀ t ∈ T, 0<t) (U : Set ℝ) :
    (∃ S, Attainable S ∧ (↑T : Set ℝ) ⊆ S ∧ Disjoint S U) ↔
      ∀ t ∈ T, Resonant t ∧ Disjoint (consequences t) U := by
  classical
  constructor
  · rintro ⟨S,hs,inc,dis⟩ t ht
    have mem := inc ht
    exact ⟨(contains_resonant (pos t ht)).mp ⟨S,hs,mem⟩,dis.mono_left (consequences_subset hs mem)⟩
  · intro ok
    refine ⟨_,least_schedule T (fun t ht => ⟨pos t ht,(ok t ht).1⟩),?_,?_⟩
    · intro t ht
      exact mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨ht,self_mem (pos t ht)⟩⟩
    · apply Set.disjoint_left.mpr
      intro u hu mem
      obtain ⟨t,ut⟩ := mem_iUnion.mp hu
      obtain ⟨ht,forced⟩ := mem_iUnion.mp ut
      exact Set.disjoint_left.mp (ok t ht).2 forced mem

#print axioms interpolation_iff
#print axioms least_spectrum
#print axioms least_schedule
#print axioms full_blind_set_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
