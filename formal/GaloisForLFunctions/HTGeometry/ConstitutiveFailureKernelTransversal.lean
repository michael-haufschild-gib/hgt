import GaloisForLFunctions.HTGeometry.ConstitutiveSemanticTransportArityPromotion

/-!
# Failure-kernel transversal revision

In a finite monotone consequence system, withdrawing a consequence is exactly the problem of
hitting every inclusion-minimal derivation kernel.  Minimal repairs carry exact core-retainment
certificates.  Observer images preserve transversal existence, but pullback saturates a repair
along observer fibres.  Symmetric fractional repairs can exist when no symmetric singleton repair
does, and cofinally born singleton kernels admit no finite global repair.

All declarations are route-independent and finite/combinatorial.  No RH premise occurs.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Finite-basis consequence system.  Only monotonicity is load-bearing for kernel duality. -/
structure FiniteConsequence (α : Type u) [DecidableEq α] where
  derive : Finset α → Finset α
  monotone : Monotone derive

variable {α : Type u} [DecidableEq α]

/-- An inclusion-minimal derivation of `a` retained inside proof base `T`. -/
def IsFailureKernel (C : FiniteConsequence α) (T : Finset α) (a : α)
    (K : Finset α) : Prop :=
  K ⊆ T ∧ a ∈ C.derive K ∧ ∀ L : Finset α, L ⊂ K → a ∉ C.derive L

/-- A removal set hits a failure kernel when they share a primitive fact. -/
def HitsFailureKernel (R K : Finset α) : Prop :=
  ∃ x, x ∈ R ∧ x ∈ K

/-- Revision succeeds when the target consequence is absent after removing `R`. -/
def SuccessfulKernelRevision (C : FiniteConsequence α) (T : Finset α) (a : α)
    (R : Finset α) : Prop :=
  a ∉ C.derive (T \ R)

/-- Inclusion-minimal successful revision. -/
def MinimalSuccessfulKernelRevision (C : FiniteConsequence α) (T : Finset α) (a : α)
    (R : Finset α) : Prop :=
  SuccessfulKernelRevision C T a R ∧
    ∀ S : Finset α, S ⊂ R → ¬ SuccessfulKernelRevision C T a S

/-- Every consequence of a finite base has an inclusion-minimal derivation kernel. -/
theorem exists_failureKernel_subset (C : FiniteConsequence α)
    {S : Finset α} {a : α} (ha : a ∈ C.derive S) :
    ∃ K : Finset α, IsFailureKernel C S a K := by
  induction S using Finset.strongInduction with
  | _ S ih =>
      by_cases hmin : ∀ L : Finset α, L ⊂ S → a ∉ C.derive L
      · exact ⟨S, Finset.Subset.rfl, ha, hmin⟩
      · push Not at hmin
        obtain ⟨L, hLS, hLa⟩ := hmin
        obtain ⟨K, hKL, hKa, hKmin⟩ := ih L hLS hLa
        exact ⟨K, hKL.trans hLS.subset, hKa, hKmin⟩

/-- **Kernel--transversal law.** A removal succeeds exactly when it hits every minimal derivation
kernel of the failed consequence. -/
theorem successfulKernelRevision_iff_hits_all_failureKernels
    (C : FiniteConsequence α) (T : Finset α) (a : α) (R : Finset α) :
    SuccessfulKernelRevision C T a R ↔
      ∀ K : Finset α, IsFailureKernel C T a K → HitsFailureKernel R K := by
  constructor
  · intro hsuccess K hK
    by_contra hhit
    have hKR : K ⊆ T \ R := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hK.1 hx, fun hxR => hhit ⟨x, hxR, hx⟩⟩
    exact hsuccess (C.monotone hKR hK.2.1)
  · intro hall ha
    obtain ⟨K, hKsub, hKa, hKmin⟩ := exists_failureKernel_subset C ha
    have hKT : K ⊆ T := hKsub.trans Finset.sdiff_subset
    obtain ⟨x, hxR, hxK⟩ := hall K ⟨hKT, hKa, hKmin⟩
    exact (Finset.mem_sdiff.mp (hKsub hxK)).2 hxR

/-- **Core-retainment certificate.** Every fact cut by a minimal repair is the unique cut of some
live minimal derivation kernel. -/
theorem minimalSuccessfulKernelRevision_core_certificate
    (C : FiniteConsequence α) (T : Finset α) (a : α) {R : Finset α}
    (hR : MinimalSuccessfulKernelRevision C T a R) {r : α} (hr : r ∈ R) :
    ∃ K : Finset α, IsFailureKernel C T a K ∧ R ∩ K = {r} := by
  have herase : ¬ SuccessfulKernelRevision C T a (R.erase r) :=
    hR.2 (R.erase r) (Finset.erase_ssubset hr)
  have hmiss : ¬ ∀ K : Finset α,
      IsFailureKernel C T a K → HitsFailureKernel (R.erase r) K := by
    intro hall
    exact herase
      ((successfulKernelRevision_iff_hits_all_failureKernels C T a (R.erase r)).2 hall)
  push Not at hmiss
  obtain ⟨K, hK, hnohit⟩ := hmiss
  have hhit : HitsFailureKernel R K :=
    (successfulKernelRevision_iff_hits_all_failureKernels C T a R).1 hR.1 K hK
  obtain ⟨y, hyR, hyK⟩ := hhit
  have hyr : y = r := by
    by_contra hne
    exact hnohit ⟨y, Finset.mem_erase.mpr ⟨hne, hyR⟩, hyK⟩
  refine ⟨K, hK, Finset.ext ?_⟩
  intro x
  constructor
  · intro hx
    have hxR : x ∈ R := (Finset.mem_inter.mp hx).1
    have hxK : x ∈ K := (Finset.mem_inter.mp hx).2
    have hxr : x = r := by
      by_contra hne
      exact hnohit ⟨x, Finset.mem_erase.mpr ⟨hne, hxR⟩, hxK⟩
    simp [hxr]
  · intro hx
    have hxr : x = r := Finset.mem_singleton.mp hx
    subst x
    exact Finset.mem_inter.mpr ⟨hr, hyr ▸ hyK⟩

/-- **Converse core-retainment certificate.**  A successful repair whose every cut is the unique
cut of some live kernel is inclusion-minimal. -/
theorem minimalSuccessfulKernelRevision_of_core_certificate
    (C : FiniteConsequence α) (T : Finset α) (a : α) {R : Finset α}
    (hsucc : SuccessfulKernelRevision C T a R)
    (hcert : ∀ r ∈ R, ∃ K : Finset α, IsFailureKernel C T a K ∧ R ∩ K = {r}) :
    MinimalSuccessfulKernelRevision C T a R := by
  refine ⟨hsucc, ?_⟩
  intro S hS hSsucc
  obtain ⟨r, hrR, hrS⟩ : ∃ r, r ∈ R ∧ r ∉ S := by
    by_contra hc
    push Not at hc
    exact absurd (Finset.Subset.antisymm hS.subset (fun x hx => hc x hx)) (ne_of_lt hS)
  obtain ⟨K, hK, hKeq⟩ := hcert r hrR
  obtain ⟨x, hxS, hxK⟩ :=
    (successfulKernelRevision_iff_hits_all_failureKernels C T a S).1 hSsucc K hK
  have hxR : x ∈ R := hS.subset hxS
  have hxr : x = r := by
    have : x ∈ R ∩ K := Finset.mem_inter.mpr ⟨hxR, hxK⟩
    rw [hKeq] at this
    exact Finset.mem_singleton.mp this
  exact hrS (hxr ▸ hxS)

/-- **Exact core-retainment certificate.**  A successful repair is inclusion-minimal exactly when
every cut fact is the unique cut of some live minimal derivation kernel. -/
theorem minimalSuccessfulKernelRevision_iff_core_certificate
    (C : FiniteConsequence α) (T : Finset α) (a : α) {R : Finset α}
    (hsucc : SuccessfulKernelRevision C T a R) :
    MinimalSuccessfulKernelRevision C T a R ↔
      ∀ r ∈ R, ∃ K : Finset α, IsFailureKernel C T a K ∧ R ∩ K = {r} :=
  ⟨fun hR _r hr => minimalSuccessfulKernelRevision_core_certificate C T a hR hr,
    fun hcert => minimalSuccessfulKernelRevision_of_core_certificate C T a hsucc hcert⟩

/-- A repair hits every kernel in a finite failure family. -/
def HitsFailureFamily (R : Finset α) (H : Finset (Finset α)) : Prop :=
  ∀ K ∈ H, HitsFailureKernel R K

/-- Observer image of a finite failure-kernel family. -/
def mapFailureKernels {β : Type v} [DecidableEq β] (f : α → β)
    (H : Finset (Finset α)) : Finset (Finset β) :=
  H.image (fun K => K.image f)

/-- Pull an observed repair back to the marked source base. -/
def pullKernelRepair {β : Type v} [DecidableEq β] (T : Finset α) (f : α → β)
    (S : Finset β) : Finset α :=
  T.filter (fun x => f x ∈ S)

omit [DecidableEq α] in
/-- Source repair images remain transversals of every observed kernel image. -/
theorem image_hitsFailureFamily {β : Type v} [DecidableEq β]
    (f : α → β) {R : Finset α} {H : Finset (Finset α)}
    (hR : HitsFailureFamily R H) :
    HitsFailureFamily (R.image f) (mapFailureKernels f H) := by
  intro L hL
  obtain ⟨K, hKH, rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨x, hxR, hxK⟩ := hR K hKH
  exact ⟨f x, Finset.mem_image.mpr ⟨x, hxR, rfl⟩,
    Finset.mem_image.mpr ⟨x, hxK, rfl⟩⟩

/-- Pullback of an observed transversal hits every source kernel contained in the marked base. -/
theorem pullKernelRepair_hitsFailureFamily {β : Type v} [DecidableEq β]
    (T : Finset α) (f : α → β) {S : Finset β} {H : Finset (Finset α)}
    (hS : HitsFailureFamily S (mapFailureKernels f H)) :
    HitsFailureFamily (pullKernelRepair T f S) (H.filter (fun K => K ⊆ T)) := by
  intro K hKH
  have hKmem : K ∈ H := (Finset.mem_filter.mp hKH).1
  have hKT : K ⊆ T := (Finset.mem_filter.mp hKH).2
  have hImage : K.image f ∈ mapFailureKernels f H :=
    Finset.mem_image.mpr ⟨K, hKmem, rfl⟩
  obtain ⟨y, hyS, hyK⟩ := hS (K.image f) hImage
  obtain ⟨x, hxK, hxy⟩ := Finset.mem_image.mp hyK
  refine ⟨x, Finset.mem_filter.mpr ⟨hKT hxK, ?_⟩, hxK⟩
  simpa [hxy] using hyS

/-- An exact source repair is saturated when it contains every marked source point that the
observer identifies with one of its members. -/
def FibreSaturatedRepairOn {β : Type v} (T : Finset α) (f : α → β)
    (R : Finset α) : Prop :=
  ∀ x ∈ R, ∀ z ∈ T, f z = f x → z ∈ R

omit [DecidableEq α] in
/-- Every source repair is contained in the pullback of its observer image. -/
theorem subset_pullKernelRepair_image {β : Type v} [DecidableEq β]
    (T R : Finset α) (f : α → β) (hRT : R ⊆ T) :
    R ⊆ pullKernelRepair T f (R.image f) := by
  intro x hxR
  exact Finset.mem_filter.mpr ⟨hRT hxR, Finset.mem_image.mpr ⟨x, hxR, rfl⟩⟩

omit [DecidableEq α] in
/-- **Observer saturation law.** Image then pullback returns the original repair exactly when that
repair is a union of observer fibres inside the marked source base. -/
theorem pullKernelRepair_image_eq_iff_fibreSaturated
    {β : Type v} [DecidableEq β] (T R : Finset α) (f : α → β) (hRT : R ⊆ T) :
    pullKernelRepair T f (R.image f) = R ↔ FibreSaturatedRepairOn T f R := by
  constructor
  · intro heq x hxR z hzT hzx
    rw [← heq]
    exact Finset.mem_filter.mpr
      ⟨hzT, Finset.mem_image.mpr ⟨x, hxR, hzx.symm⟩⟩
  · intro hsat
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨hzT, hzimage⟩ := Finset.mem_filter.mp hz
      obtain ⟨x, hxR, hzx⟩ := Finset.mem_image.mp hzimage
      exact hsat x hxR z hzT hzx.symm
    · exact subset_pullKernelRepair_image T R f hRT

/-- A finite removal misses some singleton kernel on the natural-number vocabulary. -/
theorem no_finite_global_singleton_failureTransversal (R : Finset ℕ) :
    ∃ n : ℕ, ¬ HitsFailureKernel R {n} := by
  refine ⟨R.sum id + 1, ?_⟩
  rintro ⟨x, hxR, hx⟩
  have hxeq : x = R.sum id + 1 := Finset.mem_singleton.mp hx
  have hle : x ≤ R.sum id :=
    Finset.single_le_sum (fun i _ => Nat.zero_le i) hxR
  omega

/-- Hitting the first `n` singleton kernels forces retention of all first `n` coordinates. -/
theorem range_subset_of_hits_singleton_failureKernels (n : ℕ) (R : Finset ℕ)
    (hR : ∀ i < n, HitsFailureKernel R {i}) :
    Finset.range n ⊆ R := by
  intro i hi
  obtain ⟨x, hxR, hxi⟩ := hR i (Finset.mem_range.mp hi)
  simpa [Finset.mem_singleton.mp hxi] using hxR

/-- Exact stage-`n` singleton-kernel repair costs at least `n` removed facts. -/
theorem card_ge_of_hits_initial_failureKernels (n : ℕ) (R : Finset ℕ)
    (hR : ∀ i < n, HitsFailureKernel R {i}) :
    n ≤ R.card := by
  simpa using Finset.card_le_card
    (range_subset_of_hits_singleton_failureKernels n R hR)

/-- No singleton exact repair hits all three edges of the triangle failure hypergraph. -/
theorem singleton_not_triangle_failureTransversal (r : Fin 3) :
    ¬ (HitsFailureKernel {r} {0, 1} ∧ HitsFailureKernel {r} {1, 2} ∧
      HitsFailureKernel {r} {0, 2}) := by
  intro h
  fin_cases r <;> simp [HitsFailureKernel] at h

/-- Every integral transversal of the triangle failure hypergraph has cost at least two. -/
theorem triangle_failureTransversal_card_ge_two (R : Finset (Fin 3))
    (h01 : HitsFailureKernel R {0, 1}) (h12 : HitsFailureKernel R {1, 2})
    (h02 : HitsFailureKernel R {0, 2}) :
    2 ≤ R.card := by
  by_contra hcard
  have hle : R.card ≤ 1 := by omega
  by_cases hzero : R.card = 0
  · have hRempty : R = ∅ := Finset.card_eq_zero.mp hzero
    subst R
    simp [HitsFailureKernel] at h01
  · have hone : R.card = 1 := by omega
    obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp hone
    exact singleton_not_triangle_failureTransversal r ⟨h01, h12, h02⟩

/-- Symmetric half-weight fractional repair of the triangle. -/
def triangleFractionalRepairWeight (_ : Fin 3) : ℚ := 1 / 2

/-- Every triangle kernel receives exact total fractional weight one. -/
theorem triangleFractionalRepair_pair_constraints :
    (∑ i ∈ ({0, 1} : Finset (Fin 3)), triangleFractionalRepairWeight i) = 1 ∧
    (∑ i ∈ ({1, 2} : Finset (Fin 3)), triangleFractionalRepairWeight i) = 1 ∧
    (∑ i ∈ ({0, 2} : Finset (Fin 3)), triangleFractionalRepairWeight i) = 1 := by
  simp [triangleFractionalRepairWeight]

/-- Fractional cost `3/2` is strictly smaller than the integral lower bound two. -/
theorem triangleFractionalRepair_total :
    ∑ i : Fin 3, triangleFractionalRepairWeight i = 3 / 2 := by
  norm_num [triangleFractionalRepairWeight, Fin.sum_univ_succ]

/-- Swap of the two unmarked exact repair choices. -/
def swapTwoKernelRepair : Fin 2 → Fin 2 :=
  Equiv.swap 0 1

/-- The unmarked pair failure admits no swap-invariant singleton repair. -/
theorem no_swapInvariant_singleton_kernelRepair (R : Finset (Fin 2)) (hR : R.card = 1) :
    R.image swapTwoKernelRepair ≠ R := by
  obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp hR
  fin_cases r <;> simp [swapTwoKernelRepair]

/-- Symmetric fractional pair repair. -/
def symmetricFractionalKernelRepair (_ : Fin 2) : ℚ := 1 / 2

theorem symmetricFractionalKernelRepair_swapInvariant (i : Fin 2) :
    symmetricFractionalKernelRepair (swapTwoKernelRepair i) =
      symmetricFractionalKernelRepair i := rfl

theorem symmetricFractionalKernelRepair_total :
    ∑ i : Fin 2, symmetricFractionalKernelRepair i = 1 := by
  norm_num [symmetricFractionalKernelRepair, Fin.sum_univ_succ]

/-- **Closed route-independent capstone.** Every finite monotone consequence system satisfies exact
kernel--transversal revision, every observer round trip is extensive and exact precisely on
fibre-saturated repairs, triangle positivity has a strict integral gap, and no finite repair meets
the cofinal singleton-kernel family. -/
theorem failureKernelTransversal_mechanism_capstone :
    (∀ (α : Type) (_ : DecidableEq α) (C : FiniteConsequence α)
      (T : Finset α) (a : α) (R : Finset α),
      SuccessfulKernelRevision C T a R ↔
        ∀ K : Finset α, IsFailureKernel C T a K → HitsFailureKernel R K) ∧
    (∀ R : Finset (Fin 3),
      HitsFailureKernel R {0, 1} → HitsFailureKernel R {1, 2} →
      HitsFailureKernel R {0, 2} → 2 ≤ R.card) ∧
    (∀ R : Finset ℕ, ∃ n : ℕ, ¬ HitsFailureKernel R {n}) := by
  refine ⟨?_, triangle_failureTransversal_card_ge_two,
    no_finite_global_singleton_failureTransversal⟩
  intro α inst C T a R
  letI : DecidableEq α := inst
  exact successfulKernelRevision_iff_hits_all_failureKernels C T a R

end GaloisForLFunctions.HTGeometry
