import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.BoundaryTateTrace

/-!
# Kloosterman moments and the compactified reciprocal locus

The homogeneous reciprocal zero locus splits into its torus and coordinate
boundary. Counting scalar representatives identifies its projective torus with
the normalized double-zero locus. The moment identity then separates the
compactified point count from an explicit signed Tate trace.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

section Homogeneity

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Clearing reciprocal denominators gives a homogeneous equation of degree `n−1`. -/
theorem reciprocalClearedValue_scale (a : F) (x : ι → F) :
    reciprocalClearedValue (fun i => a * x i) =
      a ^ (Fintype.card ι - 1) * reciprocalClearedValue x := by
  rw [reciprocalClearedValue, reciprocalClearedValue, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ i), card_univ]

/-- The homogeneous zero locus is invariant under nonzero scalar multiplication. -/
theorem reciprocalClearedValue_scale_zero_iff (u : Fˣ) (x : ι → F) :
    reciprocalClearedValue (fun i => (u : F) * x i) = 0 ↔ reciprocalClearedValue x = 0 := by
  rw [reciprocalClearedValue_scale, mul_eq_zero]
  exact or_iff_right (pow_ne_zero _ u.ne_zero)

/-- On the torus, the cleared value is the coordinate product times the reciprocal sum. -/
theorem reciprocalClearedValue_eq (x : ι → F) (hx : ∀ i, x i ≠ 0) :
    reciprocalClearedValue x = (∏ i, x i) * ∑ i, (x i)⁻¹ := by
  rw [reciprocalClearedValue, mul_sum]
  apply sum_congr rfl
  intro i _
  symm
  rw [← prod_erase_mul univ x (mem_univ i), mul_assoc, mul_inv_cancel₀ (hx i), mul_one]

/-- Denominator clearing preserves the zero equation on the torus. -/
theorem reciprocalClearedValue_zero_iff (x : ι → F) (hx : ∀ i, x i ≠ 0) :
    reciprocalClearedValue x = 0 ↔ (∑ i, (x i)⁻¹) = 0 := by
  rw [reciprocalClearedValue_eq x hx, mul_eq_zero]
  exact or_iff_right (prod_ne_zero_iff.mpr (fun i _ => hx i))

end Homogeneity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Nonzero vectors in the coordinate-sum hyperplane. -/
abbrev FullZeroCone (n : ℕ) := ↥(boundedSupportZeroSum (F := F) (ι := Fin n) n)

theorem mem_fullZeroCone_iff (n : ℕ) (x : Fin n → F) :
    x ∈ boundedSupportZeroSum n ↔ (∃ i, x i ≠ 0) ∧ ∑ i, x i = 0 := by
  simp only [boundedSupportZeroSum, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hp, _, hs⟩
    obtain ⟨i, hi⟩ := card_pos.mp hp
    exact ⟨⟨i, HTGeometry.mem_configSupport.mp hi⟩, hs⟩
  · rintro ⟨⟨i, hi⟩, hs⟩
    refine ⟨card_pos.mpr ⟨i, HTGeometry.mem_configSupport.mpr hi⟩, ?_, hs⟩
    simpa only [Fintype.card_fin] using card_le_univ (HTGeometry.configSupport 0 x)

/-- The nonzero affine cone of the compactified reciprocal locus. -/
def reciprocalCone (n : ℕ) : Finset (FullZeroCone (F := F) n) :=
  univ.filter (fun x => reciprocalClearedValue x.val = 0)

/-- The homogeneous reciprocal zero locus inside the actual projective hyperplane. -/
def projectiveReciprocalLocus (n : ℕ) :
    Finset (ProjectiveSupportZeroSum (F := F) (ι := Fin n) n) :=
  univ.filter (fun q => reciprocalClearedValue q.out.val = 0)

/-- The projective equation is independent of the representative. -/
theorem mem_projectiveReciprocalLocus_iff (n : ℕ) (x : FullZeroCone (F := F) n) :
    Quotient.mk (supportScalarSetoid n) x ∈ projectiveReciprocalLocus n ↔
      reciprocalClearedValue x.val = 0 := by
  obtain ⟨u, hu⟩ := Quotient.mk_out (s := supportScalarSetoid n) x
  have heq : (Quotient.mk (supportScalarSetoid n) x).out.val =
      fun i => (u : F) * x.val i := funext hu
  constructor
  · intro hx
    have hv : reciprocalClearedValue (Quotient.mk (supportScalarSetoid n) x).out.val = 0 :=
      (mem_filter.mp hx).2
    rwa [heq, reciprocalClearedValue_scale_zero_iff] at hv
  · intro hx
    apply mem_filter.mpr
    refine ⟨mem_univ (α := ProjectiveSupportZeroSum (F := F) (ι := Fin n) n) _, ?_⟩
    rwa [heq, reciprocalClearedValue_scale_zero_iff]

/-- Every projective point of the compactification has exactly `q−1` scalar representatives. -/
theorem reciprocalCone_card_orbits (n : ℕ) :
    (reciprocalCone (F := F) n).card =
      (projectiveReciprocalLocus (F := F) n).card * (Fintype.card F - 1) := by
  classical
  let π : FullZeroCone (F := F) n → ProjectiveSupportZeroSum (F := F) (ι := Fin n) n :=
    Quotient.mk (supportScalarSetoid n)
  have hsplit : reciprocalCone (F := F) n = (projectiveReciprocalLocus n).biUnion
      (fun q => univ.filter (fun x : FullZeroCone (F := F) n => π x = q)) := by
    ext x
    simp only [reciprocalCone, mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hx
      exact ⟨π x, (mem_projectiveReciprocalLocus_iff n x).mpr hx, rfl⟩
    · rintro ⟨q, hq, hx⟩
      apply (mem_projectiveReciprocalLocus_iff n x).mp
      change π x ∈ projectiveReciprocalLocus n
      rwa [hx]
  rw [hsplit, card_biUnion]
  · have hf : ∀ q : ProjectiveSupportZeroSum (F := F) (ι := Fin n) n,
        (univ.filter (fun x : FullZeroCone (F := F) n => π x = q)).card =
          Fintype.card F - 1 := by
      intro q
      rw [← Fintype.card_subtype, ← Fintype.card_units F]
      convert (Fintype.card_congr (projectiveSupportFiberEquiv n q)).symm <;> rfl
    rw [sum_congr rfl (fun q _ => hf q), sum_const, nsmul_eq_mul, Nat.cast_id]
  · intro q _ q' _ hne
    apply disjoint_left.mpr
    intro x hx hy
    exact hne ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)

/-- Representatives with at least one zero coordinate. -/
def reciprocalBoundaryCone (n : ℕ) : Finset (FullZeroCone (F := F) n) :=
  (reciprocalCone n).filter (fun x => ∃ i, x.val i = 0)

/-- Representatives with every coordinate nonzero. -/
def reciprocalTorusCone (n : ℕ) : Finset (FullZeroCone (F := F) n) :=
  (reciprocalCone n).filter (fun x => ∀ i, x.val i ≠ 0)

/-- The compactified cone is the disjoint union of its boundary and torus. -/
theorem reciprocalCone_card_split (n : ℕ) :
    (reciprocalCone (F := F) n).card =
      (reciprocalBoundaryCone (F := F) n).card + (reciprocalTorusCone (F := F) n).card := by
  have heq : reciprocalCone (F := F) n = reciprocalBoundaryCone n ∪ reciprocalTorusCone n := by
    ext x
    simp only [reciprocalBoundaryCone, reciprocalTorusCone, mem_union, mem_filter]
    constructor
    · intro hx
      by_cases hz : ∃ i, x.val i = 0
      · exact Or.inl ⟨hx, hz⟩
      · exact Or.inr ⟨hx, fun i hi => hz ⟨i, hi⟩⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hd : Disjoint (reciprocalBoundaryCone (F := F) n) (reciprocalTorusCone n) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi⟩ := (mem_filter.mp hx).2
    exact (mem_filter.mp hy).2 i hi
  rw [heq, card_union_of_disjoint hd]

/-- The boundary representatives are exactly the previously counted coordinate boundary cone. -/
theorem reciprocalBoundaryCone_card (n : ℕ) :
    (reciprocalBoundaryCone (F := F) n).card =
      (coordinateBoundaryCone (F := F) (ι := Fin n)).card := by
  apply card_bij (fun (x : FullZeroCone (F := F) n) _ => x.val)
  · intro x hx
    have hfull := (mem_fullZeroCone_iff n x.val).mp x.property
    have hvalue := (mem_filter.mp (mem_filter.mp hx).1).2
    exact (mem_coordinateBoundaryCone_iff x.val).mpr
      ⟨hfull.2, hfull.1, (mem_filter.mp hx).2, hvalue⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro y hy
    have hg := (mem_coordinateBoundaryCone_iff y).mp hy
    let x : FullZeroCone (F := F) n := ⟨y, (mem_fullZeroCone_iff n y).mpr ⟨hg.2.1, hg.1⟩⟩
    refine ⟨x, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hg.2.2.2⟩, hg.2.2.1⟩

/-- With at least one coordinate, torus representatives satisfy the two original sum equations. -/
theorem reciprocalTorusCone_card (m : ℕ) :
    (reciprocalTorusCone (F := F) (m + 1)).card = (doubleZeroTorus (F := F) (m + 1)).card := by
  apply card_bij (fun (x : FullZeroCone (F := F) (m + 1))
    (hx : x ∈ reciprocalTorusCone (F := F) (m + 1)) =>
    fun i : Fin (m + 1) => (⟨x.val i, (mem_filter.mp hx).2 i⟩ : {a : F // a ≠ 0}))
  · intro x hx
    have hfull := (mem_fullZeroCone_iff (m + 1) x.val).mp x.property
    have hvalue := (mem_filter.mp (mem_filter.mp hx).1).2
    have hr := (reciprocalClearedValue_zero_iff x.val (mem_filter.mp hx).2).mp hvalue
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hfull.2⟩, hr⟩
  · intro x _ y _ h
    apply Subtype.ext
    funext i
    exact congrArg (fun z : {a : F // a ≠ 0} => z.val) (congrFun h i)
  · intro y hy
    have hs := (mem_filter.mp (mem_filter.mp hy).1).2
    have hr := (mem_filter.mp hy).2
    let x : FullZeroCone (F := F) (m + 1) :=
      ⟨fun i => (y i : F), (mem_fullZeroCone_iff (m + 1) _).mpr ⟨⟨0, (y 0).property⟩, hs⟩⟩
    have hn : ∀ i, x.val i ≠ 0 := fun i => (y i).property
    refine ⟨x, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hn⟩, ?_⟩
    · exact (reciprocalClearedValue_zero_iff x.val hn).mpr hr
    · funext i
      exact Subtype.ext rfl

/-- The projective compactification is counted by its normalized torus and coordinate boundary. -/
theorem projectiveReciprocalLocus_card (m : ℕ) :
    (projectiveReciprocalLocus (F := F) (m + 1)).card =
      Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := Fin (m + 1))) +
        (normalizedDoubleZeroTorus (F := F) m).card := by
  have hq : Fintype.card F - 1 ≠ 0 := by
    have h := Fintype.one_lt_card (α := F)
    omega
  apply mul_right_cancel₀ hq
  calc (projectiveReciprocalLocus (F := F) (m + 1)).card * (Fintype.card F - 1) =
      (reciprocalCone (F := F) (m + 1)).card := (reciprocalCone_card_orbits _).symm
    _ = (coordinateBoundaryCone (F := F) (ι := Fin (m + 1))).card +
        (doubleZeroTorus (F := F) (m + 1)).card := by
      rw [reciprocalCone_card_split, reciprocalBoundaryCone_card, reciprocalTorusCone_card]
    _ = _ := by
      rw [coordinateBoundaryCone, boundedSupportZeroSum_card_orbits, doubleZeroTorus_card]
      ring

/-- The Kloosterman moment is the compactified count with its explicit boundary removed. -/
theorem kloosterman_moment_compactified {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ∑ a : F, SignedSuccessorArithmetic.kloosterman ψ a b ^ (m + 1) =
      (Fintype.card F : ℂ) ^ 2 *
        (((projectiveReciprocalLocus (F := F) (m + 1)).card : ℂ) -
          Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := Fin (m + 1)))) -
        ((Fintype.card F : ℂ) - 1) ^ m + (-1) ^ m := by
  have hc : ((projectiveReciprocalLocus (F := F) (m + 1)).card : ℂ) =
      Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := Fin (m + 1))) +
        (normalizedDoubleZeroTorus (F := F) m).card := by
    exact_mod_cast projectiveReciprocalLocus_card (F := F) m
  rw [kloosterman_moment_double_count hψ hb, hc, add_sub_cancel_left]

/-- The boundary and hyperplane contributions form an explicit signed Tate trace. -/
def compactificationTateTrace (n : ℕ) (q : ℂ) (e : ℕ) : ℂ :=
  (q ^ 2) ^ e * boundaryTateTrace n q e + q ^ e * hyperplaneTateTrace (n - 1) q e

omit [DecidableEq F] in
/-- The correction trace recovers the two geometric correction counts over every finite extension. -/
theorem compactificationTateTrace_extension_count (n : ℕ) (E : Type*) [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] :
    compactificationTateTrace n (Fintype.card F : ℂ) (Module.finrank F E) =
      (Fintype.card E : ℂ) ^ 2 *
          Fintype.card (ProjectiveCoordinateBoundary (F := E) (ι := Fin n)) +
        (Fintype.card E : ℂ) * (normalizedCoordinateZeroTorus (F := E) (n - 1)).card := by
  have hb := boundaryTateTrace_extension_count (F := F) (ι := Fin n) E
  simp only [Fintype.card_fin] at hb
  have hh := hyperplaneTateTrace_extension_count (F := F) (n - 1) E
  have hq : (Fintype.card F : ℂ) ^ Module.finrank F E = (Fintype.card E : ℂ) := by
    rw [← Nat.cast_pow, ← Module.card_eq_pow_finrank (K := F) (V := E)]
  have hp : ((Fintype.card F : ℂ) ^ 2) ^ Module.finrank F E =
      ((Fintype.card F : ℂ) ^ Module.finrank F E) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2]
  rw [compactificationTateTrace, hb, hh, hp, hq]

/-- The exact compactified point-count trace, with all Tate corrections displayed. -/
theorem kloosterman_moment_projective_trace {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ∑ a : F, SignedSuccessorArithmetic.kloosterman ψ a b ^ (m + 1) =
      (Fintype.card F : ℂ) ^ 2 * (projectiveReciprocalLocus (F := F) (m + 1)).card -
        ((Fintype.card F : ℂ) ^ 2 *
            Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := Fin (m + 1))) +
          (Fintype.card F : ℂ) * (normalizedCoordinateZeroTorus (F := F) m).card) := by
  have hc : ((projectiveReciprocalLocus (F := F) (m + 1)).card : ℂ) =
      Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := Fin (m + 1))) +
        (normalizedDoubleZeroTorus (F := F) m).card := by
    exact_mod_cast projectiveReciprocalLocus_card (F := F) m
  rw [kloosterman_moment_projective_counts hψ hb, hc]
  ring

omit [DecidableEq F] in
/-- Over every finite extension, the global moment is the compactified trace minus explicit Tate terms. -/
theorem kloosterman_moment_compactified_extension (E : Type*) [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] {ψ : AddChar E ℂ} (hψ : ψ.IsPrimitive)
    {b : E} (hb : b ≠ 0) (m : ℕ) :
    ∑ a : E, SignedSuccessorArithmetic.kloosterman ψ a b ^ (m + 1) =
      (Fintype.card E : ℂ) ^ 2 * (projectiveReciprocalLocus (F := E) (m + 1)).card -
        compactificationTateTrace (m + 1) (Fintype.card F : ℂ) (Module.finrank F E) := by
  rw [compactificationTateTrace_extension_count]
  exact kloosterman_moment_projective_trace hψ hb m

/-- Even-degree positivity gives an unconditional incidence inequality on the compactification. -/
theorem projectiveReciprocalLocus_even_incidence (k : ℕ) :
    Fintype.card F * Fintype.card (ProjectiveCoordinateBoundary (F := F) (ι := Fin (2 * k + 2))) +
        (normalizedCoordinateZeroTorus (F := F) (2 * k + 1)).card ≤
      Fintype.card F * (projectiveReciprocalLocus (F := F) (2 * k + 2)).card := by
  rw [projectiveReciprocalLocus_card (2 * k + 1), mul_add]
  exact Nat.add_le_add_left (normalized_even_incidence (F := F) k) _

omit [DecidableEq F] in
/-- The corrected even-degree compactified trace is nonnegative over every finite extension,
without a character or purity premise. -/
theorem compactified_even_trace_nonneg (k : ℕ) (E : Type*) [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] :
    0 ≤ ((Fintype.card E : ℂ) ^ 2 * (projectiveReciprocalLocus (F := E) (2 * k + 2)).card -
      compactificationTateTrace (2 * k + 2) (Fintype.card F : ℂ) (Module.finrank F E)).re := by
  rw [compactificationTateTrace_extension_count]
  have hr : (Fintype.card E : ℝ) *
        Fintype.card (ProjectiveCoordinateBoundary (F := E) (ι := Fin (2 * k + 2))) +
          (normalizedCoordinateZeroTorus (F := E) (2 * k + 1)).card ≤
      (Fintype.card E : ℝ) * (projectiveReciprocalLocus (F := E) (2 * k + 2)).card := by
    exact_mod_cast projectiveReciprocalLocus_even_incidence (F := E) k
  have hscale := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (Fintype.card E) : (0 : ℝ) ≤ _)
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero, add_zero]
  change 0 ≤ (Fintype.card E : ℝ) * Fintype.card E *
    (projectiveReciprocalLocus (F := E) (2 * k + 2)).card -
      ((Fintype.card E : ℝ) * Fintype.card E *
        Fintype.card (ProjectiveCoordinateBoundary (F := E) (ι := Fin (2 * k + 2))) +
          (Fintype.card E : ℝ) * (normalizedCoordinateZeroTorus (F := E) (2 * k + 1)).card)
  nlinarith only [hscale]

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
