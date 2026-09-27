import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpSlopeDecomposition

/-!
# Isoclinic lattices and slope-adapted frames

Each slope part `E_s` of a uniformizer-semilinear automorphism `T` is **isoclinic**: it carries a
lattice `N_s` fixed by the normalized power `ϖ^{num s} T^{den s}`
(`DiffOp.exists_isoclinic_lattice`).  Consequently, for every common multiple `D` of the
denominators, `T^{D n}` acts on `N_s` as the dilation by `ϖ^{-n D s}`
(`DiffOp.semilinearImage_pow_mul_isoclinic`): on the slope-`s` part, `D n` steps of `T` expand by
exactly `n D s` uniformizer steps.

On the coordinate space `𝔻^r`, integral bases of the isoclinic lattices assemble into one skew
basis `B` adapted to the slope decomposition (`DiffOp.exists_slope_adapted_basis`): the `j`-th basis
vector has slope `sl j`, the slopes are sorted, slope `t` occurs exactly `dim E_t` times, and
`T^{D n}` carries the coordinate lattice `{y | 0 ≤ v(B-coordinates of y)}` to the coordinate lattice
`{y | -n D sl j ≤ v(j-th B-coordinate of y)}`.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

section General

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]
  [FiniteDimensional (CompletedPseudoDiffOp K) E]

variable {T : E ≃ₗ[ℤ] E} (hT : IsUniformizerSemilinear (K := K) T)

/-- **Each slope part is isoclinic.** -/
theorem exists_isoclinic_lattice (s : ℚ) :
    ∃ N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, IsLatticeOf N (slopeSubspace T hT s) ∧
      semilinearImage (slopeAut (K := K) T s.num s.den)
        (isUniformizerSemilinear_slopeAut hT s.num s.den) N = N := by
  have hS := isUniformizerSemilinear_slopeAut hT s.num s.den
  obtain ⟨hSB, -, hSB', -⟩ := pieces_invariant_of_commute hS hS (Commute.refl _)
  obtain ⟨hSiB, -, hSiB', -⟩ := pieces_invariant_of_commute hS hS.inv (Commute.refl _).inv_left
  exact exists_stable_lattice_of_le_neutral hS
    (fun x hx => ⟨hSB x hx.1, hSB' x hx.2⟩) (fun x hx => ⟨hSiB x hx.1, hSiB' x hx.2⟩) le_rfl

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem semilinearImage_pow_of_fixed {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    {N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hN : semilinearImage S hS N = N)
    (k : ℕ) : semilinearImage (S ^ k) (hS.pow k) N = N := by
  induction k with
  | zero => exact semilinearImage_pow_zero (hS.pow 0)
  | succ k ih => rw [semilinearImage_pow_succ hS k _ (hS.pow k), ih, hN]

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- **`T^{D n}` acts on an isoclinic lattice as a dilation.** -/
theorem semilinearImage_pow_mul_isoclinic {s : ℚ} {D : ℕ} (hD : s.den ∣ D)
    {N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hN : semilinearImage (slopeAut (K := K) T s.num s.den)
      (isUniformizerSemilinear_slopeAut hT s.num s.den) N = N) (n : ℕ) :
    semilinearImage (T ^ (D * n)) (hT.pow (D * n)) N =
      uniformizerDilate (-((n : ℤ) * (s.num * ((D / s.den : ℕ) : ℤ)))) N := by
  have hS := isUniformizerSemilinear_slopeAut hT s.num s.den
  set k := D / s.den with hk
  have hkD : k * s.den = D := Nat.div_mul_cancel hD
  set a : ℤ := s.num * (k : ℤ) with ha
  -- one block: `ϖ^a T^D` fixes `N`
  have hblock : semilinearImage (uniformizerSMulAut (K := K) a * T ^ D)
      ((isUniformizerSemilinear_uniformizerSMulAut a).mul (hT.pow D)) N = N := by
    have h := semilinearImage_pow_of_fixed hS hN k
    have heq : slopeAut (K := K) T s.num s.den ^ k = uniformizerSMulAut (K := K) a * T ^ D := by
      rw [slopeAut_pow hT, slopeAut, ← hkD, ha]
      congr 2
      ring
    have hcongr : ∀ {S₁ S₂ : E ≃ₗ[ℤ] E} (h₁₂ : S₁ = S₂) (h₁ : IsUniformizerSemilinear (K := K) S₁)
        (h₂ : IsUniformizerSemilinear (K := K) S₂),
        semilinearImage S₁ h₁ N = semilinearImage S₂ h₂ N := by
      intro S₁ S₂ h₁₂ h₁ h₂
      subst h₁₂
      rfl
    rw [← hcongr heq (hS.pow k)]
    exact h
  have hstep : semilinearImage (T ^ D) (hT.pow D) N = uniformizerDilate (-a) N := by
    rw [semilinearImage_mul (hT := isUniformizerSemilinear_uniformizerSMulAut a) (hS := hT.pow D),
      semilinearImage_uniformizerSMulAut] at hblock
    have h := congrArg (uniformizerDilate (-a)) hblock
    rwa [uniformizerDilate_uniformizerDilate, neg_add_cancel, uniformizerDilate_zero] at h
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, neg_zero, uniformizerDilate_zero, Nat.mul_zero]
      exact semilinearImage_pow_zero (hT.pow 0)
  | succ n ih =>
      rw [semilinearImage_pow_congr hT (show D * (n + 1) = D + D * n by ring),
        semilinearImage_pow_add hT, ih, semilinearImage_uniformizerDilate, hstep,
        uniformizerDilate_uniformizerDilate]
      congr 1
      push_cast
      ring

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem semilinearImage_iSup {ι : Sort*} (M : ι → Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    semilinearImage T hT (⨆ i, M i) = ⨆ i, semilinearImage T hT (M i) := by
  refine le_antisymm (fun y hy => ?_) (iSup_le fun i => semilinearImage_mono (le_iSup M i))
  obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
  refine Submodule.iSup_induction M (motive := fun x => T x ∈ ⨆ i, semilinearImage T hT (M i)) hx
    (fun i x hx => Submodule.mem_iSup_of_mem i (apply_mem_semilinearImage hx)) ?_ ?_
  · rw [_root_.map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [_root_.map_add]
    exact Submodule.add_mem _ hx hy

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- The skew span of an integral span is the skew span of the generators. -/
theorem span_integerSpan (S : Set E) :
    Submodule.span (CompletedPseudoDiffOp K)
      ((Submodule.span (CompletedPseudoDiffOpInteger (K := K)) S :
        Submodule (CompletedPseudoDiffOpInteger (K := K)) E) : Set E) =
      Submodule.span (CompletedPseudoDiffOp K) S := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => ?_)
    (Submodule.span_mono Submodule.subset_span)
  refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span (CompletedPseudoDiffOp K) S)
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _)
    (fun _ _ _ _ hx hy => Submodule.add_mem _ hx hy) (fun a y _ hy => ?_) hx
  rw [integer_smul_eq]
  exact Submodule.smul_mem _ _ hy

theorem mul_uniformizerZPow_neg_mem_integer_iff (k : ℤ) (x : CompletedPseudoDiffOp K) :
    x * uniformizerZPow (-k) ∈ CompletedPseudoDiffOpInteger (K := K) ↔
      (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue x := by
  rw [← uniformizerZPow_neg_mul_mem_integer_iff, mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    mem_completedPseudoDiffOpInteger_iff_addValue_nonneg, completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_mul, add_comm]

section CoordinateLattice

variable {ι : Type*}

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- The integral lattice cut out by lower bounds on the valuations of the coordinates in a skew
basis. -/
def coordinateLattice (B : Module.Basis ι (CompletedPseudoDiffOp K) E) (β : ι → WithTop ℤ) :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) E where
  carrier := {y | ∀ j, β j ≤ completedPseudoDiffOpAddValue (B.repr y j)}
  add_mem' {x y} hx hy j := by
    change β j ≤ completedPseudoDiffOpAddValue (B.repr (x + y) j)
    rw [_root_.map_add, Finsupp.add_apply]
    exact le_completedPseudoDiffOpAddValue_add (hx j) (hy j)
  zero_mem' j := by
    change β j ≤ completedPseudoDiffOpAddValue (B.repr 0 j)
    rw [_root_.map_zero, Finsupp.zero_apply, completedPseudoDiffOpAddValue_zero]
    exact le_top
  smul_mem' a y hy j := by
    change β j ≤ completedPseudoDiffOpAddValue (B.repr ((a : CompletedPseudoDiffOp K) • y) j)
    rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, completedPseudoDiffOpAddValue_mul]
    have ha := (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).1 a.2
    calc β j ≤ completedPseudoDiffOpAddValue (B.repr y j) := hy j
      _ = 0 + completedPseudoDiffOpAddValue (B.repr y j) := (zero_add _).symm
      _ ≤ _ := add_le_add ha le_rfl

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem mem_coordinateLattice {B : Module.Basis ι (CompletedPseudoDiffOp K) E} {β : ι → WithTop ℤ}
    {y : E} :
    y ∈ coordinateLattice B β ↔ ∀ j, β j ≤ completedPseudoDiffOpAddValue (B.repr y j) :=
  Iff.rfl

end CoordinateLattice

end General

section Frame

variable {r : ℕ} {T : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[ℤ] (Fin r → CompletedPseudoDiffOp K)}
  (hT : IsUniformizerSemilinear (K := K) T)

/-- **Integral bases of isoclinic lattices.**  Every slope part has a skew basis whose integral span
is fixed by the normalized power `ϖ^{num s} T^{den s}`. -/
theorem exists_isoclinic_basis (s : ℚ) :
    ∃ (n : ℕ) (v : Fin n → (Fin r → CompletedPseudoDiffOp K)),
      LinearIndependent (CompletedPseudoDiffOp K) v ∧
      Submodule.span (CompletedPseudoDiffOp K) (Set.range v) = slopeSubspace T hT s ∧
      semilinearImage (slopeAut (K := K) T s.num s.den)
        (isUniformizerSemilinear_slopeAut hT s.num s.den)
        (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range v)) =
        Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range v) := by
  obtain ⟨N, ⟨hNfg, hNspan⟩, hNfix⟩ := exists_isoclinic_lattice hT s
  obtain ⟨n, v, -, hli, hvN⟩ := exists_completedPseudoDiffOp_basis_of_fg_submodule N hNfg
  refine ⟨n, v, linearIndependent_completedPseudoDiffOp_of_integer hli, ?_, ?_⟩
  · rw [← span_integerSpan, hvN]
    exact hNspan
  · rw [hvN]
    exact hNfix

/-- **Slope-adapted frame.**  The coordinate space has a skew basis `B` with sorted slopes `sl`,
slope `t` occurring exactly `dim E_t` times, and a common denominator `D` of the slopes, such that
`T^{D n}` carries the unit coordinate lattice of `B` onto the coordinate lattice with valuation
bounds `-n D sl j`. -/
theorem exists_slope_adapted_basis :
    ∃ (B : Module.Basis (Fin r) (CompletedPseudoDiffOp K) (Fin r → CompletedPseudoDiffOp K))
      (sl : Fin r → ℚ) (D : ℕ) (A : Fin r → ℤ),
      Monotone sl ∧ 0 < D ∧ (∀ j, (A j : ℚ) = D * sl j) ∧
      (∀ t : ℚ, (Finset.univ.filter fun j => sl j = t).card =
        Module.finrank (CompletedPseudoDiffOp K) (slopeSubspace T hT t)) ∧
      ∀ n : ℕ, semilinearImage (T ^ (D * n)) (hT.pow (D * n))
          (coordinateLattice B fun _ => ((0 : ℤ) : WithTop ℤ)) =
        coordinateLattice B fun j => ((-((n : ℤ) * A j) : ℤ) : WithTop ℤ) := by
  classical
  choose n v hli hspan hfix using fun s => exists_isoclinic_basis hT s
  let bs : ∀ s, Module.Basis (Fin (n s)) (CompletedPseudoDiffOp K) (slopeSubspace T hT s) :=
    fun s => (Module.Basis.span (hli s)).map (LinearEquiv.ofEq _ _ (hspan s))
  have hbs : ∀ s i, (bs s i : Fin r → CompletedPseudoDiffOp K) = v s i := fun s i => by
    simp only [bs, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
  have hint : DirectSum.IsInternal fun s => slopeSubspace T hT s :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_slopeSubspace hT)
      (iSup_slopeSubspace_eq_top hT)
  let V : (Σ s, Fin (n s)) → (Fin r → CompletedPseudoDiffOp K) := fun x => v x.1 x.2
  let Bc := hint.collectedBasis bs
  have hBc : ∀ x, Bc x = V x := fun x => by
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact hbs x.1 x.2
  haveI : Finite (Σ s, Fin (n s)) := Module.Finite.finite_basis Bc
  letI : Fintype (Σ s, Fin (n s)) := Fintype.ofFinite _
  have hcard : Fintype.card (Σ s, Fin (n s)) = r := by
    rw [← Module.finrank_eq_card_basis Bc, Module.finrank_fin_fun]
  let φ₀ := Fintype.equivFinOfCardEq hcard
  let f : Fin r → ℚ := fun j => (φ₀.symm j).1
  let ψ : Fin r ≃ (Σ s, Fin (n s)) := (Tuple.sort f).trans φ₀.symm
  let B := Bc.reindex ψ.symm
  have hB : ∀ j, B j = V (ψ j) := fun j => by
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hBc]
  let sl : Fin r → ℚ := fun j => (ψ j).1
  have hsl : Monotone sl := Tuple.monotone_sort f
  -- multiplicities
  have hfib : ∀ t, (Finset.univ.filter fun j => sl j = t).card = n t := by
    intro t
    rw [← Fintype.card_subtype, Fintype.card_congr ((ψ.subtypeEquiv (p := fun j => sl j = t)
      (q := fun x => x.1 = t) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype t)), Fintype.card_fin]
  -- common denominator
  let D : ℕ := ∏ j, (sl j).den
  have hD : 0 < D := Finset.prod_pos fun j _ => (sl j).den_pos
  have hdvd : ∀ j, (sl j).den ∣ D := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let a : ℚ → ℤ := fun s => s.num * ((D / s.den : ℕ) : ℤ)
  have hA : ∀ j, (a (sl j) : ℚ) = D * sl j := by
    intro j
    have h1 : ((D / (sl j).den : ℕ) : ℚ) * (sl j).den = D := by
      exact_mod_cast Nat.div_mul_cancel (hdvd j)
    have h2 : sl j * (sl j).den = (sl j).num := Rat.mul_den_eq_num (sl j)
    show (((sl j).num * ((D / (sl j).den : ℕ) : ℤ) : ℤ) : ℚ) = D * sl j
    rw [Int.cast_mul, Int.cast_natCast]
    linear_combination sl j * h1 - ((D / (sl j).den : ℕ) : ℚ) * h2
  -- the isoclinic lattices and their dynamics
  let N : ℚ → Submodule (CompletedPseudoDiffOpInteger (K := K)) (Fin r → CompletedPseudoDiffOp K) :=
    fun s => Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range (v s))
  have hdyn : ∀ (m : ℕ) (s : ℚ), semilinearImage (T ^ (D * m)) (hT.pow (D * m)) (N s) =
      uniformizerDilate (-((m : ℤ) * a s)) (N s) := by
    intro m s
    by_cases hs : n s = 0
    · have hN : N s = Submodule.span (CompletedPseudoDiffOpInteger (K := K)) ∅ := by
        simp only [N]
        congr 1
        rw [Set.range_eq_empty_iff]
        rw [hs]
        infer_instance
      rw [hN, semilinearImage_span, uniformizerDilate_span, Set.image_empty, Set.image_empty]
    · have hne : (Finset.univ.filter fun j => sl j = s).Nonempty := by
        rw [← Finset.card_pos, hfib]
        omega
      obtain ⟨j, hj⟩ := hne
      have hjs : sl j = s := (Finset.mem_filter.1 hj).2
      have := semilinearImage_pow_mul_isoclinic hT (hjs ▸ hdvd j) (hfix s) m
      exact this
  -- the coordinate lattices are the sums of dilated isoclinic lattices
  have hsup : ∀ k : ℚ → ℤ, ⨆ s, uniformizerDilate (k s) (N s) =
      coordinateLattice B fun j => ((k (sl j) : ℤ) : WithTop ℤ) := by
    intro k
    apply le_antisymm
    · refine iSup_le fun s => ?_
      rw [uniformizerDilate_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have hvB : v s i = B (ψ.symm ⟨s, i⟩) := by
        rw [hB, Equiv.apply_symm_apply]
      have hsj : sl (ψ.symm ⟨s, i⟩) = s := by
        simp only [sl, Equiv.apply_symm_apply]
      rw [SetLike.mem_coe, mem_coordinateLattice, hvB]
      intro j
      rw [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
      by_cases hj : ψ.symm ⟨s, i⟩ = j
      · subst hj
        rw [Finsupp.single_eq_same, mul_one, completedPseudoDiffOpAddValue_uniformizerZPow, hsj]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hj), mul_zero, completedPseudoDiffOpAddValue_zero]
        exact le_top
    · intro y hy
      rw [mem_coordinateLattice] at hy
      rw [← B.sum_repr y]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hc := (mul_uniformizerZPow_neg_mem_integer_iff (k (sl j)) (B.repr y j)).2 (hy j)
      have hmem : uniformizerZPow (K := K) (k (sl j)) • B j ∈ uniformizerDilate (k (sl j)) (N (sl j)) := by
        refine smul_mem_uniformizerDilate _ ?_
        rw [hB]
        exact Submodule.subset_span ⟨(ψ j).2, rfl⟩
      have heq : (⟨_, hc⟩ : CompletedPseudoDiffOpInteger (K := K)) •
          (uniformizerZPow (K := K) (k (sl j)) • B j) = B.repr y j • B j := by
        rw [integer_smul_eq, smul_smul, mul_assoc, uniformizerZPow_neg_mul, mul_one]
      rw [← heq]
      exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem (sl j) hmem)
  refine ⟨B, sl, D, fun j => a (sl j), hsl, hD, hA, fun t => ?_, fun m => ?_⟩
  · rw [hfib, Module.finrank_eq_card_basis (bs t), Fintype.card_fin]
  · have h0 := hsup fun _ => 0
    have hm := hsup fun s => -((m : ℤ) * a s)
    simp only [uniformizerDilate_zero] at h0
    rw [← h0, ← hm, semilinearImage_iSup]
    exact iSup_congr fun s => hdyn m s

end Frame

end

end DiffOp

end GaloisForLFunctions.HTGeometry
