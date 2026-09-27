import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpVectorLattice

/-!
# Descending chains above a lattice stabilize

The quotient of a finite-dimensional completed skew vector space by an integral lattice is an
Artinian module over the valuation ring.  This leaf proves it in the form the slope theory uses: a
descending chain of integral submodules squeezed between a lattice of a subspace and the subspace
itself is eventually constant.

* `DiffOp.integerSubmodule` — the valuation ring as a submodule of `𝔻`.
* `DiffOp.mem_of_completedPseudoDiffOpAddValue_le` — an integral submodule of `𝔻` containing a
  nonzero element contains everything of larger valuation, because the quotient of the two is
  integral.
* `DiffOp.isArtinian_quotient_integerSubmodule` — `𝔻/𝒪` is Artinian.  The depth
  `sup {n | ϖ^{-n} ∈ X}` is strictly monotone on submodules containing `𝒪`: an element of the
  larger submodule outside the smaller one has valuation `-m < 0`, so `ϖ^{-m}` lies in the larger
  one and no `ϖ^{-n}` with `n ≥ m` lies in the smaller one.
* `DiffOp.exists_stabilizes_of_pi_le` — chains above the integral product lattice in a coordinate
  space stabilize, through the noncommutative identification of `(ι → 𝔻)/𝒪^ι` with `ι → 𝔻/𝒪`.
* `DiffOp.exists_stabilizes_of_lattice_le` — the general statement for a lattice of a subspace,
  transported along coordinates, which are injective on the subspace, and along a uniformizer
  dilation that moves the coordinate lattice below the given one.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

/-- The valuation ring as a submodule of the completed skew field. -/
def integerSubmodule :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) (CompletedPseudoDiffOp K) where
  carrier := CompletedPseudoDiffOpInteger (K := K)
  add_mem' := fun hx hy => add_mem hx hy
  zero_mem' := zero_mem _
  smul_mem' a _ hx := mul_mem a.2 hx

theorem mem_integerSubmodule {x : CompletedPseudoDiffOp K} :
    x ∈ integerSubmodule (K := K) ↔ x ∈ CompletedPseudoDiffOpInteger (K := K) := Iff.rfl

/-- An integral submodule of the completed skew field is closed upward in valuation. -/
theorem mem_of_completedPseudoDiffOpAddValue_le
    {X : Submodule (CompletedPseudoDiffOpInteger (K := K)) (CompletedPseudoDiffOp K)}
    {x y : CompletedPseudoDiffOp K} (hx : x ∈ X)
    (hxy : completedPseudoDiffOpAddValue x ≤ completedPseudoDiffOpAddValue y) : y ∈ X := by
  by_cases hx0 : x = 0
  · subst x
    rw [completedPseudoDiffOpAddValue_zero, top_le_iff] at hxy
    have hy0 : y = 0 := by
      by_contra hy0
      exact completedPseudoDiffOpAddValue_ne_top_of_ne_zero hy0 hxy
    rw [hy0]
    exact X.zero_mem
  · have hint : y * x⁻¹ ∈ CompletedPseudoDiffOpInteger (K := K) := by
      rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg, completedPseudoDiffOpAddValue_mul,
        completedPseudoDiffOpAddValue_inv]
      have hfin := completedPseudoDiffOpAddValue_ne_top_of_ne_zero hx0
      set m := (completedPseudoDiffOpAddValue x).untop hfin
      have hm : completedPseudoDiffOpAddValue x = (m : WithTop ℤ) :=
        (WithTop.coe_untop _ hfin).symm
      rw [hm] at hxy ⊢
      generalize completedPseudoDiffOpAddValue y = t at hxy ⊢
      induction t using WithTop.recTopCoe with
      | top => exact le_top
      | coe n =>
          have hmn : m ≤ n := by exact_mod_cast hxy
          rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
          exact_mod_cast (show (0 : ℤ) ≤ n + -m by omega)
    have hmem := X.smul_mem ⟨y * x⁻¹, hint⟩ hx
    rw [integer_smul_eq] at hmem
    change y * x⁻¹ * x ∈ X at hmem
    rwa [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at hmem

/-- The depth of an integral submodule of the completed skew field. -/
def integerDepth (X : Submodule (CompletedPseudoDiffOpInteger (K := K)) (CompletedPseudoDiffOp K)) :
    ℕ∞ :=
  ⨆ n ∈ {n : ℕ | uniformizerZPow (K := K) (-(n : ℤ)) ∈ X}, (n : ℕ∞)

/-- Depth is strictly monotone on integral submodules containing the valuation ring. -/
theorem integerDepth_lt_integerDepth
    {X Y : Submodule (CompletedPseudoDiffOpInteger (K := K)) (CompletedPseudoDiffOp K)}
    (hX : integerSubmodule ≤ X) (hXY : X < Y) : integerDepth X < integerDepth Y := by
  obtain ⟨y, hyY, hyX⟩ := SetLike.exists_of_lt hXY
  have hy0 : y ≠ 0 := fun h => hyX (h ▸ X.zero_mem)
  have hfin := completedPseudoDiffOpAddValue_ne_top_of_ne_zero hy0
  set v := (completedPseudoDiffOpAddValue y).untop hfin
  have hv : completedPseudoDiffOpAddValue y = (v : WithTop ℤ) := (WithTop.coe_untop _ hfin).symm
  have hvneg : v < 0 := by
    by_contra hnn
    push Not at hnn
    apply hyX
    apply hX
    rw [mem_integerSubmodule, mem_completedPseudoDiffOpInteger_iff_addValue_nonneg, hv]
    exact_mod_cast hnn
  set m : ℕ := (-v).toNat
  have hmv : ((m : ℕ) : ℤ) = -v := by omega
  have hpowY : uniformizerZPow (K := K) (-(m : ℤ)) ∈ Y := by
    refine mem_of_completedPseudoDiffOpAddValue_le hyY ?_
    rw [completedPseudoDiffOpAddValue_uniformizerZPow, hv, hmv, neg_neg]
  have hnotX : ∀ n : ℕ, uniformizerZPow (K := K) (-(n : ℤ)) ∈ X → n < m := by
    intro n hn
    by_contra hge
    push Not at hge
    apply hyX
    refine mem_of_completedPseudoDiffOpAddValue_le hn ?_
    rw [completedPseudoDiffOpAddValue_uniformizerZPow, hv]
    exact_mod_cast (show -(n : ℤ) ≤ v by omega)
  have hXle : integerDepth X ≤ ((m - 1 : ℕ) : ℕ∞) := by
    refine iSup₂_le fun n hn => ?_
    have := hnotX n hn
    exact_mod_cast (show n ≤ m - 1 by omega)
  have hYge : ((m : ℕ) : ℕ∞) ≤ integerDepth Y :=
    le_iSup₂ (f := fun n (_ : n ∈ {n : ℕ | uniformizerZPow (K := K) (-(n : ℤ)) ∈ Y}) =>
      (n : ℕ∞)) m hpowY
  have hm1 : 1 ≤ m := by omega
  refine lt_of_le_of_lt hXle (lt_of_lt_of_le ?_ hYge)
  exact_mod_cast (show m - 1 < m by omega)

/-- `𝔻/𝒪` is an Artinian module over the valuation ring. -/
theorem isArtinian_quotient_integerSubmodule :
    IsArtinian (CompletedPseudoDiffOpInteger (K := K))
      (CompletedPseudoDiffOp K ⧸ integerSubmodule (K := K)) := by
  rw [isArtinian_iff]
  refine Subrelation.wf (r := InvImage (· < ·)
    (fun X => integerDepth ((X.comap (integerSubmodule (K := K)).mkQ)))) ?_
    (InvImage.wf _ wellFounded_lt)
  intro X Y hXY
  refine integerDepth_lt_integerDepth ?_ ?_
  · intro x hx
    rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx]
    exact X.zero_mem
  · exact (Submodule.comapMkQRelIso (integerSubmodule (K := K))).strictMono hXY

instance isArtinian_quotient_integerSubmodule_inst :
    IsArtinian (CompletedPseudoDiffOpInteger (K := K))
      (CompletedPseudoDiffOp K ⧸ integerSubmodule (K := K)) :=
  isArtinian_quotient_integerSubmodule

/-- Descending chains of integral submodules above the integral product lattice stabilize. -/
theorem exists_stabilizes_of_pi_le {ι : Type*} [Finite ι]
    (Y : ℕ → Submodule (CompletedPseudoDiffOpInteger (K := K)) (ι → CompletedPseudoDiffOp K))
    (hY : Antitone Y)
    (hpi : ∀ n, Submodule.pi Set.univ (fun _ : ι => integerSubmodule (K := K)) ≤ Y n) :
    ∃ n₀, ∀ n, n₀ ≤ n → Y n = Y n₀ := by
  haveI : IsArtinian (CompletedPseudoDiffOpInteger (K := K))
      ((ι → CompletedPseudoDiffOp K) ⧸
        Submodule.pi Set.univ (fun _ : ι => integerSubmodule (K := K))) :=
    isArtinian_of_linearEquiv
      (noncommutativeQuotientPiLinearEquiv (fun _ : ι => integerSubmodule (K := K))).symm
  set p := Submodule.pi Set.univ (fun _ : ι => integerSubmodule (K := K))
  let f : ℕ →o (Submodule (CompletedPseudoDiffOpInteger (K := K))
      ((ι → CompletedPseudoDiffOp K) ⧸ p))ᵒᵈ :=
    ⟨fun n => OrderDual.toDual ((Y n).map p.mkQ), fun a b hab =>
      Submodule.map_mono (hY hab)⟩
  obtain ⟨n₀, hn₀⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨n₀, fun n hn => ?_⟩
  have h := congrArg (fun Z => Submodule.comap p.mkQ (OrderDual.ofDual Z)) (hn₀ n hn)
  simp only [f, OrderHom.coe_mk, OrderDual.ofDual_toDual, Submodule.comap_map_mkQ] at h
  rw [sup_eq_right.2 (hpi n₀), sup_eq_right.2 (hpi n)] at h
  exact h.symm

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]
  [FiniteDimensional (CompletedPseudoDiffOp K) E]

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- An integral combination of a coordinate family lies in its integral span. -/
theorem sum_smul_mem_span_of_integer {W : Submodule (CompletedPseudoDiffOp K) E} {d : ℕ}
    {e : Fin d → E} {c : E →ₗ[CompletedPseudoDiffOp K] (Fin d → CompletedPseudoDiffOp K)}
    (he : ∀ i, e i ∈ W) (hsum : ∀ x ∈ W, ∑ i, c x i • e i = x)
    (hδ : ∀ i j, c (e j) i = (Pi.single j 1 : Fin d → CompletedPseudoDiffOp K) i)
    (v : Fin d → CompletedPseudoDiffOp K) (hv : ∀ i, v i ∈ CompletedPseudoDiffOpInteger (K := K)) :
    ∑ i, v i • e i ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) := by
  have hmem : ∑ i, v i • e i ∈ uniformizerDilate (0 : ℤ)
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) := by
    rw [mem_uniformizerDilate_span_iff he hsum hδ]
    refine ⟨sum_mem_of_coordinates he v, fun i => ?_⟩
    rw [coordinate_sum_smul hδ]
    exact_mod_cast (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).1 (hv i)
  rwa [uniformizerDilate_zero] at hmem

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Chains above the integral span of a coordinate family stabilize. -/
theorem exists_stabilizes_of_coordinate_le {W : Submodule (CompletedPseudoDiffOp K) E} {d : ℕ}
    {e : Fin d → E} {c : E →ₗ[CompletedPseudoDiffOp K] (Fin d → CompletedPseudoDiffOp K)}
    (he : ∀ i, e i ∈ W) (hsum : ∀ x ∈ W, ∑ i, c x i • e i = x)
    (hδ : ∀ i j, c (e j) i = (Pi.single j 1 : Fin d → CompletedPseudoDiffOp K) i)
    (Y : ℕ → Submodule (CompletedPseudoDiffOpInteger (K := K)) E) (hY : Antitone Y)
    (hlow : ∀ n, Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) ≤ Y n)
    (hup : ∀ n, ∀ x ∈ Y n, x ∈ W) :
    ∃ n₀, ∀ n, n₀ ≤ n → Y n = Y n₀ := by
  let cO : E →ₗ[CompletedPseudoDiffOpInteger (K := K)] (Fin d → CompletedPseudoDiffOp K) :=
    c.restrictScalars (CompletedPseudoDiffOpInteger (K := K))
  have hZpi : ∀ n, Submodule.pi Set.univ (fun _ : Fin d => integerSubmodule (K := K)) ≤
      (Y n).map cO := by
    intro n v hv
    refine ⟨∑ i, v i • e i, hlow n (sum_smul_mem_span_of_integer he hsum hδ v
      fun i => hv i (Set.mem_univ i)), ?_⟩
    funext i
    exact coordinate_sum_smul hδ v i
  obtain ⟨n₀, hn₀⟩ := exists_stabilizes_of_pi_le (fun n => (Y n).map cO)
    (fun m n hmn => Submodule.map_mono (hY hmn)) hZpi
  have hdet : ∀ n, Y n = ((Y n).map cO).comap cO ⊓
      W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
    intro n
    apply le_antisymm
    · intro x hx
      exact ⟨Submodule.mem_map_of_mem hx, hup n x hx⟩
    · rintro x ⟨⟨y, hy, hxy⟩, hxW⟩
      have hcy : c y = c x := hxy
      have : x = y := by rw [← hsum x hxW, ← hsum y (hup n y hy), hcy]
      rw [this]
      exact hy
  exact ⟨n₀, fun n hn => by rw [hdet n, hdet n₀, hn₀ n hn]⟩

/-- **Descending chains above a lattice stabilize.**  A descending chain of integral submodules
lying between an integral submodule `Λ` and its skew span is eventually constant. -/
theorem exists_stabilizes_of_lattice_le
    {Λ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (Y : ℕ → Submodule (CompletedPseudoDiffOpInteger (K := K)) E) (hY : Antitone Y)
    (hlow : ∀ n, Λ ≤ Y n)
    (hup : ∀ n, (Y n : Set E) ⊆ Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E)) :
    ∃ n₀, ∀ n, n₀ ≤ n → Y n = Y n₀ := by
  classical
  obtain ⟨d, e, c, he, hsum, hδ⟩ :=
    exists_coordinates (Submodule.span (CompletedPseudoDiffOp K) (Λ : Set E))
  have hspan := span_span_range_eq he hsum
  have hΛefg : (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)).FG :=
    ⟨Finset.univ.image e, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  obtain ⟨a, ha⟩ := exists_nat_le_uniformizerDilate_of_fg
    (M := Λ) (N := Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) hΛefg
    (fun x hx => by
      have h : x ∈ Submodule.span (CompletedPseudoDiffOp K)
          ((Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) :
            Submodule (CompletedPseudoDiffOpInteger (K := K)) E) : Set E) :=
        Submodule.subset_span hx
      rw [hspan] at h
      exact h)
  obtain ⟨n₀, hn₀⟩ := exists_stabilizes_of_coordinate_le he hsum hδ
    (fun n => uniformizerDilate (-(a : ℤ)) (Y n))
    (fun m n hmn => uniformizerDilate_mono (hY hmn))
    (fun n => ha.trans (uniformizerDilate_mono (hlow n)))
    (fun n x hx => (Submodule.span_le.2 (hup n)) (uniformizerDilate_subset_span _ hx))
  have hback : ∀ m, Y m = uniformizerDilate (a : ℤ) (uniformizerDilate (-(a : ℤ)) (Y m)) := by
    intro m
    rw [uniformizerDilate_uniformizerDilate, add_neg_cancel, uniformizerDilate_zero]
  exact ⟨n₀, fun n hn => by rw [hback n, hback n₀, hn₀ n hn]⟩

end

end DiffOp

end GaloisForLFunctions.HTGeometry
