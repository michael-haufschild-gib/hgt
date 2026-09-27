import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpAdicCompleteness

/-!
# Integral submodules of a finite-dimensional completed skew vector space

The slope theory of a semilinear automorphism is run in an arbitrary finite-dimensional vector space
`E` over the completed pseudodifferential skew field `𝔻`, so that invariant subspaces and quotients
are again spaces of the same kind.  This leaf supplies the integral-submodule calculus there.

* `DiffOp.uniformizerDilate k M` — the dilation `ϖ^k M` of a valuation-ring submodule, defined as the
  preimage `{y | ϖ^{-k} y ∈ M}`.  Conjugation by uniformizer powers preserves the valuation ring, so
  this is again a submodule; dilations compose additively, are antitone in `k`, commute with sums,
  preserve finite generation and fix every subspace.
* `DiffOp.exists_nat_uniformizerZPow_smul_mem_of_mem_span` and
  `DiffOp.exists_nat_le_uniformizerDilate_of_fg` — **absorption**: a vector of the skew span of `M` is
  pushed into `M` by a uniformizer power, and a finitely generated submodule of that span by a single
  one.
* `DiffOp.exists_coordinates` — a subspace carries a finite family of vectors and skew-linear
  coordinate functionals reproducing each of its vectors.  Membership of a vector in a dilation of the
  integral span of the family is read off from the valuations of its coordinates
  (`DiffOp.mem_uniformizerDilate_span_iff`).
* `DiffOp.eq_zero_of_forall_mem_uniformizerDilate` — **separation**: a finitely generated integral
  submodule meets the intersection of its dilations only in zero.
* `DiffOp.exists_limit_of_eventually_sub_mem_uniformizerDilate` — **completeness**: a sequence whose
  successive differences eventually lie in every dilation of a finitely generated `M` has a limit in
  the same sense, coordinatewise from the adic completeness of `𝔻`; the limit is unique.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

/-- Left multiplication of the valuation ring on the completed skew field.  Registering this
instance locally lets instance search find the valuation-ring structure of skew vector spaces
directly. -/
abbrev completedPseudoDiffOpIntegerSMul :
    SMul (CompletedPseudoDiffOpInteger (K := K)) (CompletedPseudoDiffOp K) :=
  Submonoid.smul (CompletedPseudoDiffOpInteger (K := K)).toSubmonoid

attribute [local instance] completedPseudoDiffOpIntegerSMul

/-- Integer powers of the canonical uniformizer. -/
abbrev uniformizerZPow (k : ℤ) : CompletedPseudoDiffOp K :=
  ((completedPseudoDiffOpUniformizerUnit (K := K) ^ k : (CompletedPseudoDiffOp K)ˣ) :
    CompletedPseudoDiffOp K)

theorem uniformizerZPow_add (j k : ℤ) :
    uniformizerZPow (K := K) (j + k) = uniformizerZPow j * uniformizerZPow k := by
  rw [uniformizerZPow, zpow_add, Units.val_mul]

@[simp] theorem uniformizerZPow_zero : uniformizerZPow (K := K) 0 = 1 := by
  rw [uniformizerZPow, zpow_zero, Units.val_one]

theorem uniformizerZPow_mul_neg (k : ℤ) :
    uniformizerZPow (K := K) k * uniformizerZPow (-k) = 1 := by
  rw [← uniformizerZPow_add, add_neg_cancel, uniformizerZPow_zero]

theorem uniformizerZPow_neg_mul (k : ℤ) :
    uniformizerZPow (K := K) (-k) * uniformizerZPow k = 1 := by
  rw [← uniformizerZPow_add, neg_add_cancel, uniformizerZPow_zero]

theorem uniformizerZPow_ne_zero (k : ℤ) : uniformizerZPow (K := K) k ≠ 0 :=
  Units.ne_zero _

theorem completedPseudoDiffOpAddValue_uniformizerZPow (k : ℤ) :
    completedPseudoDiffOpAddValue (uniformizerZPow (K := K) k) = (k : WithTop ℤ) :=
  completedPseudoDiffOpAddValue_uniformizer_zpow k

theorem completedPseudoDiffOpAddValue_uniformizerZPow_mul (k : ℤ) (x : CompletedPseudoDiffOp K) :
    completedPseudoDiffOpAddValue (uniformizerZPow k * x) =
      (k : WithTop ℤ) + completedPseudoDiffOpAddValue x := by
  rw [completedPseudoDiffOpAddValue_mul, completedPseudoDiffOpAddValue_uniformizerZPow]

theorem uniformizerZPow_mem_integer {k : ℤ} (hk : 0 ≤ k) :
    uniformizerZPow (K := K) k ∈ CompletedPseudoDiffOpInteger (K := K) := by
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_uniformizerZPow]
  exact_mod_cast hk

theorem uniformizerZPow_conj_mem_integer (k : ℤ) {o : CompletedPseudoDiffOp K}
    (ho : o ∈ CompletedPseudoDiffOpInteger (K := K)) :
    uniformizerZPow k * o * uniformizerZPow (-k) ∈ CompletedPseudoDiffOpInteger (K := K) :=
  uniformizer_conj_mem_integer k ho

/-- An element lies in `ϖ^k 𝒪` exactly when its additive valuation is at least `k`. -/
theorem uniformizerZPow_neg_mul_mem_integer_iff (k : ℤ) (x : CompletedPseudoDiffOp K) :
    uniformizerZPow (-k) * x ∈ CompletedPseudoDiffOpInteger (K := K) ↔
      (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue x := by
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_uniformizerZPow_mul]
  induction completedPseudoDiffOpAddValue x using WithTop.recTopCoe with
  | top => simp
  | coe m =>
      rw [← WithTop.coe_add]
      constructor
      · intro h
        have h' : (0 : ℤ) ≤ -k + m := by exact_mod_cast h
        exact_mod_cast (show k ≤ m by omega)
      · intro h
        have h' : k ≤ m := by exact_mod_cast h
        exact_mod_cast (show (0 : ℤ) ≤ -k + m by omega)

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

theorem integer_smul_eq (a : CompletedPseudoDiffOpInteger (K := K)) (x : E) :
    a • x = (a : CompletedPseudoDiffOp K) • x := rfl

/-- The uniformizer dilation `ϖ^k M` of a valuation-ring submodule. -/
def uniformizerDilate (k : ℤ) (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    Submodule (CompletedPseudoDiffOpInteger (K := K)) E where
  carrier := {y | uniformizerZPow (K := K) (-k) • y ∈ M}
  add_mem' {x y} hx hy := by
    change uniformizerZPow (K := K) (-k) • (x + y) ∈ M
    rw [smul_add]
    exact M.add_mem hx hy
  zero_mem' := by
    change uniformizerZPow (K := K) (-k) • (0 : E) ∈ M
    rw [smul_zero]
    exact M.zero_mem
  smul_mem' a y hy := by
    change uniformizerZPow (K := K) (-k) • ((a : CompletedPseudoDiffOp K) • y) ∈ M
    have hconj := uniformizerZPow_conj_mem_integer (K := K) (-k) a.2
    rw [neg_neg] at hconj
    have heq : uniformizerZPow (K := K) (-k) • ((a : CompletedPseudoDiffOp K) • y) =
        (⟨uniformizerZPow (K := K) (-k) * a * uniformizerZPow (K := K) k, hconj⟩ :
          CompletedPseudoDiffOpInteger (K := K)) • (uniformizerZPow (K := K) (-k) • y) := by
      rw [integer_smul_eq, smul_smul, smul_smul]
      congr 1
      change uniformizerZPow (K := K) (-k) * a =
        uniformizerZPow (K := K) (-k) * a * uniformizerZPow (K := K) k * uniformizerZPow (K := K) (-k)
      rw [mul_assoc (uniformizerZPow (K := K) (-k) * _), uniformizerZPow_mul_neg, mul_one]
    rw [heq]
    exact M.smul_mem _ hy

variable {M N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}

theorem mem_uniformizerDilate {k : ℤ} {y : E} :
    y ∈ uniformizerDilate k M ↔ uniformizerZPow (K := K) (-k) • y ∈ M := Iff.rfl

theorem smul_mem_uniformizerDilate (k : ℤ) {x : E} (hx : x ∈ M) :
    uniformizerZPow (K := K) k • x ∈ uniformizerDilate k M := by
  rw [mem_uniformizerDilate, smul_smul, uniformizerZPow_neg_mul, one_smul]
  exact hx

theorem mem_uniformizerDilate_iff_exists {k : ℤ} {y : E} :
    y ∈ uniformizerDilate k M ↔ ∃ x ∈ M, uniformizerZPow (K := K) k • x = y := by
  refine ⟨fun hy => ⟨_, hy, ?_⟩, ?_⟩
  · rw [smul_smul, uniformizerZPow_mul_neg, one_smul]
  · rintro ⟨x, hx, rfl⟩
    exact smul_mem_uniformizerDilate k hx

@[simp] theorem uniformizerDilate_zero (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    uniformizerDilate 0 M = M := by
  ext y
  rw [mem_uniformizerDilate, neg_zero, uniformizerZPow_zero, one_smul]

theorem uniformizerDilate_uniformizerDilate (j k : ℤ)
    (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    uniformizerDilate j (uniformizerDilate k M) = uniformizerDilate (j + k) M := by
  ext y
  rw [mem_uniformizerDilate, mem_uniformizerDilate, mem_uniformizerDilate, smul_smul,
    ← uniformizerZPow_add, neg_add_rev]

theorem uniformizerDilate_mono {k : ℤ} (h : M ≤ N) : uniformizerDilate k M ≤ uniformizerDilate k N :=
  fun _ hy => h hy

theorem uniformizerDilate_antitone (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E)
    {j k : ℤ} (hjk : j ≤ k) : uniformizerDilate k M ≤ uniformizerDilate j M := by
  intro y hy
  rw [mem_uniformizerDilate] at hy ⊢
  have hint : uniformizerZPow (K := K) (k - j) ∈ CompletedPseudoDiffOpInteger (K := K) :=
    uniformizerZPow_mem_integer (by omega)
  have heq : uniformizerZPow (K := K) (-j) • y =
      (⟨uniformizerZPow (K := K) (k - j), hint⟩ : CompletedPseudoDiffOpInteger (K := K)) •
        (uniformizerZPow (K := K) (-k) • y) := by
    rw [integer_smul_eq, smul_smul]
    congr 1
    change uniformizerZPow (K := K) (-j) = uniformizerZPow (K := K) (k - j) * uniformizerZPow (K := K) (-k)
    rw [← uniformizerZPow_add]
    congr 1
    ring
  rw [heq]
  exact M.smul_mem _ hy

theorem uniformizerDilate_le_iff {k : ℤ} :
    uniformizerDilate k M ≤ N ↔ M ≤ uniformizerDilate (-k) N := by
  constructor
  · intro h x hx
    have := h (smul_mem_uniformizerDilate k hx)
    rwa [mem_uniformizerDilate, neg_neg]
  · intro h y hy
    have := h hy
    rw [mem_uniformizerDilate, neg_neg, smul_smul, uniformizerZPow_mul_neg, one_smul] at this
    exact this

theorem uniformizerDilate_sup (k : ℤ) (M N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    uniformizerDilate k (M ⊔ N) = uniformizerDilate k M ⊔ uniformizerDilate k N := by
  apply le_antisymm
  · intro y hy
    rw [mem_uniformizerDilate, Submodule.mem_sup] at hy
    obtain ⟨m, hm, n, hn, hmn⟩ := hy
    have hy' : y = uniformizerZPow (K := K) k • m + uniformizerZPow (K := K) k • n := by
      rw [← smul_add, hmn, smul_smul, uniformizerZPow_mul_neg, one_smul]
    rw [hy']
    exact Submodule.add_mem_sup (smul_mem_uniformizerDilate k hm) (smul_mem_uniformizerDilate k hn)
  · exact sup_le (uniformizerDilate_mono le_sup_left) (uniformizerDilate_mono le_sup_right)

/-- Dilation fixes every skew subspace. -/
theorem uniformizerDilate_restrictScalars (k : ℤ) (W : Submodule (CompletedPseudoDiffOp K) E) :
    uniformizerDilate k (W.restrictScalars (CompletedPseudoDiffOpInteger (K := K))) =
      W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
  ext y
  rw [mem_uniformizerDilate, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem]
  constructor
  · intro hy
    have := W.smul_mem (uniformizerZPow (K := K) k) hy
    rwa [smul_smul, uniformizerZPow_mul_neg, one_smul] at this
  · exact W.smul_mem _

/-- Dilation of an integral span is the integral span of the dilated generators. -/
theorem uniformizerDilate_span (k : ℤ) (S : Set E) :
    uniformizerDilate k (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) S) =
      Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        ((fun x => uniformizerZPow (K := K) k • x) '' S) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_uniformizerDilate_iff_exists.1 hy
    clear hy
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
    | smul a x _ hx =>
        have hconj := uniformizerZPow_conj_mem_integer (K := K) k a.2
        have heq : uniformizerZPow (K := K) k • (a • x) =
            (⟨uniformizerZPow (K := K) k * a * uniformizerZPow (K := K) (-k), hconj⟩ :
              CompletedPseudoDiffOpInteger (K := K)) • (uniformizerZPow (K := K) k • x) := by
          rw [integer_smul_eq, integer_smul_eq, smul_smul, smul_smul]
          congr 1
          change uniformizerZPow (K := K) k * a =
            uniformizerZPow (K := K) k * a * uniformizerZPow (K := K) (-k) * uniformizerZPow (K := K) k
          rw [mul_assoc (uniformizerZPow (K := K) k * _), uniformizerZPow_neg_mul, mul_one]
        rw [heq]
        exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_uniformizerDilate k (Submodule.subset_span hx)

theorem uniformizerDilate_fg (k : ℤ) (hM : M.FG) : (uniformizerDilate k M).FG := by
  classical
  obtain ⟨S, rfl⟩ := hM
  rw [uniformizerDilate_span, ← Finset.coe_image]
  exact ⟨_, rfl⟩

theorem uniformizerDilate_subset_span (k : ℤ) :
    (uniformizerDilate k M : Set E) ⊆ Submodule.span (CompletedPseudoDiffOp K) (M : Set E) := by
  intro y hy
  have hy' : uniformizerZPow (K := K) (-k) • y ∈ Submodule.span (CompletedPseudoDiffOp K) (M : Set E) :=
    Submodule.subset_span hy
  have := Submodule.smul_mem _ (uniformizerZPow (K := K) k) hy'
  rwa [smul_smul, uniformizerZPow_mul_neg, one_smul] at this

theorem span_uniformizerDilate (k : ℤ) :
    Submodule.span (CompletedPseudoDiffOp K) (uniformizerDilate k M : Set E) =
      Submodule.span (CompletedPseudoDiffOp K) (M : Set E) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact uniformizerDilate_subset_span k
  · rw [Submodule.span_le]
    intro x hx
    have hmem : uniformizerZPow (K := K) k • x ∈ Submodule.span (CompletedPseudoDiffOp K)
        (uniformizerDilate k M : Set E) :=
      Submodule.subset_span (smul_mem_uniformizerDilate k hx)
    have := Submodule.smul_mem _ (uniformizerZPow (K := K) (-k)) hmem
    rwa [smul_smul, uniformizerZPow_neg_mul, one_smul] at this

/-- **Absorption of a vector**, dilation form. -/
theorem exists_nat_mem_uniformizerDilate_of_mem_span {x : E}
    (hx : x ∈ Submodule.span (CompletedPseudoDiffOp K) (M : Set E)) :
    ∃ n : ℕ, x ∈ uniformizerDilate (-(n : ℤ)) M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [Nat.cast_zero, neg_zero, uniformizerDilate_zero]; exact hx⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨kx, hkx⟩ := ihx
      obtain ⟨ky, hky⟩ := ihy
      refine ⟨max kx ky, Submodule.add_mem _ ?_ ?_⟩
      · exact uniformizerDilate_antitone M (by omega) hkx
      · exact uniformizerDilate_antitone M (by omega) hky
  | smul a x _ ihx =>
      obtain ⟨k, hk⟩ := ihx
      obtain ⟨t, ht⟩ := exists_uniformizer_left_scale_mem_integer a
      have hint : (⟨uniformizerZPow (K := K) t * a, ht⟩ : CompletedPseudoDiffOpInteger (K := K)) • x ∈
          uniformizerDilate (-(k : ℤ)) M := Submodule.smul_mem _ _ hk
      have hscaled := smul_mem_uniformizerDilate (-t) hint
      rw [uniformizerDilate_uniformizerDilate, integer_smul_eq, smul_smul] at hscaled
      have heq : uniformizerZPow (K := K) (-t) * (uniformizerZPow (K := K) t * a) = a := by
        rw [← mul_assoc, uniformizerZPow_neg_mul, one_mul]
      change (uniformizerZPow (K := K) (-t) * (uniformizerZPow (K := K) t * a)) • x ∈ _ at hscaled
      rw [heq] at hscaled
      refine ⟨(t + k).toNat, uniformizerDilate_antitone M ?_ hscaled⟩
      omega

/-- **Absorption of a vector.**  A vector of the skew span of an integral submodule is pushed into
it by a nonnegative uniformizer power. -/
theorem exists_nat_uniformizerZPow_smul_mem_of_mem_span {x : E}
    (hx : x ∈ Submodule.span (CompletedPseudoDiffOp K) (M : Set E)) :
    ∃ n : ℕ, uniformizerZPow (K := K) (n : ℤ) • x ∈ M := by
  obtain ⟨n, hn⟩ := exists_nat_mem_uniformizerDilate_of_mem_span hx
  refine ⟨n, ?_⟩
  rwa [mem_uniformizerDilate, neg_neg] at hn

/-- **Absorption of a finitely generated submodule.**  A finitely generated integral submodule of
the skew span of `M` lies in a single dilation `ϖ^{-n} M`. -/
theorem exists_nat_le_uniformizerDilate_of_fg (hN : N.FG)
    (hspan : (N : Set E) ⊆ Submodule.span (CompletedPseudoDiffOp K) (M : Set E)) :
    ∃ n : ℕ, N ≤ uniformizerDilate (-(n : ℤ)) M := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hgen : ∀ x ∈ S, ∃ n : ℕ, x ∈ uniformizerDilate (-(n : ℤ)) M := fun x hx =>
    exists_nat_mem_uniformizerDilate_of_mem_span (hspan (Submodule.subset_span hx))
  choose f hf using hgen
  refine ⟨S.attach.sup (fun x => f x.1 x.2), ?_⟩
  rw [Submodule.span_le]
  intro x hx
  refine uniformizerDilate_antitone M ?_ (hf x hx)
  have : f x hx ≤ S.attach.sup (fun x => f x.1 x.2) :=
    Finset.le_sup (f := fun x : S => f x.1 x.2) (Finset.mem_attach S ⟨x, hx⟩)
  omega

theorem eventually_add_iff_eventually {P : ℕ → Prop} (n₀ : ℕ) :
    (∀ᶠ n in atTop, P (n₀ + n)) → ∀ᶠ m in atTop, P m := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨n₀ + N, fun m hm => ?_⟩
  have := hN (m - n₀) (by omega)
  rwa [show n₀ + (m - n₀) = m by omega] at this

section Coordinates

variable {W : Submodule (CompletedPseudoDiffOp K) E} {d : ℕ} {e : Fin d → E}
  {c : E →ₗ[CompletedPseudoDiffOp K] (Fin d → CompletedPseudoDiffOp K)}

theorem coordinate_sum_smul (hδ : ∀ i j, c (e j) i = (Pi.single j 1 : Fin d → CompletedPseudoDiffOp K) i)
    (a : Fin d → CompletedPseudoDiffOp K) (i : Fin d) : c (∑ j, a j • e j) i = a i := by
  classical
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [c.map_smul, Pi.smul_apply, hδ, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro j _ hji
    rw [c.map_smul, Pi.smul_apply, hδ, Pi.single_eq_of_ne hji.symm, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem sum_mem_of_coordinates (he : ∀ i, e i ∈ W) (a : Fin d → CompletedPseudoDiffOp K) :
    ∑ j, a j • e j ∈ W :=
  W.sum_mem fun j _ => W.smul_mem _ (he j)

/-- The skew span of the integral span of a coordinate family is its subspace. -/
theorem span_span_range_eq (he : ∀ i, e i ∈ W) (hsum : ∀ x ∈ W, ∑ i, c x i • e i = x) :
    Submodule.span (CompletedPseudoDiffOp K)
      ((Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) :
        Submodule (CompletedPseudoDiffOpInteger (K := K)) E) : Set E) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    have hle : Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) ≤
        W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact he i
    exact hle hx
  · intro x hx
    rw [← hsum x hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Submodule.subset_span ⟨i, rfl⟩

/-- Membership in a dilation of the integral span of a coordinate family is read off from the
valuations of the coordinates. -/
theorem mem_uniformizerDilate_span_iff (he : ∀ i, e i ∈ W) (hsum : ∀ x ∈ W, ∑ i, c x i • e i = x)
    (hδ : ∀ i j, c (e j) i = (Pi.single j 1 : Fin d → CompletedPseudoDiffOp K) i) (k : ℤ) (y : E) :
    y ∈ uniformizerDilate k (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) ↔
      y ∈ W ∧ ∀ i, (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (c y i) := by
  classical
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_uniformizerDilate_iff_exists.1 hy
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    have hrewrite : uniformizerZPow (K := K) k • ∑ i, g i • e i =
        ∑ i, (uniformizerZPow (K := K) k * g i) • e i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integer_smul_eq, smul_smul]
    rw [hrewrite]
    refine ⟨sum_mem_of_coordinates he _, fun i => ?_⟩
    rw [coordinate_sum_smul hδ, completedPseudoDiffOpAddValue_uniformizerZPow_mul]
    have hg := (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).1 (g i).2
    calc (k : WithTop ℤ) = (k : WithTop ℤ) + 0 := (add_zero _).symm
      _ ≤ (k : WithTop ℤ) + completedPseudoDiffOpAddValue (g i : CompletedPseudoDiffOp K) :=
        add_le_add le_rfl hg
  · rintro ⟨hyW, hy⟩
    rw [mem_uniformizerDilate, ← hsum y hyW, Finset.smul_sum]
    have hint : ∀ i, uniformizerZPow (K := K) (-k) * c y i ∈ CompletedPseudoDiffOpInteger (K := K) :=
      fun i => (uniformizerZPow_neg_mul_mem_integer_iff k _).2 (hy i)
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨_, hint i⟩, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integer_smul_eq, smul_smul]

end Coordinates

variable [FiniteDimensional (CompletedPseudoDiffOp K) E]

/-- Every subspace carries a finite family of its vectors together with skew-linear coordinate
functionals on the ambient space that reproduce each vector of the subspace. -/
theorem exists_coordinates (W : Submodule (CompletedPseudoDiffOp K) E) :
    ∃ (d : ℕ) (e : Fin d → E)
      (c : E →ₗ[CompletedPseudoDiffOp K] (Fin d → CompletedPseudoDiffOp K)),
      (∀ i, e i ∈ W) ∧ (∀ x ∈ W, ∑ i, c x i • e i = x) ∧
        (∀ i j, c (e j) i = (Pi.single j 1 : Fin d → CompletedPseudoDiffOp K) i) := by
  classical
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  let b := Module.finBasis (CompletedPseudoDiffOp K) W
  let p := Submodule.projectionOnto W W' hW'
  refine ⟨Module.finrank (CompletedPseudoDiffOp K) W, fun i => (b i : E),
    b.equivFun.toLinearMap ∘ₗ p, fun i => (b i).2, ?_, ?_⟩
  · intro x hx
    have hp : p x = ⟨x, hx⟩ := Submodule.projectionOnto_apply_left hW' ⟨x, hx⟩
    have hsum := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hp]
    rw [Submodule.coe_sum] at hsum
    simpa only [Submodule.coe_smul] using hsum
  · intro i j
    have hp : p (b j : E) = b j := Submodule.projectionOnto_apply_left hW' (b j)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hp, Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]


/-- **Separation.**  A vector lying in every dilation `ϖ^k M` of a finitely generated integral
submodule is zero. -/
theorem eq_zero_of_forall_mem_uniformizerDilate (hM : M.FG) {x : E}
    (hx : ∀ k : ℕ, x ∈ uniformizerDilate k M) : x = 0 := by
  classical
  obtain ⟨d, e, c, he, hsum, hδ⟩ :=
    exists_coordinates (Submodule.span (CompletedPseudoDiffOp K) (M : Set E))
  have hspan := span_span_range_eq he hsum
  obtain ⟨a, ha⟩ := exists_nat_le_uniformizerDilate_of_fg
    (M := Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) (N := M) hM
    (by rw [hspan]; exact Submodule.subset_span)
  have hmem : ∀ k : ℕ, x ∈ Submodule.span (CompletedPseudoDiffOp K) (M : Set E) ∧
      ∀ i, (((k : ℤ) - a : ℤ) : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (c x i) := by
    intro k
    have h1 := uniformizerDilate_mono (k := (k : ℤ)) ha (hx k)
    rw [uniformizerDilate_uniformizerDilate] at h1
    rw [← mem_uniformizerDilate_span_iff he hsum hδ]
    convert h1 using 2
    ring
  have hzero : ∀ i, c x i = 0 := by
    intro i
    by_contra hne
    have hfin := completedPseudoDiffOpAddValue_ne_top_of_ne_zero hne
    set m := (completedPseudoDiffOpAddValue (c x i)).untop hfin
    have hm : completedPseudoDiffOpAddValue (c x i) = (m : WithTop ℤ) :=
      (WithTop.coe_untop _ hfin).symm
    have := (hmem (m + a + 1).toNat).2 i
    rw [hm, WithTop.coe_le_coe] at this
    omega
  rw [← hsum x (hmem 0).1]
  simp [hzero]

/-- **Uniqueness of limits.** -/
theorem eq_of_eventually_sub_mem_uniformizerDilate (hM : M.FG) {s : ℕ → E} {y y' : E}
    (hy : ∀ k : ℕ, ∀ᶠ n in atTop, y - s n ∈ uniformizerDilate k M)
    (hy' : ∀ k : ℕ, ∀ᶠ n in atTop, y' - s n ∈ uniformizerDilate k M) : y = y' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_uniformizerDilate hM fun k => ?_
  obtain ⟨n, hn, hn'⟩ := ((hy k).and (hy' k)).exists
  have := Submodule.sub_mem _ hn hn'
  rwa [sub_sub_sub_cancel_right] at this

/-- **Completeness.**  A sequence whose successive differences eventually lie in every dilation of
a finitely generated integral submodule `M` converges in the same sense. -/
theorem exists_limit_of_eventually_sub_mem_uniformizerDilate (hM : M.FG) (s : ℕ → E)
    (hs : ∀ k : ℕ, ∀ᶠ n in atTop, s (n + 1) - s n ∈ uniformizerDilate k M) :
    ∃ y, ∀ k : ℕ, ∀ᶠ n in atTop, y - s n ∈ uniformizerDilate k M := by
  classical
  obtain ⟨d, e, c, he, hsum, hδ⟩ :=
    exists_coordinates (Submodule.span (CompletedPseudoDiffOp K) (M : Set E))
  have hspan := span_span_range_eq he hsum
  have hΛfg : (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)).FG :=
    ⟨Finset.univ.image e, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  obtain ⟨a, ha⟩ := exists_nat_le_uniformizerDilate_of_fg
    (M := Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) (N := M) hM
    (by rw [hspan]; exact Submodule.subset_span)
  obtain ⟨b, hb⟩ := exists_nat_le_uniformizerDilate_of_fg
    (M := M) (N := Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) hΛfg
    (by rw [← hspan]; exact Submodule.subset_span)
  have hdilM : ∀ k : ℤ, uniformizerDilate k M ≤ uniformizerDilate (k - a)
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) := by
    intro k
    refine (uniformizerDilate_mono ha).trans ?_
    rw [uniformizerDilate_uniformizerDilate, sub_eq_add_neg]
  have hdilΛ : ∀ k : ℤ, uniformizerDilate k
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) ≤
        uniformizerDilate (k - b) M := by
    intro k
    refine (uniformizerDilate_mono hb).trans ?_
    rw [uniformizerDilate_uniformizerDilate, sub_eq_add_neg]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hs 0)
  have hsubW : ∀ x ∈ uniformizerDilate (0 : ℤ) M,
      x ∈ Submodule.span (CompletedPseudoDiffOp K) (M : Set E) := by
    intro x hx
    rw [uniformizerDilate_zero] at hx
    exact Submodule.subset_span hx
  have hW : ∀ n, s (n₀ + n) - s n₀ ∈ Submodule.span (CompletedPseudoDiffOp K) (M : Set E) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep := hsubW _ (hn₀ (n₀ + n) (by omega))
        have := Submodule.add_mem _ hstep ih
        rwa [show s (n₀ + n + 1) - s (n₀ + n) + (s (n₀ + n) - s n₀) = s (n₀ + (n + 1)) - s n₀ by
          rw [← add_assoc]; abel] at this
  have hcoord : ∀ i, ∃ yi : CompletedPseudoDiffOp K, ∀ k : ℤ, ∀ᶠ n in atTop,
      (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (yi - c (s (n₀ + n) - s n₀) i) := by
    intro i
    apply exists_limit_of_eventually_le_addValue_sub
    intro k
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hs (k + a).toNat)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hmem := hdilM _ (hN (n₀ + n) (by omega))
    rw [mem_uniformizerDilate_span_iff he hsum hδ] at hmem
    have hi := hmem.2 i
    have hdiff : c (s (n₀ + (n + 1)) - s n₀) i - c (s (n₀ + n) - s n₀) i =
        c (s (n₀ + n + 1) - s (n₀ + n)) i := by
      rw [← Pi.sub_apply, ← map_sub, show s (n₀ + (n + 1)) - s n₀ - (s (n₀ + n) - s n₀) =
        s (n₀ + n + 1) - s (n₀ + n) by rw [← add_assoc]; abel]
    rw [hdiff]
    refine le_trans ?_ hi
    exact_mod_cast (show k ≤ (((k + a).toNat : ℕ) : ℤ) - a by omega)
  choose yc hyc using hcoord
  refine ⟨s n₀ + ∑ i, yc i • e i, fun k => ?_⟩
  refine eventually_add_iff_eventually n₀ ?_
  have hall := eventually_all.2 fun i => hyc i ((k : ℤ) + b)
  filter_upwards [hall] with n hn
  have hdecomp : s n₀ + ∑ i, yc i • e i - s (n₀ + n) =
      ∑ i, (yc i - c (s (n₀ + n) - s n₀) i) • e i := by
    have hrep := hsum _ (hW n)
    simp only [sub_smul, Finset.sum_sub_distrib, hrep]
    abel
  rw [hdecomp]
  have hmem : ∑ i, (yc i - c (s (n₀ + n) - s n₀) i) • e i ∈ uniformizerDilate ((k : ℤ) + b)
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) := by
    rw [mem_uniformizerDilate_span_iff he hsum hδ]
    refine ⟨sum_mem_of_coordinates he _, fun i => ?_⟩
    rw [coordinate_sum_smul hδ]
    exact hn i
  have := hdilΛ _ hmem
  rwa [add_sub_cancel_right] at this

end

end DiffOp

end GaloisForLFunctions.HTGeometry
