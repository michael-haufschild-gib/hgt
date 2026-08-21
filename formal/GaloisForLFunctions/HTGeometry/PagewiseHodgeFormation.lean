import GaloisForLFunctions.HTGeometry.PagewiseHodgeFlag
import GaloisForLFunctions.HTGeometry.OperatorAbsoluteValueBetween
import GaloisForLFunctions.HTGeometry.HilbertClosedRange

/-!
# Pagewise Hodge formation and stable-organ selection

The page differentials of a Hodge realization assemble into a positive formation operator whose
blocks are the absolute values of the page bijections and whose kernel is exactly the stable
survivor sector.  Its energy splits pagewise, it is bounded below on the complement of the stable
sector by the least page gap, and adjoining a terminal response on the stable sector produces an
operator whose kernel is the terminal kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

open ContinuousLinearMap

noncomputable section

variable {K C : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]

/-! ## Auxiliary Hilbert facts -/

theorem starProjection_eq_zero_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℂ E) [S.HasOrthogonalProjection] (x : E) :
    S.starProjection x = 0 ↔ x ∈ Sᗮ := by
  constructor
  · intro h
    have := S.sub_starProjection_mem_orthogonal (v := x)
    rwa [h, sub_zero] at this
  · intro h
    refine S.eq_starProjection_of_mem_of_inner_eq_zero S.zero_mem ?_
    intro w hw
    rw [sub_zero]
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal S x).mp h w hw)

theorem range_le_ker_orthogonal_of_isSelfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {S : E →L[ℂ] E} (hS : IsSelfAdjoint S) :
    LinearMap.range (S : E →ₗ[ℂ] E) ≤ (LinearMap.ker (S : E →ₗ[ℂ] E))ᗮ := by
  rintro y ⟨x, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro v hv
  have hSA : adjoint S = S := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hS
  have hadj : ⟪v, S x⟫_ℂ = ⟪S v, x⟫_ℂ := by
    conv_lhs => rw [← hSA]
    exact adjoint_inner_right S v x
  show ⟪v, S x⟫_ℂ = 0
  rw [hadj]
  have hv0 : S v = 0 := hv
  rw [hv0, inner_zero_left]

/-- Pythagoras for a finite pairwise orthogonal family. -/
theorem norm_sq_sum_pairwise_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (m : ℕ) (g : ℕ → E)
    (h : ∀ r s, r < m → s < m → r ≠ s → ⟪g r, g s⟫_ℂ = 0) :
    ‖∑ r ∈ Finset.range m, g r‖ * ‖∑ r ∈ Finset.range m, g r‖
      = ∑ r ∈ Finset.range m, ‖g r‖ * ‖g r‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcross : ⟪∑ r ∈ Finset.range m, g r, g m⟫_ℂ = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hrm : r < m := Finset.mem_range.mp hr
      exact h r m (by omega) (by omega) (Nat.ne_of_lt hrm)
    rw [Finset.sum_range_succ,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hcross,
      ih (fun r s hr hs hrs => h r s (by omega) (by omega) hrs), Finset.sum_range_succ]

/-! ## The stable sector as a common orthogonal complement -/

omit [CompleteSpace C] in
/-- **The kernel survivor is exactly what is orthogonal to every earlier positive death layer.** -/
theorem mem_kerFlag_iff (d : ℕ → (K →L[ℂ] C)) (m : ℕ) (k : K) :
    k ∈ kerFlag d m ↔ ∀ r, r < m → k ∈ (deathPos d r)ᗮ := by
  induction m with
  | zero => exact ⟨fun _ r hr => absurd hr (Nat.not_lt_zero r), fun _ => trivial⟩
  | succ m ih =>
    constructor
    · intro hk r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · exact ih.mp (kerFlag_antitone d m hk) r hlt
      · subst heq
        rw [Submodule.mem_orthogonal]
        intro v hv
        exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ v).mp hv.2 k hk)
    · intro hall
      have hkm : k ∈ kerFlag d m := ih.mpr fun r hr => hall r (by omega)
      refine ⟨hkm, ?_⟩
      have hks : k ∈ deathPos d m ⊔ kerFlag d (m + 1) := by
        rw [deathPos_sup_kerFlag d m]
        exact hkm
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hks
      have hab' : ⟪a, b⟫_ℂ = 0 :=
        inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ a).mp ha.2 b hb)
      have hak : ⟪a, k⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ k).mp (hall m (by omega)) a ha
      have haa : ⟪a, a⟫_ℂ = 0 := by
        rw [← hab] at hak
        rw [inner_add_right, hab', add_zero] at hak
        exact hak
      have ha0 : a = 0 := inner_self_eq_zero.mp haa
      have hkb : k = b := by rw [← hab, ha0, zero_add]
      show k ∈ LinearMap.ker ((d m : K →ₗ[ℂ] C))
      rw [LinearMap.mem_ker, hkb]
      exact hb.2

omit [CompleteSpace K] [CompleteSpace C] in
/-- **The cokernel survivor is exactly what is orthogonal to every earlier negative death
layer.** -/
theorem mem_cokerFlag_iff (d : ℕ → (K →L[ℂ] C)) (m : ℕ) (c : C) :
    c ∈ cokerFlag d m ↔ ∀ r, r < m → c ∈ (deathImage d r)ᗮ := by
  induction m with
  | zero => exact ⟨fun _ r hr => absurd hr (Nat.not_lt_zero r), fun _ => trivial⟩
  | succ m ih =>
    constructor
    · intro hc r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · exact ih.mp (cokerFlag_antitone d m hc) r hlt
      · subst heq
        exact hc.2
    · intro hall
      exact ⟨ih.mpr fun r hr => hall r (by omega), hall m (by omega)⟩

/-! ## The page responses -/

/-- The page differential compressed to its positive death layer. -/
def pageCompression (d : ℕ → (K →L[ℂ] C)) (r : ℕ) : K →L[ℂ] C :=
  (d r).comp (deathPos d r).starProjection

omit [CompleteSpace C] in
@[simp] theorem pageCompression_apply (d : ℕ → (K →L[ℂ] C)) (r : ℕ) (k : K) :
    pageCompression d r k = d r ((deathPos d r).starProjection k) := rfl

omit [CompleteSpace C] in
theorem ker_pageCompression (d : ℕ → (K →L[ℂ] C)) (r : ℕ) :
    LinearMap.ker (pageCompression d r : K →ₗ[ℂ] C) = (deathPos d r)ᗮ := by
  ext k
  constructor
  · intro hk
    have h0 : d r ((deathPos d r).starProjection k) = 0 := hk
    have hp : (deathPos d r).starProjection k = 0 :=
      eq_zero_of_mem_deathPos_of_apply_eq_zero d
        ((deathPos d r).starProjection_apply_mem k) h0
    exact (starProjection_eq_zero_iff (deathPos d r) k).mp hp
  · intro hk
    show d r ((deathPos d r).starProjection k) = 0
    rw [(starProjection_eq_zero_iff (deathPos d r) k).mpr hk, map_zero]

omit [CompleteSpace C] in
theorem range_pageCompression (d : ℕ → (K →L[ℂ] C)) (r : ℕ) :
    LinearMap.range (pageCompression d r : K →ₗ[ℂ] C) = deathImage d r := by
  rw [pageCompression]
  show LinearMap.range ((d r : K →ₗ[ℂ] C).comp ((deathPos d r).starProjection : K →ₗ[ℂ] K))
    = deathImage d r
  rw [LinearMap.range_comp, Submodule.range_starProjection, map_deathPos]

/-- The kernel-side page response `|d̂_r|`, extended by zero off the positive death layer. -/
def pageResponseK (d : ℕ → (K →L[ℂ] C)) (r : ℕ) : K →L[ℂ] K :=
  absMap (pageCompression d r)

/-- The cokernel-side page response `|d̂_r*|`, extended by zero off the negative death layer. -/
def pageResponseC (d : ℕ → (K →L[ℂ] C)) (r : ℕ) : C →L[ℂ] C :=
  absMap (adjoint (pageCompression d r))

theorem norm_pageResponseK_apply (d : ℕ → (K →L[ℂ] C)) (r : ℕ) (k : K) :
    ‖pageResponseK d r k‖ = ‖d r ((deathPos d r).starProjection k)‖ :=
  norm_absMap_apply _ k

theorem norm_pageResponseC_apply (d : ℕ → (K →L[ℂ] C)) (r : ℕ) (c : C) :
    ‖pageResponseC d r c‖ = ‖adjoint (pageCompression d r) c‖ :=
  norm_absMap_apply _ c

theorem ker_pageResponseK (d : ℕ → (K →L[ℂ] C)) (r : ℕ) :
    LinearMap.ker (pageResponseK d r : K →ₗ[ℂ] K) = (deathPos d r)ᗮ := by
  rw [pageResponseK, ker_absMap, ker_pageCompression]

theorem ker_pageResponseC (d : ℕ → (K →L[ℂ] C)) (r : ℕ) :
    LinearMap.ker (pageResponseC d r : C →ₗ[ℂ] C) = (deathImage d r)ᗮ := by
  rw [pageResponseC, ker_absMap, ← ContinuousLinearMap.orthogonal_range,
    range_pageCompression]

theorem range_pageResponseK_le (d : ℕ → (K →L[ℂ] C)) (r : ℕ) :
    LinearMap.range (pageResponseK d r : K →ₗ[ℂ] K) ≤ deathPos d r := by
  have h := range_le_ker_orthogonal_of_isSelfAdjoint
    (isSelfAdjoint_absMap (pageCompression d r))
  rw [show (absMap (pageCompression d r)) = pageResponseK d r from rfl,
    ker_pageResponseK, Submodule.orthogonal_orthogonal] at h
  exact h

theorem range_pageResponseC_le (d : ℕ → (K →L[ℂ] C)) (r : ℕ)
    (hcl : IsClosed ((deathImage d r : Submodule ℂ C) : Set C)) :
    LinearMap.range (pageResponseC d r : C →ₗ[ℂ] C) ≤ deathImage d r := by
  haveI : CompleteSpace (deathImage d r) := hcl.completeSpace_coe
  have h := range_le_ker_orthogonal_of_isSelfAdjoint
    (isSelfAdjoint_absMap (adjoint (pageCompression d r)))
  rw [show (absMap (adjoint (pageCompression d r))) = pageResponseC d r from rfl,
    ker_pageResponseC, Submodule.orthogonal_orthogonal] at h
  exact h

/-! ## The assembled formation operator -/

/-- The assembled kernel-side formation operator: the direct sum of the page responses. -/
def formationK (d : ℕ → (K →L[ℂ] C)) (m : ℕ) : K →L[ℂ] K :=
  ∑ r ∈ Finset.range m, pageResponseK d r

/-- The assembled cokernel-side formation operator. -/
def formationC (d : ℕ → (K →L[ℂ] C)) (m : ℕ) : C →L[ℂ] C :=
  ∑ r ∈ Finset.range m, pageResponseC d r

theorem formationK_apply (d : ℕ → (K →L[ℂ] C)) (m : ℕ) (k : K) :
    formationK d m k = ∑ r ∈ Finset.range m, pageResponseK d r k := by
  rw [formationK]
  simp

theorem formationC_apply (d : ℕ → (K →L[ℂ] C)) (m : ℕ) (c : C) :
    formationC d m c = ∑ r ∈ Finset.range m, pageResponseC d r c := by
  rw [formationC]
  simp

/-- **(PHF.17), kernel side.**  Formation energy splits pagewise. -/
theorem norm_sq_formationK (d : ℕ → (K →L[ℂ] C)) (m : ℕ) (k : K) :
    ‖formationK d m k‖ * ‖formationK d m k‖
      = ∑ r ∈ Finset.range m,
          ‖d r ((deathPos d r).starProjection k)‖ * ‖d r ((deathPos d r).starProjection k)‖ := by
  rw [formationK_apply]
  rw [norm_sq_sum_pairwise_orthogonal m (fun r => pageResponseK d r k) ?_]
  · exact Finset.sum_congr rfl fun r _ => by rw [norm_pageResponseK_apply]
  · intro r s hr hs hrs
    rcases Nat.lt_or_ge r s with hlt | hge
    · exact inner_eq_zero_symm.mp
        (inner_deathPos_eq_zero d hlt (range_pageResponseK_le d r ⟨k, rfl⟩)
          (range_pageResponseK_le d s ⟨k, rfl⟩))
    · have hsr : s < r := by omega
      exact inner_deathPos_eq_zero d hsr (range_pageResponseK_le d s ⟨k, rfl⟩)
        (range_pageResponseK_le d r ⟨k, rfl⟩)

/-- **(PHF.17), cokernel side.** -/
theorem norm_sq_formationC (d : ℕ → (K →L[ℂ] C)) (m : ℕ)
    (hcl : ∀ r, IsClosed ((deathImage d r : Submodule ℂ C) : Set C))
    (hle : ∀ r, deathImage d r ≤ cokerFlag d r) (c : C) :
    ‖formationC d m c‖ * ‖formationC d m c‖
      = ∑ r ∈ Finset.range m,
          ‖adjoint (pageCompression d r) c‖ * ‖adjoint (pageCompression d r) c‖ := by
  rw [formationC_apply]
  rw [norm_sq_sum_pairwise_orthogonal m (fun r => pageResponseC d r c) ?_]
  · exact Finset.sum_congr rfl fun r _ => by rw [norm_pageResponseC_apply]
  · intro r s hr hs hrs
    rcases Nat.lt_or_ge r s with hlt | hge
    · exact inner_eq_zero_symm.mp
        (inner_deathImage_eq_zero d hlt hle (range_pageResponseC_le d r (hcl r) ⟨c, rfl⟩)
          (range_pageResponseC_le d s (hcl s) ⟨c, rfl⟩))
    · have hsr : s < r := by omega
      exact inner_deathImage_eq_zero d hsr hle (range_pageResponseC_le d s (hcl s) ⟨c, rfl⟩)
        (range_pageResponseC_le d r (hcl r) ⟨c, rfl⟩)

/-- **(PHF.16), kernel side.**  Old-page formation misses exactly the stable survivor. -/
theorem ker_formationK (d : ℕ → (K →L[ℂ] C)) (m : ℕ) :
    LinearMap.ker (formationK d m : K →ₗ[ℂ] K) = kerFlag d m := by
  ext k
  rw [LinearMap.mem_ker, mem_kerFlag_iff]
  constructor
  · intro h0 r hr
    have hz : ∑ s ∈ Finset.range m,
        ‖d s ((deathPos d s).starProjection k)‖ * ‖d s ((deathPos d s).starProjection k)‖ = 0 := by
      rw [← norm_sq_formationK]
      have hk0 : formationK d m k = 0 := h0
      rw [hk0, norm_zero, mul_zero]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s (_ : s ∈ Finset.range m) => by positivity)).mp hz r (Finset.mem_range.mpr hr)
    have hnn := norm_nonneg (d r ((deathPos d r).starProjection k))
    have hn : ‖d r ((deathPos d r).starProjection k)‖ = 0 := by nlinarith
    have hmem : k ∈ LinearMap.ker (pageCompression d r : K →ₗ[ℂ] C) := norm_eq_zero.mp hn
    rwa [ker_pageCompression] at hmem
  · intro hall
    have hz : ∑ s ∈ Finset.range m,
        ‖d s ((deathPos d s).starProjection k)‖ * ‖d s ((deathPos d s).starProjection k)‖ = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      have hk : k ∈ LinearMap.ker (pageCompression d s : K →ₗ[ℂ] C) := by
        rw [ker_pageCompression]
        exact hall s (Finset.mem_range.mp hs)
      have h0 : d s ((deathPos d s).starProjection k) = 0 := hk
      rw [h0, norm_zero, mul_zero]
    have hnorm : ‖formationK d m k‖ * ‖formationK d m k‖ = 0 := by
      rw [norm_sq_formationK, hz]
    have hnn := norm_nonneg (formationK d m k)
    show formationK d m k = 0
    exact norm_eq_zero.mp (by nlinarith)

/-- **(PHF.16), cokernel side.** -/
theorem ker_formationC (d : ℕ → (K →L[ℂ] C)) (m : ℕ)
    (hcl : ∀ r, IsClosed ((deathImage d r : Submodule ℂ C) : Set C))
    (hle : ∀ r, deathImage d r ≤ cokerFlag d r) :
    LinearMap.ker (formationC d m : C →ₗ[ℂ] C) = cokerFlag d m := by
  ext c
  rw [LinearMap.mem_ker, mem_cokerFlag_iff]
  constructor
  · intro h0 r hr
    have hz : ∑ s ∈ Finset.range m,
        ‖adjoint (pageCompression d s) c‖ * ‖adjoint (pageCompression d s) c‖ = 0 := by
      rw [← norm_sq_formationC d m hcl hle]
      have hc0 : formationC d m c = 0 := h0
      rw [hc0, norm_zero, mul_zero]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s (_ : s ∈ Finset.range m) => by positivity)).mp hz r (Finset.mem_range.mpr hr)
    have hnn := norm_nonneg (adjoint (pageCompression d r) c)
    have hn : ‖adjoint (pageCompression d r) c‖ = 0 := by nlinarith
    have hmem : c ∈ LinearMap.ker (adjoint (pageCompression d r) : C →ₗ[ℂ] K) :=
      norm_eq_zero.mp hn
    rw [← ContinuousLinearMap.orthogonal_range, range_pageCompression] at hmem
    exact hmem
  · intro hall
    have hz : ∑ s ∈ Finset.range m,
        ‖adjoint (pageCompression d s) c‖ * ‖adjoint (pageCompression d s) c‖ = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      have hk : c ∈ LinearMap.ker (adjoint (pageCompression d s) : C →ₗ[ℂ] K) := by
        rw [← ContinuousLinearMap.orthogonal_range, range_pageCompression]
        exact hall s (Finset.mem_range.mp hs)
      have h0 : adjoint (pageCompression d s) c = 0 := hk
      rw [h0, norm_zero, mul_zero]
    have hnorm : ‖formationC d m c‖ * ‖formationC d m c‖ = 0 := by
      rw [norm_sq_formationC d m hcl hle, hz]
    have hnn := norm_nonneg (formationC d m c)
    show formationC d m c = 0
    exact norm_eq_zero.mp (by nlinarith)

/-! ## Global properness (PHF.18) -/

omit [CompleteSpace C] in
theorem starProjection_deathPos_sum (d : ℕ → (K →L[ℂ] C)) (m : ℕ) (f : ℕ → K) (z : K)
    (hf : ∀ s, s < m → f s ∈ deathPos d s) (hz : z ∈ kerFlag d m) {r : ℕ} (hr : r < m) :
    (deathPos d r).starProjection ((∑ s ∈ Finset.range m, f s) + z) = f r := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hf r hr) ?_
  intro w hw
  have hsub : ((∑ s ∈ Finset.range m, f s) + z) - f r
      = ((∑ s ∈ Finset.range m, f s) - f r) + z := by abel
  have hzw : ⟪z, w⟫_ℂ = 0 := inner_deathPos_kerFlag_eq_zero d hr hw hz
  have hsum : ⟪∑ s ∈ Finset.range m, f s, w⟫_ℂ = ⟪f r, w⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_eq_single r (fun s hs hsr => ?_) (fun hnr => absurd
      (Finset.mem_range.mpr hr) hnr)
    rcases Nat.lt_or_ge r s with hlt | hge
    · exact inner_deathPos_eq_zero d hlt hw (hf s (Finset.mem_range.mp hs))
    · have hsr' : s < r := by omega
      exact inner_eq_zero_symm.mp
        (inner_deathPos_eq_zero d hsr' (hf s (Finset.mem_range.mp hs)) hw)
  rw [hsub, inner_add_left, inner_sub_left, hsum, hzw, sub_self, add_zero]

theorem exists_uniform_deathGap (d : ℕ → (K →L[ℂ] C)) (m : ℕ)
    (hcl : ∀ r, IsClosed ((deathImage d r : Submodule ℂ C) : Set C)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ r, r < m → ∀ x ∈ deathPos d r, γ * ‖x‖ ≤ ‖d r x‖ := by
  induction m with
  | zero => exact ⟨1, one_pos, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ m ih =>
    obtain ⟨γ₁, hγ₁, h₁⟩ := ih
    obtain ⟨γ₂, hγ₂, h₂⟩ := exists_pos_deathGap d m (hcl m)
    refine ⟨min γ₁ γ₂, lt_min hγ₁ hγ₂, fun r hr x hx => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg x)) (h₁ r hlt x hx)
    · subst heq
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg x)) (h₂ x hx)

/-- **Global properness (PHF.18).**  The assembled formation operator is bounded below on the
orthogonal complement of the stable survivor by the least page gap. -/
theorem formationK_hasTransverseLowerBound (d : ℕ → (K →L[ℂ] C)) (m : ℕ)
    (hcl : ∀ r, IsClosed ((deathImage d r : Submodule ℂ C) : Set C)) :
    ContinuousLinearMap.HasTransverseLowerBound (formationK d m) := by
  obtain ⟨γ, hγ, hbound⟩ := exists_uniform_deathGap d m hcl
  refine ⟨γ, hγ, ?_⟩
  intro k hk
  rw [ker_formationK] at hk
  obtain ⟨f, z, hf, hz, hkeq⟩ := exists_death_decomposition d m k
  have hzk : ⟪z, k⟫_ℂ = 0 := (Submodule.mem_orthogonal _ k).mp hk z hz
  have hzf : ⟪z, ∑ s ∈ Finset.range m, f s⟫_ℂ = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    exact inner_deathPos_kerFlag_eq_zero d (Finset.mem_range.mp hs) (hf s
      (Finset.mem_range.mp hs)) hz
  have hzz : ⟪z, z⟫_ℂ = 0 := by
    rw [hkeq, inner_add_right, hzf, zero_add] at hzk
    exact hzk
  have hz0 : z = 0 := inner_self_eq_zero.mp hzz
  have hknorm : ‖k‖ * ‖k‖ = ∑ r ∈ Finset.range m, ‖f r‖ * ‖f r‖ := by
    rw [hkeq, norm_sq_death_decomposition d m f z hf hz, hz0, norm_zero, mul_zero, add_zero]
  have hproj : ∀ r, r < m → (deathPos d r).starProjection k = f r := fun r hr => by
    rw [hkeq]
    exact starProjection_deathPos_sum d m f z hf hz hr
  have hAnorm : ‖formationK d m k‖ * ‖formationK d m k‖
      = ∑ r ∈ Finset.range m, ‖d r (f r)‖ * ‖d r (f r)‖ := by
    rw [norm_sq_formationK]
    exact Finset.sum_congr rfl fun r hr => by rw [hproj r (Finset.mem_range.mp hr)]
  have hcomp : γ * γ * (‖k‖ * ‖k‖) ≤ ‖formationK d m k‖ * ‖formationK d m k‖ := by
    rw [hknorm, hAnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hb := hbound r (Finset.mem_range.mp hr) (f r) (hf r (Finset.mem_range.mp hr))
    have hsq := mul_self_le_mul_self (mul_nonneg hγ.le (norm_nonneg (f r))) hb
    nlinarith [hsq]
  nlinarith [hcomp, norm_nonneg k, norm_nonneg (formationK d m k), hγ.le,
    mul_nonneg hγ.le (norm_nonneg k)]

theorem isClosed_range_formationK (d : ℕ → (K →L[ℂ] C)) (m : ℕ)
    (hcl : ∀ r, IsClosed ((deathImage d r : Submodule ℂ C) : Set C)) :
    IsClosed (Set.range (formationK d m)) :=
  (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range (formationK d m)).mp
    (formationK_hasTransverseLowerBound d m hcl)

/-! ## Stable-organ selection -/

section Selection

variable {E F W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem norm_sq_prodL2 (x : WithLp 2 (F × W)) :
    ‖x‖ * ‖x‖ = ‖(WithLp.ofLp x).1‖ * ‖(WithLp.ofLp x).1‖
      + ‖(WithLp.ofLp x).2‖ * ‖(WithLp.ofLp x).2‖ := by
  have h := WithLp.prod_inner_apply (𝕜 := ℂ) x x
  have h2 := congrArg RCLike.re h
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, pow_two] using h2

/-- The completed formation: page work paired with a terminal response. -/
def completedFormation (A : E →L[ℂ] F) (B : E →L[ℂ] W) : E →L[ℂ] WithLp 2 (F × W) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ F W).symm :
      F × W →L[ℂ] WithLp 2 (F × W)).comp (A.prod B)

omit [CompleteSpace E] in
@[simp] theorem ofLp_completedFormation (A : E →L[ℂ] F) (B : E →L[ℂ] W) (x : E) :
    WithLp.ofLp (completedFormation A B x) = (A x, B x) := rfl

omit [CompleteSpace E] in
theorem norm_sq_completedFormation (A : E →L[ℂ] F) (B : E →L[ℂ] W) (x : E) :
    ‖completedFormation A B x‖ * ‖completedFormation A B x‖
      = ‖A x‖ * ‖A x‖ + ‖B x‖ * ‖B x‖ := by
  rw [norm_sq_prodL2, ofLp_completedFormation]

omit [CompleteSpace E] in
/-- **(PHF.22).**  The completed kernel is the intersection of the two kernels. -/
theorem ker_completedFormation (A : E →L[ℂ] F) (B : E →L[ℂ] W) :
    LinearMap.ker (completedFormation A B : E →ₗ[ℂ] WithLp 2 (F × W))
      = LinearMap.ker (A : E →ₗ[ℂ] F) ⊓ LinearMap.ker (B : E →ₗ[ℂ] W) := by
  ext x
  constructor
  · intro hx
    have h0 : ((WithLp.prodContinuousLinearEquiv 2 ℂ F W).symm :
        F × W →L[ℂ] WithLp 2 (F × W)) ((A.prod B) x) = 0 := hx
    have hpb : (A.prod B) x = 0 := by
      have hc := congrArg (WithLp.prodContinuousLinearEquiv 2 ℂ F W) h0
      simpa using hc
    have hp : (A x, B x) = ((0 : F), (0 : W)) := hpb
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨h1, h2⟩
    have hA : A x = 0 := h1
    have hB : B x = 0 := h2
    have hpb : (A.prod B) x = 0 := by
      show (A x, B x) = 0
      rw [hA, hB]
      rfl
    show ((WithLp.prodContinuousLinearEquiv 2 ℂ F W).symm :
      F × W →L[ℂ] WithLp 2 (F × W)) ((A.prod B) x) = 0
    rw [hpb, map_zero]

omit [CompleteSpace E] in
theorem norm_sq_starProjection_add (S : Submodule ℂ E) [S.HasOrthogonalProjection] (x : E) :
    ‖x‖ * ‖x‖ = ‖S.starProjection x‖ * ‖S.starProjection x‖
      + ‖x - S.starProjection x‖ * ‖x - S.starProjection x‖ := by
  have horth : ⟪S.starProjection x, x - S.starProjection x⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal S _).mp
      (S.sub_starProjection_mem_orthogonal (v := x)) _ (S.starProjection_apply_mem x)
  have hsum : S.starProjection x + (x - S.starProjection x) = x := by abel
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (S.starProjection x) (x - S.starProjection x) horth
  rw [hsum] at this
  exact this

omit [CompleteSpace E] in
/-- **(PHF.24).**  A page gap on the complement and a terminal gap on the stable sector give a
global gap equal to their minimum. -/
theorem completedFormation_lower_bound {A : E →L[ℂ] F} {B : E →L[ℂ] W} {S : Submodule ℂ E}
    [S.HasOrthogonalProjection] (hker : LinearMap.ker (A : E →ₗ[ℂ] F) = S)
    {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (hA : ∀ x ∈ Sᗮ, γ * ‖x‖ ≤ ‖A x‖) (hB : ∀ x ∈ S, β * ‖x‖ ≤ ‖B x‖) (x : E) :
    min γ β * ‖x‖ ≤ ‖completedFormation A (B.comp S.starProjection) x‖ := by
  have hker0 : A (S.starProjection x) = 0 := by
    have : S.starProjection x ∈ LinearMap.ker (A : E →ₗ[ℂ] F) := by
      rw [hker]
      exact S.starProjection_apply_mem x
    exact this
  have hAx : A x = A (x - S.starProjection x) := by
    rw [map_sub, hker0, sub_zero]
  have h1 : γ * ‖x - S.starProjection x‖ ≤ ‖A x‖ := by
    rw [hAx]
    exact hA _ (S.sub_starProjection_mem_orthogonal (v := x))
  have h2 : β * ‖S.starProjection x‖ ≤ ‖(B.comp S.starProjection) x‖ :=
    hB _ (S.starProjection_apply_mem x)
  have hsplit := norm_sq_starProjection_add S x
  have hnormsq := norm_sq_completedFormation A (B.comp S.starProjection) x
  have hmin1 : min γ β ≤ γ := min_le_left _ _
  have hmin2 : min γ β ≤ β := min_le_right _ _
  have hminpos : 0 < min γ β := lt_min hγ hβ
  have hq1 : (min γ β * ‖x - S.starProjection x‖) * (min γ β * ‖x - S.starProjection x‖)
      ≤ ‖A x‖ * ‖A x‖ := by
    have hle : min γ β * ‖x - S.starProjection x‖ ≤ ‖A x‖ :=
      le_trans (mul_le_mul_of_nonneg_right hmin1 (norm_nonneg _)) h1
    exact mul_self_le_mul_self (mul_nonneg hminpos.le (norm_nonneg _)) hle
  have hq2 : (min γ β * ‖S.starProjection x‖) * (min γ β * ‖S.starProjection x‖)
      ≤ ‖(B.comp S.starProjection) x‖ * ‖(B.comp S.starProjection) x‖ := by
    have hle : min γ β * ‖S.starProjection x‖ ≤ ‖(B.comp S.starProjection) x‖ :=
      le_trans (mul_le_mul_of_nonneg_right hmin2 (norm_nonneg _)) h2
    exact mul_self_le_mul_self (mul_nonneg hminpos.le (norm_nonneg _)) hle
  have e1 : (min γ β * ‖x‖) * (min γ β * ‖x‖)
      = (min γ β * ‖S.starProjection x‖) * (min γ β * ‖S.starProjection x‖)
        + (min γ β * ‖x - S.starProjection x‖) * (min γ β * ‖x - S.starProjection x‖) := by
    linear_combination (min γ β * min γ β) * hsplit
  have hkey : (min γ β * ‖x‖) * (min γ β * ‖x‖)
      ≤ ‖completedFormation A (B.comp S.starProjection) x‖
        * ‖completedFormation A (B.comp S.starProjection) x‖ := by
    rw [e1, hnormsq]
    linarith [hq1, hq2]
  nlinarith [hkey, norm_nonneg (completedFormation A (B.comp S.starProjection) x),
    mul_nonneg hminpos.le (norm_nonneg x)]

omit [CompleteSpace E] in
/-- **(PHF.26).**  A response factored through the old formation is blind wherever the old
formation is, so adjoining it cannot shrink the common kernel. -/
theorem ker_factored_response (A : E →L[ℂ] F) (Sm : F →L[ℂ] W) :
    LinearMap.ker (A : E →ₗ[ℂ] F) ≤ LinearMap.ker ((Sm.comp A) : E →ₗ[ℂ] W)
      ∧ LinearMap.ker (A : E →ₗ[ℂ] F) ⊓ LinearMap.ker ((Sm.comp A) : E →ₗ[ℂ] W)
        = LinearMap.ker (A : E →ₗ[ℂ] F) := by
  have hle : LinearMap.ker (A : E →ₗ[ℂ] F) ≤ LinearMap.ker ((Sm.comp A) : E →ₗ[ℂ] W) := by
    intro x hx
    have h0 : A x = 0 := hx
    show Sm (A x) = 0
    rw [h0, map_zero]
  exact ⟨hle, inf_eq_left.mpr hle⟩

omit [CompleteSpace E] in
/-- **(PHF.28).**  Bounded formation work along a dilation orbit forces the vector into the
kernel. -/
theorem bddAbove_norm_orbit_iff (A : E →L[ℂ] F) {a : ℝ} (ha : 1 < a) (x : E) :
    BddAbove (Set.range fun n : ℕ => ‖A ((a ^ n : ℝ) • x)‖) ↔ A x = 0 := by
  have hnorm : ∀ n : ℕ, ‖A ((a ^ n : ℝ) • x)‖ = a ^ n * ‖A x‖ := by
    intro n
    rw [ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
      abs_of_pos (pow_pos (lt_trans one_pos ha) n)]
  constructor
  · rintro ⟨M, hM⟩
    by_contra hAx
    have hpos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖A x‖) ha
    have hle : a ^ n * ‖A x‖ ≤ M := by
      have := hM (Set.mem_range_self n)
      rwa [hnorm n] at this
    rw [div_lt_iff₀ hpos] at hn
    linarith
  · intro hAx
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    show ‖A ((a ^ n : ℝ) • x)‖ ≤ 0
    rw [hnorm n, hAx, norm_zero, mul_zero]

end Selection

/-! ## Functional-equation neutrality -/

section FunctionalEquation

variable {K' C' : Type*}
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup C'] [InnerProductSpace ℂ C'] [CompleteSpace C']

theorem map_orthogonal_of_isometryEquiv {E E' : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (J : E ≃ₗᵢ[ℂ] E') (S : Submodule ℂ E) :
    Submodule.map (J.toLinearEquiv : E →ₗ[ℂ] E') Sᗮ
      = (Submodule.map (J.toLinearEquiv : E →ₗ[ℂ] E') S)ᗮ := by
  apply le_antisymm
  · rintro y ⟨u, hu, rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro v ⟨w, hw, rfl⟩
    show ⟪J w, J u⟫_ℂ = 0
    rw [J.inner_map_map]
    exact (Submodule.mem_orthogonal S u).mp hu w hw
  · intro y hy
    refine ⟨J.symm y, ?_, by simp⟩
    show J.symm y ∈ Sᗮ
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hzero : ⟪J w, y⟫_ℂ = 0 := (Submodule.mem_orthogonal _ y).mp hy (J w) ⟨w, hw, rfl⟩
    have hmap : ⟪J w, J (J.symm y)⟫_ℂ = ⟪w, J.symm y⟫_ℂ := J.inner_map_map w (J.symm y)
    rw [J.apply_symm_apply] at hmap
    rw [← hmap]
    exact hzero

omit [CompleteSpace K] [CompleteSpace C] [CompleteSpace K'] [CompleteSpace C'] in
/-- **(PHF.29)–(PHF.30).**  A unitary intertwiner transports the kernel flag. -/
theorem kerFlag_map_of_intertwine (d : ℕ → (K →L[ℂ] C)) (d' : ℕ → (K' →L[ℂ] C'))
    (J : K ≃ₗᵢ[ℂ] K') (J' : C ≃ₗᵢ[ℂ] C')
    (hint : ∀ r, ∀ x : K, d' r (J x) = J' (d r x)) (r : ℕ) :
    kerFlag d' r = Submodule.map (J.toLinearEquiv : K →ₗ[ℂ] K') (kerFlag d r) := by
  induction r with
  | zero =>
    show (⊤ : Submodule ℂ K') = Submodule.map (J.toLinearEquiv : K →ₗ[ℂ] K') ⊤
    rw [Submodule.map_top]
    symm
    rw [LinearMap.range_eq_top]
    exact J.surjective
  | succ r ih =>
    show kerFlag d' r ⊓ LinearMap.ker (d' r : K' →ₗ[ℂ] C')
      = Submodule.map (J.toLinearEquiv : K →ₗ[ℂ] K')
        (kerFlag d r ⊓ LinearMap.ker (d r : K →ₗ[ℂ] C))
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      rw [ih] at hy1
      obtain ⟨x, hx, hxy⟩ := hy1
      refine ⟨x, ⟨hx, ?_⟩, hxy⟩
      have h0 : d' r y = 0 := hy2
      have hjx : J x = y := hxy
      have hkey := hint r x
      rw [hjx, h0] at hkey
      show d r x = 0
      exact J'.injective (by rw [← hkey, map_zero])
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [ih]
        exact ⟨x, hx1, rfl⟩
      · show d' r (J x) = 0
        rw [hint r x]
        have hx0 : d r x = 0 := hx2
        rw [hx0, map_zero]

omit [CompleteSpace K] [CompleteSpace C] [CompleteSpace K'] [CompleteSpace C'] in
/-- A unitary intertwiner transports the negative death layers. -/
theorem deathImage_map_of_intertwine (d : ℕ → (K →L[ℂ] C)) (d' : ℕ → (K' →L[ℂ] C'))
    (J : K ≃ₗᵢ[ℂ] K') (J' : C ≃ₗᵢ[ℂ] C')
    (hint : ∀ r, ∀ x : K, d' r (J x) = J' (d r x)) (r : ℕ) :
    deathImage d' r = Submodule.map (J'.toLinearEquiv : C →ₗ[ℂ] C') (deathImage d r) := by
  show Submodule.map (d' r : K' →ₗ[ℂ] C') (kerFlag d' r)
    = Submodule.map (J'.toLinearEquiv : C →ₗ[ℂ] C')
      (Submodule.map (d r : K →ₗ[ℂ] C) (kerFlag d r))
  rw [kerFlag_map_of_intertwine d d' J J' hint r]
  apply le_antisymm
  · rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨d r x, ⟨x, hx, rfl⟩, (hint r x).symm⟩
  · rintro z ⟨c, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨J x, ⟨x, hx, rfl⟩, hint r x⟩

omit [CompleteSpace K] [CompleteSpace C] [CompleteSpace K'] [CompleteSpace C'] in
/-- A unitary intertwiner transports the positive death layers. -/
theorem deathPos_map_of_intertwine (d : ℕ → (K →L[ℂ] C)) (d' : ℕ → (K' →L[ℂ] C'))
    (J : K ≃ₗᵢ[ℂ] K') (J' : C ≃ₗᵢ[ℂ] C')
    (hint : ∀ r, ∀ x : K, d' r (J x) = J' (d r x)) (r : ℕ) :
    deathPos d' r = Submodule.map (J.toLinearEquiv : K →ₗ[ℂ] K') (deathPos d r) := by
  show kerFlag d' r ⊓ (kerFlag d' (r + 1))ᗮ
    = Submodule.map (J.toLinearEquiv : K →ₗ[ℂ] K') (kerFlag d r ⊓ (kerFlag d (r + 1))ᗮ)
  rw [kerFlag_map_of_intertwine d d' J J' hint r,
    kerFlag_map_of_intertwine d d' J J' hint (r + 1),
    ← map_orthogonal_of_isometryEquiv J (kerFlag d (r + 1)),
    Submodule.map_inf _ J.injective]

omit [CompleteSpace K] [CompleteSpace C] [CompleteSpace K'] [CompleteSpace C'] in
/-- Unitary intertwiners preserve the page gaps. -/
theorem norm_intertwine (d : ℕ → (K →L[ℂ] C)) (d' : ℕ → (K' →L[ℂ] C'))
    (J : K ≃ₗᵢ[ℂ] K') (J' : C ≃ₗᵢ[ℂ] C')
    (hint : ∀ r, ∀ x : K, d' r (J x) = J' (d r x)) (r : ℕ) (x : K) :
    ‖d' r (J x)‖ = ‖d r x‖ := by
  rw [hint r x, J'.norm_map]

end FunctionalEquation

end

end GaloisForLFunctions.HTGeometry
