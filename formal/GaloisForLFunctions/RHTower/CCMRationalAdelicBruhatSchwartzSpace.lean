import GaloisForLFunctions.RHTower.CCMRationalAdelicBruhatSimpleTensorReal
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleNonarchimedean
import GaloisForLFunctions.RHTower.CCMRationalIntegralAdeleHaarIndex

/-!
# The algebraic Bruhat core is the whole adelic Bruhat--Schwartz space

Bruhat's Schwartz space of `ℝ × 𝔸_f` consists of the functions that are periodic under a compact
open subgroup of the finite adeles, supported in a compact set of finite adeles, and Schwartz along
every archimedean fibre.  Because a compact set meets only finitely many cosets of an open
subgroup, every such function is a *finite* sum of products `f(x) · 1_{y + K}(y')`.  Hence the
algebraic tensor product

```text
𝒮(ℝ) ⊗ C_c^∞(𝔸_f)
```

is not merely a dense core: its canonical realization as functions on `ℝ × 𝔸_f` is exactly Bruhat's
space, so no completion step separates the corpus's algebraic adelic core from `𝒮(𝔸_ℚ)`.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions
namespace RHTower

private abbrev FinAdele := CCMRationalFiniteAdele
private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor

/-- The rational adele ring in the archimedean/finite presentation used by CCM. -/
abbrev CCMRationalAdele := ℝ × FinAdele

/-! ## The canonical realization of the algebraic core -/

/-- Realization of one simple tensor as a function on the adeles. -/
def ccmRationalAdelicBruhatEvalBilinear : Arch →ₗ[ℂ] FinBruhat →ₗ[ℂ] (CCMRationalAdele → ℂ) :=
  LinearMap.mk₂ ℂ (fun f g p => f p.1 * (g.1 : FinAdele → ℂ) p.2)
    (fun f₁ f₂ g => by
      funext p
      simp [add_mul])
    (fun c f g => by
      funext p
      simp [mul_assoc])
    (fun f g₁ g₂ => by
      funext p
      simp [mul_add])
    (fun c f g => by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      change f p.1 * (c * (g.1 : FinAdele → ℂ) p.2) = c * (f p.1 * (g.1 : FinAdele → ℂ) p.2)
      ring)

/-- Realization of the algebraic adelic Bruhat core as genuine functions on `ℝ × 𝔸_f`. -/
def ccmRationalAdelicBruhatEval : Core →ₗ[ℂ] (CCMRationalAdele → ℂ) :=
  TensorProduct.lift ccmRationalAdelicBruhatEvalBilinear

@[simp]
theorem ccmRationalAdelicBruhatEval_tmul (f : Arch) (g : FinBruhat) (p : CCMRationalAdele) :
    ccmRationalAdelicBruhatEval (f ⊗ₜ[ℂ] g) p = f p.1 * (g.1 : FinAdele → ℂ) p.2 := rfl

/-! ## Bruhat's condition -/

/-- Bruhat's Schwartz condition on `ℝ × 𝔸_f`: one compact open period in the finite variable, one
compact support in the finite variable, and a Schwartz function along every finite fibre. -/
structure IsCCMRationalAdelicBruhatSchwartz (φ : CCMRationalAdele → ℂ) : Prop where
  period : ∃ K : AddSubgroup FinAdele, IsOpen (K : Set FinAdele) ∧ IsCompact (K : Set FinAdele) ∧
    ∀ (x : ℝ) (y k : FinAdele), k ∈ K → φ (x, y + k) = φ (x, y)
  support : ∃ C : Set FinAdele, IsCompact C ∧ ∀ (x : ℝ) (y : FinAdele), y ∉ C → φ (x, y) = 0
  fibre : ∀ y : FinAdele, ∃ f : Arch, ∀ x : ℝ, φ (x, y) = f x

theorem isCCMRationalAdelicBruhatSchwartz_zero :
    IsCCMRationalAdelicBruhatSchwartz (0 : CCMRationalAdele → ℂ) where
  period :=
    ⟨ccmRationalIntegralFiniteAdelesAddSubgroup,
      ccmRationalIntegralFiniteAdeles_isOpen, ccmRationalIntegralFiniteAdeles_isCompact,
      fun _ _ _ _ => rfl⟩
  support := ⟨∅, isCompact_empty, fun _ _ _ => rfl⟩
  fibre := fun _ => ⟨0, fun _ => rfl⟩

/-- An open subgroup of the finite adeles has a compact open refinement. -/
theorem ccmRationalFiniteAdele_exists_compactOpen_le {K : AddSubgroup FinAdele}
    (hK : IsOpen (K : Set FinAdele)) :
    ∃ L : AddSubgroup FinAdele, IsOpen (L : Set FinAdele) ∧ IsCompact (L : Set FinAdele) ∧
      (L : Set FinAdele) ⊆ (K : Set FinAdele) := by
  have hKclosed : IsClosed (K : Set FinAdele) :=
    (⟨K, hK⟩ : OpenAddSubgroup FinAdele).isClosed
  have hZclosed : IsClosed ccmRationalIntegralFiniteAdeles :=
    ccmRationalIntegralFiniteAdeles_isCompact.isClosed
  have hcoe : ((K ⊓ ccmRationalIntegralFiniteAdelesAddSubgroup : AddSubgroup FinAdele) :
      Set FinAdele) = (K : Set FinAdele) ∩ ccmRationalIntegralFiniteAdeles := rfl
  refine ⟨K ⊓ ccmRationalIntegralFiniteAdelesAddSubgroup, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact hK.inter ccmRationalIntegralFiniteAdeles_isOpen
  · rw [hcoe]
    exact ccmRationalIntegralFiniteAdeles_isCompact.of_isClosed_subset
      (hKclosed.inter hZclosed) (fun _ hx => hx.2)
  · rw [hcoe]
    exact fun _ hx => hx.1

theorem isCCMRationalAdelicBruhatSchwartz_add {φ ψ : CCMRationalAdele → ℂ}
    (hφ : IsCCMRationalAdelicBruhatSchwartz φ) (hψ : IsCCMRationalAdelicBruhatSchwartz ψ) :
    IsCCMRationalAdelicBruhatSchwartz (φ + ψ) where
  period := by
    obtain ⟨K, hKopen, hKcompact, hKper⟩ := hφ.period
    obtain ⟨L, hLopen, hLcompact, hLper⟩ := hψ.period
    have hcoe : ((K ⊓ L : AddSubgroup FinAdele) : Set FinAdele) =
        (K : Set FinAdele) ∩ (L : Set FinAdele) := rfl
    refine ⟨K ⊓ L, ?_, ?_, ?_⟩
    · rw [hcoe]
      exact hKopen.inter hLopen
    · have hLclosed : IsClosed (L : Set FinAdele) :=
        (⟨L, hLopen⟩ : OpenAddSubgroup FinAdele).isClosed
      rw [hcoe]
      exact hKcompact.of_isClosed_subset (hKcompact.isClosed.inter hLclosed) (fun _ hx => hx.1)
    · intro x y k hk
      simp only [Pi.add_apply]
      rw [hKper x y k hk.1, hLper x y k hk.2]
  support := by
    obtain ⟨C, hC, hCsupp⟩ := hφ.support
    obtain ⟨D, hD, hDsupp⟩ := hψ.support
    refine ⟨C ∪ D, hC.union hD, fun x y hy => ?_⟩
    simp only [Pi.add_apply]
    rw [hCsupp x y (fun h => hy (Or.inl h)), hDsupp x y (fun h => hy (Or.inr h)), add_zero]
  fibre := by
    intro y
    obtain ⟨f, hf⟩ := hφ.fibre y
    obtain ⟨g, hg⟩ := hψ.fibre y
    exact ⟨f + g, fun x => by simp [hf x, hg x]⟩

theorem isCCMRationalAdelicBruhatSchwartz_smul {φ : CCMRationalAdele → ℂ} (c : ℂ)
    (hφ : IsCCMRationalAdelicBruhatSchwartz φ) :
    IsCCMRationalAdelicBruhatSchwartz (c • φ) where
  period := by
    obtain ⟨K, hKopen, hKcompact, hKper⟩ := hφ.period
    refine ⟨K, hKopen, hKcompact, fun x y k hk => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hKper x y k hk]
  support := by
    obtain ⟨C, hC, hCsupp⟩ := hφ.support
    refine ⟨C, hC, fun x y hy => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hCsupp x y hy, mul_zero]
  fibre := by
    intro y
    obtain ⟨f, hf⟩ := hφ.fibre y
    exact ⟨c • f, fun x => by simp [hf x]⟩

/-- Bruhat's Schwartz space of the rational adeles, as a submodule of all functions. -/
def CCMRationalAdelicBruhatSchwartz : Submodule ℂ (CCMRationalAdele → ℂ) where
  carrier := {φ | IsCCMRationalAdelicBruhatSchwartz φ}
  zero_mem' := isCCMRationalAdelicBruhatSchwartz_zero
  add_mem' := isCCMRationalAdelicBruhatSchwartz_add
  smul_mem' := fun c _ hx => isCCMRationalAdelicBruhatSchwartz_smul c hx

@[simp]
theorem mem_ccmRationalAdelicBruhatSchwartz_iff (φ : CCMRationalAdele → ℂ) :
    φ ∈ CCMRationalAdelicBruhatSchwartz ↔ IsCCMRationalAdelicBruhatSchwartz φ := Iff.rfl

/-! ## The core realizes into Bruhat's space -/

theorem isCCMRationalAdelicBruhatSchwartz_tmul (f : Arch) (g : FinBruhat) :
    IsCCMRationalAdelicBruhatSchwartz (ccmRationalAdelicBruhatEval (f ⊗ₜ[ℂ] g)) where
  period := by
    obtain ⟨V, hV⟩ := ccmRationalFiniteBruhat_exists_openAddSubgroup_stabilizer g
    obtain ⟨L, hLopen, hLcompact, hLV⟩ :=
      ccmRationalFiniteAdele_exists_compactOpen_le V.isOpen
    refine ⟨L, hLopen, hLcompact, fun x y k hk => ?_⟩
    have hkV : k ∈ V := hLV hk
    have := hV y ⟨k, hkV⟩
    simp only [ccmRationalAdelicBruhatEval_tmul]
    rw [this]
  support := by
    refine ⟨tsupport (g.1 : FinAdele → ℂ), g.2, fun x y hy => ?_⟩
    have hzero : (g.1 : FinAdele → ℂ) y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [ccmRationalAdelicBruhatEval_tmul]
    rw [hzero, mul_zero]
  fibre := by
    intro y
    refine ⟨((g.1 : FinAdele → ℂ) y) • f, fun x => ?_⟩
    simp only [ccmRationalAdelicBruhatEval_tmul, smul_apply, smul_eq_mul]
    ring

theorem isCCMRationalAdelicBruhatSchwartz_eval (t : Core) :
    IsCCMRationalAdelicBruhatSchwartz (ccmRationalAdelicBruhatEval t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      simpa using isCCMRationalAdelicBruhatSchwartz_zero
  | tmul f g => exact isCCMRationalAdelicBruhatSchwartz_tmul f g
  | add s t hs ht =>
      have := isCCMRationalAdelicBruhatSchwartz_add hs ht
      simpa using this

theorem range_ccmRationalAdelicBruhatEval_le :
    LinearMap.range ccmRationalAdelicBruhatEval ≤ CCMRationalAdelicBruhatSchwartz := by
  rintro φ ⟨t, rfl⟩
  exact isCCMRationalAdelicBruhatSchwartz_eval t

/-! ## Every Bruhat function is a finite sum of products -/

section Decomposition

variable {K : AddSubgroup FinAdele}

/-- The coset of a compact open period subgroup through a finite adele. -/
private def bruhatCoset (K : AddSubgroup FinAdele) (y : FinAdele) : Set FinAdele :=
  {z | z - y ∈ K}

private theorem mem_bruhatCoset {y z : FinAdele} : z ∈ bruhatCoset K y ↔ z - y ∈ K := Iff.rfl

private theorem bruhatCoset_isOpen (hKopen : IsOpen (K : Set FinAdele)) (y : FinAdele) :
    IsOpen (bruhatCoset K y) :=
  hKopen.preimage (continuous_id.sub continuous_const)

private theorem bruhatCoset_isClosed (hKopen : IsOpen (K : Set FinAdele)) (y : FinAdele) :
    IsClosed (bruhatCoset K y) :=
  ((⟨K, hKopen⟩ : OpenAddSubgroup FinAdele).isClosed).preimage
    (continuous_id.sub continuous_const)

private theorem bruhatCoset_isClopen (hKopen : IsOpen (K : Set FinAdele)) (y : FinAdele) :
    IsClopen (bruhatCoset K y) :=
  ⟨bruhatCoset_isClosed hKopen y, bruhatCoset_isOpen hKopen y⟩

private theorem bruhatCoset_isCompact (hKcompact : IsCompact (K : Set FinAdele)) (y : FinAdele) :
    IsCompact (bruhatCoset K y) := by
  have himage : bruhatCoset K y = (fun z : FinAdele => z + y) '' (K : Set FinAdele) := by
    ext z
    constructor
    · intro hz
      exact ⟨z - y, hz, by ring⟩
    · rintro ⟨k, hk, rfl⟩
      simpa [mem_bruhatCoset] using hk
  rw [himage]
  exact hKcompact.image (continuous_id.add continuous_const)

/-- The characteristic function of a period coset, as a finite Bruhat function. -/
private def bruhatCosetIndicator (hKopen : IsOpen (K : Set FinAdele))
    (hKcompact : IsCompact (K : Set FinAdele)) (y : FinAdele) : FinBruhat :=
  ⟨(LocallyConstant.const FinAdele (1 : ℂ)).indicator (bruhatCoset_isClopen hKopen y), by
    classical
    apply HasCompactSupport.of_support_subset_isCompact (bruhatCoset_isCompact hKcompact y)
    intro z hz
    by_contra hmem
    apply hz
    change ((LocallyConstant.const FinAdele (1 : ℂ)).indicator
      (bruhatCoset_isClopen hKopen y)) z = 0
    rw [LocallyConstant.indicator_apply_eq_if]
    exact if_neg hmem⟩

open Classical in
private theorem bruhatCosetIndicator_apply (hKopen : IsOpen (K : Set FinAdele))
    (hKcompact : IsCompact (K : Set FinAdele)) (y z : FinAdele) :
    ((bruhatCosetIndicator hKopen hKcompact y).1 : FinAdele → ℂ) z =
      if z ∈ bruhatCoset K y then 1 else 0 :=
  LocallyConstant.indicator_apply_eq_if _ _ (bruhatCoset_isClopen hKopen y)

end Decomposition

/-! ## Bruhat's space is exactly the algebraic core -/

theorem ccmRationalAdelicBruhatSchwartz_le_range :
    CCMRationalAdelicBruhatSchwartz ≤ LinearMap.range ccmRationalAdelicBruhatEval := by
  classical
  intro φ hφ
  obtain ⟨K, hKopen, hKcompact, hKper⟩ := hφ.period
  obtain ⟨C, hC, hCsupp⟩ := hφ.support
  have hq_eq : ∀ z y : FinAdele,
      (QuotientAddGroup.mk' K) z = (QuotientAddGroup.mk' K) y ↔ z - y ∈ K := by
    intro z y
    constructor
    · intro h
      have h' : (-z + y) ∈ K := QuotientAddGroup.eq.mp h
      have : -(z - y) ∈ K := by simpa [neg_sub, sub_eq_neg_add] using h'
      simpa using (neg_mem this)
    · intro h
      refine QuotientAddGroup.eq.mpr ?_
      have : -(z - y) ∈ K := neg_mem h
      simpa [neg_sub, sub_eq_neg_add] using this
  have hq_rep : ∀ c : FinAdele ⧸ K, (QuotientAddGroup.mk' K) (Quotient.out c) = c := by
    intro c
    exact Quotient.out_eq c
  have hcover : C ⊆ ⋃ y ∈ C, bruhatCoset K y := by
    intro y hy
    exact Set.mem_biUnion hy (by simp [mem_bruhatCoset])
  obtain ⟨F, _hFC, hFfin, hFcover⟩ :=
    hC.elim_finite_subcover_image (fun y _ => bruhatCoset_isOpen hKopen y) hcover
  set classes : Finset (FinAdele ⧸ K) :=
    hFfin.toFinset.image (QuotientAddGroup.mk' K) with hclasses
  set fibreFn : FinAdele → Arch := fun y => (hφ.fibre y).choose with hfibreFn
  have hfibre : ∀ (y : FinAdele) (x : ℝ), φ (x, y) = (fibreFn y) x :=
    fun y => (hφ.fibre y).choose_spec
  refine ⟨∑ c ∈ classes, (fibreFn (Quotient.out c)) ⊗ₜ[ℂ]
      bruhatCosetIndicator hKopen hKcompact (Quotient.out c), ?_⟩
  funext p
  have hval : ccmRationalAdelicBruhatEval (∑ c ∈ classes, (fibreFn (Quotient.out c)) ⊗ₜ[ℂ]
        bruhatCosetIndicator hKopen hKcompact (Quotient.out c)) p =
      ∑ c ∈ classes, (fibreFn (Quotient.out c)) p.1 *
        ((bruhatCosetIndicator hKopen hKcompact (Quotient.out c)).1 : FinAdele → ℂ) p.2 := by
    rw [map_sum]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => rfl
  rw [hval]
  by_cases hmem : (QuotientAddGroup.mk' K) p.2 ∈ classes
  · rw [Finset.sum_eq_single ((QuotientAddGroup.mk' K) p.2)]
    · have hin : p.2 ∈ bruhatCoset K (Quotient.out ((QuotientAddGroup.mk' K) p.2)) := by
        rw [mem_bruhatCoset, ← hq_eq, hq_rep]
      rw [bruhatCosetIndicator_apply, if_pos hin, mul_one]
      have hk : p.2 - Quotient.out ((QuotientAddGroup.mk' K) p.2) ∈ K := hin
      have hshift := hKper p.1 (Quotient.out ((QuotientAddGroup.mk' K) p.2))
        (p.2 - Quotient.out ((QuotientAddGroup.mk' K) p.2)) hk
      have hsum : Quotient.out ((QuotientAddGroup.mk' K) p.2) +
          (p.2 - Quotient.out ((QuotientAddGroup.mk' K) p.2)) = p.2 := by ring
      rw [hsum] at hshift
      rw [← hfibre, hshift]
    · intro c _hc hne
      have hnot : p.2 ∉ bruhatCoset K (Quotient.out c) := by
        intro hmem2
        apply hne
        have hqq : (QuotientAddGroup.mk' K) p.2 =
            (QuotientAddGroup.mk' K) (Quotient.out c) := (hq_eq _ _).mpr hmem2
        rw [hqq, hq_rep]
      rw [bruhatCosetIndicator_apply, if_neg hnot, mul_zero]
    · intro hnot
      exact absurd hmem hnot
  · have hzero : ∀ c ∈ classes, (fibreFn (Quotient.out c)) p.1 *
        ((bruhatCosetIndicator hKopen hKcompact (Quotient.out c)).1 : FinAdele → ℂ) p.2 = 0 := by
      intro c hc
      have hnot : p.2 ∉ bruhatCoset K (Quotient.out c) := by
        intro hmem2
        apply hmem
        have hqq : (QuotientAddGroup.mk' K) p.2 =
            (QuotientAddGroup.mk' K) (Quotient.out c) := (hq_eq _ _).mpr hmem2
        rw [hqq, hq_rep]
        exact hc
      rw [bruhatCosetIndicator_apply, if_neg hnot, mul_zero]
    rw [Finset.sum_eq_zero hzero]
    have hnotC : p.2 ∉ C := by
      intro hinC
      obtain ⟨y, hyF, hy⟩ := Set.mem_iUnion₂.mp (hFcover hinC)
      apply hmem
      have hqq : (QuotientAddGroup.mk' K) p.2 = (QuotientAddGroup.mk' K) y :=
        (hq_eq _ _).mpr hy
      rw [hclasses, Finset.mem_image]
      exact ⟨y, hFfin.mem_toFinset.mpr hyF, hqq.symm⟩
    exact (hCsupp p.1 p.2 hnotC).symm

/-- **Bruhat's Schwartz space of the rational adeles is the algebraic tensor core.**  The canonical
realization of `𝒮(ℝ) ⊗ C_c^∞(𝔸_f)` as functions on `ℝ × 𝔸_f` has range exactly Bruhat's space:
no completion is needed. -/
theorem range_ccmRationalAdelicBruhatEval_eq :
    LinearMap.range ccmRationalAdelicBruhatEval = CCMRationalAdelicBruhatSchwartz :=
  le_antisymm range_ccmRationalAdelicBruhatEval_le ccmRationalAdelicBruhatSchwartz_le_range

theorem mem_range_ccmRationalAdelicBruhatEval_iff (φ : CCMRationalAdele → ℂ) :
    φ ∈ LinearMap.range ccmRationalAdelicBruhatEval ↔
      IsCCMRationalAdelicBruhatSchwartz φ := by
  rw [range_ccmRationalAdelicBruhatEval_eq]
  exact Iff.rfl

/-! ## The algebraic Real structure is the pointwise sign reflection -/

/-- **The core involution realizes as Bruhat's involution.**  The algebraic sign-reflection of the
adelic Bruhat core is, as a function on `ℝ × 𝔸_f`, exactly `φ ↦ conj (φ ∘ (-1))`. -/
theorem ccmRationalAdelicBruhatEval_sigma (t : Core) (p : CCMRationalAdele) :
    ccmRationalAdelicBruhatEval (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma t) p =
      star (ccmRationalAdelicBruhatEval t (-p.1, -p.2)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [ccmRationalAdelicBruhatSimpleTensor_sigma_tmul, ccmRationalAdelicBruhatEval_tmul,
        ccmRationalAdelicBruhatEval_tmul, ccmRationalArchimedeanSchwartzReflection_apply,
        ccmRationalFiniteBruhatReflection_apply, star_mul']
  | add s t hs ht =>
      simp only [map_add, Pi.add_apply, star_add, hs, ht]

/-! ## Faithfulness of the realization -/

private noncomputable def bruhatFinBasis :
    Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ FinBruhat) ℂ FinBruhat :=
  Module.Basis.ofVectorSpace ℂ FinBruhat

private noncomputable def bruhatCoreEquivFinsupp :
    Core ≃ₗ[ℂ] ((Module.Basis.ofVectorSpaceIndex ℂ FinBruhat) →₀ Arch) := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl ℂ Arch) bruhatFinBasis.repr).trans
    (TensorProduct.finsuppScalarRight ℂ ℂ Arch _)

private theorem bruhatCoreEquivFinsupp_symm_apply
    (w : (Module.Basis.ofVectorSpaceIndex ℂ FinBruhat) →₀ Arch) :
    bruhatCoreEquivFinsupp.symm w = w.sum fun i a => a ⊗ₜ[ℂ] bruhatFinBasis i := by
  classical
  induction w using Finsupp.induction with
  | zero => simp [bruhatCoreEquivFinsupp]
  | single_add i a w hi ha hw =>
      rw [map_add, hw, Finsupp.sum_add_index' (by simp) (by intros; rw [TensorProduct.add_tmul])]
      congr 1
      · rw [Finsupp.sum_single_index (by simp)]
        show (TensorProduct.congr (LinearEquiv.refl ℂ Arch) bruhatFinBasis.repr).symm
            ((TensorProduct.finsuppScalarRight ℂ ℂ Arch _).symm (Finsupp.single i a)) = _
        rw [TensorProduct.finsuppScalarRight_symm_apply_single]
        simp [TensorProduct.congr_symm_tmul, bruhatFinBasis]

theorem ccmRationalAdelicBruhatEval_injective :
    Function.Injective ccmRationalAdelicBruhatEval := by
  classical
  rw [injective_iff_map_eq_zero]
  intro t ht
  set w := bruhatCoreEquivFinsupp t with hw
  have hrepr : t = w.sum fun i a => a ⊗ₜ[ℂ] bruhatFinBasis i := by
    rw [← bruhatCoreEquivFinsupp_symm_apply, hw, LinearEquiv.symm_apply_apply]
  have hfun : ∀ (x : ℝ) (y : FinAdele),
      ∑ i ∈ w.support, (w i) x * ((bruhatFinBasis i).1 : FinAdele → ℂ) y = 0 := by
    intro x y
    have hpt := congrFun ht (x, y)
    rw [hrepr] at hpt
    rw [Finsupp.sum] at hpt
    rw [map_sum] at hpt
    simpa using hpt
  have hcoeff : ∀ i ∈ w.support, w i = 0 := by
    intro i hi
    ext x
    have hzero : ∑ j ∈ w.support, ((w j) x) • (bruhatFinBasis j) = 0 := by
      apply Subtype.ext
      apply LocallyConstant.ext
      intro y
      have hcoe : (((∑ j ∈ w.support, ((w j) x) • (bruhatFinBasis j) : FinBruhat)).1 :
          FinAdele → ℂ) y =
          ∑ j ∈ w.support, (w j) x * ((bruhatFinBasis j).1 : FinAdele → ℂ) y := by
        induction w.support using Finset.induction_on with
        | empty => simp
        | insert a s ha hind =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            simp only [Submodule.coe_add, LocallyConstant.coe_add, Pi.add_apply,
              Submodule.coe_smul, LocallyConstant.coe_smul, Pi.smul_apply, smul_eq_mul]
            rw [hind]
      rw [hcoe, hfun x y]
      rfl
    have hind := bruhatFinBasis.linearIndependent
    rw [linearIndependent_iff'] at hind
    exact hind w.support (fun j => (w j) x) hzero i hi
  have hwzero : w = 0 := by
    ext i a
    by_cases hi : i ∈ w.support
    · rw [hcoeff i hi]
      simp
    · simp [Finsupp.notMem_support_iff.mp hi]
  have : t = 0 := by
    rw [hrepr, hwzero]
    simp
  exact this

/-- **The adelic Bruhat--Schwartz space is the algebraic tensor core.**  Realization is a linear
isomorphism of `𝒮(ℝ) ⊗ C_c^∞(𝔸_f)` onto Bruhat's space of `ℝ × 𝔸_f`. -/
noncomputable def ccmRationalAdelicBruhatEquiv :
    Core ≃ₗ[ℂ] CCMRationalAdelicBruhatSchwartz :=
  (LinearEquiv.ofInjective ccmRationalAdelicBruhatEval
      ccmRationalAdelicBruhatEval_injective).trans
    (LinearEquiv.ofEq _ _ range_ccmRationalAdelicBruhatEval_eq)

@[simp]
theorem ccmRationalAdelicBruhatEquiv_coe (t : Core) :
    ((ccmRationalAdelicBruhatEquiv t : CCMRationalAdelicBruhatSchwartz) :
      CCMRationalAdele → ℂ) = ccmRationalAdelicBruhatEval t := rfl

end RHTower
end GaloisForLFunctions
