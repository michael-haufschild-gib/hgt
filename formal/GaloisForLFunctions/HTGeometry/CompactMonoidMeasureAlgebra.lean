import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# The measure algebra of a compact commutative monoid

Let `K` be a compact commutative topological monoid.  Its measure algebra `M(K)` is the space of
complex Radon measures on `K` with the total-variation norm and the convolution product
`(μ ⋆ ν)(f) = ∫∫ f(xy) dμ(x) dν(y)`.  By the Riesz representation theorem a complex Radon measure
is the same as a continuous linear functional on `C(K, ℂ)`, with total variation equal to the dual
norm; we realize `M(K)` this way, as `StrongDual ℂ C(K, ℂ)` with the product
`(Φ ⋆ Ψ)(f) = Φ (x ↦ Ψ (y ↦ f (x y)))`.

* Associativity and the unit `δ₁` are formal consequences of the monoid laws.
* Commutativity is a Fubini theorem for functionals: the two iterated functionals on
  `C(K × K, ℂ)` agree on the products `a(x) b(y)`, whose span is dense by Stone–Weierstrass.
* `‖Φ ⋆ Ψ‖ ≤ ‖Φ‖ ‖Ψ‖` and `‖δ₁‖ = 1`, so `M(K)` is a commutative unital Banach algebra.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

section Defs

variable (K : Type*) [TopologicalSpace K]

/-- The measure algebra `M(K)`: complex Radon measures on `K`, realized as continuous linear
functionals on `C(K, ℂ)` with the dual (total-variation) norm. -/
def MeasureAlgebra : Type _ := StrongDual ℂ C(K, ℂ)

namespace MeasureAlgebra

instance : FunLike (MeasureAlgebra K) C(K, ℂ) ℂ :=
  inferInstanceAs (FunLike (StrongDual ℂ C(K, ℂ)) C(K, ℂ) ℂ)

instance : ContinuousLinearMapClass (MeasureAlgebra K) ℂ C(K, ℂ) ℂ :=
  inferInstanceAs (ContinuousLinearMapClass (StrongDual ℂ C(K, ℂ)) ℂ C(K, ℂ) ℂ)

variable {K}

/-- The underlying functional. -/
def toDual (Φ : MeasureAlgebra K) : StrongDual ℂ C(K, ℂ) := Φ

/-- A functional, viewed as an element of the measure algebra. -/
def ofDual (Λ : StrongDual ℂ C(K, ℂ)) : MeasureAlgebra K := Λ

@[simp] theorem toDual_apply (Φ : MeasureAlgebra K) (f : C(K, ℂ)) : toDual Φ f = Φ f := rfl

@[simp] theorem ofDual_apply (Λ : StrongDual ℂ C(K, ℂ)) (f : C(K, ℂ)) : ofDual Λ f = Λ f := rfl

@[ext] theorem ext {Φ Ψ : MeasureAlgebra K} (h : ∀ f, Φ f = Ψ f) : Φ = Ψ :=
  ContinuousLinearMap.ext h

/-- The product function `a(x) b(y)` on `K × K`. -/
def tensorFun (a b : C(K, ℂ)) : C(K × K, ℂ) :=
  ⟨fun p => a p.1 * b p.2, by fun_prop⟩

@[simp] theorem tensorFun_apply (a b : C(K, ℂ)) (p : K × K) : tensorFun a b p = a p.1 * b p.2 :=
  rfl

/-- The product functions. -/
def tensorSet : Set C(K × K, ℂ) := {g | ∃ a b : C(K, ℂ), g = tensorFun a b}

theorem tensorSet_mul {g h : C(K × K, ℂ)} (hg : g ∈ tensorSet) (hh : h ∈ tensorSet) :
    g * h ∈ tensorSet := by
  obtain ⟨a, b, rfl⟩ := hg
  obtain ⟨c, d, rfl⟩ := hh
  exact ⟨a * c, b * d, by ext p; simp; ring⟩

theorem span_tensorSet_mul {g h : C(K × K, ℂ)} (hg : g ∈ Submodule.span ℂ (tensorSet (K := K)))
    (hh : h ∈ Submodule.span ℂ (tensorSet (K := K))) :
    g * h ∈ Submodule.span ℂ (tensorSet (K := K)) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    induction hh using Submodule.span_induction with
    | mem h hh => exact Submodule.subset_span (tensorSet_mul hg hh)
    | zero => simp
    | add h₁ h₂ _ _ ih₁ ih₂ => rw [mul_add]; exact add_mem ih₁ ih₂
    | smul c h _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih
  | zero => simp
  | add g₁ g₂ _ _ ih₁ ih₂ => rw [add_mul]; exact add_mem ih₁ ih₂
  | smul c g _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih

theorem span_tensorSet_star {g : C(K × K, ℂ)} (hg : g ∈ Submodule.span ℂ (tensorSet (K := K))) :
    star g ∈ Submodule.span ℂ (tensorSet (K := K)) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, b, rfl⟩ := hg
    exact Submodule.subset_span ⟨star a, star b, by ext p; simp⟩
  | zero => simp
  | add g₁ g₂ _ _ ih₁ ih₂ => rw [star_add]; exact add_mem ih₁ ih₂
  | smul c g _ ih => rw [star_smul]; exact Submodule.smul_mem _ _ ih

/-- The star subalgebra spanned by the product functions. -/
def tensorSubalgebra : StarSubalgebra ℂ C(K × K, ℂ) where
  carrier := Submodule.span ℂ (tensorSet (K := K))
  mul_mem' := span_tensorSet_mul
  add_mem' := add_mem
  algebraMap_mem' c := by
    have h1 : (1 : C(K × K, ℂ)) ∈ tensorSet := ⟨1, 1, by ext p; simp⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span h1)
  star_mem' := span_tensorSet_star

end MeasureAlgebra

end Defs

section Normed

variable (K : Type*) [TopologicalSpace K] [CompactSpace K]

namespace MeasureAlgebra

instance : NormedAddCommGroup (MeasureAlgebra K) :=
  inferInstanceAs (NormedAddCommGroup (StrongDual ℂ C(K, ℂ)))

instance : NormedSpace ℂ (MeasureAlgebra K) :=
  inferInstanceAs (NormedSpace ℂ (StrongDual ℂ C(K, ℂ)))

instance : CompleteSpace (MeasureAlgebra K) :=
  inferInstanceAs (CompleteSpace (StrongDual ℂ C(K, ℂ)))

variable {K}

@[simp] theorem norm_toDual (Φ : MeasureAlgebra K) : ‖toDual Φ‖ = ‖Φ‖ := rfl

@[simp] theorem norm_ofDual (Λ : StrongDual ℂ C(K, ℂ)) : ‖ofDual Λ‖ = ‖Λ‖ := rfl

@[simp] theorem add_apply (Φ Ψ : MeasureAlgebra K) (f : C(K, ℂ)) : (Φ + Ψ) f = Φ f + Ψ f := rfl

@[simp] theorem sub_apply (Φ Ψ : MeasureAlgebra K) (f : C(K, ℂ)) : (Φ - Ψ) f = Φ f - Ψ f := rfl

@[simp] theorem neg_apply (Φ : MeasureAlgebra K) (f : C(K, ℂ)) : (-Φ) f = -Φ f := rfl

@[simp] theorem zero_apply (f : C(K, ℂ)) : (0 : MeasureAlgebra K) f = 0 := rfl

@[simp] theorem smul_apply (c : ℂ) (Φ : MeasureAlgebra K) (f : C(K, ℂ)) : (c • Φ) f = c * Φ f :=
  rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (Φ : ι → MeasureAlgebra K) (f : C(K, ℂ)) :
    (∑ i ∈ s, Φ i) f = ∑ i ∈ s, Φ i f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_apply, ih]

theorem le_opNorm (Φ : MeasureAlgebra K) (f : C(K, ℂ)) : ‖Φ f‖ ≤ ‖Φ‖ * ‖f‖ :=
  ContinuousLinearMap.le_opNorm (toDual Φ) f

theorem opNorm_le_bound (Φ : MeasureAlgebra K) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ f, ‖Φ f‖ ≤ M * ‖f‖) : ‖Φ‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound (toDual Φ) hM h

theorem norm_curry_le (g : C(K × K, ℂ)) (x : K) : ‖g.curry x‖ ≤ ‖g‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun _ => g.norm_coe_le_norm _

/-- The partial functional `g ↦ (x ↦ Ψ (g (x, ·)))` on `C(K × K, ℂ)`. -/
def partialRight (Ψ : MeasureAlgebra K) : C(K × K, ℂ) →L[ℂ] C(K, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun g => ⟨fun x => Ψ (g.curry x), (map_continuous Ψ).comp g.curry.continuous⟩
      map_add' := fun g h => by
        ext x
        change Ψ ((g + h).curry x) = Ψ (g.curry x) + Ψ (h.curry x)
        rw [← map_add]
        rfl
      map_smul' := fun c g => by
        ext x
        change Ψ ((c • g).curry x) = c * Ψ (g.curry x)
        rw [← smul_eq_mul, ← map_smul]
        rfl }
    ‖Ψ‖ fun g => (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
      (le_opNorm Ψ _).trans (mul_le_mul_of_nonneg_left (norm_curry_le g x) (norm_nonneg _))

@[simp] theorem partialRight_apply (Ψ : MeasureAlgebra K) (g : C(K × K, ℂ)) (x : K) :
    partialRight Ψ g x = Ψ (g.curry x) := rfl

theorem norm_partialRight_le (Ψ : MeasureAlgebra K) : ‖partialRight Ψ‖ ≤ ‖Ψ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- The coordinate swap on `C(K × K, ℂ)`. -/
def swapCLM : C(K × K, ℂ) →L[ℂ] C(K × K, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun g => g.comp ⟨Prod.swap, continuous_swap⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun g => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun p => g.norm_coe_le_norm _

@[simp] theorem swapCLM_apply (g : C(K × K, ℂ)) (p : K × K) : swapCLM g p = g p.swap := rfl

section Fubini

variable [T2Space K]

/-- Continuous functions separate the points of a compact Hausdorff space. -/
theorem exists_continuousMap_ne {x y : K} (hxy : x ≠ y) : ∃ a : C(K, ℂ), a x ≠ a y := by
  obtain ⟨f, hfx, hfy, -⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := x))
    (isClosed_singleton (x := y)) (Set.disjoint_singleton.2 hxy)
  refine ⟨⟨fun z => (f z : ℂ), by fun_prop⟩, ?_⟩
  simp only [ContinuousMap.coe_mk, hfx (Set.mem_singleton x), hfy (Set.mem_singleton y),
    Pi.zero_apply, Pi.one_apply, ne_eq]
  norm_num

theorem tensorSubalgebra_separatesPoints : (tensorSubalgebra (K := K)).SeparatesPoints := by
  intro p q hpq
  by_cases h : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
    obtain ⟨b, hb⟩ := exists_continuousMap_ne h2
    refine ⟨tensorFun 1 b, ⟨tensorFun 1 b, Submodule.subset_span ⟨1, b, rfl⟩, rfl⟩, ?_⟩
    simpa using hb
  · obtain ⟨a, ha⟩ := exists_continuousMap_ne h
    refine ⟨tensorFun a 1, ⟨tensorFun a 1, Submodule.subset_span ⟨a, 1, rfl⟩, rfl⟩, ?_⟩
    simpa using ha

theorem dense_span_tensorSet :
    Dense (Submodule.span ℂ (tensorSet (K := K)) : Set C(K × K, ℂ)) := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (tensorSubalgebra_separatesPoints (K := K))
  have h' := congrArg (fun A : StarSubalgebra ℂ C(K × K, ℂ) => (A : Set C(K × K, ℂ))) h
  simp only [StarSubalgebra.topologicalClosure_coe, StarSubalgebra.coe_top] at h'
  exact dense_iff_closure_eq.2 h'

/-- **Fubini for functionals.**  For `Φ, Ψ ∈ M(K)` and `g ∈ C(K × K, ℂ)`,
`Φ (x ↦ Ψ (g (x, ·))) = Ψ (y ↦ Φ (g (·, y)))`. -/
theorem fubini (Φ Ψ : MeasureAlgebra K) (g : C(K × K, ℂ)) :
    Φ (partialRight Ψ g) = Ψ (partialRight Φ (swapCLM g)) := by
  have key : (toDual Φ).comp (partialRight Ψ) =
      ((toDual Ψ).comp (partialRight Φ)).comp swapCLM := by
    refine ContinuousLinearMap.ext_on dense_span_tensorSet ?_
    rintro _ ⟨a, b, rfl⟩
    have h1 : partialRight Ψ (tensorFun a b) = Ψ b • a := by
      ext x
      change Ψ ((tensorFun a b).curry x) = Ψ b * a x
      have : (tensorFun a b).curry x = a x • b := by ext y; simp
      rw [this, map_smul, smul_eq_mul, mul_comm]
    have h2 : partialRight Φ (swapCLM (tensorFun a b)) = Φ a • b := by
      ext y
      change Φ ((swapCLM (tensorFun a b)).curry y) = Φ a * b y
      have : (swapCLM (tensorFun a b)).curry y = b y • a := by ext x; simp [mul_comm]
      rw [this, map_smul, smul_eq_mul, mul_comm]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, toDual_apply, h1, h2,
      map_smul, smul_eq_mul]
    ring
  exact congrArg (fun L : C(K × K, ℂ) →L[ℂ] ℂ => L g) key

end Fubini

/-! ## The convolution product -/

section Product

variable [CommMonoid K] [ContinuousMul K]

/-- The multiplication map `K × K → K`. -/
def mulMap : C(K × K, K) := ⟨fun p => p.1 * p.2, continuous_mul⟩

/-- The translates `x ↦ (y ↦ f (x y))`, as a continuous map into `C(K, ℂ)`. -/
def shift (f : C(K, ℂ)) : C(K, C(K, ℂ)) := (f.comp mulMap).curry

omit [CompactSpace K] in
@[simp] theorem shift_apply (f : C(K, ℂ)) (x y : K) : shift f x y = f (x * y) := rfl

/-- Pullback along the multiplication, `f ↦ f (x y)`. -/
def compMulCLM : C(K, ℂ) →L[ℂ] C(K × K, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp mulMap
      map_add' := fun f g => ContinuousMap.add_comp f g mulMap
      map_smul' := fun c f => ContinuousMap.smul_comp c f mulMap }
    1 fun f => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun p => f.norm_coe_le_norm _

/-- The right transform `(T_Ψ f)(x) = Ψ (y ↦ f (x y))`. -/
def rightTransform (Ψ : MeasureAlgebra K) : C(K, ℂ) →L[ℂ] C(K, ℂ) :=
  (partialRight Ψ).comp compMulCLM

@[simp] theorem rightTransform_apply (Ψ : MeasureAlgebra K) (f : C(K, ℂ)) (x : K) :
    rightTransform Ψ f x = Ψ (shift f x) := rfl

theorem norm_rightTransform_le (Ψ : MeasureAlgebra K) : ‖rightTransform Ψ‖ ≤ ‖Ψ‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖partialRight Ψ‖ * ‖_‖ ≤ ‖Ψ‖ * 1 := by
        gcongr
        · exact norm_partialRight_le Ψ
        · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
    _ = ‖Ψ‖ := mul_one _

instance : Mul (MeasureAlgebra K) := ⟨fun Φ Ψ => ofDual ((toDual Φ).comp (rightTransform Ψ))⟩

/-- The unit `δ₁`: evaluation at the identity. -/
instance : One (MeasureAlgebra K) := ⟨ofDual (ContinuousMap.evalCLM ℂ 1)⟩

theorem mul_apply (Φ Ψ : MeasureAlgebra K) (f : C(K, ℂ)) : (Φ * Ψ) f = Φ (rightTransform Ψ f) :=
  rfl

omit [CompactSpace K] [ContinuousMul K] in
@[simp] theorem one_apply (f : C(K, ℂ)) : (1 : MeasureAlgebra K) f = f 1 := rfl

theorem rightTransform_add (Ψ₁ Ψ₂ : MeasureAlgebra K) (f : C(K, ℂ)) :
    rightTransform (Ψ₁ + Ψ₂) f = rightTransform Ψ₁ f + rightTransform Ψ₂ f := by
  ext x; rfl

theorem rightTransform_smul (c : ℂ) (Ψ : MeasureAlgebra K) (f : C(K, ℂ)) :
    rightTransform (c • Ψ) f = c • rightTransform Ψ f := by
  ext x; rfl

theorem rightTransform_zero (f : C(K, ℂ)) : rightTransform (0 : MeasureAlgebra K) f = 0 := by
  ext x; rfl

theorem rightTransform_one (f : C(K, ℂ)) : rightTransform (1 : MeasureAlgebra K) f = f := by
  ext x; simp

theorem rightTransform_mul (Ψ Ρ : MeasureAlgebra K) (f : C(K, ℂ)) :
    rightTransform (Ψ * Ρ) f = rightTransform Ψ (rightTransform Ρ f) := by
  ext x
  change Ψ (rightTransform Ρ (shift f x)) = Ψ (shift (rightTransform Ρ f) x)
  congr 1
  ext y
  change Ρ (shift (shift f x) y) = Ρ (shift f (x * y))
  congr 1
  ext z
  simp [mul_assoc]

theorem mul_assoc' (Φ Ψ Ρ : MeasureAlgebra K) : Φ * Ψ * Ρ = Φ * (Ψ * Ρ) := by
  ext f
  rw [mul_apply, mul_apply, mul_apply, rightTransform_mul]

theorem one_mul' (Ψ : MeasureAlgebra K) : 1 * Ψ = Ψ := by
  ext f
  rw [mul_apply, one_apply, rightTransform_apply]
  congr 1
  ext y
  simp

theorem mul_one' (Φ : MeasureAlgebra K) : Φ * 1 = Φ := by
  ext f
  rw [mul_apply, rightTransform_one]

theorem norm_mul_le' (Φ Ψ : MeasureAlgebra K) : ‖Φ * Ψ‖ ≤ ‖Φ‖ * ‖Ψ‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_rightTransform_le Ψ) (norm_nonneg _)

variable [T2Space K]

theorem mul_comm' (Φ Ψ : MeasureAlgebra K) : Φ * Ψ = Ψ * Φ := by
  ext f
  have h1 : rightTransform Ψ f = partialRight Ψ (f.comp mulMap) := rfl
  have h2 : rightTransform Φ f = partialRight Φ (swapCLM (f.comp mulMap)) := by
    ext y
    change Φ (shift f y) = Φ ((swapCLM (f.comp mulMap)).curry y)
    congr 1
    ext x
    simp [mulMap, mul_comm]
  rw [mul_apply, mul_apply, h1, h2, fubini]

instance : CommRing (MeasureAlgebra K) :=
  { (inferInstance : AddCommGroup (MeasureAlgebra K)) with
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one'
    left_distrib := fun Φ Ψ₁ Ψ₂ => by
      ext f
      rw [mul_apply, rightTransform_add, map_add]
      rfl
    right_distrib := fun Φ₁ Φ₂ Ψ => by ext f; rfl
    zero_mul := fun Ψ => by ext f; rfl
    mul_zero := fun Φ => by
      ext f
      rw [mul_apply, rightTransform_zero, map_zero]
      rfl
    mul_comm := mul_comm' }

instance : NormedCommRing (MeasureAlgebra K) :=
  { (inferInstance : NormedAddCommGroup (MeasureAlgebra K)),
    (inferInstance : CommRing (MeasureAlgebra K)) with
    norm_mul_le := norm_mul_le' }

instance : Algebra ℂ (MeasureAlgebra K) :=
  Algebra.ofModule (fun c Φ Ψ => by ext f; rfl)
    (fun c Φ Ψ => by
      ext f
      rw [mul_apply, rightTransform_smul, map_smul]
      rfl)

instance : NormedAlgebra ℂ (MeasureAlgebra K) :=
  { (inferInstance : Algebra ℂ (MeasureAlgebra K)) with
    norm_smul_le := norm_smul_le }

instance : NormOneClass (MeasureAlgebra K) := by
  refine ⟨le_antisymm ?_ ?_⟩
  · refine opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_apply, one_mul]
    exact f.norm_coe_le_norm 1
  · have h := le_opNorm (1 : MeasureAlgebra K) 1
    simpa using h

theorem algebraMap_apply' (c : ℂ) (f : C(K, ℂ)) : algebraMap ℂ (MeasureAlgebra K) c f = c * f 1 :=
  rfl

end Product

end MeasureAlgebra

end Normed

/-! ## Positive functionals and finite positive measures -/

section Measures

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

namespace MeasureAlgebra

/-- The real-valued continuous functions inside `C(K, ℂ)`. -/
def realToComplex (f : C(K, ℝ)) : C(K, ℂ) := ⟨fun x => (f x : ℂ), by fun_prop⟩

omit [CompactSpace K] in
@[simp] theorem realToComplex_apply (f : C(K, ℝ)) (x : K) : realToComplex f x = f x := rfl

omit [CompactSpace K] in
theorem realToComplex_add (f g : C(K, ℝ)) :
    realToComplex (f + g) = realToComplex f + realToComplex g := by
  ext x; simp

omit [CompactSpace K] in
theorem realToComplex_smul (c : ℝ) (f : C(K, ℝ)) :
    realToComplex (c • f) = (c : ℂ) • realToComplex f := by
  ext x; simp

/-- A functional is positive when it is real and nonnegative on nonnegative real functions. -/
def IsPositive (Φ : MeasureAlgebra K) : Prop :=
  ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → (Φ (realToComplex f)).im = 0 ∧ 0 ≤ (Φ (realToComplex f)).re

theorem IsPositive.im_eq_zero {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) (f : C(K, ℝ)) :
    (Φ (realToComplex f)).im = 0 := by
  set c : C(K, ℝ) := ContinuousMap.const K ‖f‖
  have hc : ∀ x, 0 ≤ c x := fun x => by
    simp only [c, ContinuousMap.const_apply]
    exact norm_nonneg _
  have hfc : ∀ x, 0 ≤ (f + c) x := fun x => by
    have := neg_abs_le (f x)
    have h2 : |f x| ≤ ‖f‖ := by
      have := f.norm_coe_le_norm x
      rwa [Real.norm_eq_abs] at this
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, c]
    linarith
  have h1 := (hΦ _ hfc).1
  have h2 := (hΦ _ hc).1
  rw [realToComplex_add, map_add, Complex.add_im, h2, add_zero] at h1
  exact h1

theorem IsPositive.apply_realToComplex {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ)
    (f : C(K, ℝ)) : Φ (realToComplex f) = ((Φ (realToComplex f)).re : ℂ) :=
  Complex.ext rfl (by simp [hΦ.im_eq_zero f])

theorem IsPositive.add {Φ Ψ : MeasureAlgebra K} (hΦ : IsPositive Φ) (hΨ : IsPositive Ψ) :
    IsPositive (Φ + Ψ) := fun f hf => by
  rw [add_apply, Complex.add_im, Complex.add_re]
  exact ⟨by rw [(hΦ f hf).1, (hΨ f hf).1, add_zero], add_nonneg (hΦ f hf).2 (hΨ f hf).2⟩

theorem isPositive_zero : IsPositive (0 : MeasureAlgebra K) := fun f _ => by simp

variable [MeasurableSpace K] [BorelSpace K]

omit [TopologicalSpace K] [CompactSpace K] [BorelSpace K] in
theorem mass_eq_real (μ : FiniteMeasure K) : (μ.mass : ℝ) = (μ : Measure K).real Set.univ := by
  simp only [FiniteMeasure.mass, FiniteMeasure.coeFn_def, Measure.real]
  exact ENNReal.coe_toNNReal_eq_toReal _

theorem integrable_continuousMap (f : C(K, ℂ)) (μ : FiniteMeasure K) :
    Integrable f (μ : Measure K) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable (μ : Measure K)

omit [BorelSpace K] in
theorem norm_integral_continuousMap_le (μ : FiniteMeasure K) (f : C(K, ℂ)) :
    ‖∫ x, f x ∂(μ : Measure K)‖ ≤ (μ.mass : ℝ) * ‖f‖ := by
  rw [mass_eq_real, mul_comm]
  exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => f.norm_coe_le_norm x)

/-- Integration against a finite positive Borel measure, as an element of `M(K)`. -/
def ofMeasure (μ : FiniteMeasure K) : MeasureAlgebra K :=
  ofDual <| LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂(μ : Measure K)
      map_add' := fun f g =>
        integral_add (integrable_continuousMap f μ) (integrable_continuousMap g μ)
      map_smul' := fun c f => integral_smul c f }
    (μ.mass : ℝ) (norm_integral_continuousMap_le μ)

theorem ofMeasure_apply (μ : FiniteMeasure K) (f : C(K, ℂ)) :
    ofMeasure μ f = ∫ x, f x ∂(μ : Measure K) := rfl

theorem ofMeasure_realToComplex (μ : FiniteMeasure K) (f : C(K, ℝ)) :
    ofMeasure μ (realToComplex f) = ((∫ x, f x ∂(μ : Measure K) : ℝ) : ℂ) := by
  rw [ofMeasure_apply]
  exact integral_ofReal

theorem norm_ofMeasure_le (μ : FiniteMeasure K) : ‖ofMeasure μ‖ ≤ μ.mass :=
  opNorm_le_bound _ (NNReal.coe_nonneg _) (norm_integral_continuousMap_le μ)

theorem norm_ofMeasure [Nonempty K] (μ : FiniteMeasure K) : ‖ofMeasure μ‖ = μ.mass := by
  refine le_antisymm (norm_ofMeasure_le μ) ?_
  have h := le_opNorm (ofMeasure μ) 1
  have h1 : ofMeasure μ 1 = ((μ.mass : ℝ) : ℂ) := by
    rw [ofMeasure_apply, mass_eq_real]
    simp
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] at h
  have h1' : ‖(1 : C(K, ℂ))‖ = 1 := norm_one
  rw [h1', mul_one] at h
  exact h

@[simp] theorem ofMeasure_zero : ofMeasure (0 : FiniteMeasure K) = 0 := by
  ext f; simp [ofMeasure_apply]

theorem ofMeasure_add (μ ν : FiniteMeasure K) :
    ofMeasure (μ + ν) = ofMeasure μ + ofMeasure ν := by
  ext f
  rw [ofMeasure_apply, add_apply, ofMeasure_apply, ofMeasure_apply, FiniteMeasure.toMeasure_add]
  exact integral_add_measure (integrable_continuousMap f μ) (integrable_continuousMap f ν)

theorem ofMeasure_smul (c : NNReal) (μ : FiniteMeasure K) :
    ofMeasure (c • μ) = (c : ℂ) • ofMeasure μ := by
  ext f
  rw [ofMeasure_apply, smul_apply, ofMeasure_apply, FiniteMeasure.toMeasure_smul]
  rw [integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

theorem ofMeasure_sum {ι : Type*} (s : Finset ι) (μ : ι → FiniteMeasure K) :
    ofMeasure (∑ i ∈ s, μ i) = ∑ i ∈ s, ofMeasure (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ofMeasure_add, ih]

theorem isPositive_ofMeasure (μ : FiniteMeasure K) : IsPositive (ofMeasure μ) := by
  intro f hf
  rw [ofMeasure_realToComplex, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, integral_nonneg hf⟩

/-- The Dirac mass at a point, as a finite measure. -/
def diracMeasure (x : K) : FiniteMeasure K := ⟨Measure.dirac x, inferInstance⟩

variable [T2Space K]

theorem ofMeasure_diracMeasure (x : K) (f : C(K, ℂ)) :
    ofMeasure (diracMeasure x) f = f x := by
  rw [ofMeasure_apply]
  exact integral_dirac _ x

/-- The positive linear functional on `C_c(K, ℝ) = C(K, ℝ)` induced by a positive `Φ`. -/
def positivePart {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) :
    CompactlySupportedContinuousMap K ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun g => (Φ (realToComplex
        (CompactlySupportedContinuousMap.continuousMapEquiv.symm g))).re
      map_add' := fun g h => by
        have : CompactlySupportedContinuousMap.continuousMapEquiv.symm (g + h) =
            CompactlySupportedContinuousMap.continuousMapEquiv.symm g +
              CompactlySupportedContinuousMap.continuousMapEquiv.symm h := rfl
        rw [this, realToComplex_add, map_add, Complex.add_re]
      map_smul' := fun c g => by
        have : CompactlySupportedContinuousMap.continuousMapEquiv.symm (c • g) =
            c • CompactlySupportedContinuousMap.continuousMapEquiv.symm g := rfl
        rw [this, realToComplex_smul, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]
        simp [hΦ.im_eq_zero] }
    fun g hg => (hΦ _ fun x => hg x).2

/-- **Riesz–Markov–Kakutani.**  Every positive element of `M(K)` is integration against a finite
positive Borel measure. -/
theorem IsPositive.exists_ofMeasure_eq {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ) :
    ∃ μ : FiniteMeasure K, ofMeasure μ = Φ := by
  set ρ := RealRMK.rieszMeasure (positivePart hΦ)
  refine ⟨⟨ρ, inferInstance⟩, ?_⟩
  have hreal : ∀ g : C(K, ℝ), ∫ x, g x ∂ρ = (Φ (realToComplex g)).re := fun g =>
    RealRMK.integral_rieszMeasure (positivePart hΦ)
      (CompactlySupportedContinuousMap.continuousMapEquiv g)
  ext f
  set fr : C(K, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
  set fi : C(K, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
  have hf : f = realToComplex fr + Complex.I • realToComplex fi := by
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, realToComplex_apply,
      ContinuousMap.coe_mk, smul_eq_mul, fr, fi]
    rw [mul_comm, Complex.re_add_im]
  rw [ofMeasure_apply, ← integral_re_add_im (integrable_continuousMap f ⟨ρ, inferInstance⟩)]
  change ((∫ x, fr x ∂ρ : ℝ) : ℂ) + ((∫ x, fi x ∂ρ : ℝ) : ℂ) * Complex.I = Φ f
  rw [hreal, hreal, hf, map_add, map_smul, smul_eq_mul, hΦ.apply_realToComplex fr,
    hΦ.apply_realToComplex fi]
  simp only [Complex.ofReal_re]
  ring

variable [SecondCountableTopology K]

theorem ofMeasure_injective : Function.Injective (ofMeasure (K := K)) := by
  intro μ ν h
  refine FiniteMeasure.ext_of_forall_integral_eq fun f => ?_
  have h1 := congrArg (fun Φ : MeasureAlgebra K => Φ (realToComplex f.toContinuousMap)) h
  simp only [ofMeasure_realToComplex] at h1
  exact_mod_cast h1

/-! ### Convolution of finite measures -/

section Convolution

variable [CommMonoid K] [ContinuousMul K]

/-- The convolution `μ ⋆ ν` of finite measures on `K` (`Measure.mconv`). -/
def measureConv (μ ν : FiniteMeasure K) : FiniteMeasure K :=
  ⟨(μ : Measure K) ∗ₘ (ν : Measure K), by
    unfold Measure.mconv
    infer_instance⟩

omit [T2Space K] in
theorem ofMeasure_measureConv (μ ν : FiniteMeasure K) :
    ofMeasure (measureConv μ ν) = ofMeasure μ * ofMeasure ν := by
  ext f
  have hmul : Measurable fun p : K × K => p.1 * p.2 := measurable_mul
  have hint : Integrable (fun p : K × K => f (p.1 * p.2))
      ((μ : Measure K).prod (ν : Measure K)) :=
    (BoundedContinuousFunction.mkOfCompact (f.comp mulMap)).integrable _
  rw [ofMeasure_apply, mul_apply]
  change ∫ x, f x ∂(Measure.map (fun p : K × K => p.1 * p.2) ((μ : Measure K).prod ν)) = _
  rw [integral_map hmul.aemeasurable f.continuous.aestronglyMeasurable, integral_prod _ hint]
  rfl

omit [SecondCountableTopology K] [ContinuousMul K] in
theorem ofMeasure_diracMeasure_one : ofMeasure (diracMeasure (1 : K)) = 1 := by
  ext f
  rw [ofMeasure_diracMeasure, one_apply]

omit [CompactSpace K] [T2Space K] in
theorem mass_measureConv (μ ν : FiniteMeasure K) :
    (measureConv μ ν).mass = μ.mass * ν.mass := by
  have h1 : ((measureConv μ ν : Measure K) Set.univ) =
      (μ : Measure K) Set.univ * (ν : Measure K) Set.univ := by
    change ((μ : Measure K) ∗ₘ (ν : Measure K)) Set.univ = _
    unfold Measure.mconv
    rw [Measure.map_apply measurable_mul MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
  apply ENNReal.coe_injective
  rw [ENNReal.coe_mul, FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass,
    FiniteMeasure.ennreal_mass, h1]

end Convolution

/-! ### The weak topology -/

omit [T2Space K] [SecondCountableTopology K] in
/-- Weak convergence of finite measures is convergence against every `f ∈ C(K, ℂ)`. -/
theorem tendsto_iff_forall_ofMeasure_tendsto {ι : Type*} {F : Filter ι}
    {μs : ι → FiniteMeasure K} {μ : FiniteMeasure K} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : C(K, ℂ), Tendsto (fun i => ofMeasure (μs i) f) F (𝓝 (ofMeasure μ f)) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  constructor
  · intro h f
    set fr : C(K, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
    set fi : C(K, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
    have hf : f = realToComplex fr + Complex.I • realToComplex fi := by
      ext x
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, realToComplex_apply,
        ContinuousMap.coe_mk, smul_eq_mul, fr, fi]
      rw [mul_comm, Complex.re_add_im]
    have hr := h (BoundedContinuousFunction.mkOfCompact fr)
    have hi := h (BoundedContinuousFunction.mkOfCompact fi)
    simp only [BoundedContinuousFunction.mkOfCompact_apply] at hr hi
    rw [hf]
    simp only [map_add, map_smul, smul_eq_mul, ofMeasure_realToComplex]
    exact ((Complex.continuous_ofReal.tendsto _).comp hr).add
      (((Complex.continuous_ofReal.tendsto _).comp hi).const_mul Complex.I)
  · intro h f
    have h1 := h (realToComplex f.toContinuousMap)
    simp only [ofMeasure_realToComplex] at h1
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2

omit [T2Space K] [SecondCountableTopology K] in
theorem continuous_ofMeasure_apply (f : C(K, ℂ)) :
    Continuous fun μ : FiniteMeasure K => ofMeasure μ f :=
  continuous_iff_continuousAt.2 fun _ =>
    tendsto_iff_forall_ofMeasure_tendsto.1 tendsto_id f

end MeasureAlgebra

end Measures

end GaloisForLFunctions.HTGeometry
