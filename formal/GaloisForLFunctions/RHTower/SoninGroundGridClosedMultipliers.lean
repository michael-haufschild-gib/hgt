import GaloisForLFunctions.RHTower.SoninGroundGridArithmeticSelection
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closed multipliers on the physical Sonin ground grid

The finite ground-grid coefficient multipliers have single-valued closed graph
closures, without a boundedness assumption on their scalar weights. Their
domains are dense in the original closed ground-grid span. Binary weights give
closed idempotents, including domain invariance. These statements do not assert
that an infinite arithmetic source belongs to any such domain.
-/

noncomputable section

open Filter Topology
open scoped ComplexInnerProductSpace

namespace RHTower

/-- The original physical closed ground-grid carrier. -/
def soninGroundGridCarrier (a : ℝ) : Submodule ℂ SoninL2 :=
  (Submodule.span ℂ (Set.range (soninGroundGridVector a))).topologicalClosure

theorem soninGroundGridVector_tendsto_zero (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (soninGroundGridVector a) atTop (𝓝 0) := by
  have hsq (n : ℕ) : ‖soninGroundGridVector a n‖ ^ 2 = 2 * a / (n + 2 : ℝ) := by
    have hh := inner_soninGroundEntry_of_le a ha
      (Real.log (n + 2 : ℝ)) (Real.log (n + 2 : ℝ)) le_rfl
    have hn : (0 : ℝ) < n + 2 := by positivity
    apply Complex.ofReal_inj.mp
    push_cast
    simpa [soninGroundGridVector, inner_self_eq_norm_sq_to_K,
      Real.exp_neg, Real.exp_log hn, div_eq_mul_inv] using hh
  have hshift : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n 2) tendsto_id
  have hsqLimit : Tendsto (fun n => ‖soninGroundGridVector a n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 * a : ℝ)).comp hshift
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsqLimit
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

private def prefixDual (a : ℝ) (n : ℕ) : SoninL2 :=
  (((n + 2 : ℝ) * (n + 3 : ℝ) / (2 * a) : ℝ) : ℂ) •
    (soninGroundGridVector a n - soninGroundGridVector a (n + 1))

/-- The continuous coefficient duals separate the physical grid carrier. -/
theorem soninGroundGridCoefficientDual_total (a : ℝ) (ha : 0 < a)
    {f : SoninL2} (hf : f ∈ soninGroundGridCarrier a)
    (hcoeff : ∀ n, inner ℂ (soninGroundGridCoefficientDual a n) f = 0) : f = 0 := by
  have hp (n : ℕ) : inner ℂ (prefixDual a n) f = 0 := by
    induction n with
    | zero => exact hcoeff 0
    | succ n ih =>
      have hn := hcoeff (n + 1)
      change inner ℂ (prefixDual a (n + 1) - prefixDual a n) f = 0 at hn
      rw [inner_sub_left, ih, sub_zero] at hn
      exact hn
  have hd (n : ℕ) :
      inner ℂ (soninGroundGridVector a n - soninGroundGridVector a (n + 1)) f = 0 := by
    have hn := hp n
    have hscalar : ((n + 2 : ℝ) * (n + 3 : ℝ) / (2 * a) : ℝ) ≠ 0 := by positivity
    rw [prefixDual, inner_smul_left] at hn
    have hc : (starRingEnd ℂ) (((n + 2 : ℝ) * (n + 3 : ℝ) / (2 * a) : ℝ) : ℂ) ≠ 0 := by
      simpa only [Complex.conj_ofReal, Complex.ofReal_ne_zero] using hscalar
    exact (mul_eq_zero.mp hn).resolve_left hc
  have hconst (n : ℕ) :
      inner ℂ (soninGroundGridVector a n) f = inner ℂ (soninGroundGridVector a 0) f := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn := hd n
      rw [inner_sub_left, sub_eq_zero] at hn
      exact hn.symm.trans ih
  have hzero : inner ℂ (soninGroundGridVector a 0) f = 0 := by
    have hl := (soninGroundGridVector_tendsto_zero a ha.le).inner (𝕜 := ℂ)
      (tendsto_const_nhds (x := f))
    simp only [hconst, inner_zero_left] at hl
    exact tendsto_nhds_unique tendsto_const_nhds hl
  have hspan : Submodule.span ℂ (Set.range (soninGroundGridVector a)) ≤
      (innerSL ℂ f).toLinearMap.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change inner ℂ f (soninGroundGridVector a n) = 0
    exact inner_eq_zero_symm.mpr ((hconst n).trans hzero)
  have hclosed : soninGroundGridCarrier a ≤ (innerSL ℂ f).toLinearMap.ker :=
    Submodule.topologicalClosure_minimal _ hspan (innerSL ℂ f).isClosed_ker
  exact inner_self_eq_zero.mp (hclosed hf)

/-- Finite physical-source coefficient multiplication, as a linear relation. -/
def soninGroundGridMultiplierCore (a : ℝ) (w : ℕ → ℂ) :
    Submodule ℂ (SoninL2 × SoninL2) :=
  Submodule.span ℂ (Set.range fun n =>
    (soninGroundGridVector a n, w n • soninGroundGridVector a n))

/-- Closure in the product of the original physical Hilbert spaces. -/
def soninGroundGridMultiplierGraph (a : ℝ) (w : ℕ → ℂ) :
    Submodule ℂ (SoninL2 × SoninL2) :=
  (soninGroundGridMultiplierCore a w).topologicalClosure

theorem soninGroundGridMultiplierGraph_generator (a : ℝ) (w : ℕ → ℂ) (n : ℕ) :
    (soninGroundGridVector a n, w n • soninGroundGridVector a n) ∈
      soninGroundGridMultiplierGraph a w :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

theorem soninGroundGridMultiplierGraph_coordinates (a : ℝ) (w : ℕ → ℂ)
    {p : SoninL2 × SoninL2} (hp : p ∈ soninGroundGridMultiplierGraph a w) :
    p.1 ∈ soninGroundGridCarrier a ∧ p.2 ∈ soninGroundGridCarrier a := by
  have hc := (Submodule.span ℂ (Set.range (soninGroundGridVector a))).isClosed_topologicalClosure
  have hle : soninGroundGridMultiplierCore a w ≤
      (soninGroundGridCarrier a).prod (soninGroundGridCarrier a) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    have hn : soninGroundGridVector a n ∈ soninGroundGridCarrier a :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
    exact ⟨hn, (soninGroundGridCarrier a).smul_mem (w n) hn⟩
  exact Submodule.topologicalClosure_minimal _ hle (hc.prod hc) hp

/-- Every graph limit retains the literal coefficient multiplication law. -/
theorem soninGroundGridMultiplierGraph_coefficient (a : ℝ) (ha : 0 < a)
    (w : ℕ → ℂ) {p : SoninL2 × SoninL2}
    (hp : p ∈ soninGroundGridMultiplierGraph a w) (n : ℕ) :
    inner ℂ (soninGroundGridCoefficientDual a n) p.2 =
      w n * inner ℂ (soninGroundGridCoefficientDual a n) p.1 := by
  let L : (SoninL2 × SoninL2) →L[ℂ] ℂ :=
    (innerSL ℂ (soninGroundGridCoefficientDual a n)).comp (ContinuousLinearMap.snd ℂ _ _) -
      w n • (innerSL ℂ (soninGroundGridCoefficientDual a n)).comp
        (ContinuousLinearMap.fst ℂ _ _)
  have hle : soninGroundGridMultiplierCore a w ≤ L.toLinearMap.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    change inner ℂ (soninGroundGridCoefficientDual a n) (w j • soninGroundGridVector a j) -
      w n * inner ℂ (soninGroundGridCoefficientDual a n) (soninGroundGridVector a j) = 0
    rw [inner_smul_right, soninGroundGridCoefficientDual_inner a ha]
    by_cases h : n = j
    · subst j; simp
    · simp [h]
  have hzero := Submodule.topologicalClosure_minimal _ hle L.isClosed_ker hp
  exact sub_eq_zero.mp hzero

theorem soninGroundGridMultiplierGraph_vertical (a : ℝ) (ha : 0 < a) (w : ℕ → ℂ)
    (p : SoninL2 × SoninL2) (hp : p ∈ soninGroundGridMultiplierGraph a w)
    (hx : p.1 = 0) : p.2 = 0 := by
  apply soninGroundGridCoefficientDual_total a ha
    (soninGroundGridMultiplierGraph_coordinates a w hp).2
  intro n
  simpa [hx] using soninGroundGridMultiplierGraph_coefficient a ha w hp n

/-- The minimal closed extension of finite physical coefficient multiplication. -/
def soninGroundGridClosedMultiplier (a : ℝ) (w : ℕ → ℂ) : SoninL2 →ₗ.[ℂ] SoninL2 :=
  (soninGroundGridMultiplierGraph a w).toLinearPMap

theorem soninGroundGridClosedMultiplier_graph (a : ℝ) (ha : 0 < a) (w : ℕ → ℂ) :
    (soninGroundGridClosedMultiplier a w).graph = soninGroundGridMultiplierGraph a w :=
  Submodule.toLinearPMap_graph_eq _ (soninGroundGridMultiplierGraph_vertical a ha w)

theorem soninGroundGridClosedMultiplier_isClosed (a : ℝ) (ha : 0 < a) (w : ℕ → ℂ) :
    (soninGroundGridClosedMultiplier a w).IsClosed := by
  change IsClosed ((soninGroundGridClosedMultiplier a w).graph : Set (SoninL2 × SoninL2))
  rw [soninGroundGridClosedMultiplier_graph a ha]
  exact Submodule.isClosed_topologicalClosure _

theorem soninGroundGridClosedMultiplier_generator_mem_domain
    (a : ℝ) (ha : 0 < a) (w : ℕ → ℂ) (n : ℕ) :
    soninGroundGridVector a n ∈ (soninGroundGridClosedMultiplier a w).domain := by
  apply LinearPMap.mem_domain_of_mem_graph (y := w n • soninGroundGridVector a n)
  rw [soninGroundGridClosedMultiplier_graph a ha]
  exact soninGroundGridMultiplierGraph_generator a w n

theorem soninGroundGridClosedMultiplier_apply_generator
    (a : ℝ) (ha : 0 < a) (w : ℕ → ℂ) (n : ℕ) :
    soninGroundGridClosedMultiplier a w
        ⟨soninGroundGridVector a n,
          soninGroundGridClosedMultiplier_generator_mem_domain a ha w n⟩ =
      w n • soninGroundGridVector a n := by
  apply Eq.symm
  apply (LinearPMap.image_iff _).mpr
  rw [soninGroundGridClosedMultiplier_graph a ha]
  exact soninGroundGridMultiplierGraph_generator a w n

/-- Density is in the original carrier, not in a newly completed coefficient space. -/
theorem soninGroundGridClosedMultiplier_domain_closure
    (a : ℝ) (ha : 0 < a) (w : ℕ → ℂ) :
    (soninGroundGridClosedMultiplier a w).domain.topologicalClosure =
      soninGroundGridCarrier a := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · intro x hx
      obtain ⟨y, hy⟩ := LinearPMap.mem_domain_iff.mp hx
      rw [soninGroundGridClosedMultiplier_graph a ha] at hy
      exact (soninGroundGridMultiplierGraph_coordinates a w hy).1
    · exact Submodule.isClosed_topologicalClosure _
  · apply Submodule.topologicalClosure_mono
    exact Submodule.span_le.mpr (by
      rintro _ ⟨n, rfl⟩
      exact soninGroundGridClosedMultiplier_generator_mem_domain a ha w n)

/-- No smaller closed linear graph can extend all finite generator pairs. -/
theorem soninGroundGridMultiplierGraph_minimal (a : ℝ) (w : ℕ → ℂ)
    {G : Submodule ℂ (SoninL2 × SoninL2)} (hG : IsClosed (G : Set (SoninL2 × SoninL2)))
    (hgen : ∀ n, (soninGroundGridVector a n, w n • soninGroundGridVector a n) ∈ G) :
    soninGroundGridMultiplierGraph a w ≤ G := by
  apply Submodule.topologicalClosure_minimal _ _ hG
  exact Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hgen n)

/-- Idempotent scalar weights preserve the closed graph under `(x,y) ↦ (y,y)`. -/
theorem soninGroundGridMultiplierGraph_idempotent (a : ℝ) (w : ℕ → ℂ)
    (hw : ∀ n, w n * w n = w n) {x y : SoninL2}
    (hxy : (x, y) ∈ soninGroundGridMultiplierGraph a w) :
    (y, y) ∈ soninGroundGridMultiplierGraph a w := by
  let J : (SoninL2 × SoninL2) →L[ℂ] (SoninL2 × SoninL2) :=
    (ContinuousLinearMap.snd ℂ SoninL2 SoninL2).prod
      (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)
  have hcore : soninGroundGridMultiplierCore a w ≤
      (soninGroundGridMultiplierGraph a w).comap J.toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change (w n • soninGroundGridVector a n, w n • soninGroundGridVector a n) ∈
      soninGroundGridMultiplierGraph a w
    have hn := (soninGroundGridMultiplierGraph a w).smul_mem (w n)
      (soninGroundGridMultiplierGraph_generator a w n)
    simpa only [Prod.smul_mk, smul_smul, hw n] using hn
  have hclosed : IsClosed (((soninGroundGridMultiplierGraph a w).comap J.toLinearMap) :
      Set (SoninL2 × SoninL2)) :=
    (Submodule.isClosed_topologicalClosure _).preimage J.continuous
  exact Submodule.topologicalClosure_minimal _ hcore hclosed hxy

/-- Idempotence includes the essential domain-invariance statement. -/
theorem soninGroundGridClosedMultiplier_idempotent (a : ℝ) (ha : 0 < a)
    (w : ℕ → ℂ) (hw : ∀ n, w n * w n = w n)
    (x : (soninGroundGridClosedMultiplier a w).domain) :
    ∃ hy : soninGroundGridClosedMultiplier a w x ∈ (soninGroundGridClosedMultiplier a w).domain,
      soninGroundGridClosedMultiplier a w ⟨soninGroundGridClosedMultiplier a w x, hy⟩ =
        soninGroundGridClosedMultiplier a w x := by
  have hxy := (soninGroundGridClosedMultiplier a w).mem_graph x
  rw [soninGroundGridClosedMultiplier_graph a ha] at hxy
  have hyy := soninGroundGridMultiplierGraph_idempotent a w hw hxy
  rw [← soninGroundGridClosedMultiplier_graph a ha] at hyy
  exact ⟨LinearPMap.mem_domain_of_mem_graph hyy, ((LinearPMap.image_iff _).mpr hyy).symm⟩

/-- Literal binary selection, retaining the physical topology and its domain. -/
def soninGroundGridClosedSelector (a : ℝ) (mask : ℕ → Prop) [DecidablePred mask] :
    SoninL2 →ₗ.[ℂ] SoninL2 :=
  soninGroundGridClosedMultiplier a (fun n => if mask n then 1 else 0)

theorem soninGroundGridClosedSelector_idempotent (a : ℝ) (ha : 0 < a)
    (mask : ℕ → Prop) [DecidablePred mask]
    (x : (soninGroundGridClosedSelector a mask).domain) :
    ∃ hy : soninGroundGridClosedSelector a mask x ∈ (soninGroundGridClosedSelector a mask).domain,
      soninGroundGridClosedSelector a mask ⟨soninGroundGridClosedSelector a mask x, hy⟩ =
        soninGroundGridClosedSelector a mask x := by
  apply soninGroundGridClosedMultiplier_idempotent a ha
  intro n
  split_ifs <;> norm_num

/-- The finite TG source has its original signed coefficients, with no weighting. -/
theorem soninPrimePolarGridSource_coefficient (a : ℝ) (ha : 0 < a) (N n : ℕ) :
    inner ℂ (soninGroundGridCoefficientDual a n) (soninPrimePolarGridSource a N) =
      if n ≤ N then (soninPrimePolarGridCoefficient n : ℂ) else 0 := by
  classical
  change inner ℂ (soninGroundGridCoefficientDual a n)
    (∑ j ∈ Finset.range (N + 1), (soninPrimePolarGridCoefficient j : ℂ) •
      soninGroundGridVector a j) = _
  simp_rw [inner_sum, inner_smul_right, soninGroundGridCoefficientDual_inner a ha]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [eq_comm (a := n)]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- Any cofinal physical limit retains every original signed coefficient. -/
theorem soninPrimePolarGridSource_limit_coefficient (a : ℝ) (ha : 0 < a)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {f : SoninL2}
    (hf : Tendsto (fun k => soninPrimePolarGridSource a (φ k)) atTop (𝓝 f)) (n : ℕ) :
    inner ℂ (soninGroundGridCoefficientDual a n) f =
      (soninPrimePolarGridCoefficient n : ℂ) := by
  have hl := ((innerSL ℂ (soninGroundGridCoefficientDual a n)).continuous.tendsto f).comp hf
  have he : ∀ᶠ k in atTop, n ≤ φ k := hφ.eventually (eventually_ge_atTop n)
  have hc : Tendsto
      (fun k => inner ℂ (soninGroundGridCoefficientDual a n) (soninPrimePolarGridSource a (φ k)))
      atTop (𝓝 (soninPrimePolarGridCoefficient n : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    simp [soninPrimePolarGridSource_coefficient a ha, hk]
  exact tendsto_nhds_unique hl hc

theorem soninPrimePolarGridSource_limit_mem_carrier (a : ℝ)
    {φ : ℕ → ℕ} {f : SoninL2}
    (hf : Tendsto (fun k => soninPrimePolarGridSource a (φ k)) atTop (𝓝 f)) :
    f ∈ soninGroundGridCarrier a := by
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hf
  apply Filter.Eventually.of_forall
  intro k
  apply Submodule.le_topologicalClosure
  change (∑ j ∈ Finset.range (φ k + 1), (soninPrimePolarGridCoefficient j : ℂ) •
    soninGroundGridVector a j) ∈ Submodule.span ℂ (Set.range (soninGroundGridVector a))
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- A cofinal schedule cannot change the admitted native source. -/
theorem soninPrimePolarGridSource_cofinal_limit_unique (a : ℝ) (ha : 0 < a)
    {φ ψ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) (hψ : Tendsto ψ atTop atTop)
    {f g : SoninL2}
    (hf : Tendsto (fun k => soninPrimePolarGridSource a (φ k)) atTop (𝓝 f))
    (hg : Tendsto (fun k => soninPrimePolarGridSource a (ψ k)) atTop (𝓝 g)) : f = g := by
  apply sub_eq_zero.mp
  apply soninGroundGridCoefficientDual_total a ha
    ((soninGroundGridCarrier a).sub_mem (soninPrimePolarGridSource_limit_mem_carrier a hf)
      (soninPrimePolarGridSource_limit_mem_carrier a hg))
  intro n
  rw [inner_sub_right, soninPrimePolarGridSource_limit_coefficient a ha hφ hf,
    soninPrimePolarGridSource_limit_coefficient a ha hψ hg, sub_self]

/-- Applying a closed multiplier to an admitted TG source requires its exact
weighted coefficients to be represented by a vector in the same carrier. -/
theorem soninPrimePolarGridSource_multiplier_coefficients (a : ℝ) (ha : 0 < a)
    (w : ℕ → ℂ) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {f g : SoninL2}
    (hf : Tendsto (fun k => soninPrimePolarGridSource a (φ k)) atTop (𝓝 f))
    (hfg : (f, g) ∈ (soninGroundGridClosedMultiplier a w).graph) (n : ℕ) :
    inner ℂ (soninGroundGridCoefficientDual a n) g =
      w n * (soninPrimePolarGridCoefficient n : ℂ) := by
  rw [soninGroundGridClosedMultiplier_graph a ha] at hfg
  rw [soninGroundGridMultiplierGraph_coefficient a ha w hfg n]
  rw [soninPrimePolarGridSource_limit_coefficient a ha hφ hf]

end RHTower
