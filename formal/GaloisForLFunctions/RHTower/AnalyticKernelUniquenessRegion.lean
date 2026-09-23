import GaloisForLFunctions.HTGeometry.AnalyticOpenCutoffNoGo
import GaloisForLFunctions.RHTower.DetectorDuality

namespace RHTower

open Set Filter Topology
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An analytic family of kernel sections whose global span is total. -/
structure AnalyticTotalSectionFamily (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  domain : Set ℂ
  kernelSection : ℂ → H
  domain_preconnected : IsPreconnected domain
  coefficient_analytic : ∀ w : H,
    AnalyticOnNhd ℂ (fun z => inner ℂ w (kernelSection z)) domain
  global_total : (Submodule.span ℂ (kernelSection '' domain)).topologicalClosure = ⊤

/-- A nonempty open uniqueness region inside the analytic domain. -/
structure AnalyticTotalSectionFamily.OpenRegion (R : AnalyticTotalSectionFamily H) where
  region : Set ℂ
  isOpen_region : IsOpen region
  region_subset : region ⊆ R.domain
  region_nonempty : region.Nonempty

/-- A sampling set with an accumulation point inside the analytic domain. -/
structure AnalyticTotalSectionFamily.AccumulationSet (R : AnalyticTotalSectionFamily H) where
  nodes : Set ℂ
  nodes_subset : nodes ⊆ R.domain
  point : ℂ
  point_mem_domain : point ∈ R.domain
  frequently_nodes : ∃ᶠ z in nhdsWithin point ({point}ᶜ), z ∈ nodes

namespace AnalyticTotalSectionFamily

variable (R : AnalyticTotalSectionFamily H)

/-- Kernel sections sampled in any nonempty open uniqueness region remain total. -/
theorem openRegion_total (V : R.OpenRegion) :
    (Submodule.span ℂ (R.kernelSection '' V.region)).topologicalClosure = ⊤ := by
  rw [topologicalClosure_span_eq_top_iff]
  intro w hw
  have hzero : EqOn (fun z => inner ℂ w (R.kernelSection z)) 0 V.region := by
    intro z hz
    exact hw (R.kernelSection z) ⟨z, hz, rfl⟩
  have hglobal := analytic_eq_zero_of_eq_zero_on_nonempty_open
    (R.coefficient_analytic w) R.domain_preconnected V.isOpen_region
    V.region_subset V.region_nonempty hzero
  have htotal := (topologicalClosure_span_eq_top_iff
    (R.kernelSection '' R.domain)).mp R.global_total
  exact htotal w (by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := hs
    exact hglobal hz)

/-- Any sampling set accumulating inside the analytic domain remains total. -/
theorem accumulationSet_total (D : R.AccumulationSet) :
    (Submodule.span ℂ (R.kernelSection '' D.nodes)).topologicalClosure = ⊤ := by
  rw [topologicalClosure_span_eq_top_iff]
  intro w hw
  have hzero : ∀ z ∈ D.nodes, inner ℂ w (R.kernelSection z) = 0 := by
    intro z hz
    exact hw (R.kernelSection z) ⟨z, hz, rfl⟩
  have hfreq : ∃ᶠ z in nhdsWithin D.point ({D.point}ᶜ),
      (fun u => inner ℂ w (R.kernelSection u)) z = 0 :=
    D.frequently_nodes.mono (fun z hz => hzero z hz)
  have hglobal : EqOn (fun z => inner ℂ w (R.kernelSection z)) 0 R.domain :=
    (R.coefficient_analytic w).eqOn_zero_of_preconnected_of_frequently_eq_zero
      R.domain_preconnected D.point_mem_domain hfreq
  have htotal := (topologicalClosure_span_eq_top_iff
    (R.kernelSection '' R.domain)).mp R.global_total
  exact htotal w (by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := hs
    exact hglobal hz)

end AnalyticTotalSectionFamily

/-- Minimal analytic Hermitian-kernel realization on a Hilbert majorant. -/
structure AnalyticHermitianKernelRealization (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    extends AnalyticTotalSectionFamily H where
  form : H →L[ℂ] H
  form_hermitian : ∀ x y : H, inner ℂ x (form y) = inner ℂ (form x) y

namespace AnalyticHermitianKernelRealization

variable (R : AnalyticHermitianKernelRealization H)

/-- Hermitian kernel induced by the analytic section family and bounded form. -/
def kernel (z w : ℂ) : ℂ := inner ℂ (R.kernelSection w) (R.form (R.kernelSection z))

theorem kernel_conj_symm (z w : ℂ) : R.kernel z w = star (R.kernel w z) := by
  rw [kernel, kernel, R.form_hermitian]
  exact (inner_conj_symm (𝕜 := ℂ)
    (R.form (R.kernelSection w)) (R.kernelSection z)).symm

/-- Synthesis of a finite tuple in the Hilbert majorant. -/
def sectionSynthesis {r : ℕ} (v : Fin r → H) (c : Fin r → ℂ) : H :=
  ∑ i, c i • v i

omit [CompleteSpace H] in
theorem sectionSynthesis_smul {r : ℕ} (v : Fin r → H) (a : ℂ) (c : Fin r → ℂ) :
    sectionSynthesis v (a • c) = a • sectionSynthesis v c := by
  simp only [sectionSynthesis, Pi.smul_apply, Finset.smul_sum, smul_eq_mul, mul_smul]

/-- Real quadratic form of the bounded Hermitian realization on a finite tuple. -/
def sectionQuadratic {r : ℕ} (v : Fin r → H) (c : Fin r → ℂ) : ℝ :=
  (inner ℂ (sectionSynthesis v c) (R.form (sectionSynthesis v c))).re

theorem sectionQuadratic_smul {r : ℕ} (v : Fin r → H) (a : ℂ) (c : Fin r → ℂ) :
    R.sectionQuadratic v (a • c) = ‖a‖ ^ (2 : ℕ) * R.sectionQuadratic v c := by
  simp [sectionQuadratic, sectionSynthesis_smul, map_smul]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

/-- Strict negativity on the compact unit sphere of a coefficient space. -/
def IsNegativeTuple {r : ℕ} (v : Fin r → H) : Prop :=
  ∀ c : Fin r → ℂ, ‖c‖ = 1 → R.sectionQuadratic v c < 0

/-- Unit-sphere negativity is strict negativity for every nonzero coefficient vector. -/
theorem isNegativeTuple_quadratic_neg {r : ℕ} {v : Fin r → H}
    (hv : R.IsNegativeTuple v) {c : Fin r → ℂ} (hc : c ≠ 0) :
    R.sectionQuadratic v c < 0 := by
  let a : ℂ := (‖c‖ : ℂ)⁻¹
  have hnorm : ‖c‖ ≠ 0 := by simpa using hc
  have haNorm : ‖a‖ = ‖c‖⁻¹ := by simp [a]
  have hunit : ‖a • c‖ = 1 := by
    rw [norm_smul, haNorm, inv_mul_cancel₀ hnorm]
  have hneg := hv (a • c) hunit
  rw [R.sectionQuadratic_smul v a c, haNorm] at hneg
  have hfactor : 0 < ‖c‖⁻¹ ^ (2 : ℕ) := sq_pos_of_ne_zero (inv_ne_zero hnorm)
  nlinarith

/-- A strictly negative `r`-tuple consists of `r` linearly independent vectors. -/
theorem isNegativeTuple_linearIndependent {r : ℕ} {v : Fin r → H}
    (hv : R.IsNegativeTuple v) : LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hci
  have hcne : c ≠ 0 := by
    intro hzero
    exact hci (congrFun hzero i)
  have hneg := R.isNegativeTuple_quadratic_neg hv hcne
  unfold sectionQuadratic at hneg
  change sectionSynthesis v c = 0 at hc
  rw [hc] at hneg
  simp at hneg

/-- Joint continuity of the finite-tuple quadratic form. -/
theorem continuous_sectionQuadratic {r : ℕ} :
    Continuous (fun p : (Fin r → H) × (Fin r → ℂ) =>
      R.sectionQuadratic p.1 p.2) := by
  unfold sectionQuadratic sectionSynthesis
  fun_prop

/-- Strictly negative `r`-tuples form an open subset of the finite product. -/
theorem isOpen_isNegativeTuple (r : ℕ) :
    IsOpen {v : Fin r → H | R.IsNegativeTuple v} := by
  let sphere := Metric.sphere (0 : Fin r → ℂ) 1
  let bad : Set ((Fin r → H) × sphere) :=
    {p | 0 ≤ R.sectionQuadratic p.1 p.2}
  have hcont : Continuous
      (fun p : (Fin r → H) × sphere => R.sectionQuadratic p.1 p.2) :=
    R.continuous_sectionQuadratic.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hclosed : IsClosed bad := isClosed_Ici.preimage hcont
  haveI : CompactSpace sphere :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Fin r → ℂ) 1)
  have hproj : IsClosed (Prod.fst '' bad) :=
    isClosedMap_fst_of_compactSpace _ hclosed
  rw [show {v : Fin r → H | R.IsNegativeTuple v} = (Prod.fst '' bad)ᶜ by
    ext v
    constructor
    · intro hv
      rw [mem_compl_iff]
      rintro ⟨p, hp, rfl⟩
      exact (not_lt_of_ge hp) (hv p.2 (mem_sphere_zero_iff_norm.mp p.2.2))
    · intro hv c hc
      rw [mem_compl_iff] at hv
      by_contra hneg
      apply hv
      exact ⟨(v, ⟨c, mem_sphere_zero_iff_norm.mpr hc⟩), le_of_not_gt hneg, rfl⟩]
  exact hproj.isOpen_compl

/-- A negative tuple in the closure of a submodule can be approximated by a
negative tuple inside the submodule itself. -/
theorem exists_negativeTuple_mem_of_mem_topologicalClosure
    {r : ℕ} (D : Submodule ℂ H) (v : Fin r → H)
    (hvD : ∀ i, v i ∈ D.topologicalClosure) (hv : R.IsNegativeTuple v) :
    ∃ y : Fin r → H, (∀ i, y i ∈ D) ∧ R.IsNegativeTuple y := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (R.isOpen_isNegativeTuple r) v hv
  have happrox : ∀ i, ∃ y ∈ D, dist (v i) y < ε := by
    intro i
    apply Metric.mem_closure_iff.mp
      (show v i ∈ closure (D : Set H) from hvD i)
    exact hε
  choose y hyD hyDist using happrox
  refine ⟨y, hyD, hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
  intro i
  change ‖y i - v i‖ < ε
  rw [← dist_eq_norm, dist_comm]
  exact hyDist i

/-- A finite negative dimension visible in the completed span of sections sampled from `S`. -/
def HasNegativeDimensionOn (S : Set ℂ) (r : ℕ) : Prop :=
  ∃ v : Fin r → H,
    (∀ i, v i ∈ (Submodule.span ℂ (R.kernelSection '' S)).topologicalClosure) ∧
      R.IsNegativeTuple v

/-- A finite negative dimension already visible in algebraic finite combinations
of sections sampled from `S`. -/
def HasFiniteSectionNegativeDimensionOn (S : Set ℂ) (r : ℕ) : Prop :=
  ∃ v : Fin r → H,
    (∀ i, v i ∈ Submodule.span ℂ (R.kernelSection '' S)) ∧
      R.IsNegativeTuple v

/-- Hilbert-space vector represented by a finitely supported coefficient packet
on a sampling set. -/
def finiteKernelCombination (S : Set ℂ) (d : S →₀ ℂ) : H :=
  Finsupp.linearCombination ℂ (fun z : S => R.kernelSection z) d

/-- Literal finite kernel-Gram quadratic form of a coefficient packet. -/
def finiteKernelGramQuadratic (S : Set ℂ) (d : S →₀ ℂ) : ℝ :=
  (d.sum fun z dz =>
    d.sum fun w dw => star dw * dz * R.kernel z w).re

theorem finiteKernelCombination_eq_sum (S : Set ℂ) (d : S →₀ ℂ) :
    R.finiteKernelCombination S d =
      d.sum (fun z a => a • R.kernelSection z) := rfl

/-- The explicit double kernel sum is exactly the realized Hermitian quadratic form. -/
theorem finiteKernelGramQuadratic_eq (S : Set ℂ) (d : S →₀ ℂ) :
    R.finiteKernelGramQuadratic S d =
      (inner ℂ (R.finiteKernelCombination S d)
        (R.form (R.finiteKernelCombination S d))).re := by
  classical
  unfold finiteKernelGramQuadratic
  apply congrArg Complex.re
  rw [R.finiteKernelCombination_eq_sum S d]
  simp [Finsupp.sum, kernel, map_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

/-- Finite kernel combination commutes with a finite coefficient-space synthesis. -/
theorem finiteKernelCombination_sum_smul {r : ℕ} (S : Set ℂ)
    (d : Fin r → (S →₀ ℂ)) (c : Fin r → ℂ) :
    R.finiteKernelCombination S (∑ i, c i • d i) =
      sectionSynthesis (fun i => R.finiteKernelCombination S (d i)) c := by
  simp [finiteKernelCombination, sectionSynthesis]

theorem range_kernelSection_subtype (S : Set ℂ) :
    Set.range (fun z : S => R.kernelSection z) = R.kernelSection '' S := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩

theorem finiteKernelCombination_mem_span (S : Set ℂ) (d : S →₀ ℂ) :
    R.finiteKernelCombination S d ∈ Submodule.span ℂ (R.kernelSection '' S) := by
  rw [← R.range_kernelSection_subtype S]
  apply Finsupp.mem_span_range_iff_exists_finsupp.mpr
  exact ⟨d, rfl⟩

theorem exists_finiteKernelCombination_eq_of_mem_span
    (S : Set ℂ) {x : H} (hx : x ∈ Submodule.span ℂ (R.kernelSection '' S)) :
    ∃ d : S →₀ ℂ, R.finiteKernelCombination S d = x := by
  rw [← R.range_kernelSection_subtype S] at hx
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp hx

/-- A literal finite Gram witness: `r` coefficient packets synthesize an
`r`-dimensional strictly negative subspace of one finite kernel section. -/
def HasFiniteGramNegativeDimensionOn (S : Set ℂ) (r : ℕ) : Prop :=
  ∃ d : Fin r → (S →₀ ℂ),
    R.IsNegativeTuple (fun i => R.finiteKernelCombination S (d i))

/-- Literal finite Gram witnesses and finite-section negative dimensions are equivalent. -/
theorem hasFiniteGramNegativeDimensionOn_iff
    (S : Set ℂ) (r : ℕ) :
    R.HasFiniteGramNegativeDimensionOn S r ↔
      R.HasFiniteSectionNegativeDimensionOn S r := by
  constructor
  · rintro ⟨d, hneg⟩
    exact ⟨fun i => R.finiteKernelCombination S (d i),
      fun i => R.finiteKernelCombination_mem_span S (d i), hneg⟩
  · rintro ⟨v, hv, hneg⟩
    have hex : ∀ i, ∃ d : S →₀ ℂ, R.finiteKernelCombination S d = v i :=
      fun i => R.exists_finiteKernelCombination_eq_of_mem_span S (hv i)
    choose d hd using hex
    refine ⟨d, ?_⟩
    convert hneg using 1
    funext i
    exact hd i

/-- A bundled Gram witness supplies a literal strictly negative double-kernel
sum for every nonzero coefficient vector in its `r`-dimensional packet space. -/
theorem hasFiniteGramNegativeDimensionOn_literal_negative
    {S : Set ℂ} {r : ℕ} (h : R.HasFiniteGramNegativeDimensionOn S r) :
    ∃ d : Fin r → (S →₀ ℂ), ∀ c : Fin r → ℂ, c ≠ 0 →
      R.finiteKernelGramQuadratic S (∑ i, c i • d i) < 0 := by
  obtain ⟨d, hneg⟩ := h
  refine ⟨d, ?_⟩
  intro c hc
  have hq := R.isNegativeTuple_quadratic_neg hneg hc
  rw [sectionQuadratic, ← R.finiteKernelCombination_sum_smul S d c,
    ← R.finiteKernelGramQuadratic_eq S (∑ i, c i • d i)] at hq
  exact hq

/-- Passing from finite section combinations to their Hilbert closure neither
creates nor destroys any finite negative dimension. -/
theorem hasFiniteSectionNegativeDimensionOn_iff
    (S : Set ℂ) (r : ℕ) :
    R.HasFiniteSectionNegativeDimensionOn S r ↔ R.HasNegativeDimensionOn S r := by
  constructor
  · rintro ⟨v, hv, hneg⟩
    exact ⟨v, fun i => Submodule.le_topologicalClosure _ (hv i), hneg⟩
  · rintro ⟨v, hv, hneg⟩
    obtain ⟨y, hy, hyneg⟩ := R.exists_negativeTuple_mem_of_mem_topologicalClosure
      (Submodule.span ℂ (R.kernelSection '' S)) v hv hneg
    exact ⟨y, hy, hyneg⟩

/-- Restriction to a nonempty open uniqueness region preserves every finite
negative dimension, hence preserves finite or infinite negative index. -/
theorem hasNegativeDimensionOn_openRegion_iff
    (V : R.toAnalyticTotalSectionFamily.OpenRegion) (r : ℕ) :
    R.HasNegativeDimensionOn V.region r ↔
      R.HasNegativeDimensionOn R.domain r := by
  unfold HasNegativeDimensionOn
  rw [R.toAnalyticTotalSectionFamily.openRegion_total V, R.global_total]

/-- Sampling on any accumulating node set preserves every finite negative
dimension, including the unbounded-index profile. -/
theorem hasNegativeDimensionOn_accumulationSet_iff
    (D : R.toAnalyticTotalSectionFamily.AccumulationSet) (r : ℕ) :
    R.HasNegativeDimensionOn D.nodes r ↔
      R.HasNegativeDimensionOn R.domain r := by
  unfold HasNegativeDimensionOn
  rw [R.toAnalyticTotalSectionFamily.accumulationSet_total D, R.global_total]

/-- Every nonempty open uniqueness region preserves literal finite-section
negative dimensions. -/
theorem hasFiniteSectionNegativeDimensionOn_openRegion_iff
    (V : R.toAnalyticTotalSectionFamily.OpenRegion) (r : ℕ) :
    R.HasFiniteSectionNegativeDimensionOn V.region r ↔
      R.HasFiniteSectionNegativeDimensionOn R.domain r := by
  rw [R.hasFiniteSectionNegativeDimensionOn_iff,
    R.hasNegativeDimensionOn_openRegion_iff V,
    R.hasFiniteSectionNegativeDimensionOn_iff]

/-- Every accumulating node set preserves literal finite-section negative
dimensions, hence also an unbounded negative-index profile. -/
theorem hasFiniteSectionNegativeDimensionOn_accumulationSet_iff
    (D : R.toAnalyticTotalSectionFamily.AccumulationSet) (r : ℕ) :
    R.HasFiniteSectionNegativeDimensionOn D.nodes r ↔
      R.HasFiniteSectionNegativeDimensionOn R.domain r := by
  rw [R.hasFiniteSectionNegativeDimensionOn_iff,
    R.hasNegativeDimensionOn_accumulationSet_iff D,
    R.hasFiniteSectionNegativeDimensionOn_iff]

/-- Every nonempty open uniqueness region preserves every literal finite Gram
negative dimension. -/
theorem hasFiniteGramNegativeDimensionOn_openRegion_iff
    (V : R.toAnalyticTotalSectionFamily.OpenRegion) (r : ℕ) :
    R.HasFiniteGramNegativeDimensionOn V.region r ↔
      R.HasFiniteGramNegativeDimensionOn R.domain r := by
  rw [R.hasFiniteGramNegativeDimensionOn_iff,
    R.hasFiniteSectionNegativeDimensionOn_openRegion_iff V,
    R.hasFiniteGramNegativeDimensionOn_iff]

/-- Every node set accumulating in the analytic domain preserves every literal
finite Gram negative dimension, including an unbounded index profile. -/
theorem hasFiniteGramNegativeDimensionOn_accumulationSet_iff
    (D : R.toAnalyticTotalSectionFamily.AccumulationSet) (r : ℕ) :
    R.HasFiniteGramNegativeDimensionOn D.nodes r ↔
      R.HasFiniteGramNegativeDimensionOn R.domain r := by
  rw [R.hasFiniteGramNegativeDimensionOn_iff,
    R.hasFiniteSectionNegativeDimensionOn_accumulationSet_iff D,
    R.hasFiniteGramNegativeDimensionOn_iff]

end AnalyticHermitianKernelRealization

end

end RHTower
