import GaloisForLFunctions.HTGeometry.KernelNegativeSquareCongruence

/-!
# Finite negative dimensions and closed section spans

A bounded form has the same finite negative dimensions on any two section
families with equal closed spans. Strict negativity is open on finite tuples,
so passage between algebraic spans and their closures preserves each dimension.
Positive real scaling of a kernel preserves these dimensions as well.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.KernelClosedSpanInertia
open Set Filter Topology Metric
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (A : H →L[ℂ] H)
/-- Synthesis of a finite tuple in the Hilbert majorant. -/
def sectionSynthesis {r : ℕ} (v : Fin r → H) (c : Fin r → ℂ) : H :=
  ∑ i, c i • v i

theorem sectionSynthesis_smul {r : ℕ} (v : Fin r → H) (a : ℂ) (c : Fin r → ℂ) :
    sectionSynthesis v (a • c) = a • sectionSynthesis v c := by
  simp only [sectionSynthesis, Pi.smul_apply, Finset.smul_sum, smul_eq_mul, mul_smul]

/-- Real quadratic form of the bounded Hermitian realization on a finite tuple. -/
def sectionQuadratic {r : ℕ} (v : Fin r → H) (c : Fin r → ℂ) : ℝ :=
  (inner ℂ (sectionSynthesis v c) (A (sectionSynthesis v c))).re

theorem sectionQuadratic_smul {r : ℕ} (v : Fin r → H) (a : ℂ) (c : Fin r → ℂ) :
    (sectionQuadratic A) v (a • c) = ‖a‖ ^ (2 : ℕ) * (sectionQuadratic A) v c := by
  simp [sectionQuadratic, sectionSynthesis_smul, map_smul]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

/-- Strict negativity on the compact unit sphere of a coefficient space. -/
def IsNegativeTuple {r : ℕ} (v : Fin r → H) : Prop :=
  ∀ c : Fin r → ℂ, ‖c‖ = 1 → (sectionQuadratic A) v c < 0

/-- Unit-sphere negativity is strict negativity for every nonzero coefficient vector. -/
theorem isNegativeTuple_quadratic_neg {r : ℕ} {v : Fin r → H}
    (hv : (IsNegativeTuple A) v) {c : Fin r → ℂ} (hc : c ≠ 0) :
    (sectionQuadratic A) v c < 0 := by
  let a : ℂ := (‖c‖ : ℂ)⁻¹
  have hnorm : ‖c‖ ≠ 0 := by simpa using hc
  have haNorm : ‖a‖ = ‖c‖⁻¹ := by simp [a]
  have hunit : ‖a • c‖ = 1 := by
    rw [norm_smul, haNorm, inv_mul_cancel₀ hnorm]
  have hneg := hv (a • c) hunit
  rw [(sectionQuadratic_smul A) v a c, haNorm] at hneg
  have hfactor : 0 < ‖c‖⁻¹ ^ (2 : ℕ) := sq_pos_of_ne_zero (inv_ne_zero hnorm)
  nlinarith

/-- Joint continuity of the finite-tuple quadratic form. -/
theorem continuous_sectionQuadratic {r : ℕ} :
    Continuous (fun p : (Fin r → H) × (Fin r → ℂ) =>
      (sectionQuadratic A) p.1 p.2) := by
  unfold sectionQuadratic sectionSynthesis
  fun_prop

/-- Strictly negative `r`-tuples form an open subset of the finite product. -/
theorem isOpen_isNegativeTuple (r : ℕ) :
    IsOpen {v : Fin r → H | (IsNegativeTuple A) v} := by
  let sphere := Metric.sphere (0 : Fin r → ℂ) 1
  let bad : Set ((Fin r → H) × sphere) :=
    {p | 0 ≤ (sectionQuadratic A) p.1 p.2}
  have hcont : Continuous
      (fun p : (Fin r → H) × sphere => (sectionQuadratic A) p.1 p.2) :=
    (continuous_sectionQuadratic A).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hclosed : IsClosed bad := isClosed_Ici.preimage hcont
  haveI : CompactSpace sphere :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Fin r → ℂ) 1)
  have hproj : IsClosed (Prod.fst '' bad) :=
    isClosedMap_fst_of_compactSpace _ hclosed
  rw [show {v : Fin r → H | (IsNegativeTuple A) v} = (Prod.fst '' bad)ᶜ by
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
    (hvD : ∀ i, v i ∈ D.topologicalClosure) (hv : (IsNegativeTuple A) v) :
    ∃ y : Fin r → H, (∀ i, y i ∈ D) ∧ (IsNegativeTuple A) y := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ((isOpen_isNegativeTuple A) r) v hv
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


variable {X Y : Type*}

lemma kernelForm_inner (f : X → H) (d : X →₀ ℂ) :
    kernelForm (fun x y => inner ℂ (f y) (A (f x))) d d =
      inner ℂ (Finsupp.linearCombination ℂ f d) (A (Finsupp.linearCombination ℂ f d)) := by
  classical
  simp only [kernelForm, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma synthesis_linearCombination {r : ℕ} (f : X → H) (d : Fin r → X →₀ ℂ)
    (c : Fin r → ℂ) :
    Finsupp.linearCombination ℂ f (∑ i, c i • d i) =
      sectionSynthesis (fun i => Finsupp.linearCombination ℂ f (d i)) c := by
  simp [sectionSynthesis]

lemma kernel_negative_iff_closedSpan (f : X → H) (r : ℕ) :
    HasFiniteKernelNegativeDimension (fun x y => inner ℂ (f y) (A (f x))) r ↔
    ∃ v : Fin r → H, (∀ i, v i ∈ (Submodule.span ℂ (range f)).topologicalClosure) ∧
      (IsNegativeTuple A) v := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨fun i => Finsupp.linearCombination ℂ f (d i), ?_, ?_⟩
    · intro i
      apply Submodule.le_topologicalClosure
      exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨d i, rfl⟩
    · intro c hc
      have hcne : c ≠ 0 := by intro hz; simp [hz] at hc
      have hh := hd c hcne
      rw [kernelForm_inner, synthesis_linearCombination] at hh
      exact hh
  · rintro ⟨v, hv, hn⟩
    obtain ⟨y, hy, hyn⟩ := (exists_negativeTuple_mem_of_mem_topologicalClosure A)
      (Submodule.span ℂ (range f)) v hv hn
    have hex : ∀ i, ∃ d : X →₀ ℂ, Finsupp.linearCombination ℂ f d = y i :=
      fun i => Finsupp.mem_span_range_iff_exists_finsupp.mp (hy i)
    choose d hd using hex
    refine ⟨d, fun c hc => ?_⟩
    rw [kernelForm_inner, synthesis_linearCombination]
    have heq : (fun i => Finsupp.linearCombination ℂ f (d i)) = y := funext hd
    rw [heq]
    exact (isNegativeTuple_quadratic_neg A) hyn hc

/-- Equal closed section spans preserve every finite negative dimension. -/
theorem kernel_negative_iff_of_closedSpan_eq (f : X → H) (g : Y → H)
    (h : (Submodule.span ℂ (range f)).topologicalClosure =
      (Submodule.span ℂ (range g)).topologicalClosure) (r : ℕ) :
    HasFiniteKernelNegativeDimension (fun x y => inner ℂ (f y) (A (f x))) r ↔
    HasFiniteKernelNegativeDimension (fun x y => inner ℂ (g y) (A (g x))) r := by
  rw [kernel_negative_iff_closedSpan, kernel_negative_iff_closedSpan, h]

lemma kernelForm_scale (K : X → X → ℂ) (a : ℂ) (d : X →₀ ℂ) :
    kernelForm (fun x y => a * K x y) d d = a * kernelForm K d d := by
  classical
  simp only [kernelForm, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma kernel_negative_scale_iff (K : X → X → ℂ) {a : ℝ} (ha : 0 < a) (r : ℕ) :
    HasFiniteKernelNegativeDimension (fun x y => (a:ℂ) * K x y) r ↔
      HasFiniteKernelNegativeDimension K r := by
  have he (d : X →₀ ℂ) :
      (kernelForm (fun x y => (a:ℂ) * K x y) d d).re =
        a * (kernelForm K d d).re := by
    rw [kernelForm_scale]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, fun c hc => ?_⟩
    have h := hd c hc
    rw [he] at h
    nlinarith
  · rintro ⟨d, hd⟩
    refine ⟨d, fun c hc => ?_⟩
    rw [he]
    exact mul_neg_of_pos_of_neg ha (hd c hc)

end GaloisForLFunctions.HTGeometry.KernelClosedSpanInertia
