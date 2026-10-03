import GaloisForLFunctions.HTGeometry.SourceCompleteTransience
import GaloisForLFunctions.HTGeometry.OperatorTraceAdjoint
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

/-!
# Source-complete corona conservation and properness selection

For positive trace-class defects `T_n` of bounded trace that asymptotically commute in trace norm with
a source-complete packet (**(SC.7)**) on a space with a Hilbert basis indexed by `ℕ`:

* the positive functionals `φ_n(K + c1) = tr(K T_n) + c tr T_n` on the unitization `𝒦 + ℂ1` converge
  weak-star to `m ω_∞`, `ω_∞(K + c1) = c` (**(SC.11)–(SC.16)**); every finite head loses its mass
  while the tails keep all of it (**(SC.17)–(SC.20)**);
* uniform source-tightness forces `‖T_n‖₁ → 0` (**(SC.21)–(SC.23)**), and so does a bounded proper
  spectral cost, while persistent trace makes every proper cost diverge (**(SC.24)–(SC.29a)**).

A proper cost `C ≥ 0` with compact resolvent is given by its spectral data: an orthonormal eigenbasis
`(f_k)` and eigenvalues `μ_k ≥ 0` with finite sublevel sets; its energy is
`E_C(T) = Σ_k μ_k ⟨f_k, T f_k⟩ ∈ [0, ∞]` (**(SC.25)**).
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate ENNReal ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Positivity of traces -/

theorem opTrace_nonneg_of_isPositive {T : E →L[ℂ] E} (hT : T.IsPositive) : 0 ≤ opTrace T :=
  tsum_nonneg fun _ => hT.inner_nonneg_right _

theorem opTrace_eq_ofReal_re_of_isPositive {T : E →L[ℂ] E} (hT : T.IsPositive) :
    opTrace T = ((opTrace T).re : ℂ) := by
  have h := opTrace_nonneg_of_isPositive hT
  rw [Complex.nonneg_iff] at h
  exact Complex.ext (by simp) (by simp [← h.2])

omit [CompleteSpace E] in
theorem inner_basis_nonneg_of_isPositive {T : E →L[ℂ] E} (hT : T.IsPositive) {ι : Type*}
    (f : HilbertBasis ι ℂ E) (k : ι) : 0 ≤ (⟪f k, T (f k)⟫_ℂ).re :=
  hT.re_inner_nonneg_right _

theorem hasSum_re_inner_basis {T : E →L[ℂ] E} (hS : MemSchattenClass 1 T) {ι : Type*}
    (f : HilbertBasis ι ℂ E) : HasSum (fun k => (⟪f k, T (f k)⟫_ℂ).re) (opTrace T).re := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS f]
  exact Complex.hasSum_re (hS.one_summable_inner_diag_basis f).hasSum

/-! ## The (SC.7) hypotheses -/

/-- **(SC.7)** Positive trace-class defects of bounded trace asymptotically commuting in trace norm
with the packet `A`. -/
structure IsAsymptoticallySourceInvariant {κ : Type*} (A : κ → E →L[ℂ] E) (T : ℕ → E →L[ℂ] E) :
    Prop where
  pos : ∀ n, (T n).IsPositive
  traceClass : ∀ n, MemSchattenClass 1 (T n)
  bdd : ∃ B, ∀ n, (opTrace (T n)).re ≤ B
  comm : ∀ a, Tendsto (fun n => traceNorm E (T n ∘L A a - A a ∘L T n)) atTop (𝓝 0)

namespace IsAsymptoticallySourceInvariant

variable {κ : Type*} {A : κ → E →L[ℂ] E} {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T)
include h

theorem traceNorm_eq (n : ℕ) : traceNorm E (T n) = (opTrace (T n)).re :=
  traceNorm_eq_re_opTrace_of_isPositive (h.traceClass n) (h.pos n)

theorem bdd_traceNorm : ∃ B, ∀ n, traceNorm E (T n) ≤ B :=
  let ⟨B, hB⟩ := h.bdd
  ⟨B, fun n => (h.traceNorm_eq n).trans_le (hB n)⟩

theorem tendsto_inner (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A) (x y : E) :
    Tendsto (fun n => ⟪x, T n y⟫_ℂ) atTop (𝓝 0) :=
  let ⟨_, hB⟩ := h.bdd_traceNorm
  tendsto_inner_of_isSourceComplete b hA T h.traceClass hB h.comm x y

/-- **(SC.8)** Compact-observer extinction. -/
theorem tendsto_opTrace_comp (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A) (K : E →L[ℂ] E)
    (hK : IsCompactOperator K) : Tendsto (fun n => opTrace (K ∘L T n)) atTop (𝓝 0) :=
  let ⟨_, hB⟩ := h.bdd_traceNorm
  tendsto_opTrace_comp_of_isSourceComplete b hA T h.traceClass hB h.comm K hK

theorem tendsto_re_inner_basis (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A) {ι : Type*}
    (f : HilbertBasis ι ℂ E) (k : ι) : Tendsto (fun n => (⟪f k, T n (f k)⟫_ℂ).re) atTop (𝓝 0) := by
  have h1 := (Complex.continuous_re.tendsto 0).comp (h.tendsto_inner b hA (f k) (f k))
  simp only [Function.comp_def, Complex.zero_re] at h1
  exact h1

end IsAsymptoticallySourceInvariant

/-! ## Normal/corona conservation -/

/-- In infinite dimension the identity is not compact: the basis is weakly null of norm one. -/
theorem not_isCompactOperator_id (b : HilbertBasis ℕ ℂ E) : ¬ IsCompactOperator (ContinuousLinearMap.id ℂ E) := by
  intro hK
  have hweak : ∀ z : E, Tendsto (fun n => ⟪z, b n⟫_ℂ) atTop (𝓝 0) := fun z => by
    have hs : Summable fun n => ‖b.repr z n‖ ^ 2 := summable_norm_sq_lp (b.repr z)
    have h0 := hs.tendsto_atTop_zero
    have h1 : Tendsto (fun n => ‖⟪b n, z⟫_ℂ‖) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h0
      simp only [Real.sqrt_zero] at this
      refine this.congr fun n => ?_
      simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _), HilbertBasis.repr_apply_apply]
    refine tendsto_zero_iff_norm_tendsto_zero.2 (h1.congr fun n => ?_)
    rw [← inner_conj_symm, Complex.norm_conj]
  have h := tendsto_norm_compact_of_weaklyNull (ContinuousLinearMap.id ℂ E) hK (fun n => b n)
    (fun n => (b.orthonormal.1 n).le) hweak
  have h2 := (continuous_norm.tendsto 0).comp h
  simp only [Function.comp_def, id_apply, norm_zero, b.orthonormal.1] at h2
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h2)

/-- **(SC.11)–(SC.12)** On `𝒦(E) + ℂ1` the scalar part is well defined, so the corona character
`ω_∞(K + c1) = c` is well defined. -/
theorem unitization_scalar_unique (b : HilbertBasis ℕ ℂ E) {K K' : E →L[ℂ] E} (hK : IsCompactOperator K)
    (hK' : IsCompactOperator K') {c c' : ℂ}
    (h : K + c • ContinuousLinearMap.id ℂ E = K' + c' • ContinuousLinearMap.id ℂ E) : c = c' := by
  by_contra hne
  have hid : ContinuousLinearMap.id ℂ E = (c - c')⁻¹ • (K' - K) := by
    have h2 : (c - c') • ContinuousLinearMap.id ℂ E = K' - K := by
      rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm (c • ContinuousLinearMap.id ℂ E) K]
      exact h
    rw [← h2, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul]
  apply not_isCompactOperator_id b
  rw [hid]
  exact (hK'.sub hK).smul _

theorem opTrace_smul_eq (c : ℂ) (T : E →L[ℂ] E) : opTrace (c • T) = c * opTrace T := by
  simp only [opTrace, smul_apply, inner_smul_right, tsum_mul_left]

theorem opTrace_unitization {T : E →L[ℂ] E} (hT : MemSchattenClass 1 T) (K : E →L[ℂ] E) (c : ℂ) :
    opTrace ((K + c • ContinuousLinearMap.id ℂ E) ∘L T) = opTrace (K ∘L T) + c * opTrace T := by
  rw [add_comp, smul_comp, id_comp, opTrace_add_of_memSchattenClass_one (memSchattenClass_one_comp_left hT K)
    (memSchattenClass_one_smul hT c), opTrace_smul_eq]

/-- **Theorem 4.1 (SC.14)–(SC.16) Trace becomes corona mass.**  If `tr T_n → m`, the functionals
`φ_n(K + c1) = tr((K + c1) T_n) = tr(K T_n) + c tr T_n` converge to `m ω_∞(K + c1) = c m`. -/
theorem IsAsymptoticallySourceInvariant.tendsto_unitization {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) {m : ℝ} (hm : Tendsto (fun n => (opTrace (T n)).re) atTop (𝓝 m))
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (c : ℂ) :
    Tendsto (fun n => opTrace ((K + c • ContinuousLinearMap.id ℂ E) ∘L T n)) atTop (𝓝 (c * m)) := by
  have hm' : Tendsto (fun n => opTrace (T n)) atTop (𝓝 (m : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto m).comp hm
    exact this.congr fun n => (opTrace_eq_ofReal_re_of_isPositive (h.pos n)).symm
  have h1 := (h.tendsto_opTrace_comp b hA K hK).add (hm'.const_mul c)
  rw [zero_add] at h1
  exact h1.congr fun n => (opTrace_unitization (h.traceClass n) K c).symm

/-- A positive bounded observer has nonnegative trace against a positive trace-class defect:
`tr(X T) = tr(R X R)` with `R = T^{1/2}`. -/
theorem re_opTrace_comp_nonneg {X T : E →L[ℂ] E} (hX : X.IsPositive) (hT : T.IsPositive)
    (hS : MemSchattenClass 1 T) : 0 ≤ (opTrace (X ∘L T)).re := by
  set R := CFC.sqrt T
  have hT0 : 0 ≤ T := (nonneg_iff_isPositive T).2 hT
  have hRR : R ∘L R = T := CFC.sqrt_mul_sqrt_self T hT0
  have hRpos : R.IsPositive := (nonneg_iff_isPositive R).1 (CFC.sqrt_nonneg T)
  have hR : R.IsHilbertSchmidt := by
    have habs : absOp T = T := by
      rw [absOp, hT.isSelfAdjoint.star_eq, ← sq, CFC.sqrt_sq T hT0]
    have := traceClassRoot_isHilbertSchmidt hS
    rwa [traceClassRoot, habs] at this
  have hcyc : opTrace (X ∘L T) = opTrace (R ∘L X ∘L R) := by
    rw [← hRR, ← comp_assoc, opTrace_comp_comm (hR.comp_left X) hR]
  rw [hcyc]
  have hpos : (R ∘L X ∘L R).IsPositive := by
    have := hX.conj_adjoint R
    rwa [hRpos.isSelfAdjoint.adjoint_eq] at this
  exact (Complex.nonneg_iff.1 (opTrace_nonneg_of_isPositive hpos)).1

/-- **Theorem 4.1** When `tr T_n = 1` each `φ_n` is a state on the unitization: it is positive and
normalized. -/
theorem unitization_isState {T : E →L[ℂ] E} (hT : T.IsPositive) (hS : MemSchattenClass 1 T)
    (h1 : opTrace T = 1) :
    opTrace ((0 + (1 : ℂ) • ContinuousLinearMap.id ℂ E) ∘L T) = 1 ∧
      ∀ X : E →L[ℂ] E, X.IsPositive → 0 ≤ (opTrace (X ∘L T)).re := by
  refine ⟨?_, fun X hX => re_opTrace_comp_nonneg hX hT hS⟩
  rw [zero_add, one_smul, id_comp, h1]

/-! ## Finite heads and tails -/

/-- **(SC.17)** The finite source-head projection `Q_r = Σ_{i ≤ r} |b_i⟩⟨b_i|`. -/
def basisHead (b : HilbertBasis ℕ ℂ E) (r : ℕ) : E →L[ℂ] E :=
  ∑ i ∈ Finset.range (r + 1), InnerProductSpace.rankOne ℂ (b i) (b i)

omit [CompleteSpace E] in
theorem basisHead_apply (b : HilbertBasis ℕ ℂ E) (r : ℕ) (x : E) :
    basisHead b r x = ∑ i ∈ Finset.range (r + 1), ⟪b i, x⟫_ℂ • b i := by
  simp [basisHead, InnerProductSpace.rankOne_apply]

omit [CompleteSpace E] in
theorem basisHead_basis (b : HilbertBasis ℕ ℂ E) (r k : ℕ) :
    basisHead b r (b k) = if k ≤ r then b k else 0 := by
  rw [basisHead_apply]
  simp_rw [orthonormal_iff_ite.1 b.orthonormal, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

omit [CompleteSpace E] in
theorem isCompactOperator_basisHead (b : HilbertBasis ℕ ℂ E) (r : ℕ) : IsCompactOperator (basisHead b r) := by
  set v : Fin (r + 1) → E := fun i => b i
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  refine isCompactOperator_of_hasRankLE (n := r + 1) ⟨Submodule.span ℂ (Set.range v), inferInstance,
    (_root_.finrank_range_le_card v).trans (by simp), fun x => ?_⟩
  rw [basisHead_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.mem_range] at hi
  exact ⟨⟨i, hi⟩, rfl⟩

theorem opTrace_comp_basisHead (b : HilbertBasis ℕ ℂ E) {T : E →L[ℂ] E} (hT : MemSchattenClass 1 T) (r : ℕ) :
    opTrace (T ∘L basisHead b r) = ∑ i ∈ Finset.range (r + 1), ⟪b i, T (b i)⟫_ℂ := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one (hT.one_comp_right _) b,
    tsum_eq_sum (s := Finset.range (r + 1)) fun i hi => ?_]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [comp_apply, basisHead_basis, if_pos (by omega)]
  · rw [Finset.mem_range] at hi
    rw [comp_apply, basisHead_basis, if_neg (by omega), map_zero, inner_zero_right]

theorem opTrace_basisHead_comp (b : HilbertBasis ℕ ℂ E) {T : E →L[ℂ] E} (hT : MemSchattenClass 1 T) (r : ℕ) :
    opTrace (basisHead b r ∘L T) = ∑ i ∈ Finset.range (r + 1), ⟪b i, T (b i)⟫_ℂ := by
  rw [hT.one_opTrace_comp_comm, opTrace_comp_basisHead b hT]

/-- **(SC.20)** `tr T = tr(Q_r T) + tr((1 - Q_r)T)`. -/
theorem opTrace_head_add_tail (b : HilbertBasis ℕ ℂ E) {T : E →L[ℂ] E} (hT : MemSchattenClass 1 T) (r : ℕ) :
    opTrace T = opTrace (basisHead b r ∘L T) +
      opTrace ((ContinuousLinearMap.id ℂ E - basisHead b r) ∘L T) := by
  rw [sub_comp, id_comp, opTrace_sub_of_memSchattenClass_one hT (memSchattenClass_one_comp_left hT _)]
  ring

/-- **Corollary 4.2 (SC.18)–(SC.19) Exact head/tail conservation.**  Every finite head loses its
mass, `tr(Q_r T_n) → 0`, and the tails keep it: `tr((1 - Q_r)T_n) → m` for every `r`, so
`lim_r lim_n tr((1 - Q_r)T_n) = m`. -/
theorem IsAsymptoticallySourceInvariant.head_tail {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) {m : ℝ} (hm : Tendsto (fun n => (opTrace (T n)).re) atTop (𝓝 m)) :
    (∀ r, Tendsto (fun n => opTrace (basisHead b r ∘L T n)) atTop (𝓝 0)) ∧
    (∀ r, Tendsto (fun n => (opTrace ((ContinuousLinearMap.id ℂ E - basisHead b r) ∘L T n)).re)
      atTop (𝓝 m)) ∧
    Tendsto (fun r => limUnder atTop fun n =>
      (opTrace ((ContinuousLinearMap.id ℂ E - basisHead b r) ∘L T n)).re) atTop (𝓝 m) := by
  have hhead : ∀ r, Tendsto (fun n => opTrace (basisHead b r ∘L T n)) atTop (𝓝 0) := fun r =>
    h.tendsto_opTrace_comp b hA _ (isCompactOperator_basisHead b r)
  have htail : ∀ r, Tendsto (fun n => (opTrace ((ContinuousLinearMap.id ℂ E - basisHead b r) ∘L T n)).re)
      atTop (𝓝 m) := fun r => by
    have h1 := hm.sub ((Complex.continuous_re.tendsto 0).comp (hhead r))
    simp only [Complex.zero_re, sub_zero] at h1
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [opTrace_head_add_tail b (h.traceClass n) r, Complex.add_re]
    ring
  exact ⟨hhead, htail, tendsto_const_nhds.congr fun r => ((htail r).limUnder_eq).symm⟩

/-- **(SC.21)** Uniform source-tightness. -/
def IsSourceTight (b : HilbertBasis ℕ ℂ E) (T : ℕ → E →L[ℂ] E) : Prop :=
  ∀ ε > 0, ∃ r, ∀ n, (opTrace ((ContinuousLinearMap.id ℂ E - basisHead b r) ∘L T n)).re ≤ ε

/-- **Theorem 5.2 (SC.22) Tight source-complete defects become extinct.** -/
theorem IsAsymptoticallySourceInvariant.tendsto_traceNorm_of_tight {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) (ht : IsSourceTight b T) :
    Tendsto (fun n => traceNorm E (T n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr⟩ := ht (ε / 2) (by positivity)
  have hhead := (Complex.continuous_re.tendsto 0).comp
    (h.tendsto_opTrace_comp b hA _ (isCompactOperator_basisHead b r))
  rw [Complex.zero_re] at hhead
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hhead (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  simp only [Function.comp_apply, Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (traceNorm_nonneg _), h.traceNorm_eq n,
    opTrace_head_add_tail b (h.traceClass n) r, Complex.add_re]
  linarith [hr n, (abs_lt.1 h1).2]

/-! ## Proper spectral costs -/

/-- **(SC.25)** The extended energy `E_C(T) = Σ_k μ_k ⟨f_k, T f_k⟩` of a cost with eigenbasis `f` and
eigenvalues `μ`. -/
def properCostEnergy {κ : Type*} (f : HilbertBasis κ ℂ E) (μ : κ → ℝ) (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (μ k * (⟪f k, T (f k)⟫_ℂ).re)

/-- A nonnegative cost with compact resolvent: eigenvalues `μ_k ≥ 0` tending to infinity with finite
multiplicity. -/
structure IsProperSpectrum {κ : Type*} (μ : κ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ μ k
  finite_sublevel : ∀ M, {k | μ k ≤ M}.Finite

/-- **(SC.27), (SC.29a) Markov bound.**  If `μ_k ≥ M` off a finite set `S`, the trace outside `S`
costs at least `M` per unit: `M (tr T - Σ_{k ∈ S} ⟨f_k, T f_k⟩) ≤ E_C(T)`. -/
theorem ofReal_mul_tail_le_properCostEnergy {κ : Type*} (f : HilbertBasis κ ℂ E) {μ : κ → ℝ}
    (hμ0 : ∀ k, 0 ≤ μ k) {T : E →L[ℂ] E} (hT : T.IsPositive) (hS : MemSchattenClass 1 T) {M : ℝ}
    (hM : 0 ≤ M) (S : Finset κ) (hSM : ∀ k ∉ S, M ≤ μ k) :
    ENNReal.ofReal (M * ((opTrace T).re - ∑ k ∈ S, (⟪f k, T (f k)⟫_ℂ).re)) ≤ properCostEnergy f μ T := by
  classical
  set a : κ → ℝ := fun k => (⟪f k, T (f k)⟫_ℂ).re with hadef
  have ha0 : ∀ k, 0 ≤ a k := fun k => inner_basis_nonneg_of_isPositive hT f k
  have hsum := hasSum_re_inner_basis hS f
  set g : κ → ℝ := fun k => if k ∈ S then 0 else a k with hgdef
  have h1 : HasSum (fun k => if k ∈ S then a k else 0) (∑ k ∈ S, a k) := by
    have h1' : HasSum (fun k => if k ∈ S then a k else 0) (∑ k ∈ S, (if k ∈ S then a k else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => if_neg hk)
    rwa [Finset.sum_congr rfl fun k hk => if_pos hk] at h1'
  have hg : HasSum g ((opTrace T).re - ∑ k ∈ S, a k) :=
    (hsum.sub h1).congr_fun fun k => by by_cases hk : k ∈ S <;> simp [hgdef, hadef, hk]
  have hg0 : ∀ k, 0 ≤ g k := fun k => by by_cases hk : k ∈ S <;> simp [hgdef, hk, ha0 k]
  rw [← hg.tsum_eq, ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hM (hg0 k))
    (hg.summable.mul_left M)]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  by_cases hk : k ∈ S
  · simp only [hgdef, hk, if_true, mul_zero]
    exact mul_nonneg (hμ0 k) (ha0 k)
  · simp only [hgdef, hk, if_false]
    exact mul_le_mul_of_nonneg_right (hSM k hk) (ha0 k)

theorem notMem_sublevel {κ : Type*} {μ : κ → ℝ} (hμ : IsProperSpectrum μ) (M : ℝ) (k : κ)
    (hk : k ∉ (hμ.finite_sublevel M).toFinset) : M ≤ μ k := by
  by_contra hlt
  exact hk ((hμ.finite_sublevel M).mem_toFinset.2 (not_le.1 hlt).le)

theorem IsAsymptoticallySourceInvariant.tendsto_head {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) {ι : Type*} (f : HilbertBasis ι ℂ E) (S : Finset ι) :
    Tendsto (fun n => ∑ k ∈ S, (⟪f k, T n (f k)⟫_ℂ).re) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ _k ∈ S, (0 : ℝ) by simp]
  exact tendsto_finsetSum _ fun k _ => h.tendsto_re_inner_basis b hA f k

/-- **Corollary 5.4 (1) / Theorem 5.3 (1).**  A bounded proper cost forces `‖T_n‖₁ → 0`. -/
theorem IsAsymptoticallySourceInvariant.tendsto_traceNorm_of_bounded_energy {κ : Type*}
    {A : κ → E →L[ℂ] E} {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T)
    (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A) {ι : Type*} (f : HilbertBasis ι ℂ E)
    {μ : ι → ℝ} (hμ : IsProperSpectrum μ) {C : ℝ} (hC : ∀ n, properCostEnergy f μ (T n) ≤ ENNReal.ofReal C) :
    Tendsto (fun n => traceNorm E (T n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C' := max C 0
  set M := 2 * (C' + 1) / ε with hMdef
  have hM : 0 < M := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h.tendsto_head b hA f (hμ.finite_sublevel M).toFinset)
    (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1
  have h2 := (ofReal_mul_tail_le_properCostEnergy f hμ.nonneg (h.pos n) (h.traceClass n) hM.le _
    (notMem_sublevel hμ M)).trans
    ((hC n).trans (ENNReal.ofReal_le_ofReal (le_max_left C 0)))
  rw [ENNReal.ofReal_le_ofReal_iff (le_max_right C 0)] at h2
  have h3 : (opTrace (T n)).re - ∑ k ∈ (hμ.finite_sublevel M).toFinset, (⟪f k, T n (f k)⟫_ℂ).re < ε / 2 := by
    by_contra hge
    push Not at hge
    have : M * (ε / 2) ≤ C' := (mul_le_mul_of_nonneg_left hge hM.le).trans h2
    rw [hMdef, div_mul_eq_mul_div, div_le_iff₀ hε] at this
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (traceNorm_nonneg _), h.traceNorm_eq n]
  linarith [(abs_lt.1 h1).2]

/-- **Corollary 5.4 (2) / Theorem 5.3 (2) (SC.26), (SC.28)–(SC.29).**  Persistent trace `m > 0` makes
every proper cost diverge. -/
theorem IsAsymptoticallySourceInvariant.tendsto_properCostEnergy_top {κ : Type*}
    {A : κ → E →L[ℂ] E} {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T)
    (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A) {ι : Type*} (f : HilbertBasis ι ℂ E)
    {μ : ι → ℝ} (hμ : IsProperSpectrum μ) {m : ℝ} (hm0 : 0 < m)
    (hm : Tendsto (fun n => (opTrace (T n)).re) atTop (𝓝 m)) :
    Tendsto (fun n => properCostEnergy f μ (T n)) atTop (𝓝 ⊤) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => absurd ha not_top_lt⟩
  set M := 2 * (a.toReal + 1) / m with hMdef
  have hM : 0 < M := by positivity
  have hhead := h.tendsto_head b hA f (hμ.finite_sublevel M).toFinset
  filter_upwards [hhead.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < m / 4)),
    hm.eventually (lt_mem_nhds (by linarith : 3 * m / 4 < m))] with n h1 h2
  refine lt_of_lt_of_le ?_ (ofReal_mul_tail_le_properCostEnergy f hμ.nonneg (h.pos n) (h.traceClass n) hM.le
    _ (notMem_sublevel hμ M))
  rw [← ENNReal.ofReal_toReal ha.ne_top, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
  have h3 : m / 2 < (opTrace (T n)).re - ∑ k ∈ (hμ.finite_sublevel M).toFinset, (⟪f k, T n (f k)⟫_ℂ).re := by
    linarith
  calc a.toReal < a.toReal + 1 := by linarith
    _ = M * (m / 2) := by rw [hMdef]; field_simp
    _ < M * _ := mul_lt_mul_of_pos_left h3 hM

/-- A diagonal cost `C e_j = c_j e_j` with `c` increasing, positive and unbounded is proper. -/
theorem isProperSpectrum_of_monotone {c : ℕ → ℝ} (hpos : ∀ j, 0 < c j) (htop : Tendsto c atTop atTop) :
    IsProperSpectrum c := by
  refine ⟨fun j => (hpos j).le, fun M => ?_⟩
  obtain ⟨N, hN⟩ := (htop.eventually (eventually_gt_atTop M)).exists_forall_of_atTop
  exact (Set.finite_lt_nat N).subset fun j (hj : c j ≤ M) => by
    by_contra hge
    exact absurd (hN j (not_lt.1 hge)) (not_lt.2 hj)

/-- **(SC.27)** For an increasing diagonal cost, the tail beyond the head `Q_r` costs at least
`c_{r+1}` per unit: `c_{r+1} tr((1 - Q_r)T) ≤ E_C(T)`. -/
theorem ofReal_mul_tail_basisHead_le {c : ℕ → ℝ} (hc : Monotone c) (hpos : ∀ j, 0 < c j)
    (b : HilbertBasis ℕ ℂ E) {T : E →L[ℂ] E} (hT : T.IsPositive) (hS : MemSchattenClass 1 T) (r : ℕ) :
    ENNReal.ofReal (c (r + 1) * (opTrace ((ContinuousLinearMap.id ℂ E - basisHead b r) ∘L T)).re) ≤
      properCostEnergy b c T := by
  have htail : (opTrace ((ContinuousLinearMap.id ℂ E - basisHead b r) ∘L T)).re =
      (opTrace T).re - ∑ k ∈ Finset.range (r + 1), (⟪b k, T (b k)⟫_ℂ).re := by
    rw [sub_comp, id_comp, opTrace_sub_of_memSchattenClass_one hS (memSchattenClass_one_comp_left hS _),
      opTrace_basisHead_comp b hS, Complex.sub_re, Complex.re_sum]
  rw [htail]
  refine ofReal_mul_tail_le_properCostEnergy b (fun j => (hpos j).le) hT hS (hpos (r + 1)).le
    (Finset.range (r + 1)) fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  exact hc hk

end GaloisForLFunctions.HTGeometry
