import GaloisForLFunctions.HTGeometry.SourceCompleteCoronaProperness
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed

/-!
# Source-complete fusion, recovery neutrality and compact Gram collapse

* **Positive fusion (§6).**  Finite nonnegative combinations of asymptotically source-invariant defects
  are again asymptotically source-invariant; compact extinction, corona mass and proper cost add
  (**(SC.30)–(SC.33)**), and a persistent component cannot be cancelled by positive fusion
  (**(SC.33a)–(SC.33c)**).
* **Recovery neutrality (§7).**  An isometric corner embedding `X ↦ VXV*` preserves traces,
  commutator trace norms, compact pairings (`tr(K' VTV*) = tr((V*K'V)T)`) and the energy of the
  recovered cost `VCV* ⊕ D` (**(SC.34)–(SC.39)**).
* **Compact Gram collapse (§8).**  For compact reporters `A_i` the Gram matrices
  `G_n(i,j) = tr(T_n A_i* A_j)` are positive semidefinite and tend to zero, with all principal minors
  and eigenvalues (**(SC.40)–(SC.42)**).
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate ENNReal ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Finite sums of trace-class operators -/

theorem memSchattenClass_one_finset_sum {ι : Type*} (s : Finset ι) {X : ι → E →L[ℂ] E}
    (hX : ∀ i ∈ s, MemSchattenClass 1 (X i)) :
    MemSchattenClass 1 (∑ i ∈ s, X i) ∧ traceNorm E (∑ i ∈ s, X i) ≤ ∑ i ∈ s, traceNorm E (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : ∀ n, approxNumber (0 : E →L[ℂ] E) n = 0 := fun n =>
      le_antisymm ((approxNumber_le_norm _ n).trans (by simp)) (approxNumber_nonneg _ n)
    refine ⟨?_, by rw [traceNorm_zero]⟩
    unfold MemSchattenClass
    simp only [h0, Real.zero_rpow one_ne_zero]
    exact summable_zero
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hX i (Finset.mem_insert_of_mem hi)
    have hXa := hX a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨memSchattenClass_one_add (hXa.isCompactOperator one_pos) (h1.isCompactOperator one_pos) hXa h1, ?_⟩
    refine (traceNorm_add_le (hXa.isCompactOperator one_pos) (h1.isCompactOperator one_pos)
      hXa.one_summable_approxNumber h1.one_summable_approxNumber).trans ?_
    linarith

theorem opTrace_finset_sum {ι : Type*} (s : Finset ι) {X : ι → E →L[ℂ] E}
    (hX : ∀ i ∈ s, MemSchattenClass 1 (X i)) : opTrace (∑ i ∈ s, X i) = ∑ i ∈ s, opTrace (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTrace]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      opTrace_add_of_memSchattenClass_one (hX a (Finset.mem_insert_self a s))
        (memSchattenClass_one_finset_sum s fun i hi => hX i (Finset.mem_insert_of_mem hi)).1,
      ih fun i hi => hX i (Finset.mem_insert_of_mem hi)]

/-! ## Positive fusion -/

section Fusion

variable {κ : Type*} {A : κ → E →L[ℂ] E} {ι : Type*} (s : Finset ι) (Tf : ι → ℕ → E →L[ℂ] E)
  (α : ι → ℝ)

/-- **(SC.30)** The fused defect `S_n = Σ_a α_a T_n^{(a)}`. -/
def fusedDefect (n : ℕ) : E →L[ℂ] E := ∑ a ∈ s, ((α a : ℝ) : ℂ) • Tf a n

omit [CompleteSpace E] in
theorem fusedDefect_comm (n : ℕ) (B : E →L[ℂ] E) :
    fusedDefect s Tf α n ∘L B - B ∘L fusedDefect s Tf α n =
      ∑ a ∈ s, ((α a : ℝ) : ℂ) • (Tf a n ∘L B - B ∘L Tf a n) := by
  ext1 x
  simp only [fusedDefect, comp_apply, sub_apply, sum_apply, smul_apply, map_sum, map_smul,
    ← Finset.sum_sub_distrib, smul_sub]

variable {s Tf α}

/-- **Theorem 6.1 (SC.30), (SC.33)** Positive fusion preserves the (SC.7) hypotheses. -/
theorem IsAsymptoticallySourceInvariant.fusion (hα : ∀ a, 0 ≤ α a)
    (h : ∀ a ∈ s, IsAsymptoticallySourceInvariant A (Tf a)) :
    IsAsymptoticallySourceInvariant A (fusedDefect s Tf α) := by
  have hS : ∀ n, ∀ a ∈ s, MemSchattenClass 1 (((α a : ℝ) : ℂ) • Tf a n) := fun n a ha =>
    memSchattenClass_one_smul ((h a ha).traceClass n) _
  refine ⟨fun n => ?_, fun n => (memSchattenClass_one_finset_sum s (hS n)).1, ?_, fun c => ?_⟩
  · exact isPositive_sum s fun a ha => ((h a ha).pos n).smul_of_nonneg (by exact_mod_cast hα a)
  · choose B hB using fun a (ha : a ∈ s) => (h a ha).bdd
    refine ⟨∑ a ∈ s.attach, α a * B a.1 a.2, fun n => ?_⟩
    rw [fusedDefect, opTrace_finset_sum s (hS n), Complex.re_sum, ← Finset.sum_attach]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [opTrace_smul_eq, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (hB a.1 a.2 n) (hα a)
  · have hbound : ∀ n, traceNorm E (fusedDefect s Tf α n ∘L A c - A c ∘L fusedDefect s Tf α n) ≤
        ∑ a ∈ s, α a * traceNorm E (Tf a n ∘L A c - A c ∘L Tf a n) := fun n => by
      rw [fusedDefect_comm]
      refine (memSchattenClass_one_finset_sum s fun a ha => memSchattenClass_one_smul
        (memSchattenClass_one_comp_sub_comp ((h a ha).traceClass n) _) _).2.trans
        (Finset.sum_le_sum fun a _ => ?_)
      rw [traceNorm_smul, Complex.norm_real, Real.norm_of_nonneg (hα a)]
    refine squeeze_zero (fun n => traceNorm_nonneg _) hbound ?_
    rw [show (0 : ℝ) = ∑ a ∈ s, α a * 0 by simp]
    exact tendsto_finsetSum _ fun a ha => ((h a ha).comm c).const_mul _

/-- **(SC.31)** Fused corona mass: `tr(K S_n) → 0` for compact `K`, and the unitization functionals
of `S_n` converge to `(Σ_a α_a m_a) ω_∞`. -/
theorem IsAsymptoticallySourceInvariant.fusion_corona (hα : ∀ a, 0 ≤ α a)
    (h : ∀ a ∈ s, IsAsymptoticallySourceInvariant A (Tf a)) (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A)
    {m : ι → ℝ} (hm : ∀ a ∈ s, Tendsto (fun n => (opTrace (Tf a n)).re) atTop (𝓝 (m a)))
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (c : ℂ) :
    Tendsto (fun n => opTrace (K ∘L fusedDefect s Tf α n)) atTop (𝓝 0) ∧
    Tendsto (fun n => opTrace ((K + c • ContinuousLinearMap.id ℂ E) ∘L fusedDefect s Tf α n)) atTop
      (𝓝 (c * ((∑ a ∈ s, α a * m a : ℝ) : ℂ))) := by
  have hF := IsAsymptoticallySourceInvariant.fusion hα h
  refine ⟨hF.tendsto_opTrace_comp b hA K hK, hF.tendsto_unitization b hA ?_ K hK c⟩
  have hS : ∀ n, ∀ a ∈ s, MemSchattenClass 1 (((α a : ℝ) : ℂ) • Tf a n) := fun n a ha =>
    memSchattenClass_one_smul ((h a ha).traceClass n) _
  have hsum := tendsto_finsetSum s fun a ha => (hm a ha).const_mul (α a)
  refine hsum.congr fun n => ?_
  rw [fusedDefect, opTrace_finset_sum s (hS n), Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [opTrace_smul_eq, Complex.re_ofReal_mul]

omit [CompleteSpace E] in
/-- **(SC.32)** Proper cost fuses additively: `E_C(S_n) = Σ_a α_a E_C(T_n^{(a)})`. -/
theorem properCostEnergy_fusedDefect {κ' : Type*} (f : HilbertBasis κ' ℂ E) {μ : κ' → ℝ}
    (hμ : ∀ k, 0 ≤ μ k) (hα : ∀ a, 0 ≤ α a) (hpos : ∀ a ∈ s, ∀ n, (Tf a n).IsPositive) (n : ℕ) :
    properCostEnergy f μ (fusedDefect s Tf α n) = ∑ a ∈ s, ENNReal.ofReal (α a) * properCostEnergy f μ (Tf a n) := by
  have hterm : ∀ k, ENNReal.ofReal (μ k * (⟪f k, fusedDefect s Tf α n (f k)⟫_ℂ).re) =
      ∑ a ∈ s, ENNReal.ofReal (α a) * ENNReal.ofReal (μ k * (⟪f k, Tf a n (f k)⟫_ℂ).re) := fun k => by
    have hlin : (⟪f k, fusedDefect s Tf α n (f k)⟫_ℂ).re = ∑ a ∈ s, α a * (⟪f k, Tf a n (f k)⟫_ℂ).re := by
      simp only [fusedDefect, sum_apply, smul_apply, inner_sum, inner_smul_right, Complex.re_sum,
        Complex.re_ofReal_mul]
    rw [hlin, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun a ha =>
      mul_nonneg (hμ k) (mul_nonneg (hα a) (inner_basis_nonneg_of_isPositive (hpos a ha n) f k))]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← ENNReal.ofReal_mul (hα a)]
    ring_nf
  simp_rw [properCostEnergy, hterm]
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  exact Finset.sum_congr rfl fun a _ => ENNReal.tsum_mul_left

/-- **Corollary 6.2 (SC.33a)–(SC.33c) Positive fusion has no cancellation channel.**  With all
`α_a > 0`: bounded fused energy extinguishes every component; a persistent component makes the
fused energy diverge. -/
theorem IsAsymptoticallySourceInvariant.fusion_no_cancellation (hα : ∀ a, 0 < α a)
    (h : ∀ a ∈ s, IsAsymptoticallySourceInvariant A (Tf a)) (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A)
    {κ' : Type*} (f : HilbertBasis κ' ℂ E) {μ : κ' → ℝ} (hμ : IsProperSpectrum μ) :
    ((∃ C, ∀ n, properCostEnergy f μ (fusedDefect s Tf α n) ≤ ENNReal.ofReal C) →
      ∀ a ∈ s, Tendsto (fun n => traceNorm E (Tf a n)) atTop (𝓝 0)) ∧
    (∀ a ∈ s, ∀ {m : ℝ}, 0 < m → Tendsto (fun n => (opTrace (Tf a n)).re) atTop (𝓝 m) →
      Tendsto (fun n => properCostEnergy f μ (fusedDefect s Tf α n)) atTop (𝓝 ⊤)) := by
  have hle : ∀ a ∈ s, ∀ n, ENNReal.ofReal (α a) * properCostEnergy f μ (Tf a n) ≤
      properCostEnergy f μ (fusedDefect s Tf α n) := fun a ha n => by
    rw [properCostEnergy_fusedDefect f hμ.nonneg (fun a => (hα a).le) (fun a ha => (h a ha).pos)]
    exact Finset.single_le_sum (f := fun a => ENNReal.ofReal (α a) * properCostEnergy f μ (Tf a n))
      (fun _ _ => bot_le) ha
  refine ⟨fun ⟨C, hC⟩ a ha => ?_, fun a ha m hm0 hm => ?_⟩
  · refine (h a ha).tendsto_traceNorm_of_bounded_energy b hA f hμ (C := C / α a) fun n => ?_
    have h1 := (hle a ha n).trans (hC n)
    have hα0 : ENNReal.ofReal (α a) ≠ 0 := (ENNReal.ofReal_pos.2 (hα a)).ne'
    calc properCostEnergy f μ (Tf a n)
        = (ENNReal.ofReal (α a))⁻¹ * (ENNReal.ofReal (α a) * properCostEnergy f μ (Tf a n)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hα0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (α a))⁻¹ * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal (C / α a) := by
          rw [ENNReal.ofReal_div_of_pos (hα a), div_eq_mul_inv, mul_comm]
  · have htop := (h a ha).tendsto_properCostEnergy_top b hA f hμ hm0 hm
    have h2 : Tendsto (fun n => ENNReal.ofReal (α a) * properCostEnergy f μ (Tf a n)) atTop (𝓝 ⊤) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (α a)) htop (Or.inl ENNReal.top_ne_zero)
      rwa [ENNReal.mul_top (ENNReal.ofReal_pos.2 (hα a)).ne'] at this
    exact tendsto_nhds_top_mono h2 (Eventually.of_forall (hle a ha))

end Fusion

/-! ## Common recovery and functional-equation action -/

section Recovery

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
variable {V : E →L[ℂ] E'} (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ E)
include hV

theorem adjoint_comp_comp_of_isometry {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (Z : F →L[ℂ] E) : adjoint V ∘L (V ∘L Z) = Z := by
  rw [← comp_assoc, hV, id_comp]

theorem cornerConj_comp (X Y : E →L[ℂ] E) :
    cornerConj V X ∘L cornerConj V Y = cornerConj V (X ∘L Y) := by
  simp only [cornerConj, comp_assoc, adjoint_comp_comp_of_isometry hV]

theorem cornerConj_commutator (X Y : E →L[ℂ] E) :
    cornerConj V X ∘L cornerConj V Y - cornerConj V Y ∘L cornerConj V X = cornerConj V (X ∘L Y - Y ∘L X) := by
  rw [cornerConj_comp hV, cornerConj_comp hV]
  simp only [cornerConj, comp_sub, sub_comp]

theorem inner_map_map_of_adjoint_comp (x y : E) : ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← adjoint_inner_right, ← comp_apply, hV, id_apply]

/-- **Theorem 7.1 (SC.35)–(SC.37) Isometric common recovery is information-neutral.**  The corner
embedding preserves the trace, the commutator trace norms, and compact pairings
`tr(K' VTV*) = tr((V*K'V)T)`. -/
theorem recovery_invariants {T : E →L[ℂ] E} (hT : MemSchattenClass 1 T) (L : E →L[ℂ] E) :
    opTrace (cornerConj V T) = opTrace T ∧
    traceNorm E' (cornerConj V T ∘L cornerConj V L - cornerConj V L ∘L cornerConj V T) =
      traceNorm E (T ∘L L - L ∘L T) ∧
    ∀ K' : E' →L[ℂ] E', opTrace (K' ∘L cornerConj V T) = opTrace ((adjoint V ∘L K' ∘L V) ∘L T) := by
  refine ⟨opTrace_cornerConj hV hT, by rw [cornerConj_commutator hV, traceNorm_cornerConj hV], fun K' => ?_⟩
  obtain ⟨S, U, hS, hU, rfl⟩ := hT.one_isTraceClass
  have h1 : K' ∘L cornerConj V (S ∘L U) = (K' ∘L V ∘L S) ∘L (U ∘L adjoint V) := by
    simp only [cornerConj, comp_assoc]
  have h2 : (U ∘L adjoint V) ∘L (K' ∘L V ∘L S) = U ∘L ((adjoint V ∘L K' ∘L V) ∘L S) := by
    simp only [comp_assoc]
  rw [h1, ← opTrace_comp_comm (hU.comp_right (adjoint V)) ((hS.comp_left V).comp_left K'), h2,
    opTrace_comp_comm hU (hS.comp_left _)]
  simp only [comp_assoc]

/-- **(SC.36)–(SC.37)** The recovered packet satisfies **(SC.7)** for the recovered reporters. -/
theorem IsAsymptoticallySourceInvariant.recovery {κ : Type*} {A : κ → E →L[ℂ] E} {T : ℕ → E →L[ℂ] E}
    (h : IsAsymptoticallySourceInvariant A T) :
    IsAsymptoticallySourceInvariant (fun a => cornerConj V (A a)) (fun n => cornerConj V (T n)) := by
  obtain ⟨B, hB⟩ := h.bdd
  refine ⟨fun n => cornerConj_isPositive (h.pos n), fun n => (memSchattenClass_cornerConj_iff hV _).2
    (h.traceClass n), ⟨B, fun n => by rw [opTrace_cornerConj hV (h.traceClass n)]; exact hB n⟩, fun a => ?_⟩
  refine (h.comm a).congr fun n => ?_
  rw [(recovery_invariants hV (h.traceClass n) (A a)).2.1]

/-- **(SC.37)** Common recovery preserves compact-observer extinction. -/
theorem IsAsymptoticallySourceInvariant.recovery_extinction {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) (K' : E' →L[ℂ] E') (hK' : IsCompactOperator K') :
    Tendsto (fun n => opTrace (K' ∘L cornerConj V (T n))) atTop (𝓝 0) := by
  have h1 := h.tendsto_opTrace_comp b hA (adjoint V ∘L K' ∘L V) ((hK'.comp_clm V).clm_comp (adjoint V))
  exact h1.congr fun n => ((recovery_invariants hV (h.traceClass n) 0).2.2 K').symm

/-- **(SC.38a)–(SC.38)** The recovered cost `C' = VCV* ⊕ D`, diagonal in a basis `V f ∪ g` with
`g ⊥ VE`, has `E_{C'}(VTV*) = E_C(T)`: the recovered defect lives on `VE`. -/
theorem properCostEnergy_recovery {κ ν : Type*} (f : HilbertBasis κ ℂ E) (μ : κ → ℝ)
    (f' : HilbertBasis (κ ⊕ ν) ℂ E') (hfl : ∀ k, f' (Sum.inl k) = V (f k))
    (hfr : ∀ l x, ⟪V x, f' (Sum.inr l)⟫_ℂ = 0) (d : ν → ℝ) (T : E →L[ℂ] E) :
    properCostEnergy f' (Sum.elim μ d) (cornerConj V T) = properCostEnergy f μ T := by
  have hr : ∀ l, adjoint V (f' (Sum.inr l)) = 0 := fun l =>
    ext_inner_left ℂ fun x => by rw [adjoint_inner_right, hfr, inner_zero_right]
  rw [properCostEnergy, Summable.tsum_sum ENNReal.summable ENNReal.summable]
  have hinr : ∀ l, ENNReal.ofReal (Sum.elim μ d (Sum.inr l) *
      (⟪f' (Sum.inr l), cornerConj V T (f' (Sum.inr l))⟫_ℂ).re) = 0 := fun l => by
    rw [cornerConj, comp_apply, comp_apply, hr, map_zero, map_zero, inner_zero_right, Complex.zero_re,
      mul_zero, ENNReal.ofReal_zero]
  simp only [hinr, tsum_zero, add_zero, Sum.elim_inl, properCostEnergy]
  refine tsum_congr fun k => ?_
  rw [hfl, cornerConj, comp_apply, comp_apply, ← comp_apply (adjoint V) V, hV, id_apply,
    inner_map_map_of_adjoint_comp hV]

omit hV [CompleteSpace E] [CompleteSpace E'] in
/-- A unitary carries a Hilbert basis to a Hilbert basis. -/
theorem exists_hilbertBasis_map {κ : Type*} (U : E ≃ₗᵢ[ℂ] E') (f : HilbertBasis κ ℂ E) :
    ∃ f' : HilbertBasis κ ℂ E', ∀ k, f' k = U (f k) := by
  classical
  refine ⟨HilbertBasis.ofRepr (U.symm.trans f.repr), fun k => ?_⟩
  rw [← HilbertBasis.repr_symm_single, ← HilbertBasis.repr_symm_single]
  rfl

/-- **Corollary 7.2 (SC.39) Functional-equation conjugation is information-neutral.**  For a
unitary-transported cost (basis `U f`) the energy of `UTU*` equals that of `T`. -/
theorem properCostEnergy_conj {κ : Type*} (f : HilbertBasis κ ℂ E) (μ : κ → ℝ) (f' : HilbertBasis κ ℂ E')
    (hf' : ∀ k, f' k = V (f k)) (T : E →L[ℂ] E) :
    properCostEnergy f' μ (cornerConj V T) = properCostEnergy f μ T := by
  refine tsum_congr fun k => ?_
  rw [hf', cornerConj, comp_apply, comp_apply, ← comp_apply (adjoint V) V, hV, id_apply,
    inner_map_map_of_adjoint_comp hV]

end Recovery

/-! ## Compact Gram collapse -/

section Gram

variable {d : ℕ}

/-- **(SC.40)** The Gram matrix `G(i,j) = tr(T A_i* A_j)` of a reporter packet. -/
def reporterGramMatrix (T : E →L[ℂ] E) (R : Fin d → E →L[ℂ] E) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => opTrace (T ∘L (adjoint (R i) ∘L R j))

theorem adjoint_sum_smul (x : Fin d → ℂ) (R : Fin d → E →L[ℂ] E) :
    adjoint (∑ j, x j • R j) = ∑ j, starRingEnd ℂ (x j) • adjoint (R j) := by
  simp only [map_sum, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply]

/-- **(SC.42)** `z* G z = tr(T X* X)` with `X = Σ_j z_j A_j`. -/
theorem dotProduct_reporterGramMatrix {T : E →L[ℂ] E} (hS : MemSchattenClass 1 T) (R : Fin d → E →L[ℂ] E)
    (x : Fin d → ℂ) : star x ⬝ᵥ (reporterGramMatrix T R *ᵥ x) = opTrace (T ∘L (adjoint (∑ j, x j • R j) ∘L ∑ j, x j • R j)) := by
  have hterm : ∀ i j, MemSchattenClass 1 ((starRingEnd ℂ (x i) * x j) • (T ∘L (adjoint (R i) ∘L R j))) :=
    fun i j => memSchattenClass_one_smul (hS.one_comp_right _) _
  have hexp : T ∘L (adjoint (∑ j, x j • R j) ∘L ∑ j, x j • R j) =
      ∑ i, ∑ j, (starRingEnd ℂ (x i) * x j) • (T ∘L (adjoint (R i) ∘L R j)) := by
    rw [adjoint_sum_smul]
    ext1 y
    simp only [comp_apply, sum_apply, smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [hexp, opTrace_finset_sum _ fun i _ => (memSchattenClass_one_finset_sum _ fun j _ => hterm i j).1]
  simp only [dotProduct, Matrix.mulVec, reporterGramMatrix, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [opTrace_finset_sum _ fun j _ => hterm i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [opTrace_smul_eq, RCLike.star_def]
  ring

/-- **(SC.42)** The Gram matrix of a positive trace-class defect is positive semidefinite. -/
theorem reporterGramMatrix_posSemidef {T : E →L[ℂ] E} (hT : T.IsPositive) (hS : MemSchattenClass 1 T)
    (R : Fin d → E →L[ℂ] E) : (reporterGramMatrix T R).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, reporterGramMatrix, RCLike.star_def]
    rw [← RCLike.star_def, ← opTrace_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
      hT.isSelfAdjoint.adjoint_eq]
    exact hS.one_opTrace_comp_comm _
  · rw [dotProduct_reporterGramMatrix hS]
    set X := ∑ j, x j • R j
    have hcyc : opTrace (T ∘L (adjoint X ∘L X)) = opTrace (X ∘L T ∘L adjoint X) := by
      rw [← comp_assoc, ((hS.one_comp_right (adjoint X))).one_opTrace_comp_comm X, comp_assoc]
    rw [hcyc]
    exact opTrace_nonneg_of_isPositive (hT.conj_adjoint X)

/-- **Theorem 8.1 (SC.41)** For compact reporters the Gram matrices collapse: `G_n → 0`. -/
theorem IsAsymptoticallySourceInvariant.tendsto_reporterGramMatrix {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) (R : Fin d → E →L[ℂ] E) (hR : ∀ i, IsCompactOperator (R i)) :
    Tendsto (fun n => reporterGramMatrix (T n) R) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h1 := h.tendsto_opTrace_comp b hA (adjoint (R i) ∘L R j) ((hR j).clm_comp (adjoint (R i)))
  exact h1.congr fun n => (h.traceClass n).one_opTrace_comp_comm _

/-- **(SC.41)** Every positive-size principal minor of `G_n` tends to zero. -/
theorem IsAsymptoticallySourceInvariant.tendsto_det_reporterGramMatrix {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) (R : Fin d → E →L[ℂ] E) (hR : ∀ i, IsCompactOperator (R i)) {k : ℕ}
    (hk : 0 < k) (e : Fin k → Fin d) :
    Tendsto (fun n => ((reporterGramMatrix (T n) R).submatrix e e).det) atTop (𝓝 0) := by
  have hc : Continuous fun M : Matrix (Fin d) (Fin d) ℂ => (M.submatrix e e).det :=
    (continuous_id.matrix_submatrix e e).matrix_det
  have h1 := (hc.tendsto 0).comp (h.tendsto_reporterGramMatrix b hA R hR)
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  simpa [Function.comp_def, Matrix.det_zero] using h1

/-- **(SC.41)** Every eigenvalue (equivalently, singular value) of `G_n` tends to zero. -/
theorem IsAsymptoticallySourceInvariant.tendsto_eigenvalues_reporterGramMatrix {κ : Type*}
    {A : κ → E →L[ℂ] E} {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T)
    (b : HilbertBasis ℕ ℂ E) (hA : IsSourceComplete A) (R : Fin d → E →L[ℂ] E)
    (hR : ∀ i, IsCompactOperator (R i)) (i : Fin d) :
    Tendsto (fun n => (reporterGramMatrix_posSemidef (h.pos n) (h.traceClass n) R).1.eigenvalues i) atTop (𝓝 0) := by
  have htr : Tendsto (fun n => (reporterGramMatrix (T n) R).trace) atTop (𝓝 0) := by
    have := ((continuous_id.matrix_trace).tendsto 0).comp (h.tendsto_reporterGramMatrix b hA R hR)
    simpa [Function.comp_def] using this
  have hsum : ∀ n, (∑ j, (reporterGramMatrix_posSemidef (h.pos n) (h.traceClass n) R).1.eigenvalues j) =
      ((reporterGramMatrix (T n) R).trace).re := fun n => by
    rw [(reporterGramMatrix_posSemidef (h.pos n) (h.traceClass n) R).1.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum]
  have hre := (Complex.continuous_re.tendsto 0).comp htr
  simp only [Function.comp_def, Complex.zero_re] at hre
  refine squeeze_zero (fun n => (reporterGramMatrix_posSemidef (h.pos n) (h.traceClass n) R).eigenvalues_nonneg i)
    (fun n => ?_) hre
  rw [← hsum]
  exact Finset.single_le_sum (f := fun j => (reporterGramMatrix_posSemidef (h.pos n) (h.traceClass n) R).1.eigenvalues j)
    (fun j _ => (reporterGramMatrix_posSemidef (h.pos n) (h.traceClass n) R).eigenvalues_nonneg j) (Finset.mem_univ i)

/-- **(SC.41)** `G_n → 0` in every matrix norm: any norm on the matrices, carried by a linear
identification with a normed space, is continuous for the entrywise topology in finite dimension. -/
theorem IsAsymptoticallySourceInvariant.tendsto_norm_reporterGramMatrix {κ : Type*} {A : κ → E →L[ℂ] E}
    {T : ℕ → E →L[ℂ] E} (h : IsAsymptoticallySourceInvariant A T) (b : HilbertBasis ℕ ℂ E)
    (hA : IsSourceComplete A) (R : Fin d → E →L[ℂ] E) (hR : ∀ i, IsCompactOperator (R i))
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] M) :
    Tendsto (fun n => ‖e (reporterGramMatrix (T n) R)‖) atTop (𝓝 0) := by
  have hc : Continuous e := LinearMap.continuous_of_finiteDimensional e
  have h1 := ((continuous_norm.comp hc).tendsto 0).comp (h.tendsto_reporterGramMatrix b hA R hR)
  simpa [Function.comp_def] using h1

end Gram

end GaloisForLFunctions.HTGeometry
