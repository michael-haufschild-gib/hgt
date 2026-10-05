import GaloisForLFunctions.HTGeometry.FormationQuotientCountermodels
import GaloisForLFunctions.HTGeometry.ConstitutiveCompactCofinalFusion
import GaloisForLFunctions.HTGeometry.CompactPerturbationFredholm

/-!
# Global residual coverage

Let `S_i` be operators with strong sum `Σ_i S_i = cI` (`c > 0`) and `C_i : H → Y_i` bounded
channels with finite Gram residuals `G_F = Σ_{i ∈ F} (C_i*C_i - S_i)`.

**Theorem 5.1.**  If `G_F → G` weakly along finite sets, then `Σ_i ⟨C_i x, C_i y⟩ = c⟨x, y⟩ +
⟨G x, y⟩`; the family is Bessel, the analysis operator `C x = (C_i x)_i` satisfies `C*C = cI + G`,
and if `‖G‖ < c` it obeys `(c - ‖G‖)‖x‖² ≤ Σ_i ‖C_i x‖² ≤ (c + ‖G‖)‖x‖²`, hence is injective with
closed range and decoder `(C*C)⁻¹C*`.

**Theorem 5.2.**  For bounded `C` and compact `A`, `(A, C)` is bounded below iff `ran C` is closed,
`ker C` is finite-dimensional and `A` is injective on `ker C`; equivalently the same holds for the
Gram `C*C`.  The common-kernel decoder reconstructs the source.

**Theorem 6.1.**  A unitary `U` with permuted unitary channel maps `V_i : Y_i → Y_{σ(i)}`
transports channels `C'_{σ(i)} = V_i C_i U*` and carriers `S'_{σ(i)} = U S_i U*`: `G' = U G U*` and
`C'*C' = U (C*C) U*`, preserving formation, frame bounds, kernel, closed range, residual norm,
essential norm and decoder conditioning.

**§8.**  Retaining the carrier, the packet `Ψ_δ = (A, C, δC)` is bounded below for every `δ` exactly
when `(A, C)` is; the defect `δC` vanishes exactly at `δ = 0`; dropping the carrier leaves the
compact `A`, which is never bounded below on an infinite-dimensional space.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TightFormation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℂ (Y i)]
  [∀ i, CompleteSpace (Y i)]

omit [CompleteSpace H] in
/-- `Σ_i ⟨f_i, y⟩ = ⟨Σ_i f_i, y⟩` for a convergent series. -/
theorem hasSum_inner_left {f : ι → H} {a : H} (hf : HasSum f a) (y : H) :
    HasSum (fun i => ⟪f i, y⟫_ℂ) ⟪a, y⟫_ℂ := by
  rw [HasSum, SummationFilter.unconditional_filter] at hf ⊢
  have h := Filter.Tendsto.inner (𝕜 := ℂ) hf (tendsto_const_nhds (x := y))
  simpa [sum_inner] using h

/-! ### Theorem 5.1: uniform Gram formation -/

/-- The finite Gram residual `G_F = Σ_{i ∈ F} (C_i*C_i - S_i)`. -/
def gramResidual (S : ι → H →L[ℂ] H) (C : ∀ i, H →L[ℂ] Y i) (F : Finset ι) : H →L[ℂ] H :=
  ∑ i ∈ F, (ContinuousLinearMap.adjoint (C i) ∘L C i - S i)

/-- Weak-operator convergence of the Gram residuals to `G` along finite subsets. -/
def HasWeakGramLimit (S : ι → H →L[ℂ] H) (C : ∀ i, H →L[ℂ] Y i) (G : H →L[ℂ] H) : Prop :=
  ∀ x y : H, Tendsto (fun F : Finset ι => ⟪gramResidual S C F x, y⟫_ℂ) atTop (𝓝 ⟪G x, y⟫_ℂ)

theorem inner_gramResidual (S : ι → H →L[ℂ] H) (C : ∀ i, H →L[ℂ] Y i) (F : Finset ι)
    (x y : H) :
    ⟪gramResidual S C F x, y⟫_ℂ = ∑ i ∈ F, (⟪C i x, C i y⟫_ℂ - ⟪S i x, y⟫_ℂ) := by
  rw [gramResidual, sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_apply, inner_sub_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- The weak Gram limit is the convergence of the residual Gram series. -/
theorem hasWeakGramLimit_iff (S : ι → H →L[ℂ] H) (C : ∀ i, H →L[ℂ] Y i) (G : H →L[ℂ] H) :
    HasWeakGramLimit S C G ↔
      ∀ x y : H, HasSum (fun i => ⟪C i x, C i y⟫_ℂ - ⟪S i x, y⟫_ℂ) ⟪G x, y⟫_ℂ := by
  simp only [HasWeakGramLimit, inner_gramResidual, HasSum, SummationFilter.unconditional_filter]

variable {S : ι → H →L[ℂ] H} {C : ∀ i, H →L[ℂ] Y i} {G : H →L[ℂ] H} {c : ℝ}

/-- **Theorem 5.1, polarized `(5.4)`**: `Σ_i ⟨C_i x, C_i y⟩ = c⟨x, y⟩ + ⟨G x, y⟩`. -/
theorem hasSum_inner_channel (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x y : H) :
    HasSum (fun i => ⟪C i x, C i y⟫_ℂ) ((c : ℂ) * ⟪x, y⟫_ℂ + ⟪G x, y⟫_ℂ) := by
  have h1 := hasSum_inner_left (hS x) y
  rw [inner_smul_left, Complex.conj_ofReal] at h1
  have h2 := (hasWeakGramLimit_iff S C G).1 hG x y
  rw [add_comm]
  exact (h2.add h1).congr_fun fun i => (sub_add_cancel _ _).symm

/-- **Theorem 5.1, `(5.4)`**: `Σ_i ‖C_i x‖² = c‖x‖² + ⟨G x, x⟩`. -/
theorem hasSum_norm_sq_channel (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x : H) :
    HasSum (fun i => ‖C i x‖ ^ 2) (c * ‖x‖ ^ 2 + RCLike.re ⟪G x, x⟫_ℂ) := by
  have h := (hasSum_inner_channel hS hG x x).mapL Complex.reCLM
  simp only [Complex.reCLM_apply] at h
  convert h using 1
  · funext i
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  · rw [Complex.add_re, Complex.re_ofReal_mul, ← RCLike.re_to_complex,
      ← norm_sq_eq_re_inner (𝕜 := ℂ)]
    rfl

omit [CompleteSpace H] in
theorem abs_re_inner_apply_le (T : H →L[ℂ] H) (x : H) :
    |RCLike.re ⟪T x, x⟫_ℂ| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc |RCLike.re ⟪T x, x⟫_ℂ| ≤ ‖⟪T x, x⟫_ℂ‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ ‖T‖ * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- **Theorem 5.1**: the family is Bessel with bound `c + ‖G‖`, and `cI + G` is positive. -/
theorem channel_bessel (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x : H) :
    0 ≤ c * ‖x‖ ^ 2 + RCLike.re ⟪G x, x⟫_ℂ ∧
      ∑' i, ‖C i x‖ ^ 2 ≤ (c + ‖G‖) * ‖x‖ ^ 2 := by
  have h := hasSum_norm_sq_channel hS hG x
  refine ⟨h.nonneg fun i => by positivity, ?_⟩
  rw [h.tsum_eq]
  have := (abs_le.1 (abs_re_inner_apply_le G x)).2
  nlinarith

/-- The assembled analysis operator `C x = (C_i x)_i` (linear part). -/
def gramAnalysisLin (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) : H →ₗ[ℂ] lp Y 2 where
  toFun x := ⟨fun i => C i x, (memℓp_gen_iff (by norm_num)).2 (by
    simpa using (hasSum_norm_sq_channel hS hG x).summable)⟩
  map_add' x y := lp.ext (funext fun i => map_add _ _ _)
  map_smul' a x := lp.ext (funext fun i => map_smul _ _ _)

theorem norm_sq_gramAnalysisLin (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x : H) :
    ‖gramAnalysisLin hS hG x‖ ^ 2 = c * ‖x‖ ^ 2 + RCLike.re ⟪G x, x⟫_ℂ := by
  rw [norm_sq_lp]
  exact (hasSum_norm_sq_channel hS hG x).tsum_eq

/-- **Theorem 5.1, `(5.3)`**: the analysis operator `C : H → ⊕_i Y_i`. -/
def gramAnalysis (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) : H →L[ℂ] lp Y 2 :=
  (gramAnalysisLin hS hG).mkContinuous (Real.sqrt (c + ‖G‖)) fun x => by
    have hpos : 0 ≤ c + ‖G‖ := by positivity
    have h : ‖gramAnalysisLin hS hG x‖ ^ 2 ≤ (Real.sqrt (c + ‖G‖) * ‖x‖) ^ 2 := by
      rw [norm_sq_gramAnalysisLin, mul_pow, Real.sq_sqrt hpos]
      have := (abs_le.1 (abs_re_inner_apply_le G x)).2
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem norm_sq_gramAnalysis (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x : H) :
    ‖gramAnalysis hc hS hG x‖ ^ 2 = c * ‖x‖ ^ 2 + RCLike.re ⟪G x, x⟫_ℂ :=
  norm_sq_gramAnalysisLin hS hG x

theorem gramAnalysis_apply (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x : H) (i : ι) :
    (gramAnalysis hc hS hG x : ∀ i, Y i) i = C i x := rfl

theorem inner_gramAnalysis (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x y : H) :
    ⟪gramAnalysis hc hS hG x, gramAnalysis hc hS hG y⟫_ℂ = (c : ℂ) * ⟪x, y⟫_ℂ + ⟪G x, y⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  exact (hasSum_inner_channel hS hG x y).tsum_eq

/-- **Theorem 5.1, `(5.4)`**: `C*C = cI + G`. -/
theorem adjoint_gramAnalysis_comp (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) :
    ContinuousLinearMap.adjoint (gramAnalysis hc hS hG) ∘L gramAnalysis hc hS hG =
      (c : ℂ) • 1 + G := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, inner_gramAnalysis,
    add_apply, smul_apply,
    one_apply_eq_self, inner_add_left, inner_smul_left, Complex.conj_ofReal]

/-- **Theorem 5.1, `(5.6)`**: if `‖G‖ < c` then
`(c - ‖G‖)‖x‖² ≤ Σ_i ‖C_i x‖² ≤ (c + ‖G‖)‖x‖²`. -/
theorem channel_frame_bounds (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (x : H) :
    (c - ‖G‖) * ‖x‖ ^ 2 ≤ ∑' i, ‖C i x‖ ^ 2 ∧ ∑' i, ‖C i x‖ ^ 2 ≤ (c + ‖G‖) * ‖x‖ ^ 2 := by
  rw [(hasSum_norm_sq_channel hS hG x).tsum_eq]
  have := abs_le.1 (abs_re_inner_apply_le G x)
  constructor <;> nlinarith [this.1, this.2]

theorem isUnit_gram (hc : 0 < c) (hGc : ‖G‖ < c) : IsUnit ((c : ℂ) • (1 : H →L[ℂ] H) + G) := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hsmall : ‖-((c : ℂ)⁻¹ • G)‖ < 1 := by
    rw [norm_neg, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le,
      inv_mul_lt_iff₀ hc, mul_one]
    exact hGc
  have hu := (Units.oneSub (-((c : ℂ)⁻¹ • G)) hsmall).isUnit
  rw [Units.val_oneSub, sub_neg_eq_add] at hu
  have hcu : IsUnit ((c : ℂ) • (1 : H →L[ℂ] H)) := by
    have : IsUnit (algebraMap ℂ (H →L[ℂ] H) (c : ℂ)) := (isUnit_iff_ne_zero.2 hc0).map _
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have := hcu.mul hu
  rwa [smul_one_mul, smul_add, smul_smul, mul_inv_cancel₀ hc0, one_smul] at this

/-- The canonical decoder `L_C = (C*C)⁻¹ C*`. -/
def gramDecoder (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) : lp Y 2 →L[ℂ] H :=
  Ring.inverse (ContinuousLinearMap.adjoint (gramAnalysis hc hS hG) ∘L gramAnalysis hc hS hG) ∘L
    ContinuousLinearMap.adjoint (gramAnalysis hc hS hG)

/-- **Theorem 5.1, `(5.7)`**: if `‖G‖ < c`, then `C` is bounded below, injective, has closed range,
and the decoder `(C*C)⁻¹C*` recovers every vector. -/
theorem gramAnalysis_proper (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (hGc : ‖G‖ < c) :
    (∀ x, (c - ‖G‖) * ‖x‖ ^ 2 ≤ ‖gramAnalysis hc hS hG x‖ ^ 2) ∧
      Function.Injective (gramAnalysis hc hS hG) ∧
      IsClosed (Set.range (gramAnalysis hc hS hG)) ∧
      ∀ x, gramDecoder hc hS hG (gramAnalysis hc hS hG x) = x := by
  have hdec : ∀ x, gramDecoder hc hS hG (gramAnalysis hc hS hG x) = x := fun x => by
    have hunit := isUnit_gram (H := H) hc hGc
    rw [← adjoint_gramAnalysis_comp hc hS hG] at hunit
    have h := congrArg (fun T : H →L[ℂ] H => T x) (Ring.inverse_mul_cancel _ hunit)
    simpa [gramDecoder] using h
  refine ⟨fun x => ?_, fun x y hxy => ?_, ?_, hdec⟩
  · change (c - ‖G‖) * ‖x‖ ^ 2 ≤ ‖gramAnalysisLin hS hG x‖ ^ 2
    rw [norm_sq_gramAnalysisLin]
    have := (abs_le.1 (abs_re_inner_apply_le G x)).1
    nlinarith
  · have := congrArg (gramDecoder hc hS hG) hxy
    rwa [hdec, hdec] at this
  · have hrange : Set.range (gramAnalysis hc hS hG) =
        {v | gramAnalysis hc hS hG (gramDecoder hc hS hG v) = v} := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact congrArg _ (hdec x)
      · intro hv
        exact ⟨_, hv⟩
    rw [hrange]
    exact isClosed_eq (by fun_prop) continuous_id

/-! ### Theorem 5.2: finite local repair of a global residual kernel -/

section Repair

variable {Y₀ Z : Type*} [NormedAddCommGroup Y₀] [InnerProductSpace ℂ Y₀] [CompleteSpace Y₀]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]

/-- The `ℓ²` lower bound for the packet `T = (A, C)`. -/
def IsPacketBoundedBelow (A : H →L[ℂ] Y₀) (R : H →L[ℂ] Z) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x, c ^ 2 * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ‖R x‖ ^ 2

omit [CompleteSpace H] [CompleteSpace Y₀] [CompleteSpace Z] in
theorem isPacketBoundedBelow_iff (A : H →L[ℂ] Y₀) (R : H →L[ℂ] Z) :
    IsPacketBoundedBelow A R ↔ IsJointlyBoundedBelow A R := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c / Real.sqrt 2, by positivity, fun x => ?_⟩
    rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
    have hx := h x
    have hm : ‖A x‖ ^ 2 + ‖R x‖ ^ 2 ≤ 2 * max ‖A x‖ ‖R x‖ ^ 2 := by
      have h1 : ‖A x‖ ≤ max ‖A x‖ ‖R x‖ := le_max_left _ _
      have h2 : ‖R x‖ ≤ max ‖A x‖ ‖R x‖ := le_max_right _ _
      nlinarith [norm_nonneg (A x), norm_nonneg (R x)]
    have hsq : (c / Real.sqrt 2 * ‖x‖) ^ 2 ≤ max ‖A x‖ ‖R x‖ ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (le_max_of_le_left (norm_nonneg _))
      two_ne_zero).1 hsq
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun x => ?_⟩
    have hx := h x
    rw [ContinuousLinearMap.prod_apply, Prod.norm_def] at hx
    have hsq := pow_le_pow_left₀ (by positivity) hx 2
    rw [mul_pow] at hsq
    rcases le_total ‖A x‖ ‖R x‖ with hle | hle
    · rw [max_eq_right hle] at hsq
      nlinarith [sq_nonneg ‖A x‖]
    · rw [max_eq_left hle] at hsq
      nlinarith [sq_nonneg ‖R x‖]

/-- **Theorem 5.2**: for bounded `C` and compact `A`, the packet `(A, C)` is bounded below iff
`ran C` is closed, `ker C` is finite-dimensional, and `A` is injective on `ker C`. -/
theorem packetBoundedBelow_iff (A : H →L[ℂ] Y₀) (R : H →L[ℂ] Z) (hA : IsCompactOperator A) :
    IsPacketBoundedBelow A R ↔
      IsClosed (Set.range R) ∧ FiniteDimensional ℂ (LinearMap.ker (R : H →ₗ[ℂ] Z)) ∧
        ∀ x : H, x ∈ LinearMap.ker (R : H →ₗ[ℂ] Z) → A x = 0 → x = 0 := by
  rw [isPacketBoundedBelow_iff, compactCofinal_jointlyBoundedBelow_iff A R hA]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- Closed range of `C` gives closed range of the Gram `C*C`. -/
theorem isClosed_range_adjoint_comp_self (R : H →L[ℂ] Z) (hR : IsClosed (Set.range R)) :
    IsClosed (Set.range (ContinuousLinearMap.adjoint R ∘L R)) := by
  have hker := ker_adjoint_comp_self R
  obtain ⟨γ, hγ, hbound⟩ := (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range R).2 hR
  apply (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range _).1
  refine ⟨γ ^ 2, by positivity, fun x hx => ?_⟩
  rw [hker] at hx
  have h1 := hbound x hx
  have h2 : ‖R x‖ ^ 2 ≤ ‖(ContinuousLinearMap.adjoint R ∘L R) x‖ * ‖x‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) (ContinuousLinearMap.adjoint R (R x)) x
    rw [ContinuousLinearMap.adjoint_inner_left, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h
    exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h3 : γ ^ 2 * ‖x‖ * ‖x‖ ≤ ‖(ContinuousLinearMap.adjoint R ∘L R) x‖ * ‖x‖ := by
    nlinarith [pow_le_pow_left₀ (by positivity) h1 2]
  exact le_of_mul_le_mul_right h3 hxpos

theorem isClosed_range_adjoint_comp_self_iff (R : H →L[ℂ] Z) :
    IsClosed (Set.range (ContinuousLinearMap.adjoint R ∘L R)) ↔ IsClosed (Set.range R) :=
  ⟨isClosed_range_of_isClosed_range_adjoint_comp_self R, isClosed_range_adjoint_comp_self R⟩

/-- **Theorem 5.2, Gram form**: the Gram `C*C` may lose only finitely many directions, and the
compact packet must separate exactly those. -/
theorem packetBoundedBelow_iff_gram (A : H →L[ℂ] Y₀) (R : H →L[ℂ] Z) (hA : IsCompactOperator A) :
    IsPacketBoundedBelow A R ↔
      IsClosed (Set.range (ContinuousLinearMap.adjoint R ∘L R)) ∧
        FiniteDimensional ℂ (LinearMap.ker ((ContinuousLinearMap.adjoint R ∘L R : H →L[ℂ] H) :
          H →ₗ[ℂ] H)) ∧
        ∀ x : H, x ∈ LinearMap.ker ((ContinuousLinearMap.adjoint R ∘L R : H →L[ℂ] H) :
          H →ₗ[ℂ] H) → A x = 0 → x = 0 := by
  rw [packetBoundedBelow_iff A R hA, ker_adjoint_comp_self R]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨isClosed_range_adjoint_comp_self R h1, h2, h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨isClosed_range_of_isClosed_range_adjoint_comp_self R h1, h2, h3⟩⟩

/-- **Theorem 5.2, decoder**: under the repair conditions the common-kernel decoder reconstructs
every vector from the packet. -/
theorem exists_packetDecoder (A : H →L[ℂ] Y₀) (R : H →L[ℂ] Z) (hR : IsClosed (Set.range R))
    (hker : FiniteDimensional ℂ (LinearMap.ker (R : H →ₗ[ℂ] Z)))
    (hsep : ∀ x : H, x ∈ LinearMap.ker (R : H →ₗ[ℂ] Z) → A x = 0 → x = 0) :
    ∃ L : (Y₀ × Z) →L[ℂ] H, ∀ x : H, L (A x, R x) = x :=
  exists_commonRecovery_of_cofinalTransducer A R ⟨hR, hker⟩ hsep

/-! ### Section 8: carrier--defect bifurcation -/

omit [CompleteSpace H] [CompleteSpace Y₀] [CompleteSpace Z] in
/-- **§8, `(8.1)`**: retaining the carrier, `Ψ_δ = (A, C, δC)` is bounded below exactly when
`(A, C)` is, for every `δ`. -/
theorem carrierDefect_boundedBelow_iff (A : H →L[ℂ] Y₀) (R : H →L[ℂ] Z) (δ : ℂ) :
    (∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖carrierDefectPacket A R δ x‖) ↔
      IsJointlyBoundedBelow A R := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c / (1 + ‖δ‖), by positivity, fun x => ?_⟩
    have hx := h x
    have hle : ‖carrierDefectPacket A R δ x‖ ≤ (1 + ‖δ‖) * ‖(A.prod R) x‖ := by
      simp only [carrierDefectPacket, ContinuousLinearMap.prod_apply, Prod.norm_def,
        smul_apply, norm_smul]
      refine max_le ?_ ?_
      · nlinarith [norm_nonneg δ, le_max_left ‖A x‖ ‖R x‖, norm_nonneg (A x), norm_nonneg (R x),
          le_max_right ‖A x‖ ‖R x‖]
      · nlinarith [norm_nonneg δ, le_max_right ‖A x‖ ‖R x‖, norm_nonneg (R x)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun x => (h x).trans ?_⟩
    simp only [carrierDefectPacket, ContinuousLinearMap.prod_apply, Prod.norm_def]
    exact le_max_left _ _

omit [CompleteSpace H] [CompleteSpace Z] in
/-- **§8, `(8.2)`**: the relative defect `D_δ = δC` vanishes exactly at `δ = 0`. -/
theorem defect_eq_zero_iff (R : H →L[ℂ] Z) (hR : R ≠ 0) (δ : ℂ) : δ • R = 0 ↔ δ = 0 :=
  ⟨fun h => (smul_eq_zero.1 h).resolve_right hR, fun h => by rw [h, zero_smul]⟩

omit [CompleteSpace Y₀] in
/-- **§8**: dropping the retained carrier leaves the compact packet alone, which cannot be bounded
below on an infinite-dimensional space. -/
theorem not_boundedBelow_compact (A : H →L[ℂ] Y₀) (hA : IsCompactOperator A)
    (hinf : ¬ FiniteDimensional ℂ H) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖A x‖ := by
  rintro ⟨c, hc, h⟩
  apply hinf
  have := finiteDimensional_of_isCompactOperator_of_bounded_below hA ⊤ isClosed_univ hc
    fun x _ => h x
  exact (LinearEquiv.ofTop ⊤ rfl).finiteDimensional

end Repair

/-! ### Theorem 6.1: information-neutral residual transport -/

section Transport

variable (U : H ≃ₗᵢ[ℂ] H) (σ : ι ≃ ι) (V : ∀ i, Y i ≃ₗᵢ[ℂ] Y (σ i))
  {S' : ι → H →L[ℂ] H} {C' : ∀ i, H →L[ℂ] Y i}

omit [CompleteSpace H] in
/-- `⟨U a, y⟩ = ⟨a, U* y⟩`. -/
theorem inner_map_left (a y : H) : ⟪U a, y⟫_ℂ = ⟪a, U.symm y⟫_ℂ := by
  conv_lhs => rw [← U.apply_symm_apply y]
  exact U.inner_map_map _ _

omit [CompleteSpace H] in
/-- **Theorem 6.1, carrier transport**: `Σ_j S'_j = cI` when `Σ_i S_i = cI`. -/
theorem transport_carrier (hS' : ∀ i x, S' (σ i) x = U (S i (U.symm x)))
    (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x)) (x : H) :
    HasSum (fun j => S' j x) ((c : ℂ) • x) := by
  rw [← σ.hasSum_iff]
  have h : HasSum (fun i => U (S i (U.symm x))) ((c : ℂ) • x) := by
    simpa using (hS (U.symm x)).mapL (U.toContinuousLinearEquiv : H →L[ℂ] H)
  exact h.congr_fun fun i => hS' i x

/-- **Theorem 6.1, `(6.2)`**: the residual transports as `G' = U G U*`. -/
theorem transport_weakGramLimit (hC' : ∀ i x, C' (σ i) x = V i (C i (U.symm x)))
    (hS' : ∀ i x, S' (σ i) x = U (S i (U.symm x))) (hG : HasWeakGramLimit S C G) :
    HasWeakGramLimit S' C' (RHTower.unitaryPush U G) := by
  rw [hasWeakGramLimit_iff] at hG ⊢
  intro x y
  rw [← σ.hasSum_iff, RHTower.unitaryPush_apply, inner_map_left]
  refine (hG (U.symm x) (U.symm y)).congr_fun fun i => ?_
  simp only [Function.comp_apply, hC', hS', LinearIsometryEquiv.inner_map_map, inner_map_left]

/-- **Theorem 6.1, `(6.2)`**: `C' = V C U*`, `G' = U G U*`, `C'*C' = U (C*C) U*`; the duality
preserves Bessel sums, frame bounds, the residual norm and essential norm, kernels and closed
range, and the decoder conditioning. -/
theorem residual_transport (hc : 0 < c) (hS : ∀ x, HasSum (fun i => S i x) ((c : ℂ) • x))
    (hG : HasWeakGramLimit S C G) (hC' : ∀ i x, C' (σ i) x = V i (C i (U.symm x)))
    (hS' : ∀ i x, S' (σ i) x = U (S i (U.symm x))) :
    let hS'' := transport_carrier U σ hS' hS
    let hG' := transport_weakGramLimit U σ V hC' hS' hG
    (∀ x i, (gramAnalysis hc hS'' hG' x : ∀ j, Y j) (σ i) =
        V i ((gramAnalysis hc hS hG (U.symm x) : ∀ j, Y j) i)) ∧
      ContinuousLinearMap.adjoint (gramAnalysis hc hS'' hG') ∘L gramAnalysis hc hS'' hG' =
        RHTower.unitaryPush U
          (ContinuousLinearMap.adjoint (gramAnalysis hc hS hG) ∘L gramAnalysis hc hS hG) ∧
      (∀ x, ‖gramAnalysis hc hS'' hG' x‖ = ‖gramAnalysis hc hS hG (U.symm x)‖) ∧
      ‖RHTower.unitaryPush U G‖ = ‖G‖ ∧
      RHTower.essentialNorm (RHTower.unitaryPush U G) = RHTower.essentialNorm G ∧
      (∀ x, gramAnalysis hc hS'' hG' x = 0 ↔ gramAnalysis hc hS hG (U.symm x) = 0) ∧
      Module.rank ℂ (LinearMap.ker (gramAnalysis hc hS'' hG' : H →ₗ[ℂ] lp Y 2)) =
        Module.rank ℂ (LinearMap.ker (gramAnalysis hc hS hG : H →ₗ[ℂ] lp Y 2)) ∧
      (IsClosed (Set.range (gramAnalysis hc hS'' hG')) ↔
        IsClosed (Set.range (gramAnalysis hc hS hG))) ∧
      ‖Ring.inverse (ContinuousLinearMap.adjoint (gramAnalysis hc hS'' hG') ∘L
          gramAnalysis hc hS'' hG')‖ =
        ‖Ring.inverse (ContinuousLinearMap.adjoint (gramAnalysis hc hS hG) ∘L
          gramAnalysis hc hS hG)‖ := by
  intro hS'' hG'
  have hgram : ContinuousLinearMap.adjoint (gramAnalysis hc hS'' hG') ∘L gramAnalysis hc hS'' hG' =
      RHTower.unitaryPush U
        (ContinuousLinearMap.adjoint (gramAnalysis hc hS hG) ∘L gramAnalysis hc hS hG) := by
    rw [adjoint_gramAnalysis_comp, adjoint_gramAnalysis_comp, RHTower.unitaryPush_add,
      RHTower.unitaryPush_smul, RHTower.unitaryPush_one]
  have hnorm : ∀ x, ‖gramAnalysis hc hS'' hG' x‖ = ‖gramAnalysis hc hS hG (U.symm x)‖ := fun x => by
    have h : ‖gramAnalysis hc hS'' hG' x‖ ^ 2 = ‖gramAnalysis hc hS hG (U.symm x)‖ ^ 2 := by
      rw [norm_sq_gramAnalysis, norm_sq_gramAnalysis, RHTower.unitaryPush_apply, inner_map_left,
        LinearIsometryEquiv.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  have hrange : Set.range (ContinuousLinearMap.adjoint (gramAnalysis hc hS'' hG') ∘L
      gramAnalysis hc hS'' hG') = U '' Set.range (ContinuousLinearMap.adjoint
        (gramAnalysis hc hS hG) ∘L gramAnalysis hc hS hG) := by
    rw [hgram]
    ext v
    simp only [Set.mem_range, Set.mem_image, RHTower.unitaryPush_apply]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨U.symm x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨U x, by rw [LinearIsometryEquiv.symm_apply_apply]⟩
  let φ : (H →L[ℂ] H) →* (H →L[ℂ] H) :=
    { toFun := RHTower.unitaryPush U
      map_one' := RHTower.unitaryPush_one U
      map_mul' := RHTower.unitaryPush_mul U }
  have hinv : ∀ T : H →L[ℂ] H,
      Ring.inverse (RHTower.unitaryPush U T) = RHTower.unitaryPush U (Ring.inverse T) := by
    intro T
    by_cases hT : IsUnit T
    · obtain ⟨u, rfl⟩ := hT
      have h := Ring.inverse_unit (Units.map φ u)
      rw [Ring.inverse_unit]
      exact h
    · let ψ : (H →L[ℂ] H) →* (H →L[ℂ] H) :=
        { toFun := RHTower.unitaryPush U.symm
          map_one' := RHTower.unitaryPush_one U.symm
          map_mul' := RHTower.unitaryPush_mul U.symm }
      have hT' : ¬ IsUnit (RHTower.unitaryPush U T) := fun h => hT (by
        have := h.map ψ
        rwa [show ψ (RHTower.unitaryPush U T) = T from
          RHTower.unitaryPush_symm_unitaryPush U T] at this)
      rw [Ring.inverse_non_unit _ hT, Ring.inverse_non_unit _ hT']
      ext x
      simp
  have hker : ∀ x, gramAnalysis hc hS'' hG' x = 0 ↔ gramAnalysis hc hS hG (U.symm x) = 0 :=
    fun x => by rw [← norm_eq_zero, hnorm, norm_eq_zero]
  have hmap : (LinearMap.ker (gramAnalysis hc hS hG : H →ₗ[ℂ] lp Y 2)).map
      (U.toLinearEquiv : H →ₗ[ℂ] H) = LinearMap.ker
    (gramAnalysis hc hS'' hG' : H →ₗ[ℂ] lp Y 2) := by
    ext x
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    exact (hker x).symm
  refine ⟨fun x i => hC' i x, hgram, hnorm, RHTower.norm_unitaryPush U G,
    RHTower.essentialNorm_unitaryPush U G, hker,
    (LinearEquiv.ofSubmodules U.toLinearEquiv _ _ hmap).rank_eq.symm,
    ?_, by rw [hgram, hinv, RHTower.norm_unitaryPush]⟩
  rw [← isClosed_range_adjoint_comp_self_iff (gramAnalysis hc hS'' hG'),
    ← isClosed_range_adjoint_comp_self_iff (gramAnalysis hc hS hG), hrange]
  exact U.toHomeomorph.isClosed_image

end Transport

end GaloisForLFunctions.HTGeometry.TightFormation
