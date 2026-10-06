import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.BigOperators.Sym
import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import GaloisForLFunctions.HTGeometry.HilbertBlockOperator

/-!
# Source-response formation energy

One source intervention produces bounded responses `ρ_i : V → W` (`i ∈ I`, finite) with weights
`c_i > 0`, total weight `C` and mean `ρ̄ = C⁻¹ Σ_i c_i ρ_i`.  The centred analysis operator
`A x = (√c_i (ρ_i - ρ̄) x)_i` into `⊕_I W` has formation energy `𝓔(x) = ‖A x‖²` and formation
Laplacian `L = A*A`.

* **(FLP.6)** pairwise conservation `𝓔(x) = Σ_i c_i ‖ρ_i x - ρ̄ x‖² = C⁻¹ Σ_{{i,j}} c_i c_j
  ‖ρ_i x - ρ_j x‖²`;
* **(FLP.7)** `ker A = ker L = K = ⋂_i ker(ρ_i - ρ_{i₀})`, so `𝓔` descends to `V/K`;
* **(FLP.9)** `𝓔(dⁿ x) = d²ⁿ 𝓔(x)` and the dilation orbit has bounded work iff `x ∈ K`;
* **Part VI** `ran A` is closed iff `𝓔(x) ≥ α dist(x, K)²` for some `α > 0` iff there is no unit
  adaptive escape sequence in `Kᗮ`;
* **Part VII** an added response factoring through the packet is energy-equivalent and cannot change
  the kernel or closedness of the range, while an unlocking organ must intercept every escape
  sequence.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SourceResponse

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] {I : Type*} [Fintype I]

/-- A source-generated response packet: bounded responses with positive weights. -/
structure ResponsePacket (I V W : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  /-- the response maps -/
  ρ : I → V →L[ℝ] W
  /-- the weights -/
  c : I → ℝ
  c_pos : ∀ i, 0 < c i

namespace ResponsePacket

variable (P : ResponsePacket I V W)

/-- **(FLP.2)** the total weight `C = Σ_i c_i`. -/
def totalWeight : ℝ := ∑ i, P.c i

theorem totalWeight_pos [Nonempty I] : 0 < P.totalWeight :=
  Finset.sum_pos (fun i _ => P.c_pos i) Finset.univ_nonempty

/-- **(FLP.2)** the weighted mean response `ρ̄ = C⁻¹ Σ_i c_i ρ_i`. -/
def mean : V →L[ℝ] W := P.totalWeight⁻¹ • ∑ i, P.c i • P.ρ i

/-- **(FLP.3)** the centred analysis operator `A x = (√c_i (ρ_i - ρ̄) x)_i`. -/
def analysis : V →L[ℝ] PiLp 2 (fun _ : I => W) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => W)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => Real.sqrt (P.c i) • (P.ρ i - P.mean)

theorem analysis_apply (x : V) (i : I) :
    (P.analysis x).ofLp i = Real.sqrt (P.c i) • (P.ρ i x - P.mean x) := rfl

/-- **(FLP.4)** the formation energy `𝓔(x) = ‖A x‖²`. -/
def energy (x : V) : ℝ := ‖P.analysis x‖ ^ 2

/-- **(FLP.4)** the formation Laplacian `L = A*A`. -/
def laplacian [CompleteSpace V] [CompleteSpace W] : V →L[ℝ] V :=
  ContinuousLinearMap.adjoint P.analysis ∘L P.analysis

/-- **(FLP.5)** the synchronization kernel `K = ⋂_i ker(ρ_i - ρ_{i₀})`. -/
def syncKernel (i₀ : I) : Submodule ℝ V :=
  ⨅ i, LinearMap.ker ((P.ρ i - P.ρ i₀ : V →L[ℝ] W) : V →ₗ[ℝ] W)

omit [Fintype I] in
theorem mem_syncKernel_iff (i₀ : I) (x : V) :
    x ∈ P.syncKernel i₀ ↔ ∀ i, P.ρ i x = P.ρ i₀ x := by
  simp only [syncKernel, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, sub_eq_zero]

theorem mean_apply (x : V) : P.mean x = P.totalWeight⁻¹ • ∑ i, P.c i • P.ρ i x := by
  simp [mean]

/-! ### (FLP.6): pairwise conservation -/

theorem energy_eq_sum (x : V) : P.energy x = ∑ i, P.c i * ‖P.ρ i x - P.mean x‖ ^ 2 := by
  rw [energy, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [analysis_apply, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (P.c_pos i).le]

/-- The centred and doubly-indexed forms of the weighted variance. -/
theorem sum_mul_sum_norm_sq_sub [Nonempty I] (y : I → W) :
    ∑ i, ∑ j, P.c i * P.c j * ‖y i - y j‖ ^ 2 =
      2 * P.totalWeight * ∑ i, P.c i * ‖y i - P.totalWeight⁻¹ • ∑ j, P.c j • y j‖ ^ 2 := by
  have hC := P.totalWeight_pos
  set C := P.totalWeight with hCdef
  set s : W := ∑ j, P.c j • y j with hs
  have hexp : ∀ i j, ‖y i - y j‖ ^ 2 = ‖y i‖ ^ 2 - 2 * ⟪y i, y j⟫_ℝ + ‖y j‖ ^ 2 := fun i j =>
    norm_sub_sq_real _ _
  have hexp' : ∀ i, ‖y i - C⁻¹ • s‖ ^ 2 = ‖y i‖ ^ 2 - 2 * C⁻¹ * ⟪y i, s⟫_ℝ + C⁻¹ ^ 2 * ‖s‖ ^ 2 :=
    fun i => by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg (by positivity),
        mul_pow]
      ring
  have hss : ‖s‖ ^ 2 = ∑ i, ∑ j, P.c i * P.c j * ⟪y i, y j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, hs, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hsi : ∀ i, ⟪y i, s⟫_ℝ = ∑ j, P.c j * ⟪y i, y j⟫_ℝ := fun i => by
    rw [hs, inner_sum]
    exact Finset.sum_congr rfl fun j _ => real_inner_smul_right _ _ _
  simp_rw [hexp, hexp']
  have hCsum : ∑ i, P.c i = C := rfl
  calc ∑ i, ∑ j, P.c i * P.c j * (‖y i‖ ^ 2 - 2 * ⟪y i, y j⟫_ℝ + ‖y j‖ ^ 2)
      = 2 * C * ∑ i, P.c i * ‖y i‖ ^ 2 - 2 * ‖s‖ ^ 2 := by
        rw [hss]
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h1 : ∑ i, ∑ j, P.c i * P.c j * ‖y i‖ ^ 2 = C * ∑ i, P.c i * ‖y i‖ ^ 2 := by
          rw [← hCsum, Finset.sum_mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
        have h2 : ∑ i, ∑ j, P.c i * P.c j * ‖y j‖ ^ 2 = C * ∑ i, P.c i * ‖y i‖ ^ 2 := by
          rw [← hCsum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
        have h3 : ∑ i, ∑ j, P.c i * P.c j * (2 * ⟪y i, y j⟫_ℝ) =
            2 * ∑ i, ∑ j, P.c i * P.c j * ⟪y i, y j⟫_ℝ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h1, h2, h3]
        ring
    _ = 2 * C * ∑ i, P.c i * (‖y i‖ ^ 2 - 2 * C⁻¹ * ⟪y i, s⟫_ℝ + C⁻¹ ^ 2 * ‖s‖ ^ 2) := by
        have h4 : ∑ i, P.c i * (‖y i‖ ^ 2 - 2 * C⁻¹ * ⟪y i, s⟫_ℝ + C⁻¹ ^ 2 * ‖s‖ ^ 2) =
            ∑ i, P.c i * ‖y i‖ ^ 2 - 2 * C⁻¹ * ∑ i, P.c i * ⟪y i, s⟫_ℝ +
              C⁻¹ ^ 2 * ‖s‖ ^ 2 * C := by
          rw [← hCsum]
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
          congr 1
          · congr 1
            exact Finset.sum_congr rfl fun i _ => by ring
          · exact Finset.sum_congr rfl fun i _ => by ring
        have h5 : ∑ i, P.c i * ⟪y i, s⟫_ℝ = ‖s‖ ^ 2 := by
          rw [hss]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsi, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h4, h5]
        field_simp
        ring

/-- **(FLP.6)**, ordered form: `𝓔(x) = (2C)⁻¹ Σ_{i,j} c_i c_j ‖ρ_i x - ρ_j x‖²`. -/
theorem energy_eq_pairwise [Nonempty I] (x : V) :
    P.energy x = (2 * P.totalWeight)⁻¹ *
      ∑ i, ∑ j, P.c i * P.c j * ‖P.ρ i x - P.ρ j x‖ ^ 2 := by
  have hC := P.totalWeight_pos
  rw [P.sum_mul_sum_norm_sq_sub (fun i => P.ρ i x), energy_eq_sum, mean_apply]
  field_simp

/-- The symmetric pair weight `c_i c_j ‖ρ_i x - ρ_j x‖²` on unordered pairs. -/
def pairWeight (x : V) : Sym2 I → ℝ :=
  Sym2.lift ⟨fun i j => P.c i * P.c j * ‖P.ρ i x - P.ρ j x‖ ^ 2, fun i j => by
    show P.c i * P.c j * ‖P.ρ i x - P.ρ j x‖ ^ 2 = P.c j * P.c i * ‖P.ρ j x - P.ρ i x‖ ^ 2
    rw [norm_sub_rev, mul_comm (P.c i)]⟩

/-- **(FLP.6)**, unordered form: `𝓔(x) = C⁻¹ Σ_{{i,j} ⊂ I} c_i c_j ‖ρ_i x - ρ_j x‖²`, the sum
running over two-element subsets (empty when `|I| = 1`). -/
theorem energy_eq_sum_unordered [Nonempty I] [DecidableEq I] (x : V) :
    P.energy x = P.totalWeight⁻¹ *
      ∑ z ∈ (Finset.univ : Finset I).sym2 with ¬ z.IsDiag, P.pairWeight x z := by
  classical
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hC := P.totalWeight_pos
  have hsym := Finset.sum_sym2_filter_not_isDiag (Finset.univ : Finset I) (P.pairWeight x)
  have hsym' : ∑ z ∈ (Finset.univ : Finset I).sym2 with ¬ z.IsDiag, P.pairWeight x z =
      ∑ p ∈ (Finset.univ : Finset I).offDiag with p.1 < p.2, P.pairWeight x s(p.1, p.2) := by
    convert hsym
  rw [hsym', P.energy_eq_pairwise]
  set g : I → I → ℝ := fun i j => P.c i * P.c j * ‖P.ρ i x - P.ρ j x‖ ^ 2 with hg
  have hsymm : ∀ i j, g i j = g j i := fun i j => by
    simp only [hg]
    rw [norm_sub_rev, mul_comm (P.c i)]
  have hdiag : ∀ i, g i i = 0 := fun i => by simp [hg]
  -- the full double sum is twice the sum over `i < j`
  have hsplit : ∑ i, ∑ j, g i j = 2 * ∑ p ∈ (Finset.univ : Finset I).offDiag with p.1 < p.2,
      g p.1 p.2 := by
    have hfull : ∑ i, ∑ j, g i j = ∑ p ∈ (Finset.univ : Finset (I × I)), g p.1 p.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    have hlt : ∑ p ∈ (Finset.univ : Finset (I × I)) with p.1 < p.2, g p.1 p.2 =
        ∑ p ∈ (Finset.univ : Finset (I × I)) with p.2 < p.1, g p.1 p.2 := by
      refine Finset.sum_nbij' Prod.swap Prod.swap (by simp) (by simp) (by simp) (by simp)
        fun p _ => hsymm _ _
    have heq : ∑ p ∈ (Finset.univ : Finset (I × I)) with p.1 = p.2, g p.1 p.2 = 0 :=
      Finset.sum_eq_zero fun p hp => by
        rw [(Finset.mem_filter.1 hp).2, hdiag]
    have h3 : ∑ p ∈ (Finset.univ : Finset (I × I)), g p.1 p.2 =
        ∑ p ∈ (Finset.univ : Finset (I × I)) with p.1 < p.2, g p.1 p.2 +
          ∑ p ∈ (Finset.univ : Finset (I × I)) with p.2 < p.1, g p.1 p.2 +
          ∑ p ∈ (Finset.univ : Finset (I × I)) with p.1 = p.2, g p.1 p.2 := by
      rw [← Finset.sum_union, ← Finset.sum_union]
      · congr 1
        ext p
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases lt_trichotomy p.1 p.2 with h | h | h <;> simp [h]
      · rw [Finset.disjoint_union_left, Finset.disjoint_filter, Finset.disjoint_filter]
        exact ⟨fun p _ h1 h2 => ne_of_lt h1 h2, fun p _ h1 h2 => ne_of_gt h1 h2⟩
      · rw [Finset.disjoint_filter]
        intro p _ h1 h2
        exact lt_asymm h1 h2
    have hoff : ∑ p ∈ (Finset.univ : Finset I).offDiag with p.1 < p.2, g p.1 p.2 =
        ∑ p ∈ (Finset.univ : Finset (I × I)) with p.1 < p.2, g p.1 p.2 := by
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
    rw [hfull, h3, hoff, ← hlt, heq]
    ring
  rw [hsplit]
  simp only [pairWeight, Sym2.lift_mk]
  field_simp
  ring

/-! ### (FLP.7): the synchronization kernel -/

theorem analysis_eq_zero_iff [Nonempty I] (i₀ : I) (x : V) :
    P.analysis x = 0 ↔ x ∈ P.syncKernel i₀ := by
  rw [mem_syncKernel_iff]
  constructor
  · intro h
    have hmean : ∀ i, P.ρ i x = P.mean x := fun i => by
      have := congrArg (fun z : PiLp 2 (fun _ : I => W) => z.ofLp i) h
      simp only [analysis_apply, PiLp.zero_apply] at this
      rcases smul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (Real.sqrt_ne_zero'.2 (P.c_pos i))
      · exact sub_eq_zero.1 h0
    intro i
    rw [hmean, hmean]
  · intro h
    have hmean : P.mean x = P.ρ i₀ x := by
      have hC := P.totalWeight_pos
      rw [mean_apply]
      simp_rw [h]
      rw [← Finset.sum_smul, inv_smul_eq_iff₀ hC.ne', totalWeight]
    ext i
    simp only [analysis_apply, PiLp.zero_apply, h i, hmean, sub_self, smul_zero]

/-- **(FLP.7)**: `ker A = K`. -/
theorem ker_analysis [Nonempty I] (i₀ : I) :
    LinearMap.ker (P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) = P.syncKernel i₀ := by
  ext x
  rw [LinearMap.mem_ker]
  exact P.analysis_eq_zero_iff i₀ x

theorem inner_laplacian_self [CompleteSpace V] [CompleteSpace W] (x : V) :
    ⟪P.laplacian x, x⟫_ℝ = P.energy x := by
  rw [laplacian, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]
  rfl

/-- **(FLP.7)**: `ker L = ker A = K`. -/
theorem ker_laplacian [CompleteSpace V] [CompleteSpace W] [Nonempty I] (i₀ : I) :
    LinearMap.ker (P.laplacian : V →ₗ[ℝ] V) = P.syncKernel i₀ := by
  rw [← P.ker_analysis i₀]
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    have h1 := P.inner_laplacian_self x
    rw [h, inner_zero_left, energy] at h1
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1.symm)
  · intro h
    rw [laplacian, ContinuousLinearMap.comp_apply, h, map_zero]

/-- **(FLP.7)**: the energy descends to `V/K`: it is invariant under `K`-translation and vanishes
exactly on `K`. -/
theorem energy_add_mem [Nonempty I] (i₀ : I) (x k : V) (hk : k ∈ P.syncKernel i₀) :
    P.energy (x + k) = P.energy x := by
  rw [energy, energy, map_add, (P.analysis_eq_zero_iff i₀ k).2 hk, add_zero]

theorem energy_eq_zero_iff [Nonempty I] (i₀ : I) (x : V) :
    P.energy x = 0 ↔ x ∈ P.syncKernel i₀ := by
  rw [energy, pow_eq_zero_iff two_ne_zero, norm_eq_zero, P.analysis_eq_zero_iff i₀]

theorem energy_nonneg (x : V) : 0 ≤ P.energy x := by
  rw [energy]
  positivity

/-! ### (FLP.9): scale-orbit selection -/

theorem energy_smul (a : ℝ) (x : V) : P.energy (a • x) = a ^ 2 * P.energy x := by
  rw [energy, energy, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- **(FLP.9)**: `𝓔(dⁿ x) = d²ⁿ 𝓔(x)`. -/
theorem energy_dilate (d : ℝ) (n : ℕ) (x : V) : P.energy (d ^ n • x) = d ^
    (2 * n) * P.energy x := by
  rw [energy_smul, ← pow_mul, mul_comm n 2]

/-- **(FLP.9)**: for `d > 1`, the dilation orbit of `x` has bounded work iff `x ∈ K`. -/
theorem bddAbove_energy_dilate_iff [Nonempty I] (i₀ : I) {d : ℝ} (hd : 1 < d) (x : V) :
    BddAbove (Set.range fun n : ℕ => P.energy (d ^ n • x)) ↔ x ∈ P.syncKernel i₀ := by
  constructor
  · intro ⟨M, hM⟩
    by_contra hx
    have hpos : 0 < P.energy x :=
      lt_of_le_of_ne (P.energy_nonneg x) (fun h => hx ((P.energy_eq_zero_iff i₀ x).1 h.symm))
    have htend : Tendsto (fun n : ℕ => d ^ (2 * n) * P.energy x) atTop atTop := by
      refine Tendsto.atTop_mul_const hpos ?_
      exact (tendsto_pow_atTop_atTop_of_one_lt hd).comp
        (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop M).exists
    have := hM ⟨n, rfl⟩
    dsimp only at this
    rw [energy_dilate] at this
    linarith
  · intro hx
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [energy_dilate, (P.energy_eq_zero_iff i₀ x).2 hx, mul_zero]

/-! ### Part VI: closed range and adaptive escape -/

section ClosedRange

variable [CompleteSpace V] [CompleteSpace W] [Nonempty I]

omit [CompleteSpace V] [CompleteSpace W] in
theorem isClosed_syncKernel (i₀ : I) : IsClosed (P.syncKernel i₀ : Set V) := by
  rw [← P.ker_analysis i₀]
  exact P.analysis.isClosed_ker

omit [CompleteSpace W] in
theorem completeSpace_syncKernel (i₀ : I) : CompleteSpace (P.syncKernel i₀) :=
  (P.isClosed_syncKernel i₀).completeSpace_coe

omit [CompleteSpace W] in
/-- `dist(x, K) = ‖x - P_K x‖`, and the energy only sees the component `x - P_K x ∈ Kᗮ`. -/
theorem infDist_syncKernel (i₀ : I) (x : V) :
    haveI := P.completeSpace_syncKernel i₀
    Metric.infDist x (P.syncKernel i₀) = ‖x - (P.syncKernel i₀).starProjection x‖ ∧
      P.energy (x - (P.syncKernel i₀).starProjection x) = P.energy x := by
  haveI := P.completeSpace_syncKernel i₀
  refine ⟨?_, ?_⟩
  · rw [Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
    simp only [dist_eq_norm]
    rfl
  · rw [sub_eq_add_neg]
    exact P.energy_add_mem i₀ x _ (Submodule.neg_mem _ (Submodule.starProjection_apply_mem _ x))

omit [CompleteSpace W] in
theorem infDist_syncKernel_of_mem_orthogonal (i₀ : I) {u : V}
    (hu : u ∈ (P.syncKernel i₀)ᗮ) : Metric.infDist u (P.syncKernel i₀) = ‖u‖ := by
  haveI := P.completeSpace_syncKernel i₀
  have h0 : (P.syncKernel i₀).starProjection u = 0 := by
    rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hu,
      Submodule.coe_zero]
  rw [(P.infDist_syncKernel i₀ u).1, h0, sub_zero]

/-- **Part VI, (FLP.11)–(FLP.23)**: for the packet operator `A`, the following are equivalent:
`ran A` is closed; `𝓔(x) ≥ α dist(x, K)²` for some `α > 0`; there is no unit adaptive escape
sequence `x_n ∈ Kᗮ` with `𝓔(x_n) → 0`. -/
theorem adaptiveEscape_tfae (i₀ : I) :
    [IsClosed (Set.range P.analysis),
      ∃ α : ℝ, 0 < α ∧ ∀ x, α * Metric.infDist x (P.syncKernel i₀) ^ 2 ≤ P.energy x,
      ¬ ∃ u : ℕ → V, (∀ n, u n ∈ (P.syncKernel i₀)ᗮ ∧ ‖u n‖ = 1) ∧
        Tendsto (fun n => P.energy (u n)) atTop (𝓝 0)].TFAE := by
  haveI := P.completeSpace_syncKernel i₀
  have hker := P.ker_analysis i₀
  tfae_have 1 → 2 := by
    intro hcl
    obtain ⟨c, hc, hbound⟩ :=
      (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range P.analysis).2 hcl
    refine ⟨c ^ 2, by positivity, fun x => ?_⟩
    obtain ⟨hdist, hE⟩ := P.infDist_syncKernel i₀ x
    have hy : x - (P.syncKernel i₀).starProjection x ∈
        (LinearMap.ker (P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)))ᗮ := by
      rw [hker]
      exact Submodule.sub_starProjection_mem_orthogonal x
    have h1 := hbound _ hy
    rw [hdist, ← hE, energy, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 2
  tfae_have 2 → 3 := by
    rintro ⟨α, hα, hbound⟩ ⟨u, hu, hlim⟩
    have hge : ∀ n, α ≤ P.energy (u n) := fun n => by
      have := hbound (u n)
      rwa [P.infDist_syncKernel_of_mem_orthogonal i₀ (hu n).1, (hu n).2, one_pow,
        mul_one] at this
    have := ge_of_tendsto hlim (Eventually.of_forall hge)
    linarith
  tfae_have 3 → 1 := by
    intro hno
    by_contra hcl
    rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range] at hcl
    have hex : ∀ n : ℕ, ∃ u : V, u ∈ (P.syncKernel i₀)ᗮ ∧ ‖u‖ = 1 ∧
        ‖P.analysis u‖ < 1 / ((n : ℝ) + 1) := fun n => by
      by_contra hcon
      simp only [not_exists, not_and, not_lt] at hcon
      apply hcl
      refine ⟨1 / ((n : ℝ) + 1), by positivity, fun x hx => ?_⟩
      rw [hker] at hx
      rcases eq_or_ne x 0 with rfl | hx0
      · simp
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hmem : ‖x‖⁻¹ • x ∈ (P.syncKernel i₀)ᗮ := Submodule.smul_mem _ _ hx
      have hn1 : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
      have h := hcon _ hmem hn1
      rw [map_smul, norm_smul, norm_inv, norm_norm] at h
      rw [mul_comm]
      calc ‖x‖ * (1 / ((n : ℝ) + 1)) ≤ ‖x‖ * (‖x‖⁻¹ * ‖P.analysis x‖) :=
            mul_le_mul_of_nonneg_left h hxpos.le
        _ = ‖P.analysis x‖ := by field_simp
    choose u hu using hex
    apply hno
    refine ⟨u, fun n => ⟨(hu n).1, (hu n).2.1⟩, ?_⟩
    have hupper : ∀ n, P.energy (u n) ≤ (1 / ((n : ℝ) + 1)) ^ 2 := fun n =>
      pow_le_pow_left₀ (norm_nonneg _) (hu n).2.2.le 2
    refine squeeze_zero (fun n => P.energy_nonneg _) hupper ?_
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    simpa using h
  tfae_finish

/-- **Part VI**: an injective packet with nonclosed range detects every fixed displacement and
expels every fixed dilation orbit, yet admits a unit escape sequence of vanishing energy. -/
theorem injective_nonclosed_escape (i₀ : I) (hK : P.syncKernel i₀ = ⊥)
    (hcl : ¬ IsClosed (Set.range P.analysis)) {d : ℝ} (hd : 1 < d) :
    (∀ x, x ≠ 0 → 0 < P.energy x ∧ ¬ BddAbove (Set.range fun n : ℕ => P.energy (d ^ n • x))) ∧
      ∃ u : ℕ → V, (∀ n, ‖u n‖ = 1) ∧ Tendsto (fun n => P.energy (u n)) atTop (𝓝 0) := by
  refine ⟨fun x hx => ⟨lt_of_le_of_ne (P.energy_nonneg x) fun h => hx ?_, fun hb => hx ?_⟩, ?_⟩
  · have := (P.energy_eq_zero_iff i₀ x).1 h.symm
    rwa [hK, Submodule.mem_bot] at this
  · have := (P.bddAbove_energy_dilate_iff i₀ hd x).1 hb
    rwa [hK, Submodule.mem_bot] at this
  · have h := (P.adaptiveEscape_tfae i₀).out 0 2
    rw [h, not_not] at hcl
    obtain ⟨u, hu, hlim⟩ := hcl
    exact ⟨u, fun n => (hu n).2, hlim⟩

end ClosedRange

/-! ### Part VII: fourth-organ redundancy and escape interception -/

section FourthOrgan

variable [CompleteSpace V] [CompleteSpace W] [Nonempty I] {Z : Type*} [NormedAddCommGroup Z]
  [InnerProductSpace ℝ Z] [CompleteSpace Z]

/-- **(FLP.12)** the enlarged packet `A⁺ x = (A x, R x)`. -/
def augmented (R : V →L[ℝ] Z) : V →L[ℝ] WithLp 2 (PiLp 2 (fun _ : I => W) × Z) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : I => W)) Z).symm.toContinuousLinearMap ∘L
    P.analysis.prod R

omit [CompleteSpace V] [CompleteSpace W] [Nonempty I] [CompleteSpace Z] in
/-- **(FLP.12)** `𝓔⁺(x) = 𝓔(x) + ‖R x‖²`. -/
theorem norm_sq_augmented (R : V →L[ℝ] Z) (x : V) :
    ‖P.augmented R x‖ ^ 2 = P.energy x + ‖R x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

omit [CompleteSpace V] [CompleteSpace W] [Nonempty I] [CompleteSpace Z] in
/-- **(FLP.13)**: if `R = S A` then `𝓔 ≤ 𝓔⁺ ≤ (1 + ‖S‖²) 𝓔`. -/
theorem augmented_energy_bounds (S : PiLp 2 (fun _ : I => W) →L[ℝ] Z) (x : V) :
    P.energy x ≤ ‖P.augmented (S ∘L P.analysis) x‖ ^ 2 ∧
      ‖P.augmented (S ∘L P.analysis) x‖ ^ 2 ≤ (1 + ‖S‖ ^ 2) * P.energy x := by
  rw [norm_sq_augmented]
  refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
  have h := (S.le_opNorm (P.analysis x))
  have h2 : ‖S (P.analysis x)‖ ^ 2 ≤ ‖S‖ ^ 2 * P.energy x := by
    rw [energy, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [ContinuousLinearMap.comp_apply]
  nlinarith

/-- **(FLP.14)**: a fourth organ factoring through the packet leaves the kernel and the closedness
of the range unchanged. -/
theorem augmented_redundant (i₀ : I) (S : PiLp 2 (fun _ : I => W) →L[ℝ] Z) :
    LinearMap.ker (P.augmented (S ∘L P.analysis) :
        V →ₗ[ℝ] WithLp 2 (PiLp 2 (fun _ : I => W) × Z)) = P.syncKernel i₀ ∧
      (IsClosed (Set.range (P.augmented (S ∘L P.analysis))) ↔
        IsClosed (Set.range P.analysis)) := by
  have hkerA := P.ker_analysis i₀
  have hker : LinearMap.ker (P.augmented (S ∘L P.analysis) :
      V →ₗ[ℝ] WithLp 2 (PiLp 2 (fun _ : I => W) × Z)) =
      LinearMap.ker (P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) := by
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    obtain ⟨h1, h2⟩ := P.augmented_energy_bounds S x
    constructor
    · intro h
      have h0 : ‖P.augmented (S ∘L P.analysis) x‖ ^ 2 = 0 := by rw [h, norm_zero]; ring
      have hE : P.energy x = 0 := le_antisymm (h0 ▸ h1) (P.energy_nonneg x)
      rwa [energy, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hE
    · intro h
      have hE : P.energy x = 0 := by rw [energy, h, norm_zero]; ring
      rw [hE, mul_zero] at h2
      have h0 : ‖P.augmented (S ∘L P.analysis) x‖ ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
      rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h0
  refine ⟨hker.trans hkerA, ?_⟩
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range,
    ← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
  simp only [ContinuousLinearMap.HasTransverseLowerBound]
  rw [hker]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c / Real.sqrt (1 + ‖S‖ ^ 2), by positivity, fun x hx => ?_⟩
    have h1 := h x hx
    have h2 := (P.augmented_energy_bounds S x).2
    have hs : 0 < Real.sqrt (1 + ‖S‖ ^ 2) := by positivity
    have h3 : ‖P.augmented (S ∘L P.analysis) x‖ ≤ Real.sqrt (1 + ‖S‖ ^ 2) * ‖P.analysis x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (P.augmented (S ∘L P.analysis) x)),
        ← Real.sqrt_sq (norm_nonneg (P.analysis x)), ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by rw [energy] at h2; linarith)
    rw [div_mul_eq_mul_div, div_le_iff₀ hs]
    nlinarith
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun x hx => (h x hx).trans ?_⟩
    have h1 := (P.augmented_energy_bounds S x).1
    rw [energy] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

omit [CompleteSpace V] [CompleteSpace W] [Nonempty I] [CompleteSpace Z] in
/-- **(FLP.15)**: if the enlarged packet is coercive, `𝓔⁺(x) ≥ α‖x‖²`, then along every unit
sequence with `𝓔(x_n) → 0` the added organ eventually carries energy at least `α - ε`. -/
theorem augmented_intercepts (R : V →L[ℝ] Z) {α : ℝ}
    (hα : ∀ x, α * ‖x‖ ^ 2 ≤ ‖P.augmented R x‖ ^ 2) {u : ℕ → V} (hu : ∀ n, ‖u n‖ = 1)
    (hlim : Tendsto (fun n => P.energy (u n)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, α - ε ≤ ‖R (u n)‖ ^ 2 := by
  filter_upwards [(hlim.eventually (gt_mem_nhds hε))] with n hn
  have h := hα (u n)
  rw [norm_sq_augmented, hu n, one_pow, mul_one] at h
  linarith

omit [CompleteSpace Z] in
/-- **Part VII, unlocking organ**: for an injective packet with nonclosed range, an enlarged packet
with `𝓔⁺(x) ≥ α‖x‖²` (`α > 0`) admits escape sequences of the old packet, and the new organ
intercepts every one of them: `liminf ‖R x_n‖² ≥ α > 0`. -/
theorem unlocking_organ_intercepts (i₀ : I) (hK : P.syncKernel i₀ = ⊥)
    (hcl : ¬ IsClosed (Set.range P.analysis)) (R : V →L[ℝ] Z) {α : ℝ} (hα0 : 0 < α)
    (hα : ∀ x, α * ‖x‖ ^ 2 ≤ ‖P.augmented R x‖ ^ 2) :
    (∃ u : ℕ → V, (∀ n, ‖u n‖ = 1) ∧ Tendsto (fun n => P.energy (u n)) atTop (𝓝 0)) ∧
      ∀ u : ℕ → V, (∀ n, ‖u n‖ = 1) → Tendsto (fun n => P.energy (u n)) atTop (𝓝 0) →
        ∀ᶠ n in atTop, α / 2 ≤ ‖R (u n)‖ ^ 2 := by
  refine ⟨(P.injective_nonclosed_escape i₀ hK hcl (by norm_num : (1 : ℝ) < 2)).2,
    fun u hu hlim => ?_⟩
  have := P.augmented_intercepts R hα hu hlim (ε := α / 2) (by positivity)
  filter_upwards [this] with n hn
  linarith

end FourthOrgan

end ResponsePacket

/-! ### §5: sharp countermodels and boundaries -/

section Countermodels

/-- **§5.1**: a single organ forms no disagreement: `ρ̄ = ρ`, `A = 0`, `K = V`. -/
theorem singleton_packet [Unique I] (P : ResponsePacket I V W) :
    P.mean = P.ρ default ∧ P.analysis = 0 ∧ P.syncKernel default = ⊤ := by
  have hC : P.totalWeight = P.c default := by
    rw [ResponsePacket.totalWeight, Fintype.sum_unique]
  have hmean : P.mean = P.ρ default := by
    rw [ResponsePacket.mean, Fintype.sum_unique, hC, smul_smul,
      inv_mul_cancel₀ (P.c_pos default).ne', one_smul]
  refine ⟨hmean, ?_, ?_⟩
  · ext x i
    rw [ResponsePacket.analysis_apply, Subsingleton.elim i default, hmean, sub_self, smul_zero]
    rfl
  · rw [eq_top_iff]
    intro x _
    rw [ResponsePacket.mem_syncKernel_iff]
    intro i
    rw [Subsingleton.elim i default]

/-- The real diagonal `D e_n = (n+1)⁻¹ e_n` on `ℓ²(ℕ)`. -/
def harmonicDiagonal : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  blockOperator (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) zero_le_one
    fun n => by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
      calc ((n : ℝ) + 1)⁻¹ * ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 * 1 :=
            mul_le_mul (inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
              ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

theorem harmonicDiagonal_apply (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    (harmonicDiagonal x : ℕ → ℝ) n = ((n : ℝ) + 1)⁻¹ * (x : ℕ → ℝ) n := rfl

theorem harmonicDiagonal_injective : Function.Injective harmonicDiagonal := fun x y h => by
  refine lp.ext (funext fun n => ?_)
  have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => (z : ℕ → ℝ) n) h
  simp only [harmonicDiagonal_apply] at this
  exact mul_left_cancel₀ (by positivity) this

/-- The two-organ packet `ρ₁ = D`, `ρ₂ = -D` with unit weights. -/
def harmonicPacket : ResponsePacket (Fin 2) (lp (fun _ : ℕ => ℝ) 2) (lp (fun _ : ℕ => ℝ) 2) where
  ρ := ![harmonicDiagonal, -harmonicDiagonal]
  c := fun _ => 1
  c_pos := fun _ => one_pos

/-- **§5.2, (FLP.26)–(FLP.27)**: algebraic separation does not imply uniform selection: for
`ρ₁ = D`, `ρ₂ = -D`, `ρ̄ = 0`, `K = {0}`, `𝓔(x) = 2‖Dx‖²`, `𝓔(e_n) → 0`, and `ran A` is not
closed. -/
theorem harmonicPacket_escape :
    harmonicPacket.mean = 0 ∧ harmonicPacket.syncKernel 0 = ⊥ ∧
      (∀ x, harmonicPacket.energy x = 2 * ‖harmonicDiagonal x‖ ^ 2) ∧
      (∀ n : ℕ, harmonicPacket.energy (lp.single 2 n 1) = 2 / ((n : ℝ) + 1) ^ 2) ∧
      Tendsto (fun n : ℕ => harmonicPacket.energy (lp.single 2 n 1)) atTop (𝓝 0) ∧
      ¬ IsClosed (Set.range harmonicPacket.analysis) := by
  have hmean : harmonicPacket.mean = 0 := by
    simp [ResponsePacket.mean, harmonicPacket, Fin.sum_univ_two]
  have hK : harmonicPacket.syncKernel 0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [ResponsePacket.mem_syncKernel_iff] at hx
    have h1 := hx 1
    simp only [harmonicPacket, Matrix.cons_val_one, Matrix.cons_val_zero,
      neg_apply] at h1
    have h2 : harmonicDiagonal x = 0 := by
      have : (2 : ℝ) • harmonicDiagonal x = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← neg_neg (harmonicDiagonal x)]
        rw [h1, neg_add_cancel]
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
    rw [Submodule.mem_bot]
    exact harmonicDiagonal_injective (h2.trans (map_zero _).symm)
  have hE : ∀ x, harmonicPacket.energy x = 2 * ‖harmonicDiagonal x‖ ^ 2 := fun x => by
    rw [ResponsePacket.energy_eq_sum, Fin.sum_univ_two, hmean]
    simp [harmonicPacket]
    ring
  have hEn : ∀ n : ℕ, harmonicPacket.energy (lp.single 2 n 1) = 2 / ((n : ℝ) + 1) ^ 2 := fun n => by
    rw [hE, harmonicDiagonal, blockOperator_single, lp.norm_single (by norm_num)]
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one,
      norm_inv, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    field_simp
  have hlim : Tendsto (fun n : ℕ => harmonicPacket.energy (lp.single 2 n 1)) atTop (𝓝 0) := by
    simp_rw [hEn]
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul 2
    simp only [zero_pow two_ne_zero, mul_zero] at h
    refine h.congr fun n => ?_
    rw [div_pow, one_pow]
    field_simp
  refine ⟨hmean, hK, hE, hEn, hlim, fun hcl => ?_⟩
  have h := (harmonicPacket.adaptiveEscape_tfae 0).out 0 2
  rw [h] at hcl
  apply hcl
  refine ⟨fun n => lp.single 2 n 1, fun n => ⟨?_, ?_⟩, hlim⟩
  · rw [hK, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  · rw [lp.norm_single (by norm_num), norm_one]

/-- The two-organ packet `ρ₁ = id`, `ρ₂ = -id`, so that `A x = (x, -x)`. -/
def identityPacket (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ResponsePacket (Fin 2) V V where
  ρ := ![ContinuousLinearMap.id ℝ V, -ContinuousLinearMap.id ℝ V]
  c := fun _ => 1
  c_pos := fun _ => one_pos

/-- **§5.3**: on an infinite-dimensional space coercivity `𝓔(x) ≥ α dist(x, K)²` holds for
`A = (I, -I)` but the finite-energy sublevel `{𝓔 ≤ 2}`, the closed unit ball, is not compact. -/
theorem identityPacket_noncompact [CompleteSpace V] (hV : ¬ FiniteDimensional ℝ V) :
    (∃ α : ℝ, 0 < α ∧ ∀ x : V,
        α * Metric.infDist x ((identityPacket V).syncKernel 0) ^ 2 ≤ (identityPacket V).energy x) ∧
      ¬ IsCompact {x : V | (identityPacket V).energy x ≤ 2} := by
  have hmean : (identityPacket V).mean = 0 := by
    simp [ResponsePacket.mean, identityPacket, Fin.sum_univ_two]
  have hE : ∀ x, (identityPacket V).energy x = 2 * ‖x‖ ^ 2 := fun x => by
    rw [ResponsePacket.energy_eq_sum, Fin.sum_univ_two, hmean]
    simp [identityPacket]
    ring
  have hK : (identityPacket V).syncKernel 0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [ResponsePacket.mem_syncKernel_iff] at hx
    have h1 := hx 1
    simp only [identityPacket, Matrix.cons_val_one, Matrix.cons_val_zero,
      neg_apply, ContinuousLinearMap.id_apply] at h1
    rw [Submodule.mem_bot]
    have : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← neg_neg x]
      rw [h1, neg_add_cancel]
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  refine ⟨⟨2, two_pos, fun x => ?_⟩, fun hc => hV ?_⟩
  · rw [hE, hK]
    have : Metric.infDist x ((⊥ : Submodule ℝ V) : Set V) = ‖x‖ := by
      rw [Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
    rw [this]
  · have hball : {x : V | (identityPacket V).energy x ≤ 2} = Metric.closedBall 0 1 := by
      ext x
      simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right, hE]
      constructor
      · intro h
        have : ‖x‖ ^ 2 ≤ 1 ^ 2 := by linarith
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).1 this
      · intro h
        nlinarith [norm_nonneg x]
    rw [hball] at hc
    exact FiniteDimensional.of_isCompact_closedBall₀ ℝ one_pos hc

end Countermodels

end GaloisForLFunctions.HTGeometry.SourceResponse
