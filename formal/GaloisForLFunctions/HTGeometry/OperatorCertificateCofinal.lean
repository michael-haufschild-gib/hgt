import GaloisForLFunctions.HTGeometry.OperatorCertificateGenealogy
import GaloisForLFunctions.HTGeometry.VectorSequenceShift
import GaloisForLFunctions.HTGeometry.RectangularVectorDiagonal
import GaloisForLFunctions.HTGeometry.WeightedOrbitInductionGap
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator certificates on `ℓ²(ℕ; ℂ^d)`: admission, hidden lineage, mirage, minimal repair rank

Cofinal part of ULF-CRGM-3.  Certificate matrices act on the fibre `V = ℂ^d` through
`Matrix.toEuclideanCLM`; the completed genealogy on `ℓ²(ℕ; V)` is `(G x)_n = x_n - C_n x_{n+1}`
(OP.20).

* **Theorem 5.1:** the semantic packet is bounded iff `∑ ‖A_n‖²_HS < ∞` (OP.22), the lineage packet
  iff `∑ ‖A_n⁻¹‖²_HS < ∞` (OP.23); both cannot hold; `ker G ≅ V₋` (OP.24); `G` has dense range.
* **Theorem 6.1:** a critical lineage direction is invisible to every compact observer.
* **Theorem 7.1:** for closed range, an observer repairs `G` iff it is injective on `ker G`, and
  the minimal finite repair rank is `dim V₋`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology Matrix
open scoped InnerProductSpace ENNReal

variable {d : ℕ}

/-- The fibre `V = ℂ^d`. -/
abbrev Fib (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The completed history carrier `ℓ²(ℕ; V)`. -/
abbrev FibSeq (d : ℕ) := VecSeq (Fib d)

/-- A matrix acting on the fibre. -/
abbrev matOp (A : Matrix (Fin d) (Fin d) ℂ) : Fib d →L[ℂ] Fib d :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) A

theorem norm_sq_fib (v : Fib d) : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem matOp_apply_coord (A : Matrix (Fin d) (Fin d) ℂ) (v : Fib d) (i : Fin d) :
    matOp A v i = ∑ j, A i j * v j := by
  show (A *ᵥ WithLp.ofLp v) i = _
  rfl

/-- `‖A v‖² ≤ ‖A‖²_HS ‖v‖²`. -/
theorem norm_sq_matOp_apply_le (A : Matrix (Fin d) (Fin d) ℂ) (v : Fib d) :
    ‖matOp A v‖ ^ 2 ≤ hsSq A * ‖v‖ ^ 2 := by
  rw [norm_sq_fib, norm_sq_fib, hsSq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [matOp_apply_coord]
  calc ‖∑ j, A i j * v j‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Hilbert--Schmidt energy as the sum of squared column norms. -/
theorem hsSq_eq_sum_col (A : Matrix (Fin d) (Fin d) ℂ) :
    hsSq A = ∑ j, ‖matOp A (EuclideanSpace.single j 1)‖ ^ 2 := by
  have hcol : ∀ j, ‖matOp A (EuclideanSpace.single j 1)‖ ^ 2 = ∑ i, ‖A i j‖ ^ 2 := by
    intro j
    rw [norm_sq_fib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [matOp_apply_coord]
    congr 2
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj; simp [hkj]
    · simp
  rw [Finset.sum_congr rfl fun j _ => hcol j, hsSq, Finset.sum_comm]

theorem matOp_mul_apply (A B : Matrix (Fin d) (Fin d) ℂ) (v : Fib d) :
    matOp (A * B) v = matOp A (matOp B v) := by
  rw [matOp, map_mul]; rfl

theorem matOp_one_apply (v : Fib d) : matOp (1 : Matrix (Fin d) (Fin d) ℂ) v = v := by
  rw [matOp, map_one]; rfl

theorem hsSq_star (A : Matrix (Fin d) (Fin d) ℂ) : hsSq (star A) = hsSq A := by
  rw [hsSq, hsSq, Finset.sum_comm]
  simp [Matrix.star_apply]

theorem matOp_star (A : Matrix (Fin d) (Fin d) ℂ) :
    matOp (star A) = ContinuousLinearMap.adjoint (matOp A) := by
  rw [matOp, map_star]
  rfl

theorem hsSq_nonneg (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ hsSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Column syntheses -/

/-- The column synthesis `w ↦ (T_n w)_n` of a Hilbert--Schmidt-summable matrix family. -/
def colSynthLinear (T : ℕ → Matrix (Fin d) (Fin d) ℂ) (h : Summable fun n => hsSq (T n)) :
    Fib d →ₗ[ℂ] FibSeq d where
  toFun w := ⟨fun n => matOp (T n) w, memℓp_of_summable_sq
    (Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun n => norm_sq_matOp_apply_le (T n) w) (h.mul_right _))⟩
  map_add' x y := by ext n; simp
  map_smul' c x := by ext n; simp

theorem norm_colSynthLinear_le (T : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (h : Summable fun n => hsSq (T n)) (w : Fib d) :
    ‖colSynthLinear T h w‖ ≤ Real.sqrt (∑' n, hsSq (T n)) * ‖w‖ := by
  apply vecSeq_norm_le_of_tsum_le _ (by positivity)
  rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun n => hsSq_nonneg _), ← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun n => norm_sq_matOp_apply_le (T n) w)
    (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => norm_sq_matOp_apply_le (T n) w)
      (h.mul_right _)) (h.mul_right _)

/-- The column synthesis as a bounded operator `V → ℓ²(ℕ; V)`. -/
def colSynth (T : ℕ → Matrix (Fin d) (Fin d) ℂ) (h : Summable fun n => hsSq (T n)) :
    Fib d →L[ℂ] FibSeq d :=
  (colSynthLinear T h).mkContinuous _ (norm_colSynthLinear_le T h)

@[simp] theorem colSynth_apply (T : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (h : Summable fun n => hsSq (T n)) (w : Fib d) (n : ℕ) :
    (colSynth T h w : ℕ → Fib d) n = matOp (T n) w := rfl

/-- If every column family is square summable, the family is Hilbert--Schmidt summable. -/
theorem summable_hsSq_of_forall (T : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ w : Fib d, Summable fun n => ‖matOp (T n) w‖ ^ 2) :
    Summable fun n => hsSq (T n) := by
  simp_rw [hsSq_eq_sum_col]
  exact summable_sum fun j _ => h _

/-! ## The operator certificate stream -/

/-- A uniformly bounded stream of invertible certificate matrices (OP.1)–(OP.2). -/
structure OpCertStream (d : ℕ) where
  C : ℕ → Matrix (Fin d) (Fin d) ℂ
  unit : ∀ n, IsUnit (C n)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  le_bound : ∀ n, ‖matOp (C n)‖ ≤ bound

namespace OpCertStream

variable (a : OpCertStream d)

/-- Block diagonal `x ↦ (C_n x_n)`. -/
def blockDiag : FibSeq d →L[ℂ] FibSeq d :=
  RHTower.rectangularBlockOperator (fun n => matOp (a.C n)) a.bound_nonneg a.le_bound

/-- The weighted backward shift `(W x)_n = C_n x_{n+1}`. -/
def weight : FibSeq d →L[ℂ] FibSeq d := a.blockDiag ∘L vecBack

/-- The completed genealogy `(G x)_n = x_n - C_n x_{n+1}` (OP.20). -/
def genealogy : FibSeq d →L[ℂ] FibSeq d := ContinuousLinearMap.id ℂ _ - a.weight

theorem genealogy_apply (x : FibSeq d) (n : ℕ) :
    (a.genealogy x : ℕ → Fib d) n = (x : ℕ → Fib d) n - matOp (a.C n) ((x : ℕ → Fib d) (n + 1)) :=
  rfl

/-- Prefix transports `A_n`. -/
abbrev A (n : ℕ) : Matrix (Fin d) (Fin d) ℂ := opPrefix a.C n

theorem A_isUnit (n : ℕ) : IsUnit (a.A n) := opPrefix_isUnit a.unit n

/-! ### Theorem 5.1(1): bounded semantic packet -/

/-- **(OP.22)** The semantic packet `x ↦ ∑ A_n x_n` extends to a bounded map exactly when
`∑ ‖A_n‖²_HS < ∞`. -/
theorem exists_semantic_iff :
    (∃ B : FibSeq d →L[ℂ] Fib d, ∀ n (v : Fib d), B (lp.single 2 n v) = matOp (a.A n) v) ↔
      Summable fun n => hsSq (a.A n) := by
  constructor
  · rintro ⟨B, hB⟩
    have hcoord : ∀ w n, (ContinuousLinearMap.adjoint B w : ℕ → Fib d) n = matOp (star (a.A n)) w := by
      intro w n
      apply ext_inner_right ℂ
      intro v
      rw [← lp.inner_single_right, ContinuousLinearMap.adjoint_inner_left, hB, matOp_star,
        ContinuousLinearMap.adjoint_inner_left]
    have hsum : ∀ w : Fib d, Summable fun n => ‖matOp (star (a.A n)) w‖ ^ 2 := by
      intro w
      have := vecSeq_summable_sq (ContinuousLinearMap.adjoint B w)
      simpa [hcoord] using this
    have := summable_hsSq_of_forall (fun n => star (a.A n)) hsum
    simpa [hsSq_star] using this
  · intro h
    have h' : Summable fun n => hsSq (star (a.A n)) := by simpa [hsSq_star] using h
    refine ⟨ContinuousLinearMap.adjoint (colSynth (fun n => star (a.A n)) h'), fun n v => ?_⟩
    apply ext_inner_left ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right, colSynth_apply,
      matOp_star, ContinuousLinearMap.adjoint_inner_left]

/-! ### Theorem 5.1(2): bounded lineage packet -/

/-- **(OP.23)** The lineage packet `v ↦ (A_n⁻¹ v)_n` extends to a bounded map exactly when
`∑ ‖A_n⁻¹‖²_HS < ∞`. -/
theorem exists_lineage_iff :
    (∃ Q : Fib d →L[ℂ] FibSeq d, ∀ v n, (Q v : ℕ → Fib d) n = matOp (a.A n)⁻¹ v) ↔
      Summable fun n => hsSq (a.A n)⁻¹ := by
  constructor
  · rintro ⟨Q, hQ⟩
    apply summable_hsSq_of_forall
    intro w
    have := vecSeq_summable_sq (Q w)
    simpa [hQ] using this
  · intro h
    exact ⟨colSynth (fun n => (a.A n)⁻¹) h, fun v n => rfl⟩

/-- **Theorem 5.1(3)** For `d ≥ 1` the two admissions exclude each other. -/
theorem not_summable_both (hd : 0 < d) :
    ¬ ((Summable fun n => hsSq (a.A n)) ∧ Summable fun n => hsSq (a.A n)⁻¹) := by
  rintro ⟨hA, hQ⟩
  set SA := ∑' n, hsSq (a.A n)
  set SQ := ∑' n, hsSq (a.A n)⁻¹
  obtain ⟨N, hN⟩ := exists_nat_gt (SA * SQ)
  have hunc := opPolar_uncertainty a.unit N
  have hE1 : opSemanticEnergy a.C N ≤ SA :=
    hA.sum_le_tsum _ fun n _ => hsSq_nonneg _
  have hE2 : opLineageEnergy a.C N ≤ SQ :=
    hQ.sum_le_tsum _ fun n _ => hsSq_nonneg _
  have hE1' : 0 ≤ opSemanticEnergy a.C N := Finset.sum_nonneg fun _ _ => hsSq_nonneg _
  have hE2' : 0 ≤ opLineageEnergy a.C N := Finset.sum_nonneg fun _ _ => hsSq_nonneg _
  have hprod : opSemanticEnergy a.C N * opLineageEnergy a.C N ≤ SA * SQ :=
    mul_le_mul hE1 hE2 hE2' (hE1'.trans hE1)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlow : ((N : ℝ) + 1) ^ 2 ≤ ((d * (N + 1) : ℕ) : ℝ) ^ 2 := by
    push_cast
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have : ((N : ℝ) + 1) ^ 2 ≤ SA * SQ := hlow.trans (hunc.trans hprod)
  nlinarith

/-! ### Theorem 5.1(4): the kernel is the admitted hidden-lineage space -/

/-- The admitted hidden-lineage space `V₋ = {v : ∑ ‖A_n⁻¹ v‖² < ∞}` (OP.21). -/
def hiddenLineage : Submodule ℂ (Fib d) where
  carrier := {v | Summable fun n => ‖matOp (a.A n)⁻¹ v‖ ^ 2}
  zero_mem' := by simp
  add_mem' {v w} hv hw := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) ((hv.add hw).mul_left 2)
    rw [map_add]
    have h := norm_add_le (matOp (a.A n)⁻¹ v) (matOp (a.A n)⁻¹ w)
    nlinarith [norm_nonneg (matOp (a.A n)⁻¹ v + matOp (a.A n)⁻¹ w),
      norm_nonneg (matOp (a.A n)⁻¹ v), norm_nonneg (matOp (a.A n)⁻¹ w),
      sq_nonneg (‖matOp (a.A n)⁻¹ v‖ - ‖matOp (a.A n)⁻¹ w‖)]
  smul_mem' c v hv := by
    show Summable fun n => ‖matOp (a.A n)⁻¹ (c • v)‖ ^ 2
    simp_rw [map_smul, norm_smul, mul_pow]
    exact hv.mul_left _

/-- The lineage vector of an admitted direction. -/
def lineageVec (v : a.hiddenLineage) : FibSeq d :=
  ⟨fun n => matOp (a.A n)⁻¹ v, memℓp_of_summable_sq v.2⟩

theorem matOp_C_lineage (n : ℕ) (v : Fib d) :
    matOp (a.C n) (matOp (a.A (n + 1))⁻¹ v) = matOp (a.A n)⁻¹ v := by
  rw [← matOp_mul_apply, mul_opPrefix_inv_succ a.unit]

theorem genealogy_lineageVec (v : a.hiddenLineage) : a.genealogy (a.lineageVec v) = 0 := by
  refine lp.ext (funext fun n => ?_)
  rw [genealogy_apply]
  show matOp (a.A n)⁻¹ v - matOp (a.C n) (matOp (a.A (n + 1))⁻¹ v) = 0
  rw [matOp_C_lineage, sub_self]

/-- Kernel vectors are determined by their zeroth coordinate. -/
theorem genealogy_eq_zero_iff (x : FibSeq d) :
    a.genealogy x = 0 ↔ ∀ n, (x : ℕ → Fib d) n = matOp (a.A n)⁻¹ ((x : ℕ → Fib d) 0) := by
  constructor
  · intro hx n
    induction n with
    | zero => simp
    | succ n ih =>
        have h := congrArg (fun y : FibSeq d => (y : ℕ → Fib d) n) hx
        simp only [genealogy_apply, lp.coeFn_zero, Pi.zero_apply, sub_eq_zero] at h
        have hinv : (a.C n)⁻¹ * a.C n = 1 :=
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (a.unit n))
        have hA : (a.A (n + 1))⁻¹ = (a.C n)⁻¹ * (a.A n)⁻¹ := by
          rw [A, opPrefix_succ, Matrix.mul_inv_rev]
        calc (x : ℕ → Fib d) (n + 1) = matOp ((a.C n)⁻¹ * a.C n) ((x : ℕ → Fib d) (n + 1)) := by
              rw [hinv, matOp_one_apply]
          _ = matOp (a.C n)⁻¹ (matOp (a.C n) ((x : ℕ → Fib d) (n + 1))) := matOp_mul_apply _ _ _
          _ = matOp (a.C n)⁻¹ (matOp (a.A n)⁻¹ ((x : ℕ → Fib d) 0)) := by rw [← h, ih]
          _ = matOp (a.A (n + 1))⁻¹ ((x : ℕ → Fib d) 0) := by rw [hA, matOp_mul_apply]
  · intro hx
    refine lp.ext (funext fun n => ?_)
    rw [genealogy_apply, hx n, hx (n + 1), lp.coeFn_zero, Pi.zero_apply, matOp_C_lineage,
      sub_self]

/-- **(OP.24)** `V₋ ≅ ker G` via `v ↦ (A_n⁻¹ v)_n`. -/
def hiddenLineageEquiv :
    a.hiddenLineage ≃ₗ[ℂ] LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d) :=
  LinearEquiv.ofBijective
    { toFun := fun v => ⟨a.lineageVec v, a.genealogy_lineageVec v⟩
      map_add' := fun v w => by
        apply Subtype.ext; refine lp.ext (funext fun n => ?_); simp [lineageVec]
      map_smul' := fun c v => by
        apply Subtype.ext; refine lp.ext (funext fun n => ?_); simp [lineageVec] }
    ⟨fun v w h => by
      have := congrArg (fun y : LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d) =>
        ((y : FibSeq d) : ℕ → Fib d) 0) h
      change matOp (a.A 0)⁻¹ (v : Fib d) = matOp (a.A 0)⁻¹ (w : Fib d) at this
      rw [A, opPrefix_zero, inv_one, matOp_one_apply, matOp_one_apply] at this
      exact Subtype.ext this,
     fun y => by
      have hy : a.genealogy (y : FibSeq d) = 0 := y.2
      have hform := (a.genealogy_eq_zero_iff y).mp hy
      have hmem : ((y : FibSeq d) : ℕ → Fib d) 0 ∈ a.hiddenLineage := by
        show Summable fun n => ‖matOp (a.A n)⁻¹ (((y : FibSeq d) : ℕ → Fib d) 0)‖ ^ 2
        simp_rw [← hform]
        exact vecSeq_summable_sq _
      refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
      refine lp.ext (funext fun n => ?_)
      exact (hform n).symm⟩

/-! ### Theorem 5.1(5): dense range -/

theorem genealogy_single_zero (v : Fib d) :
    a.genealogy (lp.single 2 0 v) = lp.single 2 0 v := by
  refine lp.ext (funext fun n => ?_)
  rw [genealogy_apply, lp.single_apply, lp.single_apply]
  simp [Pi.single_apply]

theorem genealogy_single_succ (n : ℕ) (v : Fib d) :
    a.genealogy (lp.single 2 (n + 1) v) =
      lp.single 2 (n + 1) v - lp.single 2 n (matOp (a.C n) v) := by
  refine lp.ext (funext fun k => ?_)
  rw [genealogy_apply, lp.coeFn_sub, Pi.sub_apply]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : k = n
  · subst h; simp
  · by_cases h' : k = n + 1
    · subst h'; simp
    · rw [if_neg h', if_neg (by omega), if_neg h]; simp

/-- **Theorem 5.1(5)** The range of `G` is dense. -/
theorem dense_range_genealogy : Dense (Set.range a.genealogy) := by
  have hperp : (LinearMap.range (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hortho : ∀ x, ⟪a.genealogy x, y⟫_ℂ = 0 := fun x =>
      (Submodule.mem_orthogonal _ _).mp hy _ ⟨x, rfl⟩
    have hcoord : ∀ n, (y : ℕ → Fib d) n = 0 := by
      intro n
      induction n with
      | zero =>
          apply ext_inner_left ℂ
          intro v
          have := hortho (lp.single 2 0 v)
          rw [genealogy_single_zero, lp.inner_single_left] at this
          rw [this, inner_zero_right]
      | succ n ih =>
          apply ext_inner_left ℂ
          intro v
          have := hortho (lp.single 2 (n + 1) v)
          rw [genealogy_single_succ, inner_sub_left, lp.inner_single_left, lp.inner_single_left,
            ih, inner_zero_right, sub_zero] at this
          rw [this, inner_zero_right]
    refine lp.ext (funext fun n => ?_); rw [hcoord n]; rfl
  have hclos : (LinearMap.range
      (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]
  have h := Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos
  simpa [LinearMap.coe_range] using h

end OpCertStream

/-! ## Generic facts -/

/-- A compact operator from a Hilbert space into any normed space sends a bounded weakly-null
sequence to zero. -/
theorem tendsto_compactOperator_of_weaklyNull_hilbert {H Y : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (K : H →L[ℂ] Y) (hK : IsCompactOperator K) (x : ℕ → H) (hb : ∀ n, ‖x n‖ ≤ 1)
    (hweak : ∀ z, Tendsto (fun n => ⟪z, x n⟫_ℂ) atTop (𝓝 0)) :
    Tendsto (fun n => K (x n)) atTop (𝓝 0) := by
  have hfun : ∀ φ : Y →L[ℂ] ℂ, Tendsto (fun n => φ (K (x n))) atTop (𝓝 0) := by
    intro φ
    set z := (InnerProductSpace.toDual ℂ H).symm (φ ∘L K)
    have hz : ∀ n, φ (K (x n)) = ⟪z, x n⟫_ℂ := by
      intro n; rw [InnerProductSpace.toDual_symm_apply]; rfl
    simp_rw [hz]
    exact hweak z
  by_contra hne
  rw [Metric.tendsto_atTop] at hne
  simp only [not_forall, not_exists, not_lt] at hne
  obtain ⟨ε, hε, hfreq⟩ := hne
  have hfreq' : ∃ᶠ n in atTop, ε ≤ ‖K (x n)‖ := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, h⟩ := hfreq N
    exact ⟨n, hn, by simpa using h⟩
  obtain ⟨φs, hmono, hφ⟩ := Filter.extraction_of_frequently_atTop hfreq'
  have hKc := hK.isCompact_closure_image_closedBall 1
  have hmem : ∀ k, K (x (φs k)) ∈ closure (K '' Metric.closedBall 0 1) := fun k =>
    subset_closure ⟨x (φs k), by simpa using hb (φs k), rfl⟩
  obtain ⟨y, -, ψ, hψ, hlim⟩ := hKc.tendsto_subseq hmem
  have hy : ε ≤ ‖y‖ :=
    ge_of_tendsto ((continuous_norm.tendsto y).comp hlim)
      (Eventually.of_forall fun k => hφ (ψ k))
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  obtain ⟨g, -, hgy⟩ := exists_dual_vector ℂ y (norm_ne_zero_iff.mpr hy0)
  have h1 := (hfun g).comp (hmono.comp hψ).tendsto_atTop
  have h2 := (g.continuous.tendsto y).comp hlim
  have hzero : g y = 0 := tendsto_nhds_unique h2 h1
  rw [hgy] at hzero
  have : ‖y‖ = 0 := (RCLike.ofReal_eq_zero (K := ℂ)).mp hzero
  exact hy0 (norm_eq_zero.mp this)

/-- Joint lower bound of the observer `x ↦ (K x, G x)`. -/
def IsSumJointlyBoundedBelow {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (K : H →L[ℂ] Y) (G : H →L[ℂ] H) : Prop :=
  ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖K x‖ + ‖G x‖

namespace OpCertStream

variable (a : OpCertStream d)

/-! ### Theorem 6.1: directional critical mirage -/

/-- Directional lineage energy `L_N(v) = (∑_{n ≤ N} ‖A_n⁻¹ v‖²)^{1/2}` (OP.25). -/
def dirEnergy (v : Fib d) (N : ℕ) : ℝ :=
  Real.sqrt (∑ n ∈ Finset.range (N + 1), ‖matOp (a.A n)⁻¹ v‖ ^ 2)

theorem dirEnergy_pos {v : Fib d} (hv : v ≠ 0) (N : ℕ) : 0 < a.dirEnergy v N := by
  apply Real.sqrt_pos.mpr
  calc (0 : ℝ) < ‖matOp (a.A 0)⁻¹ v‖ ^ 2 := by
        rw [A, opPrefix_zero, inv_one, matOp_one_apply]; positivity
    _ ≤ _ := Finset.single_le_sum (f := fun n => ‖matOp (a.A n)⁻¹ v‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.succ_pos N))

/-- The normalized directional approximate lineage `u_N(v)` (OP.25). -/
def dirHistory (v : Fib d) (N : ℕ) : FibSeq d :=
  ((a.dirEnergy v N)⁻¹ : ℂ) • ∑ n ∈ Finset.range (N + 1), lp.single 2 n (matOp (a.A n)⁻¹ v)

theorem dirHistory_apply (v : Fib d) (N k : ℕ) :
    (a.dirHistory v N : ℕ → Fib d) k =
      ((a.dirEnergy v N)⁻¹ : ℂ) • if k ≤ N then matOp (a.A k)⁻¹ v else 0 := by
  rw [dirHistory, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply]
  congr 1
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem norm_dirHistory {v : Fib d} (hv : v ≠ 0) (N : ℕ) : ‖a.dirHistory v N‖ = 1 := by
  have hsum := lp.norm_sum_single (p := 2) (E := fun _ : ℕ => Fib d) (by norm_num)
    (fun n => matOp (a.A n)⁻¹ v) (Finset.range (N + 1))
  have hsum' : ‖∑ n ∈ Finset.range (N + 1),
      (lp.single 2 n (matOp (a.A n)⁻¹ v) : FibSeq d)‖ = a.dirEnergy v N := by
    rw [dirEnergy, ← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    simpa using hsum
  have hpos := a.dirEnergy_pos hv N
  rw [dirHistory, norm_smul, hsum', norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- **Theorem 6.1(2)** `G u_N(v) = L_N(v)⁻¹ A_N⁻¹ v · e_N`. -/
theorem genealogy_dirHistory (v : Fib d) (N : ℕ) :
    a.genealogy (a.dirHistory v N) =
      ((a.dirEnergy v N)⁻¹ : ℂ) • lp.single 2 N (matOp (a.A N)⁻¹ v) := by
  refine lp.ext (funext fun k => ?_)
  rw [genealogy_apply, dirHistory_apply, dirHistory_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, map_smul]
  rcases lt_trichotomy k N with h | h | h
  · rw [if_pos h.le, if_pos (by omega : k + 1 ≤ N), if_neg h.ne, matOp_C_lineage, sub_self,
      smul_zero]
  · subst h
    rw [if_pos le_rfl, if_neg (by omega), if_pos rfl, map_zero, smul_zero, sub_zero]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), map_zero, smul_zero,
      sub_zero]

theorem norm_genealogy_dirHistory {v : Fib d} (hv : v ≠ 0) (N : ℕ) :
    ‖a.genealogy (a.dirHistory v N)‖ = ‖matOp (a.A N)⁻¹ v‖ / a.dirEnergy v N := by
  rw [genealogy_dirHistory, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.dirEnergy_pos hv N), div_eq_inv_mul]

/-- **Theorem 6.1(1)** `u_N(v)` is weakly null when `L_N(v) → ∞`. -/
theorem dirHistory_weaklyNull {v : Fib d} (hv : v ≠ 0)
    (hL : Tendsto (a.dirEnergy v) atTop atTop) (z : FibSeq d) :
    Tendsto (fun N => ⟪z, a.dirHistory v N⟫_ℂ) atTop (𝓝 0) := by
  apply tendsto_inner_vecSeq_of_coord (C := 1) (a.dirHistory v) zero_le_one
    (fun N => (a.norm_dirHistory hv N).le)
  intro k
  have hinv : Tendsto (fun N => ((a.dirEnergy v N)⁻¹ : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hL.inv_tendsto_atTop
    rw [Complex.ofReal_zero] at this
    refine this.congr fun N => ?_
    simp
  have := hinv.smul_const (matOp (a.A k)⁻¹ v)
  rw [zero_smul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  rw [dirHistory_apply, if_pos hN]

/-- **Theorem 6.1(3)** No compact observer repairs a critical lineage direction. -/
theorem not_isJointlyBoundedBelow_of_dirMirage {v : Fib d} (hv : v ≠ 0)
    (hL : Tendsto (a.dirEnergy v) atTop atTop)
    (hratio : Tendsto (fun N => ‖matOp (a.A N)⁻¹ v‖ / a.dirEnergy v N) atTop (𝓝 0))
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] (K : FibSeq d →L[ℂ] Y)
    (hK : IsCompactOperator K) : ¬ IsSumJointlyBoundedBelow K a.genealogy := by
  rintro ⟨c, hc, hb⟩
  have hK0 := tendsto_compactOperator_of_weaklyNull_hilbert K hK (a.dirHistory v)
    (fun N => (a.norm_dirHistory hv N).le) (a.dirHistory_weaklyNull hv hL)
  have hsum : Tendsto (fun N => ‖K (a.dirHistory v N)‖ + ‖a.genealogy (a.dirHistory v N)‖)
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun N => ‖a.genealogy (a.dirHistory v N)‖) atTop (𝓝 0) := by
      simp_rw [a.norm_genealogy_dirHistory hv]; exact hratio
    have := (tendsto_norm_zero.comp hK0).add h2
    simpa using this
  obtain ⟨N, hN⟩ := (hsum.eventually (gt_mem_nhds hc)).exists
  have := hb (a.dirHistory v N)
  rw [a.norm_dirHistory hv, mul_one] at this
  linarith

/-! ### Theorem 7.1: closed range and minimal compact repair rank -/

instance : FiniteDimensional ℂ (LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d)) :=
  LinearEquiv.finiteDimensional a.hiddenLineageEquiv

theorem finrank_ker_genealogy :
    Module.finrank ℂ (LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d)) =
      Module.finrank ℂ a.hiddenLineage :=
  a.hiddenLineageEquiv.finrank_eq.symm

theorem surjective_of_isClosed_range (hcl : IsClosed (Set.range a.genealogy)) :
    Function.Surjective a.genealogy := by
  intro y
  have : y ∈ closure (Set.range a.genealogy) := by
    rw [a.dense_range_genealogy.closure_eq]; trivial
  rwa [hcl.closure_eq] at this

/-- **Theorem 7.1** For closed range, an observer repairs `G` exactly when it is injective on
`ker G`. -/
theorem isJointlyBoundedBelow_iff_of_isClosed (hcl : IsClosed (Set.range a.genealogy))
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] (K : FibSeq d →L[ℂ] Y) :
    IsSumJointlyBoundedBelow K a.genealogy ↔
      ∀ x ∈ LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d), K x = 0 → x = 0 := by
  set N := LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d)
  constructor
  · rintro ⟨c, hc, hb⟩ x hx hKx
    have := hb x
    have hGx : a.genealogy x = 0 := hx
    rw [hKx, hGx, norm_zero, norm_zero, add_zero] at this
    exact norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg x]) (norm_nonneg x))
  · intro hinj
    haveI : N.HasOrthogonalProjection := inferInstance
    -- lower bound of `G` on `Nᗮ`
    set T : Nᗮ →L[ℂ] FibSeq d := a.genealogy ∘L Nᗮ.subtypeL
    have hTker : LinearMap.ker (T : Nᗮ →ₗ[ℂ] FibSeq d) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro u hu
      have hu' : (u : FibSeq d) ∈ N := hu
      have : (u : FibSeq d) ∈ N ⊓ Nᗮ := ⟨hu', u.2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
      exact Subtype.ext this
    have hTrange : Set.range T = Set.range a.genealogy := by
      apply Set.Subset.antisymm
      · rintro _ ⟨u, rfl⟩; exact ⟨u, rfl⟩
      · rintro _ ⟨x, rfl⟩
        obtain ⟨k, hk, u, hu, rfl⟩ := N.exists_add_mem_mem_orthogonal x
        refine ⟨⟨u, hu⟩, ?_⟩
        show a.genealogy u = a.genealogy (k + u)
        rw [map_add, show a.genealogy k = 0 from hk, zero_add]
    obtain ⟨γ, hγ, hγb⟩ := (exists_pos_mul_norm_le_iff T).mpr ⟨hTker, hTrange ▸ hcl⟩
    -- lower bound of `K` on the finite-dimensional kernel
    set KN : N →ₗ[ℂ] Y := (K : FibSeq d →ₗ[ℂ] Y).comp N.subtype
    have hKN : Function.Injective KN := by
      intro k₁ k₂ h
      have : K ((k₁ : FibSeq d) - k₂) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr h
      exact Subtype.ext (sub_eq_zero.mp (hinj _ (Submodule.sub_mem _ k₁.2 k₂.2) this))
    set e := (LinearEquiv.ofInjective KN hKN).toContinuousLinearEquiv
    have hκ : ∀ k : N, ‖(k : FibSeq d)‖ ≤
        ‖(e.symm : LinearMap.range KN →L[ℂ] N)‖ * ‖K k‖ := by
      intro k
      have h1 : k = e.symm (e k) := (e.symm_apply_apply k).symm
      calc ‖(k : FibSeq d)‖ = ‖k‖ := rfl
        _ = ‖e.symm (e k)‖ := by rw [← h1]
        _ ≤ ‖(e.symm : LinearMap.range KN →L[ℂ] N)‖ * ‖e k‖ :=
            (e.symm : LinearMap.range KN →L[ℂ] N).le_opNorm _
        _ = ‖(e.symm : LinearMap.range KN →L[ℂ] N)‖ * ‖K k‖ := rfl
    set E := ‖(e.symm : LinearMap.range KN →L[ℂ] N)‖
    set C := (E + 1) * (1 + ‖K‖ / γ) + 1 / γ
    have hCpos : 0 < C := by positivity
    refine ⟨C⁻¹, inv_pos.mpr hCpos, fun x => ?_⟩
    obtain ⟨k, hk, u, hu, rfl⟩ := N.exists_add_mem_mem_orthogonal x
    have hGx : a.genealogy (k + u) = a.genealogy u := by
      rw [map_add, show a.genealogy k = 0 from hk, zero_add]
    have hu_le : ‖u‖ ≤ ‖a.genealogy (k + u)‖ / γ := by
      rw [hGx, le_div_iff₀ hγ, mul_comm]; exact hγb ⟨u, hu⟩
    have hE0 : 0 ≤ E := norm_nonneg (e.symm : LinearMap.range KN →L[ℂ] N)
    have hk_le : ‖k‖ ≤ E * (‖K (k + u)‖ + ‖K‖ * ‖u‖) := by
      have h1 := hκ ⟨k, hk⟩
      have h2 : ‖K k‖ ≤ ‖K (k + u)‖ + ‖K‖ * ‖u‖ := by
        calc ‖K k‖ = ‖K (k + u) - K u‖ := by rw [map_add, add_sub_cancel_right]
          _ ≤ ‖K (k + u)‖ + ‖K u‖ := norm_sub_le _ _
          _ ≤ ‖K (k + u)‖ + ‖K‖ * ‖u‖ := add_le_add le_rfl (K.le_opNorm u)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hE0)
    rw [inv_mul_eq_div, div_le_iff₀ hCpos]
    have hKx := norm_nonneg (K (k + u))
    have hGx0 := norm_nonneg (a.genealogy (k + u))
    have hK0 := norm_nonneg K
    have hu0 := norm_nonneg u
    calc ‖k + u‖ ≤ ‖k‖ + ‖u‖ := norm_add_le _ _
      _ ≤ E * (‖K (k + u)‖ + ‖K‖ * (‖a.genealogy (k + u)‖ / γ)) +
            ‖a.genealogy (k + u)‖ / γ := by
          have := mul_le_mul_of_nonneg_left hu_le hK0
          nlinarith [mul_le_mul_of_nonneg_left (add_le_add_left this ‖K (k + u)‖) hE0]
      _ ≤ (‖K (k + u)‖ + ‖a.genealogy (k + u)‖) * C := by
          have hdiff : (‖K (k + u)‖ + ‖a.genealogy (k + u)‖) * C -
              (E * (‖K (k + u)‖ + ‖K‖ * (‖a.genealogy (k + u)‖ / γ)) +
                ‖a.genealogy (k + u)‖ / γ) =
              ‖K (k + u)‖ * (1 + ‖K‖ / γ + 1 / γ) + ‖K (k + u)‖ * E * (‖K‖ / γ) +
                ‖a.genealogy (k + u)‖ * (E + 1 + ‖K‖ / γ) := by
            simp only [C]; field_simp; ring
          have hnn : 0 ≤ ‖K (k + u)‖ * (1 + ‖K‖ / γ + 1 / γ) + ‖K (k + u)‖ * E * (‖K‖ / γ) +
              ‖a.genealogy (k + u)‖ * (E + 1 + ‖K‖ / γ) := by positivity
          linarith

/-- **Theorem 7.1(2)** Every finite-rank repair has rank at least `dim V₋`. -/
theorem finrank_hiddenLineage_le_rank (hcl : IsClosed (Set.range a.genealogy))
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] (K : FibSeq d →L[ℂ] Y)
    [FiniteDimensional ℂ (LinearMap.range (K : FibSeq d →ₗ[ℂ] Y))]
    (hK : IsSumJointlyBoundedBelow K a.genealogy) :
    Module.finrank ℂ a.hiddenLineage ≤
      Module.finrank ℂ (LinearMap.range (K : FibSeq d →ₗ[ℂ] Y)) := by
  have hinj := (a.isJointlyBoundedBelow_iff_of_isClosed hcl K).mp hK
  set N := LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d)
  set f : N →ₗ[ℂ] LinearMap.range (K : FibSeq d →ₗ[ℂ] Y) :=
    LinearMap.codRestrict _ ((K : FibSeq d →ₗ[ℂ] Y).comp N.subtype) fun k => ⟨k, rfl⟩
  have hf : Function.Injective f := by
    intro k₁ k₂ h
    have h' : K ((k₁ : FibSeq d) - k₂) = 0 := by
      have := congrArg Subtype.val h
      simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        ContinuousLinearMap.coe_coe] at this
      rw [map_sub, this, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hinj _ (Submodule.sub_mem _ k₁.2 k₂.2) h'))
  rw [← a.finrank_ker_genealogy]
  exact LinearMap.finrank_le_finrank_of_injective hf

/-- **Theorem 7.1(1),(3),(4)** A compact repair of rank exactly `dim V₋` exists: the orthogonal
projection onto the hidden-lineage kernel. -/
theorem exists_minimal_compact_repair (hcl : IsClosed (Set.range a.genealogy)) :
    ∃ K : FibSeq d →L[ℂ] LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d),
      IsCompactOperator K ∧ IsSumJointlyBoundedBelow K a.genealogy ∧
        Module.finrank ℂ (LinearMap.range
          (K : FibSeq d →ₗ[ℂ] LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d))) =
          Module.finrank ℂ a.hiddenLineage := by
  set N := LinearMap.ker (a.genealogy : FibSeq d →ₗ[ℂ] FibSeq d)
  haveI : N.HasOrthogonalProjection := inferInstance
  refine ⟨N.orthogonalProjectionOnto, isCompactOperator_of_locallyCompactSpace_dom _, ?_, ?_⟩
  · rw [a.isJointlyBoundedBelow_iff_of_isClosed hcl]
    intro x hx hPx
    have := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := N) ⟨x, hx⟩
    rw [hPx] at this
    exact (congrArg Subtype.val this).symm
  · have hsurj : LinearMap.range (N.orthogonalProjectionOnto : FibSeq d →ₗ[ℂ] N) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro k
      exact ⟨k, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self k⟩
    rw [hsurj, finrank_top, a.finrank_ker_genealogy]

end OpCertStream

end

end GaloisForLFunctions.HTGeometry
