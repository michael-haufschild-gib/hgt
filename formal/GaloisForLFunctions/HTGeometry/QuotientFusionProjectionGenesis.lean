import Mathlib

/-!
# The coordinate-free quotient--fusion genesis theorem

Finitely many organs receive one shared gauge.  Organ `i` carries a datum `x i` in a
finite-dimensional real inner product space and reads the gauge through a linear map `A i`.
Fitting all organs with one common gauge costs

`E_shared = ⨅_u ∑_i ‖x i - A i u‖²`,

while fitting each organ with its own gauge costs `E_separate = ∑_i dist(x i, ran (A i))²`.  Their
difference is the *genesis*: the information that exists only because the gauge is shared.

Splitting each residual by Pythagoras along `ran (A i)` shows the genesis is exactly the shared
fit of the locally optimal histories, hence nonnegative, and that it vanishes precisely when the
locally optimal histories have one common realization.  The genesis can be positive while every
organ separately fits perfectly.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, FiniteDimensional ℝ (H i)]

/-- The locally optimal gauge history of one organ: the orthogonal projection of its datum onto
the range of its gauge map. -/
def localOptimalHistory (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (i : ι) : H i :=
  (LinearMap.range (A i)).starProjection (x i)

omit [Fintype ι] in
theorem localOptimalHistory_mem (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (i : ι) :
    localOptimalHistory A x i ∈ LinearMap.range (A i) :=
  Submodule.starProjection_apply_mem _ _

omit [Fintype ι] in
/-- **Organwise Pythagoras.**  The residual of any shared gauge splits into the inherited local
residual and the generated residual against the locally optimal history. -/
theorem norm_sub_apply_sq (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (i : ι) (u : K) :
    ‖x i - A i u‖ ^ 2
      = ‖x i - localOptimalHistory A x i‖ ^ 2 + ‖localOptimalHistory A x i - A i u‖ ^ 2 := by
  have hmem : localOptimalHistory A x i - A i u ∈ LinearMap.range (A i) :=
    Submodule.sub_mem _ (localOptimalHistory_mem A x i) (LinearMap.mem_range_self _ _)
  have hperp : ⟪x i - localOptimalHistory A x i, localOptimalHistory A x i - A i u⟫_ℝ = 0 := by
    have h := (Submodule.sub_starProjection_mem_orthogonal
      (K := LinearMap.range (A i)) (x i)) _ hmem
    rw [real_inner_comm]
    exact h
  have hsplit : x i - A i u
      = (x i - localOptimalHistory A x i) + (localOptimalHistory A x i - A i u) := by
    abel
  rw [hsplit, norm_add_sq_real, hperp]
  ring

/-- The organwise splitting, summed. -/
theorem sum_norm_sub_apply_sq (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (u : K) :
    ∑ i, ‖x i - A i u‖ ^ 2
      = (∑ i, ‖x i - localOptimalHistory A x i‖ ^ 2)
        + ∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => norm_sub_apply_sq A x i u)

/-- `(QFG.1)`, shared: the cost of fitting every organ with one common gauge. -/
def sharedEnergy (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : ℝ :=
  ⨅ u : K, ∑ i, ‖x i - A i u‖ ^ 2

/-- `(QFG.1)`, separate: the cost of fitting every organ with its own gauge. -/
def separateEnergy (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : ℝ :=
  ∑ i, ‖x i - localOptimalHistory A x i‖ ^ 2

/-- The generated fit: the shared cost of the locally optimal histories. -/
def generatedEnergy (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : ℝ :=
  ⨅ u : K, ∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2

/-- `(QFG.2)`, the quotient--fusion genesis. -/
def quotientFusionGenesis (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : ℝ :=
  sharedEnergy A x - separateEnergy A x

theorem bddBelow_generatedRange (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    BddBelow (Set.range fun u : K => ∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2) := by
  refine ⟨0, ?_⟩
  rintro r ⟨u, rfl⟩
  positivity

theorem generatedEnergy_nonneg (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    0 ≤ generatedEnergy A x :=
  le_ciInf (fun u => by positivity)

/-- **(QFG.3), first half.**  The genesis is exactly the shared fit of the locally optimal
histories. -/
theorem quotientFusionGenesis_eq (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    quotientFusionGenesis A x = generatedEnergy A x := by
  have hfun : (fun u : K => ∑ i, ‖x i - A i u‖ ^ 2)
      = fun u : K => (∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2) + separateEnergy A x := by
    funext u
    rw [sum_norm_sub_apply_sq A x u, separateEnergy]
    ring
  have hshift : sharedEnergy A x = generatedEnergy A x + separateEnergy A x := by
    rw [sharedEnergy, hfun, generatedEnergy]
    exact (ciInf_add (bddBelow_generatedRange A x) (separateEnergy A x)).symm
  rw [quotientFusionGenesis, hshift]
  ring

/-- **(QFG.3), second half.**  The genesis is nonnegative. -/
theorem quotientFusionGenesis_nonneg (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    0 ≤ quotientFusionGenesis A x := by
  rw [quotientFusionGenesis_eq]
  exact generatedEnergy_nonneg A x

/-- **Corollary 2.2, `(QFG.5)`.**  The shared energy splits exactly into inherited local
information and collectively generated information. -/
theorem sharedEnergy_decomposition (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    sharedEnergy A x = separateEnergy A x + generatedEnergy A x := by
  have h := quotientFusionGenesis_eq A x
  rw [quotientFusionGenesis] at h
  linarith

/-! ## Attainment and the exact zero classification -/

variable [FiniteDimensional ℝ K]

/-- The joint gauge map into the `L²` product of the organs. -/
def jointGaugeMap (A : ∀ i, K →ₗ[ℝ] H i) : K →ₗ[ℝ] PiLp 2 H :=
  (WithLp.linearEquiv 2 ℝ (∀ i, H i)).symm.toLinearMap.comp (LinearMap.pi A)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (H i)] [FiniteDimensional ℝ K] in
theorem jointGaugeMap_ofLp (A : ∀ i, K →ₗ[ℝ] H i) (u : K) (i : ι) :
    (jointGaugeMap A u).ofLp i = A i u := rfl

/-- The locally optimal histories assembled into the `L²` product. -/
def jointLocalOptimalHistory (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) : PiLp 2 H :=
  (WithLp.linearEquiv 2 ℝ (∀ i, H i)).symm (localOptimalHistory A x)

omit [Fintype ι] [FiniteDimensional ℝ K] in
theorem jointLocalOptimalHistory_ofLp (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (i : ι) :
    (jointLocalOptimalHistory A x).ofLp i = localOptimalHistory A x i := rfl

omit [FiniteDimensional ℝ K] in
theorem norm_joint_sub_sq (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) (u : K) :
    ‖jointLocalOptimalHistory A x - jointGaugeMap A u‖ ^ 2
      = ∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun i _ => by rfl)

/-- **Attainment.**  In finite dimensions the shared fit of the locally optimal histories is
realized by an actual gauge. -/
theorem exists_generatedEnergy_eq (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    ∃ u : K, (∑ i, ‖localOptimalHistory A x i - A i u‖ ^ 2) = generatedEnergy A x := by
  classical
  set S : Submodule ℝ (PiLp 2 H) := LinearMap.range (jointGaugeMap A) with hS
  obtain ⟨u, hu⟩ : ∃ u : K, jointGaugeMap A u = S.starProjection (jointLocalOptimalHistory A x) :=
    S.starProjection_apply_mem (jointLocalOptimalHistory A x)
  refine ⟨u, le_antisymm ?_ (ciInf_le (bddBelow_generatedRange A x) u)⟩
  refine le_ciInf (fun v => ?_)
  have hmin := Submodule.starProjection_minimal (U := S) (jointLocalOptimalHistory A x)
  have hle : ‖jointLocalOptimalHistory A x - S.starProjection (jointLocalOptimalHistory A x)‖
      ≤ ‖jointLocalOptimalHistory A x - jointGaugeMap A v‖ := by
    rw [hmin]
    refine ciInf_le ⟨0, ?_⟩ (⟨jointGaugeMap A v, LinearMap.mem_range_self _ v⟩ : S)
    rintro r ⟨w, rfl⟩
    positivity
  rw [← hu] at hle
  have hsq : ‖jointLocalOptimalHistory A x - jointGaugeMap A u‖ ^ 2
      ≤ ‖jointLocalOptimalHistory A x - jointGaugeMap A v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rwa [norm_joint_sub_sq, norm_joint_sub_sq] at hsq

/-- **(QFG.4).**  The genesis vanishes exactly when the locally optimal histories have one common
realization. -/
theorem quotientFusionGenesis_eq_zero_iff (A : ∀ i, K →ₗ[ℝ] H i) (x : ∀ i, H i) :
    quotientFusionGenesis A x = 0 ↔ ∃ u : K, ∀ i, A i u = localOptimalHistory A x i := by
  rw [quotientFusionGenesis_eq]
  constructor
  · intro hzero
    obtain ⟨u, hu⟩ := exists_generatedEnergy_eq A x
    rw [hzero] at hu
    refine ⟨u, fun i => ?_⟩
    have hterm : ∀ j ∈ (Finset.univ : Finset ι),
        (0 : ℝ) ≤ ‖localOptimalHistory A x j - A j u‖ ^ 2 := fun j _ => by positivity
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hu i (Finset.mem_univ i)
    have hz : localOptimalHistory A x i - A i u = 0 := by
      have hn := pow_eq_zero_iff (n := 2) (by omega) |>.mp hj
      exact norm_eq_zero.mp hn
    exact (sub_eq_zero.mp hz).symm
  · rintro ⟨u, hu⟩
    refine le_antisymm ?_ (generatedEnergy_nonneg A x)
    refine le_of_le_of_eq (ciInf_le (bddBelow_generatedRange A x) u) ?_
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hu i, sub_self, norm_zero]
    norm_num

/-! ## Genesis without inherited information -/

/-- **The generated term of `(QFG.5)` can be positive while every inherited term vanishes.**  Two
organs that each fit perfectly on their own can still be jointly unfittable by one shared gauge:
here both read the gauge by the identity but carry opposite data. -/
theorem exists_positive_generatedEnergy_with_zero_separateEnergy :
    ∃ (A : ∀ _ : Fin 2, ℝ →ₗ[ℝ] ℝ) (x : ∀ _ : Fin 2, ℝ),
      separateEnergy A x = 0 ∧ 0 < generatedEnergy A x := by
  classical
  refine ⟨fun _ => LinearMap.id, ![1, -1], ?_, ?_⟩
  · have hloc : ∀ i : Fin 2,
        localOptimalHistory (fun _ : Fin 2 => (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ![1, -1] i
          = ![(1 : ℝ), -1] i := by
      intro i
      rw [localOptimalHistory]
      refine Submodule.starProjection_eq_self_iff.mpr ?_
      rw [LinearMap.range_id]
      trivial
    rw [separateEnergy]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hloc i, sub_self, norm_zero]
    norm_num
  · have hloc : ∀ i : Fin 2,
        localOptimalHistory (fun _ : Fin 2 => (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ![1, -1] i
          = ![(1 : ℝ), -1] i := by
      intro i
      rw [localOptimalHistory]
      refine Submodule.starProjection_eq_self_iff.mpr ?_
      rw [LinearMap.range_id]
      trivial
    have hval : ∀ u : ℝ,
        (∑ i : Fin 2, ‖localOptimalHistory (fun _ : Fin 2 => (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
          ![1, -1] i - (LinearMap.id : ℝ →ₗ[ℝ] ℝ) u‖ ^ 2) = 2 + 2 * u ^ 2 := by
      intro u
      rw [Fin.sum_univ_two, hloc 0, hloc 1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearMap.id_coe, id_eq, Real.norm_eq_abs, sq_abs]
      ring
    have hge : (2 : ℝ) ≤ generatedEnergy (fun _ : Fin 2 => (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ![1, -1] := by
      refine le_ciInf (fun u => ?_)
      rw [hval u]
      nlinarith [sq_nonneg u]
    linarith


/-! ## The Schur-complement form -/

/-- **(QFG.12).**  The Schur complement of a sum of positive semidefinite `2 × 2` blocks exceeds
the sum of the Schur complements by exactly the `c`-weighted spread of the local slopes.  In
particular the Schur complement is superadditive, and when every block has rank one — every local
Schur complement zero — the sum has positive Schur complement exactly when the local slopes are
not all equal. -/
theorem schurComplement_sum_eq {ι : Type*} [Fintype ι] [Nonempty ι] (a b c : ι → ℝ)
    (hc : ∀ i, 0 < c i) :
    (∑ i, a i) - (∑ i, b i) ^ 2 / (∑ i, c i)
      = (∑ i, (a i - b i ^ 2 / c i))
        + ∑ i, c i * (b i / c i - (∑ i, b i) / (∑ i, c i)) ^ 2 := by
  have hC : (0 : ℝ) < ∑ i, c i := Finset.sum_pos (fun i _ => hc i) Finset.univ_nonempty
  have hterm : ∀ i : ι, c i * (b i / c i - (∑ j, b j) / (∑ j, c j)) ^ 2
      = b i ^ 2 / c i - 2 * ((∑ j, b j) / (∑ j, c j)) * b i
        + c i * ((∑ j, b j) / (∑ j, c j)) ^ 2 := by
    intro i
    have hci := (hc i).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp
  ring


end

end GaloisForLFunctions.HTGeometry
