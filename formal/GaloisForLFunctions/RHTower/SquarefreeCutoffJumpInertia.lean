import GaloisForLFunctions.RHTower.SquarefreeCutoffLocalBlocks

/-!
# Inertia of the squarefree cutoff jump

For a finite family of local scales `P_i = m_i + 2` the occupancy and density tensors are

`E = ⊗ Δ_i`,   `R = ⊗ T_i = V J Vᴴ`,   `V = ⊗ U_i`,   `J = ⊗ J₀`,

and the cutoff jump is `K = (−1)^r (E − R)`.  Haynsworth additivity applied at both corners of

`[[−E, V], [Vᴴ, −J]]`

reduces the inertia of `E − R` to that of `E`, because the binary block `J − G`,
`G = Vᴴ E⁻¹ V = ⊗ G_i`, is balanced and nonsingular.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace RHTower

open Matrix GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)

/-- The occupancy tensor `E = ⊗ Δ_i`. -/
def crossingOccupancy : Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ :=
  tensorFamily fun i => localOccupancyBlock (m i)

/-- The density tensor `R = ⊗ T_i`. -/
def crossingDensity : Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ :=
  tensorFamily fun i => localDensityBlock (m i)

/-- The frame tensor `V = ⊗ U_i`. -/
def crossingFrame : Matrix (∀ i, Fin (m i + 2)) (ι → Fin 2) ℂ :=
  tensorFamily fun i => localFrame (m i)

/-- The binary signature tensor `J = ⊗ J₀`. -/
def crossingJ : Matrix (ι → Fin 2) (ι → Fin 2) ℂ := tensorFamily fun _ : ι => binaryJ

/-- The Gram tensor `G = ⊗ G_i`. -/
def crossingGram : Matrix (ι → Fin 2) (ι → Fin 2) ℂ := tensorFamily fun i => localGram (m i)

theorem crossingDensity_eq :
    crossingDensity m
      = crossingFrame m * crossingJ (ι := ι) * (crossingFrame m)ᴴ := by
  rw [crossingDensity, crossingFrame, crossingJ, tensorFamily_conjTranspose,
    tensorFamily_mul (fun i => localFrame (m i)) (fun _ : ι => binaryJ),
    tensorFamily_mul (fun i => localFrame (m i) * binaryJ) (fun i => (localFrame (m i))ᴴ)]
  rfl

theorem crossingJ_mul_self : crossingJ (ι := ι) * crossingJ = 1 := by
  rw [crossingJ, tensorFamily_mul]
  have hfun : (fun _ : ι => binaryJ * binaryJ) = fun _ : ι => (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext i
    exact binaryJ_mul_self
  rw [hfun, tensorFamily_one]

theorem isUnit_crossingJ : IsUnit (crossingJ (ι := ι)) :=
  ⟨⟨crossingJ, crossingJ, crossingJ_mul_self, crossingJ_mul_self⟩, rfl⟩

theorem inv_crossingJ : (crossingJ (ι := ι))⁻¹ = crossingJ :=
  Matrix.inv_eq_right_inv crossingJ_mul_self

omit [DecidableEq ι] in
theorem isHermitian_crossingJ : (crossingJ (ι := ι)).IsHermitian :=
  isHermitian_tensorFamily fun _ => isHermitian_binaryJ

theorem isUnit_crossingOccupancy : IsUnit (crossingOccupancy m) :=
  isUnit_tensorFamily fun i => isUnit_localOccupancyBlock (m i)

omit [DecidableEq ι] in
theorem isHermitian_crossingOccupancy : (crossingOccupancy m).IsHermitian :=
  isHermitian_tensorFamily fun i => isHermitian_localOccupancyBlock (m i)

theorem inv_crossingOccupancy :
    (crossingOccupancy m)⁻¹ = tensorFamily fun i => (localOccupancyBlock (m i))⁻¹ :=
  tensorFamily_inv fun i => isUnit_localOccupancyBlock (m i)

theorem crossingGram_eq :
    crossingGram m
      = (crossingFrame m)ᴴ * (crossingOccupancy m)⁻¹ * crossingFrame m := by
  rw [crossingGram, crossingFrame, inv_crossingOccupancy, tensorFamily_conjTranspose,
    tensorFamily_mul (fun i => (localFrame (m i))ᴴ) (fun i => (localOccupancyBlock (m i))⁻¹),
    tensorFamily_mul (fun i => (localFrame (m i))ᴴ * (localOccupancyBlock (m i))⁻¹)
      (fun i => localFrame (m i))]
  rfl

/-- A congruence acting on a single tensor factor. -/
def tensorSingleFactor (i₀ : ι) (L : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  tensorFamily fun i => if i = i₀ then L else 1

theorem isUnit_tensorSingleFactor (i₀ : ι) {L : Matrix (Fin 2) (Fin 2) ℂ} (hL : IsUnit L) :
    IsUnit (tensorSingleFactor (ι := ι) i₀ L) := by
  refine isUnit_tensorFamily fun i => ?_
  by_cases h : i = i₀
  · rw [if_pos h]; exact hL
  · rw [if_neg h]; exact isUnit_one

theorem tensorSingleFactor_congr (i₀ : ι) (L : Matrix (Fin 2) (Fin 2) ℂ)
    (Y : ι → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (h : Lᴴ * Y i₀ * L = c • Y i₀) :
    (tensorSingleFactor (ι := ι) i₀ L)ᴴ * tensorFamily Y * tensorSingleFactor (ι := ι) i₀ L
      = c • tensorFamily Y := by
  classical
  rw [tensorSingleFactor, tensorFamily_conjTranspose,
    tensorFamily_mul (fun i => (if i = i₀ then L else 1)ᴴ) Y,
    tensorFamily_mul (fun i => (if i = i₀ then L else 1)ᴴ * Y i)
      (fun i => if i = i₀ then L else 1)]
  have hfun : (fun i => (if i = i₀ then L else 1)ᴴ * Y i * (if i = i₀ then L else 1))
      = fun i => (if i = i₀ then c else 1) • Y i := by
    funext i
    by_cases hi : i = i₀
    · subst hi
      simpa using h
    · simp [hi]
  rw [hfun, tensorFamily_smul]
  congr 1
  rw [Finset.prod_ite_eq' Finset.univ i₀ (fun _ => c)]
  simp

theorem posIndex_crossingJ_eq_negIndex [Nonempty ι] :
    hermPosIndex (crossingJ (ι := ι)) = hermNegIndex (crossingJ (ι := ι)) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hc := tensorSingleFactor_congr (ι := ι) i₀ (localBalance 0) (fun _ : ι => binaryJ)
    (-((localBalanceFactor 0 : ℝ) : ℂ)) (localBalance_binaryJ 0)
  have hJ : crossingJ (ι := ι) = tensorFamily fun _ : ι => binaryJ := rfl
  have hpos := posIndex_conjugate (crossingJ (ι := ι))
    (isUnit_tensorSingleFactor (ι := ι) i₀ (isUnit_localBalance 0))
  rw [hJ] at hpos ⊢
  rw [hc] at hpos
  rw [← hpos]
  have hneg : (-((localBalanceFactor 0 : ℝ) : ℂ)) • (tensorFamily fun _ : ι => binaryJ)
      = ((localBalanceFactor 0 : ℝ) : ℂ) • (-(tensorFamily fun _ : ι => binaryJ)) := by
    rw [smul_neg, neg_smul]
  rw [hneg, posIndex_smul_pos (localBalanceFactor_pos 0)]
  rfl

theorem localBalance_gram (k : ℕ) :
    (localBalance k)ᴴ * localGram k * localBalance k
      = -((localBalanceFactor k : ℝ) : ℂ) • localGram k := by
  rw [localGram_eq_smul, Matrix.mul_smul, Matrix.smul_mul, localBalance_gramRaw, smul_comm]

theorem tensorSingleFactor_congr_sub (i₀ : ι) (L : Matrix (Fin 2) (Fin 2) ℂ)
    (Y Z : ι → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (hY : Lᴴ * Y i₀ * L = c • Y i₀) (hZ : Lᴴ * Z i₀ * L = c • Z i₀) :
    (tensorSingleFactor (ι := ι) i₀ L)ᴴ * (tensorFamily Y - tensorFamily Z) *
        tensorSingleFactor (ι := ι) i₀ L
      = c • (tensorFamily Y - tensorFamily Z) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, tensorSingleFactor_congr i₀ L Y c hY,
    tensorSingleFactor_congr i₀ L Z c hZ, smul_sub]

/-- **The binary block `J − G` is balanced.** -/
theorem posIndex_crossingJ_sub_gram_eq_negIndex [Nonempty ι] :
    hermPosIndex (crossingJ (ι := ι) - crossingGram m)
      = hermNegIndex (crossingJ (ι := ι) - crossingGram m) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set L := localBalance (m i₀) with hL
  set c : ℂ := -((localBalanceFactor (m i₀) : ℝ) : ℂ) with hcdef
  have hc := tensorSingleFactor_congr_sub (ι := ι) i₀ L (fun _ : ι => binaryJ)
    (fun i => localGram (m i)) c (localBalance_binaryJ (m i₀)) (localBalance_gram (m i₀))
  have hJ : crossingJ (ι := ι) = tensorFamily fun _ : ι => binaryJ := rfl
  have hG : crossingGram m = tensorFamily fun i => localGram (m i) := rfl
  have hpos := posIndex_conjugate (crossingJ (ι := ι) - crossingGram m)
    (isUnit_tensorSingleFactor (ι := ι) i₀ (isUnit_localBalance (m i₀)))
  rw [hJ, hG] at hpos ⊢
  rw [hc] at hpos
  rw [← hpos, hcdef]
  have hneg : (-((localBalanceFactor (m i₀) : ℝ) : ℂ)) •
      ((tensorFamily fun _ : ι => binaryJ) - tensorFamily fun i => localGram (m i))
      = ((localBalanceFactor (m i₀) : ℝ) : ℂ) •
        (-((tensorFamily fun _ : ι => binaryJ) - tensorFamily fun i => localGram (m i))) := by
    rw [smul_neg, neg_smul]
  rw [hneg, posIndex_smul_pos (localBalanceFactor_pos (m i₀))]
  rfl

/-- The unscaled pencil tensor `M̃ = ⊗ M̃_i`. -/
def crossingPencil : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  tensorFamily fun i => localPencilRaw (m i)

/-- The metric tensor `P₀ = ⊗ P₀_i`. -/
def crossingMetric : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  tensorFamily fun i => localMetric (m i)

/-- The product of the local denominators `2P_i − 1`. -/
def crossingDenom : ℝ := ∏ i, (2 * realScale (m i) - 1)

/-- The product of the local metric multipliers. -/
def crossingScalar : ℝ := ∏ i, localMetricScalar (m i)

omit [DecidableEq ι] in
theorem crossingDenom_pos : 0 < crossingDenom m :=
  Finset.prod_pos fun i _ => two_realScale_sub_one_pos (m i)

omit [DecidableEq ι] in
theorem crossingDenom_cast :
    ((crossingDenom m : ℝ) : ℂ) = ∏ i, (2 * localScale (m i) - 1) := by
  rw [crossingDenom]
  push_cast
  exact Finset.prod_congr rfl fun i _ => by rw [localScale_eq]

omit [DecidableEq ι] in
theorem crossingMetric_isHermitian : (crossingMetric m).IsHermitian :=
  isHermitian_tensorFamily fun i => isHermitian_localMetric (m i)

theorem localMetric_eigenvalues_pos (k : ℕ) (a : Fin 2) :
    0 < (isHermitian_localMetric k).eigenvalues a := by
  classical
  have hcard := posIndex_eq_card_pos_eigenvalues (isHermitian_localMetric k)
  rw [posIndex_localMetric k] at hcard
  have huniv : ({a : Fin 2 | 0 < (isHermitian_localMetric k).eigenvalues a} : Finset (Fin 2))
      = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcard]
    simp
  have : a ∈ ({a : Fin 2 | 0 < (isHermitian_localMetric k).eigenvalues a} : Finset (Fin 2)) := by
    rw [huniv]
    exact Finset.mem_univ a
  simpa using this

theorem crossingMetric_posDef : IsPosDefOn (crossingMetric m) ⊤ := by
  classical
  refine isPosDefOn_top_of_posIndex_eq_card ?_
  rw [crossingMetric, posIndex_tensorFamily (fun i => isHermitian_localMetric (m i))]
  have huniv : ({x : ∀ i, Fin 2 |
      0 < ∏ i, (isHermitian_localMetric (m i)).eigenvalues (x i)} : Finset (∀ i, Fin 2))
      = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.prod_pos fun i _ => localMetric_eigenvalues_pos (m i) (x i)
  rw [huniv, Finset.card_univ]

omit [DecidableEq ι] in
theorem crossingScalar_cast :
    ((crossingScalar m : ℝ) : ℂ) = ∏ i, ((localMetricScalar (m i) : ℝ) : ℂ) := by
  rw [crossingScalar]
  push_cast
  rfl

/-- **The pencil tensor scales the metric tensor.** -/
theorem crossingPencil_metric :
    (crossingPencil m)ᴴ * crossingMetric m * crossingPencil m
      = ((crossingScalar m : ℝ) : ℂ) • crossingMetric m := by
  rw [crossingPencil, crossingMetric, tensorFamily_conjTranspose,
    tensorFamily_mul (fun i => (localPencilRaw (m i))ᴴ) (fun i => localMetric (m i)),
    tensorFamily_mul (fun i => (localPencilRaw (m i))ᴴ * localMetric (m i))
      (fun i => localPencilRaw (m i))]
  have hfun : (fun i => (localPencilRaw (m i))ᴴ * localMetric (m i) * localPencilRaw (m i))
      = fun i => ((localMetricScalar (m i) : ℝ) : ℂ) • localMetric (m i) :=
    funext fun i => localPencilRaw_metric (m i)
  rw [hfun, tensorFamily_smul, crossingScalar_cast]

/-- **The `J G` product is a scalar multiple of the pencil tensor.** -/
theorem crossingJ_mul_gram :
    crossingJ (ι := ι) * crossingGram m
      = (((crossingDenom m : ℝ) : ℂ))⁻¹ • crossingPencil m := by
  rw [crossingJ, crossingGram, tensorFamily_mul (fun _ : ι => binaryJ) (fun i => localGram (m i))]
  have hfun : (fun i => binaryJ * localGram (m i))
      = fun i => (2 * localScale (m i) - 1)⁻¹ • localPencilRaw (m i) := by
    funext i
    rw [localGram_eq_smul, Matrix.mul_smul, localPencilRaw]
  rw [hfun, tensorFamily_smul, crossingPencil, crossingDenom_cast, ← Finset.prod_inv_distrib]

omit [DecidableEq ι] in
theorem crossingDenom_sq_lt_scalar [Nonempty ι] : crossingDenom m ^ 2 < crossingScalar m := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  have hsplit : crossingScalar m
      = (∏ i, (realScale (m i) ^ 2 * (realScale (m i) - 1))) * crossingDenom m := by
    rw [crossingScalar, crossingDenom, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [localMetricScalar]; ring
  have hlt : crossingDenom m < ∏ i, (realScale (m i) ^ 2 * (realScale (m i) - 1)) := by
    rw [crossingDenom]
    refine Finset.prod_lt_prod_of_nonempty (fun i _ => two_realScale_sub_one_pos (m i))
      (fun i _ => two_realScale_sub_one_lt_metricScalar (m i)) hne
  have hpos := crossingDenom_pos m
  rw [hsplit]
  nlinarith

/-- **The binary block `J − G` is nonsingular.** -/
theorem isUnit_crossingJ_sub_gram [Nonempty ι] :
    IsUnit (crossingJ (ι := ι) - crossingGram m) := by
  classical
  have hcpos : 0 < crossingDenom m := crossingDenom_pos m
  have hcne : ((crossingDenom m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hcpos.ne'
  have hinj : ∀ x : (ι → Fin 2) → ℂ,
      ((1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) - crossingJ * crossingGram m) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hJG : (crossingJ (ι := ι) * crossingGram m) *ᵥ x = x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hx
      exact hx.symm
    have hpen : crossingPencil m *ᵥ x = ((crossingDenom m : ℝ) : ℂ) • x := by
      rw [crossingJ_mul_gram, Matrix.smul_mulVec] at hJG
      have := congrArg (fun y => ((crossingDenom m : ℝ) : ℂ) • y) hJG
      simpa [smul_smul, mul_inv_cancel₀ hcne] using this
    have hq1 : hermQuad ((crossingPencil m)ᴴ * crossingMetric m * crossingPencil m) x
        = hermQuad (crossingMetric m) (crossingPencil m *ᵥ x) :=
      hermQuad_rect_conjugate _ _ _
    rw [crossingPencil_metric, hpen, hermQuad_smul_vec, hermQuad_smul] at hq1
    have hzero : (crossingScalar m - crossingDenom m ^ 2) * hermQuad (crossingMetric m) x = 0 := by
      have hsub : crossingScalar m * hermQuad (crossingMetric m) x
          - crossingDenom m ^ 2 * hermQuad (crossingMetric m) x = 0 := by
        rw [hq1]
        ring
      linarith [hsub, sub_mul (crossingScalar m) (crossingDenom m ^ 2)
        (hermQuad (crossingMetric m) x)]
    have hne : crossingScalar m - crossingDenom m ^ 2 ≠ 0 := by
      have := crossingDenom_sq_lt_scalar m
      intro h
      linarith [sub_eq_zero.mp h]
    have hQ : hermQuad (crossingMetric m) x = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h hne
      · exact h
    by_contra hx0
    have hpos := crossingMetric_posDef m x Submodule.mem_top hx0
    linarith
  have hdet : ((1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) - crossingJ * crossingGram m).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    exact hv0 (hinj v hv)
  have hfac : crossingJ (ι := ι) * (crossingJ (ι := ι) - crossingGram m)
      = (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) - crossingJ * crossingGram m := by
    rw [Matrix.mul_sub, crossingJ_mul_self]
  have hdet2 : (crossingJ (ι := ι) - crossingGram m).det ≠ 0 := by
    intro hd
    apply hdet
    rw [← hfac, Matrix.det_mul, hd, mul_zero]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet2)

theorem inv_neg_crossingOccupancy :
    (-crossingOccupancy m)⁻¹ = -(crossingOccupancy m)⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [neg_mul_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_crossingOccupancy m))

theorem inv_neg_crossingJ : (-crossingJ (ι := ι))⁻¹ = -crossingJ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [neg_mul_neg]
  exact crossingJ_mul_self

theorem schur_at_occupancy :
    -crossingJ (ι := ι) - (crossingFrame m)ᴴ * (-crossingOccupancy m)⁻¹ * crossingFrame m
      = -(crossingJ (ι := ι) - crossingGram m) := by
  rw [inv_neg_crossingOccupancy, crossingGram_eq]
  have h : (crossingFrame m)ᴴ * (-(crossingOccupancy m)⁻¹) * crossingFrame m
      = -((crossingFrame m)ᴴ * (crossingOccupancy m)⁻¹ * crossingFrame m) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [h]
  abel

theorem schur_at_binary :
    -crossingOccupancy m - crossingFrame m * (-crossingJ (ι := ι))⁻¹ * (crossingFrame m)ᴴ
      = crossingDensity m - crossingOccupancy m := by
  rw [inv_neg_crossingJ, crossingDensity_eq]
  have h : crossingFrame m * (-crossingJ (ι := ι)) * (crossingFrame m)ᴴ
      = -(crossingFrame m * crossingJ (ι := ι) * (crossingFrame m)ᴴ) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [h]
  abel

theorem crossingOccupancy_eq_diagonal :
    crossingOccupancy m
      = diagonal fun x : (∀ i, Fin (m i + 2)) =>
          ((∏ i, localOccupancyEigen (m i) (x i) : ℝ) : ℂ) := by
  rw [crossingOccupancy]
  have hfun : (fun i => localOccupancyBlock (m i))
      = fun i => diagonal fun a => ((localOccupancyEigen (m i) a : ℝ) : ℂ) :=
    funext fun i => localOccupancyBlock_eq_diagonal (m i)
  rw [hfun, tensorFamily_diagonal]
  congr 1
  funext x
  push_cast
  rfl

theorem posIndex_crossingOccupancy :
    hermPosIndex (crossingOccupancy m)
      = ({x : ∀ i, Fin (m i + 2) | 0 < ∏ i, localOccupancyEigen (m i) (x i)} :
          Finset (∀ i, Fin (m i + 2))).card := by
  rw [crossingOccupancy_eq_diagonal, posIndex_diagonal]

theorem negIndex_crossingOccupancy :
    hermNegIndex (crossingOccupancy m)
      = ({x : ∀ i, Fin (m i + 2) | ∏ i, localOccupancyEigen (m i) (x i) < 0} :
          Finset (∀ i, Fin (m i + 2))).card := by
  rw [crossingOccupancy_eq_diagonal, negIndex_diagonal]

/-- **The signature of the occupancy tensor is `∏ (−m_i) = (−1)^r κ`.** -/
theorem crossingOccupancy_signature :
    (hermPosIndex (crossingOccupancy m) : ℝ) - (hermNegIndex (crossingOccupancy m) : ℝ)
      = ∏ i, (-(m i : ℝ)) := by
  rw [posIndex_crossingOccupancy, negIndex_crossingOccupancy,
    card_pos_sub_card_neg_tensor (fun i => localOccupancyEigen (m i))
      (fun i a => localOccupancyEigen_ne_zero (m i) a)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [card_pos_localOccupancyEigen, card_neg_localOccupancyEigen]
  push_cast
  ring

theorem haynsworth_pos_eq :
    hermPosIndex (-crossingJ (ι := ι))
        + hermPosIndex (crossingDensity m - crossingOccupancy m)
      = hermPosIndex (-crossingOccupancy m)
        + hermPosIndex (-(crossingJ (ι := ι) - crossingGram m)) := by
  have hEu : IsUnit (-crossingOccupancy m) := (isUnit_crossingOccupancy m).neg
  have hEh : (-crossingOccupancy m).IsHermitian := (isHermitian_crossingOccupancy m).neg
  have hJu : IsUnit (-crossingJ (ι := ι)) := (isUnit_crossingJ (ι := ι)).neg
  have hJh : (-crossingJ (ι := ι)).IsHermitian := (isHermitian_crossingJ (ι := ι)).neg
  have h1 := haynsworth_posIndex hEu hEh (crossingFrame m) hJh
  have h2 := haynsworth_posIndex hJu hJh ((crossingFrame m)ᴴ) hEh
  rw [schur_at_occupancy] at h1
  rw [Matrix.conjTranspose_conjTranspose, schur_at_binary] at h2
  rw [← h2, ← h1, posIndex_swapBlocks]

theorem haynsworth_neg_eq :
    hermNegIndex (-crossingJ (ι := ι))
        + hermNegIndex (crossingDensity m - crossingOccupancy m)
      = hermNegIndex (-crossingOccupancy m)
        + hermNegIndex (-(crossingJ (ι := ι) - crossingGram m)) := by
  have hEu : IsUnit (-crossingOccupancy m) := (isUnit_crossingOccupancy m).neg
  have hEh : (-crossingOccupancy m).IsHermitian := (isHermitian_crossingOccupancy m).neg
  have hJu : IsUnit (-crossingJ (ι := ι)) := (isUnit_crossingJ (ι := ι)).neg
  have hJh : (-crossingJ (ι := ι)).IsHermitian := (isHermitian_crossingJ (ι := ι)).neg
  have h1 := haynsworth_negIndex hEu hEh (crossingFrame m) hJh
  have h2 := haynsworth_negIndex hJu hJh ((crossingFrame m)ᴴ) hEh
  rw [schur_at_occupancy] at h1
  rw [Matrix.conjTranspose_conjTranspose, schur_at_binary] at h2
  rw [← h2, ← h1, negIndex_swapBlocks]

theorem haynsworth_null_eq :
    hermNullIndex (-crossingJ (ι := ι))
        + hermNullIndex (crossingDensity m - crossingOccupancy m)
      = hermNullIndex (-crossingOccupancy m)
        + hermNullIndex (-(crossingJ (ι := ι) - crossingGram m)) := by
  have hEu : IsUnit (-crossingOccupancy m) := (isUnit_crossingOccupancy m).neg
  have hEh : (-crossingOccupancy m).IsHermitian := (isHermitian_crossingOccupancy m).neg
  have hJu : IsUnit (-crossingJ (ι := ι)) := (isUnit_crossingJ (ι := ι)).neg
  have hJh : (-crossingJ (ι := ι)).IsHermitian := (isHermitian_crossingJ (ι := ι)).neg
  have h1 := haynsworth_nullIndex hEu hEh (crossingFrame m) hJh
  have h2 := haynsworth_nullIndex hJu hJh ((crossingFrame m)ᴴ) hEh
  rw [schur_at_occupancy] at h1
  rw [Matrix.conjTranspose_conjTranspose, schur_at_binary] at h2
  rw [← h2, ← h1, nullIndex_swapBlocks hEh hJh (crossingFrame m)]

section Jump

theorem nullIndex_neg_crossingJ : hermNullIndex (-crossingJ (ι := ι)) = 0 :=
  nullIndex_eq_zero_of_isUnit (isUnit_crossingJ (ι := ι)).neg

theorem nullIndex_neg_crossingOccupancy : hermNullIndex (-crossingOccupancy m) = 0 :=
  nullIndex_eq_zero_of_isUnit (isUnit_crossingOccupancy m).neg

variable [Nonempty ι]

theorem nullIndex_neg_crossingJ_sub_gram :
    hermNullIndex (-(crossingJ (ι := ι) - crossingGram m)) = 0 :=
  nullIndex_eq_zero_of_isUnit (isUnit_crossingJ_sub_gram m).neg

theorem posIndex_neg_crossingJ_eq_negIndex :
    hermPosIndex (-crossingJ (ι := ι)) = hermNegIndex (-crossingJ (ι := ι)) := by
  have h := posIndex_crossingJ_eq_negIndex (ι := ι)
  show hermPosIndex (-crossingJ (ι := ι)) = hermPosIndex (-(-crossingJ (ι := ι)))
  rw [neg_neg]
  exact h.symm

theorem posIndex_neg_crossingJ_sub_gram_eq_negIndex :
    hermPosIndex (-(crossingJ (ι := ι) - crossingGram m))
      = hermNegIndex (-(crossingJ (ι := ι) - crossingGram m)) := by
  have h := posIndex_crossingJ_sub_gram_eq_negIndex m
  show hermPosIndex (-(crossingJ (ι := ι) - crossingGram m))
      = hermPosIndex (-(-(crossingJ (ι := ι) - crossingGram m)))
  rw [neg_neg]
  exact h.symm

/-- **The jump is nonsingular on the crossing space.** -/
theorem nullIndex_crossingJump :
    hermNullIndex (crossingDensity m - crossingOccupancy m) = 0 := by
  have h := haynsworth_null_eq m
  rw [nullIndex_neg_crossingJ, nullIndex_neg_crossingOccupancy m,
    nullIndex_neg_crossingJ_sub_gram m] at h
  omega

/-- **The jump signature is minus the occupancy signature.** -/
theorem crossingJump_signature_balance :
    hermPosIndex (crossingDensity m - crossingOccupancy m) + hermPosIndex (crossingOccupancy m)
      = hermNegIndex (crossingDensity m - crossingOccupancy m)
        + hermNegIndex (crossingOccupancy m) := by
  have hp := haynsworth_pos_eq m
  have hn := haynsworth_neg_eq m
  have hJ := posIndex_neg_crossingJ_eq_negIndex (ι := ι)
  have hJG := posIndex_neg_crossingJ_sub_gram_eq_negIndex m
  have hEp : hermPosIndex (-crossingOccupancy m) = hermNegIndex (crossingOccupancy m) := rfl
  have hEn : hermNegIndex (-crossingOccupancy m) = hermPosIndex (crossingOccupancy m) := by
    show hermPosIndex (-(-crossingOccupancy m)) = hermPosIndex (crossingOccupancy m)
    rw [neg_neg]
  rw [hEp] at hp
  rw [hEn] at hn
  omega

end Jump

section Final

omit [DecidableEq ι] in
theorem isHermitian_crossingDensity : (crossingDensity m).IsHermitian :=
  isHermitian_tensorFamily fun i => isHermitian_localDensityBlock (m i)

omit [DecidableEq ι] in
theorem isHermitian_crossingJump :
    (crossingOccupancy m - crossingDensity m).IsHermitian :=
  (isHermitian_crossingOccupancy m).sub (isHermitian_crossingDensity m)

theorem card_crossingSpace :
    Fintype.card (∀ i, Fin (m i + 2)) = ∏ i, (m i + 2) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => Fintype.card_fin _

variable [Nonempty ι]

/-- **`(CJ2)` active dimension: the jump is nonsingular of full crossing rank.** -/
theorem posIndex_add_negIndex_crossingJump :
    hermPosIndex (crossingOccupancy m - crossingDensity m)
        + hermNegIndex (crossingOccupancy m - crossingDensity m)
      = ∏ i, (m i + 2) := by
  have hfull := posIndex_add_negIndex_add_nullIndex (isHermitian_crossingJump m)
  have hnull : hermNullIndex (crossingOccupancy m - crossingDensity m) = 0 := by
    rw [← neg_sub (crossingDensity m) (crossingOccupancy m), nullIndex_neg]
    exact nullIndex_crossingJump m
  rw [hnull, card_crossingSpace] at hfull
  omega

/-- **`(CJ2)` signature: the jump signature is `∏ (−m_i)`.** -/
theorem crossingJump_signature :
    (hermPosIndex (crossingOccupancy m - crossingDensity m) : ℝ)
        - (hermNegIndex (crossingOccupancy m - crossingDensity m) : ℝ)
      = ∏ i, (-(m i : ℝ)) := by
  have hpos : hermPosIndex (crossingOccupancy m - crossingDensity m)
      = hermNegIndex (crossingDensity m - crossingOccupancy m) := by
    rw [← neg_sub (crossingDensity m) (crossingOccupancy m)]
    rfl
  have hneg : hermNegIndex (crossingOccupancy m - crossingDensity m)
      = hermPosIndex (crossingDensity m - crossingOccupancy m) := by
    show hermPosIndex (-(crossingOccupancy m - crossingDensity m))
      = hermPosIndex (crossingDensity m - crossingOccupancy m)
    rw [neg_sub]
  have hbal := crossingJump_signature_balance m
  have hE := crossingOccupancy_signature m
  rw [hpos, hneg]
  have hcastbal : (hermPosIndex (crossingDensity m - crossingOccupancy m) : ℝ)
      + (hermPosIndex (crossingOccupancy m) : ℝ)
      = (hermNegIndex (crossingDensity m - crossingOccupancy m) : ℝ)
        + (hermNegIndex (crossingOccupancy m) : ℝ) := by
    exact_mod_cast hbal
  rw [← hE]
  linarith [hcastbal]

end Final

omit [DecidableEq ι] in
theorem prod_neg_cast : (∏ i, (-(m i : ℝ)))
    = (-1 : ℝ) ^ Fintype.card ι * ∏ i, (m i : ℝ) := by
  have h : (fun i => (-(m i : ℝ))) = fun i => (-1 : ℝ) * (m i : ℝ) := by
    funext i; ring
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- **`(CJ1)`: the cutoff jump `K = (−1)^r (E − R)`.** -/
def crossingJump : Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ :=
  (((-1 : ℝ) ^ Fintype.card ι : ℝ) : ℂ) • (crossingOccupancy m - crossingDensity m)

omit [DecidableEq ι] in
theorem crossingJump_eq_of_even (h : Even (Fintype.card ι)) :
    crossingJump m = crossingOccupancy m - crossingDensity m := by
  rw [crossingJump, h.neg_one_pow]
  simp

omit [DecidableEq ι] in
theorem crossingJump_eq_of_odd (h : Odd (Fintype.card ι)) :
    crossingJump m = -(crossingOccupancy m - crossingDensity m) := by
  rw [crossingJump, h.neg_one_pow]
  simp

variable [Nonempty ι]

/-- **`(CJ2)`: the cutoff jump has full crossing rank.** -/
theorem crossingJump_pos_add_neg :
    hermPosIndex (crossingJump m) + hermNegIndex (crossingJump m) = ∏ i, (m i + 2) := by
  rcases Nat.even_or_odd (Fintype.card ι) with h | h
  · rw [crossingJump_eq_of_even m h]
    exact posIndex_add_negIndex_crossingJump m
  · rw [crossingJump_eq_of_odd m h]
    have hp : hermPosIndex (-(crossingOccupancy m - crossingDensity m))
        = hermNegIndex (crossingOccupancy m - crossingDensity m) := rfl
    have hn : hermNegIndex (-(crossingOccupancy m - crossingDensity m))
        = hermPosIndex (crossingOccupancy m - crossingDensity m) := by
      show hermPosIndex (-(-(crossingOccupancy m - crossingDensity m)))
        = hermPosIndex (crossingOccupancy m - crossingDensity m)
      rw [neg_neg]
    rw [hp, hn]
    have := posIndex_add_negIndex_crossingJump m
    omega

/-- **`(CJ2)`: the cutoff jump has signature `κ = ∏ m_i`, the root-avoidance count.** -/
theorem crossingJump_signature_eq_kappa :
    (hermPosIndex (crossingJump m) : ℝ) - (hermNegIndex (crossingJump m) : ℝ)
      = ∏ i, (m i : ℝ) := by
  have hsig := crossingJump_signature m
  rw [prod_neg_cast] at hsig
  rcases Nat.even_or_odd (Fintype.card ι) with h | h
  · rw [crossingJump_eq_of_even m h, hsig, h.neg_one_pow, one_mul]
  · rw [crossingJump_eq_of_odd m h]
    have hp : hermPosIndex (-(crossingOccupancy m - crossingDensity m))
        = hermNegIndex (crossingOccupancy m - crossingDensity m) := rfl
    have hn : hermNegIndex (-(crossingOccupancy m - crossingDensity m))
        = hermPosIndex (crossingOccupancy m - crossingDensity m) := by
      show hermPosIndex (-(-(crossingOccupancy m - crossingDensity m)))
        = hermPosIndex (crossingOccupancy m - crossingDensity m)
      rw [neg_neg]
    rw [hp, hn, h.neg_one_pow] at *
    linarith [hsig]

omit [Nonempty ι] in
/-- **`(CJ16)`: occupancy and density have the same trace `∏ P_i⁻¹`, so every jump is
traceless.** -/
theorem trace_crossingOccupancy :
    Matrix.trace (crossingOccupancy m) = ∏ i, (localScale (m i))⁻¹ := by
  rw [crossingOccupancy, trace_tensorFamily]
  exact Finset.prod_congr rfl fun i _ => trace_localOccupancyBlock (m i)

omit [Nonempty ι] in
theorem trace_crossingDensity :
    Matrix.trace (crossingDensity m) = ∏ i, (localScale (m i))⁻¹ := by
  rw [crossingDensity, trace_tensorFamily]
  exact Finset.prod_congr rfl fun i _ => trace_localDensityBlock (m i)

omit [Nonempty ι] in
/-- **`(CJ16)`: every cutoff jump is traceless.** -/
theorem trace_crossingJump : Matrix.trace (crossingJump m) = 0 := by
  rw [crossingJump, Matrix.trace_smul, Matrix.trace_sub, trace_crossingOccupancy,
    trace_crossingDensity, sub_self, smul_zero]

section Padding

variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- Padding by a rank-one anchor supported on a unit vector `v`. -/
def anchorPad (v : ρ → ℂ) :
    Matrix ((∀ i, Fin (m i + 2)) × ρ) (∀ i, Fin (m i + 2)) ℂ :=
  Matrix.of fun p y => (if p.1 = y then (1 : ℂ) else 0) * v p.2

omit [Nonempty ι] [DecidableEq ρ] in
theorem anchorPad_isometry (v : ρ → ℂ) (hv : (∑ s, (starRingEnd ℂ) (v s) * v s) = 1) :
    (anchorPad m v)ᴴ * anchorPad m v = 1 := by
  classical
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hadj : ∀ (x y : ∀ i, Fin (m i + 2)) (s : ρ),
      (anchorPad m v)ᴴ y (x, s) = (if x = y then (1 : ℂ) else 0) * (starRingEnd ℂ) (v s) := by
    intro x y s
    rw [Matrix.conjTranspose_apply, anchorPad]
    simp only [Matrix.of_apply]
    by_cases h : x = y <;> simp [h]
  have hstep : ∀ x : ∀ i, Fin (m i + 2),
      (∑ s : ρ, (anchorPad m v)ᴴ a (x, s) * anchorPad m v (x, s) b)
        = (if x = a then (1 : ℂ) else 0) * (if x = b then (1 : ℂ) else 0) := by
    intro x
    have hterm : ∀ s : ρ, (anchorPad m v)ᴴ a (x, s) * anchorPad m v (x, s) b
        = ((if x = a then (1 : ℂ) else 0) * (if x = b then (1 : ℂ) else 0))
          * ((starRingEnd ℂ) (v s) * v s) := by
      intro s
      rw [hadj x a s, anchorPad]
      simp only [Matrix.of_apply]
      ring
    rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.mul_sum, hv, mul_one]
  rw [Finset.sum_congr rfl fun x _ => hstep x]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq, Finset.sum_eq_single a]
    · simp
    · intro x _ hx
      simp [hx]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [Matrix.one_apply_ne hab]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = a
    · subst hx
      simp [hab]
    · simp [hx]

variable (v : ρ → ℂ) (hv : (∑ s, (starRingEnd ℂ) (v s) * v s) = 1)

include hv

omit [Nonempty ι] [DecidableEq ρ] in
theorem posIndex_anchorPad (X : Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ) :
    hermPosIndex (anchorPad m v * X * (anchorPad m v)ᴴ) = hermPosIndex X :=
  posIndex_isometric_congr (anchorPad_isometry m v hv) X

omit [Nonempty ι] [DecidableEq ρ] in
theorem negIndex_anchorPad (X : Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ) :
    hermNegIndex (anchorPad m v * X * (anchorPad m v)ᴴ) = hermNegIndex X :=
  negIndex_isometric_congr (anchorPad_isometry m v hv) X

/-- **`(CJ2)` in the ambient space: the padded jump has inertia
`((q+κ)/2, (q−κ)/2, Q−q)`.** -/
theorem nullIndex_anchorPad_crossingJump :
    hermNullIndex (anchorPad m v * crossingJump m * (anchorPad m v)ᴴ)
      = (∏ i, (m i + 2)) * Fintype.card ρ - ∏ i, (m i + 2) := by
  have hHerm : (crossingJump m).IsHermitian := by
    rw [crossingJump, Matrix.IsHermitian, Matrix.conjTranspose_smul,
      (isHermitian_crossingJump m).eq]
    congr 1
    simp
  have hHerm2 : (anchorPad m v * crossingJump m * (anchorPad m v)ᴴ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hHerm.eq, Matrix.mul_assoc]
  have hfull := posIndex_add_negIndex_add_nullIndex hHerm2
  rw [posIndex_anchorPad m v hv, negIndex_anchorPad m v hv,
    crossingJump_pos_add_neg m] at hfull
  have hcard : Fintype.card ((∀ i, Fin (m i + 2)) × ρ)
      = (∏ i, (m i + 2)) * Fintype.card ρ := by
    rw [Fintype.card_prod, card_crossingSpace]
  rw [hcard] at hfull
  omega

end Padding

section PositiveCore

/-- **`(CJ5)`: on the root-avoidance core the jump is the positive scalar `q⁻²`.** -/
theorem crossingJump_mulVec_core (v : ∀ i, Fin (m i + 2) → ℂ)
    (h0 : ∀ i, v i 0 = 0) (hsum : ∀ i, (∑ a, v i a) = 0) :
    crossingJump m *ᵥ tensorVec v = (∏ i, ((localScale (m i)) ^ 2)⁻¹) • tensorVec v := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hR : crossingDensity m *ᵥ tensorVec v = 0 := by
    rw [crossingDensity, tensorFamily_mulVec]
    refine tensorVec_eq_zero _ i₀ ?_
    exact localDensityBlock_mulVec_eq_zero (m i₀) (v i₀) (h0 i₀) (hsum i₀)
  have hE : crossingOccupancy m *ᵥ tensorVec v
      = (∏ i, (-((localScale (m i)) ^ 2)⁻¹)) • tensorVec v := by
    rw [crossingOccupancy, tensorFamily_mulVec]
    have hfun : (fun i => localOccupancyBlock (m i) *ᵥ v i)
        = fun i => (-((localScale (m i)) ^ 2)⁻¹) • v i :=
      funext fun i => localOccupancyBlock_mulVec (m i) (v i) (h0 i)
    rw [hfun, tensorVec_smul]
  have hprod : (∏ i, (-((localScale (m i)) ^ 2)⁻¹))
      = ((-1 : ℂ)) ^ Fintype.card ι * ∏ i, ((localScale (m i)) ^ 2)⁻¹ := by
    have h : (fun i => (-((localScale (m i)) ^ 2)⁻¹))
        = fun i => (-1 : ℂ) * ((localScale (m i)) ^ 2)⁻¹ := by
      funext i; ring
    rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [crossingJump, Matrix.smul_mulVec, Matrix.sub_mulVec, hR, hE, sub_zero, hprod, smul_smul]
  congr 1
  push_cast
  rw [← mul_assoc, ← mul_pow]
  norm_num

end PositiveCore

section Explicit

/-- **`(CJ3)`: the positive index exceeds the negative index by exactly the root-avoidance
count `κ = ∏ m_i`.** -/
theorem posIndex_crossingJump_eq_negIndex_add :
    hermPosIndex (crossingJump m) = hermNegIndex (crossingJump m) + ∏ i, m i := by
  have h := crossingJump_signature_eq_kappa m
  have hcast : ((∏ i, m i : ℕ) : ℝ) = ∏ i, (m i : ℝ) := by push_cast; rfl
  rw [← hcast] at h
  have : ((hermPosIndex (crossingJump m) : ℝ))
      = ((hermNegIndex (crossingJump m) + ∏ i, m i : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **`(CJ3)`: the hyperbolic complement has `(q − κ)/2` planes.** -/
theorem two_mul_negIndex_crossingJump :
    2 * hermNegIndex (crossingJump m) + ∏ i, m i = ∏ i, (m i + 2) := by
  have h1 := crossingJump_pos_add_neg m
  have h2 := posIndex_crossingJump_eq_negIndex_add m
  omega

/-- **`(CJ4)`: the raw curvature `R − E` has the opposite signature.** -/
theorem crossingCurvature_signature :
    (hermPosIndex (crossingDensity m - crossingOccupancy m) : ℝ)
        - (hermNegIndex (crossingDensity m - crossingOccupancy m) : ℝ)
      = -∏ i, (-(m i : ℝ)) := by
  have h := crossingJump_signature m
  have hpos : hermPosIndex (crossingOccupancy m - crossingDensity m)
      = hermNegIndex (crossingDensity m - crossingOccupancy m) := by
    rw [← neg_sub (crossingDensity m) (crossingOccupancy m)]
    rfl
  have hneg : hermNegIndex (crossingOccupancy m - crossingDensity m)
      = hermPosIndex (crossingDensity m - crossingOccupancy m) := by
    show hermPosIndex (-(crossingOccupancy m - crossingDensity m))
      = hermPosIndex (crossingDensity m - crossingOccupancy m)
    rw [neg_sub]
  rw [hpos, hneg] at h
  linarith

end Explicit

end

end RHTower
