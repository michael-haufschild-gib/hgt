import GaloisForLFunctions.HTGeometry.OccupationVacuumAnomalyReciprocity
import GaloisForLFunctions.HTGeometry.HilbertSchmidt
import GaloisForLFunctions.HTGeometry.PrimeValuationKakutaniSector

open scoped BigOperators ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Diagonal standard-form kernel associated with a square-summable vector. -/
def thermofieldDiagonalKernel {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) : Ω × Ω → ℂ :=
  fun p => if p.1 = p.2 then v p.1 else 0

theorem thermofieldDiagonalKernel_isHS {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) :
    HilbertSchmidt.IsHS (thermofieldDiagonalKernel v) := by
  rw [HilbertSchmidt.IsHS, summable_prod_of_nonneg (fun p => by positivity)]
  constructor
  · intro i
    apply summable_of_ne_finset_zero (s := {i})
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [thermofieldDiagonalKernel, Ne.symm hji]
  · have hrow : ∀ i,
        (∑' j, ‖thermofieldDiagonalKernel v (i, j)‖ ^ 2) = ‖v i‖ ^ 2 := by
      intro i
      rw [tsum_eq_single i]
      · simp [thermofieldDiagonalKernel]
      · intro j hji
        simp [thermofieldDiagonalKernel, Ne.symm hji]
    simpa only [hrow] using HilbertSchmidt.summable_coe_sq v

theorem hsNormSq_thermofieldDiagonalKernel {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) :
    HilbertSchmidt.hsNormSq (thermofieldDiagonalKernel v) = ‖v‖ ^ 2 := by
  rw [HilbertSchmidt.hsNormSq,
    (thermofieldDiagonalKernel_isHS v).tsum_prod,
    HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro i
  rw [tsum_eq_single i]
  · simp [thermofieldDiagonalKernel]
  · intro j hji
    simp [thermofieldDiagonalKernel, Ne.symm hji]

/-- Left diagonal multiplication on standard-form kernels. -/
def thermofieldLeftAction {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ) : Ω × Ω → ℂ :=
  fun p => f p.1 * K p

/-- Conjugate right diagonal multiplication, in standard-form coordinates. -/
def thermofieldRightAction {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ) : Ω × Ω → ℂ :=
  fun p => f p.2 * K p

theorem thermofieldLeftAction_isHS {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) (hK : HilbertSchmidt.IsHS K) :
    HilbertSchmidt.IsHS (thermofieldLeftAction f K) := by
  rw [HilbertSchmidt.IsHS] at hK ⊢
  apply Summable.of_nonneg_of_le (fun p => by positivity) _ (hK.mul_left (C ^ 2))
  intro p
  have hsq : ‖f p.1‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [norm_nonneg (f p.1), hf p.1]
  calc
    ‖thermofieldLeftAction f K p‖ ^ 2 = ‖f p.1‖ ^ 2 * ‖K p‖ ^ 2 := by
      rw [thermofieldLeftAction, norm_mul]
      ring
    _ ≤ C ^ 2 * ‖K p‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

theorem thermofieldRightAction_isHS {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) (hK : HilbertSchmidt.IsHS K) :
    HilbertSchmidt.IsHS (thermofieldRightAction f K) := by
  rw [HilbertSchmidt.IsHS] at hK ⊢
  apply Summable.of_nonneg_of_le (fun p => by positivity) _ (hK.mul_left (C ^ 2))
  intro p
  have hsq : ‖f p.2‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [norm_nonneg (f p.2), hf p.2]
  calc
    ‖thermofieldRightAction f K p‖ ^ 2 = ‖f p.2‖ ^ 2 * ‖K p‖ ^ 2 := by
      rw [thermofieldRightAction, norm_mul]
      ring
    _ ≤ C ^ 2 * ‖K p‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

theorem thermofieldDiagonalKernel_central {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) (f : Ω → ℂ) :
    thermofieldLeftAction f (thermofieldDiagonalKernel v) =
      thermofieldRightAction f (thermofieldDiagonalKernel v) := by
  funext p
  by_cases h : p.1 = p.2
  · simp [thermofieldLeftAction, thermofieldRightAction, thermofieldDiagonalKernel, h]
  · simp [thermofieldLeftAction, thermofieldRightAction, thermofieldDiagonalKernel, h]

theorem hsInner_thermofieldDiagonalKernel_actions {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) (f g : Ω → ℂ)
    (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ i, ‖f i‖ ≤ Cf) (hg : ∀ i, ‖g i‖ ≤ Cg) :
    HilbertSchmidt.hsInner (thermofieldDiagonalKernel v)
        (thermofieldLeftAction f
          (thermofieldRightAction g (thermofieldDiagonalKernel v))) =
      ∑' i, ((‖v i‖ ^ 2 : ℝ) : ℂ) * f i * g i := by
  have hK := thermofieldDiagonalKernel_isHS v
  have hR := thermofieldRightAction_isHS g _ Cg hCg hg hK
  have hLR := thermofieldLeftAction_isHS f _ Cf hCf hf hR
  rw [HilbertSchmidt.hsInner, (HilbertSchmidt.hsInner_summable hK hLR).tsum_prod]
  apply tsum_congr
  intro i
  rw [tsum_eq_single i]
  · simp [thermofieldDiagonalKernel, thermofieldLeftAction, thermofieldRightAction]
    calc
      (starRingEnd ℂ) (v i) * (f i * (g i * v i)) =
          f i * g i * (v i * (starRingEnd ℂ) (v i)) := by ring
      _ = f i * g i * (Complex.normSq (v i) : ℂ) := by rw [Complex.mul_conj]
      _ = (‖v i‖ : ℂ) ^ 2 * f i * g i := by
        rw [Complex.normSq_eq_norm_sq]
        rw [Complex.ofReal_pow]
        ring
  · intro j hji
    simp [thermofieldDiagonalKernel, thermofieldLeftAction, thermofieldRightAction,
      Ne.symm hji]

/-! ## Canonical pure-tensor shuffle -/

theorem summable_norm_sq_tensorCoefficients {Ω Λ : Type*}
    (v : lp (fun _ : Ω => ℂ) 2) (w : lp (fun _ : Λ => ℂ) 2) :
    Summable (fun p : Ω × Λ => ‖v p.1 * w p.2‖ ^ 2) := by
  rw [summable_prod_of_nonneg (fun p => by positivity)]
  constructor
  · intro i
    simpa [norm_mul, mul_pow] using
      (HilbertSchmidt.summable_coe_sq w).mul_left (‖v i‖ ^ 2)
  · have hrow : ∀ i,
        (∑' j, ‖v i * w j‖ ^ 2) = ‖v i‖ ^ 2 * ‖w‖ ^ 2 := by
      intro i
      calc
        (∑' j, ‖v i * w j‖ ^ 2) =
            ∑' j, ‖v i‖ ^ 2 * ‖w j‖ ^ 2 := by
              apply tsum_congr
              intro j
              rw [norm_mul]
              ring
        _ = ‖v i‖ ^ 2 * ∑' j, ‖w j‖ ^ 2 :=
          (HilbertSchmidt.summable_coe_sq w).tsum_mul_left _
        _ = ‖v i‖ ^ 2 * ‖w‖ ^ 2 := by rw [HilbertSchmidt.lp_norm_sq_eq]
    simpa only [hrow] using
      (HilbertSchmidt.summable_coe_sq v).mul_right (‖w‖ ^ 2)

/-- Square-summable pure tensor in product coordinates. -/
def lpTensorProductVector {Ω Λ : Type*}
    (v : lp (fun _ : Ω => ℂ) 2) (w : lp (fun _ : Λ => ℂ) 2) :
    lp (fun _ : Ω × Λ => ℂ) 2 :=
  ⟨fun p => v p.1 * w p.2,
    HilbertSchmidt.memℓp_of_sq (summable_norm_sq_tensorCoefficients v w)⟩

@[simp] theorem lpTensorProductVector_apply {Ω Λ : Type*}
    (v : lp (fun _ : Ω => ℂ) 2) (w : lp (fun _ : Λ => ℂ) 2) (p : Ω × Λ) :
    lpTensorProductVector v w p = v p.1 * w p.2 := rfl

theorem norm_sq_lpTensorProductVector {Ω Λ : Type*}
    (v : lp (fun _ : Ω => ℂ) 2) (w : lp (fun _ : Λ => ℂ) 2) :
    ‖lpTensorProductVector v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq,
    show (fun p : Ω × Λ => ‖lpTensorProductVector v w p‖ ^ 2) =
      (fun p : Ω × Λ => ‖v p.1 * w p.2‖ ^ 2) by rfl,
    (summable_norm_sq_tensorCoefficients v w).tsum_prod]
  calc
    (∑' i, ∑' j, ‖lpTensorProductVector v w (i, j)‖ ^ 2) =
        ∑' i, ‖v i‖ ^ 2 * ‖w‖ ^ 2 := by
      apply tsum_congr
      intro i
      calc
        (∑' j, ‖lpTensorProductVector v w (i, j)‖ ^ 2) =
            ∑' j, ‖v i‖ ^ 2 * ‖w j‖ ^ 2 := by
              apply tsum_congr
              intro j
              simp only [lpTensorProductVector_apply, norm_mul]
              ring
        _ = ‖v i‖ ^ 2 * ∑' j, ‖w j‖ ^ 2 :=
          (HilbertSchmidt.summable_coe_sq w).tsum_mul_left _
        _ = ‖v i‖ ^ 2 * ‖w‖ ^ 2 := by rw [HilbertSchmidt.lp_norm_sq_eq]
    _ = (∑' i, ‖v i‖ ^ 2) * ‖w‖ ^ 2 :=
      (HilbertSchmidt.summable_coe_sq v).tsum_mul_right _
    _ = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by rw [← HilbertSchmidt.lp_norm_sq_eq v]

/-- Coefficient form of the canonical tensor shuffle for diagonal standard-form vectors. -/
theorem thermofieldDiagonalKernel_lpTensorProductVector
    {Ω Λ : Type*} [DecidableEq Ω] [DecidableEq Λ]
    (v : lp (fun _ : Ω => ℂ) 2) (w : lp (fun _ : Λ => ℂ) 2)
    (i j : Ω × Λ) :
    thermofieldDiagonalKernel (lpTensorProductVector v w) (i, j) =
      thermofieldDiagonalKernel v (i.1, j.1) *
        thermofieldDiagonalKernel w (i.2, j.2) := by
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2
  · have hij : i = j := Prod.ext h1 h2
    simp [thermofieldDiagonalKernel, hij]
  · have hij : i ≠ j := fun h => h2 (congrArg Prod.snd h)
    simp [thermofieldDiagonalKernel, h1, h2, hij]
  · have hij : i ≠ j := fun h => h1 (congrArg Prod.fst h)
    simp [thermofieldDiagonalKernel, h1, h2, hij]
  · have hij : i ≠ j := fun h => h1 (congrArg Prod.fst h)
    simp [thermofieldDiagonalKernel, h1, h2, hij]

theorem summable_lp_inner_coordinates {Ω : Type*}
    (v w : lp (fun _ : Ω => ℂ) 2) :
    Summable (fun i => w i * (starRingEnd ℂ) (v i)) := by
  apply Summable.of_norm_bounded
      (g := fun i => (‖v i‖ ^ 2 + ‖w i‖ ^ 2) / 2)
  · exact ((HilbertSchmidt.summable_coe_sq v).add
      (HilbertSchmidt.summable_coe_sq w)).div_const 2
  · intro i
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖v i‖ - ‖w i‖), norm_nonneg (v i), norm_nonneg (w i)]

/-- Inner products multiply under the canonical pure-tensor coordinate shuffle. -/
theorem inner_lpTensorProductVector {Ω Λ : Type*}
    (v₁ v₂ : lp (fun _ : Ω => ℂ) 2) (w₁ w₂ : lp (fun _ : Λ => ℂ) 2) :
    inner ℂ (lpTensorProductVector v₁ w₁) (lpTensorProductVector v₂ w₂) =
      inner ℂ v₁ v₂ * inner ℂ w₁ w₂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, lpTensorProductVector_apply, map_mul]
  have hΩ := summable_lp_inner_coordinates v₁ v₂
  have hΛ := summable_lp_inner_coordinates w₁ w₂
  have hprod : Summable (fun p : Ω × Λ =>
      (v₂ p.1 * (starRingEnd ℂ) (v₁ p.1)) *
        (w₂ p.2 * (starRingEnd ℂ) (w₁ p.2))) := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    constructor
    · intro i
      simpa [norm_mul] using
        hΛ.norm.mul_left ‖v₂ i * (starRingEnd ℂ) (v₁ i)‖
    · have hrow : ∀ i,
          (∑' j, ‖(v₂ i * (starRingEnd ℂ) (v₁ i)) *
              (w₂ j * (starRingEnd ℂ) (w₁ j))‖) =
            ‖v₂ i * (starRingEnd ℂ) (v₁ i)‖ *
              ∑' j, ‖w₂ j * (starRingEnd ℂ) (w₁ j)‖ := by
        intro i
        simpa [norm_mul] using
          hΛ.norm.tsum_mul_left ‖v₂ i * (starRingEnd ℂ) (v₁ i)‖
      simpa only [hrow] using
        hΩ.norm.mul_right (∑' j, ‖w₂ j * (starRingEnd ℂ) (w₁ j)‖)
  rw [show (fun p : Ω × Λ =>
      v₂ p.1 * w₂ p.2 *
        ((starRingEnd ℂ) (v₁ p.1) * (starRingEnd ℂ) (w₁ p.2))) =
      fun p => (v₂ p.1 * (starRingEnd ℂ) (v₁ p.1)) *
        (w₂ p.2 * (starRingEnd ℂ) (w₁ p.2)) by
          funext p
          ring]
  exact (hΩ.tsum_mul_tsum hΛ hprod).symm

/-- Reindexing an `ℓ²` space by an equivalence is unitary. -/
noncomputable def lpReindexEquiv {ι κ : Type*} (e : ι ≃ κ) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2 where
  toFun x :=
    ⟨fun k => x (e.symm k), by
      apply memℓp_gen
      have hx :
          Summable (fun i : ι => ‖x i‖ ^ (2 : ENNReal).toReal) :=
        (memℓp_gen_iff (by norm_num)).mp (lp.memℓp x)
      exact e.symm.summable_iff.mpr hx⟩
  invFun y :=
    ⟨fun i => y (e i), by
      apply memℓp_gen
      have hy :
          Summable (fun k : κ => ‖y k‖ ^ (2 : ENNReal).toReal) :=
        (memℓp_gen_iff (by norm_num)).mp (lp.memℓp y)
      exact e.summable_iff.mpr hy⟩
  left_inv x := by
    apply lp.ext
    funext i
    simp
  right_inv y := by
    apply lp.ext
    funext k
    simp
  map_add' x y := by
    apply lp.ext
    funext k
    rfl
  map_smul' c x := by
    apply lp.ext
    funext k
    rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i : ι => ‖x i‖ ^ (2 : ENNReal).toReal)

@[simp] theorem lpReindexEquiv_apply
    {ι κ : Type*} (e : ι ≃ κ)
    (x : lp (fun _ : ι => ℂ) 2) (k : κ) :
    lpReindexEquiv e x k = x (e.symm k) := rfl

@[simp] theorem lpReindexEquiv_symm_apply
    {ι κ : Type*} (e : ι ≃ κ)
    (y : lp (fun _ : κ => ℂ) 2) (i : ι) :
    (lpReindexEquiv e).symm y i = y (e i) := rfl

/-! ## Local geometric half-density and Hellinger overlap -/

def geometricOccupationProbability (a : ℝ) (k : ℕ) : ℝ :=
  (1 - a) * a ^ k

theorem summable_geometricOccupationProbability {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (geometricOccupationProbability a) := by
  exact ((hasSum_geometric_of_lt_one ha0 ha1).summable.mul_left (1 - a)).congr
    (fun k => rfl)

theorem geometricOccupationProbability_nonneg {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (k : ℕ) :
    0 ≤ geometricOccupationProbability a k :=
  mul_nonneg (sub_nonneg.mpr ha1.le) (pow_nonneg ha0 k)

/-- Unit half-density of a geometric occupation law. -/
def geometricOccupationHalfDensity (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun k => (Real.sqrt (geometricOccupationProbability a k) : ℂ),
    HilbertSchmidt.memℓp_of_sq (by
      apply (summable_geometricOccupationProbability ha0 ha1).congr
      intro k
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (geometricOccupationProbability_nonneg ha0 ha1 k)])⟩

@[simp] theorem geometricOccupationHalfDensity_apply {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (k : ℕ) :
    geometricOccupationHalfDensity a ha0 ha1 k =
      (Real.sqrt (geometricOccupationProbability a k) : ℂ) := rfl

theorem norm_sq_geometricOccupationHalfDensity {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ‖geometricOccupationHalfDensity a ha0 ha1‖ ^ 2 = 1 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  have hsum := (hasSum_geometric_of_lt_one ha0 ha1).mul_left (1 - a)
  rw [show (fun k => ‖geometricOccupationHalfDensity a ha0 ha1 k‖ ^ 2) =
      geometricOccupationProbability a by
        funext k
        rw [geometricOccupationHalfDensity_apply, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (geometricOccupationProbability_nonneg ha0 ha1 k)]]
  change (∑' k, (1 - a) * a ^ k) = 1
  rw [hsum.tsum_eq]
  exact div_self (ne_of_gt (sub_pos.mpr ha1))

theorem inner_geometricOccupationHalfDensity {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    inner ℂ (geometricOccupationHalfDensity a ha0 ha1)
        (geometricOccupationHalfDensity b hb0 hb1) =
      (geometricHellingerAffinity a b : ℂ) := by
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, geometricOccupationHalfDensity_apply,
    Complex.conj_ofReal]
  rw [show (fun k => (Real.sqrt (geometricOccupationProbability b k) : ℂ) *
      (Real.sqrt (geometricOccupationProbability a k) : ℂ)) =
      fun k => (Real.sqrt (geometricOccupationProbability a k *
        geometricOccupationProbability b k) : ℂ) by
          funext k
          rw [Real.sqrt_mul (geometricOccupationProbability_nonneg ha0 ha1 k)]
          rw [← Complex.ofReal_mul]
          ring_nf]
  rw [← Complex.ofReal_tsum]
  exact_mod_cast (hasSum_geometricHellinger ha0 ha1 hb0 hb1).tsum_eq

/-! ## Finite occupation specialization -/

/-- Point mass of the normalized finite occupation probability law. -/
def finiteOccupationProbabilityWeight {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (ν : ι →₀ ℕ) : ℝ :=
  HTGeometry.finiteOccupationBoundaryVolume q * ν.prod (fun i n => q i ^ n)

theorem norm_finiteOccupationNormalizedHalfDensity_apply_sq
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (ν : ι →₀ ℕ) :
    ‖HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1 ν‖ ^ 2 =
      finiteOccupationProbabilityWeight q ν := by
  change ‖((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) : ℝ) : ℂ) *
      HTGeometry.finiteOccupationHalfDensityWeight q ν‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (HTGeometry.finiteOccupationBoundaryVolume_pos q hq1).le,
    HTGeometry.norm_finiteOccupationHalfDensityWeight_sq q hq0 ν]
  rfl

/-- Point mass on the card's literal finite-function carrier `ι → ℕ`. -/
def finiteFunctionOccupationProbabilityWeight {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (ν : ι → ℕ) : ℝ :=
  HTGeometry.finiteOccupationBoundaryVolume q * ∏ i, q i ^ ν i

/-- The normalized finite occupation half-density on `ℕ₀^ι`, transported from finite support
along the canonical equivalence valid for finite `ι`. -/
def finiteFunctionOccupationHalfDensity {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    lp (fun _ : ι → ℕ => ℂ) 2 :=
  lpReindexEquiv Finsupp.equivFunOnFinite
    (HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1)

theorem norm_sq_finiteFunctionOccupationHalfDensity_apply
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (ν : ι → ℕ) :
    ‖finiteFunctionOccupationHalfDensity q hq0 hq1 ν‖ ^ 2 =
      finiteFunctionOccupationProbabilityWeight q ν := by
  rw [finiteFunctionOccupationHalfDensity, lpReindexEquiv_apply,
    norm_finiteOccupationNormalizedHalfDensity_apply_sq]
  rw [finiteOccupationProbabilityWeight, finiteFunctionOccupationProbabilityWeight]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem norm_sq_finiteFunctionOccupationHalfDensity
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ‖finiteFunctionOccupationHalfDensity q hq0 hq1‖ ^ 2 = 1 := by
  rw [finiteFunctionOccupationHalfDensity,
    LinearIsometryEquiv.norm_map,
    HTGeometry.norm_finiteOccupationNormalizedHalfDensity_sq q hq0 hq1]

/-- Standard-form vector on the card's literal carrier `Ω_P = ℕ₀^P`. -/
def finiteFunctionOccupationThermofieldKernel {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (ι → ℕ) × (ι → ℕ) → ℂ :=
  thermofieldDiagonalKernel
    (finiteFunctionOccupationHalfDensity q hq0 hq1)

theorem finiteFunctionOccupationThermofieldKernel_isHS
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    HilbertSchmidt.IsHS
      (finiteFunctionOccupationThermofieldKernel q hq0 hq1) :=
  thermofieldDiagonalKernel_isHS _

theorem hsNormSq_finiteFunctionOccupationThermofieldKernel
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    HilbertSchmidt.hsNormSq
      (finiteFunctionOccupationThermofieldKernel q hq0 hq1) = 1 := by
  rw [finiteFunctionOccupationThermofieldKernel,
    hsNormSq_thermofieldDiagonalKernel,
    norm_sq_finiteFunctionOccupationHalfDensity q hq0 hq1]

theorem finiteFunctionOccupationThermofieldKernel_central
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (f : (ι → ℕ) → ℂ) :
    thermofieldLeftAction f
        (finiteFunctionOccupationThermofieldKernel q hq0 hq1) =
      thermofieldRightAction f
        (finiteFunctionOccupationThermofieldKernel q hq0 hq1) :=
  thermofieldDiagonalKernel_central _ f

theorem finiteFunctionOccupationThermofieldVectorState
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (f g : (ι → ℕ) → ℂ) (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ ν, ‖f ν‖ ≤ Cf) (hg : ∀ ν, ‖g ν‖ ≤ Cg) :
    HilbertSchmidt.hsInner
        (finiteFunctionOccupationThermofieldKernel q hq0 hq1)
        (thermofieldLeftAction f
          (thermofieldRightAction g
            (finiteFunctionOccupationThermofieldKernel q hq0 hq1))) =
      ∑' ν, (finiteFunctionOccupationProbabilityWeight q ν : ℂ) * f ν * g ν := by
  rw [finiteFunctionOccupationThermofieldKernel,
    hsInner_thermofieldDiagonalKernel_actions _ f g Cf Cg hCf hCg hf hg]
  apply tsum_congr
  intro ν
  rw [norm_sq_finiteFunctionOccupationHalfDensity_apply q hq0 hq1 ν]

def finiteFunctionOccupationTensorHalfDensity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1) :
    lp (fun _ : (ι → ℕ) × (κ → ℕ) => ℂ) 2 :=
  lpTensorProductVector
    (finiteFunctionOccupationHalfDensity q hq0 hq1)
    (finiteFunctionOccupationHalfDensity r hr0 hr1)

theorem norm_sq_finiteFunctionOccupationTensorHalfDensity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1) :
    ‖finiteFunctionOccupationTensorHalfDensity q r hq0 hq1 hr0 hr1‖ ^ 2 = 1 := by
  rw [finiteFunctionOccupationTensorHalfDensity, norm_sq_lpTensorProductVector,
    norm_sq_finiteFunctionOccupationHalfDensity q hq0 hq1,
    norm_sq_finiteFunctionOccupationHalfDensity r hr0 hr1, mul_one]

def finiteFunctionOccupationTensorThermofieldKernel
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1) :
    (((ι → ℕ) × (κ → ℕ)) × ((ι → ℕ) × (κ → ℕ))) → ℂ :=
  thermofieldDiagonalKernel
    (finiteFunctionOccupationTensorHalfDensity q r hq0 hq1 hr0 hr1)

/-- Literal `ℕ₀^P × ℕ₀^Q` form of disjoint-packet factorization `(19)`. -/
theorem finiteFunctionOccupationTensorThermofieldKernel_factor
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1)
    (x y : (ι → ℕ) × (κ → ℕ)) :
    finiteFunctionOccupationTensorThermofieldKernel
        q r hq0 hq1 hr0 hr1 (x, y) =
      finiteFunctionOccupationThermofieldKernel q hq0 hq1 (x.1, y.1) *
        finiteFunctionOccupationThermofieldKernel r hr0 hr1 (x.2, y.2) :=
  thermofieldDiagonalKernel_lpTensorProductVector _ _ x y

/-! ## Literal finite-prime Wold law -/

def finitePrimeOccupationRatio (S : Finset Nat.Primes) (p : S) : ℝ :=
  ((((p : Nat.Primes) : ℕ) : ℝ))⁻¹

theorem finitePrimeOccupationRatio_nonneg (S : Finset Nat.Primes) (p : S) :
    0 ≤ finitePrimeOccupationRatio S p := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem finitePrimeOccupationRatio_lt_one (S : Finset Nat.Primes) (p : S) :
    finitePrimeOccupationRatio S p < 1 := by
  rw [finitePrimeOccupationRatio]
  have hp0 : (0 : ℝ) < ((p : Nat.Primes) : ℕ) := by
    exact_mod_cast (p : Nat.Primes).2.pos
  apply (inv_lt_one₀ hp0).2
  exact_mod_cast (p : Nat.Primes).2.one_lt

def finitePrimeOccupationProbabilityWeight
    (S : Finset Nat.Primes) (ν : S → ℕ) : ℝ :=
  ∏ p : S, (1 - ((((p : Nat.Primes) : ℕ) : ℝ))⁻¹) *
    ((((p : Nat.Primes) : ℕ) : ℝ)) ^ (-(ν p : ℤ))

theorem finitePrimeFunctionOccupationProbabilityWeight_eq
    (S : Finset Nat.Primes) (ν : S → ℕ) :
    finiteFunctionOccupationProbabilityWeight
        (finitePrimeOccupationRatio S) ν =
      finitePrimeOccupationProbabilityWeight S ν := by
  rw [finiteFunctionOccupationProbabilityWeight,
    HTGeometry.finiteOccupationBoundaryVolume,
    finitePrimeOccupationProbabilityWeight]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [finitePrimeOccupationRatio]
  congr 1
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- Card `(18)` on the literal carrier `Ω_S = ℕ₀^S`. -/
def finitePrimeWoldThermofieldKernel (S : Finset Nat.Primes) :
    (S → ℕ) × (S → ℕ) → ℂ :=
  finiteFunctionOccupationThermofieldKernel
    (finitePrimeOccupationRatio S)
    (finitePrimeOccupationRatio_nonneg S)
    (finitePrimeOccupationRatio_lt_one S)

theorem finitePrimeWoldThermofieldKernel_isHS (S : Finset Nat.Primes) :
    HilbertSchmidt.IsHS (finitePrimeWoldThermofieldKernel S) :=
  finiteFunctionOccupationThermofieldKernel_isHS _ _ _

theorem hsNormSq_finitePrimeWoldThermofieldKernel (S : Finset Nat.Primes) :
    HilbertSchmidt.hsNormSq (finitePrimeWoldThermofieldKernel S) = 1 :=
  hsNormSq_finiteFunctionOccupationThermofieldKernel _ _ _

theorem finitePrimeWoldThermofieldKernel_central
    (S : Finset Nat.Primes) (f : (S → ℕ) → ℂ) :
    thermofieldLeftAction f (finitePrimeWoldThermofieldKernel S) =
      thermofieldRightAction f (finitePrimeWoldThermofieldKernel S) :=
  finiteFunctionOccupationThermofieldKernel_central _ _ _ f

theorem finitePrimeWoldThermofieldVectorState
    (S : Finset Nat.Primes) (f g : (S → ℕ) → ℂ)
    (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ ν, ‖f ν‖ ≤ Cf) (hg : ∀ ν, ‖g ν‖ ≤ Cg) :
    HilbertSchmidt.hsInner (finitePrimeWoldThermofieldKernel S)
        (thermofieldLeftAction f
          (thermofieldRightAction g (finitePrimeWoldThermofieldKernel S))) =
      ∑' ν, (finitePrimeOccupationProbabilityWeight S ν : ℂ) * f ν * g ν := by
  rw [finitePrimeWoldThermofieldKernel,
    finiteFunctionOccupationThermofieldVectorState _ _ _ f g Cf Cg hCf hCg hf hg]
  apply tsum_congr
  intro ν
  rw [finitePrimeFunctionOccupationProbabilityWeight_eq]

theorem finiteOccupationHalfDensityWeight_mul_conj
    {ι : Type*} [Fintype ι] (q r : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (ν : ι →₀ ℕ) :
    HTGeometry.finiteOccupationHalfDensityWeight r ν *
        (starRingEnd ℂ) (HTGeometry.finiteOccupationHalfDensityWeight q ν) =
      HTGeometry.nomeMonomial (fun i => (Real.sqrt (q i * r i) : ℂ)) ν := by
  simp only [HTGeometry.finiteOccupationHalfDensityWeight, HTGeometry.nomeMonomial,
    Finsupp.prod, map_prod, map_pow, Complex.conj_ofReal]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← mul_pow]
  congr 1
  rw [Real.sqrt_mul (hq0 i)]
  rw [← Complex.ofReal_mul]
  ring_nf

/-- Exact finite-product Hellinger overlap `(24)` for normalized occupation vectors. -/
theorem inner_finiteOccupationNormalizedHalfDensity
    {ι : Type*} [Fintype ι] (q r : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) :
    inner ℂ (HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1)
        (HTGeometry.finiteOccupationNormalizedHalfDensity r hr0 hr1) =
      (∏ i, geometricHellingerAffinity (q i) (r i) : ℂ) := by
  rw [lp.inner_eq_tsum]
  change (∑' ν : ι →₀ ℕ,
      ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume r) : ℂ) *
          HTGeometry.finiteOccupationHalfDensityWeight r ν) *
        (starRingEnd ℂ)
          ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) : ℂ) *
            HTGeometry.finiteOccupationHalfDensityWeight q ν)) = _
  let s : ι → ℂ := fun i => (Real.sqrt (q i * r i) : ℂ)
  have hs : ∀ i, ‖s i‖ < 1 := by
    intro i
    change ‖(Real.sqrt (q i * r i) : ℂ)‖ < 1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sqrt_lt' zero_lt_one]
    nlinarith [hq0 i, hq1 i, hr0 i, hr1 i]
  have hEuler :
      (∑' ν : ι →₀ ℕ, HTGeometry.nomeMonomial s ν) =
        ∏ i, (1 - s i)⁻¹ := by
    let e := (Finsupp.equivFunOnFinite : (ι →₀ ℕ) ≃ (ι → ℕ))
    calc
      (∑' ν : ι →₀ ℕ, HTGeometry.nomeMonomial s ν) =
          ∑' ν : ι →₀ ℕ, ∏ i, s i ^ (e ν) i := by
            apply tsum_congr
            intro ν
            rw [HTGeometry.nomeMonomial,
              Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
            rfl
      _ = ∑' f : ι → ℕ, ∏ i, s i ^ f i :=
        e.tsum_eq (fun f : ι → ℕ => ∏ i, s i ^ f i)
      _ = ∏ i, (1 - s i)⁻¹ :=
        HTGeometry.complex_tsum_pi_geometric s hs
  rw [show (fun ν : ι →₀ ℕ =>
      ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume r) : ℂ) *
          HTGeometry.finiteOccupationHalfDensityWeight r ν) *
        (starRingEnd ℂ)
          ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) : ℂ) *
            HTGeometry.finiteOccupationHalfDensityWeight q ν)) =
      fun ν => ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume r) : ℂ) *
          (Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) : ℂ)) *
        HTGeometry.nomeMonomial s ν by
          funext ν
          rw [map_mul, Complex.conj_ofReal]
          calc
            ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume r) : ℂ) *
                HTGeometry.finiteOccupationHalfDensityWeight r ν) *
              ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) : ℂ) *
                (starRingEnd ℂ) (HTGeometry.finiteOccupationHalfDensityWeight q ν)) =
              ((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume r) : ℂ) *
                (Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) : ℂ)) *
              (HTGeometry.finiteOccupationHalfDensityWeight r ν *
                (starRingEnd ℂ) (HTGeometry.finiteOccupationHalfDensityWeight q ν)) := by
                  ring_nf
            _ = _ := by
              rw [finiteOccupationHalfDensityWeight_mul_conj q r hq0 ν]]
  rw [tsum_mul_left, hEuler]
  simp only [s]
  have hsqrtq :
      Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) =
        ∏ i, Real.sqrt (1 - q i) := by
    rw [HTGeometry.finiteOccupationBoundaryVolume]
    simpa using Real.sqrt_prod (Finset.univ : Finset ι)
      (fun i _ => sub_nonneg.mpr (hq1 i).le)
  have hsqrtr :
      Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume r) =
        ∏ i, Real.sqrt (1 - r i) := by
    rw [HTGeometry.finiteOccupationBoundaryVolume]
    simpa using Real.sqrt_prod (Finset.univ : Finset ι)
      (fun i _ => sub_nonneg.mpr (hr1 i).le)
  have hnum :
      (∏ i, Real.sqrt (1 - r i)) * (∏ i, Real.sqrt (1 - q i)) =
        ∏ i, Real.sqrt ((1 - q i) * (1 - r i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Real.sqrt_mul (sub_nonneg.mpr (hq1 i).le)]
    ring_nf
  have hreal :
      Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume r) *
          Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) *
          ∏ i, (1 - Real.sqrt (q i * r i))⁻¹ =
        ∏ i, geometricHellingerAffinity (q i) (r i) := by
    rw [hsqrtr, hsqrtq, hnum]
    simp only [geometricHellingerAffinity]
    rw [Finset.prod_div_distrib, div_eq_mul_inv, Finset.prod_inv_distrib]
  exact_mod_cast hreal

/-- Diagonal standard-form purification of the normalized finite occupation law. -/
def finiteOccupationThermofieldKernel {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (ι →₀ ℕ) × (ι →₀ ℕ) → ℂ :=
  thermofieldDiagonalKernel
    (HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1)

theorem finiteOccupationThermofieldKernel_isHS {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    HilbertSchmidt.IsHS (finiteOccupationThermofieldKernel q hq0 hq1) :=
  thermofieldDiagonalKernel_isHS _

theorem hsNormSq_finiteOccupationThermofieldKernel {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    HilbertSchmidt.hsNormSq (finiteOccupationThermofieldKernel q hq0 hq1) = 1 := by
  rw [finiteOccupationThermofieldKernel, hsNormSq_thermofieldDiagonalKernel,
    HTGeometry.norm_finiteOccupationNormalizedHalfDensity_sq q hq0 hq1]

theorem finiteOccupationThermofieldKernel_central {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (f : (ι →₀ ℕ) → ℂ) :
    thermofieldLeftAction f (finiteOccupationThermofieldKernel q hq0 hq1) =
      thermofieldRightAction f (finiteOccupationThermofieldKernel q hq0 hq1) :=
  thermofieldDiagonalKernel_central _ f

theorem finiteOccupationThermofieldVectorState {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (f g : (ι →₀ ℕ) → ℂ) (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ ν, ‖f ν‖ ≤ Cf) (hg : ∀ ν, ‖g ν‖ ≤ Cg) :
    HilbertSchmidt.hsInner (finiteOccupationThermofieldKernel q hq0 hq1)
        (thermofieldLeftAction f
          (thermofieldRightAction g (finiteOccupationThermofieldKernel q hq0 hq1))) =
      ∑' ν, (finiteOccupationProbabilityWeight q ν : ℂ) * f ν * g ν := by
  rw [finiteOccupationThermofieldKernel,
    hsInner_thermofieldDiagonalKernel_actions _ f g Cf Cg hCf hCg hf hg]
  apply tsum_congr
  intro ν
  rw [norm_finiteOccupationNormalizedHalfDensity_apply_sq q hq0 hq1 ν]

/-- Normalized occupation vector for two disjoint finite packets under their canonical product
carrier identification. -/
def finiteOccupationTensorHalfDensity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1) :
    lp (fun _ : (ι →₀ ℕ) × (κ →₀ ℕ) => ℂ) 2 :=
  lpTensorProductVector
    (HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1)
    (HTGeometry.finiteOccupationNormalizedHalfDensity r hr0 hr1)

theorem norm_sq_finiteOccupationTensorHalfDensity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1) :
    ‖finiteOccupationTensorHalfDensity q r hq0 hq1 hr0 hr1‖ ^ 2 = 1 := by
  rw [finiteOccupationTensorHalfDensity, norm_sq_lpTensorProductVector,
    HTGeometry.norm_finiteOccupationNormalizedHalfDensity_sq q hq0 hq1,
    HTGeometry.norm_finiteOccupationNormalizedHalfDensity_sq r hr0 hr1,
    mul_one]

/-- Exact coefficient form of disjoint-packet factorization `(19)`. -/
theorem finiteOccupationTensorHalfDensity_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1)
    (ν : ι →₀ ℕ) (ω : κ →₀ ℕ) :
    finiteOccupationTensorHalfDensity q r hq0 hq1 hr0 hr1 (ν, ω) =
      HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1 ν *
        HTGeometry.finiteOccupationNormalizedHalfDensity r hr0 hr1 ω := rfl

/-- Diagonal standard-form kernel for the canonical product of two disjoint occupation packets. -/
def finiteOccupationTensorThermofieldKernel
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1) :
    ((ι →₀ ℕ) × (κ →₀ ℕ)) × ((ι →₀ ℕ) × (κ →₀ ℕ)) → ℂ :=
  thermofieldDiagonalKernel
    (finiteOccupationTensorHalfDensity q r hq0 hq1 hr0 hr1)

/-- Exact standard-form tensor shuffle for disjoint finite occupation packets. -/
theorem finiteOccupationTensorThermofieldKernel_factor
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (r : κ → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j < 1)
    (x y : (ι →₀ ℕ) × (κ →₀ ℕ)) :
    finiteOccupationTensorThermofieldKernel q r hq0 hq1 hr0 hr1 (x, y) =
      finiteOccupationThermofieldKernel q hq0 hq1 (x.1, y.1) *
        finiteOccupationThermofieldKernel r hr0 hr1 (x.2, y.2) :=
  thermofieldDiagonalKernel_lpTensorProductVector _ _ x y

end GaloisForLFunctions.HTGeometry
