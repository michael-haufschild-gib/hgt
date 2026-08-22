import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Reciprocal contraction sections: full binary history and adjoint-mate fracture

Let `H j` be a sequence of complex Hilbert spaces and let

`T⁺_j, T⁻_j : H (j+1) → H j`

be contractions carrying a distinguished nonzero vector `y (j+1)` to `conj λ • y j` and
`conj λ⁻¹ • y j` respectively.  Two unconditional laws follow from that data alone.

* **Full-history contraction and exact energy.**  The normalized map sending `x ∈ H N` to the
  family `2^{-N/2} T_ω x`, indexed by the `2^N` words `ω ∈ {+,-}^N`, is a contraction, and on the
  distinguished vector its energy is exactly `((a² + a⁻²)/2)^N ‖y 0‖²` with `a = ‖λ‖`.  Hence
  `‖y N‖ ≥ ((a² + a⁻²)/2)^{N/2} ‖y 0‖`.

* **Adjoint-mate fracture.**  The two defects between the Hilbert adjoint lift and the algebraic
  inverse lift have radial coefficients whose normalized difference is exactly `a² − a⁻²`,
  independently of the aperture norm ratio; consequently at every level one of the two mates has
  relative defect at least `|a² − a⁻²|`, and simultaneous vanishing of both relative defects forces
  `a = 1`.

Everything is unconditional Hilbert-space algebra; no arithmetic input is used.
-/

open scoped BigOperators

namespace HTGeometry

section BooleanSonin

variable {H : ℕ → Type*} [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℂ (H j)]

/-- A reciprocal contraction section: two downward contractions with a distinguished eigenray on
which they act by the reciprocal characters `conj λ` and `conj λ⁻¹`. -/
structure ReciprocalContractionSection (H : ℕ → Type*)
    [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℂ (H j)] (lam : ℂ) where
  /-- The two downward maps, indexed by a Boolean sign. -/
  T : Bool → ∀ j : ℕ, H (j + 1) →L[ℂ] H j
  /-- Both maps are contractions. -/
  contract : ∀ (b : Bool) (j : ℕ) (x : H (j + 1)), ‖T b j x‖ ≤ ‖x‖
  /-- The distinguished vectors. -/
  y : ∀ j : ℕ, H j
  /-- They are nonzero. -/
  y_ne : ∀ j : ℕ, y j ≠ 0
  /-- The plus map acts by `conj λ`. -/
  T_true : ∀ j : ℕ, T true j (y (j + 1)) = (starRingEnd ℂ) lam • y j
  /-- The minus map acts by `conj λ⁻¹`. -/
  T_false : ∀ j : ℕ, T false j (y (j + 1)) = (starRingEnd ℂ) lam⁻¹ • y j

variable {lam : ℂ}

/-- The word map `T_ω = T^{ω₀}_0 ⋯ T^{ω_{N-1}}_{N-1} : H N → H 0`. -/
def ReciprocalContractionSection.wordMap (S : ReciprocalContractionSection H lam) :
    ∀ N : ℕ, (Fin N → Bool) → (H N →L[ℂ] H 0)
  | 0, _ => ContinuousLinearMap.id ℂ (H 0)
  | N + 1, ω =>
      (S.wordMap N fun i => ω i.castSucc).comp (S.T (ω (Fin.last N)) N)

@[simp] theorem ReciprocalContractionSection.wordMap_zero
    (S : ReciprocalContractionSection H lam) (ω : Fin 0 → Bool) (x : H 0) :
    S.wordMap 0 ω x = x := rfl

theorem ReciprocalContractionSection.wordMap_succ (S : ReciprocalContractionSection H lam)
    (N : ℕ) (ω : Fin (N + 1) → Bool) (x : H (N + 1)) :
    S.wordMap (N + 1) ω x =
      S.wordMap N (fun i => ω i.castSucc) (S.T (ω (Fin.last N)) N x) := rfl

/-- Splitting a Boolean word into its initial segment and its last letter. -/
def snocBoolEquiv (N : ℕ) : ((Fin N → Bool) × Bool) ≃ (Fin (N + 1) → Bool) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (fun i => ω i.castSucc, ω (Fin.last N))
  left_inv p := by
    ext i
    · simp
    · simp
  right_inv ω := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp

/-- The unnormalized full-history energy `∑_ω ‖T_ω x‖²`. -/
noncomputable def ReciprocalContractionSection.historyEnergy
    (S : ReciprocalContractionSection H lam) (N : ℕ) (x : H N) : ℝ :=
  ∑ ω : Fin N → Bool, ‖S.wordMap N ω x‖ ^ 2

theorem ReciprocalContractionSection.historyEnergy_zero
    (S : ReciprocalContractionSection H lam) (x : H 0) :
    S.historyEnergy 0 x = ‖x‖ ^ 2 := by
  simp [historyEnergy]

theorem ReciprocalContractionSection.historyEnergy_succ
    (S : ReciprocalContractionSection H lam) (N : ℕ) (x : H (N + 1)) :
    S.historyEnergy (N + 1) x =
      S.historyEnergy N (S.T true N x) + S.historyEnergy N (S.T false N x) := by
  rw [historyEnergy, ← Fintype.sum_equiv (snocBoolEquiv N)
    (fun p => ‖S.wordMap (N + 1) (snocBoolEquiv N p) x‖ ^ 2)
    (fun ω => ‖S.wordMap (N + 1) ω x‖ ^ 2) (fun p => rfl)]
  rw [Fintype.sum_prod_type_right]
  have hval : ∀ (b : Bool) (ω : Fin N → Bool),
      ‖S.wordMap (N + 1) (snocBoolEquiv N (ω, b)) x‖ ^ 2
        = ‖S.wordMap N ω (S.T b N x)‖ ^ 2 := by
    intro b ω
    have hcast : (fun i : Fin N => (snocBoolEquiv N) (ω, b) i.castSucc) = ω := by
      funext i
      simp [snocBoolEquiv]
    have hlast : (snocBoolEquiv N) (ω, b) (Fin.last N) = b := by
      simp [snocBoolEquiv]
    rw [ReciprocalContractionSection.wordMap_succ, hcast, hlast]
  simp only [hval]
  rw [Fintype.sum_bool]
  rw [historyEnergy, historyEnergy]

/-- **Full-history contraction.**  `2^{-N} ∑_ω ‖T_ω x‖² ≤ ‖x‖²`. -/
theorem ReciprocalContractionSection.historyEnergy_le
    (S : ReciprocalContractionSection H lam) (N : ℕ) (x : H N) :
    S.historyEnergy N x ≤ 2 ^ N * ‖x‖ ^ 2 := by
  induction N with
  | zero => simp [historyEnergy_zero]
  | succ N ih =>
      rw [historyEnergy_succ]
      have h1 := ih (S.T true N x)
      have h2 := ih (S.T false N x)
      have hc1 : ‖S.T true N x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (S.contract true N x) 2
      have hc2 : ‖S.T false N x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (S.contract false N x) 2
      have hpow : (0 : ℝ) ≤ 2 ^ N := by positivity
      calc S.historyEnergy N (S.T true N x) + S.historyEnergy N (S.T false N x)
          ≤ 2 ^ N * ‖S.T true N x‖ ^ 2 + 2 ^ N * ‖S.T false N x‖ ^ 2 := by linarith
        _ ≤ 2 ^ N * ‖x‖ ^ 2 + 2 ^ N * ‖x‖ ^ 2 := by
            exact add_le_add (mul_le_mul_of_nonneg_left hc1 hpow)
              (mul_le_mul_of_nonneg_left hc2 hpow)
        _ = 2 ^ (N + 1) * ‖x‖ ^ 2 := by ring

theorem ReciprocalContractionSection.wordMap_smul
    (S : ReciprocalContractionSection H lam) (N : ℕ) (ω : Fin N → Bool) (c : ℂ) (x : H N) :
    S.wordMap N ω (c • x) = c • S.wordMap N ω x :=
  map_smul _ _ _

theorem ReciprocalContractionSection.historyEnergy_smul
    (S : ReciprocalContractionSection H lam) (N : ℕ) (c : ℂ) (x : H N) :
    S.historyEnergy N (c • x) = ‖c‖ ^ 2 * S.historyEnergy N x := by
  rw [historyEnergy, historyEnergy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [wordMap_smul, norm_smul]
  ring

/-- **Exact full-history energy on the distinguished ray.** -/
theorem ReciprocalContractionSection.historyEnergy_y
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (N : ℕ) :
    S.historyEnergy N (S.y N) = (‖lam‖ ^ 2 + ‖lam‖⁻¹ ^ 2) ^ N * ‖S.y 0‖ ^ 2 := by
  induction N with
  | zero => simp [historyEnergy_zero]
  | succ N ih =>
      have hnorm : ‖lam‖ ≠ 0 := norm_ne_zero_iff.mpr hlam
      rw [historyEnergy_succ, S.T_true N, S.T_false N, historyEnergy_smul, historyEnergy_smul, ih]
      have h1 : ‖(starRingEnd ℂ) lam‖ = ‖lam‖ := by simp
      have h2 : ‖(starRingEnd ℂ) lam⁻¹‖ = ‖lam‖⁻¹ := by simp
      rw [h1, h2]
      ring

/-- **Lower growth of the distinguished ray.** -/
theorem ReciprocalContractionSection.norm_y_lower
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (N : ℕ) :
    ((‖lam‖ ^ 2 + ‖lam‖⁻¹ ^ 2) / 2) ^ N * ‖S.y 0‖ ^ 2 ≤ ‖S.y N‖ ^ 2 := by
  have hE := S.historyEnergy_y hlam N
  have hle := S.historyEnergy_le N (S.y N)
  rw [hE] at hle
  have hpow : (0 : ℝ) < 2 ^ N := by positivity
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hpow]
  calc (‖lam‖ ^ 2 + ‖lam‖⁻¹ ^ 2) ^ N * ‖S.y 0‖ ^ 2 ≤ 2 ^ N * ‖S.y N‖ ^ 2 := hle
    _ = ‖S.y N‖ ^ 2 * 2 ^ N := by ring

/-! ## The adjoint-mate fracture -/

/-- The aperture norm ratio `R_j = ‖y (j+1)‖ / ‖y j‖`. -/
noncomputable def ReciprocalContractionSection.ratio
    (S : ReciprocalContractionSection H lam) (j : ℕ) : ℝ :=
  ‖S.y (j + 1)‖ / ‖S.y j‖

theorem ReciprocalContractionSection.ratio_pos (S : ReciprocalContractionSection H lam) (j : ℕ) :
    0 < S.ratio j :=
  div_pos (norm_pos_iff.mpr (S.y_ne (j + 1))) (norm_pos_iff.mpr (S.y_ne j))

/-- Contractivity forces `R_j ≥ ‖λ‖`. -/
theorem ReciprocalContractionSection.norm_le_ratio
    (S : ReciprocalContractionSection H lam) (j : ℕ) : ‖lam‖ ≤ S.ratio j := by
  have h := S.contract true j (S.y (j + 1))
  rw [S.T_true j, norm_smul] at h
  simp only [RCLike.norm_conj] at h
  rw [ReciprocalContractionSection.ratio, le_div_iff₀ (norm_pos_iff.mpr (S.y_ne j))]
  linarith

/-- Contractivity forces `R_j ≥ ‖λ‖⁻¹`. -/
theorem ReciprocalContractionSection.inv_norm_le_ratio
    (S : ReciprocalContractionSection H lam) (_hlam : lam ≠ 0) (j : ℕ) :
    ‖lam‖⁻¹ ≤ S.ratio j := by
  have h := S.contract false j (S.y (j + 1))
  rw [S.T_false j, norm_smul] at h
  simp only [RCLike.norm_conj, norm_inv] at h
  rw [ReciprocalContractionSection.ratio, le_div_iff₀ (norm_pos_iff.mpr (S.y_ne j))]
  linarith

/-! ## The adjoint-mate defects -/

section Mate

variable [∀ j, CompleteSpace (H j)]

/-- The algebraic inverse lift dictated by the eigenray relation. -/
noncomputable def ReciprocalContractionSection.inverseLift (lam : ℂ) (b : Bool) : ℂ :=
  (starRingEnd ℂ) (if b then lam⁻¹ else lam)

/-- The mate defect `D_j^b = (T_j^b)^* y_j − (inverse lift) y_{j+1}`. -/
noncomputable def ReciprocalContractionSection.mateDefect
    (S : ReciprocalContractionSection H lam) (b : Bool) (j : ℕ) : H (j + 1) :=
  (ContinuousLinearMap.adjoint (S.T b j)) (S.y j) -
    ReciprocalContractionSection.inverseLift lam b • S.y (j + 1)

/-- The radial coefficient of the mate defect on the distinguished ray. -/
noncomputable def ReciprocalContractionSection.mateCoeff
    (S : ReciprocalContractionSection H lam) (b : Bool) (j : ℕ) : ℂ :=
  inner ℂ (S.y (j + 1)) (S.mateDefect b j) / ((‖S.y (j + 1)‖ ^ 2 : ℝ) : ℂ)

theorem ReciprocalContractionSection.norm_mateCoeff_smul_le
    (S : ReciprocalContractionSection H lam) (b : Bool) (j : ℕ) :
    ‖S.mateCoeff b j • S.y (j + 1)‖ ≤ ‖S.mateDefect b j‖ := by
  have hy : 0 < ‖S.y (j + 1)‖ := norm_pos_iff.mpr (S.y_ne (j + 1))
  rw [norm_smul, ReciprocalContractionSection.mateCoeff, norm_div]
  have hnorm : ‖((‖S.y (j + 1)‖ ^ 2 : ℝ) : ℂ)‖ = ‖S.y (j + 1)‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hnorm]
  have hcs : ‖inner ℂ (S.y (j + 1)) (S.mateDefect b j)‖ ≤
      ‖S.y (j + 1)‖ * ‖S.mateDefect b j‖ := norm_inner_le_norm _ _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (S.mateDefect b j)]

/-- **Exact radial mate coefficients.**  Plus mate: `λ / R_j² − conj(λ⁻¹) = (R_j⁻² − ‖λ‖⁻²) λ`. -/
theorem ReciprocalContractionSection.mateCoeff_true
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (j : ℕ) :
    S.mateCoeff true j = (((S.ratio j ^ 2)⁻¹ - (‖lam‖ ^ 2)⁻¹ : ℝ) : ℂ) * lam := by
  have hyj : (0 : ℝ) < ‖S.y j‖ := norm_pos_iff.mpr (S.y_ne j)
  have hyj1 : (0 : ℝ) < ‖S.y (j + 1)‖ := norm_pos_iff.mpr (S.y_ne (j + 1))
  have hinner : inner ℂ (S.y (j + 1)) ((ContinuousLinearMap.adjoint (S.T true j)) (S.y j))
      = lam * ((‖S.y j‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_right, S.T_true j, inner_smul_left,
      inner_self_eq_norm_sq_to_K]
    simp
  have hself : inner ℂ (S.y (j + 1)) (S.y (j + 1)) = ((‖S.y (j + 1)‖ ^ 2 : ℝ) : ℂ) := by
    simp
  have hnum : inner ℂ (S.y (j + 1)) (S.mateDefect true j)
      = lam * ((‖S.y j‖ ^ 2 : ℝ) : ℂ)
        - (starRingEnd ℂ) lam⁻¹ * ((‖S.y (j + 1)‖ ^ 2 : ℝ) : ℂ) := by
    rw [ReciprocalContractionSection.mateDefect, inner_sub_right, inner_smul_right, hinner, hself]
    simp [ReciprocalContractionSection.inverseLift]
  have hsq : ((‖lam‖ ^ 2 : ℝ) : ℂ) = lam * (starRingEnd ℂ) lam := by
    rw [mul_comm, Complex.conj_mul', Complex.ofReal_pow]
  have hconj : (starRingEnd ℂ) lam⁻¹ = lam * (((‖lam‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [map_inv₀, Complex.ofReal_inv, hsq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  rw [ReciprocalContractionSection.mateCoeff, hnum, hconj, ReciprocalContractionSection.ratio]
  have hane : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hlam).ne'
  have hy0ne : ((‖S.y j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyj.ne'
  have hy1ne : ((‖S.y (j + 1)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyj1.ne'
  push_cast
  field_simp

/-- **Exact radial mate coefficients.**  Minus mate:
`λ⁻¹ / R_j² − conj λ = (‖λ‖⁻² R_j⁻² − 1) conj λ`. -/
theorem ReciprocalContractionSection.mateCoeff_false
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (j : ℕ) :
    S.mateCoeff false j =
      ((((‖lam‖ ^ 2)⁻¹ * (S.ratio j ^ 2)⁻¹ - 1 : ℝ)) : ℂ) * (starRingEnd ℂ) lam := by
  have hyj : (0 : ℝ) < ‖S.y j‖ := norm_pos_iff.mpr (S.y_ne j)
  have hyj1 : (0 : ℝ) < ‖S.y (j + 1)‖ := norm_pos_iff.mpr (S.y_ne (j + 1))
  have hinner : inner ℂ (S.y (j + 1)) ((ContinuousLinearMap.adjoint (S.T false j)) (S.y j))
      = lam⁻¹ * ((‖S.y j‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_right, S.T_false j, inner_smul_left,
      inner_self_eq_norm_sq_to_K]
    simp
  have hself : inner ℂ (S.y (j + 1)) (S.y (j + 1)) = ((‖S.y (j + 1)‖ ^ 2 : ℝ) : ℂ) := by
    simp
  have hnum : inner ℂ (S.y (j + 1)) (S.mateDefect false j)
      = lam⁻¹ * ((‖S.y j‖ ^ 2 : ℝ) : ℂ)
        - (starRingEnd ℂ) lam * ((‖S.y (j + 1)‖ ^ 2 : ℝ) : ℂ) := by
    rw [ReciprocalContractionSection.mateDefect, inner_sub_right, inner_smul_right, hinner, hself]
    simp [ReciprocalContractionSection.inverseLift]
  have hinv : lam⁻¹ = (starRingEnd ℂ) lam * (((‖lam‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.inv_def]
    congr 1
    rw [Complex.normSq_eq_norm_sq]
  rw [ReciprocalContractionSection.mateCoeff, hnum, hinv, ReciprocalContractionSection.ratio]
  have hane : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hlam).ne'
  have hy0ne : ((‖S.y j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyj.ne'
  have hy1ne : ((‖S.y (j + 1)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hyj1.ne'
  push_cast
  field_simp

/-- **The aperture norm cancels from the normalized mate difference.** -/
theorem ReciprocalContractionSection.mate_difference
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (j : ℕ) :
    lam⁻¹ * S.mateCoeff true j - lam * S.mateCoeff false j =
      ((‖lam‖ ^ 2 : ℝ) : ℂ) - (((‖lam‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hmul : lam * (starRingEnd ℂ) lam = ((‖lam‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.conj_mul']
  rw [S.mateCoeff_true hlam j, S.mateCoeff_false hlam j]
  have hR : (S.ratio j : ℂ) ≠ 0 := by
    exact_mod_cast (S.ratio_pos j).ne'
  have ha : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hlam).ne'
  push_cast
  field_simp
  linear_combination (((‖lam‖ : ℝ) : ℂ) ^ 2 * (S.ratio j : ℂ) ^ 2 - 1) * hmul

theorem ReciprocalContractionSection.norm_mateCoeff_true
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (j : ℕ) :
    ‖S.mateCoeff true j‖ = |(S.ratio j ^ 2)⁻¹ - (‖lam‖ ^ 2)⁻¹| * ‖lam‖ := by
  rw [S.mateCoeff_true hlam j, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem ReciprocalContractionSection.norm_mateCoeff_false
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (j : ℕ) :
    ‖S.mateCoeff false j‖ = |(‖lam‖ ^ 2)⁻¹ * (S.ratio j ^ 2)⁻¹ - 1| * ‖lam‖ := by
  rw [S.mateCoeff_false hlam j, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]

/-- **Persistent adjoint-mate fracture.**  At every level, one of the two radial mate defects has
relative size at least `|‖λ‖² − ‖λ‖⁻²|`. -/
theorem ReciprocalContractionSection.mate_fracture
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0) (j : ℕ) :
    |‖lam‖ ^ 2 - (‖lam‖ ^ 2)⁻¹| * ‖S.y j‖ ≤
      max ‖S.mateDefect true j‖ ‖S.mateDefect false j‖ := by
  set a : ℝ := ‖lam‖ with hadef
  set R : ℝ := S.ratio j with hRdef
  have ha : 0 < a := norm_pos_iff.mpr hlam
  have hR : 0 < R := S.ratio_pos j
  have hRa : a ≤ R := S.norm_le_ratio j
  have hRa' : a⁻¹ ≤ R := S.inv_norm_le_ratio hlam j
  have hyj : (0 : ℝ) < ‖S.y j‖ := norm_pos_iff.mpr (S.y_ne j)
  have hy1 : ‖S.y (j + 1)‖ = R * ‖S.y j‖ := by
    rw [hRdef, ReciprocalContractionSection.ratio]
    field_simp
  have hcoeff : ∀ b : Bool, ‖S.mateCoeff b j • S.y (j + 1)‖ =
      ‖S.mateCoeff b j‖ * R * ‖S.y j‖ := by
    intro b
    rw [norm_smul, hy1]
    ring
  have key : |a ^ 2 - (a ^ 2)⁻¹| ≤ max (‖S.mateCoeff true j‖ * R) (‖S.mateCoeff false j‖ * R) := by
    rcases le_or_gt 1 a with hge | hlt
    · -- `a ≥ 1`: the minus mate carries the fracture
      have habs : |a ^ 2 - (a ^ 2)⁻¹| = a ^ 2 - (a ^ 2)⁻¹ := by
        rw [abs_of_nonneg]
        have h1 : (a ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (by positivity)]
          nlinarith
        nlinarith
      have hprod : 1 ≤ a ^ 2 * R ^ 2 := by
        have h1R : (1 : ℝ) ≤ R := le_trans hge hRa
        have ha2 : (1 : ℝ) ≤ a ^ 2 := by nlinarith
        have hR2 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
        nlinarith [ha2, hR2]
      have hnf : ‖S.mateCoeff false j‖ = (1 - (a ^ 2)⁻¹ * (R ^ 2)⁻¹) * a := by
        rw [S.norm_mateCoeff_false hlam j, ← hadef, ← hRdef, abs_of_nonpos, neg_sub]
        rw [sub_nonpos, ← mul_inv, inv_le_one₀ (by positivity)]
        exact hprod
      have hbound : a ^ 2 - (a ^ 2)⁻¹ ≤ ‖S.mateCoeff false j‖ * R := by
        rw [hnf]
        have hexp : (1 - (a ^ 2)⁻¹ * (R ^ 2)⁻¹) * a * R = a * R - (a * R)⁻¹ := by
          field_simp
        rw [hexp]
        have h1 : a ^ 2 ≤ a * R := by nlinarith
        have h2 : (a * R)⁻¹ ≤ (a ^ 2)⁻¹ := by
          apply inv_anti₀ (by positivity)
          nlinarith
        linarith
      rw [habs]
      exact le_max_of_le_right hbound
    · -- `a < 1`: the plus mate carries the fracture
      have habs : |a ^ 2 - (a ^ 2)⁻¹| = (a ^ 2)⁻¹ - a ^ 2 := by
        rw [abs_of_nonpos, neg_sub]
        have h1 : (1 : ℝ) ≤ (a ^ 2)⁻¹ := by
          rw [le_inv_comm₀ (by norm_num) (by positivity)]
          nlinarith
        nlinarith
      have hRinv : 1 ≤ a * R := by
        have := mul_le_mul_of_nonneg_left hRa' ha.le
        rw [mul_inv_cancel₀ ha.ne'] at this
        linarith
      have hnt : ‖S.mateCoeff true j‖ = ((a ^ 2)⁻¹ - (R ^ 2)⁻¹) * a := by
        rw [S.norm_mateCoeff_true hlam j, ← hadef, ← hRdef, abs_of_nonpos, neg_sub]
        rw [sub_nonpos]
        apply inv_anti₀ (by positivity)
        nlinarith
      have hbound : (a ^ 2)⁻¹ - a ^ 2 ≤ ‖S.mateCoeff true j‖ * R := by
        rw [hnt]
        have hexp : ((a ^ 2)⁻¹ - (R ^ 2)⁻¹) * a * R = R * a⁻¹ - a * R⁻¹ := by
          field_simp
        rw [hexp]
        have h1 : (a ^ 2)⁻¹ ≤ R * a⁻¹ := by
          rw [show (a ^ 2)⁻¹ = a⁻¹ * a⁻¹ by rw [← mul_inv]; ring_nf]
          have : a⁻¹ ≤ R := hRa'
          nlinarith [inv_pos.mpr ha]
        have h2 : a * R⁻¹ ≤ a ^ 2 := by
          have hRinv2 : R⁻¹ ≤ a := by
            rw [inv_le_comm₀ hR ha]
            exact hRa'
          nlinarith
        linarith
      rw [habs]
      exact le_max_of_le_left hbound
  have hfinal : |a ^ 2 - (a ^ 2)⁻¹| * ‖S.y j‖ ≤
      max (‖S.mateCoeff true j‖ * R * ‖S.y j‖) (‖S.mateCoeff false j‖ * R * ‖S.y j‖) := by
    rcases le_total (‖S.mateCoeff true j‖ * R) (‖S.mateCoeff false j‖ * R) with h | h
    · rw [max_eq_right h] at key
      rw [max_eq_right (by nlinarith)]
      nlinarith
    · rw [max_eq_left h] at key
      rw [max_eq_left (by nlinarith)]
      nlinarith
  refine hfinal.trans (max_le_max ?_ ?_)
  · rw [← hcoeff true]; exact S.norm_mateCoeff_smul_le true j
  · rw [← hcoeff false]; exact S.norm_mateCoeff_smul_le false j

/-- **Simultaneous smallness of both mates forces the unitary locus.** -/
theorem ReciprocalContractionSection.norm_eq_one_of_mates_small
    (S : ReciprocalContractionSection H lam) (hlam : lam ≠ 0)
    (h : ∀ ε > (0 : ℝ), ∃ j : ℕ, ‖S.mateDefect true j‖ ≤ ε * ‖S.y j‖ ∧
      ‖S.mateDefect false j‖ ≤ ε * ‖S.y j‖) :
    ‖lam‖ = 1 := by
  by_contra hne
  set a : ℝ := ‖lam‖ with hadef
  have ha : 0 < a := norm_pos_iff.mpr hlam
  have hpos : 0 < |a ^ 2 - (a ^ 2)⁻¹| := by
    rw [abs_pos, sub_ne_zero]
    intro hEq
    apply hne
    have h4 : a ^ 2 * a ^ 2 = 1 := by
      field_simp at hEq
      nlinarith
    have h2 : a ^ 2 = 1 := by nlinarith [h4, sq_nonneg a, sq_nonneg (a ^ 2 - 1)]
    nlinarith [h2, ha]
  obtain ⟨j, h1, h2⟩ := h (|a ^ 2 - (a ^ 2)⁻¹| / 2) (by positivity)
  have hyj : (0 : ℝ) < ‖S.y j‖ := norm_pos_iff.mpr (S.y_ne j)
  have hfrac := S.mate_fracture hlam j
  rw [← hadef] at hfrac
  have hmax : max ‖S.mateDefect true j‖ ‖S.mateDefect false j‖ ≤
      |a ^ 2 - (a ^ 2)⁻¹| / 2 * ‖S.y j‖ := max_le h1 h2
  nlinarith

end Mate

end BooleanSonin

/-! ## The reciprocal dilation character `λ_r(ρ) = r^{ρ − 1/2}` -/

section DilationCharacter

/-- The normalized dilation character of a boundary point. -/
noncomputable def dilationCharacter (r : ℝ) (rho : ℂ) : ℂ :=
  (r : ℂ) ^ (rho - 1 / 2)

theorem norm_dilationCharacter {r : ℝ} (hr : 0 < r) (rho : ℂ) :
    ‖dilationCharacter r rho‖ = r ^ (rho.re - 1 / 2) := by
  rw [dilationCharacter, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

theorem dilationCharacter_ne_zero {r : ℝ} (hr : 0 < r) (rho : ℂ) :
    dilationCharacter r rho ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_dilationCharacter hr]
  exact (Real.rpow_pos_of_pos hr _).ne'

/-- The squared character is an exponential of the centered real part. -/
theorem sq_rpow_sub_half {r : ℝ} (hr : 0 < r) (sigma : ℝ) :
    (r ^ (sigma - 1 / 2) : ℝ) ^ 2 = Real.exp ((2 * sigma - 1) * Real.log r) := by
  rw [Real.rpow_def_of_pos hr, ← Real.exp_nat_mul]
  congr 1
  ring

/-- **Full-history excess is a hyperbolic cosine.** -/
theorem avg_sq_add_inv_sq_rpow {r : ℝ} (hr : 0 < r) (sigma : ℝ) :
    ((r ^ (sigma - 1 / 2) : ℝ) ^ 2 + ((r ^ (sigma - 1 / 2) : ℝ) ^ 2)⁻¹) / 2 =
      Real.cosh ((2 * sigma - 1) * Real.log r) := by
  rw [sq_rpow_sub_half hr, ← Real.exp_neg, Real.cosh_eq]

/-- **The mate curvature is a hyperbolic sine.** -/
theorem sq_sub_inv_sq_rpow {r : ℝ} (hr : 0 < r) (sigma : ℝ) :
    (r ^ (sigma - 1 / 2) : ℝ) ^ 2 - ((r ^ (sigma - 1 / 2) : ℝ) ^ 2)⁻¹ =
      2 * Real.sinh ((2 * sigma - 1) * Real.log r) := by
  rw [sq_rpow_sub_half hr, ← Real.exp_neg, Real.sinh_eq]
  ring

/-- The mate curvature of a dilation character vanishes exactly on the critical line, provided the
dilation is nontrivial. -/
theorem sq_sub_inv_sq_rpow_eq_zero_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (sigma : ℝ) :
    (r ^ (sigma - 1 / 2) : ℝ) ^ 2 - ((r ^ (sigma - 1 / 2) : ℝ) ^ 2)⁻¹ = 0 ↔ sigma = 1 / 2 := by
  rw [sq_sub_inv_sq_rpow hr]
  have hlog : Real.log r ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hr hr1
  constructor
  · intro h
    have hs : Real.sinh ((2 * sigma - 1) * Real.log r) = 0 := by linarith
    have hz := Real.sinh_eq_zero.mp hs
    have h2 : 2 * sigma - 1 = 0 := by
      rcases mul_eq_zero.mp hz with h' | h'
      · exact h'
      · exact absurd h' hlog
    linarith
  · intro h
    rw [h]
    norm_num

end DilationCharacter

end HTGeometry
