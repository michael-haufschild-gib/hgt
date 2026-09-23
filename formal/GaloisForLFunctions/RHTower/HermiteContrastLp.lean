import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast
import GaloisForLFunctions.RHTower.ConstrainedProlateOperatorIdentification

/-!
# The Hermite contrast ladder as an orthogonal system in `ℓ²`

The fixed-depth contrast vectors are supported on the first `k + 2` coordinates, so each is a
genuine `ℓ²` vector, not merely a coordinate array.  Their pairwise pairings vanish, so after
normalization they form an orthonormal system — the canonical orthogonal ladder selected by the
constrained spectrum.

Everything here is unconditional: the support is finite by construction, the orthogonality is the
algebraic pairing already established, and the normalization is legitimate because the top
coordinate `S_k / a_{k+1}` is nonzero.
-/

open Filter GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## Finite support and membership -/

theorem constrainedProlateHermiteContrast_eq_zero_of_notMem {k j : ℕ}
    (hj : j ∉ Finset.range (k + 2)) : constrainedProlateHermiteContrast k j = 0 := by
  rw [Finset.mem_range] at hj
  exact constrainedProlateHermiteContrast_eq_zero_of_succ_lt (by omega)

theorem summable_constrainedProlateHermiteContrast_sq (k : ℕ) :
    Summable fun j => constrainedProlateHermiteContrast k j ^ (2 : ℕ) := by
  refine summable_of_ne_finset_zero (s := Finset.range (k + 2)) ?_
  intro j hj
  rw [constrainedProlateHermiteContrast_eq_zero_of_notMem hj]
  exact zero_pow two_ne_zero

theorem memℓp_constrainedProlateHermiteContrast (k : ℕ) :
    Memℓp (constrainedProlateHermiteContrast k) 2 :=
  memℓp_two_of_sq_summable (summable_constrainedProlateHermiteContrast_sq k)

/-- The depth-`k` Hermite contrast vector as an element of `ℓ²`. -/
def hermiteContrastLp (k : ℕ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨constrainedProlateHermiteContrast k, memℓp_constrainedProlateHermiteContrast k⟩

@[simp] theorem hermiteContrastLp_coeFn (k : ℕ) :
    ((hermiteContrastLp k : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ)
      = constrainedProlateHermiteContrast k := rfl

/-! ## The inner product is the algebraic pairing -/

theorem inner_hermiteContrastLp (m k : ℕ) :
    inner ℝ (hermiteContrastLp m) (hermiteContrastLp k)
      = constrainedProlateHermiteContrastPairing m k := by
  rw [lp_inner_eq_tsum_mul, constrainedProlateHermiteContrastPairing]
  refine tsum_eq_sum ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have hm : constrainedProlateHermiteContrast m j = 0 :=
    constrainedProlateHermiteContrast_eq_zero_of_succ_lt (by omega)
  simp [hermiteContrastLp_coeFn, hm]

/-- **The contrast ladder is orthogonal in `ℓ²`.** -/
theorem inner_hermiteContrastLp_eq_zero {m k : ℕ} (hmk : m ≠ k) :
    inner ℝ (hermiteContrastLp m) (hermiteContrastLp k) = 0 := by
  rw [inner_hermiteContrastLp]
  rcases lt_or_gt_of_ne hmk with h | h
  · exact constrainedProlateHermiteContrastPairing_eq_zero h
  · have hsymm : constrainedProlateHermiteContrastPairing m k
        = constrainedProlateHermiteContrastPairing k m := by
      rw [constrainedProlateHermiteContrastPairing, constrainedProlateHermiteContrastPairing,
        max_comm]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hsymm]
    exact constrainedProlateHermiteContrastPairing_eq_zero h

/-! ## Nonvanishing and normalization -/

/-- **No contrast vector vanishes.**  Its top coordinate is `S_k / a_{k+1}`, a ratio of a positive
square sum by a nonzero coordinate. -/
theorem hermiteContrastLp_ne_zero (k : ℕ) : hermiteContrastLp k ≠ 0 := by
  intro hz
  have hk1 : constrainedProlateHermiteContrast k (k + 1) = 0 := by
    have h := congrArg (fun v : lp (fun _ : ℕ => ℝ) 2 => (v : ℕ → ℝ) (k + 1)) hz
    simpa using h
  rw [constrainedProlateHermiteContrast_succ] at hk1
  have hSpos := constrainedProlateHermiteSquareSum_pos k
  have hane := constrainedProlateHermiteCoordinate_ne_zero (k + 1)
  rcases div_eq_zero_iff.mp hk1 with h | h
  · exact absurd h (ne_of_gt hSpos)
  · exact hane h

/-- The normalized contrast ladder. -/
def hermiteContrastUnit (k : ℕ) : lp (fun _ : ℕ => ℝ) 2 :=
  (‖hermiteContrastLp k‖)⁻¹ • hermiteContrastLp k

theorem norm_hermiteContrastUnit (k : ℕ) : ‖hermiteContrastUnit k‖ = 1 := by
  rw [hermiteContrastUnit, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hermiteContrastLp_ne_zero k))

/-- **The normalized Hermite contrast ladder is an orthonormal system in `ℓ²`.**  This is the
`ℓ²` form of the mutual orthogonality of the limiting ladder vectors. -/
theorem orthonormal_hermiteContrastUnit : Orthonormal ℝ hermiteContrastUnit := by
  constructor
  · intro k
    exact norm_hermiteContrastUnit k
  · intro m k hmk
    rw [hermiteContrastUnit, hermiteContrastUnit, real_inner_smul_left, real_inner_smul_right,
      inner_hermiteContrastLp_eq_zero hmk, mul_zero, mul_zero]

/-! ## The squared norm -/

/-- The squared norm of a contrast vector is its self-pairing. -/
theorem norm_sq_hermiteContrastLp (k : ℕ) :
    ‖hermiteContrastLp k‖ ^ (2 : ℕ) = constrainedProlateHermiteContrastPairing k k := by
  rw [← real_inner_self_eq_norm_sq, inner_hermiteContrastLp]


/-- The self-pairing splits into the head square sum and the top coordinate. -/
theorem constrainedProlateHermiteContrastPairing_self (k : ℕ) :
    constrainedProlateHermiteContrastPairing k k
      = constrainedProlateHermiteSquareSum k
        + constrainedProlateHermiteSquareSum k ^ (2 : ℕ)
          / constrainedProlateHermiteCoordinate (k + 1) ^ (2 : ℕ) := by
  rw [constrainedProlateHermiteContrastPairing, max_self,
    show k + 2 = (k + 1) + 1 from rfl, Finset.sum_range_succ]
  congr 1
  · rw [constrainedProlateHermiteSquareSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [constrainedProlateHermiteContrast_of_le (by omega)]
    ring
  · rw [constrainedProlateHermiteContrast_succ, ← sq, div_pow]

/-- **The exact squared norm of the depth-`k` contrast vector.**  In terms of the Hermite weights
it is `√2·Q_k·Q_{k+1}/q_{k+1}`, so the normalization required by the ladder limit is explicit. -/
theorem norm_sq_hermiteContrastLp_eq (k : ℕ) :
    ‖hermiteContrastLp k‖ ^ (2 : ℕ)
      = Real.sqrt 2 * constrainedProlateHermiteWeightSum k
          * constrainedProlateHermiteWeightSum (k + 1)
          / constrainedProlateHermiteWeight (k + 1) := by
  have hq : (0 : ℝ) < constrainedProlateHermiteWeight (k + 1) :=
    constrainedProlateHermiteWeight_pos _
  rw [norm_sq_hermiteContrastLp, constrainedProlateHermiteContrastPairing_self,
    constrainedProlateHermiteSquareSum_eq, constrainedProlateHermiteCoordinate_sq,
    constrainedProlateHermiteWeightSum_succ]
  field_simp
  ring_nf

/-! ## The raw CCM contrasts in `ℓ²`

The raw contrast `r_m = a_0 e_m - a_m e_0` is supported on two coordinates, so it too is a genuine
`ℓ²` vector.  Orthogonality of the spectral ladder to every preceding raw contrast is what makes
the ladder the Gram-Schmidt orthogonalization of the raw family rather than merely an orthogonal
system in its own right.
-/

theorem constrainedProlateRawHermiteContrast_eq_zero_of_notMem {m j : ℕ}
    (hj : j ∉ ({0, m} : Finset ℕ)) : constrainedProlateRawHermiteContrast m j = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  rw [constrainedProlateRawHermiteContrast, if_neg hj.2, if_neg hj.1]

theorem summable_constrainedProlateRawHermiteContrast_sq (m : ℕ) :
    Summable fun j => constrainedProlateRawHermiteContrast m j ^ (2 : ℕ) := by
  refine summable_of_ne_finset_zero (s := ({0, m} : Finset ℕ)) ?_
  intro j hj
  rw [constrainedProlateRawHermiteContrast_eq_zero_of_notMem hj]
  exact zero_pow two_ne_zero

theorem memℓp_constrainedProlateRawHermiteContrast (m : ℕ) :
    Memℓp (constrainedProlateRawHermiteContrast m) 2 :=
  memℓp_two_of_sq_summable (summable_constrainedProlateRawHermiteContrast_sq m)

/-- The raw CCM Hermite contrast as an element of `ℓ²`. -/
def rawHermiteContrastLp (m : ℕ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨constrainedProlateRawHermiteContrast m, memℓp_constrainedProlateRawHermiteContrast m⟩

@[simp] theorem rawHermiteContrastLp_coeFn (m : ℕ) :
    ((rawHermiteContrastLp m : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ)
      = constrainedProlateRawHermiteContrast m := rfl

theorem inner_hermiteContrastLp_raw (k m : ℕ) :
    inner ℝ (hermiteContrastLp k) (rawHermiteContrastLp m)
      = ∑ j ∈ Finset.range (k + 2),
          constrainedProlateHermiteContrast k j * constrainedProlateRawHermiteContrast m j := by
  rw [lp_inner_eq_tsum_mul]
  refine tsum_eq_sum ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have hm : constrainedProlateHermiteContrast k j = 0 :=
    constrainedProlateHermiteContrast_eq_zero_of_succ_lt (by omega)
  simp [hermiteContrastLp_coeFn, rawHermiteContrastLp_coeFn, hm]

/-- **The spectral ladder is orthogonal in `ℓ²` to every preceding raw CCM contrast.**  With the
mutual orthogonality of the ladder itself, this exhibits the ladder as the Gram-Schmidt
orthogonalization of the raw Hermite contrasts. -/
theorem inner_hermiteContrastLp_rawHermiteContrastLp_eq_zero {k m : ℕ}
    (hm0 : 0 < m) (hmk : m ≤ k) :
    inner ℝ (hermiteContrastLp k) (rawHermiteContrastLp m) = 0 := by
  rw [inner_hermiteContrastLp_raw]
  exact constrainedProlateHermiteContrast_raw_orthogonal hm0 hmk

/-! ## The ladder direction is pinned

Orthogonality to the constraint together with orthogonality to the preceding raw contrasts
determines the depth-`k` direction completely, not merely up to a `(k+1)`-dimensional freedom.
The raw conditions force the first `k+1` coordinates to be proportional to `(a_0, ..., a_k)`, and
the constraint then fixes the top coordinate.  So the ladder vector is the unique such direction
up to scale — the pinning that the eigenvector limit must reproduce.
-/

theorem sum_mul_rawHermiteContrast {k m : ℕ} (hm0 : 0 < m) (hmk : m ≤ k) (x : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k + 2), x j * constrainedProlateRawHermiteContrast m j)
      = x m * constrainedProlateHermiteCoordinate 0
        - x 0 * constrainedProlateHermiteCoordinate m := by
  have hsplit : ∀ j : ℕ, x j * constrainedProlateRawHermiteContrast m j
      = (if j = m then x j * constrainedProlateHermiteCoordinate 0 else 0)
        + (if j = 0 then -(x j * constrainedProlateHermiteCoordinate m) else 0) := by
    intro j
    rw [constrainedProlateRawHermiteContrast]
    rcases eq_or_ne j m with rfl | hjm
    · rw [if_pos rfl, if_pos rfl, if_neg (by omega : ¬ j = 0)]
      ring
    · rw [if_neg hjm, if_neg hjm]
      rcases eq_or_ne j 0 with rfl | hj0
      · rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg hj0, if_neg hj0]
        ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (k + 2)) m
      (fun j => x j * constrainedProlateHermiteCoordinate 0),
    Finset.sum_ite_eq' (Finset.range (k + 2)) 0
      (fun j => -(x j * constrainedProlateHermiteCoordinate m)),
    if_pos (by simp only [Finset.mem_range]; omega),
    if_pos (by simp only [Finset.mem_range]; omega)]
  ring

/-- **The ladder direction is unique.**  Any vector supported on the first `k + 2` coordinates that
is orthogonal to the constraint and to every preceding raw contrast is a scalar multiple of the
depth-`k` ladder vector. -/
theorem eq_smul_constrainedProlateHermiteContrast_of_orthogonal {k : ℕ} (x : ℕ → ℝ)
    (hsupp : ∀ j, k + 1 < j → x j = 0)
    (hconstraint :
      (∑ j ∈ Finset.range (k + 2), x j * constrainedProlateHermiteCoordinate j) = 0)
    (hraw : ∀ m, 0 < m → m ≤ k →
      (∑ j ∈ Finset.range (k + 2), x j * constrainedProlateRawHermiteContrast m j) = 0) :
    ∀ j, x j = (-(x 0) / constrainedProlateHermiteCoordinate 0)
      * constrainedProlateHermiteContrast k j := by
  have ha0 : constrainedProlateHermiteCoordinate 0 ≠ 0 :=
    constrainedProlateHermiteCoordinate_ne_zero 0
  have hhead : ∀ m, m ≤ k → x m * constrainedProlateHermiteCoordinate 0
      = x 0 * constrainedProlateHermiteCoordinate m := by
    intro m hmk
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · ring
    · have hr := hraw m hm0 hmk
      rw [sum_mul_rawHermiteContrast hm0 hmk] at hr
      linarith
  have htop : x (k + 1) * constrainedProlateHermiteCoordinate (k + 1)
      * constrainedProlateHermiteCoordinate 0
      = -(x 0 * constrainedProlateHermiteSquareSum k) := by
    have hsum : (∑ j ∈ Finset.range (k + 1),
        x j * constrainedProlateHermiteCoordinate j) * constrainedProlateHermiteCoordinate 0
        = x 0 * constrainedProlateHermiteSquareSum k := by
      rw [Finset.sum_mul, constrainedProlateHermiteSquareSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hh := hhead j (by omega)
      linear_combination constrainedProlateHermiteCoordinate j * hh
    rw [show k + 2 = (k + 1) + 1 from rfl, Finset.sum_range_succ] at hconstraint
    linear_combination constrainedProlateHermiteCoordinate 0 * hconstraint - hsum
  intro j
  rcases le_or_gt j k with hjk | hjk
  · rw [constrainedProlateHermiteContrast_of_le hjk]
    have hh := hhead j hjk
    field_simp
    linear_combination hh
  · rcases eq_or_ne j (k + 1) with rfl | hne
    · rw [constrainedProlateHermiteContrast_succ]
      have ha1 : constrainedProlateHermiteCoordinate (k + 1) ≠ 0 :=
        constrainedProlateHermiteCoordinate_ne_zero (k + 1)
      field_simp
      linear_combination htop
    · have hgt : k + 1 < j := by omega
      rw [hsupp j hgt, constrainedProlateHermiteContrast_eq_zero_of_succ_lt hgt, mul_zero]

/-! ## The pinning in `ℓ²`, up to sign

The card states the limit as "the unique unit vector up to sign" in the constrained head space.
That is exactly what the pinning gives once it is transported to `ℓ²` and combined with
normalization.
-/

theorem inner_rawHermiteContrastLp_eq_sum {k : ℕ} (v : lp (fun _ : ℕ => ℝ) 2) (m : ℕ)
    (hsupp : ∀ j, k + 1 < j → (v : ℕ → ℝ) j = 0) :
    inner ℝ v (rawHermiteContrastLp m)
      = ∑ j ∈ Finset.range (k + 2),
          (v : ℕ → ℝ) j * constrainedProlateRawHermiteContrast m j := by
  rw [lp_inner_eq_tsum_mul]
  refine tsum_eq_sum ?_
  intro j hj
  rw [Finset.mem_range] at hj
  rw [hsupp j (by omega), zero_mul]

/-- **The pinning, in `ℓ²`.**  A vector of `ℓ²` supported on the first `k+2` coordinates and
orthogonal to the constraint and to every preceding raw contrast is a multiple of the ladder
vector. -/
theorem eq_smul_hermiteContrastLp_of_orthogonal {k : ℕ} (v : lp (fun _ : ℕ => ℝ) 2)
    (hsupp : ∀ j, k + 1 < j → (v : ℕ → ℝ) j = 0)
    (hconstraint :
      (∑ j ∈ Finset.range (k + 2),
        (v : ℕ → ℝ) j * constrainedProlateHermiteCoordinate j) = 0)
    (hraw : ∀ m, 0 < m → m ≤ k → inner ℝ v (rawHermiteContrastLp m) = 0) :
    v = (-((v : ℕ → ℝ) 0) / constrainedProlateHermiteCoordinate 0) • hermiteContrastLp k := by
  have hraw' : ∀ m, 0 < m → m ≤ k →
      (∑ j ∈ Finset.range (k + 2),
        (v : ℕ → ℝ) j * constrainedProlateRawHermiteContrast m j) = 0 := by
    intro m hm0 hmk
    rw [← inner_rawHermiteContrastLp_eq_sum v m hsupp]
    exact hraw m hm0 hmk
  have hpt := eq_smul_constrainedProlateHermiteContrast_of_orthogonal
    (v : ℕ → ℝ) hsupp hconstraint hraw'
  refine lp.ext ?_
  funext j
  rw [hpt j]
  rfl

/-- **The unit ladder vector is unique up to sign.**  This is the card's description of the limit
object made precise in `ℓ²`. -/
theorem eq_pm_hermiteContrastUnit_of_orthogonal {k : ℕ} (v : lp (fun _ : ℕ => ℝ) 2)
    (hsupp : ∀ j, k + 1 < j → (v : ℕ → ℝ) j = 0)
    (hconstraint :
      (∑ j ∈ Finset.range (k + 2),
        (v : ℕ → ℝ) j * constrainedProlateHermiteCoordinate j) = 0)
    (hraw : ∀ m, 0 < m → m ≤ k → inner ℝ v (rawHermiteContrastLp m) = 0)
    (hnorm : ‖v‖ = 1) :
    v = hermiteContrastUnit k ∨ v = -hermiteContrastUnit k := by
  set c : ℝ := -((v : ℕ → ℝ) 0) / constrainedProlateHermiteCoordinate 0 with hc
  have hv := eq_smul_hermiteContrastLp_of_orthogonal v hsupp hconstraint hraw
  have hW : (0 : ℝ) < ‖hermiteContrastLp k‖ :=
    norm_pos_iff.mpr (hermiteContrastLp_ne_zero k)
  have habs : |c| * ‖hermiteContrastLp k‖ = 1 := by
    rw [← Real.norm_eq_abs, ← norm_smul, ← hv, hnorm]
  have hcases : c = (‖hermiteContrastLp k‖)⁻¹ ∨ c = -(‖hermiteContrastLp k‖)⁻¹ := by
    rcases abs_cases c with ⟨h1, _⟩ | ⟨h1, _⟩
    · left
      rw [h1] at habs
      field_simp at habs ⊢
      linarith [habs]
    · right
      rw [h1] at habs
      field_simp at habs ⊢
      linarith [habs]
  rcases hcases with h | h
  · left
    rw [hv, ← hc, h, hermiteContrastUnit]
  · right
    rw [hv, ← hc, h, hermiteContrastUnit, neg_smul]

/-! ## The pinning is quantitative

The uniqueness argument is an exact computation, so it survives perturbation without any
compactness or continuity step: each coordinate deviation of `x` from the ladder direction is
*exactly* the corresponding orthogonality defect, rescaled.  A convergence proof therefore only has
to drive the defects to zero.
-/

theorem sub_smul_hermiteContrast_head_mul {k m : ℕ} (hm : m ≤ k) (x : ℕ → ℝ) :
    (x m - (-(x 0) / constrainedProlateHermiteCoordinate 0)
        * constrainedProlateHermiteContrast k m) * constrainedProlateHermiteCoordinate 0
      = x m * constrainedProlateHermiteCoordinate 0
        - x 0 * constrainedProlateHermiteCoordinate m := by
  have ha0 : constrainedProlateHermiteCoordinate 0 ≠ 0 :=
    constrainedProlateHermiteCoordinate_ne_zero 0
  rw [constrainedProlateHermiteContrast_of_le hm]
  field_simp

/-- **The head deviation is exactly the raw defect.**  For `0 < m ≤ k` the `m`-th coordinate of
`x` differs from the ladder direction by precisely `⟨x, r_m⟩ / a_0`. -/
theorem sub_smul_hermiteContrast_head_eq_raw {k m : ℕ} (hm0 : 0 < m) (hmk : m ≤ k) (x : ℕ → ℝ) :
    (x m - (-(x 0) / constrainedProlateHermiteCoordinate 0)
        * constrainedProlateHermiteContrast k m) * constrainedProlateHermiteCoordinate 0
      = ∑ j ∈ Finset.range (k + 2), x j * constrainedProlateRawHermiteContrast m j := by
  rw [sub_smul_hermiteContrast_head_mul hmk x, sum_mul_rawHermiteContrast hm0 hmk]

/-- **The top deviation is exactly the constraint defect corrected by the raw defects.** -/
theorem sub_smul_hermiteContrast_top_mul {k : ℕ} (x : ℕ → ℝ) :
    (x (k + 1) - (-(x 0) / constrainedProlateHermiteCoordinate 0)
        * constrainedProlateHermiteContrast k (k + 1))
      * constrainedProlateHermiteCoordinate (k + 1)
      * constrainedProlateHermiteCoordinate 0
      = (∑ j ∈ Finset.range (k + 2), x j * constrainedProlateHermiteCoordinate j)
          * constrainedProlateHermiteCoordinate 0
        - ∑ j ∈ Finset.range (k + 1),
            (x j * constrainedProlateHermiteCoordinate 0
              - x 0 * constrainedProlateHermiteCoordinate j)
            * constrainedProlateHermiteCoordinate j := by
  have ha0 : constrainedProlateHermiteCoordinate 0 ≠ 0 :=
    constrainedProlateHermiteCoordinate_ne_zero 0
  have ha1 : constrainedProlateHermiteCoordinate (k + 1) ≠ 0 :=
    constrainedProlateHermiteCoordinate_ne_zero (k + 1)
  have hexpand : ∑ j ∈ Finset.range (k + 1),
      (x j * constrainedProlateHermiteCoordinate 0
        - x 0 * constrainedProlateHermiteCoordinate j)
      * constrainedProlateHermiteCoordinate j
      = (∑ j ∈ Finset.range (k + 1), x j * constrainedProlateHermiteCoordinate j)
          * constrainedProlateHermiteCoordinate 0
        - x 0 * constrainedProlateHermiteSquareSum k := by
    rw [Finset.sum_mul, constrainedProlateHermiteSquareSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexpand, constrainedProlateHermiteContrast_succ,
    show k + 2 = (k + 1) + 1 from rfl, Finset.sum_range_succ]
  field_simp
  ring

end RHTower

end
