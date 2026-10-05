import GaloisForLFunctions.HTGeometry.HardyShiftCommutant
import GaloisForLFunctions.HTGeometry.HardyDiskModelSpace


/-!
# Beurling's theorem for the shift on `H²(𝔻)`

Every closed subspace `M ≠ 0` of coefficient `H²(𝔻)` invariant under the unilateral shift `S` is
`θ H²` for a bounded analytic `θ` whose multiplication operator is an isometry
(`exists_inner_multiplier_of_shiftInvariant`).

**Proof (wandering subspace).**  `L = M ⊖ S M` is nonzero (otherwise every `x ∈ M` lies in every
`Sⁿ H²`) and at most one-dimensional: two orthogonal unit vectors of `L` would give an orthonormal
family `{Sⁿφ} ∪ {Sⁿψ}` whose Bessel sums against `e_k` exhaust `‖φ‖² + ‖ψ‖² = 2`
(`wandering_eq_zero_of_inner_eq_zero`).  A unit `φ ∈ L` has orthonormal shifts, so Bessel against the
Szegő kernel gives `|φ(z)| ≤ 1` (`norm_hardyFun_wandering_le_one`); multiplication by `φ` sends the
monomials to the orthonormal `Sⁿφ`, hence is an isometry, and its range is `M` because a vector of
`M` orthogonal to every `Sⁿφ` lies in `⋂ Sⁿ H² = 0`.
-/

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The unilateral shift on coefficients -/

/-- The unilateral shift `S` on `H²(𝔻)`. -/
abbrev hardyShift : HardyDisk →L[ℂ] HardyDisk := hardyMul diskShift

theorem memℓp_shiftCoeff (x : HardyDisk) :
    Memℓp (fun n : ℕ => if n = 0 then (0 : ℂ) else x (n - 1)) 2 := by
  have hx : Summable fun n : ℕ => ‖x n‖ ^ (2 : ℝ) := by
    have := (lp.memℓp x).summable (by norm_num : (0 : ENNReal).toReal < (2 : ENNReal).toReal)
    simpa using this
  refine memℓp_gen ?_
  have h : (fun n : ℕ => ‖(if n = 0 then (0 : ℂ) else x (n - 1))‖ ^ (2 : ENNReal).toReal) =
      fun n => if n = 0 then 0 else ‖x (n - 1)‖ ^ (2 : ℝ) := by
    funext n; split_ifs <;> simp
  rw [h]
  refine (summable_nat_add_iff 1).mp ?_
  simpa using hx

/-- The shifted coefficient sequence `(0, x₀, x₁, …)`. -/
def hardyShiftSeq (x : HardyDisk) : HardyDisk := ⟨_, memℓp_shiftCoeff x⟩

theorem shiftSeq_apply (x : HardyDisk) (n : ℕ) :
    hardyShiftSeq x n = if n = 0 then 0 else x (n - 1) := rfl

theorem hardyFun_shiftSeq (x : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (hardyShiftSeq x) z = z * hardyFun x z := by
  unfold hardyFun
  rw [(summable_hardyDisk_terms (hardyShiftSeq x) hz).tsum_eq_zero_add]
  simp only [shiftSeq_apply, if_pos, pow_zero, mul_one, zero_add, Nat.succ_ne_zero, if_false,
    Nat.add_sub_cancel]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem hardyShift_eq_shiftSeq (x : HardyDisk) : hardyShift x = hardyShiftSeq x := by
  refine hardyDisk_ext fun z hz => ?_
  rw [hardyFun_hardyMul diskShift x hz, hardyFun_shiftSeq x hz]
  rfl

theorem hardyShift_apply_zero (x : HardyDisk) : hardyShift x 0 = 0 := by
  rw [hardyShift_eq_shiftSeq, shiftSeq_apply, if_pos rfl]

theorem hardyShift_apply_succ (x : HardyDisk) (n : ℕ) : hardyShift x (n + 1) = x n := by
  rw [hardyShift_eq_shiftSeq, shiftSeq_apply, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]

theorem norm_hardyShift (x : HardyDisk) : ‖hardyShift x‖ = ‖x‖ := by
  have h2 : ‖hardyShift x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [hardyDisk_norm_sq, hardyDisk_norm_sq]
    have hs : Summable fun n => ‖hardyShift x n‖ ^ 2 := by
      have := (lp.memℓp (hardyShift x)).summable
        (by norm_num : (0 : ENNReal).toReal < (2 : ENNReal).toReal)
      simpa using this
    rw [hs.tsum_eq_zero_add]
    simp only [hardyShift_apply_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add, hardyShift_apply_succ]
  have h0 := norm_nonneg (hardyShift x)
  have h1 := norm_nonneg x
  nlinarith [sq_nonneg (‖hardyShift x‖ - ‖x‖), sq_nonneg (‖hardyShift x‖ + ‖x‖)]

theorem inner_hardyShift (x y : HardyDisk) :
    inner ℂ (hardyShift x) (hardyShift y) = inner ℂ x y := by
  have hiso : ∀ v, ‖hardyShift v‖ = ‖v‖ := norm_hardyShift
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ), inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)]
  simp only [← map_add, ← map_sub, ← map_smul, hiso]

theorem hardyShift_pow_succ_apply (n : ℕ) (x : HardyDisk) :
    (hardyShift ^ (n + 1)) x = hardyShift ((hardyShift ^ n) x) := by
  rw [pow_succ']; rfl

theorem hardyShift_pow_add_apply (a b : ℕ) (x : HardyDisk) :
    (hardyShift ^ (a + b)) x = (hardyShift ^ a) ((hardyShift ^ b) x) := by
  rw [pow_add]; rfl

theorem hardyShift_pow_apply (n : ℕ) (x : HardyDisk) (k : ℕ) :
    (hardyShift ^ n) x k = if k < n then 0 else x (k - n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [hardyShift_pow_succ_apply]
    rcases k with _ | k
    · rw [hardyShift_apply_zero, if_pos (Nat.succ_pos n)]
    · rw [hardyShift_apply_succ, ih]
      by_cases h : k < n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega), show k + 1 - (n + 1) = k - n by omega]

theorem eq_zero_of_forall_mem_range_shift_pow {x : HardyDisk}
    (h : ∀ n : ℕ, ∃ y : HardyDisk, x = (hardyShift ^ n) y) : x = 0 := by
  refine lp.ext (funext fun k => ?_)
  obtain ⟨y, hy⟩ := h (k + 1)
  rw [hy, hardyShift_pow_apply, if_pos (Nat.lt_succ_self k)]
  rfl

theorem norm_hardyShift_pow (n : ℕ) (x : HardyDisk) : ‖(hardyShift ^ n) x‖ = ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [hardyShift_pow_succ_apply, norm_hardyShift, ih]

theorem inner_hardyShift_pow (n : ℕ) (x y : HardyDisk) :
    inner ℂ ((hardyShift ^ n) x) ((hardyShift ^ n) y) = inner ℂ x y := by
  induction n with
  | zero => simp
  | succ n ih => rw [hardyShift_pow_succ_apply, hardyShift_pow_succ_apply, inner_hardyShift, ih]

/-! ## The wandering subspace of a shift-invariant subspace -/

theorem isometry_hardyShift : Isometry hardyShift :=
  AddMonoidHomClass.isometry_of_norm hardyShift norm_hardyShift

/-- The image `S M` of a subspace under the shift. -/
def shiftImage (M : Submodule ℂ HardyDisk) : Submodule ℂ HardyDisk :=
  M.map (hardyShift : HardyDisk →ₗ[ℂ] HardyDisk)

theorem isClosed_shiftImage {M : Submodule ℂ HardyDisk} (hMc : IsClosed (M : Set HardyDisk)) :
    IsClosed (shiftImage M : Set HardyDisk) := by
  have h := isometry_hardyShift.isClosedEmbedding.isClosedMap _ hMc
  simpa [shiftImage] using h

theorem hardyShift_pow_mem {M : Submodule ℂ HardyDisk} (hinv : ∀ x ∈ M, hardyShift x ∈ M)
    {x : HardyDisk} (hx : x ∈ M) (n : ℕ) : (hardyShift ^ n) x ∈ M := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [hardyShift_pow_succ_apply]; exact hinv _ ih

/-- **The wandering decomposition.**  Every `x ∈ M` is `y + S x'` with `y ∈ M ⊖ S M`, `x' ∈ M`. -/
theorem exists_wandering_decomp {M : Submodule ℂ HardyDisk} (hMc : IsClosed (M : Set HardyDisk))
    (hinv : ∀ x ∈ M, hardyShift x ∈ M) {x : HardyDisk} (hx : x ∈ M) :
    ∃ y x' : HardyDisk, y ∈ M ∧ y ∈ (shiftImage M)ᗮ ∧ x' ∈ M ∧ x = y + hardyShift x' := by
  haveI : CompleteSpace (shiftImage M) := (isClosed_shiftImage hMc).completeSpace_coe
  haveI := Submodule.HasOrthogonalProjection.ofCompleteSpace (shiftImage M)
  set P := (shiftImage M).starProjection
  have hP := (shiftImage M).starProjection_apply_mem x
  obtain ⟨x', hx', hPx⟩ := Submodule.mem_map.mp hP
  refine ⟨x - P x, x', ?_, Submodule.sub_starProjection_mem_orthogonal x, hx', ?_⟩
  · refine M.sub_mem hx ?_
    rw [← hPx]; exact hinv x' hx'
  · rw [← hPx]; simp

/-- If the wandering subspace is trivial, so is `M`. -/
theorem eq_bot_of_wandering_eq_zero {M : Submodule ℂ HardyDisk}
    (hMc : IsClosed (M : Set HardyDisk)) (hinv : ∀ x ∈ M, hardyShift x ∈ M)
    (h : ∀ y ∈ M, y ∈ (shiftImage M)ᗮ → y = 0) : M = ⊥ := by
  refine (Submodule.eq_bot_iff M).mpr fun x hx => ?_
  have key : ∀ n : ℕ, ∃ y ∈ M, x = (hardyShift ^ n) y := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, by simp⟩
    | succ n ih =>
      obtain ⟨y, hyM, rfl⟩ := ih
      obtain ⟨w, y', hwM, hwo, hy'M, hdec⟩ := exists_wandering_decomp hMc hinv hyM
      rw [h w hwM hwo, zero_add] at hdec
      refine ⟨y', hy'M, ?_⟩
      rw [hdec, pow_succ]; rfl
  exact eq_zero_of_forall_mem_range_shift_pow fun n => by
    obtain ⟨y, -, hy⟩ := key n; exact ⟨y, hy⟩

/-- Shifts of wandering vectors are orthogonal. -/
theorem inner_hardyShift_pow_wandering {M : Submodule ℂ HardyDisk}
    (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ ψ : HardyDisk} (hφ : φ ∈ M)
    (hφo : φ ∈ (shiftImage M)ᗮ) (hψ : ψ ∈ M) (hψo : ψ ∈ (shiftImage M)ᗮ) (m n : ℕ) :
    inner ℂ ((hardyShift ^ m) φ) ((hardyShift ^ n) ψ) = if m = n then inner ℂ φ ψ else 0 := by
  rcases lt_trichotomy m n with hmn | rfl | hmn
  · rw [if_neg hmn.ne]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [show m + k + 1 = m + (k + 1) by ring, hardyShift_pow_add_apply, inner_hardyShift_pow,
      hardyShift_pow_succ_apply]
    exact Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_map.mpr ⟨_, hardyShift_pow_mem hinv hψ k, rfl⟩) hφo
  · rw [if_pos rfl, inner_hardyShift_pow]
  · rw [if_neg hmn.ne']
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [show n + k + 1 = n + (k + 1) by ring, hardyShift_pow_add_apply, inner_hardyShift_pow,
      hardyShift_pow_succ_apply]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_map.mpr ⟨_, hardyShift_pow_mem hinv hφ k, rfl⟩) hψo

theorem inner_hardyShift_pow_single (n : ℕ) (x : HardyDisk) (k : ℕ) (hnk : n ≤ k) :
    ‖inner ℂ ((hardyShift ^ n) x) (lp.single 2 k (1 : ℂ) : HardyDisk)‖ = ‖x (k - n)‖ := by
  rw [lp.inner_single_right, hardyShift_pow_apply, if_neg (by omega)]
  simp

/-- **The wandering subspace is at most a line.**  Two orthogonal wandering vectors cannot both be
nonzero: their shifts form an orthonormal family whose Bessel sums against `e_k` exhaust both
norms. -/
theorem wandering_eq_zero_of_inner_eq_zero {M : Submodule ℂ HardyDisk}
    (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ ψ : HardyDisk} (hφ : φ ∈ M)
    (hφo : φ ∈ (shiftImage M)ᗮ) (hψ : ψ ∈ M) (hψo : ψ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1)
    (hφψ : inner ℂ φ ψ = 0) : ψ = 0 := by
  classical
  by_contra hψ0
  have hψn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ0
  set ψ' : HardyDisk := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ with hψ'
  have hψ'n : ‖ψ'‖ = 1 := by
    rw [hψ', norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ hψn]
  have hψ'M : ψ' ∈ M := M.smul_mem _ hψ
  have hψ'o : ψ' ∈ (shiftImage M)ᗮ := (shiftImage M)ᗮ.smul_mem _ hψo
  have hφψ' : inner ℂ φ ψ' = 0 := by rw [hψ', inner_smul_right, hφψ, mul_zero]
  have hψ'φ : inner ℂ ψ' φ = 0 := by rw [← inner_conj_symm, hφψ', map_zero]
  set v : ℕ ⊕ ℕ → HardyDisk :=
    Sum.elim (fun n => (hardyShift ^ n) φ) (fun n => (hardyShift ^ n) ψ') with hv
  have hφφ : inner ℂ φ φ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφn]; simp
  have hψψ : inner ℂ ψ' ψ' = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ'n]; simp
  have hon : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    rintro (m | m) (n | n)
    · simp only [hv, Sum.elim_inl, Sum.inl.injEq]
      rw [inner_hardyShift_pow_wandering hinv hφ hφo hφ hφo, hφφ]
    · simp only [hv, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [inner_hardyShift_pow_wandering hinv hφ hφo hψ'M hψ'o, hφψ']
      simp
    · simp only [hv, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [inner_hardyShift_pow_wandering hinv hψ'M hψ'o hφ hφo, hψ'φ]
      simp
    · simp only [hv, Sum.elim_inr, Sum.inr.injEq]
      rw [inner_hardyShift_pow_wandering hinv hψ'M hψ'o hψ'M hψ'o, hψψ]
  -- Bessel against `e_k`
  have hbessel : ∀ k : ℕ, ∑ j ∈ Finset.range (k + 1), (‖φ j‖ ^ 2 + ‖ψ' j‖ ^ 2) ≤ 1 := by
    intro k
    have h := hon.sum_inner_products_le (lp.single 2 k (1 : ℂ) : HardyDisk)
      (s := (Finset.range (k + 1)).disjSum (Finset.range (k + 1)))
    rw [lp.norm_single (by norm_num), norm_one, one_pow, Finset.sum_disjSum] at h
    simp only [hv, Sum.elim_inl, Sum.elim_inr] at h
    have hre : ∀ x : HardyDisk, ∑ n ∈ Finset.range (k + 1),
        ‖inner ℂ ((hardyShift ^ n) x) (lp.single 2 k (1 : ℂ) : HardyDisk)‖ ^ 2 =
        ∑ j ∈ Finset.range (k + 1), ‖x j‖ ^ 2 := by
      intro x
      rw [Finset.sum_congr rfl fun n hn => by
        rw [inner_hardyShift_pow_single n x k (by simp at hn; omega)]]
      have := Finset.sum_range_reflect (fun j => ‖x j‖ ^ 2) (k + 1)
      simpa [Nat.add_sub_cancel] using this
    rw [hre, hre] at h
    rw [Finset.sum_add_distrib]
    exact h
  have hsum : ∑' j, (‖φ j‖ ^ 2 + ‖ψ' j‖ ^ 2) ≤ 1 := by
    refine Real.tsum_le_of_sum_range_le (fun j => by positivity) fun n => ?_
    rcases n with _ | k
    · simp
    · exact hbessel k
  have hsφ : Summable fun j => ‖φ j‖ ^ 2 := by
    have := (lp.memℓp φ).summable (by norm_num : (0 : ENNReal).toReal < (2 : ENNReal).toReal)
    simpa using this
  have hsψ : Summable fun j => ‖ψ' j‖ ^ 2 := by
    have := (lp.memℓp ψ').summable (by norm_num : (0 : ENNReal).toReal < (2 : ENNReal).toReal)
    simpa using this
  rw [hsφ.tsum_add hsψ, ← hardyDisk_norm_sq, ← hardyDisk_norm_sq, hφn, hψ'n] at hsum
  norm_num at hsum

/-! ## The wandering vector is an inner function -/

theorem orthonormal_hardyShift_pow_wandering {M : Submodule ℂ HardyDisk}
    (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ : HardyDisk} (hφ : φ ∈ M)
    (hφo : φ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1) :
    Orthonormal ℂ (fun n : ℕ => (hardyShift ^ n) φ) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [inner_hardyShift_pow_wandering hinv hφ hφo hφ hφo, inner_self_eq_norm_sq_to_K, hφn]
  simp

/-- **The wandering vector is bounded by one on the disc.**  Bessel's inequality for the
orthonormal shifts `Sⁿφ` against the Szegő kernel `k_z` gives
`|φ(z)|²/(1 − |z|²) ≤ 1/(1 − |z|²)`. -/
theorem norm_hardyFun_wandering_le_one {M : Submodule ℂ HardyDisk}
    (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ : HardyDisk} (hφ : φ ∈ M)
    (hφo : φ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖hardyFun φ z‖ ≤ 1 := by
  have hon := orthonormal_hardyShift_pow_wandering hinv hφ hφo hφn
  set k := hardyKernel hz
  have hterm : ∀ n : ℕ, ‖inner ℂ ((hardyShift ^ n) φ) k‖ ^ 2 =
      (‖z‖ ^ 2) ^ n * ‖hardyFun φ z‖ ^ 2 := by
    intro n
    rw [← inner_conj_symm, RCLike.norm_conj, inner_hardyKernel hz, hardyFun_shift_pow n φ hz,
      norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hgeom := hasSum_geometric_of_lt_one (sq_nonneg ‖z‖) hz2
  have hpartial : ∀ K : ℕ, ∑ n ∈ Finset.range K, (‖z‖ ^ 2) ^ n * ‖hardyFun φ z‖ ^ 2 ≤
      (1 - ‖z‖ ^ 2)⁻¹ := by
    intro K
    have h := hon.sum_inner_products_le k (s := Finset.range K)
    rw [norm_sq_hardyKernel hz] at h
    simpa only [hterm] using h
  have htsum : (∑' n : ℕ, (‖z‖ ^ 2) ^ n * ‖hardyFun φ z‖ ^ 2) ≤ (1 - ‖z‖ ^ 2)⁻¹ :=
    Real.tsum_le_of_sum_range_le (fun n => by positivity) hpartial
  rw [tsum_mul_right, hgeom.tsum_eq] at htsum
  have hpos : 0 < (1 - ‖z‖ ^ 2)⁻¹ := inv_pos.mpr (by linarith)
  have h2 : ‖hardyFun φ z‖ ^ 2 ≤ 1 := by
    rw [mul_comm] at htsum
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon hpos
    linarith
  nlinarith [norm_nonneg (hardyFun φ z)]

/-- The bounded analytic function of a unit wandering vector. -/
def wanderingMultiplier {M : Submodule ℂ HardyDisk} (hinv : ∀ x ∈ M, hardyShift x ∈ M)
    {φ : HardyDisk} (hφ : φ ∈ M) (hφo : φ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1) :
    DiskMultiplier where
  fn := hardyFun φ
  diff := differentiableOn_hardyFun φ
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => norm_hardyFun_wandering_le_one hinv hφ hφo hφn
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)

theorem hardyMul_wanderingMultiplier_shift_pow {M : Submodule ℂ HardyDisk}
    (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ : HardyDisk} (hφ : φ ∈ M)
    (hφo : φ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1) (n : ℕ) :
    hardyMul (wanderingMultiplier hinv hφ hφo hφn) ((hardyShift ^ n) hardyOne) =
      (hardyShift ^ n) φ := by
  refine hardyDisk_ext fun z hz => ?_
  rw [hardyFun_hardyMul _ _ hz, hardyFun_shift_pow n hardyOne hz, hardyFun_hardyOne hz,
    hardyFun_shift_pow n φ hz]
  show hardyFun φ z * (z ^ n * 1) = z ^ n * hardyFun φ z
  ring

theorem orthonormal_hardyShift_pow_hardyOne :
    Orthonormal ℂ (fun n : ℕ => (hardyShift ^ n) hardyOne) := by
  rw [orthonormal_iff_ite]
  intro m n
  simp only [hardyShift]
  rw [shift_pow_hardyOne, shift_pow_hardyOne, lp.inner_single_left]
  by_cases h : m = n
  · subst h; simp
  · rw [if_neg h, lp.single_apply, Pi.single_apply]
    simp [h]

/-- **Multiplication by the wandering vector is an isometry.** -/
theorem norm_hardyMul_wanderingMultiplier {M : Submodule ℂ HardyDisk}
    (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ : HardyDisk} (hφ : φ ∈ M)
    (hφo : φ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1) (x : HardyDisk) :
    ‖hardyMul (wanderingMultiplier hinv hφ hφo hφn) x‖ = ‖x‖ := by
  set T := hardyMul (wanderingMultiplier hinv hφ hφo hφn)
  have hon := orthonormal_hardyShift_pow_wandering hinv hφ hφo hφn
  have hon1 := orthonormal_hardyShift_pow_hardyOne
  have hbase : ∀ m n : ℕ, inner ℂ (T ((hardyShift ^ m) hardyOne)) (T ((hardyShift ^ n) hardyOne)) =
      inner ℂ ((hardyShift ^ m) hardyOne) ((hardyShift ^ n) hardyOne) := by
    intro m n
    rw [hardyMul_wanderingMultiplier_shift_pow, hardyMul_wanderingMultiplier_shift_pow,
      orthonormal_iff_ite.mp hon, orthonormal_iff_ite.mp hon1]
  set P := polyMultiples hardyOne
  have hinner : ∀ x ∈ P, ∀ y ∈ P, inner ℂ (T x) (T y) = inner ℂ x y := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨m, rfl⟩ := ha
      induction hy using Submodule.span_induction with
      | mem b hb => obtain ⟨n, rfl⟩ := hb; exact hbase m n
      | zero => simp
      | add b c _ _ hb hc => rw [map_add, inner_add_right, inner_add_right, hb, hc]
      | smul c b _ hb => rw [map_smul, inner_smul_right, inner_smul_right, hb]
    | zero => simp
    | add a c _ _ ha hc => rw [map_add, inner_add_left, inner_add_left, ha, hc]
    | smul c a _ ha => rw [map_smul, inner_smul_left, inner_smul_left, ha]
  have hnormP : ∀ x ∈ P, ‖T x‖ = ‖x‖ := by
    intro x hx
    have h := hinner x hx x hx
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖T x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg (T x), norm_nonneg x, sq_nonneg (‖T x‖ - ‖x‖),
      sq_nonneg (‖T x‖ + ‖x‖)]
  have hclosed : IsClosed {x : HardyDisk | ‖T x‖ = ‖x‖} :=
    isClosed_eq (T.continuous.norm) continuous_norm
  have hsub : (P : Set HardyDisk) ⊆ {x | ‖T x‖ = ‖x‖} := fun x hx => hnormP x hx
  have hcl := closure_minimal hsub hclosed
  have htop : x ∈ closure (P : Set HardyDisk) := by
    rw [← Submodule.topologicalClosure_coe]
    have h : P.topologicalClosure = ⊤ := cyclicSubspace_hardyOne
    rw [h]; exact Submodule.mem_top
  exact hcl htop

/-! ## Beurling's theorem -/

/-- A vector of `M` orthogonal to every shift of a unit wandering vector vanishes. -/
theorem eq_zero_of_mem_of_inner_hardyShift_pow_wandering {M : Submodule ℂ HardyDisk}
    (hMc : IsClosed (M : Set HardyDisk)) (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ : HardyDisk}
    (hφ : φ ∈ M) (hφo : φ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1) {x : HardyDisk} (hx : x ∈ M)
    (horth : ∀ n : ℕ, inner ℂ ((hardyShift ^ n) φ) x = 0) : x = 0 := by
  have key : ∀ n : ℕ, ∃ y ∈ M, x = (hardyShift ^ n) y ∧
      ∀ m : ℕ, inner ℂ ((hardyShift ^ m) φ) y = 0 := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, by simp, horth⟩
    | succ n ih =>
      obtain ⟨y, hyM, hxy, hy⟩ := ih
      obtain ⟨w, y', hwM, hwo, hy'M, hdec⟩ := exists_wandering_decomp hMc hinv hyM
      -- the wandering part is a multiple of `φ`
      set c := inner ℂ φ w
      have hrest : w - c • φ = 0 := by
        refine wandering_eq_zero_of_inner_eq_zero hinv hφ hφo (M.sub_mem hwM (M.smul_mem _ hφ))
          (Submodule.sub_mem _ hwo (Submodule.smul_mem _ _ hφo)) hφn ?_
        rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hφn]
        simp [c]
      have hφSy' : inner ℂ φ (hardyShift y') = 0 :=
        Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map.mpr ⟨y', hy'M, rfl⟩) hφo
      have hc : c = 0 := by
        have h0 := hy 0
        rw [pow_zero] at h0
        change inner ℂ φ y = 0 at h0
        rw [hdec, inner_add_right, hφSy', add_zero] at h0
        exact h0
      have hw : w = 0 := by rw [hc, zero_smul, sub_zero] at hrest; exact hrest
      refine ⟨y', hy'M, ?_, fun m => ?_⟩
      · rw [hxy, hdec, hw, zero_add, pow_succ]; rfl
      · have h := hy (m + 1)
        rw [hdec, hw, zero_add, hardyShift_pow_succ_apply, inner_hardyShift] at h
        exact h
  exact eq_zero_of_forall_mem_range_shift_pow fun n => by
    obtain ⟨y, -, hy, -⟩ := key n; exact ⟨y, hy⟩

/-- Multiplication by the wandering vector maps `H²` into `M`. -/
theorem hardyMul_wanderingMultiplier_mem {M : Submodule ℂ HardyDisk}
    (hMc : IsClosed (M : Set HardyDisk)) (hinv : ∀ x ∈ M, hardyShift x ∈ M) {φ : HardyDisk}
    (hφ : φ ∈ M) (hφo : φ ∈ (shiftImage M)ᗮ) (hφn : ‖φ‖ = 1) (u : HardyDisk) :
    hardyMul (wanderingMultiplier hinv hφ hφo hφn) u ∈ M := by
  set T := hardyMul (wanderingMultiplier hinv hφ hφo hφn)
  have hP : ∀ u ∈ polyMultiples hardyOne, T u ∈ M := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨m, rfl⟩ := ha
      show T ((hardyShift ^ m) hardyOne) ∈ M
      rw [hardyMul_wanderingMultiplier_shift_pow]
      exact hardyShift_pow_mem hinv hφ m
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact M.smul_mem c ha
  have hclosed : IsClosed {u : HardyDisk | T u ∈ M} := hMc.preimage T.continuous
  have hcl := closure_minimal (fun u hu => hP u hu) hclosed
  have htop : u ∈ closure (polyMultiples hardyOne : Set HardyDisk) := by
    rw [← Submodule.topologicalClosure_coe]
    have h : (polyMultiples hardyOne).topologicalClosure = ⊤ := cyclicSubspace_hardyOne
    rw [h]; exact Submodule.mem_top
  exact hcl htop

/-- **Beurling's theorem.**  Every closed shift-invariant subspace `M ≠ 0` of `H²(𝔻)` is the
range of multiplication by an inner function: there is a bounded analytic `θ` such that `M_θ` is
an isometry and `M = θ H²`.  `θ` is a unit vector of the wandering subspace `M ⊖ S M`. -/
theorem exists_inner_multiplier_of_shiftInvariant {M : Submodule ℂ HardyDisk}
    (hMc : IsClosed (M : Set HardyDisk)) (hinv : ∀ x ∈ M, hardyShift x ∈ M) (hM : M ≠ ⊥) :
    ∃ θ : DiskMultiplier, (∀ x, ‖hardyMul θ x‖ = ‖x‖) ∧ ∀ x, x ∈ M ↔ ∃ y, hardyMul θ y = x := by
  -- a unit wandering vector
  have hL : ∃ y ∈ M, y ∈ (shiftImage M)ᗮ ∧ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (eq_bot_of_wandering_eq_zero hMc hinv h)
  obtain ⟨y, hyM, hyo, hy0⟩ := hL
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
  set φ : HardyDisk := ((‖y‖⁻¹ : ℝ) : ℂ) • y with hφdef
  have hφn : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ hyn]
  have hφ : φ ∈ M := M.smul_mem _ hyM
  have hφo : φ ∈ (shiftImage M)ᗮ := (shiftImage M)ᗮ.smul_mem _ hyo
  set θ := wanderingMultiplier hinv hφ hφo hφn
  set T := hardyMul θ
  have hiso : ∀ x, ‖T x‖ = ‖x‖ := norm_hardyMul_wanderingMultiplier hinv hφ hφo hφn
  refine ⟨θ, hiso, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · -- `M ⊆ θ H²`
    set R : Submodule ℂ HardyDisk := LinearMap.range (T : HardyDisk →ₗ[ℂ] HardyDisk)
    have hRc : IsClosed (R : Set HardyDisk) := by
      have h := (AddMonoidHomClass.isometry_of_norm T hiso).isClosedEmbedding.isClosedMap _
        isClosed_univ
      rw [Set.image_univ] at h
      have heq : (R : Set HardyDisk) = Set.range T := by
        ext v; simp [R]
      rw [heq]; exact h
    haveI : CompleteSpace R := hRc.completeSpace_coe
    haveI := Submodule.HasOrthogonalProjection.ofCompleteSpace R
    have hPR : R.starProjection x ∈ R := R.starProjection_apply_mem x
    have hRM : ∀ v ∈ R, v ∈ M := by
      rintro v ⟨u, rfl⟩
      exact hardyMul_wanderingMultiplier_mem hMc hinv hφ hφo hφn u
    set d := x - R.starProjection x
    have hdM : d ∈ M := M.sub_mem hx (hRM _ hPR)
    have hdo : d ∈ Rᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have hd0 : d = 0 := by
      refine eq_zero_of_mem_of_inner_hardyShift_pow_wandering hMc hinv hφ hφo hφn hdM fun n => ?_
      refine Submodule.inner_right_of_mem_orthogonal ?_ hdo
      exact ⟨(hardyShift ^ n) hardyOne, hardyMul_wanderingMultiplier_shift_pow hinv hφ hφo hφn n⟩
    have hxR : x ∈ R := by
      have : x = R.starProjection x := by rw [← sub_eq_zero]; exact hd0
      rw [this]; exact hPR
    obtain ⟨u, hu⟩ := hxR
    exact ⟨u, hu⟩
  · -- `θ H² ⊆ M`
    rintro ⟨u, rfl⟩
    exact hardyMul_wanderingMultiplier_mem hMc hinv hφ hφo hφn u

end

end GaloisForLFunctions.HTGeometry
