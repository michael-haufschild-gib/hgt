import Mathlib

/-!
# The valuated Plücker–Gram exchange law

The maximal minors of a finite frame satisfy an unconditional exchange identity: expanding one
column of a frame in the columns of a second frame and reading the coefficients by Cramer's rule
gives

`p(c) · p(b) = ∑ⱼ p(c[j ↦ b i]) · p(b[i ↦ c j])`.

Applying a nonarchimedean valuation turns this into the valuated matroid exchange axiom, and
restricting to minimal-depth frames shows that the minimal-depth frames are closed under exchange.

The Gram determinant of a rectangular frame is the square-sum of its maximal minors, in the exact
`r!`-weighted form over all ordered column selections.  Over power series this doubles the
valuation of the minor ideal and its leading coefficient is the positive square-sum of the minimal
packet.

Rephasing the columns by unimodular scalars leaves the Gram matrix fixed but multiplies every
minor by the product of the phases, so no map from Gram data can recover the phased packet.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Matrix Finset

/-! ## Column linearity of the determinant -/

variable {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]

theorem det_updateCol_finsetSum {ι : Type*} [DecidableEq ι] (A : Matrix m m R) (j : m)
    (s : Finset ι) (c : ι → R) (v : ι → m → R) :
    (A.updateCol j (fun k => ∑ i ∈ s, c i * v i k)).det
      = ∑ i ∈ s, c i * (A.updateCol j (v i)).det := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    refine Matrix.det_eq_zero_of_column_eq_zero j fun i => ?_
    simp
  | insert a s ha ih =>
    have hfun : (fun k => ∑ i ∈ insert a s, c i * v i k)
        = (fun k => c a * v a k) + (fun k => ∑ i ∈ s, c i * v i k) := by
      funext k
      rw [Finset.sum_insert ha]
      rfl
    rw [hfun, Matrix.det_updateCol_add, ih, Finset.sum_insert ha]
    congr 1
    rw [show (fun k => c a * v a k) = c a • v a from rfl, Matrix.det_updateCol_smul]

/-! ## Minors of a frame -/

variable {r n : ℕ}

/-- The maximal minor of a frame at an ordered column selection. -/
def frameMinor (T : Matrix (Fin r) (Fin n) R) (b : Fin r → Fin n) : R :=
  (T.submatrix id b).det

omit [CommRing R] in
theorem submatrix_update (T : Matrix (Fin r) (Fin n) R) (b : Fin r → Fin n) (i : Fin r)
    (k : Fin n) :
    (T.submatrix id b).updateCol i (fun row => T row k)
      = T.submatrix id (Function.update b i k) := by
  ext row j
  by_cases h : j = i
  · subst h
    simp
  · simp [Matrix.updateCol_ne h, Function.update_of_ne h]

/-- **The Plücker exchange identity.**  Unconditional: no invertibility is needed. -/
theorem plucker_exchange (T : Matrix (Fin r) (Fin n) R) (b c : Fin r → Fin n) (i : Fin r) :
    frameMinor T c * frameMinor T b
      = ∑ j : Fin r,
          frameMinor T (Function.update c j (b i)) * frameMinor T (Function.update b i (c j)) := by
  classical
  have hcramer : ∀ j : Fin r,
      (T.submatrix id c).cramer (fun row => T row (b i)) j
        = frameMinor T (Function.update c j (b i)) := by
    intro j
    rw [Matrix.cramer_apply, submatrix_update, frameMinor]
  have hmul : ∀ row : Fin r,
      ∑ j : Fin r, (T.submatrix id c).cramer (fun row => T row (b i)) j * T row (c j)
        = frameMinor T c * T row (b i) := by
    intro row
    have h := congrFun (Matrix.mulVec_cramer (T.submatrix id c) (fun row => T row (b i))) row
    rw [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] at h
    rw [frameMinor, ← h]
    exact Finset.sum_congr rfl fun j _ => by simp [Matrix.submatrix_apply, mul_comm]
  have hcol : (fun row => ∑ j : Fin r,
        (T.submatrix id c).cramer (fun row => T row (b i)) j * T row (c j))
      = frameMinor T c • fun row => (T.submatrix id b) row i := by
    funext row
    rw [hmul row, Pi.smul_apply, smul_eq_mul]
    simp
  have hself : (T.submatrix id b).updateCol i (fun row => (T.submatrix id b) row i)
      = T.submatrix id b := by
    ext row j
    by_cases h : j = i
    · subst h
      simp
    · simp [Matrix.updateCol_ne h]
  have hleft : ((T.submatrix id b).updateCol i
      (fun row => ∑ j : Fin r,
        (T.submatrix id c).cramer (fun row => T row (b i)) j * T row (c j))).det
        = frameMinor T c * frameMinor T b := by
    rw [hcol, Matrix.det_updateCol_smul, hself, frameMinor]
    rfl
  rw [← hleft, det_updateCol_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcramer j, submatrix_update, frameMinor]
  rfl

/-! ## The valuated matroid exchange axiom -/

section Valuated

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- **The valuated matroid exchange axiom.**  For frames `b`, `c` and a position `i` there is a
position `j` with `ω(b) + ω(c) ≥ ω(b[i ↦ c j]) + ω(c[j ↦ b i])`, in the multiplicative convention
`v = exp(-ω)`. -/
theorem valuated_exchange (val : Valuation K Γ) (T : Matrix (Fin r) (Fin n) K)
    (b c : Fin r → Fin n) (i : Fin r) (hr : 0 < r) :
    ∃ j : Fin r,
      val (frameMinor T c) * val (frameMinor T b)
        ≤ val (frameMinor T (Function.update c j (b i)))
            * val (frameMinor T (Function.update b i (c j))) := by
  classical
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hr
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin r))
    (fun j => val (frameMinor T (Function.update c j (b i)))
      * val (frameMinor T (Function.update b i (c j)))) hne
  refine ⟨j₀, ?_⟩
  rw [← Valuation.map_mul, plucker_exchange T b c i]
  refine Valuation.map_sum_le val fun j _ => ?_
  rw [Valuation.map_mul]
  exact hj₀ j (Finset.mem_univ j)

/-- **The minimal-depth frames are closed under exchange.**  If two frames both attain the maximal
value `M` of the minor profile, then so do the two exchanged frames. -/
theorem initial_exchange (val : Valuation K Γ) (T : Matrix (Fin r) (Fin n) K)
    {M : Γ} (hM : M ≠ 0) (hmax : ∀ d : Fin r → Fin n, val (frameMinor T d) ≤ M)
    {b c : Fin r → Fin n} (hb : val (frameMinor T b) = M) (hc : val (frameMinor T c) = M)
    (i : Fin r) (hr : 0 < r) :
    ∃ j : Fin r, val (frameMinor T (Function.update c j (b i))) = M
      ∧ val (frameMinor T (Function.update b i (c j))) = M := by
  obtain ⟨j, hj⟩ := valuated_exchange val T b c i hr
  rw [hb, hc] at hj
  set x := val (frameMinor T (Function.update c j (b i))) with hx
  set y := val (frameMinor T (Function.update b i (c j))) with hy
  have hxM : x ≤ M := hmax _
  have hyM : y ≤ M := hmax _
  have hxy : M * M ≤ x * y := hj
  have hchain : x * M = M * M := by
    refine le_antisymm (mul_le_mul' hxM le_rfl) ?_
    exact le_trans hxy (mul_le_mul' le_rfl hyM)
  have hxeq : x = M := mul_right_cancel₀ hM hchain
  have hchain2 : M * y = M * M := by
    refine le_antisymm (mul_le_mul' le_rfl hyM) ?_
    rw [hxeq] at hxy
    exact hxy
  have hyeq : y = M := mul_left_cancel₀ hM hchain2
  exact ⟨j, hxeq, hyeq⟩

/-- **The valuation of the minor ideal is the minimal depth.**  Every integral combination of the
maximal minors has value at most the maximum of the generators. -/
theorem valuation_integral_combination_le (val : Valuation K Γ) (T : Matrix (Fin r) (Fin n) K)
    {M : Γ} (hmax : ∀ d : Fin r → Fin n, val (frameMinor T d) ≤ M)
    (a : (Fin r → Fin n) → K) (ha : ∀ b, val (a b) ≤ 1) :
    val (∑ b : Fin r → Fin n, a b * frameMinor T b) ≤ M := by
  classical
  refine Valuation.map_sum_le val fun b _ => ?_
  rw [Valuation.map_mul]
  calc val (a b) * val (frameMinor T b) ≤ 1 * val (frameMinor T b) :=
        mul_le_mul' (ha b) le_rfl
    _ = val (frameMinor T b) := one_mul _
    _ ≤ M := hmax b

/-- **The minimal depth is attained inside the minor ideal.** -/
theorem valuation_integral_combination_attained (val : Valuation K Γ)
    (T : Matrix (Fin r) (Fin n) K) (b₀ : Fin r → Fin n) :
    ∃ a : (Fin r → Fin n) → K, (∀ b, val (a b) ≤ 1)
      ∧ val (∑ b : Fin r → Fin n, a b * frameMinor T b) = val (frameMinor T b₀) := by
  classical
  refine ⟨fun b => if b = b₀ then 1 else 0, fun b => ?_, ?_⟩
  · by_cases h : b = b₀ <;> simp [h]
  · rw [Finset.sum_eq_single b₀]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ b₀) h

end Valuated

/-! ## The Gram determinant is the square-sum of the maximal minors -/

section CauchyBinet

variable {S : Type*} [CommRing S]

/-- The Gram matrix of a frame relative to a coefficient involution. -/
def frameGram (cj : S →+* S) (T : Matrix (Fin r) (Fin n) S) : Matrix (Fin r) (Fin r) S :=
  T * (T.map cj)ᵀ

theorem frameGram_apply (cj : S →+* S) (T : Matrix (Fin r) (Fin n) S) (a b : Fin r) :
    frameGram cj T a b = ∑ k : Fin n, T a k * cj (T b k) := by
  rw [frameGram, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.transpose_apply, Matrix.map_apply]

theorem frameMinor_eq_sum (T : Matrix (Fin r) (Fin n) S) (f : Fin r → Fin n) :
    frameMinor T f = ∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : S) * ∏ i, T (σ i) (f i) := by
  rw [frameMinor, Matrix.det_apply']
  exact Finset.sum_congr rfl fun σ _ => by simp [Matrix.submatrix_apply]

theorem map_frameMinor_eq_sum (cj : S →+* S) (T : Matrix (Fin r) (Fin n) S) (f : Fin r → Fin n) :
    cj (frameMinor T f) = ∑ τ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign τ : ℤ) : S) * ∏ i, cj (T (τ i) (f i)) := by
  rw [frameMinor_eq_sum T f, map_sum]
  exact Finset.sum_congr rfl fun τ _ => by rw [map_mul, map_intCast, map_prod]

/-- **Cauchy–Binet in ordered form.**  The Gram determinant of a rectangular frame is the
square-sum of its maximal minors over all ordered column selections, weighted by `r!`. -/
theorem factorial_mul_det_frameGram (cj : S →+* S) (T : Matrix (Fin r) (Fin n) S) :
    ((Nat.factorial r : ℕ) : S) * (frameGram cj T).det
      = ∑ f : Fin r → Fin n, frameMinor T f * cj (frameMinor T f) := by
  classical
  have hterm : ∀ f : Fin r → Fin n, frameMinor T f * cj (frameMinor T f)
      = ∑ σ : Equiv.Perm (Fin r), ∑ τ : Equiv.Perm (Fin r),
          (((Equiv.Perm.sign σ : ℤ) : S) * ((Equiv.Perm.sign τ : ℤ) : S)) *
            ∏ i, (T (σ i) (f i) * cj (T (τ i) (f i))) := by
    intro f
    rw [map_frameMinor_eq_sum cj T f, frameMinor_eq_sum T f, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  have hfsum : ∀ σ τ : Equiv.Perm (Fin r),
      (∑ f : Fin r → Fin n, ∏ i, (T (σ i) (f i) * cj (T (τ i) (f i))))
        = ∏ i, frameGram cj T (σ i) (τ i) := by
    intro σ τ
    have hprod : ∏ i, frameGram cj T (σ i) (τ i)
        = ∏ i : Fin r, ∑ k : Fin n, T (σ i) k * cj (T (τ i) k) :=
      Finset.prod_congr rfl fun i _ => frameGram_apply cj T (σ i) (τ i)
    rw [hprod, Finset.prod_univ_sum, Fintype.piFinset_univ]
  have htau : ∀ σ : Equiv.Perm (Fin r),
      (∑ τ : Equiv.Perm (Fin r), ((Equiv.Perm.sign τ : ℤ) : S)
          * ∏ i, frameGram cj T (σ i) (τ i))
        = ((Equiv.Perm.sign σ : ℤ) : S) * (frameGram cj T).det := by
    intro σ
    have hH : (((frameGram cj T).submatrix σ id)ᵀ).det
        = ∑ τ : Equiv.Perm (Fin r), ((Equiv.Perm.sign τ : ℤ) : S)
            * ∏ i, frameGram cj T (σ i) (τ i) := by
      rw [Matrix.det_apply']
      exact Finset.sum_congr rfl fun τ _ => by simp [Matrix.transpose_apply,
        Matrix.submatrix_apply]
    rw [← hH, Matrix.det_transpose, Matrix.det_permute]
  rw [Finset.sum_congr rfl fun f _ => hterm f, Finset.sum_comm]
  have hswap : ∀ σ : Equiv.Perm (Fin r),
      (∑ f : Fin r → Fin n, ∑ τ : Equiv.Perm (Fin r),
        (((Equiv.Perm.sign σ : ℤ) : S) * ((Equiv.Perm.sign τ : ℤ) : S)) *
          ∏ i, (T (σ i) (f i) * cj (T (τ i) (f i))))
      = ((Equiv.Perm.sign σ : ℤ) : S) * (((Equiv.Perm.sign σ : ℤ) : S) *
          (frameGram cj T).det) := by
    intro σ
    rw [Finset.sum_comm]
    have hin : ∀ τ : Equiv.Perm (Fin r),
        (∑ f : Fin r → Fin n,
          (((Equiv.Perm.sign σ : ℤ) : S) * ((Equiv.Perm.sign τ : ℤ) : S)) *
            ∏ i, (T (σ i) (f i) * cj (T (τ i) (f i))))
          = ((Equiv.Perm.sign σ : ℤ) : S) * (((Equiv.Perm.sign τ : ℤ) : S)
              * ∏ i, frameGram cj T (σ i) (τ i)) := by
      intro τ
      rw [← Finset.mul_sum, hfsum σ τ]
      ring
    rw [Finset.sum_congr rfl fun τ _ => hin τ, ← Finset.mul_sum, htau σ]
  rw [Finset.sum_congr rfl fun σ _ => hswap σ]
  have hsq : ∀ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : S) * (((Equiv.Perm.sign σ : ℤ) : S) * (frameGram cj T).det)
        = (frameGram cj T).det := by
    intro σ
    have h1 : ((Equiv.Perm.sign σ : ℤ) : S) * ((Equiv.Perm.sign σ : ℤ) : S) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    rw [← mul_assoc, h1, one_mul]
  rw [Finset.sum_congr rfl fun σ _ => hsq σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end CauchyBinet

/-! ## Positive capacity erases Plücker phase -/

section Rephase

variable {S : Type*} [CommRing S]

/-- **Rephasing leaves the Gram matrix fixed.**  If `u` is unimodular for the involution, the
frame `T · diag u` has the same Gram matrix as `T`. -/
theorem frameGram_rephase (cj : S →+* S) (T : Matrix (Fin r) (Fin n) S) (u : Fin n → S)
    (hu : ∀ k, u k * cj (u k) = 1) :
    frameGram cj (T * Matrix.diagonal u) = frameGram cj T := by
  ext a b
  rw [frameGram_apply, frameGram_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, map_mul]
  calc T a k * u k * (cj (T b k) * cj (u k))
      = T a k * cj (T b k) * (u k * cj (u k)) := by ring
    _ = T a k * cj (T b k) := by rw [hu k, mul_one]

/-- **Rephasing multiplies every minor by the product of the phases.** -/
theorem frameMinor_rephase (T : Matrix (Fin r) (Fin n) S) (u : Fin n → S)
    (b : Fin r → Fin n) :
    frameMinor (T * Matrix.diagonal u) b = (∏ i, u (b i)) * frameMinor T b := by
  classical
  rw [frameMinor, frameMinor]
  have hsub : ((T * Matrix.diagonal u).submatrix id b)
      = (T.submatrix id b) * Matrix.diagonal (fun i => u (b i)) := by
    ext row j
    rw [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.submatrix_apply]
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
  ring

/-- **Positive capacity is a phase quotient.**  A single nontrivial column phase changes the minor
packet while fixing every Gram entry, so no map from Gram data recovers the phased packet. -/
theorem gram_erases_phase (cj : S →+* S) (T : Matrix (Fin r) (Fin n) S) (u : Fin n → S)
    (hu : ∀ k, u k * cj (u k) = 1) (b : Fin r → Fin n)
    (hne : (∏ i, u (b i)) * frameMinor T b ≠ frameMinor T b) :
    frameGram cj (T * Matrix.diagonal u) = frameGram cj T
      ∧ frameMinor (T * Matrix.diagonal u) b ≠ frameMinor T b := by
  refine ⟨frameGram_rephase cj T u hu, ?_⟩
  rw [frameMinor_rephase]
  exact hne

end Rephase

/-! ## Nonzero minors are exactly the frames -/

/-- **The maximal-minor criterion.**  A column selection has nonzero minor exactly when the
selected columns are linearly independent. -/
theorem frameMinor_ne_zero_iff {K : Type*} [Field K] (T : Matrix (Fin r) (Fin n) K)
    (b : Fin r → Fin n) :
    frameMinor T b ≠ 0 ↔ LinearIndependent K (T.submatrix id b).col := by
  rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det, frameMinor,
    isUnit_iff_ne_zero]

/-! ## Doubling of depth and the positive leading packet -/

section Depth

open PowerSeries

/-- The coefficientwise conjugation of a complex power series. -/
noncomputable def psConj : PowerSeries ℂ →+* PowerSeries ℂ := PowerSeries.map (starRingEnd ℂ)

theorem coeff_psConj (i : ℕ) (p : PowerSeries ℂ) :
    coeff i (psConj p) = (starRingEnd ℂ) (coeff i p) := by
  rw [psConj, PowerSeries.coeff_map]

/-- Below twice the depth the Hermitian square of a power series vanishes. -/
theorem coeff_lt_of_mul_psConj {d : ℕ} {p : PowerSeries ℂ} (hp : ∀ i < d, coeff i p = 0)
    {m : ℕ} (hm : m < 2 * d) : coeff m (p * psConj p) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hq' : q.1 + q.2 = m := List.Nat.mem_antidiagonal.mp hq
  rcases lt_or_ge q.1 d with h1 | h1
  · rw [hp q.1 h1, zero_mul]
  · have h2 : q.2 < d := by omega
    rw [coeff_psConj, hp q.2 h2, map_zero, mul_zero]

/-- At twice the depth the Hermitian square of a power series has the positive square modulus of
the leading coefficient. -/
theorem coeff_two_mul_of_mul_psConj {d : ℕ} {p : PowerSeries ℂ} (hp : ∀ i < d, coeff i p = 0) :
    coeff (2 * d) (p * psConj p) = ((Complex.normSq (coeff d p) : ℝ) : ℂ) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single ((d, d) : ℕ × ℕ)]
  · rw [coeff_psConj, Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  · intro q hq hne
    have hq' : q.1 + q.2 = 2 * d := List.Nat.mem_antidiagonal.mp hq
    rcases lt_or_ge q.1 d with h1 | h1
    · rw [hp q.1 h1, zero_mul]
    · have h2 : q.2 < d := by
        rcases lt_or_ge q.2 d with h | h
        · exact h
        · exact absurd (Prod.ext (by omega : q.1 = d) (by omega : q.2 = d)) hne
      rw [coeff_psConj, hp q.2 h2, map_zero, mul_zero]
  · intro h
    exact absurd (List.Nat.mem_antidiagonal.mpr (by omega)) h

variable {r n : ℕ}

/-- **The square law.**  Below twice the minimal depth every coefficient of the Gram determinant
vanishes. -/
theorem coeff_det_frameGram_lt {d : ℕ} (T : Matrix (Fin r) (Fin n) (PowerSeries ℂ))
    (hd : ∀ f : Fin r → Fin n, ∀ i < d, coeff i (frameMinor T f) = 0)
    {m : ℕ} (hm : m < 2 * d) :
    ((Nat.factorial r : ℕ) : ℂ) * coeff m (frameGram psConj T).det = 0 := by
  have hfac := factorial_mul_det_frameGram psConj T
  have hcoeff : coeff m (((Nat.factorial r : ℕ) : PowerSeries ℂ) * (frameGram psConj T).det)
      = ((Nat.factorial r : ℕ) : ℂ) * coeff m (frameGram psConj T).det := by
    rw [show ((Nat.factorial r : ℕ) : PowerSeries ℂ)
        = PowerSeries.C ((Nat.factorial r : ℕ) : ℂ) from
          (map_natCast (PowerSeries.C : ℂ →+* PowerSeries ℂ) (Nat.factorial r)).symm,
      PowerSeries.coeff_C_mul]
  rw [← hcoeff, hfac, map_sum]
  exact Finset.sum_eq_zero fun f _ => coeff_lt_of_mul_psConj (hd f) hm

/-- **The positive leading packet.**  At twice the minimal depth the Gram determinant has the
square-sum of the minimal Plücker packet as coefficient. -/
theorem coeff_det_frameGram_two_mul {d : ℕ} (T : Matrix (Fin r) (Fin n) (PowerSeries ℂ))
    (hd : ∀ f : Fin r → Fin n, ∀ i < d, coeff i (frameMinor T f) = 0) :
    ((Nat.factorial r : ℕ) : ℂ) * coeff (2 * d) (frameGram psConj T).det
      = ((∑ f : Fin r → Fin n, Complex.normSq (coeff d (frameMinor T f)) : ℝ) : ℂ) := by
  have hfac := factorial_mul_det_frameGram psConj T
  have hcoeff : coeff (2 * d) (((Nat.factorial r : ℕ) : PowerSeries ℂ)
        * (frameGram psConj T).det)
      = ((Nat.factorial r : ℕ) : ℂ) * coeff (2 * d) (frameGram psConj T).det := by
    rw [show ((Nat.factorial r : ℕ) : PowerSeries ℂ)
        = PowerSeries.C ((Nat.factorial r : ℕ) : ℂ) from
          (map_natCast (PowerSeries.C : ℂ →+* PowerSeries ℂ) (Nat.factorial r)).symm,
      PowerSeries.coeff_C_mul]
  rw [← hcoeff, hfac, map_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun f _ => coeff_two_mul_of_mul_psConj (hd f)

/-- **The depth doubles exactly.**  If the minimal depth `d` is attained, the Gram determinant
has a nonzero coefficient at `2d` and vanishing coefficients below. -/
theorem det_frameGram_depth {d : ℕ} (T : Matrix (Fin r) (Fin n) (PowerSeries ℂ))
    (hd : ∀ f : Fin r → Fin n, ∀ i < d, coeff i (frameMinor T f) = 0)
    {f₀ : Fin r → Fin n} (hf₀ : coeff d (frameMinor T f₀) ≠ 0) :
    (∀ m < 2 * d, coeff m (frameGram psConj T).det = 0)
      ∧ coeff (2 * d) (frameGram psConj T).det ≠ 0 := by
  have hfacne : ((Nat.factorial r : ℕ) : ℂ) ≠ 0 := by
    have : Nat.factorial r ≠ 0 := Nat.factorial_ne_zero r
    exact_mod_cast this
  refine ⟨fun m hm => ?_, ?_⟩
  · have := coeff_det_frameGram_lt T hd hm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hfacne
    · exact h
  · intro hzero
    have hsum := coeff_det_frameGram_two_mul T hd
    rw [hzero, mul_zero] at hsum
    have hreal : (∑ f : Fin r → Fin n, Complex.normSq (coeff d (frameMinor T f))) = 0 := by
      exact_mod_cast hsum.symm
    have hpos : 0 < Complex.normSq (coeff d (frameMinor T f₀)) :=
      Complex.normSq_pos.mpr hf₀
    have hnn : ∀ f ∈ (Finset.univ : Finset (Fin r → Fin n)),
        0 ≤ Complex.normSq (coeff d (frameMinor T f)) := fun f _ => Complex.normSq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hreal f₀ (Finset.mem_univ f₀)
    exact absurd this hpos.ne'

end Depth

end HTGeometry.ConstraintFrameRelativity
