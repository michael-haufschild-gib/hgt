import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalRankDecidesTheWindow

/-!
# The rank barrier

The window theorem (`TheExceptionalRankDecidesTheWindow`) has two parameters that cannot be improved.

**The window length is the exceptional rank.** The roots-of-unity tower of rank `2k`, with outer
layer `R·μ_k` and reflected inner layer `R⁻¹·μ_k`, has vanishing level sums at every level not
divisible by `k` (`levelSum_rootsOfUnityTower_eq_zero`). So a bound holding on a set of levels of
density `1 − 1/k` (`card_Ioc_filter_not_dvd`), containing runs of length `k − 1` at every position,
does not self-improve, although the top `R > 1` is visible and the tower is closed under conjugation
and inversion. The barrier survives any critical remainder of trace norm `W`, which only raises the
bound to `W` (`norm_levelSum_rootsOfUnity_add_le`). At unbounded exceptional rank only thick sets of
levels self-improve.

**The currency is the trace norm, not the rank.** Any finite sequence of values on a window of `N`
levels is cancelled exactly by `N` distinct unimodular modes (`exists_unimodular_cancelling_layer`,
inverse Vandermonde). So a critical layer of finite rank can hide every top on every finite window.
It pays for this in trace norm: for a visible top of modulus `R ≥ 1` there is `ε > 0` such that every
remainder of modulus `≤ 1`, of any rank, hiding the top on the window at position `M` has trace norm
`≥ εR^{M+1}` (`le_tsum_norm_of_hides_top`).
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-! ### The roots-of-unity tower -/

/-- The primitive `k`-th root of unity `e^{2πi/k}`. -/
def unitRoot (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / k)

theorem isPrimitiveRoot_unitRoot {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (unitRoot k) k :=
  Complex.isPrimitiveRoot_exp k hk

/-- The roots-of-unity tower: outer modes `R ωʲ` and inner modes `R⁻¹ ωʲ`, `j < k`. -/
def rootsOfUnityTower (R : ℝ) (k : ℕ) : Bool × Fin k → ℂ := fun i =>
  (if i.1 then (R : ℂ) else (R : ℂ)⁻¹) * unitRoot k ^ (i.2 : ℕ)

theorem unitRoot_pow_sub {k : ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j ≤ k) :
    unitRoot k ^ (k - j) = starRingEnd ℂ (unitRoot k ^ j) := by
  have hω := isPrimitiveRoot_unitRoot hk
  have hnorm : ‖unitRoot k ^ j‖ = 1 := by rw [norm_pow, hω.norm'_eq_one hk, one_pow]
  rw [← Complex.inv_eq_conj hnorm]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, Nat.sub_add_cancel hj, hω.pow_eq_one]

/-- The roots-of-unity tower is closed under conjugation. -/
theorem rootsOfUnityTower_conj {R : ℝ} {k : ℕ} (hk : k ≠ 0) (i : Bool × Fin k) :
    ∃ i', rootsOfUnityTower R k i' = starRingEnd ℂ (rootsOfUnityTower R k i) := by
  have hω := isPrimitiveRoot_unitRoot hk
  refine ⟨(i.1, ⟨(k - i.2) % k, Nat.mod_lt _ (Nat.pos_of_ne_zero hk)⟩), ?_⟩
  have hpow : unitRoot k ^ ((k - (i.2 : ℕ)) % k) = unitRoot k ^ (k - (i.2 : ℕ)) := by
    conv_rhs => rw [← Nat.mod_add_div (k - (i.2 : ℕ)) k]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  simp only [rootsOfUnityTower, map_mul]
  rw [hpow, unitRoot_pow_sub hk i.2.2.le]
  cases i.1 <;> simp [Complex.conj_ofReal]

/-- The roots-of-unity tower is closed under the functional equation `z ↦ 1/z`. -/
theorem rootsOfUnityTower_inv {R : ℝ} (hR : R ≠ 0) {k : ℕ} (hk : k ≠ 0) (i : Bool × Fin k) :
    ∃ i', rootsOfUnityTower R k i' * rootsOfUnityTower R k i = 1 := by
  have hω := isPrimitiveRoot_unitRoot hk
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  refine ⟨(!i.1, ⟨(k - i.2) % k, Nat.mod_lt _ (Nat.pos_of_ne_zero hk)⟩), ?_⟩
  have hpow : unitRoot k ^ ((k - (i.2 : ℕ)) % k) * unitRoot k ^ (i.2 : ℕ) = 1 := by
    rw [← pow_add, hω.pow_eq_one_iff_dvd]
    have h := i.2.2
    refine Nat.dvd_of_mod_eq_zero ?_
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.sub_add_cancel h.le, Nat.mod_self]
  simp only [rootsOfUnityTower]
  calc _ = ((if (!i.1) = true then (R : ℂ) else (R : ℂ)⁻¹) * (if i.1 = true then (R : ℂ) else
        (R : ℂ)⁻¹)) * (unitRoot k ^ ((k - (i.2 : ℕ)) % k) * unitRoot k ^ (i.2 : ℕ)) := by ring
    _ = 1 := by rw [hpow, mul_one]; cases i.1 <;> simp [hRc]

/-- The top `R` of the roots-of-unity tower is visible: its `k` outer points are distinct. -/
theorem rootsOfUnityTower_injective {R : ℝ} (hR : 1 < R) {k : ℕ} (hk : k ≠ 0) :
    Function.Injective (rootsOfUnityTower R k) := by
  have hω := isPrimitiveRoot_unitRoot hk
  have hR0 : (0 : ℝ) < R := by linarith
  have hnorm : ∀ i, ‖rootsOfUnityTower R k i‖ = if i.1 then R else R⁻¹ := fun i => by
    simp only [rootsOfUnityTower, norm_mul, norm_pow, hω.norm'_eq_one hk, one_pow, mul_one]
    cases i.1 <;> simp [Complex.norm_real, abs_of_pos hR0]
  have hRinv : R⁻¹ ≠ R := (lt_trans (inv_lt_one_of_one_lt₀ hR) hR).ne
  rintro ⟨sa, ja⟩ ⟨sb, jb⟩ h
  have hnr := congrArg norm h
  rw [hnorm, hnorm] at hnr
  have hab : sa = sb := by
    cases sa <;> cases sb
    · rfl
    · exact absurd hnr (by simpa using hRinv)
    · exact absurd hnr (by simpa using hRinv.symm)
    · rfl
  subst hab
  have hfac : (if sa then (R : ℂ) else (R : ℂ)⁻¹) ≠ 0 := by
    cases sa <;> simp [show (R : ℂ) ≠ 0 by exact_mod_cast hR0.ne']
  simp only [rootsOfUnityTower] at h
  have hj := hω.pow_inj ja.2 jb.2 (mul_left_cancel₀ hfac h)
  exact Prod.ext rfl (Fin.ext hj)

/-- **Vanishing off `kℤ`.** The unit-weight level sums of the roots-of-unity tower vanish at every
level `ν` not divisible by `k`. -/
theorem levelSum_rootsOfUnityTower_eq_zero {R : ℝ} {k : ℕ} (hk : k ≠ 0) {ν : ℕ}
    (hν : ¬ k ∣ ν) : levelSum (rootsOfUnityTower R k) (fun _ => 1) ν = 0 := by
  have hω := isPrimitiveRoot_unitRoot hk
  have hne : unitRoot k ^ ν ≠ 1 := fun h => hν ((hω.pow_eq_one_iff_dvd ν).mp h)
  have hgeom : ∑ j ∈ range k, (unitRoot k ^ ν) ^ j = 0 := by
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
      zero_div]
  have hfin : ∑ j : Fin k, unitRoot k ^ ((j : ℕ) * ν) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => unitRoot k ^ (j * ν))]
    simpa [pow_mul, mul_comm] using hgeom
  unfold levelSum
  rw [tsum_fintype, Fintype.sum_prod_type]
  simp only [one_mul, rootsOfUnityTower, zpow_natCast, mul_pow, ← pow_mul]
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, ← Finset.mul_sum, hfin, mul_zero, add_zero]

/-- **The barrier survives an infinite critical remainder.** Adjoin to the roots-of-unity tower any
remainder of modulus `≤ 1`, of any rank, with trace norm `W`: the level sums stay `≤ W` at every
level not divisible by `k`, although the top `R` is visible. -/
theorem norm_levelSum_rootsOfUnity_add_le {R : ℝ} {k : ℕ} (hk : k ≠ 0) {κ : Type*} (u w : κ → ℂ)
    (hu : ∀ l, ‖u l‖ ≤ 1) (hw : Summable fun l => ‖w l‖) {ν : ℕ} (hν : ¬ k ∣ ν) :
    ‖levelSum (Sum.elim (rootsOfUnityTower R k) u) (Sum.elim (fun _ => 1) w) ν‖ ≤
      ∑' l, ‖w l‖ := by
  have hsplit : levelSum (Sum.elim (rootsOfUnityTower R k) u) (Sum.elim (fun _ => 1) w) ν =
      levelSum (rootsOfUnityTower R k) (fun _ => 1) ν + levelSum u w ν := by
    unfold levelSum
    exact Summable.tsum_sum Summable.of_finite (summable_levelTerm hu hw ν)
  rw [hsplit, levelSum_rootsOfUnityTower_eq_zero hk hν, zero_add]
  simpa using norm_levelSum_le hu hw ν

/-- The levels not divisible by `k` have density `1 − 1/k`: `(k − 1)n` of the first `kn`. -/
theorem card_Ioc_filter_not_dvd (k n : ℕ) (hk : k ≠ 0) :
    ((Ioc 0 (k * n)).filter fun ν => ¬ k ∣ ν).card = (k - 1) * n := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div (k * n) k
  have h2 := card_filter_add_card_filter_not (s := Ioc 0 (k * n)) (fun ν => k ∣ ν)
  rw [h1, Nat.card_Ioc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)] at h2
  rw [Nat.sub_mul, one_mul]
  omega

/-- Every window `[km + 1, km + k − 1]` avoids `kℤ`: runs of length `k − 1` at every position. -/
theorem not_dvd_of_mem_window {k m ν : ℕ} (h1 : k * m + 1 ≤ ν) (h2 : ν ≤ k * m + (k - 1)) :
    ¬ k ∣ ν := by
  rintro ⟨d, rfl⟩
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at h1
    · exact h
  have : m < d := by
    by_contra hd; push Not at hd
    have := Nat.mul_le_mul_left k hd; omega
  have : k * m + k ≤ k * d := by
    have h := Nat.mul_le_mul_left k (Nat.succ_le_of_lt this)
    rwa [Nat.mul_succ] at h
  omega

/-! ### Hiding a top on a window -/

/-- **Vandermonde hiding.** For `N` distinct nonzero modes `u_l`, any values `y` on the window
`[M+1, M+N]` are cancelled: some weights `w` give `y_ν + Σ_l w_l u_lᵛ = 0` there. -/
theorem exists_unimodular_cancelling_layer {N : ℕ} (u : Fin N → ℂ) (hu : Function.Injective u)
    (hu0 : ∀ l, u l ≠ 0) (M : ℕ) (y : ℕ → ℂ) :
    ∃ w : Fin N → ℂ, ∀ m : Fin N, y (M + 1 + m) + ∑ l, w l * u l ^ (M + 1 + (m : ℕ)) = 0 := by
  classical
  set A : Matrix (Fin N) (Fin N) ℂ := fun m l => u l ^ (M + 1 + (m : ℕ)) with hA
  have hAfac : A = Matrix.transpose (Matrix.vandermonde u) *
      Matrix.diagonal (fun l => u l ^ (M + 1)) := by
    ext m l
    simp only [hA, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [add_comm (M + 1), pow_add]
  have hdet : IsUnit A.det := by
    rw [hAfac, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hu) ?_)
    exact Finset.prod_ne_zero_iff.mpr fun l _ => pow_ne_zero _ (hu0 l)
  set v : Fin N → ℂ := fun m => -y (M + 1 + (m : ℕ)) with hv
  refine ⟨A⁻¹.mulVec v, fun m => ?_⟩
  have h : (A.mulVec (A⁻¹.mulVec v)) m = v m := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hexp : (A.mulVec (A⁻¹.mulVec v)) m =
      ∑ l, (A⁻¹.mulVec v) l * u l ^ (M + 1 + (m : ℕ)) := by
    show ∑ l, A m l * (A⁻¹.mulVec v) l = _
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [← hexp, h, hv]
  ring

/-- **The price of hiding.** For a visible top (points `P`, coefficients `c`, visible points of modulus
`R ≥ 1`) there is `ε > 0` such that every remainder of modulus `≤ 1`, of any rank, cancelling the top
on the window `[M+1, M+#P]` has trace norm `≥ εR^{M+1}`. -/
theorem le_tsum_norm_of_hides_top (P : Finset ℂ) (c : ℂ → ℂ) {R : ℝ} (hR : 1 ≤ R)
    (htop : ∀ q ∈ P, c q ≠ 0 → ‖q‖ = R) (hvis : ∃ q ∈ P, c q ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (M : ℕ) {κ : Type} (u w : κ → ℂ), (∀ l, ‖u l‖ ≤ 1) →
      Summable (fun l => ‖w l‖) →
      (∀ ν, M + 1 ≤ ν → ν ≤ M + P.card → ∑ q ∈ P, c q * q ^ ν + ∑' l, w l * u l ^ ν = 0) →
      ε * R ^ (M + 1) ≤ ∑' l, ‖w l‖ := by
  obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_norm_pointSum P c (by linarith) htop hvis
  refine ⟨ε, hε, fun M κ u w hu hw hhide => ?_⟩
  obtain ⟨ν, h1, h2, h3⟩ := hwin M
  have hrest : ‖∑' l, w l * u l ^ ν‖ ≤ ∑' l, ‖w l‖ := by
    have hb : ∀ l, ‖w l * u l ^ ν‖ ≤ ‖w l‖ := fun l => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hu l))
    exact (norm_tsum_le_tsum_norm (hw.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
      ((hw.of_nonneg_of_le (fun _ => norm_nonneg _) hb).tsum_le_tsum hb hw)
  have heq : ∑ q ∈ P, c q * q ^ ν = -∑' l, w l * u l ^ ν :=
    eq_neg_of_add_eq_zero_left (hhide ν h1 h2)
  rw [heq, norm_neg] at h3
  calc ε * R ^ (M + 1) ≤ ε * R ^ ν := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR h1) hε.le
    _ ≤ ∑' l, ‖w l‖ := h3.trans hrest

end GaloisForLFunctions.InfiniteRankWeilTheory
