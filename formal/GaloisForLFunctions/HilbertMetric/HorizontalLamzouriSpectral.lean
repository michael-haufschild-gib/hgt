import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriUnnormalized

/-!
# Spectral form of the horizontal Lamzouri inequality

Split Lamzouri's packet operator `Φ = Φ_R + Φ_P` into the real points
`Φ_R = Σ c_k w_k ⊗ w_k` (weights `1` or `≥ 2`, simple vectors of norm at most `1`) and the
conjugate pairs `Φ_P = Σ_p 2m_p (g_p ⊗ g_p − h_p ⊗ h_p)`, `m_p ≥ 1`.  Three spectral facts
replace the Gram–Schmidt frames of `HorizontalLamzouriInequality` and
`HorizontalLamzouriUnnormalized`:

* `Φ_P ≤ Σ 2m_p g_p ⊗ g_p` has at most `#pairs` positive eigenvalues; Cauchy–Schwarz on them gives
  `‖Φ_P‖² − 4 tr Φ_P + 2N_P ≥ 4T + ‖Φ_P⁻‖²`, `T = tr Φ_P⁻`, `N_P = 2 Σ m_p`
  (`pair_energy_bound`);
* transporting the atoms of `Φ_R` onto its eigenvalues (`Σ_i p_{ki} ≤ 1`) gives the real four-trace
  bound with the bonus `‖(Φ_R − 2)⁺‖²`, keeping the norm slack `2(1 − ‖f‖²)` of every simple atom
  (`neg_le_sum_lamzouriFourExcess`);
* the negative part of `Φ_P` meets `Φ_R ≤ 2 + (Φ_R − 2)⁺` at cost at most
  `4T + ‖Φ_P⁻‖² + ‖(Φ_R − 2)⁺‖²` (`two_mul_sum_le_cross`).

The three bounds cancel exactly and leave the positive part of the cross term.  Hence

`4·mass − E − 2N + 2 Σ_{x ∈ M} max(G(f_x), 0) ≤ Σ_H (2‖f‖² − 1) + Σ_M (2‖f‖² − 1)`,
`G(ψ) = Σ_p 2m_p (⟪g_p, ψ⟫² − ⟪h_p, ψ⟫²)`

(`HorizontalPacket.spectral_four_mass_bound`; normalised form `spectral_energy_lower_bound`).
A mixed real point costs nothing as soon as `G(f_x) ≥ ‖f_x‖² − 1/2`
(`four_mass_sub_energy_le_of_pairField`), whatever the displacement of its own pair.  For an
isolated mixed class with `⟪h, f⟫ = 0` and `⟪g, f⟫ ≥ ‖f‖²` this always holds, since
`2t² ≥ t − 1/2`.  No orthogonality, independence or normalisation of the vectors is used.
-/

open scoped RealInnerProductSpace
open Finset Module

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Weighted rank-one forms and their diagonalisation -/

section WeightedForm

variable {κ : Type*} [Fintype κ]

/-- The quadratic form `v ↦ Σ_k c_k ⟪w_k, v⟫²` of a weighted family. -/
def weightedForm (c : κ → ℝ) (w : κ → V) (v : V) : ℝ := ∑ k, c k * ⟪w k, v⟫ ^ 2

/-- The operator `v ↦ Σ_k c_k ⟪w_k, v⟫ w_k` of a weighted family. -/
def weightedOp (c : κ → ℝ) (w : κ → V) : V →ₗ[ℝ] V where
  toFun v := ∑ k, (c k * ⟪w k, v⟫) • w k
  map_add' x y := by
    simp only [inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [real_inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; ring

variable (c : κ → ℝ) (w : κ → V)

theorem inner_weightedOp_left (v u : V) :
    ⟪weightedOp c w v, u⟫ = ∑ k, c k * ⟪w k, v⟫ * ⟪w k, u⟫ := by
  simp only [weightedOp, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, real_inner_smul_left]

theorem weightedOp_isSymmetric : (weightedOp c w).IsSymmetric := by
  intro x y
  rw [inner_weightedOp_left, real_inner_comm, inner_weightedOp_left]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem inner_weightedOp_self (v : V) : ⟪weightedOp c w v, v⟫ = weightedForm c w v := by
  rw [inner_weightedOp_left]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Every weighted form is diagonal in an orthonormal basis of eigenvectors. -/
theorem exists_weightedForm_diag [FiniteDimensional ℝ V] :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V, ∃ ev : Fin (finrank ℝ V) → ℝ,
      ∀ v, weightedForm c w v = ∑ i, ev i * ⟪b i, v⟫ ^ 2 := by
  have hT := weightedOp_isSymmetric c w
  refine ⟨hT.eigenvectorBasis rfl, hT.eigenvalues rfl, fun v => ?_⟩
  rw [← inner_weightedOp_self, ← (hT.eigenvectorBasis rfl).sum_inner_mul_inner _ v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT v, hT.apply_eigenvectorBasis, real_inner_smul_right, real_inner_comm v]
  simp only [RCLike.ofReal_real_eq_id, id]
  ring

theorem sum_weightedForm_comm {κ' : Type*} [Fintype κ'] (c' : κ' → ℝ) (w' : κ' → V) :
    ∑ l, c' l * weightedForm c w (w' l) = ∑ k, c k * weightedForm c' w' (w k) := by
  simp_rw [weightedForm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [real_inner_comm]; ring

end WeightedForm

section Basis

variable {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V)

theorem sum_sq_inner_orthonormalBasis (x : V) : ∑ i, ⟪b i, x⟫ ^ 2 = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x x]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm x, sq]

end Basis

section Diag

variable {κ : Type*} [Fintype κ] {n : ℕ} (c : κ → ℝ) (w : κ → V)
  (b : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)
  (hd : ∀ v, weightedForm c w v = ∑ i, ev i * ⟪b i, v⟫ ^ 2)
include hd

theorem weightedForm_basis (j : Fin n) : weightedForm c w (b j) = ev j := by
  rw [hd, Finset.sum_eq_single j]
  · rw [real_inner_self_eq_norm_sq, b.orthonormal.1 j]; ring
  · intro i _ hij
    rw [b.orthonormal.2 hij]; ring
  · simp

/-- The mass of a diagonalised family is the sum of its eigenvalues. -/
theorem sum_weight_mul_norm_sq_eq : ∑ k, c k * ‖w k‖ ^ 2 = ∑ i, ev i := by
  simp_rw [← sum_sq_inner_orthonormalBasis b, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← weightedForm_basis c w b ev hd i, weightedForm]
  exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm]

/-- The energy of a diagonalised family is the sum of its squared eigenvalues. -/
theorem sum_weight_mul_weightedForm_eq : ∑ k, c k * weightedForm c w (w k) = ∑ i, ev i ^ 2 := by
  simp_rw [hd, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := weightedForm_basis c w b ev hd i
  rw [weightedForm] at h
  calc ∑ k, c k * (ev i * ⟪b i, w k⟫ ^ 2) = ev i * ∑ k, c k * ⟪w k, b i⟫ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm]; ring
    _ = ev i ^ 2 := by rw [h]; ring

end Diag

/-! ### The pair part: few positive eigenvalues -/

section PairPart

variable {κ ι : Type*} [Fintype κ] [Fintype ι] {n : ℕ} (c : κ → ℝ) (w : κ → V) (g : ι → V)
  (b : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)

/-- Coordinates, against the vectors `g`, of a combination of eigenvectors with positive
eigenvalue. -/
def positiveEigenCapMap : ({i // 0 < ev i} → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun a p := ⟪g p, ∑ i, a i • b i.1⟫
  map_add' x y := by
    ext p
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, inner_add_right]
  map_smul' r x := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, ← Finset.smul_sum,
      real_inner_smul_right]

omit [Fintype ι] in
theorem inner_basis_sum_positiveEigen (a : {i // 0 < ev i} → ℝ) (j : Fin n) :
    ⟪b j, ∑ i, a i • b i.1⟫ = if h : 0 < ev j then a ⟨j, h⟩ else 0 := by
  simp only [inner_sum, real_inner_smul_right]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · rw [real_inner_self_eq_norm_sq, b.orthonormal.1 j]; ring
    · intro i _ hi
      have : j ≠ i.1 := fun hji => hi (Subtype.ext hji.symm)
      rw [b.orthonormal.2 this]; ring
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : j ≠ i.1 := fun hji => h (hji ▸ i.2)
    rw [b.orthonormal.2 this]; ring

/-- A diagonalised form that is nonpositive on the orthogonal complement of the vectors `g`
has at most `card ι` positive eigenvalues. -/
theorem card_positiveEigen_le (hd : ∀ v, weightedForm c w v = ∑ i, ev i * ⟪b i, v⟫ ^ 2)
    (hcap : ∀ v, (∀ p, ⟪g p, v⟫ = 0) → weightedForm c w v ≤ 0) :
    (univ.filter fun i => 0 < ev i).card ≤ Fintype.card ι := by
  classical
  have hinj : Function.Injective (positiveEigenCapMap g b ev) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    set v := ∑ i, a i • b i.1
    have hle := hcap v fun p => congrFun ha p
    rw [hd] at hle
    have hterm : ∀ j, 0 ≤ ev j * ⟪b j, v⟫ ^ 2 := fun j => by
      rw [inner_basis_sum_positiveEigen b ev a j]
      split_ifs with h
      · exact mul_nonneg h.le (sq_nonneg _)
      · simp
    have hall : ∀ j, ev j * ⟪b j, v⟫ ^ 2 = 0 := fun j => by
      have := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ j)
      linarith [hterm j]
    funext i
    have h := hall i.1
    rw [inner_basis_sum_positiveEigen b ev a i.1, dif_pos i.2] at h
    simpa [i.2.ne'] using h
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype] at this

end PairPart

/-- **Pair energy.**  With at most `P` positive eigenvalues and `2P ≤ N`,
`Σλ² − 4Σλ + 2N ≥ 4T + Σν²` where `ν = λ⁻` and `T = Σν`: the positive eigenvalues carry
`Σλ₊² ≥ (Σλ₊)²/P`, and `(Σλ₊)²/P − 4Σλ₊ + 4P = (Σλ₊ − 2P)²/P`. -/
theorem pair_energy_bound {n : ℕ} (ev : Fin n → ℝ) (P N : ℝ)
    (hk : ((univ.filter fun i => 0 < ev i).card : ℝ) ≤ P) (hN : 2 * P ≤ N) :
    4 * ∑ i, max (-ev i) 0 + ∑ i, max (-ev i) 0 ^ 2 + max (∑ i, ev i - 2 * P) 0 ^ 2 / P ≤
      ∑ i, ev i ^ 2 - 4 * ∑ i, ev i + 2 * N := by
  classical
  set A := ∑ i, max (ev i) 0
  set T := ∑ i, max (-ev i) 0
  set Sp := ∑ i, max (ev i) 0 ^ 2
  set Sn := ∑ i, max (-ev i) 0 ^ 2
  have hsplit : ∀ i, ev i = max (ev i) 0 - max (-ev i) 0 := fun i => by
    rcases le_total 0 (ev i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hsq : ∀ i, ev i ^ 2 = max (ev i) 0 ^ 2 + max (-ev i) 0 ^ 2 := fun i => by
    rcases le_total 0 (ev i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hsum : ∑ i, ev i = A - T := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => hsplit i
  have hsum2 : ∑ i, ev i ^ 2 = Sp + Sn := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => hsq i
  have hSp : 0 ≤ Sp := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA : A = ∑ i ∈ univ.filter (fun i => 0 < ev i), max (ev i) 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · exact max_eq_right (not_lt.mp h)
  have hSp' : ∑ i ∈ univ.filter (fun i => 0 < ev i), max (ev i) 0 ^ 2 ≤ Sp :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => sq_nonneg _)
  have hP : 0 ≤ P := (Nat.cast_nonneg _).trans hk
  have hcs : A ^ 2 ≤ P * Sp := by
    rw [hA]
    calc (∑ i ∈ univ.filter (fun i => 0 < ev i), max (ev i) 0) ^ 2
        ≤ ((univ.filter fun i => 0 < ev i).card : ℝ) *
            ∑ i ∈ univ.filter (fun i => 0 < ev i), max (ev i) 0 ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ P * Sp := mul_le_mul hk hSp' (Finset.sum_nonneg fun i _ => sq_nonneg _) hP
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [hsum, hsum2]
  suffices h : 4 * A + max (A - T - 2 * P) 0 ^ 2 / P ≤ Sp + 4 * P by linarith
  rcases hP.eq_or_lt with h0 | hpos
  · rw [← h0] at hcs
    have hA0 : A = 0 := by nlinarith [sq_nonneg A]
    rw [hA0, ← h0]; simp; linarith
  · have hbonus : max (A - T - 2 * P) 0 ^ 2 ≤ (A - 2 * P) ^ 2 := by
      rcases le_total (A - T - 2 * P) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (A - 2 * P)]
      · rw [max_eq_left h]; nlinarith
    have hsq : (A - 2 * P) ^ 2 / P ≤ Sp - 4 * A + 4 * P := by
      rw [div_le_iff₀ hpos]; nlinarith
    have := div_le_div_of_nonneg_right hbonus hpos.le
    linarith

/-! ### The real part: Lamzouri's bound with the bonus above `2` -/

/-- `x² − 4x − ((x − 2)⁺)² = ((2 − x)⁺)² − 4`: the four-trace excess of an eigenvalue after its
part above `2` is removed. -/
def lamzouriFourExcess (x : ℝ) : ℝ := x ^ 2 - 4 * x - max (x - 2) 0 ^ 2

theorem lamzouriFourExcess_zero : lamzouriFourExcess 0 = 0 := by
  simp [lamzouriFourExcess]

theorem neg_four_le_lamzouriFourExcess (x : ℝ) : -4 ≤ lamzouriFourExcess x := by
  unfold lamzouriFourExcess
  rcases le_total x 2 with h | h
  · rw [max_eq_right (by linarith)]; nlinarith [sq_nonneg (x - 2)]
  · rw [max_eq_left (by linarith)]; nlinarith

theorem tangent_le_lamzouriFourExcess (x : ℝ) : -1 - 2 * x ≤ lamzouriFourExcess x := by
  unfold lamzouriFourExcess
  rcases le_total x 2 with h | h
  · rw [max_eq_right (by linarith)]; nlinarith [sq_nonneg (x - 1)]
  · rw [max_eq_left (by linarith)]; nlinarith

section RealPart

variable {κ : Type*} [Fintype κ] {n : ℕ} (c : κ → ℝ) (w : κ → V)
  (f : OrthonormalBasis (Fin n) ℝ V) (μ : Fin n → ℝ)
  (hd : ∀ v, weightedForm c w v = ∑ i, μ i * ⟪f i, v⟫ ^ 2)
  (hc : ∀ k, c k = 1 ∨ 2 ≤ c k)

omit [Fintype κ] in
theorem weight_pos_of_one_or_two_le (hc : ∀ k, c k = 1 ∨ 2 ≤ c k) (k : κ) : 0 < c k := by
  rcases hc k with h | h <;> linarith

include hd hc

theorem eigen_nonneg_of_weights (i : Fin n) : 0 ≤ μ i := by
  rw [← weightedForm_basis c w f μ hd i]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (weight_pos_of_one_or_two_le c hc k).le (sq_nonneg _)

theorem inner_eq_zero_of_eigen_eq_zero (i : Fin n) (hi : μ i = 0) (k : κ) : ⟪w k, f i⟫ = 0 := by
  have h := weightedForm_basis c w f μ hd i
  rw [hi, weightedForm] at h
  have hterm : ∀ l, 0 ≤ c l * ⟪w l, f i⟫ ^ 2 :=
    fun l => mul_nonneg (weight_pos_of_one_or_two_le c hc l).le (sq_nonneg _)
  have hk : c k * ⟪w k, f i⟫ ^ 2 = 0 := by
    have := Finset.single_le_sum (fun l _ => hterm l) (Finset.mem_univ k)
    linarith [hterm k]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    ((mul_eq_zero.mp hk).resolve_left (weight_pos_of_one_or_two_le c hc k).ne')

omit hd hc in
/-- The transport weights `p_{ki} = c_k ⟪w_k, f_i⟫² / μ_i` from atoms to eigenvalues. -/
def transportWeight (k : κ) (i : Fin n) : ℝ := c k * ⟪w k, f i⟫ ^ 2 / μ i

theorem transportWeight_nonneg (k : κ) (i : Fin n) : 0 ≤ transportWeight c w f μ k i :=
  div_nonneg (mul_nonneg (weight_pos_of_one_or_two_le c hc k).le (sq_nonneg _))
    (eigen_nonneg_of_weights c w f μ hd hc i)

theorem transportWeight_mul_eigen (k : κ) (i : Fin n) :
    transportWeight c w f μ k i * μ i = c k * ⟪w k, f i⟫ ^ 2 := by
  unfold transportWeight
  by_cases hi : μ i = 0
  · rw [inner_eq_zero_of_eigen_eq_zero c w f μ hd hc i hi k, hi]; simp
  · field_simp

omit hc in
theorem sum_atoms_transportWeight (i : Fin n) (F : ℝ → ℝ) (hF : F 0 = 0) :
    ∑ k, transportWeight c w f μ k i * F (μ i) = F (μ i) := by
  by_cases hi : μ i = 0
  · rw [hi, hF]; simp
  · rw [← Finset.sum_mul]
    have : ∑ k, transportWeight c w f μ k i = 1 := by
      unfold transportWeight
      have h := weightedForm_basis c w f μ hd i
      rw [weightedForm] at h
      rw [← Finset.sum_div, h]
      exact div_self hi
    rw [this, one_mul]

theorem sum_transportWeight_mul_eigen (k : κ) :
    ∑ i, transportWeight c w f μ k i * μ i = c k * ‖w k‖ ^ 2 := by
  simp_rw [transportWeight_mul_eigen c w f μ hd hc, ← Finset.mul_sum]
  rw [← sum_sq_inner_orthonormalBasis f (w k)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]

/-- Every atom spends total weight at most one: `Σ_i p_{ki} ≤ 1`.  The test vector
`v = Σ_i (⟪w_k, f_i⟫/μ_i) f_i` has `Q(v) = ⟪w_k, v⟫ = S` and `Q(v) ≥ c_k ⟪w_k, v⟫²`. -/
theorem sum_transportWeight_le_one (k : κ) : ∑ i, transportWeight c w f μ k i ≤ 1 := by
  set S := ∑ i, ⟪w k, f i⟫ ^ 2 / μ i with hS
  have hμ := eigen_nonneg_of_weights c w f μ hd hc
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hμ i)
  set v := ∑ i, (⟪w k, f i⟫ / μ i) • f i
  have hcoord : ∀ j, ⟪f j, v⟫ = ⟪w k, f j⟫ / μ j :=
    fun j => f.orthonormal.inner_right_fintype (fun i => ⟪w k, f i⟫ / μ i) j
  have hform : weightedForm c w v = S := by
    rw [hd]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoord]
    by_cases hj : μ j = 0
    · simp [hj]
    · field_simp
  have hinner : ⟪w k, v⟫ = S := by
    simp only [v, inner_sum, real_inner_smul_right]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsingle : c k * ⟪w k, v⟫ ^ 2 ≤ weightedForm c w v :=
    Finset.single_le_sum (f := fun l => c l * ⟪w l, v⟫ ^ 2)
      (fun l _ => mul_nonneg (weight_pos_of_one_or_two_le c hc l).le (sq_nonneg _))
      (Finset.mem_univ k)
  rw [hform, hinner] at hsingle
  have heq : ∑ i, transportWeight c w f μ k i = c k * S := by
    rw [hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by unfold transportWeight; ring
  rw [heq]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · nlinarith

/-- **Lamzouri's real bound with the bonus above `2`.**  If the weights are `1` or at least `2`,
then `Σ_i (μ_i² − 4μ_i − ((μ_i − 2)⁺)²) ≥ −Σ_k (2c_k + [c_k < 2](2‖w_k‖² − 1))`. -/
theorem neg_le_sum_lamzouriFourExcess :
    -∑ k, (2 * c k + if c k < 2 then 2 * ‖w k‖ ^ 2 - 1 else 0) ≤
      ∑ i, lamzouriFourExcess (μ i) := by
  classical
  have hp := transportWeight_nonneg c w f μ hd hc
  have hswap : ∑ i, lamzouriFourExcess (μ i) =
      ∑ k, ∑ i, transportWeight c w f μ k i * lamzouriFourExcess (μ i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      (sum_atoms_transportWeight c w f μ hd i lamzouriFourExcess lamzouriFourExcess_zero).symm
  rw [hswap, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have hle := sum_transportWeight_le_one c w f μ hd hc k
  have hsum0 : 0 ≤ ∑ i, transportWeight c w f μ k i := Finset.sum_nonneg fun i _ => hp k i
  split_ifs with hk
  · have hc1 : c k = 1 := (hc k).resolve_right (by linarith)
    have hsum := sum_transportWeight_mul_eigen c w f μ hd hc k
    calc -(2 * c k + (2 * ‖w k‖ ^ 2 - 1))
        ≤ ∑ i, transportWeight c w f μ k i * (-1 - 2 * μ i) := by
          have : ∑ i, transportWeight c w f μ k i * (-1 - 2 * μ i) =
              -∑ i, transportWeight c w f μ k i -
                2 * ∑ i, transportWeight c w f μ k i * μ i := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [this, hsum, hc1]; linarith
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (tangent_le_lamzouriFourExcess _) (hp k i)
  · have h2 : 2 ≤ c k := not_lt.mp hk
    calc -(2 * c k + 0) ≤ ∑ i, transportWeight c w f μ k i * (-4) := by
          rw [← Finset.sum_mul]; nlinarith
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (neg_four_le_lamzouriFourExcess _) (hp k i)

end RealPart

/-! ### The cross term -/

/-- **Cross bound.**  A form diagonal in `f` with eigenvalues `μ`, tested against nonnegative
weights `ν_j` on another orthonormal basis `e`, satisfies
`2 Σ_j ν_j Q(e_j) ≤ 4 Σ ν + Σ ν² + Σ ((μ_i − 2)⁺)²`. -/
theorem two_mul_sum_le_cross {κ : Type*} [Fintype κ] {n m : ℕ} (c : κ → ℝ) (w : κ → V)
    (f : OrthonormalBasis (Fin n) ℝ V) (μ : Fin n → ℝ)
    (hd : ∀ v, weightedForm c w v = ∑ i, μ i * ⟪f i, v⟫ ^ 2)
    (e : OrthonormalBasis (Fin m) ℝ V) (ν : Fin m → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    2 * ∑ j, ν j * weightedForm c w (e j) ≤
      4 * ∑ j, ν j + ∑ j, ν j ^ 2 + ∑ i, max (μ i - 2) 0 ^ 2 := by
  set D : Fin n → ℝ := fun i => max (μ i - 2) 0
  set R : Fin m → ℝ := fun j => ∑ i, D i * ⟪f i, e j⟫ ^ 2
  have hpars : ∀ j, ∑ i, ⟪f i, e j⟫ ^ 2 = 1 := fun j => by
    rw [sum_sq_inner_orthonormalBasis, e.orthonormal.1 j, one_pow]
  have hform : ∀ j, weightedForm c w (e j) ≤ 2 + R j := fun j => by
    rw [hd]
    calc ∑ i, μ i * ⟪f i, e j⟫ ^ 2 ≤ ∑ i, (2 + D i) * ⟪f i, e j⟫ ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
            (by simp only [D]; linarith [le_max_left (μ i - 2) 0]) (sq_nonneg _)
      _ = 2 + R j := by
          simp only [R, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hpars j, mul_one]
  have hR2 : ∀ j, R j ^ 2 ≤ ∑ i, D i ^ 2 * ⟪f i, e j⟫ ^ 2 := fun j => by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => D i * ⟪f i, e j⟫)
      (fun i => ⟪f i, e j⟫)
    simp only [R]
    calc (∑ i, D i * ⟪f i, e j⟫ ^ 2) ^ 2
        = (∑ i, D i * ⟪f i, e j⟫ * ⟪f i, e j⟫) ^ 2 := by
          congr 1; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (∑ i, (D i * ⟪f i, e j⟫) ^ 2) * ∑ i, ⟪f i, e j⟫ ^ 2 := this
      _ = ∑ i, D i ^ 2 * ⟪f i, e j⟫ ^ 2 := by
          rw [hpars j, mul_one]; exact Finset.sum_congr rfl fun i _ => by ring
  have hRsum : ∑ j, R j ^ 2 ≤ ∑ i, D i ^ 2 := by
    calc ∑ j, R j ^ 2 ≤ ∑ j, ∑ i, D i ^ 2 * ⟪f i, e j⟫ ^ 2 :=
          Finset.sum_le_sum fun j _ => hR2 j
      _ = ∑ i, D i ^ 2 * ∑ j, ⟪e j, f i⟫ ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
      _ = ∑ i, D i ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sum_sq_inner_orthonormalBasis, f.orthonormal.1 i, one_pow, mul_one]
  have hstep : 2 * ∑ j, ν j * weightedForm c w (e j) ≤ 4 * ∑ j, ν j + 2 * ∑ j, ν j * R j := by
    have : ∑ j, ν j * weightedForm c w (e j) ≤ ∑ j, ν j * (2 + R j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hform j) (hν j)
    have h2 : ∑ j, ν j * (2 + R j) = 2 * ∑ j, ν j + ∑ j, ν j * R j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  have hamgm : 2 * ∑ j, ν j * R j ≤ ∑ j, ν j ^ 2 + ∑ j, R j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (ν j - R j)]
  linarith

/-! ### Assembly -/

/-- **Spectral horizontal Lamzouri inequality, general form.**  Real atoms `w_k` with weights
`1` or `≥ 2` and a pair part whose form is
nonpositive on `{g}^⊥`, with pair count `N_P ≥ 2 card ι`.  For any set `M` of weight-one atoms,
`4 tr − E − 2(Σ c_k + N_P) + 2 Σ_{k ∈ M} max(Q_P(w_k), 0) + ((tr Φ_P − 2 card ι)⁺)² / card ι
≤ Σ_{c_k < 2} (2‖w_k‖² − 1)`.  The last term on the left is the far-pair bonus. -/
theorem spectral_four_trace_bound_general [FiniteDimensional ℝ V]
    {κR κP ι : Type*} [Fintype κR] [Fintype κP] [Fintype ι]
    (cR : κR → ℝ) (wR : κR → V) (cP : κP → ℝ) (wP : κP → V) (g : ι → V) (NP : ℝ)
    (hc : ∀ k, cR k = 1 ∨ 2 ≤ cR k)
    (hcap : ∀ v, (∀ p, ⟪g p, v⟫ = 0) → weightedForm cP wP v ≤ 0)
    (hN : 2 * (Fintype.card ι : ℝ) ≤ NP) (M : Finset κR) (hM : ∀ k ∈ M, cR k = 1) :
    4 * (∑ k, cR k * ‖wR k‖ ^ 2 + ∑ l, cP l * ‖wP l‖ ^ 2)
        - (∑ k, cR k * (weightedForm cR wR (wR k) + weightedForm cP wP (wR k))
          + ∑ l, cP l * (weightedForm cR wR (wP l) + weightedForm cP wP (wP l)))
        - 2 * (∑ k, cR k + NP) + 2 * ∑ k ∈ M, max (weightedForm cP wP (wR k)) 0
        + max (∑ l, cP l * ‖wP l‖ ^ 2 - 2 * Fintype.card ι) 0 ^ 2 / Fintype.card ι
      ≤ ∑ k, if cR k < 2 then 2 * ‖wR k‖ ^ 2 - 1 else 0 := by
  classical
  obtain ⟨f, μ, hdR⟩ := exists_weightedForm_diag cR wR
  obtain ⟨e, ev, hdP⟩ := exists_weightedForm_diag cP wP
  set ν : Fin (finrank ℝ V) → ℝ := fun j => max (-ev j) 0
  set Pp : κR → ℝ := fun k => ∑ j, max (ev j) 0 * ⟪e j, wR k⟫ ^ 2
  have hER := sum_weight_mul_weightedForm_eq cR wR f μ hdR
  have htR := sum_weight_mul_norm_sq_eq cR wR f μ hdR
  have hEP := sum_weight_mul_weightedForm_eq cP wP e ev hdP
  have htP := sum_weight_mul_norm_sq_eq cP wP e ev hdP
  have hX := sum_weightedForm_comm cR wR cP wP
  -- split the cross term into positive and negative spectral parts
  have hXsplit : ∑ k, cR k * weightedForm cP wP (wR k) =
      ∑ k, cR k * Pp k - ∑ j, ν j * weightedForm cR wR (e j) := by
    have h1 : ∀ k, weightedForm cP wP (wR k) = Pp k - ∑ j, ν j * ⟪e j, wR k⟫ ^ 2 := fun k => by
      rw [hdP, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases le_total 0 (ev j) with h | h
      · simp only [ν, max_eq_left h, max_eq_right (by linarith : -ev j ≤ 0)]; ring
      · simp only [ν, max_eq_right h, max_eq_left (by linarith : 0 ≤ -ev j)]; ring
    simp_rw [h1, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp_rw [Finset.mul_sum, weightedForm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [real_inner_comm]; ring
  have hPp0 : ∀ k, 0 ≤ Pp k := fun k =>
    Finset.sum_nonneg fun j _ => mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hPpge : ∀ k, weightedForm cP wP (wR k) ≤ Pp k := fun k => by
    rw [hdP]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hXpos : ∑ k ∈ M, max (weightedForm cP wP (wR k)) 0 ≤ ∑ k, cR k * Pp k := by
    calc ∑ k ∈ M, max (weightedForm cP wP (wR k)) 0 ≤ ∑ k ∈ M, cR k * Pp k :=
          Finset.sum_le_sum fun k hk => by
            rw [hM k hk, one_mul]; exact max_le (hPpge k) (hPp0 k)
      _ ≤ ∑ k, cR k * Pp k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M) fun k _ _ =>
            mul_nonneg (weight_pos_of_one_or_two_le cR hc k).le (hPp0 k)
  -- the three spectral bounds
  have hreal := neg_le_sum_lamzouriFourExcess cR wR f μ hdR hc
  have hsplitR : ∑ k, (2 * cR k + if cR k < 2 then 2 * ‖wR k‖ ^ 2 - 1 else 0) =
      2 * ∑ k, cR k + ∑ k, (if cR k < 2 then 2 * ‖wR k‖ ^ 2 - 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hexc : ∑ i, lamzouriFourExcess (μ i) =
      ∑ i, μ i ^ 2 - 4 * ∑ i, μ i - ∑ i, max (μ i - 2) 0 ^ 2 := by
    simp only [lamzouriFourExcess, Finset.sum_sub_distrib, Finset.mul_sum]
  have hcount := card_positiveEigen_le cP wP g e ev hdP hcap
  have hpair := pair_energy_bound ev (Fintype.card ι) NP (by exact_mod_cast hcount) hN
  have hcross := two_mul_sum_le_cross cR wR f μ hdR e ν fun j => le_max_right _ _
  -- assemble
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hER, hEP, hX, hXsplit, htR, htP]
  rw [hexc, hsplitR] at hreal
  linarith

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP)

/-- The pair field `G(ψ) = Σ_p 2m_p (⟪g_p, ψ⟫² − ⟪h_p, ψ⟫²)`: the quadratic form of the pair
part of the packet operator. -/
def pairField (ψ : V) : ℝ := ∑ p, 2 * P.mP p * (⟪P.g p, ψ⟫ ^ 2 - ⟪P.h p, ψ⟫ ^ 2)

/-- The pair trace `tr Φ_P = Σ_p 2m_p (‖g_p‖² − ‖h_p‖²)`. -/
def pairTrace : ℝ := ∑ p, 2 * P.mP p * (‖P.g p‖ ^ 2 - ‖P.h p‖ ^ 2)

/-- Weights of the real atoms `f₂, fH, fM`. -/
def realWeight : ι₂ ⊕ ιH ⊕ ιM → ℝ := Sum.elim P.m₂ fun _ => 1

/-- The real atoms `f₂, fH, fM`. -/
def realVec : ι₂ ⊕ ιH ⊕ ιM → V := Sum.elim P.f₂ (Sum.elim P.fH P.fM)

/-- Weights `2m, −2m` of the pair vectors `g, h`. -/
def pairWeight : ιP ⊕ ιP → ℝ := Sum.elim (fun p => 2 * P.mP p) fun p => -(2 * P.mP p)

/-- The pair vectors `g, h`. -/
def pairVec : ιP ⊕ ιP → V := Sum.elim P.g P.h

omit [Fintype ι₂] [Fintype ιH] [Fintype ιM] in
theorem pairField_eq (ψ : V) : P.pairField ψ = weightedForm P.pairWeight P.pairVec ψ := by
  simp only [pairField, weightedForm, pairWeight, pairVec, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

theorem diagForm_eq_split (ψ : V) :
    P.diagForm ψ = weightedForm P.realWeight P.realVec ψ +
      weightedForm P.pairWeight P.pairVec ψ := by
  simp only [diagForm, weightedForm, wt, vec, realWeight, realVec, pairWeight, pairVec,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  ring

theorem sum_wt_mul_split (F : V → ℝ) :
    ∑ k, P.wt k * F (P.vec k) =
      ∑ k, P.realWeight k * F (P.realVec k) + ∑ l, P.pairWeight l * F (P.pairVec l) := by
  rw [P.sum_wt_mul]
  simp only [realWeight, realVec, pairWeight, pairVec, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, one_mul, neg_mul, Finset.sum_neg_distrib]
  ring

theorem energy_eq_sum_diagForm : P.energy = ∑ k, P.wt k * P.diagForm (P.vec k) := by
  unfold energy diagForm
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [real_inner_comm]; ring

/-- **Spectral horizontal Lamzouri inequality without normalisations.**  For a packet in a
finite-dimensional space with `m₂ ≥ 2` and `mP ≥ 1`, and no condition on the norms,
`4·mass − E − 2N + 2 Σ_{x ∈ M} max(G(f_x), 0) + ((tr Φ_P − 2P)⁺)²/P
≤ Σ_H (2‖f‖² − 1) + Σ_M (2‖f‖² − 1)`, with `P = #pairs`. -/
theorem spectral_four_mass_bound [FiniteDimensional ℝ V] (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ p, 1 ≤ P.mP p) :
    4 * P.mass - P.energy - 2 * P.count + 2 * ∑ x, max (P.pairField (P.fM x)) 0
        + max (P.pairTrace - 2 * Fintype.card ιP) 0 ^ 2 / Fintype.card ιP
      ≤ ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) := by
  classical
  set M : Finset (ι₂ ⊕ ιH ⊕ ιM) :=
    Finset.univ.map ⟨fun x => Sum.inr (Sum.inr x), fun x y h => by simpa using h⟩
  have hc : ∀ k, P.realWeight k = 1 ∨ 2 ≤ P.realWeight k := by
    rintro (i | j)
    · exact Or.inr (hm₂ i)
    · exact Or.inl rfl
  have hcap : ∀ v, (∀ p, ⟪P.g p, v⟫ = 0) → weightedForm P.pairWeight P.pairVec v ≤ 0 := by
    intro v hv
    rw [← P.pairField_eq, pairField]
    refine Finset.sum_nonpos fun p _ => ?_
    rw [hv p]
    have := hmP p
    nlinarith [sq_nonneg ⟪P.h p, v⟫]
  have hN : 2 * (Fintype.card ιP : ℝ) ≤ 2 * ∑ p, P.mP p := by
    have := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hmP p
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    linarith
  have hMmem : ∀ k ∈ M, P.realWeight k = 1 := by
    intro k hk
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hk
    rfl
  have hmain := spectral_four_trace_bound_general P.realWeight P.realVec P.pairWeight
    P.pairVec P.g (2 * ∑ p, P.mP p) hc hcap hN M hMmem
  have hslack : (∑ k, if P.realWeight k < 2 then 2 * ‖P.realVec k‖ ^ 2 - 1 else 0) =
      ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) := by
    simp only [realWeight, realVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have h₂ : ∀ i, ¬ P.m₂ i < 2 := fun i => not_lt.mpr (hm₂ i)
    simp [h₂]
  have hMsum : ∑ k ∈ M, max (weightedForm P.pairWeight P.pairVec (P.realVec k)) 0 =
      ∑ x, max (P.pairField (P.fM x)) 0 := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun x _ => by rw [P.pairField_eq]; rfl
  have hmass : P.mass = ∑ k, P.realWeight k * ‖P.realVec k‖ ^ 2 +
      ∑ l, P.pairWeight l * ‖P.pairVec l‖ ^ 2 := P.sum_wt_mul_split fun v => ‖v‖ ^ 2
  have henergy : P.energy =
      ∑ k, P.realWeight k * (weightedForm P.realWeight P.realVec (P.realVec k) +
          weightedForm P.pairWeight P.pairVec (P.realVec k)) +
        ∑ l, P.pairWeight l * (weightedForm P.realWeight P.realVec (P.pairVec l) +
          weightedForm P.pairWeight P.pairVec (P.pairVec l)) := by
    rw [P.energy_eq_sum_diagForm, P.sum_wt_mul_split P.diagForm]
    simp only [P.diagForm_eq_split]
  have hcountR : ∑ k, P.realWeight k + 2 * ∑ p, P.mP p = P.count := by
    simp only [count, realWeight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_sum, Nat.cast_add]
    ring
  have htrace : ∑ l, P.pairWeight l * ‖P.pairVec l‖ ^ 2 = P.pairTrace := by
    simp only [pairTrace, pairWeight, pairVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hslack, hMsum, ← hmass, ← henergy, hcountR, htrace] at hmain
  exact hmain

/-- The four-trace count misses `#H` only through mixed points with
`G(f_x) < ‖f_x‖² − 1/2`: `4·mass − E − 2N − Σ_x (2‖f_x‖² − 1 − 2G(f_x))⁺ ≤ #H`. -/
theorem four_mass_sub_energy_le_add_pairField_loss [FiniteDimensional ℝ V]
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p) (hH : ∀ i, ‖P.fH i‖ ≤ 1) :
    4 * P.mass - P.energy - 2 * P.count
        - ∑ x, max (2 * ‖P.fM x‖ ^ 2 - 1 - 2 * P.pairField (P.fM x)) 0
      ≤ (Fintype.card ιH : ℝ) := by
  have h := P.spectral_four_mass_bound hm₂ hmP
  have hb : 0 ≤ max (P.pairTrace - 2 * Fintype.card ιP) 0 ^ 2 / Fintype.card ιP := by positivity
  have hHsum : ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) ≤ (Fintype.card ιH : ℝ) := by
    have : ∀ i, 2 * ‖P.fH i‖ ^ 2 - 1 ≤ 1 := fun i => by
      have := hH i; nlinarith [norm_nonneg (P.fH i)]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hterm : ∀ x, (2 * ‖P.fM x‖ ^ 2 - 1) - 2 * max (P.pairField (P.fM x)) 0 ≤
      max (2 * ‖P.fM x‖ ^ 2 - 1 - 2 * P.pairField (P.fM x)) 0 := fun x => by
    rcases le_total 0 (P.pairField (P.fM x)) with h0 | h0
    · rw [max_eq_left h0]; exact le_max_left _ _
    · rw [max_eq_right h0]
      linarith [le_max_left (2 * ‖P.fM x‖ ^ 2 - 1 - 2 * P.pairField (P.fM x)) 0]
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hterm x
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

/-- **No mixed loss.**  If every mixed point has pair field `G(f_x) ≥ ‖f_x‖² − 1/2` (for instance
`G(f_x) ≥ 1/2` when `‖f_x‖ ≤ 1`), then `4·mass − E − 2N ≤ #H`. -/
theorem four_mass_sub_energy_le_of_pairField [FiniteDimensional ℝ V]
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p) (hH : ∀ i, ‖P.fH i‖ ≤ 1)
    (hG : ∀ x, ‖P.fM x‖ ^ 2 - 1 / 2 ≤ P.pairField (P.fM x)) :
    4 * P.mass - P.energy - 2 * P.count ≤ (Fintype.card ιH : ℝ) := by
  have h := P.four_mass_sub_energy_le_add_pairField_loss hm₂ hmP hH
  have hzero : ∑ x, max (2 * ‖P.fM x‖ ^ 2 - 1 - 2 * P.pairField (P.fM x)) 0 = 0 :=
    Finset.sum_eq_zero fun x _ => max_eq_right (by linarith [hG x])
  linarith

/-- **Normalised form.**  For an admissible packet,
`E ≥ 2N − #H − #M + 2 Σ_{x ∈ M} max(G(f_x), 0)`. -/
theorem spectral_energy_lower_bound [FiniteDimensional ℝ V] (hP : P.Admissible) :
    2 * P.mass - Fintype.card ιH - Fintype.card ιM +
        2 * ∑ x, max (P.pairField (P.fM x)) 0 ≤ P.energy := by
  have h := P.spectral_four_mass_bound hP.two_le_m₂ hP.one_le_mP
  have hb : 0 ≤ max (P.pairTrace - 2 * Fintype.card ιP) 0 ^ 2 / Fintype.card ιP := by positivity
  have hmc : P.mass = P.count := by rw [P.mass_eq hP, count]
  simp only [hP.norm_fH, hP.norm_fM, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  rw [hmc] at h ⊢
  linarith

/-- Normalised packets: mixed points with pair field at least `1/2` cost nothing, so
`2N − E ≤ #H`. -/
theorem card_hs_ge_of_pairField [FiniteDimensional ℝ V] (hP : P.Admissible)
    (hG : ∀ x, 1 / 2 ≤ P.pairField (P.fM x)) :
    2 * P.mass - P.energy ≤ Fintype.card ιH := by
  have h := P.four_mass_sub_energy_le_of_pairField hP.two_le_m₂ hP.one_le_mP
    (fun i => (hP.norm_fH i).le) (fun x => by rw [hP.norm_fM x]; linarith [hG x])
  have hmc : P.mass = P.count := by rw [P.mass_eq hP, count]
  rw [hmc] at h ⊢
  linarith

end HorizontalPacket

end

end GaloisForLFunctions.HilbertMetric
