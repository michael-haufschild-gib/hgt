import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Division-block operators on `ℓ²(ℕ₊)`

For a block size `b ≥ 1` and a bounded weight `w : ℕ → ℂ`, the operator
`(A_w f)(m) = w(m) f(⌊m/b⌋)` on `ℓ²(ℕ₊)` sends the basis vector `e_q` to
`Σ_{r<b} w(qb + r) e_{qb+r}`: distinct columns live on disjoint blocks.  Hence

* `⟪A_w f, A_v g⟫ = Σ_q G_q conj(f q) g q` with the block Gram coefficient
  `G_q = Σ_{r<b} conj(w(qb+r)) v(qb+r)`; a constant `G_q = κ` gives `A_w* A_v = κ I`,
  and block masses `Σ_r |w(qb+r)|² = 1` give isometries;
* `‖A_w f‖² = Σ_q M_q |f q|²` with the block mass `M_q`, so `‖A_w‖² ≤ sup M_q`;
* `A_{b₁,w₁} A_{b₂,w₂} = A_{b₁b₂, w₁ · w₂(⌊·/b₁⌋)}`;
* `A_w` is Hilbert–Schmidt when `Σ_q M_q < ∞`; finitely many blocks give a compact operator.
-/

open Filter Topology
open scoped ComplexConjugate ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace PNatBlock

local notation "ℓ²₊" => lp (fun _ : ℕ+ => ℂ) 2

/-! ## Sums over `ℕ₊` and over division blocks -/

/-- Extension by zero of a family on `ℕ₊` to `ℕ`. -/
def extZero (f : ℕ+ → ℂ) (m : ℕ) : ℂ := if h : 0 < m then f ⟨m, h⟩ else 0

@[simp] theorem extZero_zero (f : ℕ+ → ℂ) : extZero f 0 = 0 := by simp [extZero]

@[simp] theorem extZero_coe (f : ℕ+ → ℂ) (n : ℕ+) : extZero f n = f n := by
  simp only [extZero, n.pos, dif_pos]
  rfl

theorem extZero_add (f g : ℕ+ → ℂ) (m : ℕ) : extZero (f + g) m = extZero f m + extZero g m := by
  unfold extZero; split_ifs <;> simp

theorem extZero_smul (c : ℂ) (f : ℕ+ → ℂ) (m : ℕ) : extZero (c • f) m = c * extZero f m := by
  unfold extZero; split_ifs <;> simp

theorem tsum_pnat {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (F : ℕ → E) (h0 : F 0 = 0) :
    ∑' n : ℕ+, F n = ∑' n : ℕ, F n := by
  rw [tsum_pnat_eq_tsum_succ]
  by_cases hs : Summable F
  · rw [hs.tsum_eq_zero_add, h0, zero_add]
  · rw [tsum_eq_zero_of_not_summable hs,
      tsum_eq_zero_of_not_summable (mt (summable_nat_add_iff 1).1 hs)]

theorem summable_pnat_iff {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (F : ℕ → E) :
    Summable (fun n : ℕ+ => F n) ↔ Summable F := by
  rw [← summable_nat_add_iff 1, ← Equiv.pnatEquivNat.symm.summable_iff]
  rfl

/-- **Division blocks.**  `Σ_m F(m) = Σ_q Σ_{r<b} F(qb + r)`. -/
theorem tsum_block {b : ℕ} [NeZero b] {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → E} (hF : Summable F) :
    ∑' m, F m = ∑' q, ∑ r : Fin b, F (q * b + r) := by
  have hs : Summable fun c : ℕ × Fin b => F ((Nat.divModEquiv b).symm c) :=
    (Nat.divModEquiv b).symm.summable_iff.2 hF
  rw [← (Nat.divModEquiv b).symm.tsum_eq, hs.tsum_prod]
  simp [Nat.divModEquiv_symm_apply, tsum_fintype]

theorem summable_block_iff {b : ℕ} [NeZero b] {F : ℕ → ℝ} (hF : 0 ≤ F) :
    Summable F ↔ Summable fun q => ∑ r : Fin b, F (q * b + r) := by
  rw [← (Nat.divModEquiv b).symm.summable_iff]
  change Summable (fun c : ℕ × Fin b => F ((Nat.divModEquiv b).symm c)) ↔ _
  rw [summable_prod_of_nonneg (fun _ => hF _)]
  simp only [Nat.divModEquiv_symm_apply, tsum_fintype]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => Summable.of_finite, h⟩⟩

theorem div_block {b : ℕ} [NeZero b] (q : ℕ) (r : Fin b) : (q * b + r) / b = q := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt r.isLt, zero_add]

theorem summable_norm_sq_extZero (f : ℓ²₊) : Summable fun m : ℕ => ‖extZero f m‖ ^ 2 := by
  rw [← summable_pnat_iff]
  simpa using summable_norm_sq_lp f

/-! ## Block operators -/

/-- The block mass `Σ_{r<b} ‖w(qb+r)‖²`. -/
def divBlockMass (b : ℕ) (w : ℕ → ℂ) (q : ℕ) : ℝ := ∑ r : Fin b, ‖w (q * b + r)‖ ^ 2

/-- The block Gram coefficient `Σ_{r<b} conj(w(qb+r)) v(qb+r)`. -/
def divBlockGram (b : ℕ) (w v : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ r : Fin b, conj (w (q * b + r)) * v (q * b + r)

theorem divBlockMass_nonneg (b : ℕ) (w : ℕ → ℂ) (q : ℕ) : 0 ≤ divBlockMass b w q :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem divBlockGram_self (b : ℕ) (w : ℕ → ℂ) (q : ℕ) :
    divBlockGram b w w q = (divBlockMass b w q : ℂ) := by
  simp only [divBlockGram, divBlockMass, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

theorem divBlockMass_le {b : ℕ} {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K) (q : ℕ) :
    divBlockMass b w q ≤ b * K ^ 2 := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hw 0)
  calc divBlockMass b w q ≤ ∑ _r : Fin b, K ^ 2 :=
        Finset.sum_le_sum fun r _ => pow_le_pow_left₀ (norm_nonneg _) (hw _) 2
    _ = b * K ^ 2 := by simp

/-- The coordinates `m ↦ w(m) f(⌊m/b⌋)`. -/
def divBlockFun (b : ℕ) (w : ℕ → ℂ) (f : ℕ+ → ℂ) (m : ℕ) : ℂ := w m * extZero f (m / b)

theorem divBlockFun_zero (b : ℕ) (w : ℕ → ℂ) (f : ℕ+ → ℂ) : divBlockFun b w f 0 = 0 := by
  simp [divBlockFun]

theorem divBlockFun_block {b : ℕ} [NeZero b] (w : ℕ → ℂ) (f : ℕ+ → ℂ) (q : ℕ) (r : Fin b) :
    divBlockFun b w f (q * b + r) = w (q * b + r) * extZero f q := by
  rw [divBlockFun, div_block]

theorem sum_norm_sq_divBlockFun {b : ℕ} [NeZero b] (w : ℕ → ℂ) (f : ℕ+ → ℂ) (q : ℕ) :
    ∑ r : Fin b, ‖divBlockFun b w f (q * b + r)‖ ^ 2 = divBlockMass b w q * ‖extZero f q‖ ^ 2 := by
  simp only [divBlockFun_block, norm_mul, mul_pow, divBlockMass, Finset.sum_mul]

theorem summable_divBlockFun_sq {b : ℕ} [NeZero b] {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (f : ℓ²₊) : Summable fun m : ℕ => ‖divBlockFun b w f m‖ ^ 2 := by
  rw [summable_block_iff (b := b) (F := fun m => ‖divBlockFun b w f m‖ ^ 2) (fun m => sq_nonneg _)]
  simp_rw [sum_norm_sq_divBlockFun]
  exact Summable.of_nonneg_of_le (fun q => mul_nonneg (divBlockMass_nonneg _ _ _) (sq_nonneg _))
    (fun q => mul_le_mul_of_nonneg_right (divBlockMass_le hw q) (sq_nonneg _))
    ((summable_norm_sq_extZero f).mul_left _)

theorem tsum_norm_sq_divBlockFun {b : ℕ} [NeZero b] {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (f : ℓ²₊) : ∑' m : ℕ, ‖divBlockFun b w f m‖ ^ 2 = ∑' q : ℕ, divBlockMass b w q * ‖extZero f q‖ ^ 2 := by
  have hr : ∑' m : ℕ, ‖divBlockFun b w f m‖ ^ 2 =
      ∑' q : ℕ, ∑ r : Fin b, ‖divBlockFun b w f (q * b + r)‖ ^ 2 := tsum_block (summable_divBlockFun_sq hw f)
  rw [hr]
  simp_rw [sum_norm_sq_divBlockFun]

theorem norm_sq_eq_tsum_extZero (f : ℓ²₊) : ‖f‖ ^ 2 = ∑' q : ℕ, ‖extZero f q‖ ^ 2 := by
  have h : ‖f‖ ^ (2 : ℝ) = ∑' n : ℕ+, ‖f n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ+ => ℂ) (by norm_num) f
  simp only [Real.rpow_two] at h
  rw [h, ← tsum_pnat (fun q => ‖extZero f q‖ ^ 2) (by simp)]
  simp

/-- The block operator `f ↦ (m ↦ w(m) f(⌊m/b⌋))` for a bounded weight. -/
def divBlockLinearMap (b : ℕ) [NeZero b] (w : ℕ → ℂ) {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K) :
    ℓ²₊ →ₗ[ℂ] ℓ²₊ where
  toFun f := ⟨fun m : ℕ+ => divBlockFun b w f m, memℓp_gen (by
    have := (summable_pnat_iff _).2 (summable_divBlockFun_sq (b := b) hw f)
    simpa [Real.rpow_two] using this)⟩
  map_add' f g := by
    ext m
    simp only [lp.coeFn_add, Pi.add_apply]
    show divBlockFun b w (⇑f + ⇑g) m = divBlockFun b w f m + divBlockFun b w g m
    simp [divBlockFun, extZero_add, mul_add]
  map_smul' c f := by
    ext m
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    show divBlockFun b w (c • ⇑f) m = c * divBlockFun b w f m
    simp only [divBlockFun, extZero_smul]
    ring

theorem norm_sq_divBlockLinearMap (b : ℕ) [NeZero b] {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (f : ℓ²₊) :
    ‖divBlockLinearMap b w hw f‖ ^ 2 = ∑' q : ℕ, divBlockMass b w q * ‖extZero f q‖ ^ 2 := by
  rw [norm_sq_eq_tsum_extZero, ← tsum_norm_sq_divBlockFun hw f]
  congr 1
  funext m
  congr 2
  unfold extZero
  split_ifs with h
  · rfl
  · have : m = 0 := by omega
    subst this
    simp [divBlockFun]

open Classical in
/-- The bounded block operator. -/
def divBlockOp (b : ℕ) (w : ℕ → ℂ) : ℓ²₊ →L[ℂ] ℓ²₊ :=
  if h : 0 < b ∧ ∃ K, ∀ m, ‖w m‖ ≤ K then
    haveI : NeZero b := ⟨h.1.ne'⟩
    (divBlockLinearMap b w h.2.choose_spec).mkContinuous (Real.sqrt b * h.2.choose) fun f => by
      have hK : 0 ≤ h.2.choose := (norm_nonneg _).trans (h.2.choose_spec 0)
      have hsq := norm_sq_divBlockLinearMap b h.2.choose_spec f
      have hle : ‖divBlockLinearMap b w h.2.choose_spec f‖ ^ 2 ≤ (Real.sqrt b * h.2.choose * ‖f‖) ^ 2 := by
        rw [hsq, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), norm_sq_eq_tsum_extZero, ← tsum_mul_left]
        refine Summable.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_right (divBlockMass_le h.2.choose_spec q)
          (sq_nonneg _)) ?_ ((summable_norm_sq_extZero f).mul_left _)
        exact Summable.of_nonneg_of_le (fun q => mul_nonneg (divBlockMass_nonneg _ _ _) (sq_nonneg _))
          (fun q => mul_le_mul_of_nonneg_right (divBlockMass_le h.2.choose_spec q) (sq_nonneg _))
          ((summable_norm_sq_extZero f).mul_left _)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle
  else 0

theorem divBlockOp_apply {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K) (f : ℓ²₊)
    (m : ℕ+) : (divBlockOp b w f : ℕ+ → ℂ) m = w m * extZero f (m / b) := by
  have h : 0 < b ∧ ∃ K, ∀ m, ‖w m‖ ≤ K := ⟨hb, K, hw⟩
  rw [divBlockOp, dif_pos h]
  rfl

theorem extZero_divBlockOp {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K) (f : ℓ²₊)
    (m : ℕ) : extZero (divBlockOp b w f) m = w m * extZero f (m / b) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : extZero (divBlockOp b w f) m = (divBlockOp b w f : ℕ+ → ℂ) ⟨m, hm⟩ := by simp [extZero, hm]
    rw [h1, divBlockOp_apply hb hw]
    rfl

theorem norm_sq_divBlockOp {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (f : ℓ²₊) : ‖divBlockOp b w f‖ ^ 2 = ∑' q : ℕ, divBlockMass b w q * ‖extZero f q‖ ^ 2 := by
  haveI : NeZero b := ⟨hb.ne'⟩
  have h : 0 < b ∧ ∃ K, ∀ m, ‖w m‖ ≤ K := ⟨hb, K, hw⟩
  have := norm_sq_divBlockLinearMap b h.2.choose_spec f
  rw [divBlockOp, dif_pos h]
  exact this

/-! ## Gram identities -/

theorem inner_eq_tsum_ext (f g : ℓ²₊) : inner ℂ f g = ∑' q : ℕ, conj (extZero f q) * extZero g q := by
  rw [lp.inner_eq_tsum, ← tsum_pnat (fun q => conj (extZero f q) * extZero g q) (by simp)]
  simp [RCLike.inner_apply, mul_comm]

/-- **Block Gram identity.**  `⟪A_w f, A_v g⟫ = Σ_q G_q(w,v) conj(f q) g q`. -/
theorem inner_divBlockOp {b : ℕ} (hb : 0 < b) {w v : ℕ → ℂ} {K L : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (hv : ∀ m, ‖v m‖ ≤ L) (f g : ℓ²₊) :
    inner ℂ (divBlockOp b w f) (divBlockOp b v g) =
      ∑' q : ℕ, divBlockGram b w v q * (conj (extZero f q) * extZero g q) := by
  haveI : NeZero b := ⟨hb.ne'⟩
  rw [lp.inner_eq_tsum]
  have hterm : ∀ m : ℕ+, inner ℂ ((divBlockOp b w f : ℕ+ → ℂ) m) ((divBlockOp b v g : ℕ+ → ℂ) m) =
      conj (divBlockFun b w f m) * divBlockFun b v g m := fun m => by
    rw [divBlockOp_apply hb hw, divBlockOp_apply hb hv, RCLike.inner_apply]
    simp only [divBlockFun]
    ring
  simp_rw [hterm]
  rw [tsum_pnat (fun m => conj (divBlockFun b w f m) * divBlockFun b v g m) (by simp [divBlockFun_zero])]
  have hs : Summable fun m => conj (divBlockFun b w f m) * divBlockFun b v g m :=
    Summable.of_norm_bounded
      (((summable_divBlockFun_sq (b := b) hw f).add (summable_divBlockFun_sq (b := b) hv g)).div_const 2)
        fun m => by
          have h := two_mul_le_add_sq ‖divBlockFun b w f m‖ ‖divBlockFun b v g m‖
          simp only [norm_mul, Complex.norm_conj]
          linarith
  rw [tsum_block (b := b) hs]
  congr 1
  funext q
  simp only [divBlockGram, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [divBlockFun, div_block, map_mul]
  ring

theorem inner_divBlockOp_of_divBlockGram {b : ℕ} (hb : 0 < b) {w v : ℕ → ℂ} {K L : ℝ}
    (hw : ∀ m, ‖w m‖ ≤ K) (hv : ∀ m, ‖v m‖ ≤ L) {κ : ℂ} (hG : ∀ q, 0 < q → divBlockGram b w v q = κ)
    (f g : ℓ²₊) : inner ℂ (divBlockOp b w f) (divBlockOp b v g) = κ * inner ℂ f g := by
  rw [inner_divBlockOp hb hw hv, inner_eq_tsum_ext, ← tsum_mul_left]
  congr 1
  funext q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · rw [hG q hq]

/-- A constant block Gram coefficient gives `A_w* A_v = κ I`. -/
theorem adjoint_comp_divBlockOp {b : ℕ} (hb : 0 < b) {w v : ℕ → ℂ} {K L : ℝ}
    (hw : ∀ m, ‖w m‖ ≤ K) (hv : ∀ m, ‖v m‖ ≤ L) {κ : ℂ} (hG : ∀ q, 0 < q → divBlockGram b w v q = κ) :
    (divBlockOp b w).adjoint ∘L divBlockOp b v = κ • ContinuousLinearMap.id ℂ ℓ²₊ := by
  ext1 g
  refine ext_inner_left ℂ fun f => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_divBlockOp_of_divBlockGram hb hw hv hG]
  simp [inner_smul_right]

theorem norm_divBlockOp_apply_of_divBlockMass {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ}
    (hw : ∀ m, ‖w m‖ ≤ K) (hM : ∀ q, 0 < q → divBlockMass b w q = 1) (f : ℓ²₊) :
    ‖divBlockOp b w f‖ = ‖f‖ := by
  have h : ‖divBlockOp b w f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sq_divBlockOp hb hw, norm_sq_eq_tsum_extZero]
    congr 1
    funext q
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · rw [hM q hq, one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem norm_divBlockOp_le {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ q, 0 < q → divBlockMass b w q ≤ M) : ‖divBlockOp b w‖ ≤ Real.sqrt M := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun f => ?_
  have hle : ‖divBlockOp b w f‖ ^ 2 ≤ (Real.sqrt M * ‖f‖) ^ 2 := by
    rw [norm_sq_divBlockOp hb hw, mul_pow, Real.sq_sqrt hM0, norm_sq_eq_tsum_extZero, ← tsum_mul_left]
    have hs := summable_norm_sq_extZero f
    refine Summable.tsum_le_tsum (fun q => ?_) ?_ (hs.mul_left M)
    · rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · exact mul_le_mul_of_nonneg_right (hM q hq) (sq_nonneg _)
    · haveI : NeZero b := ⟨hb.ne'⟩
      exact Summable.of_nonneg_of_le (fun q => mul_nonneg (divBlockMass_nonneg _ _ _) (sq_nonneg _))
        (fun q => mul_le_mul_of_nonneg_right (divBlockMass_le hw q) (sq_nonneg _)) (hs.mul_left _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

/-! ## Basis vectors -/

theorem extZero_single (n : ℕ+) (q : ℕ) :
    extZero (lp.single 2 n (1 : ℂ) : lp (fun _ : ℕ+ => ℂ) 2) q = if q = n then 1 else 0 := by
  classical
  by_cases h : q = n
  · subst h
    simp [lp.single_apply]
  · rw [if_neg h]
    unfold extZero
    split_ifs with h1
    · rw [lp.single_apply, Pi.single_eq_of_ne]
      intro h'
      exact h (congrArg PNat.val h')
    · rfl

theorem norm_sq_divBlockOp_single {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (n : ℕ+) : ‖divBlockOp b w (lp.single 2 n (1 : ℂ))‖ ^ 2 = divBlockMass b w n := by
  rw [norm_sq_divBlockOp hb hw, tsum_eq_single (n : ℕ) fun q hq => by simp [extZero_single, hq]]
  simp

theorem divBlockOp_single_apply {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (n m : ℕ+) : (divBlockOp b w (lp.single 2 n (1 : ℂ)) : ℕ+ → ℂ) m =
      if (m : ℕ) / b = n then w m else 0 := by
  rw [divBlockOp_apply hb hw, extZero_single]
  split_ifs <;> simp

/-! ## Algebra of block operators -/

theorem divBlockOp_add {b : ℕ} (hb : 0 < b) {w v : ℕ → ℂ} {K L : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (hv : ∀ m, ‖v m‖ ≤ L) : divBlockOp b (w + v) = divBlockOp b w + divBlockOp b v := by
  have hwv : ∀ m, ‖(w + v) m‖ ≤ K + L := fun m => (norm_add_le _ _).trans (add_le_add (hw m) (hv m))
  ext1 f
  ext m
  simp only [add_apply, lp.coeFn_add, Pi.add_apply, divBlockOp_apply hb hwv,
    divBlockOp_apply hb hw, divBlockOp_apply hb hv]
  ring

theorem divBlockOp_smul {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K) (c : ℂ) :
    divBlockOp b (c • w) = c • divBlockOp b w := by
  have hcw : ∀ m, ‖(c • w) m‖ ≤ ‖c‖ * K := fun m => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hw m) (norm_nonneg _)
  ext1 f
  ext m
  simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply, divBlockOp_apply hb hcw,
    divBlockOp_apply hb hw, smul_eq_mul]
  ring

theorem divBlockOp_sub {b : ℕ} (hb : 0 < b) {w v : ℕ → ℂ} {K L : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (hv : ∀ m, ‖v m‖ ≤ L) : divBlockOp b (w - v) = divBlockOp b w - divBlockOp b v := by
  have hwv : ∀ m, ‖(w - v) m‖ ≤ K + L := fun m => (norm_sub_le _ _).trans (add_le_add (hw m) (hv m))
  ext1 f
  ext m
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, divBlockOp_apply hb hwv,
    divBlockOp_apply hb hw, divBlockOp_apply hb hv]
  ring

/-- **Composition.**  `A_{b₁,w₁} A_{b₂,w₂} = A_{b₁b₂, w₁ · w₂(⌊·/b₁⌋)}`. -/
theorem divBlockOp_comp {b₁ b₂ : ℕ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) {w₁ w₂ : ℕ → ℂ} {K₁ K₂ : ℝ}
    (hw₁ : ∀ m, ‖w₁ m‖ ≤ K₁) (hw₂ : ∀ m, ‖w₂ m‖ ≤ K₂) :
    divBlockOp b₁ w₁ ∘L divBlockOp b₂ w₂ = divBlockOp (b₁ * b₂) (fun m => w₁ m * w₂ (m / b₁)) := by
  have hw : ∀ m, ‖w₁ m * w₂ (m / b₁)‖ ≤ K₁ * K₂ := fun m => by
    rw [norm_mul]
    exact mul_le_mul (hw₁ m) (hw₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hw₁ 0))
  ext1 f
  ext m
  rw [ContinuousLinearMap.comp_apply, divBlockOp_apply hb₁ hw₁, extZero_divBlockOp hb₂ hw₂,
    divBlockOp_apply (Nat.mul_pos hb₁ hb₂) hw, Nat.div_div_eq_div_mul]
  ring

/-! ## Hilbert–Schmidt block operators and finite truncations -/

theorem isHilbertSchmidt_divBlockOp {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ} (hw : ∀ m, ‖w m‖ ≤ K)
    (hs : Summable fun q : ℕ => divBlockMass b w q) :
    ContinuousLinearMap.IsHilbertSchmidt (divBlockOp b w) := by
  classical
  refine ContinuousLinearMap.isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis ℕ+) ?_
  simp_rw [HilbertSchmidt.lpBasis_apply, norm_sq_divBlockOp_single hb hw]
  exact (summable_pnat_iff (fun q => divBlockMass b w q)).2 hs

/-- A block operator supported on finitely many blocks is Hilbert–Schmidt, hence compact. -/
theorem isCompactOperator_divBlockOp_of_le {b : ℕ} (hb : 0 < b) {w : ℕ → ℂ} {K : ℝ}
    (hw : ∀ m, ‖w m‖ ≤ K) {N : ℕ} (hN : ∀ m, N < m / b → w m = 0) :
    IsCompactOperator (divBlockOp b w) := by
  refine (isHilbertSchmidt_divBlockOp hb hw ?_).isCompactOperator
  refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun q hq => ?_
  haveI : NeZero b := ⟨hb.ne'⟩
  have hqN : N < q := by simpa using hq
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [hN _ (by rw [div_block]; exact hqN), norm_zero]
  norm_num

end PNatBlock

end

end GaloisForLFunctions.HTGeometry
