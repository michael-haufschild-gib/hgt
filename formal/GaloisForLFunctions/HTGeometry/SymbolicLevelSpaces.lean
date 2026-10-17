import GaloisForLFunctions.HTGeometry.SymbolicTransferOperator
import GaloisForLFunctions.HTGeometry.FiniteRankTraceDeterminant

/-!
# Level spaces, cylinder averages and the trace of a locally constant transfer operator

`levelSpace A ϑ n` (`V_n`) is the space of Hölder functions depending only on the first `n` symbols.
It is finite dimensional: evaluation at chosen points of the admissible cylinders is a linear
isomorphism onto the functions on admissible words (`levelEquiv`), with inverse the combinations of
cylinder indicators.  Consequently the trace of an endomorphism of `V_n` is
`Σ_u (X χ_u)(p_u)` (`trace_levelSpace_eq`).

* `cylAverage N` (`E_N`): `E_N f(y) = f(π_N y)`, of norm `≤ 1`, onto `V_N`, with
  `|f − E_N f| ≤ ‖f‖ ϑ^N`.
* `transferOp_mem_levelSpace`: the transfer operator of an `m`-local potential maps `V_j` into
  `V_J` for `J ≥ 1`, `m, j ≤ J + 1`.
* `trace_transferOp_pow_levelSpace`: for an `m`-local potential with `m ≤ n + 1`,
  `tr(Lⁿ|_{V_n}) = Σ_{σⁿp = p} e^{−s φⁿ(p)}`.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset Module

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop} {ϑ : ℝ}

/-! ## Level spaces -/

variable (A ϑ) in
/-- `V_m`: the Hölder functions depending only on the first `m` symbols. -/
def levelSpace (m : ℕ) : Submodule ℂ (HolderSpace A ϑ) where
  carrier := {f | ∀ x y, IsAdmissible A x → IsAdmissible A y → Agree m x y → f x = f y}
  add_mem' := by
    intro f g hf hg x y hx hy h
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [add_apply, add_apply, hf x y hx hy h, hg x y hx hy h]
  zero_mem' := by intro x y _ _ _; rfl
  smul_mem' := by
    intro c f hf x y hx hy h
    simp only [Set.mem_setOf_eq] at hf ⊢
    rw [smul_apply, smul_apply, hf x y hx hy h]

theorem mem_levelSpace {m : ℕ} {f : HolderSpace A ϑ} :
    f ∈ levelSpace A ϑ m ↔
      ∀ x y, IsAdmissible A x → IsAdmissible A y → Agree m x y → f x = f y := Iff.rfl

theorem levelSpace_mono {m m' : ℕ} (h : m ≤ m') : levelSpace A ϑ m ≤ levelSpace A ϑ m' :=
  fun _ hf x y hx hy hxy => hf x y hx hy (hxy.mono h)

variable (A) in
/-- Words of length `n` that begin some admissible sequence. -/
def AdmWord (n : ℕ) : Type :=
  {u : Fin n → Fin k // ∃ z, IsAdmissible A z ∧ ∀ i : Fin n, z i = u i}

instance (n : ℕ) : Fintype (AdmWord A n) := by
  classical
  unfold AdmWord
  infer_instance

instance (n : ℕ) : DecidableEq (AdmWord A n) := by
  classical
  unfold AdmWord
  infer_instance

theorem card_admWord_le (n : ℕ) : Fintype.card (AdmWord A n) ≤ k ^ n := by
  classical
  unfold AdmWord
  calc Fintype.card {u : Fin n → Fin k // ∃ z, IsAdmissible A z ∧ ∀ i : Fin n, z i = u i}
      ≤ Fintype.card (Fin n → Fin k) := Fintype.card_subtype_le _
    _ = k ^ n := by simp

/-- A chosen admissible point of the cylinder of an admissible word. -/
def AdmWord.pt {n : ℕ} (u : AdmWord A n) : ℕ → Fin k := Classical.choose u.2

theorem AdmWord.pt_spec {n : ℕ} (u : AdmWord A n) :
    IsAdmissible A u.pt ∧ ∀ i : Fin n, u.pt i = u.1 i := Classical.choose_spec u.2

/-- The word of the first `n` symbols of an admissible sequence. -/
def AdmWord.ofSeq (n : ℕ) {y : ℕ → Fin k} (hy : IsAdmissible A y) : AdmWord A n :=
  ⟨fun i => y i, y, hy, fun _ => rfl⟩

/-! ## Cylinder indicators -/

open Classical in
/-- The indicator of the admissible part of the cylinder of a word, as a function. -/
def cylFun {n : ℕ} (u : Fin n → Fin k) : (ℕ → Fin k) → ℂ :=
  fun y => if IsAdmissible A y ∧ ∀ i : Fin n, y i = u i then 1 else 0

open Classical in
/-- The **cylinder indicator** `χ_u` in the Hölder space, of norm at most `ϑ^{−n}`. -/
def cylIndicator (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {n : ℕ} (u : Fin n → Fin k) : HolderSpace A ϑ :=
  mk hϑ (cylFun (A := A) u)
    (fun y hy => by simp [cylFun, hy])
    ((ϑ ^ n)⁻¹)
    (fun y => by
      have h1 : (1 : ℝ) ≤ (ϑ ^ n)⁻¹ := one_le_inv₀ (pow_pos hϑ n) |>.mpr (pow_le_one₀ hϑ.le hϑ1)
      unfold cylFun
      split_ifs <;> simp [h1, le_trans zero_le_one h1])
    (fun x y j hx hy hxy => by
      by_cases hjn : n ≤ j
      · have : cylFun (A := A) u x = cylFun (A := A) u y := by
          unfold cylFun
          have hiff : (∀ i : Fin n, x i = u i) ↔ (∀ i : Fin n, y i = u i) :=
            ⟨fun h i => (hxy i (by omega)).symm.trans (h i),
              fun h i => (hxy i (by omega)).trans (h i)⟩
          simp only [hx, hy, true_and, hiff]
        rw [this, sub_self, norm_zero]
        positivity
      · have hle : ‖cylFun (A := A) u x - cylFun (A := A) u y‖ ≤ 1 := by
          unfold cylFun
          split_ifs <;> simp
        refine hle.trans ?_
        rw [inv_mul_eq_div, le_div_iff₀ (pow_pos hϑ n), one_mul]
        exact pow_le_pow_of_le_one hϑ.le hϑ1 (by omega))

theorem cylIndicator_apply (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {n : ℕ} (u : Fin n → Fin k)
    (y : ℕ → Fin k) : cylIndicator (A := A) hϑ hϑ1 u y = cylFun (A := A) u y := rfl

theorem cylFun_of_adm {n : ℕ} (u : Fin n → Fin k) {y : ℕ → Fin k} (hy : IsAdmissible A y) :
    cylFun (A := A) u y = if ∀ i : Fin n, y i = u i then 1 else 0 := by
  classical
  unfold cylFun
  simp only [hy, true_and]

theorem cylIndicator_mem (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {n : ℕ} (u : Fin n → Fin k) :
    cylIndicator (A := A) hϑ hϑ1 u ∈ levelSpace A ϑ n := by
  intro x y hx hy hxy
  rw [cylIndicator_apply, cylIndicator_apply, cylFun_of_adm u hx, cylFun_of_adm u hy]
  have hiff : (∀ i : Fin n, x i = u i) ↔ (∀ i : Fin n, y i = u i) :=
    ⟨fun h i => (hxy i i.2).symm.trans (h i), fun h i => (hxy i i.2).trans (h i)⟩
  simp only [hiff]

theorem finset_sum_apply {ι : Type*} (s : Finset ι) (g : ι → HolderSpace A ϑ) (y : ℕ → Fin k) :
    (∑ i ∈ s, g i) y = ∑ i ∈ s, g i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, add_apply, ih, Finset.sum_insert ha]

/-- Evaluation at the chosen points of the admissible cylinders is injective on `V_n`. -/
theorem levelSpace_eval_injective (n : ℕ) :
    Function.Injective fun f : levelSpace A ϑ n => fun u : AdmWord A n => (f : HolderSpace A ϑ) u.pt := by
  intro f g h
  apply Subtype.ext
  ext y
  by_cases hy : IsAdmissible A y
  · have hu := congrFun h (AdmWord.ofSeq n hy)
    have hpt := AdmWord.pt_spec (AdmWord.ofSeq n hy)
    have hag : Agree n (AdmWord.ofSeq n hy).pt y := fun i hi => hpt.2 ⟨i, hi⟩
    simp only at hu
    rw [← f.2 _ _ hpt.1 hy hag, ← g.2 _ _ hpt.1 hy hag]
    exact hu
  · rw [apply_of_not_adm _ hy, apply_of_not_adm _ hy]

/-- The evaluation map `V_n → (admissible words → ℂ)`. -/
def levelEval (n : ℕ) : levelSpace A ϑ n →ₗ[ℂ] (AdmWord A n → ℂ) where
  toFun f u := (f : HolderSpace A ϑ) u.pt
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance (n : ℕ) : FiniteDimensional ℂ (levelSpace A ϑ n) :=
  Module.Finite.of_injective (levelEval n) (levelSpace_eval_injective n)

theorem finrank_levelSpace_le (n : ℕ) : finrank ℂ (levelSpace A ϑ n) ≤ k ^ n := by
  calc finrank ℂ (levelSpace A ϑ n) ≤ finrank ℂ (AdmWord A n → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective (f := levelEval n) (levelSpace_eval_injective n)
    _ = Fintype.card (AdmWord A n) := Module.finrank_fintype_fun_eq_card ℂ
    _ ≤ k ^ n := card_admWord_le n

theorem isClosed_levelSpace (n : ℕ) : IsClosed (levelSpace A ϑ n : Set (HolderSpace A ϑ)) :=
  Submodule.closed_of_finiteDimensional _

theorem cylFun_pt {n : ℕ} (u v : AdmWord A n) :
    cylFun (A := A) v.1 u.pt = if u = v then 1 else 0 := by
  have hpt := AdmWord.pt_spec u
  rw [cylFun_of_adm v.1 hpt.1]
  by_cases huv : u = v
  · subst huv; simp [hpt.2]
  · rw [if_neg huv, if_neg]
    intro h
    apply huv
    apply Subtype.ext
    funext i
    rw [← hpt.2 i, h i]

/-- **The level space is the space of functions on admissible words.** -/
def levelEquiv (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (n : ℕ) : levelSpace A ϑ n ≃ₗ[ℂ] (AdmWord A n → ℂ) :=
  { levelEval n with
    invFun := fun c => ⟨∑ u, c u • cylIndicator hϑ hϑ1 u.1,
      Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (cylIndicator_mem hϑ hϑ1 u.1)⟩
    left_inv := fun f => by
      apply levelSpace_eval_injective n
      funext u
      show ((∑ v : AdmWord A n, ((f : HolderSpace A ϑ) v.pt) • cylIndicator hϑ hϑ1 v.1 :
        HolderSpace A ϑ)) u.pt = _
      rw [finset_sum_apply, Finset.sum_eq_single u]
      · rw [smul_apply, cylIndicator_apply, cylFun_pt, if_pos rfl, mul_one]
      · intro v _ hvu
        rw [smul_apply, cylIndicator_apply, cylFun_pt, if_neg (Ne.symm hvu), mul_zero]
      · simp
    right_inv := fun c => by
      funext u
      show ((∑ v : AdmWord A n, c v • cylIndicator hϑ hϑ1 v.1 : HolderSpace A ϑ)) u.pt = c u
      rw [finset_sum_apply, Finset.sum_eq_single u]
      · rw [smul_apply, cylIndicator_apply, cylFun_pt, if_pos rfl, mul_one]
      · intro v _ hvu
        rw [smul_apply, cylIndicator_apply, cylFun_pt, if_neg (Ne.symm hvu), mul_zero]
      · simp }

/-- **The trace on a level space** is `Σ_u (X χ_u)(p_u)`. -/
theorem trace_levelSpace_eq (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (n : ℕ)
    (X : Module.End ℂ (levelSpace A ϑ n)) :
    LinearMap.trace ℂ (levelSpace A ϑ n) X = ∑ u : AdmWord A n,
      ((X ⟨cylIndicator hϑ hϑ1 u.1, cylIndicator_mem hϑ hϑ1 u.1⟩ : levelSpace A ϑ n) :
        HolderSpace A ϑ) u.pt := by
  classical
  rw [← LinearMap.trace_conj' X (levelEquiv hϑ hϑ1 n),
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (AdmWord A n)), Matrix.trace]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    LinearEquiv.conj_apply]
  have hsymm : (levelEquiv hϑ hϑ1 n).symm (Pi.single u 1 : AdmWord A n → ℂ) =
      ⟨cylIndicator hϑ hϑ1 u.1, cylIndicator_mem hϑ hϑ1 u.1⟩ := by
    apply Subtype.ext
    show (∑ v : AdmWord A n, ((Pi.single u (1 : ℂ) : AdmWord A n → ℂ) v) •
      cylIndicator hϑ hϑ1 v.1 : HolderSpace A ϑ) = _
    rw [Finset.sum_eq_single u]
    · rw [Pi.single_eq_same, one_smul]
    · intro v _ hvu; rw [Pi.single_eq_of_ne hvu, zero_smul]
    · simp
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hsymm]
  rfl

/-! ## Cylinder averages -/

open Classical in
/-- `g ↦ (y ↦ g(π_N y))` on the subshift, `0` off it. -/
def cylAvgFun (N : ℕ) : ((ℕ → Fin k) → ℂ) →ₗ[ℂ] (ℕ → Fin k) → ℂ where
  toFun g y := if IsAdmissible A y then g (cylPoint A N y) else 0
  map_add' g h := by funext y; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c g := by funext y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

open Classical in
/-- The **cylinder average** `E_N`, of norm at most `1`. -/
def cylAverage (hϑ : 0 < ϑ) (N : ℕ) : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ :=
  ofLinear hϑ (cylAvgFun (A := A) N) 1 zero_le_one
    (fun f y hy => by
      show (if IsAdmissible A y then f (cylPoint A N y) else 0) = 0
      rw [if_neg hy])
    (fun f y => by
      show ‖(if IsAdmissible A y then f (cylPoint A N y) else 0)‖ ≤ 1 * ‖f‖
      rw [one_mul]
      split_ifs
      · exact norm_apply_le f _
      · simp)
    (fun f x y j hx hy hxy => by
      show ‖(if IsAdmissible A x then f (cylPoint A N x) else 0) -
        (if IsAdmissible A y then f (cylPoint A N y) else 0)‖ ≤ 1 * ‖f‖ * ϑ ^ j
      rw [if_pos hx, if_pos hy, one_mul]
      by_cases hjN : N ≤ j
      · rw [cylPoint_congr hx hy (hxy.mono hjN), sub_self, norm_zero]
        exact mul_nonneg (norm_nonneg f) (pow_nonneg hϑ.le j)
      · have h1 : Agree j (cylPoint A N x) (cylPoint A N y) :=
          (((cylPoint_spec hx).2.mono (by omega)).trans hxy).trans
            ((cylPoint_spec hy).2.mono (by omega)).symm
        exact norm_apply_sub_le hϑ f (cylPoint_spec hx).1 (cylPoint_spec hy).1 h1)

open Classical in
theorem cylAverage_apply (hϑ : 0 < ϑ) (N : ℕ) (f : HolderSpace A ϑ) {y : ℕ → Fin k}
    (hy : IsAdmissible A y) : cylAverage hϑ N f y = f (cylPoint A N y) := by
  classical
  show (if IsAdmissible A y then f (cylPoint A N y) else 0) = _
  rw [if_pos hy]

theorem norm_cylAverage_le (hϑ : 0 < ϑ) (N : ℕ) : ‖cylAverage (A := A) hϑ N‖ ≤ 1 :=
  norm_ofLinear_le _ _ _ _ _ _ _

theorem cylAverage_mem (hϑ : 0 < ϑ) (N : ℕ) (f : HolderSpace A ϑ) :
    cylAverage hϑ N f ∈ levelSpace A ϑ N := by
  intro x y hx hy hxy
  rw [cylAverage_apply hϑ N f hx, cylAverage_apply hϑ N f hy, cylPoint_congr hx hy hxy]

theorem cylAverage_of_mem (hϑ : 0 < ϑ) {N : ℕ} {f : HolderSpace A ϑ}
    (hf : f ∈ levelSpace A ϑ N) : cylAverage hϑ N f = f := by
  ext y
  by_cases hy : IsAdmissible A y
  · rw [cylAverage_apply hϑ N f hy]
    exact hf _ _ (cylPoint_spec hy).1 hy (cylPoint_spec hy).2
  · rw [apply_of_not_adm _ hy, apply_of_not_adm _ hy]

/-- `|f − E_N f| ≤ ‖f‖ ϑ^N`. -/
theorem norm_sub_cylAverage_apply_le (hϑ : 0 < ϑ) (N : ℕ) (f : HolderSpace A ϑ)
    (y : ℕ → Fin k) : ‖(f - cylAverage hϑ N f) y‖ ≤ ‖f‖ * ϑ ^ N := by
  rw [sub_apply]
  by_cases hy : IsAdmissible A y
  · rw [cylAverage_apply hϑ N f hy, norm_sub_rev]
    exact norm_apply_sub_le hϑ f (cylPoint_spec hy).1 hy (cylPoint_spec hy).2
  · rw [apply_of_not_adm _ hy, apply_of_not_adm _ hy, sub_zero, norm_zero]
    exact mul_nonneg (norm_nonneg f) (pow_nonneg hϑ.le N)

/-! ## Invariance of level spaces -/

variable (A) in
/-- A potential is **`m`-local** if on the subshift it depends only on the first `m` symbols. -/
def IsLocal (φ : (ℕ → Fin k) → ℝ) (m : ℕ) : Prop :=
  ∀ x y, IsAdmissible A x → IsAdmissible A y → Agree m x y → φ x = φ y

theorem isLocal_levelPotential (φ : (ℕ → Fin k) → ℝ) (m : ℕ) :
    IsLocal A (levelPotential A φ m) m := fun _ _ hx hy h => levelPotential_congr φ hx hy h

theorem IsLocal.mono {φ : (ℕ → Fin k) → ℝ} {m m' : ℕ} (h : IsLocal A φ m) (hm : m ≤ m') :
    IsLocal A φ m' := fun x y hx hy hxy => h x y hx hy (hxy.mono hm)

section Invariance

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

include hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 in
/-- **The transfer operator of an `m`-local potential maps `V_j` into `V_J`** when `J ≥ 1` and
`m, j ≤ J + 1`. -/
theorem transferOp_mem_levelSpace {m : ℕ} (hloc : IsLocal A φ m) {j J : ℕ} (hJ : 1 ≤ J)
    (hmJ : m ≤ J + 1) (hjJ : j ≤ J + 1) (s : ℂ) {f : HolderSpace A ϑ}
    (hf : f ∈ levelSpace A ϑ j) :
    transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s f ∈ levelSpace A ϑ J := by
  intro x y hx hy hxy
  rw [transferOp_apply, transferOp_apply, transferFun_apply, transferFun_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h0 : x 0 = y 0 := hxy 0 (by omega)
  by_cases ha : A a (x 0)
  · have hax : IsAdmissible A (cons a x) := (isAdmissible_cons_iff a x).mpr ⟨ha, hx⟩
    have hay : IsAdmissible A (cons a y) := (isAdmissible_cons_iff a y).mpr ⟨h0 ▸ ha, hy⟩
    have hag : Agree (J + 1) (cons a x) (cons a y) := (agree_cons_iff a x y).mpr hxy
    rw [hloc _ _ hax hay (hag.mono hmJ), hf _ _ hax hay (hag.mono hjJ)]
  · have hax : ¬ IsAdmissible A (cons a x) := fun h => ha ((isAdmissible_cons_iff a x).mp h).1
    have hay : ¬ IsAdmissible A (cons a y) := fun h =>
      ha (h0 ▸ ((isAdmissible_cons_iff a y).mp h).1)
    rw [apply_of_not_adm f hax, apply_of_not_adm f hay, mul_zero, mul_zero]

include hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 in
/-- **Powers of the transfer operator of an `m`-local potential, `m ≥ 2`, map `V_j` into
`V_{max(m−1, j−n)}`.** -/
theorem transferOp_pow_mem_levelSpace {m : ℕ} (hloc : IsLocal A φ m) (hm : 2 ≤ m) (s : ℂ)
    (n : ℕ) {j : ℕ} {f : HolderSpace A ϑ} (hf : f ∈ levelSpace A ϑ j) :
    (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n) f ∈ levelSpace A ϑ (max (m - 1) (j - n)) := by
  induction n with
  | zero => exact levelSpace_mono (by omega) hf
  | succ n ih =>
    rw [pow_succ']
    exact transferOp_mem_levelSpace hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 hloc (by omega) (by omega)
      (by omega) s ih

end Invariance

/-! ## The trace of a locally constant transfer operator -/

/-- If `prepend u q` is admissible for an admissible `q` in the cylinder of `u`, the word `u` is
closed. -/
theorem isAdmissible_periodicSeq_of_prepend {n : ℕ} [NeZero n] (u : Fin n → Fin k)
    {q : ℕ → Fin k} (hq : ∀ i : Fin n, q i = u i)
    (h : IsAdmissible A (prepend u q)) : IsAdmissible A (periodicSeq u) := by
  rw [isAdmissible_periodicSeq_iff]
  have hag : Agree (n + 1) (prepend u q) (periodicSeq u) := by
    intro i hi
    by_cases hin : i < n
    · rw [prepend_apply_lt u q hin, periodicSeq_apply_lt u hin]
    · have hin' : i = n := by omega
      subst hin'
      have h1 := prepend_apply_add u q 0
      rw [zero_add] at h1
      rw [h1, hq ⟨0, NeZero.pos i⟩]
      have h2 := periodicSeq_add u 0
      rw [zero_add] at h2
      rw [h2, periodicSeq_apply_lt u (NeZero.pos i)]
  exact (isAdmissibleUpTo_congr hag).mp ((isAdmissible_iff_upTo_and_shiftBy n _).mp h).1

section Trace

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

open Classical in
/-- `(Lⁿ χ_u)(y) = Σ_v e^{−s φⁿ(v y)} χ_u(v y)`. -/
theorem transferOp_pow_cylIndicator_apply (s : ℂ) {n : ℕ} (u : Fin n → Fin k)
    (y : ℕ → Fin k) :
    (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n) (cylIndicator hϑ hϑ1 u) y =
      if IsAdmissible A (prepend u y) then
        Complex.exp (-(s * birkhoff φ n (prepend u y))) else 0 := by
  classical
  rw [transferOp_pow_apply, transferFun_pow_apply, Finset.sum_eq_single u]
  · show Complex.exp _ * cylFun (A := A) u (prepend u y) = _
    have hpu : ∀ i : Fin n, prepend u y i = u i := fun i => prepend_apply_lt u y i.2
    by_cases h : IsAdmissible A (prepend u y)
    · rw [if_pos h, cylFun_of_adm u h, if_pos hpu, mul_one]
    · rw [if_neg h]
      unfold cylFun
      rw [if_neg (fun h' => h h'.1), mul_zero]
  · intro v _ hvu
    show Complex.exp _ * cylFun (A := A) u (prepend v y) = 0
    unfold cylFun
    rw [if_neg, mul_zero]
    rintro ⟨-, h⟩
    apply hvu
    funext i
    rw [← h i, prepend_apply_lt v y i.2]
  · simp

include hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 in
/-- The level space `V_n` is invariant under `Lⁿ` for an `m`-local potential with `m ≤ n + 1`. -/
theorem transferOp_pow_levelSpace_invariant {m : ℕ} (hloc : IsLocal A φ m) {n : ℕ}
    (hn : 1 ≤ n) (hmn : m ≤ n + 1) (s : ℂ) :
    ∀ f ∈ levelSpace A ϑ n, (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n) f ∈ levelSpace A ϑ n := by
  intro f hf
  have h := transferOp_pow_mem_levelSpace hϑ hϑ1 hφ hC hθ0 hθϑ hθ1
    (hloc.mono (le_max_left m 2)) (le_max_right m 2) s n hf
  exact levelSpace_mono (by omega) h

/-- **The trace identity**: for an `m`-local potential with `m ≤ n + 1`,
`tr(Lⁿ|_{V_n}) = Σ_{σⁿp = p} e^{−s φⁿ(p)}`. -/
theorem trace_transferOp_pow_levelSpace {m : ℕ} (hloc : IsLocal A φ m) {n : ℕ} [NeZero n]
    (hmn : m ≤ n + 1) (s : ℂ) :
    LinearMap.trace ℂ (levelSpace A ϑ n)
      (FiniteRank.restrictEnd (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n) (levelSpace A ϑ n)
        (transferOp_pow_levelSpace_invariant hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 hloc
          (NeZero.one_le) hmn s)) =
      ∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff φ n p)) := by
  classical
  set T := transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s
  have hinv := transferOp_pow_levelSpace_invariant hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 hloc
    (NeZero.one_le) hmn s
  rw [trace_levelSpace_eq hϑ hϑ1 n]
  set g : (ℕ → Fin k) → ℂ := fun p => Complex.exp (-(s * birkhoff φ n p))
  have hterm : ∀ u : AdmWord A n,
      (((FiniteRank.restrictEnd (T ^ n) (levelSpace A ϑ n) hinv)
        ⟨cylIndicator hϑ hϑ1 u.1, cylIndicator_mem hϑ hϑ1 u.1⟩ : levelSpace A ϑ n) :
          HolderSpace A ϑ) u.pt =
      if IsAdmissible A (periodicSeq u.1) then g (periodicSeq u.1) else 0 := by
    intro u
    rw [FiniteRank.coe_restrictEnd_apply]
    have hpt := AdmWord.pt_spec u
    have hmem := hinv _ (cylIndicator_mem hϑ hϑ1 u.1)
    split_ifs with hper
    · have hag : Agree n u.pt (periodicSeq u.1) := fun i hi => by
        rw [hpt.2 ⟨i, hi⟩, periodicSeq_apply_lt u.1 hi]
      rw [hmem _ _ hpt.1 hper hag, transferOp_pow_cylIndicator_apply, prepend_periodicSeq,
        if_pos hper]
    · rw [transferOp_pow_cylIndicator_apply, if_neg]
      intro h
      exact hper (isAdmissible_periodicSeq_of_prepend u.1 hpt.2 h)
  rw [Finset.sum_congr rfl fun u _ => hterm u]
  -- pass from admissible words to all words, then to periodic points
  have hP : ∀ u : Fin n → Fin k, (∃ z, IsAdmissible A z ∧ ∀ i : Fin n, z i = u i) ↔
      u ∈ (Finset.univ.filter fun u : Fin n → Fin k =>
        ∃ z, IsAdmissible A z ∧ ∀ i : Fin n, z i = u i) := by
    intro u; simp
  rw [← Finset.sum_subtype _ (fun u => (hP u).symm)
    (fun u : Fin n → Fin k => if IsAdmissible A (periodicSeq u) then g (periodicSeq u) else 0)]
  rw [Finset.sum_filter_of_ne]
  · rw [← Finset.sum_filter, periodicPoints, Finset.sum_image]
    intro u _ v _ h
    exact periodicSeq_injective h
  · intro u _ hne
    split_ifs at hne with hper
    · exact ⟨periodicSeq u, hper, fun i => periodicSeq_apply_lt u i.2⟩
    · exact absurd rfl hne

end Trace

end

end GaloisForLFunctions.HTGeometry.Symbolic
