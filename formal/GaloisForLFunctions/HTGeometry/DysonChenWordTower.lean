import GaloisForLFunctions.HTGeometry.SelfAdjointDysonWordReversal
import GaloisForLFunctions.HTGeometry.DuhamelSourceResponse

/-!
# The Dyson–Chen word tower of a source

For a source `L`, `(K_a)_{a ∈ A}` the word coefficients `U_w(t)` of
`e^{-tB} = ∑_w U_w(t) ⊗ δ_w` in the word algebra `ℓ¹(A*; End H)`, `B = L ⊗ δ_∅ + ∑_a K_a ⊗ δ_a`,
form the ordered response tower:

* `U_∅(t) = S_t = e^{-tL}` and `U_{aw}(t) = -∫₀ᵗ S_{t-s} K_a U_w(s) ds` `(SR.20)`; the family is
  the unique coefficient system of `e^{-tB}` `(SR.21)` and the unique solution of this recursion;
* `U_{aw}' + L U_{aw} = -K_a U_w`, `U_{aw}(0) = 0` `(SR.22)`, read off from `F' = -B F` through
  the left multiplication `(B X)_{aw} = L X_{aw} + K_a X_w`;
* `U_w(t + s) = ∑_{w = uv} U_u(t) U_v(s)` `(SR.23)`, the coefficient form of
  `e^{-(t+s)B} = e^{-tB} e^{-sB}`;
* specializing the letters to commuting scalars `ε_a`, `|ε_a| ≤ 1`, is a continuous ring
  homomorphism sending `e^{-tB}` to `e^{-t(L + ∑ ε_a K_a)}`; it sees a word series only through its
  content sums `∑_{w ∈ α} X_w` over words with a given multiset of letters, while the word tower
  separates `δ_{ab}` from `δ_{ba}` (ordered-memory separation);
* a unitary `J` with `J L = L J` and `J K_a J* = K_{σ a}` gives `J U_w(t) J* = U_{σ w}(t)`
  `(SR.24)`.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-! ## Word-algebra lemmas -/

namespace WordL1

variable {A E : Type*} [NormedRing E]

/-- Evaluation at a word, as a continuous linear map of norm at most one. -/
def evalCLM (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] (w : List A) : WordL1 A E →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun X => X w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun X => by
    simpa using norm_apply_le X w

@[simp] theorem evalCLM_apply (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] (w : List A)
    (X : WordL1 A E) : evalCLM 𝕜 w X = X w := rfl

/-- Left multiplication by an elementary tensor: `((T ⊗ δ_u) X)_w = T X_{w'}` when `w = u w'`,
and `0` when `u` is not a prefix of `w`. -/
theorem single_mul_apply [DecidableEq A] (u : List A) (T : E) (X : WordL1 A E) (w : List A) :
    (single u T * X) w = if u <+: w then T * X (w.drop u.length) else 0 := by
  rw [mul_apply]
  simp only [single_apply]
  split_ifs with h
  · obtain ⟨r, hr⟩ := h
    have hdrop : w.drop u.length = r := by rw [← hr, List.drop_left]
    rw [hdrop, Finset.sum_eq_single_of_mem (u, r) (mem_wordSplits.2 hr)]
    · simp
    · intro p hp hne
      rw [mem_wordSplits] at hp
      by_cases h1 : p.1 = u
      · exfalso
        apply hne
        have h2 : p.2 = r := List.append_cancel_left (as := u) (by
          rw [← h1, hp, h1]
          exact hr.symm)
        exact Prod.ext h1 h2
      · rw [if_neg h1, zero_mul]
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [mem_wordSplits] at hp
    have h1 : p.1 ≠ u := fun h1 => h ⟨p.2, h1 ▸ hp⟩
    rw [if_neg h1, zero_mul]

end WordL1

/-! ## Hypothesis-free algebra of a Dyson source -/

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] operatorRatAlgebra

namespace SelfAdjointDysonSource

variable (S : SelfAdjointDysonSource A H)

/-- `(B X)_∅ = L X_∅`. -/
theorem generator_mul_apply_nil (X : WordL1 A (H →L[ℂ] H)) :
    (S.generator * X) [] = S.L * X [] := by
  rw [generator, add_mul, Finset.sum_mul, WordL1.add_apply, WordL1.sum_apply,
    WordL1.single_mul_apply]
  simp [WordL1.single_mul_apply]

/-- `(B X)_{aw} = L X_{aw} + K_a X_w`. -/
theorem generator_mul_apply_cons (X : WordL1 A (H →L[ℂ] H)) (a : A) (w : List A) :
    (S.generator * X) (a :: w) = S.L * X (a :: w) + S.K a * X w := by
  rw [generator, add_mul, Finset.sum_mul, WordL1.add_apply, WordL1.sum_apply,
    WordL1.single_mul_apply]
  simp only [List.nil_prefix, if_true, List.length_nil, List.drop_zero, WordL1.single_mul_apply,
    List.cons_prefix_cons, List.nil_prefix, and_true, List.length_cons, List.length_nil,
    zero_add, List.drop_succ_cons, List.drop_zero]
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ a)]

/-- The response as a real exponential: `F_t = e^{t • (-B)}`. -/
theorem response_eq_exp_real (t : ℝ) :
    S.response t = NormedSpace.exp (t • -S.generator) := by
  rw [response]
  congr 1
  ext1 w
  show (-(t : ℂ)) • S.generator w = t • -(S.generator w)
  rw [smul_neg, neg_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- `F' = -B F`. -/
theorem hasDerivAt_response (t : ℝ) :
    HasDerivAt S.response (-S.generator * S.response t) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-S.generator) t
  have hfun : S.response = fun u : ℝ => NormedSpace.exp (u • -S.generator) :=
    funext S.response_eq_exp_real
  rw [hfun]
  exact h

theorem hasDerivAt_coeff (w : List A) (t : ℝ) :
    HasDerivAt (S.coeff w) (-((S.generator * S.response t) w)) t := by
  have h := (WordL1.evalCLM ℝ w).hasFDerivAt.comp_hasDerivAt t (S.hasDerivAt_response t)
  rw [neg_mul] at h
  exact h

/-- The free evolution `S_t = e^{-tL}`. -/
def semigroup (t : ℝ) : H →L[ℂ] H := NormedSpace.exp (t • -S.L)

omit [Fintype A] [DecidableEq A] in
theorem semigroup_zero : S.semigroup 0 = 1 := by simp [semigroup]

omit [Fintype A] [DecidableEq A] in
theorem semigroup_add (t s : ℝ) : S.semigroup (t + s) = S.semigroup t * S.semigroup s := by
  rw [semigroup, semigroup, semigroup, add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl (-S.L)).smul_left t |>.smul_right s)

omit [Fintype A] [DecidableEq A] in
theorem hasDerivAt_semigroup (t : ℝ) : HasDerivAt S.semigroup (-S.L * S.semigroup t) t :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-S.L) t

omit [Fintype A] [DecidableEq A] in
theorem commute_semigroup (t : ℝ) : Commute S.L (S.semigroup t) :=
  (((Commute.refl S.L).neg_right).smul_right t).exp_right

omit [Fintype A] [DecidableEq A] in
theorem continuous_semigroup : Continuous S.semigroup :=
  continuous_iff_continuousAt.mpr fun t => (S.hasDerivAt_semigroup t).continuousAt

theorem continuous_coeff (w : List A) : Continuous (S.coeff w) :=
  continuous_iff_continuousAt.mpr fun t => (S.hasDerivAt_coeff w t).continuousAt

/-- `F_0 = 1`, so `U_w(0) = δ_{w,∅}`. -/
theorem coeff_zero (w : List A) : S.coeff w 0 = wordUnit w := by
  simp [coeff, response, WordL1.one_apply]

/-- **`(SR.20)`, base**: `U_∅(t) = S_t`. -/
theorem coeff_nil (t : ℝ) : S.coeff [] t = S.semigroup t := by
  have h := S.constantTerm_response t
  rw [WordL1.constantTerm_apply] at h
  rw [coeff, h, semigroup]
  congr 1
  rw [smul_neg, neg_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- **`(SR.22)`: the word equation** `U_{aw}' + L U_{aw} = -K_a U_w`. -/
theorem hasDerivAt_coeff_cons (a : A) (w : List A) (t : ℝ) :
    HasDerivAt (S.coeff (a :: w)) (-(S.L * S.coeff (a :: w) t) - S.K a * S.coeff w t) t := by
  have h := S.hasDerivAt_coeff (a :: w) t
  rw [S.generator_mul_apply_cons, neg_add] at h
  exact h.congr_deriv (by rw [sub_eq_add_neg]; rfl)

/-- **`(SR.22)`, initial value**: `U_{aw}(0) = 0`. -/
theorem coeff_cons_zero (a : A) (w : List A) : S.coeff (a :: w) 0 = 0 := by
  rw [coeff_zero]
  rfl

/-- **`(SR.20)`: the Dyson recursion** `U_{aw}(t) = -∫₀ᵗ S_{t-s} K_a U_w(s) ds`. -/
theorem coeff_cons (a : A) (w : List A) (t : ℝ) :
    S.coeff (a :: w) t = -∫ s in (0 : ℝ)..t, S.semigroup (t - s) * S.K a * S.coeff w s := by
  set φ : ℝ → H →L[ℂ] H := fun s => S.semigroup (-s) * S.coeff (a :: w) s
  have hneg : ∀ s, HasDerivAt (fun r => S.semigroup (-r)) (S.L * S.semigroup (-s)) s := fun s => by
    have h := (S.hasDerivAt_semigroup (-s)).scomp s (hasDerivAt_neg s)
    refine h.congr_deriv ?_
    simp
  have hφ : ∀ s, HasDerivAt φ (-(S.semigroup (-s) * S.K a * S.coeff w s)) s := fun s => by
    have h := (hneg s).mul (S.hasDerivAt_coeff_cons a w s)
    refine h.congr_deriv ?_
    have hc := (S.commute_semigroup (-s)).eq
    rw [mul_sub, mul_neg, ← mul_assoc, ← hc]
    noncomm_ring
  have hcont : Continuous fun s => S.semigroup (-s) * S.K a * S.coeff w s :=
    ((S.continuous_semigroup.comp continuous_neg).mul continuous_const).mul (S.continuous_coeff w)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => hφ s) (hcont.neg.intervalIntegrable (μ := volume) 0 t)
  have hφ0 : φ 0 = 0 := by simp [φ, S.coeff_cons_zero]
  rw [hφ0, sub_zero, intervalIntegral.integral_neg] at hftc
  have hSt : S.coeff (a :: w) t = S.semigroup t * φ t := by
    simp only [φ, ← mul_assoc, ← S.semigroup_add, add_neg_cancel, S.semigroup_zero, one_mul]
  have hpull := (ContinuousLinearMap.mul ℝ (H →L[ℂ] H) (S.semigroup t)).intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := volume) 0 t)
  rw [hSt, ← hftc, mul_neg, ← ContinuousLinearMap.mul_apply' ℝ, ← hpull]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [ContinuousLinearMap.mul_apply', ← mul_assoc, ← S.semigroup_add, sub_eq_add_neg]

/-- **Uniqueness of the recursion**: any family with `V_∅ = S` satisfying `(SR.20)` is the word
tower. -/
theorem eq_coeff_of_recursion {V : List A → ℝ → H →L[ℂ] H} (h0 : ∀ t, V [] t = S.semigroup t)
    (hcons : ∀ a w t, V (a :: w) t = -∫ s in (0 : ℝ)..t, S.semigroup (t - s) * S.K a * V w s) :
    ∀ w t, V w t = S.coeff w t := by
  intro w
  induction w with
  | nil => intro t; rw [h0, S.coeff_nil]
  | cons a w ih =>
    intro t
    rw [hcons, S.coeff_cons]
    simp only [ih]

/-- **`(SR.21)`: uniqueness of the coefficient system** of `e^{-tB} = ∑_w U_w(t) ⊗ δ_w`. -/
theorem eq_coeff_of_hasSum {t : ℝ} {V : List A → H →L[ℂ] H}
    (hV : HasSum (fun w => WordL1.single w (V w)) (S.response t)) (w : List A) :
    V w = S.coeff w t := by
  have h := hV.mapL (WordL1.evalCLM ℂ w)
  simp only [WordL1.evalCLM_apply, WordL1.single_apply] at h
  have h' : HasSum (fun v => if v = w then V v else 0) (V w) := by
    have := hasSum_ite_eq w (V w)
    refine this.congr_fun fun v => ?_
    by_cases hv : v = w
    · subst hv; simp
    · simp [hv]
  exact h'.unique (h.congr_fun fun v => by by_cases hv : w = v <;> simp [hv, eq_comm])

/-- **`(SR.23)`: time fusion** `U_w(t + s) = ∑_{w = uv} U_u(t) U_v(s)`. -/
theorem coeff_add (w : List A) (t s : ℝ) :
    S.coeff w (t + s) = ∑ p ∈ wordSplits w, S.coeff p.1 t * S.coeff p.2 s := by
  have h : S.response (t + s) = S.response t * S.response s := by
    rw [S.response_eq_exp_real, S.response_eq_exp_real, S.response_eq_exp_real, add_smul]
    exact NormedSpace.exp_add_of_commute
      ((Commute.refl (-S.generator)).smul_left t |>.smul_right s)
  rw [coeff, h, WordL1.mul_apply]
  rfl

/-- **`(SR.24)`: functional-equation covariance.**  A unitary `J` with `J L = L J` and
`J K_a J* = K_{σ a}` conjugates the word tower: `J U_w(t) J* = U_{σ w}(t)`. -/
theorem conj_coeff_of_symmetry (J : unitary (H →L[ℂ] H)) (σ : A ≃ A)
    (hL : (J : H →L[ℂ] H) * S.L = S.L * J) (hK : ∀ a, unitaryConj J (S.K a) = S.K (σ a))
    (w : List A) (t : ℝ) : unitaryConj J (S.coeff w t) = S.coeff (w.map σ) t := by
  have hconjL : unitaryConj J S.L = S.L := by
    rw [unitaryConj_apply, hL, mul_assoc, Unitary.mul_star_self_of_mem J.2, mul_one]
  set C := WordL1.relabel σ (unitaryConj J) (norm_unitaryConj J)
  have hB : C S.generator = S.generator := by
    simp only [C, generator, map_add, map_sum, WordL1.relabel_single, List.map_nil,
      List.map_singleton, hconjL, hK]
    congr 1
    exact Equiv.sum_comp σ (fun a => WordL1.single [a] (S.K a))
  have hF : C (S.response t) = S.response t := by
    rw [response, NormedSpace.map_exp _ (WordL1.continuous_relabel _ _ _),
      WordL1.relabel_smul σ (unitaryConj J) (norm_unitaryConj J) (unitaryConj_smul J), hB]
  have h := congrArg (fun X : WordL1 A (H →L[ℂ] H) => X (w.map σ)) hF
  simp only [C, WordL1.relabel_apply, List.map_map, Equiv.symm_comp_self, List.map_id] at h
  exact h

end SelfAdjointDysonSource

/-! ## Commutative specialization and ordered memory -/

section Specialization

variable {B : Type*}

/-- The commutative weight `ε^w = ∏ᵢ ε_{wᵢ}` of a word. -/
def wordWeight (ε : B → ℂ) (w : List B) : ℂ := (w.map ε).prod

theorem wordWeight_append (ε : B → ℂ) (u v : List B) :
    wordWeight ε (u ++ v) = wordWeight ε u * wordWeight ε v := by
  simp [wordWeight, List.map_append, List.prod_append]

/-- The weight of a word depends only on its letter content. -/
theorem wordWeight_eq_of_content (ε : B → ℂ) {w : List B} {α : Multiset B}
    (h : (w : Multiset B) = α) : wordWeight ε w = (α.map ε).prod := by
  rw [wordWeight, ← Multiset.prod_coe, ← Multiset.map_coe, h]

theorem norm_wordWeight_le {ε : B → ℂ} (hε : ∀ a, ‖ε a‖ ≤ 1) (w : List B) :
    ‖wordWeight ε w‖ ≤ 1 := by
  induction w with
  | nil => simp [wordWeight]
  | cons a w ih =>
    rw [wordWeight, List.map_cons, List.prod_cons, norm_mul]
    exact mul_le_one₀ (hε a) (norm_nonneg _) ih

namespace WordL1

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]
variable {ε : B → ℂ}

omit [NormedAlgebra ℂ E] in
theorem summable_apply (X : WordL1 B E) : Summable fun w => X w :=
  (summable_norm_iff_memℓp_one.1 X.memℓp).of_norm

omit [CompleteSpace E] in
theorem summable_norm_weight (hε : ∀ a, ‖ε a‖ ≤ 1) (X : WordL1 B E) :
    Summable fun w => ‖wordWeight ε w • X w‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_wordWeight_le hε w))
    (summable_norm_iff_memℓp_one.1 X.memℓp)

/-- The commutative specialization `X ↦ ∑_w ε^w X_w` of the letters to scalars `ε_a`. -/
def specialize (ε : B → ℂ) (X : WordL1 B E) : E := ∑' w, wordWeight ε w • X w

theorem hasSum_specialize (hε : ∀ a, ‖ε a‖ ≤ 1) (X : WordL1 B E) :
    HasSum (fun w => wordWeight ε w • X w) (specialize ε X) :=
  (summable_norm_weight hε X).of_norm.hasSum

theorem norm_specialize_le (hε : ∀ a, ‖ε a‖ ≤ 1) (X : WordL1 B E) : ‖specialize ε X‖ ≤ ‖X‖ :=
  (hasSum_specialize hε X).norm_le_of_bounded (hasSum_norm X) fun w => by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_wordWeight_le hε w)

theorem specialize_add (hε : ∀ a, ‖ε a‖ ≤ 1) (X Y : WordL1 B E) :
    specialize ε (X + Y) = specialize ε X + specialize ε Y := by
  refine ((hasSum_specialize hε X).add (hasSum_specialize hε Y)).unique ?_ |>.symm
  refine (hasSum_specialize hε (X + Y)).congr_fun fun w => ?_
  rw [add_apply, smul_add]

theorem specialize_smul (hε : ∀ a, ‖ε a‖ ≤ 1) (c : ℂ) (X : WordL1 B E) :
    specialize ε (c • X) = c • specialize ε X := by
  refine (((hasSum_specialize hε X).const_smul c).unique ?_).symm
  refine (hasSum_specialize hε (c • X)).congr_fun fun w => ?_
  rw [smul_apply, smul_comm]

omit [CompleteSpace E] in
theorem specialize_single [DecidableEq B] (w : List B) (T : E) :
    specialize ε (single w T) = wordWeight ε w • T := by
  rw [specialize, tsum_eq_single w fun v hv => by rw [single_apply, if_neg hv, smul_zero]]
  rw [single_apply_self]

omit [CompleteSpace E] in
theorem specialize_one : specialize ε (1 : WordL1 B E) = 1 := by
  rw [specialize, tsum_eq_single [] fun v hv => by
    rw [one_apply]
    cases v with
    | nil => exact absurd rfl hv
    | cons _ _ => simp [wordUnit]]
  simp [one_apply, wordUnit, wordWeight]

/-- The specialization is multiplicative: commuting scalars turn concatenation into products. -/
theorem specialize_mul (hε : ∀ a, ‖ε a‖ ≤ 1) (X Y : WordL1 B E) :
    specialize ε (X * Y) = specialize ε X * specialize ε Y := by
  have hsum : Summable fun p : List B × List B =>
      ‖(wordWeight ε p.1 • X p.1) * (wordWeight ε p.2 • Y p.2)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_le _ _) ?_
    exact (summable_norm_weight hε X).mul_of_nonneg (summable_norm_weight hε Y)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hprod : HasSum (fun p : List B × List B =>
      (wordWeight ε p.1 • X p.1) * (wordWeight ε p.2 • Y p.2))
      (specialize ε X * specialize ε Y) :=
    HasSum.mul (f := fun w => wordWeight ε w • X w) (g := fun w => wordWeight ε w • Y w)
      (hasSum_specialize hε X) (hasSum_specialize hε Y) hsum.of_norm
  have hw : HasSum (fun w => ∑ p ∈ wordSplits w,
      (wordWeight ε p.1 • X p.1) * (wordWeight ε p.2 • Y p.2))
      (specialize ε X * specialize ε Y) := by
    have hsig := (wordSplitsSigmaEquiv.hasSum_iff (f := fun p : List B × List B =>
      (wordWeight ε p.1 • X p.1) * (wordWeight ε p.2 • Y p.2))).2 hprod
    refine hsig.sigma fun w => ?_
    have h := hasSum_fintype (fun c : ↥(wordSplits w) =>
      (wordWeight ε c.1.1 • X c.1.1) * (wordWeight ε c.1.2 • Y c.1.2))
    rwa [Finset.sum_coe_sort (wordSplits w) (fun p : List B × List B =>
      (wordWeight ε p.1 • X p.1) * (wordWeight ε p.2 • Y p.2))] at h
  have hw' : HasSum (fun w => wordWeight ε w • (X * Y) w) (specialize ε X * specialize ε Y) := by
    refine hw.congr_fun fun w => ?_
    rw [mul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [mem_wordSplits] at hp
    rw [smul_mul_smul_comm, ← wordWeight_append, hp]
  exact (hasSum_specialize hε (X * Y)).unique hw'

/-- The specialization as a ring homomorphism. -/
def specializeHom (ε : B → ℂ) (hε : ∀ a, ‖ε a‖ ≤ 1) : WordL1 B E →+* E where
  toFun := specialize ε
  map_one' := specialize_one
  map_mul' := specialize_mul hε
  map_zero' := by simp [specialize]
  map_add' := specialize_add hε

theorem continuous_specializeHom (hε : ∀ a, ‖ε a‖ ≤ 1) :
    Continuous (specializeHom (E := E) ε hε) :=
  AddMonoidHomClass.continuous_of_bound (specializeHom ε hε) 1 fun X => by
    rw [one_mul]
    exact norm_specialize_le hε X

/-- The content sum `∑_{w ∈ α} X_w` over the words with letter multiset `α`. -/
def contentSum (X : WordL1 B E) (α : Multiset B) : E :=
  ∑' w : ((fun w : List B => (w : Multiset B)) ⁻¹' {α}), X w

/-- **The specialization sees only content sums**:
`∑_w ε^w X_w = ∑_α ε^α ∑_{w ∈ α} X_w`. -/
theorem hasSum_specialize_content (hε : ∀ a, ‖ε a‖ ≤ 1) (X : WordL1 B E) :
    HasSum (fun α : Multiset B => (α.map ε).prod • contentSum X α) (specialize ε X) := by
  have h := (hasSum_specialize hε X).tsum_fiberwise (fun w : List B => (w : Multiset B))
  refine h.congr_fun fun α => ?_
  have hw : ∀ w : ((fun w : List B => (w : Multiset B)) ⁻¹' {α}),
      wordWeight ε w • X w = (α.map ε).prod • X w := fun w =>
    by rw [wordWeight_eq_of_content ε w.2]
  rw [tsum_congr hw, contentSum]
  exact (Summable.tsum_const_smul _ ((summable_apply X).subtype _)).symm

/-- Word series with equal content sums have equal specializations. -/
theorem specialize_eq_of_contentSum_eq (hε : ∀ a, ‖ε a‖ ≤ 1) {X Y : WordL1 B E}
    (h : ∀ α, contentSum X α = contentSum Y α) : specialize ε X = specialize ε Y :=
  (hasSum_specialize_content hε X).unique
    ((hasSum_specialize_content hε Y).congr_fun fun α => by rw [h])

omit [NormedAlgebra ℂ E] in
theorem contentSum_sub (X Y : WordL1 B E) (α : Multiset B) :
    contentSum (X - Y) α = contentSum X α - contentSum Y α := by
  rw [contentSum, contentSum, contentSum]
  exact ((summable_apply X).subtype _).tsum_sub ((summable_apply Y).subtype _)

omit [NormedAlgebra ℂ E] [CompleteSpace E] in
theorem contentSum_single [DecidableEq B] (w : List B) (T : E) (α : Multiset B) :
    contentSum (single w T) α = if (w : Multiset B) = α then T else 0 := by
  rw [contentSum]
  split_ifs with h
  · rw [tsum_eq_single (⟨w, h⟩ : ((fun w : List B => (w : Multiset B)) ⁻¹' {α}))
      fun v hv => by
        rw [single_apply, if_neg fun h' => hv (Subtype.ext h')]]
    exact single_apply_self w T
  · refine (tsum_congr fun v => ?_).trans tsum_zero
    rw [single_apply, if_neg]
    rintro rfl
    exact h v.2

omit [NormedAlgebra ℂ E] in
/-- **Ordered-memory separation.**  For distinct letters the content sums cannot distinguish
`T ⊗ δ_{ab}` from `T ⊗ δ_{ba}`, while the word series does. -/
theorem contentSum_swap [DecidableEq B] (a b : B) (T : E) (α : Multiset B) :
    contentSum (single [a, b] T - single [b, a] T) α = 0 := by
  have hperm : (([a, b] : List B) : Multiset B) = ([b, a] : List B) :=
    Multiset.coe_eq_coe.mpr (List.Perm.swap b a [])
  rw [contentSum_sub, contentSum_single, contentSum_single, hperm, sub_self]

omit [NormedAlgebra ℂ E] [CompleteSpace E] in
theorem single_swap_ne_zero [DecidableEq B] {a b : B} (hab : a ≠ b) {T : E} (hT : T ≠ 0) :
    single [a, b] T - single [b, a] T ≠ 0 := by
  intro h
  have h1 := congrArg (fun X : WordL1 B E => X [a, b]) h
  have hne : ([a, b] : List B) ≠ [b, a] := by
    intro h'
    exact hab (List.cons.inj h').1
  simp only [sub_apply, single_apply_self, single_apply, if_neg hne, sub_zero, zero_apply] at h1
  exact hT h1

end WordL1

end Specialization

namespace SelfAdjointDysonSource

variable (S : SelfAdjointDysonSource A H)

theorem specialize_generator {ε : A → ℂ} (hε : ∀ a, ‖ε a‖ ≤ 1) :
    WordL1.specialize ε S.generator = S.L + ∑ a, ε a • S.K a := by
  change WordL1.specializeHom ε hε S.generator = _
  rw [generator, map_add, map_sum]
  simp only [WordL1.specializeHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    WordL1.specialize_single]
  simp [wordWeight]

/-- **Scalar specialization of the tower**: with commuting scalar letters `|ε_a| ≤ 1`,
`∑_w ε^w U_w(t) = e^{-t(L + ∑_a ε_a K_a)}`. -/
theorem specialize_response {ε : A → ℂ} (hε : ∀ a, ‖ε a‖ ≤ 1) (t : ℝ) :
    WordL1.specialize ε (S.response t) =
      NormedSpace.exp ((-(t : ℂ)) • (S.L + ∑ a, ε a • S.K a)) := by
  change WordL1.specializeHom ε hε (S.response t) = _
  rw [response, NormedSpace.map_exp _ (WordL1.continuous_specializeHom hε)]
  congr 1
  change WordL1.specialize ε _ = _
  rw [WordL1.specialize_smul hε, S.specialize_generator hε]

/-- **Ordered-memory separation for the tower**: the scalar response
`e^{-t(L + ∑ ε_a K_a)}` is determined by the content sums `∑_{w ∈ α} U_w(t)` alone. -/
theorem specialize_response_eq_of_contentSum_eq {ε : A → ℂ} (hε : ∀ a, ‖ε a‖ ≤ 1) (t : ℝ)
    {X : WordL1 A (H →L[ℂ] H)} (hX : ∀ α, WordL1.contentSum X α =
      WordL1.contentSum (S.response t) α) :
    WordL1.specialize ε X = NormedSpace.exp ((-(t : ℂ)) • (S.L + ∑ a, ε a • S.K a)) := by
  rw [WordL1.specialize_eq_of_contentSum_eq hε hX, S.specialize_response hε]

end SelfAdjointDysonSource

end GaloisForLFunctions.HTGeometry
