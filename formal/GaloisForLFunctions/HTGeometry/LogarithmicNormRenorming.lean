import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Renorming a semigroup down to its growth bound

If a one-parameter semigroup `T` on a normed space satisfies `‖T t‖ ≤ M e^{ωt}` for `t ≥ 0`, the
formula

`p x := sup_{t ≥ 0} e^{-ωt} ‖T t x‖`

defines an equivalent norm — `‖x‖ ≤ p x ≤ M‖x‖` — for which the semigroup is exactly
`e^{ωt}`-bounded: `p (T t x) ≤ e^{ωt} p x`.  In other words the logarithmic norm of the generator
with respect to `p` is at most `ω`.  This is the renorming procedure behind the Banach–Finsler
contraction estimates.
-/

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The renormed functional attached to a semigroup with growth bound `M e^{ωt}`. -/
noncomputable def semigroupSup (T : ℝ → (E →L[ℝ] E)) (ω : ℝ) (x : E) : ℝ :=
  sSup {r : ℝ | ∃ t : ℝ, 0 ≤ t ∧ r = Real.exp (-(ω * t)) * ‖T t x‖}

variable {T : ℝ → (E →L[ℝ] E)} {M ω : ℝ}

lemma semigroupSup_nonempty (x : E) :
    {r : ℝ | ∃ t : ℝ, 0 ≤ t ∧ r = Real.exp (-(ω * t)) * ‖T t x‖}.Nonempty :=
  ⟨Real.exp (-(ω * 0)) * ‖T 0 x‖, ⟨0, le_refl 0, rfl⟩⟩

lemma semigroupSup_bddAbove (hgrowth : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    BddAbove {r : ℝ | ∃ t : ℝ, 0 ≤ t ∧ r = Real.exp (-(ω * t)) * ‖T t x‖} := by
  refine ⟨M * ‖x‖, ?_⟩
  rintro r ⟨t, ht, rfl⟩
  have h1 : ‖T t x‖ ≤ (M * Real.exp (ω * t)) * ‖x‖ :=
    le_trans ((T t).le_opNorm x) (mul_le_mul_of_nonneg_right (hgrowth t ht) (norm_nonneg _))
  have h2 : Real.exp (-(ω * t)) * ‖T t x‖
      ≤ Real.exp (-(ω * t)) * ((M * Real.exp (ω * t)) * ‖x‖) :=
    mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
  refine h2.trans (le_of_eq ?_)
  have hexp : Real.exp (-(ω * t)) * (M * Real.exp (ω * t)) = M := by
    rw [show Real.exp (-(ω * t)) * (M * Real.exp (ω * t))
        = M * (Real.exp (-(ω * t)) * Real.exp (ω * t)) by ring, ← Real.exp_add]
    simp
  rw [← mul_assoc, hexp]

/-- The renormed functional dominates the original norm. -/
lemma norm_le_semigroupSup (hT0 : T 0 = 1)
    (hgrowth : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    ‖x‖ ≤ semigroupSup T ω x := by
  refine le_csSup (semigroupSup_bddAbove hgrowth x) ⟨0, le_refl 0, ?_⟩
  rw [hT0]
  simp

/-- The renormed functional is dominated by `M` times the original norm. -/
lemma semigroupSup_le (hgrowth : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    semigroupSup T ω x ≤ M * ‖x‖ := by
  refine csSup_le (semigroupSup_nonempty x) ?_
  rintro r ⟨t, ht, rfl⟩
  have h1 : ‖T t x‖ ≤ (M * Real.exp (ω * t)) * ‖x‖ :=
    le_trans ((T t).le_opNorm x) (mul_le_mul_of_nonneg_right (hgrowth t ht) (norm_nonneg _))
  have h2 : Real.exp (-(ω * t)) * ‖T t x‖
      ≤ Real.exp (-(ω * t)) * ((M * Real.exp (ω * t)) * ‖x‖) :=
    mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
  refine h2.trans (le_of_eq ?_)
  have hexp : Real.exp (-(ω * t)) * (M * Real.exp (ω * t)) = M := by
    rw [show Real.exp (-(ω * t)) * (M * Real.exp (ω * t))
        = M * (Real.exp (-(ω * t)) * Real.exp (ω * t)) by ring, ← Real.exp_add]
    simp
  rw [← mul_assoc, hexp]

/-- The renormed functional is subadditive. -/
lemma semigroupSup_add_le (hgrowth : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) (x y : E) :
    semigroupSup T ω (x + y) ≤ semigroupSup T ω x + semigroupSup T ω y := by
  refine csSup_le (semigroupSup_nonempty (x + y)) ?_
  rintro r ⟨t, ht, rfl⟩
  have hsplit : ‖T t (x + y)‖ ≤ ‖T t x‖ + ‖T t y‖ := by
    rw [map_add]
    exact norm_add_le _ _
  have h1 : Real.exp (-(ω * t)) * ‖T t (x + y)‖
      ≤ Real.exp (-(ω * t)) * ‖T t x‖ + Real.exp (-(ω * t)) * ‖T t y‖ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hsplit (Real.exp_nonneg _)
  refine h1.trans (add_le_add ?_ ?_)
  · exact le_csSup (semigroupSup_bddAbove hgrowth x) ⟨t, ht, rfl⟩
  · exact le_csSup (semigroupSup_bddAbove hgrowth y) ⟨t, ht, rfl⟩

/-- The renormed functional is absolutely homogeneous. -/
lemma semigroupSup_smul (hgrowth : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) (c : ℝ) (x : E) :
    semigroupSup T ω (c • x) = |c| * semigroupSup T ω x := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hzero : ∀ t : ℝ, Real.exp (-(ω * t)) * ‖T t ((0 : ℝ) • x)‖ = 0 := by
      intro t
      rw [zero_smul, map_zero, norm_zero, mul_zero]
    have hset : {r : ℝ | ∃ t : ℝ, 0 ≤ t ∧ r = Real.exp (-(ω * t)) * ‖T t ((0 : ℝ) • x)‖}
        = {(0 : ℝ)} := by
      ext r
      constructor
      · rintro ⟨t, -, rfl⟩
        rw [hzero t]
        rfl
      · rintro rfl
        exact ⟨0, le_refl 0, (hzero 0).symm⟩
    rw [semigroupSup, hset, csSup_singleton, abs_zero, zero_mul]
  · have hc0 : 0 < |c| := abs_pos.mpr hc
    refine le_antisymm ?_ ?_
    · refine csSup_le (semigroupSup_nonempty (c • x)) ?_
      rintro r ⟨t, ht, rfl⟩
      rw [map_smul, norm_smul, Real.norm_eq_abs,
        show Real.exp (-(ω * t)) * (|c| * ‖T t x‖)
          = |c| * (Real.exp (-(ω * t)) * ‖T t x‖) by ring]
      exact mul_le_mul_of_nonneg_left
        (le_csSup (semigroupSup_bddAbove hgrowth x) ⟨t, ht, rfl⟩) (abs_nonneg c)
    · rw [← le_div_iff₀' hc0]
      refine csSup_le (semigroupSup_nonempty x) ?_
      rintro r ⟨t, ht, rfl⟩
      rw [le_div_iff₀' hc0]
      have hmem : |c| * (Real.exp (-(ω * t)) * ‖T t x‖)
          ∈ {r : ℝ | ∃ t : ℝ, 0 ≤ t ∧ r = Real.exp (-(ω * t)) * ‖T t (c • x)‖} := by
        refine ⟨t, ht, ?_⟩
        rw [map_smul, norm_smul, Real.norm_eq_abs]
        ring
      exact le_csSup (semigroupSup_bddAbove hgrowth (c • x)) hmem

/-- **The renorming inequality.**  In the renormed functional the semigroup is exactly
`e^{ωt}`-bounded. -/
theorem semigroupSup_apply_le (hTadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hgrowth : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) {s : ℝ} (hs : 0 ≤ s) (x : E) :
    semigroupSup T ω (T s x) ≤ Real.exp (ω * s) * semigroupSup T ω x := by
  refine csSup_le (semigroupSup_nonempty (T s x)) ?_
  rintro r ⟨t, ht, rfl⟩
  have hcomp : T t (T s x) = T (t + s) x := by
    rw [hTadd t s ht hs]
    rfl
  rw [hcomp]
  have hmem : Real.exp (-(ω * (t + s))) * ‖T (t + s) x‖
      ∈ {r : ℝ | ∃ u : ℝ, 0 ≤ u ∧ r = Real.exp (-(ω * u)) * ‖T u x‖} :=
    ⟨t + s, by linarith, rfl⟩
  have hle := le_csSup (semigroupSup_bddAbove hgrowth x) hmem
  have hid : Real.exp (-(ω * t)) * ‖T (t + s) x‖
      = Real.exp (ω * s) * (Real.exp (-(ω * (t + s))) * ‖T (t + s) x‖) := by
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hid]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)

/-! ### From a discrete geometric bound to a continuous growth bound -/

/-- Integer times of a locally bounded semigroup grow at most geometrically. -/
lemma norm_semigroup_nat_le (hT0 : T 0 = 1)
    (hTadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    {C : ℝ} (hC : 1 ≤ C) (hloc : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖T s‖ ≤ C) (n : ℕ) :
    ‖T (n : ℝ)‖ ≤ C ^ n := by
  induction n with
  | zero =>
      rw [Nat.cast_zero, hT0, pow_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, hTadd (n : ℝ) 1 (Nat.cast_nonneg _) zero_le_one]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      calc ‖T (n : ℝ)‖ * ‖T 1‖ ≤ C ^ n * C :=
            mul_le_mul ih (hloc 1 zero_le_one le_rfl) (norm_nonneg _) (by positivity)
        _ = C ^ (n + 1) := by ring

/-- **The continuous growth bound.**  A locally bounded semigroup whose integer times are
eventually dominated by `e^{ωn}` satisfies `‖T t‖ ≤ M e^{ωt}` for all `t ≥ 0`. -/
theorem exists_growth_of_pow_bound (hT0 : T 0 = 1)
    (hTadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    {C : ℝ} (hC : 1 ≤ C) (hloc : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ‖T s‖ ≤ C)
    {N : ℕ} (hpow : ∀ n : ℕ, N ≤ n → ‖T (n : ℝ)‖ ≤ Real.exp (ω * n)) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t) := by
  refine ⟨max (C * Real.exp |ω|) (C ^ N * C * Real.exp (|ω| * N)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < C * Real.exp |ω| := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  intro t ht
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊t⌋₊ := ⟨_, rfl⟩
  have hnle : (n : ℝ) ≤ t := by rw [hn]; exact Nat.floor_le ht
  have hnlt : t < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one t
  have hsplit : T t = (T (n : ℝ)).comp (T (t - (n : ℝ))) := by
    rw [← hTadd (n : ℝ) (t - (n : ℝ)) (Nat.cast_nonneg _) (by linarith)]
    congr 1
    ring
  have hs0 : (0 : ℝ) ≤ t - (n : ℝ) := by linarith
  have hs1 : t - (n : ℝ) ≤ 1 := by linarith
  have hcomp : ‖T t‖ ≤ ‖T (n : ℝ)‖ * C := by
    rw [hsplit]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    exact mul_le_mul_of_nonneg_left (hloc _ hs0 hs1) (norm_nonneg _)
  have hexpshift : Real.exp (ω * (n : ℝ)) ≤ Real.exp |ω| * Real.exp (ω * t) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hab : ω * (n : ℝ) - ω * t = ω * ((n : ℝ) - t) := by ring
    have hle : ω * ((n : ℝ) - t) ≤ |ω| := by
      have h1 : |ω * ((n : ℝ) - t)| ≤ |ω| * 1 := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ω)
        rw [abs_le]
        constructor <;> linarith
      have h2 : ω * ((n : ℝ) - t) ≤ |ω * ((n : ℝ) - t)| := le_abs_self _
      linarith
    linarith [hab, hle]
  rcases Nat.lt_or_ge n N with hNn | hNn
  swap
  · refine le_trans hcomp ?_
    have h1 : ‖T (n : ℝ)‖ * C ≤ Real.exp (ω * (n : ℝ)) * C :=
      mul_le_mul_of_nonneg_right (hpow n hNn) (by linarith)
    refine h1.trans ?_
    have h2 : Real.exp (ω * (n : ℝ)) * C ≤ (Real.exp |ω| * Real.exp (ω * t)) * C :=
      mul_le_mul_of_nonneg_right hexpshift (by linarith)
    refine h2.trans ?_
    have heq : Real.exp |ω| * Real.exp (ω * t) * C
        = (C * Real.exp |ω|) * Real.exp (ω * t) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · -- `t` lies below `N`
    have hnN : n ≤ N := le_of_lt hNn
    have hbd : ‖T (n : ℝ)‖ ≤ C ^ N :=
      le_trans (norm_semigroup_nat_le hT0 hTadd hC hloc n)
        (pow_le_pow_right₀ hC hnN)
    have htN : t ≤ (N : ℝ) := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnN
      have hnN' : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNn
      linarith
    have hlow : Real.exp (-(|ω| * (N : ℝ))) ≤ Real.exp (ω * t) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : -(|ω| * (N : ℝ)) ≤ -( |ω| * t) := by
        have : (0 : ℝ) ≤ |ω| := abs_nonneg ω
        nlinarith [htN, ht, this]
      have h2 : -(|ω| * t) ≤ ω * t := by
        nlinarith [ht, neg_abs_le ω]
      linarith
    have hfin : ‖T t‖ ≤ C ^ N * C := le_trans hcomp
      (mul_le_mul_of_nonneg_right hbd (by linarith))
    refine hfin.trans ?_
    have hgoal : C ^ N * C
        ≤ (C ^ N * C * Real.exp (|ω| * (N : ℝ))) * Real.exp (ω * t) := by
      have hpos : (0 : ℝ) ≤ C ^ N * C := by positivity
      have hkey : (1 : ℝ) ≤ Real.exp (|ω| * (N : ℝ)) * Real.exp (ω * t) := by
        rw [← Real.exp_add]
        refine Real.one_le_exp ?_
        have := Real.exp_le_exp.mp hlow
        linarith
      nlinarith [hpos, hkey]
    refine hgoal.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

/-- **Lemma 4.3 (Kim–Mer–Pálfia), the renorming procedure.**  A semigroup with growth bound
`M e^{ωt}` admits an equivalent norm in which its logarithmic norm is at most `ω`. -/
theorem exists_equivalent_norm_of_semigroup_growth (hT0 : T 0 = 1)
    (hTadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hgrowth : ∀ t, 0 ≤ t → ‖T t‖ ≤ M * Real.exp (ω * t)) :
    ∃ p : E → ℝ,
      (∀ x, ‖x‖ ≤ p x) ∧ (∀ x, p x ≤ M * ‖x‖)
        ∧ (∀ x y, p (x + y) ≤ p x + p y)
        ∧ (∀ (c : ℝ) (x : E), p (c • x) = |c| * p x)
        ∧ (∀ s, 0 ≤ s → ∀ x, p (T s x) ≤ Real.exp (ω * s) * p x) :=
  ⟨semigroupSup T ω, norm_le_semigroupSup hT0 hgrowth, semigroupSup_le hgrowth,
    semigroupSup_add_le hgrowth, semigroupSup_smul hgrowth,
    fun _ hs x => semigroupSup_apply_le hTadd hgrowth hs x⟩

end GaloisForLFunctions.HTGeometry
