import GaloisForLFunctions.ArithmeticInnerFunctionTheory.PhaseLockingIsTorusPositivity

/-!
# Echo trains on independent reflectors

A layered medium with base `1` and echoes `c_i` at reflectors `ℓ_i` has the symbol `g(b) = 1 − 2Σ c_i cos(bℓ_i)`, and is passive iff
`g ≥ 0`. The theorem below is the place where the incommensurability of `log p` acts.

**Columns add** (`le_columnSum_iff`, `le_columnSum_iff_min`). On a Kronecker family, the infimum over `b` of a sum of column functions
`Σ g_i(e^{ibℓ_i})` is the sum of the infima of the columns. Locked phases cost nothing: each column finds its worst phase at the same height.

**Size is exact on independent reflectors** (`echoSymbol_nonneg_iff`). A train on a Kronecker family is passive iff `2Σ|c_i| ≤ 1`. There is no
cancellation between independent reflectors.

**Commensurable reflectors have room** (`exists_passive_commensurable_train`). On the reflectors `kℓ₀`, the Fejér train is passive with `2Σ|c_k| = N` for every `N`.

So the `ℓ¹` mass of a passive train is unbounded on a periodic medium and at most `1` on an independent one. Over `𝔽_q` all reflectors are
commensurable; over `ℤ` each prime is a separate column with its own commensurable powers, and the columns add. The positive cone of an Euler train lives inside one column at a time; across
columns only size is available, and it has to be paid by the base.

**A positive train is worst at the origin** (`echoSymbol_ge_of_nonneg`): for `c ≥ 0` the minimum is at `b = 0`, the place of the pole. Near-alignments at large `b`
recover the same value by recurrence, and there the pole is gone and the archimedean base has to pay.
-/

open Finset Filter Topology Set Metric
open scoped Real

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

variable {n : ℕ}

/-! ### Columns -/

/-- The sum of the columns `g_i` at the locked phases `e^{ibℓ_i}`. -/
def columnSum (g : Fin n → Circle → ℝ) (ℓ : Fin n → ℝ) (b : ℝ) : ℝ :=
  ∑ i, g i (Circle.exp (b * ℓ i))

/-- Locked phases are dense in the torus. -/
theorem mem_closure_locked {ℓ : Fin n → ℝ} (hℓ : IsKroneckerFamily ℓ) (z : Fin n → Circle) :
    z ∈ closure (Set.range fun b : ℝ => fun i => Circle.exp (b * ℓ i)) := by
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨b, hb⟩ := hℓ (fun i => Complex.arg (z i)) ε hε
  refine ⟨_, ⟨b, rfl⟩, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  have h1 := hb i
  rw [norm_sub_rev] at h1
  have hz : ((z i : Circle) : ℂ) = Complex.exp ((Complex.arg (z i) : ℂ) * Complex.I) := by
    have := Circle.exp_arg (z i)
    conv_lhs => rw [← this]
    rw [Circle.coe_exp]
  change dist ((z i : Circle) : ℂ) ((Circle.exp (b * ℓ i) : Circle) : ℂ) < ε
  rw [Circle.coe_exp, dist_eq_norm, hz]
  exact h1

/-- **Locked phases see the whole torus.** -/
theorem le_columnSum_iff {g : Fin n → Circle → ℝ} (hg : ∀ i, Continuous (g i)) {ℓ : Fin n → ℝ}
    (hℓ : IsKroneckerFamily ℓ) (A : ℝ) :
    (∀ b, A ≤ columnSum g ℓ b) ↔ ∀ z : Fin n → Circle, A ≤ ∑ i, g i (z i) := by
  refine ⟨fun h z => ?_, fun h b => h _⟩
  have hc : Continuous fun z : Fin n → Circle => ∑ i, g i (z i) :=
    continuous_finsetSum _ fun i _ => (hg i).comp (continuous_apply i)
  have hclosed : IsClosed {z : Fin n → Circle | A ≤ ∑ i, g i (z i)} :=
    isClosed_le continuous_const hc
  refine closure_minimal ?_ hclosed (mem_closure_locked hℓ z)
  rintro _ ⟨b, rfl⟩
  exact h b

/-- Each continuous column attains its minimum. -/
theorem exists_column_min {g : Fin n → Circle → ℝ} (hg : ∀ i, Continuous (g i)) :
    ∃ m : Fin n → Circle, ∀ i w, g i (m i) ≤ g i w := by
  have h : ∀ i, ∃ x : Circle, ∀ w, g i x ≤ g i w := fun i => by
    obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
      (hg i).continuousOn
    exact ⟨x, fun w => hx (Set.mem_univ w)⟩
  choose m hm using h
  exact ⟨m, hm⟩

/-- **Columns add.** The infimum over the height of a sum of columns is the sum of their minima. -/
theorem le_columnSum_iff_min {g : Fin n → Circle → ℝ} (hg : ∀ i, Continuous (g i)) {ℓ : Fin n → ℝ}
    (hℓ : IsKroneckerFamily ℓ) {m : Fin n → Circle} (hm : ∀ i w, g i (m i) ≤ g i w) (A : ℝ) :
    (∀ b, A ≤ columnSum g ℓ b) ↔ A ≤ ∑ i, g i (m i) := by
  rw [le_columnSum_iff hg hℓ]
  exact ⟨fun h => h m, fun h z => h.trans (Finset.sum_le_sum fun i _ => hm i _)⟩

/-! ### The echo symbol -/

/-- The symbol `1 − 2Σ c_i cos(bℓ_i)` of the train with echoes `c_i` at the reflectors `ℓ_i`. -/
def echoSymbol (c ℓ : Fin n → ℝ) (b : ℝ) : ℝ := 1 - 2 * ∑ i, c i * Real.cos (b * ℓ i)

/-- A train with `2Σ|c_i| ≤ 1` is passive on any reflectors. -/
theorem echoSymbol_nonneg_of_size {c : Fin n → ℝ} (ℓ : Fin n → ℝ) (hc : 2 * ∑ i, |c i| ≤ 1) (b : ℝ) :
    0 ≤ echoSymbol c ℓ b := by
  have h : ∑ i, c i * Real.cos (b * ℓ i) ≤ ∑ i, |c i| := Finset.sum_le_sum fun i _ => by
    calc c i * Real.cos (b * ℓ i) ≤ |c i * Real.cos (b * ℓ i)| := le_abs_self _
      _ = |c i| * |Real.cos (b * ℓ i)| := abs_mul _ _
      _ ≤ |c i| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |c i| := mul_one _
  rw [echoSymbol]
  linarith

/-- **Size is exact on independent reflectors.** -/
theorem echoSymbol_nonneg_iff {c ℓ : Fin n → ℝ} (hℓ : IsKroneckerFamily ℓ) :
    (∀ b, 0 ≤ echoSymbol c ℓ b) ↔ 2 * ∑ i, |c i| ≤ 1 := by
  refine ⟨fun h => ?_, fun h b => echoSymbol_nonneg_of_size ℓ h b⟩
  set g : Fin n → Circle → ℝ := fun i z => -(2 * c i * ((z : ℂ)).re) with hgd
  have hg : ∀ i, Continuous (g i) := fun i => by
    have hc : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
    exact ((continuous_const.mul (Complex.continuous_re.comp hc))).neg
  have hsum : ∀ b, -1 ≤ columnSum g ℓ b := fun b => by
    have h1 := h b
    have e : columnSum g ℓ b = -(2 * ∑ i, c i * Real.cos (b * ℓ i)) := by
      simp only [columnSum, hgd, Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e]
    rw [echoSymbol] at h1
    linarith
  have htorus := (le_columnSum_iff hg hℓ (-1)).mp hsum
    (fun i => Circle.exp (if 0 ≤ c i then 0 else π))
  have e : ∑ i, g i (Circle.exp (if 0 ≤ c i then 0 else π)) = -(2 * ∑ i, |c i|) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hgd, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    by_cases hi : 0 ≤ c i
    · rw [if_pos hi, Real.cos_zero, abs_of_nonneg hi]
      ring
    · rw [if_neg hi, Real.cos_pi, abs_of_neg (not_le.mp hi)]
      ring
  rw [e] at htorus
  linarith

/-- **A positive train is worst at the origin.** -/
theorem echoSymbol_ge_of_nonneg {c : Fin n → ℝ} (hc : ∀ i, 0 ≤ c i) (ℓ : Fin n → ℝ) (b : ℝ) :
    echoSymbol c ℓ 0 ≤ echoSymbol c ℓ b := by
  have h : ∑ i, c i * Real.cos (b * ℓ i) ≤ ∑ i, c i * Real.cos (0 * ℓ i) :=
    Finset.sum_le_sum fun i _ => by
      rw [zero_mul, Real.cos_zero]
      exact mul_le_mul_of_nonneg_left (Real.cos_le_one _) (hc i)
  simp only [echoSymbol]
  linarith

/-! ### Commensurable reflectors -/

/-- The Fejér identity: `(N + 1) + 2Σ_{k<N}(N − k)cos((k + 1)t) = |Σ_{p≤N} e^{ipt}|²`. -/
theorem fejer_identity (N : ℕ) (t : ℝ) :
    ((N : ℝ) + 1) + 2 * ∑ k ∈ range N, ((N : ℝ) - k) * Real.cos (((k : ℝ) + 1) * t) =
      (∑ p ∈ range (N + 1), Real.cos ((p : ℝ) * t)) ^ 2 +
        (∑ p ∈ range (N + 1), Real.sin ((p : ℝ) * t)) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    set a : ℝ := ((N : ℝ) + 1) * t with ha
    have hrefl : ∑ p ∈ range (N + 1), Real.cos (a - (p : ℝ) * t) =
        ∑ k ∈ range (N + 1), Real.cos (((k : ℝ) + 1) * t) := by
      rw [← Finset.sum_range_reflect (fun k : ℕ => Real.cos (((k : ℝ) + 1) * t)) (N + 1)]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      have e : ((N + 1 - 1 - p : ℕ) : ℝ) = (N : ℝ) - p := by
        rw [Nat.add_sub_cancel, Nat.cast_sub hp']
      rw [e]
      congr 1
      rw [ha]
      ring
    have hexp : ∑ p ∈ range (N + 1), Real.cos (a - (p : ℝ) * t) =
        (∑ p ∈ range (N + 1), Real.cos ((p : ℝ) * t)) * Real.cos a +
          (∑ p ∈ range (N + 1), Real.sin ((p : ℝ) * t)) * Real.sin a := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Real.cos_sub]
      ring
    have hleft : ∑ k ∈ range (N + 1), (((N + 1 : ℕ) : ℝ) - k) * Real.cos (((k : ℝ) + 1) * t) =
        ∑ k ∈ range N, ((N : ℝ) - k) * Real.cos (((k : ℝ) + 1) * t) +
          ∑ k ∈ range (N + 1), Real.cos (((k : ℝ) + 1) * t) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k : ℕ => Real.cos (((k : ℝ) + 1) * t))]
      have e : ∑ k ∈ range N, (((N + 1 : ℕ) : ℝ) - k) * Real.cos (((k : ℝ) + 1) * t) =
          ∑ k ∈ range N, ((N : ℝ) - k) * Real.cos (((k : ℝ) + 1) * t) +
            ∑ k ∈ range N, Real.cos (((k : ℝ) + 1) * t) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      rw [e]
      push_cast
      ring
    rw [hleft, Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1)]
    have hcast : ((N + 1 : ℕ) : ℝ) * t = a := by
      rw [ha]
      push_cast
      ring
    rw [hcast, ← hrefl, hexp]
    have hone := Real.sin_sq_add_cos_sq a
    push_cast
    nlinarith [ih, hone]

theorem sum_range_sub (N : ℕ) : ∑ k ∈ range N, ((N : ℝ) - k) = (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : ∑ k ∈ range (N + 1), (((N + 1 : ℕ) : ℝ) - k) =
        ∑ k ∈ range N, ((N : ℝ) - k) + ((N : ℝ) + 1) := by
      rw [Finset.sum_range_succ]
      have e2 : ∑ k ∈ range N, (((N + 1 : ℕ) : ℝ) - k) =
          ∑ k ∈ range N, ((N : ℝ) - k) + N := by
        have : ∑ k ∈ range N, (((N + 1 : ℕ) : ℝ) - k) =
            ∑ k ∈ range N, (((N : ℝ) - k) + 1) := Finset.sum_congr rfl fun k _ => by
          push_cast
          ring
        rw [this, Finset.sum_add_distrib]
        simp
      rw [e2]
      push_cast
      ring
    rw [e, ih]
    push_cast
    ring

/-- **Commensurable reflectors have room.** On the reflectors `(k + 1)ℓ₀`, the Fejér train is passive with `2Σ|c_k| = N`. On an independent
family the same mass is at most `1`. -/
theorem exists_passive_commensurable_train (ℓ₀ : ℝ) (N : ℕ) :
    ∃ c : Fin N → ℝ, 2 * ∑ i, |c i| = N ∧
      ∀ b, 0 ≤ echoSymbol c (fun k : Fin N => ((k : ℕ) + 1 : ℝ) * ℓ₀) b := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨fun k => -(((N : ℝ) - (k : ℕ)) / ((N : ℝ) + 1)), ?_, fun b => ?_⟩
  · have habs : ∀ k : Fin N, |-(((N : ℝ) - (k : ℕ)) / ((N : ℝ) + 1))| =
        ((N : ℝ) - (k : ℕ)) / ((N : ℝ) + 1) := fun k => by
      have hk : ((k : ℕ) : ℝ) ≤ N := by exact_mod_cast k.isLt.le
      rw [abs_neg, abs_of_nonneg (div_nonneg (by linarith) hN.le)]
    simp only [habs]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((N : ℝ) - k) / ((N : ℝ) + 1)) N, ← Finset.sum_div,
      sum_range_sub]
    field_simp
  · have hf := fejer_identity N (b * ℓ₀)
    have hs : ∑ i : Fin N, -(((N : ℝ) - (i : ℕ)) / ((N : ℝ) + 1)) *
        Real.cos (b * (((i : ℕ) + 1 : ℝ) * ℓ₀)) =
        -(∑ k ∈ range N, ((N : ℝ) - k) * Real.cos (((k : ℝ) + 1) * (b * ℓ₀))) / ((N : ℝ) + 1) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => ((N : ℝ) - k) * Real.cos (((k : ℝ) + 1) * (b * ℓ₀))) N,
        neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : b * (((i : ℕ) + 1 : ℝ) * ℓ₀) = (((i : ℕ) : ℝ) + 1) * (b * ℓ₀) := by ring
      rw [e]
      ring
    rw [echoSymbol, hs]
    have hsq : 0 ≤ (∑ p ∈ range (N + 1), Real.cos ((p : ℝ) * (b * ℓ₀))) ^ 2 +
        (∑ p ∈ range (N + 1), Real.sin ((p : ℝ) * (b * ℓ₀))) ^ 2 := by positivity
    rw [← hf] at hsq
    have e : ∀ X : ℝ, 1 - 2 * (-X / ((N : ℝ) + 1)) = (((N : ℝ) + 1) + 2 * X) / ((N : ℝ) + 1) := fun X => by
      field_simp
      ring
    rw [e]
    exact div_nonneg hsq hN.le

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
