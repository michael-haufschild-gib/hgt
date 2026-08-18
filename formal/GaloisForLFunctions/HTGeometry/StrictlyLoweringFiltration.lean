import Mathlib

/-!
# Strictly filtration-lowering operators are determinant-blind

An operator `B` that maps each step `E_n` of an increasing filtration into the previous step
`E_{n-1}` (with `E_{-1} = 0`) is locally nilpotent, has only the eigenvalue `0` on the filtration,
and — in any basis adapted to the filtration — has strictly triangular matrix.  Hence every finite
truncation satisfies `det (1 + z B) = 1` and every positive power is traceless.

The typical source is a pair of operators inducing the *same* scalar on every graded quotient:
`strictlyLowering_sub_of_graded` shows their difference lowers the filtration strictly.  That is
exactly the situation of two number operators attached to a common polynomial filtration.

Main results:

* `StrictlyLowering.pow_apply_eq_zero` — local nilpotence `B^{n+1}|_{E_n} = 0`;
* `StrictlyLowering.eigenvalue_eq_zero` — only the zero eigenvalue occurs on the filtration;
* `det_one_add_smul_of_adapted` — `det (1 + z B) = 1` on every adapted finite truncation;
* `trace_pow_eq_zero_of_adapted` — every positive power of the truncation is traceless;
* `pow_eq_zero_of_strictlyUpper` — the truncation is nilpotent of index at most its size.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.HTGeometry.StrictlyLowering

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ## Strictly filtration-lowering operators -/

/-- An operator strictly lowering a filtration: it kills the bottom step and drops every higher
step by one.  This is the abstract form of `B_P (E_n) ⊆ E_{n-1}` with `E_{-1} = 0`. -/
structure StrictlyLowering (E : ℕ → Submodule K V) (B : V →ₗ[K] V) : Prop where
  mono : Monotone E
  bottom : ∀ v ∈ E 0, B v = 0
  step : ∀ n : ℕ, ∀ v ∈ E (n + 1), B v ∈ E n

variable {E : ℕ → Submodule K V} {B : V →ₗ[K] V}

theorem StrictlyLowering.mapsTo (h : StrictlyLowering E B) (n : ℕ) {v : V} (hv : v ∈ E n) :
    B v ∈ E n := by
  cases n with
  | zero =>
      rw [h.bottom v hv]
      exact Submodule.zero_mem _
  | succ k => exact h.mono (Nat.le_succ k) (h.step k v hv)

/-- **Local nilpotence.**  `B^{n+1}` annihilates `E_n`. -/
theorem StrictlyLowering.pow_apply_eq_zero (h : StrictlyLowering E B) :
    ∀ (n : ℕ) {v : V}, v ∈ E n → (B ^ (n + 1)) v = 0 := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simpa using h.bottom v hv
  | succ k ih =>
      intro v hv
      have h1 : B v ∈ E k := h.step k v hv
      have h2 := ih h1
      have hsplit : (B ^ (k + 1 + 1)) v = (B ^ (k + 1)) (B v) := by
        rw [pow_succ]
        rfl
      rw [hsplit, h2]

/-- **The graded criterion.**  Two operators inducing the same scalar on every graded quotient
differ by a strictly lowering operator. -/
theorem strictlyLowering_sub_of_graded {E : ℕ → Submodule K V} (hmono : Monotone E)
    (N₁ N₂ : V →ₗ[K] V) (c : ℕ → K)
    (hbot : ∀ v ∈ E 0, N₁ v = c 0 • v ∧ N₂ v = c 0 • v)
    (hstep : ∀ n : ℕ, ∀ v ∈ E (n + 1),
      N₁ v - c (n + 1) • v ∈ E n ∧ N₂ v - c (n + 1) • v ∈ E n) :
    StrictlyLowering E (N₁ - N₂) := by
  refine ⟨hmono, ?_, ?_⟩
  · intro v hv
    obtain ⟨h1, h2⟩ := hbot v hv
    simp only [LinearMap.sub_apply, h1, h2, sub_self]
  · intro n v hv
    obtain ⟨h1, h2⟩ := hstep n v hv
    have : (N₁ - N₂) v = (N₁ v - c (n + 1) • v) - (N₂ v - c (n + 1) • v) := by
      simp only [LinearMap.sub_apply]
      abel
    rw [this]
    exact Submodule.sub_mem _ h1 h2

/-- Only the zero scalar occurs as an eigenvalue on the filtration. -/
theorem StrictlyLowering.eigenvalue_eq_zero (h : StrictlyLowering E B) {n : ℕ} {v : V}
    (hv : v ∈ E n) (hne : v ≠ 0) {lam : K} (heig : B v = lam • v) : lam = 0 := by
  have hpow : ∀ k : ℕ, (B ^ k) v = lam ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have hstep : (B ^ (j + 1)) v = B ((B ^ j) v) := by
          rw [pow_succ']
          rfl
        rw [hstep, ih, LinearMap.map_smul, heig, smul_smul]
        congr 1
        ring
  have hzero := h.pow_apply_eq_zero n hv
  rw [hpow] at hzero
  rcases smul_eq_zero.mp hzero with hl | hv0
  · exact pow_eq_zero_iff'.mp hl |>.1
  · exact absurd hv0 hne

/-! ## Strictly triangular matrices -/

variable {N : ℕ}

/-- A strictly upper triangular matrix: every entry on or below the diagonal vanishes. -/
def StrictlyUpper (M : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j : Fin N, (j : ℕ) ≤ i → M i j = 0

/-- **Determinant blindness.**  `det (1 + z M) = 1` for every strictly triangular `M`. -/
theorem det_one_add_smul_of_strictlyUpper {M : Matrix (Fin N) (Fin N) K}
    (hM : StrictlyUpper M) (z : K) : (1 + z • M).det = 1 := by
  have htri : (1 + z • M).BlockTriangular id := by
    intro i j hij
    have hji : (j : ℕ) ≤ (i : ℕ) := le_of_lt (by exact_mod_cast hij)
    have hlt : (j : ℕ) < (i : ℕ) := by exact_mod_cast hij
    have hne : i ≠ j := by
      intro hcon
      rw [hcon] at hlt
      omega
    simp only [Matrix.add_apply, Matrix.smul_apply, hM i j hji, smul_zero, add_zero]
    exact Matrix.one_apply_ne hne
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one (fun i _ => ?_)
  simp [hM i i le_rfl]

/-- Powers of a strictly triangular matrix are supported strictly further above the diagonal. -/
theorem strictlyUpper_pow {M : Matrix (Fin N) (Fin N) K} (hM : StrictlyUpper M) :
    ∀ (k : ℕ) (i j : Fin N), (j : ℕ) < (i : ℕ) + k + 1 → (M ^ (k + 1)) i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      rw [pow_one]
      exact hM i j (by omega)
  | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      by_cases hl : (l : ℕ) < (i : ℕ) + k + 1
      · rw [ih i l hl, zero_mul]
      · rw [hM l j (by omega), mul_zero]

/-- Every power of a strictly triangular matrix is traceless. -/
theorem trace_pow_eq_zero_of_strictlyUpper {M : Matrix (Fin N) (Fin N) K}
    (hM : StrictlyUpper M) (k : ℕ) : (M ^ (k + 1)).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact strictlyUpper_pow hM k i i (by omega)

/-- A strictly triangular matrix is nilpotent of index at most its size. -/
theorem pow_eq_zero_of_strictlyUpper {M : Matrix (Fin N) (Fin N) K} (hM : StrictlyUpper M) :
    M ^ N = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact Subsingleton.elim _ _
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    ext i j
    rw [Matrix.zero_apply]
    exact strictlyUpper_pow hM k i j (by omega)

/-! ## The adapted basis -/

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Coordinates outside the spanning set vanish. -/
theorem repr_eq_zero_of_mem_span {ι : Type*} [DecidableEq ι] (b : Module.Basis ι K W) (s : Set ι)
    {x : W} (hx : x ∈ Submodule.span K (b '' s)) {i : ι} (hi : i ∉ s) : b.repr x i = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hji : j ≠ i := fun hcon => hi (hcon ▸ hj)
      simp [Module.Basis.repr_self, Finsupp.single_apply, hji]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

/-- **In a basis adapted to the filtration the matrix is strictly triangular.** -/
theorem strictlyUpper_toMatrix {N : ℕ} (b : Module.Basis (Fin N) K W) (B : W →ₗ[K] W)
    (hB : ∀ j : Fin N, B (b j) ∈ Submodule.span K (b '' {i : Fin N | (i : ℕ) < (j : ℕ)})) :
    StrictlyUpper (LinearMap.toMatrix b b B) := by
  classical
  intro i j hij
  rw [LinearMap.toMatrix_apply]
  exact repr_eq_zero_of_mem_span b _ (hB j) (by simpa using hij)

/-- **Equation (3).**  On every finite adapted truncation the perturbed determinant is one. -/
theorem det_one_add_smul_of_adapted {N : ℕ} (b : Module.Basis (Fin N) K W) (B : W →ₗ[K] W)
    (hB : ∀ j : Fin N, B (b j) ∈ Submodule.span K (b '' {i : Fin N | (i : ℕ) < (j : ℕ)}))
    (z : K) : LinearMap.det (LinearMap.id + z • B) = 1 := by
  classical
  have hfin : Module.Finite K W := Module.Finite.of_basis b
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id, map_smul]
  exact det_one_add_smul_of_strictlyUpper (strictlyUpper_toMatrix b B hB) z

/-- **Traceless powers.**  Every positive power of an adapted strictly lowering operator has zero
trace. -/
theorem trace_pow_eq_zero_of_adapted {N : ℕ} (b : Module.Basis (Fin N) K W) (B : W →ₗ[K] W)
    (hB : ∀ j : Fin N, B (b j) ∈ Submodule.span K (b '' {i : Fin N | (i : ℕ) < (j : ℕ)}))
    (k : ℕ) : ((LinearMap.toMatrix b b B) ^ (k + 1)).trace = 0 :=
  trace_pow_eq_zero_of_strictlyUpper (strictlyUpper_toMatrix b B hB) k

end GaloisForLFunctions.HTGeometry.StrictlyLowering

namespace GaloisForLFunctions.HTGeometry.StrictlyLowering

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Scalar multiples of a strictly lowering operator are strictly lowering, so the same
conclusions hold for `λ² B`. -/
theorem StrictlyLowering.smul {E : ℕ → Submodule K V} {B : V →ₗ[K] V}
    (h : StrictlyLowering E B) (c : K) : StrictlyLowering E (c • B) := by
  refine ⟨h.mono, ?_, ?_⟩
  · intro v hv
    show c • B v = 0
    rw [h.bottom v hv, smul_zero]
  · intro n v hv
    show c • B v ∈ E n
    exact Submodule.smul_mem _ c (h.step n v hv)

/-- **Determinant blindness is compatible with a fully populated matrix.**  Every entry above the
diagonal may be nonzero and the perturbed determinant is still one; nonzero low-mode or all-mode
coefficients therefore do not contradict the blindness statement. -/
theorem det_one_add_smul_full (N : ℕ) (z : K) :
    ((1 : Matrix (Fin N) (Fin N) K)
      + z • (Matrix.of (fun i j : Fin N => if (i : ℕ) < (j : ℕ) then (1 : K) else 0))).det = 1 := by
  refine det_one_add_smul_of_strictlyUpper (fun i j hij => ?_) z
  exact if_neg (by omega)

end GaloisForLFunctions.HTGeometry.StrictlyLowering
