import Mathlib
import GaloisForLFunctions.RHTower.SchattenApproximation
import GaloisForLFunctions.HTGeometry.SchattenApproximationAdditivity
import GaloisForLFunctions.HTGeometry.VonNeumannDeficiency

/-!
# Half-line Jacobi deficiency indices and the rank-two boundary ambiguity

A formal half-line Jacobi matrix with nonvanishing off-diagonal coefficients defines a second-order
recurrence together with one left boundary equation.  Two facts follow from that shape alone:

* a solution is determined by its first coordinate, so the space of solutions at any spectral
  parameter is at most one-dimensional;
* for *real* coefficients, complex conjugation is a bijection between the square-summable solutions
  at `z` and at `conj z`, so the two deficiency spaces are simultaneously trivial.

Hence the deficiency indices are `(0,0)` or `(1,1)`; in the second case von Neumann's construction
supplies a self-adjoint extension.  The boundary ambiguity that remains is finite rank, and finite
rank is invisible to every Schatten ideal: two operators differing by a finite-rank operator lie in
exactly the same Schatten classes.  For a direct sum of two parity blocks the ambiguity has rank at
most two.
-/

namespace RHTower

open scoped BigOperators
open Filter Topology

/-! ## The half-line Jacobi recurrence -/

section Jacobi

variable {a b : ℕ → ℝ} {z : ℂ} {u v : ℕ → ℂ}

/-- A solution of the formal half-line Jacobi recurrence `a_{n-1}u_{n-1} + b_n u_n + a_n u_{n+1}
= z u_n`, together with its left boundary equation at `n = 0`. -/
structure IsJacobiSolution (a b : ℕ → ℝ) (z : ℂ) (u : ℕ → ℂ) : Prop where
  base : (b 0 : ℂ) * u 0 + (a 0 : ℂ) * u 1 = z * u 0
  step : ∀ n : ℕ, (a n : ℂ) * u n + (b (n + 1) : ℂ) * u (n + 1)
      + (a (n + 1) : ℂ) * u (n + 2) = z * u (n + 1)

/-- **A Jacobi solution is determined by its first coordinate.**  This is the whole content of the
deficiency-index bound: the boundary equation fixes `u 1` from `u 0`, and the recurrence propagates
the pair forward. -/
theorem IsJacobiSolution.ext (ha : ∀ n, a n ≠ 0) (hu : IsJacobiSolution a b z u)
    (hv : IsJacobiSolution a b z v) (h0 : u 0 = v 0) : u = v := by
  have hpair : ∀ n : ℕ, u n = v n ∧ u (n + 1) = v (n + 1) := by
    intro n
    induction n with
    | zero =>
        refine ⟨h0, ?_⟩
        have h1 := hu.base
        have h2 := hv.base
        rw [h0] at h1
        have hstep : (a 0 : ℂ) * u 1 = (a 0 : ℂ) * v 1 := by linear_combination h1 - h2
        have hne : ((a 0 : ℝ) : ℂ) ≠ 0 := by simpa using ha 0
        exact mul_left_cancel₀ hne hstep
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have h1 := hu.step n
        have h2 := hv.step n
        rw [ih.1, ih.2] at h1
        have hstep : (a (n + 1) : ℂ) * u (n + 2) = (a (n + 1) : ℂ) * v (n + 2) := by
          linear_combination h1 - h2
        have hne : ((a (n + 1) : ℝ) : ℂ) ≠ 0 := by simpa using ha (n + 1)
        exact mul_left_cancel₀ hne hstep
  funext n
  exact (hpair n).1

/-- The space of solutions at a fixed spectral parameter. -/
def jacobiSolutions (a b : ℕ → ℝ) (z : ℂ) : Submodule ℂ (ℕ → ℂ) where
  carrier := {u | IsJacobiSolution a b z u}
  zero_mem' := ⟨by simp, fun n => by simp⟩
  add_mem' := fun {u v} hu hv =>
    ⟨by
        simp only [Pi.add_apply]
        linear_combination IsJacobiSolution.base hu + IsJacobiSolution.base hv,
      fun n => by
        simp only [Pi.add_apply]
        linear_combination IsJacobiSolution.step hu n + IsJacobiSolution.step hv n⟩
  smul_mem' := fun c {u} hu =>
    ⟨by
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination c * IsJacobiSolution.base hu,
      fun n => by
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination c * IsJacobiSolution.step hu n⟩

@[simp] theorem mem_jacobiSolutions :
    u ∈ jacobiSolutions a b z ↔ IsJacobiSolution a b z u := Iff.rfl

/-- **The solution space is at most one-dimensional.**  Evaluation at the first coordinate is
injective on it. -/
theorem rank_jacobiSolutions_le_one (ha : ∀ n, a n ≠ 0) :
    Module.rank ℂ (jacobiSolutions a b z) ≤ 1 := by
  set ev : jacobiSolutions a b z →ₗ[ℂ] ℂ :=
    (LinearMap.proj 0 : (ℕ → ℂ) →ₗ[ℂ] ℂ).comp (jacobiSolutions a b z).subtype with hev
  have hinj : Function.Injective ev := by
    intro x y hxy
    refine Subtype.ext (IsJacobiSolution.ext ha (mem_jacobiSolutions.mp x.property)
      (mem_jacobiSolutions.mp y.property) ?_)
    simpa [hev] using hxy
  calc Module.rank ℂ (jacobiSolutions a b z) ≤ Module.rank ℂ ℂ :=
        LinearMap.rank_le_of_injective ev hinj
    _ = 1 := CommSemiring.rank_self ℂ

/-- Complex conjugation carries solutions at `z` to solutions at `conj z`; the Jacobi coefficients
are real. -/
theorem IsJacobiSolution.conj (hu : IsJacobiSolution a b z u) :
    IsJacobiSolution a b ((starRingEnd ℂ) z) (fun n => (starRingEnd ℂ) (u n)) := by
  constructor
  · have h := congrArg (starRingEnd ℂ) (IsJacobiSolution.base hu)
    simpa [map_add, map_mul, Complex.conj_ofReal] using h
  · intro n
    have h := congrArg (starRingEnd ℂ) (IsJacobiSolution.step hu n)
    simpa [map_add, map_mul, Complex.conj_ofReal] using h

end Jacobi

/-! ## The deficiency spaces -/

section Deficiency

/-- The square-summable sequences, as a subspace of all sequences. -/
def sqSummable : Submodule ℂ (ℕ → ℂ) where
  carrier := {u | Memℓp u 2}
  zero_mem' := zero_memℓp
  add_mem' := fun hu hv => Memℓp.add hu hv
  smul_mem' := fun c _ hu => hu.const_smul c

theorem mem_sqSummable_iff (u : ℕ → ℂ) :
    u ∈ sqSummable ↔ Summable fun n => ‖u n‖ ^ 2 := by
  show Memℓp u 2 ↔ _
  rw [memℓp_gen_iff (by norm_num)]
  constructor
  · intro h; simpa using h
  · intro h; simpa using h

/-- The deficiency space at a spectral parameter: square-summable Jacobi solutions. -/
def jacobiDeficiency (a b : ℕ → ℝ) (z : ℂ) : Submodule ℂ (ℕ → ℂ) :=
  jacobiSolutions a b z ⊓ sqSummable

/-- **The deficiency space is at most one-dimensional.** -/
theorem rank_jacobiDeficiency_le_one (a b : ℕ → ℝ) (ha : ∀ n, a n ≠ 0) (z : ℂ) :
    Module.rank ℂ (jacobiDeficiency a b z) ≤ 1 :=
  le_trans (Submodule.rank_mono inf_le_left) (rank_jacobiSolutions_le_one (b := b) (z := z) ha)

theorem mem_jacobiDeficiency_conj {a b : ℕ → ℝ} {z : ℂ} {u : ℕ → ℂ}
    (hu : u ∈ jacobiDeficiency a b z) :
    (fun n => (starRingEnd ℂ) (u n)) ∈ jacobiDeficiency a b ((starRingEnd ℂ) z) := by
  rw [jacobiDeficiency, Submodule.mem_inf] at hu ⊢
  refine ⟨IsJacobiSolution.conj (mem_jacobiSolutions.mp hu.1), ?_⟩
  rw [mem_sqSummable_iff]
  refine ((mem_sqSummable_iff u).mp hu.2).congr fun n => ?_
  simp

/-- **The deficiency indices are equal.**  Conjugation is a bijection between the two deficiency
spaces, so they vanish together: the indices are `(0,0)` or `(1,1)`. -/
theorem jacobiDeficiency_eq_bot_iff_conj (a b : ℕ → ℝ) (z : ℂ) :
    jacobiDeficiency a b z = ⊥ ↔ jacobiDeficiency a b ((starRingEnd ℂ) z) = ⊥ := by
  have key : ∀ w : ℂ, jacobiDeficiency a b w = ⊥ →
      jacobiDeficiency a b ((starRingEnd ℂ) w) = ⊥ := by
    intro w hw
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxc := mem_jacobiDeficiency_conj hx
    rw [Complex.conj_conj] at hxc
    have : (fun n => (starRingEnd ℂ) (x n)) = 0 := by
      rw [Submodule.eq_bot_iff] at hw
      exact hw _ hxc
    funext n
    have hn := congrFun this n
    simpa using congrArg (starRingEnd ℂ) hn
  refine ⟨key z, fun h => ?_⟩
  have := key _ h
  rwa [Complex.conj_conj] at this

/-- **The deficiency dichotomy for a real half-line Jacobi matrix.**  Both deficiency spaces are at
most one-dimensional, and they are trivial together. -/
theorem jacobi_deficiency_indices (a b : ℕ → ℝ) (ha : ∀ n, a n ≠ 0) :
    (∀ z : ℂ, Module.rank ℂ (jacobiDeficiency a b z) ≤ 1) ∧
      (jacobiDeficiency a b Complex.I = ⊥ ↔ jacobiDeficiency a b (-Complex.I) = ⊥) := by
  refine ⟨rank_jacobiDeficiency_le_one a b ha, ?_⟩
  have h := jacobiDeficiency_eq_bot_iff_conj a b Complex.I
  rwa [Complex.conj_I] at h

end Deficiency

/-! ## Existence of a self-adjoint extension in the `(1,1)` case -/

section Extension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Equal one-dimensional deficiency indices give a self-adjoint extension.**  This is von
Neumann's boundary construction, packaged as an existence statement. -/
theorem exists_isSelfAdjoint_extension_of_deficiency_one {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    {p m : S.adjoint.domain}
    (hp : S.adjoint p = Complex.I • (p : H))
    (hm : S.adjoint m = (-Complex.I) • (m : H))
    (hp0 : (p : H) ≠ 0) (hnorm : ‖(p : H)‖ = ‖(m : H)‖)
    (hspanP : ∀ x : S.adjoint.domain, S.adjoint x = Complex.I • (x : H) →
      ∃ alpha : ℂ, (x : H) = alpha • (p : H))
    (hspanM : ∀ x : S.adjoint.domain, S.adjoint x = (-Complex.I) • (x : H) →
      ∃ beta : ℂ, (x : H) = beta • (m : H)) :
    ∃ A : H →ₗ.[ℂ] H, S ≤ A ∧ IsSelfAdjoint A :=
  ⟨LinearPMap.deficiencyExtension hDense hSymm p m 1,
    LinearPMap.le_deficiencyExtension hDense hSymm p m 1,
    LinearPMap.deficiencyExtension_isSelfAdjoint hDense hSymm hp hm hp0 hnorm (by simp)
      hspanP hspanM⟩

end Extension

/-! ## The finite-rank boundary ambiguity is invisible to the Schatten ideals -/

section RankAmbiguity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hasRankLE_neg {X : H →L[ℂ] H} {n : ℕ} (hX : HasRankLE X n) : HasRankLE (-X) n := by
  obtain ⟨V, hV, hVle, hVmem⟩ := hX
  exact ⟨V, hV, hVle, fun x => by simpa using V.neg_mem (hVmem x)⟩

/-- **Ranks add.**  The parity-block direct sum of two rank-one boundary corrections has rank at
most two. -/
theorem hasRankLE_add {X Y : H →L[ℂ] H} {m n : ℕ} (hX : HasRankLE X m) (hY : HasRankLE Y n) :
    HasRankLE (X + Y) (m + n) := by
  obtain ⟨V, hV, hVle, hVmem⟩ := hX
  obtain ⟨W, hW, hWle, hWmem⟩ := hY
  refine ⟨V ⊔ W, Submodule.finiteDimensional_sup V W, ?_, ?_⟩
  · exact le_trans (Submodule.finrank_add_le_finrank_add_finrank V W) (Nat.add_le_add hVle hWle)
  · intro x
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hVmem x))
      (Submodule.mem_sup_right (hWmem x))

theorem hasRankLE_sub {X Y : H →L[ℂ] H} {n : ℕ} (h : HasRankLE (X - Y) n) :
    HasRankLE (Y - X) n := by
  have hneg : Y - X = -(X - Y) := by abel
  rw [hneg]
  exact hasRankLE_neg h

end RankAmbiguity

section SchattenStability

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Schatten membership is unchanged by a finite-rank boundary correction.**  If two relative
resolvent corners differ by an operator of finite rank — as the corners of two self-adjoint
extensions with deficiency index one do — then one lies in the Schatten `p`-class exactly when the
other does. -/
theorem memSchattenClass_congr_of_hasRankLE {p : ℝ} (hp : 0 < p) {A B : H →L[ℂ] H} {n : ℕ}
    (h : HasRankLE (A - B) n) : MemSchattenClass p A ↔ MemSchattenClass p B := by
  constructor
  · intro hA
    have hBA : B = A + (B - A) := by abel
    rw [hBA]
    exact GaloisForLFunctions.HTGeometry.memSchattenClass_add hp hA
      (memSchattenClass_of_hasRankLE hp (hasRankLE_sub h))
  · intro hB
    have hAB : A = B + (A - B) := by abel
    rw [hAB]
    exact GaloisForLFunctions.HTGeometry.memSchattenClass_add hp hB
      (memSchattenClass_of_hasRankLE hp h)

/-- **The rank-two ambiguity of a two-block boundary choice is Schatten-invisible.**  If the two
parity-block corrections have rank at most one each, the total correction has rank at most two, and
Schatten membership of the corner is the same for both extensions. -/
theorem memSchattenClass_congr_of_two_block {p : ℝ} (hp : 0 < p) {A B X Y : H →L[ℂ] H}
    (hX : HasRankLE X 1) (hY : HasRankLE Y 1) (hAB : A - B = X + Y) :
    HasRankLE (A - B) 2 ∧ (MemSchattenClass p A ↔ MemSchattenClass p B) := by
  have hrank : HasRankLE (A - B) 2 := by
    rw [hAB]
    exact hasRankLE_add hX hY
  exact ⟨hrank, memSchattenClass_congr_of_hasRankLE hp hrank⟩

end SchattenStability

end RHTower
