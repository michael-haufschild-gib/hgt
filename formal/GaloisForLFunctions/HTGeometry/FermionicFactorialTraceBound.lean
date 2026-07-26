import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# The fermionic factorial gain

Antisymmetrising `n` copies of a positive operator replaces the `n`-th power of its trace by the
`n`-th elementary symmetric function of its spectrum, and

```
n! · e_n(λ) ≤ (∑ λ)^n.
```

This is the exact source of the `1/n!` in fermionic (Pauli) trace estimates: the trace of a
positive operator compressed to the antisymmetric subspace of an `n`-fold tensor power is
`e_n` of its eigenvalues, so it is at most `‖·‖₁^n / n!`.

Only the two elementary inequalities are needed.  Adjoining one index multiplies `e_n` by the
recursion `e_{n+1}(insert a s) = e_{n+1}(s) + f a · e_n(s)`, and the binomial theorem retains its
first two terms; together they give the bound by induction on the index set.

The multiplicity factor of an internal degree of freedom is recorded separately: tensoring with
the identity of a `d`-dimensional space multiplies the trace by `d`, so a componentwise
antisymmetrisation carries `d^n` alongside the same factorial gain.
-/

open Finset
open scoped Nat ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-! ### The elementary inequalities -/

/-- The binomial expansion retains its first two terms. -/
theorem pow_succ_two_term_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    b ^ (m + 1) + ((m : ℝ) + 1) * a * b ^ m ≤ (a + b) ^ (m + 1) := by
  induction m with
  | zero => simp; linarith
  | succ m ih =>
      have hab : (0 : ℝ) ≤ a + b := by linarith
      have hbm : (0 : ℝ) ≤ b ^ m := pow_nonneg hb m
      have hsq : (0 : ℝ) ≤ ((m : ℝ) + 1) * a ^ 2 * b ^ m := by positivity
      have hexp : (a + b) * (b ^ (m + 1) + ((m : ℝ) + 1) * a * b ^ m)
          = b ^ (m + 2) + (((m : ℝ) + 1) + 1) * a * b ^ (m + 1)
            + ((m : ℝ) + 1) * a ^ 2 * b ^ m := by ring
      have hstep : b ^ (m + 2) + (((m : ℝ) + 1) + 1) * a * b ^ (m + 1)
          ≤ (a + b) * (b ^ (m + 1) + ((m : ℝ) + 1) * a * b ^ m) := by
        rw [hexp]; linarith
      calc b ^ (m + 2) + (((m + 1 : ℕ) : ℝ) + 1) * a * b ^ (m + 1)
          = b ^ (m + 2) + (((m : ℝ) + 1) + 1) * a * b ^ (m + 1) := by push_cast; ring
        _ ≤ (a + b) * (b ^ (m + 1) + ((m : ℝ) + 1) * a * b ^ m) := hstep
        _ ≤ (a + b) * (a + b) ^ (m + 1) := by
            exact mul_le_mul_of_nonneg_left ih hab
        _ = (a + b) ^ (m + 2) := by ring

/-- Adjoining one index to the ground set: the elementary symmetric sums satisfy the Pascal
recursion `e_{n+1}(insert a s) = e_{n+1}(s) + f a · e_n(s)`. -/
theorem sum_powersetCard_succ_insert {ι : Type*} [DecidableEq ι] (f : ι → ℝ)
    {a : ι} {s : Finset ι} (ha : a ∉ s) (n : ℕ) :
    ∑ t ∈ (insert a s).powersetCard (n + 1), ∏ i ∈ t, f i =
      (∑ t ∈ s.powersetCard (n + 1), ∏ i ∈ t, f i) +
        f a * ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i := by
  have hdisj : Disjoint (s.powersetCard (n + 1)) ((s.powersetCard n).image (insert a)) := by
    refine Finset.disjoint_left.2 fun t ht htimg => ?_
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 htimg
    have hts : insert a u ⊆ s := (Finset.mem_powersetCard.1 ht).1
    exact ha (hts (Finset.mem_insert_self a u))
  have hinj : Set.InjOn (insert a) (s.powersetCard n : Set (Finset ι)) := by
    intro u hu v hv huv
    have hu' : a ∉ u := fun h => ha ((Finset.mem_powersetCard.1 hu).1 h)
    have hv' : a ∉ v := fun h => ha ((Finset.mem_powersetCard.1 hv).1 h)
    have := congrArg (fun w : Finset ι => w.erase a) huv
    simpa [Finset.erase_insert hu', Finset.erase_insert hv'] using this
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj,
    Finset.sum_image fun u hu v hv h => hinj hu hv h]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : a ∉ u := fun h => ha ((Finset.mem_powersetCard.1 hu).1 h)
  rw [Finset.prod_insert hu']

/-- **The fermionic factorial gain.**  For a nonnegative weight, the `n`-th elementary symmetric
sum is at most the `n`-th power of the total weight divided by `n!`. -/
theorem factorial_mul_sum_powersetCard_le_sum_pow {ι : Type*} [DecidableEq ι] {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (s : Finset ι) (n : ℕ) :
    (n ! : ℝ) * ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i ≤ (∑ i ∈ s, f i) ^ n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
      cases n with
      | zero => simp
      | succ m =>
          rw [Finset.powersetCard_eq_empty.mpr (by simp)]
          simp
  | @insert a s ha ih =>
      cases n with
      | zero => simp
      | succ m =>
          have hsum : (0 : ℝ) ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i _ => hf i
          rw [sum_powersetCard_succ_insert f ha m, Finset.sum_insert ha]
          have hsplit : ((m + 1)! : ℝ) *
              ((∑ t ∈ s.powersetCard (m + 1), ∏ i ∈ t, f i) +
                f a * ∑ t ∈ s.powersetCard m, ∏ i ∈ t, f i)
              = ((m + 1)! : ℝ) * ∑ t ∈ s.powersetCard (m + 1), ∏ i ∈ t, f i +
                ((m : ℝ) + 1) * f a * ((m ! : ℝ) * ∑ t ∈ s.powersetCard m, ∏ i ∈ t, f i) := by
            rw [Nat.factorial_succ]
            push_cast
            ring
          rw [hsplit]
          have h1 : ((m + 1)! : ℝ) * ∑ t ∈ s.powersetCard (m + 1), ∏ i ∈ t, f i
              ≤ (∑ i ∈ s, f i) ^ (m + 1) := ih (m + 1)
          have h2 : ((m : ℝ) + 1) * f a * ((m ! : ℝ) * ∑ t ∈ s.powersetCard m, ∏ i ∈ t, f i)
              ≤ ((m : ℝ) + 1) * f a * (∑ i ∈ s, f i) ^ m := by
            refine mul_le_mul_of_nonneg_left (ih m) ?_
            have : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
            exact mul_nonneg this (hf a)
          refine le_trans (add_le_add h1 h2) ?_
          exact pow_succ_two_term_le (hf a) hsum m

/-- The bound in divided form: the `n`-th elementary symmetric sum of a nonnegative weight is at
most `(∑ f)^n / n!`. -/
theorem sum_powersetCard_le_sum_pow_div_factorial {ι : Type*} [DecidableEq ι] {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (s : Finset ι) (n : ℕ) :
    ∑ t ∈ s.powersetCard n, ∏ i ∈ t, f i ≤ (∑ i ∈ s, f i) ^ n / (n ! : ℝ) := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact factorial_mul_sum_powersetCard_le_sum_pow hf s n

/-! ### The positive-operator form -/

/-- **Pauli trace bound.**  For a positive semidefinite matrix, the `n`-th elementary symmetric
function of its spectrum is at most `(Tr A)^n / n!`.  The eigenvalues are nonnegative and sum to
the trace, so this is the previous bound applied to the spectrum. -/
theorem sum_powersetCard_eigenvalues_le_trace_pow_div_factorial {m : Type*} [Fintype m]
    [DecidableEq m] {A : Matrix m m ℂ} (hA : A.PosSemidef) (n : ℕ) :
    ∑ t ∈ (Finset.univ : Finset m).powersetCard n, ∏ i ∈ t, hA.1.eigenvalues i
      ≤ A.trace.re ^ n / (n ! : ℝ) := by
  have htrace : ∑ i, hA.1.eigenvalues i = A.trace.re := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp
  rw [← htrace]
  exact sum_powersetCard_le_sum_pow_div_factorial hA.eigenvalues_nonneg _ n

/-! ### The internal multiplicity factor -/

/-- Tensoring with the identity of a `d`-dimensional internal space multiplies the trace by `d`.
The one-particle trace norm of `R ⊗ I_K` is therefore `d` times that of `R`. -/
theorem trace_kronecker_one {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (A : Matrix m m ℂ) :
    (Matrix.kroneckerMap (· * ·) A (1 : Matrix k k ℂ)).trace = (Fintype.card k : ℂ) * A.trace := by
  rw [Matrix.trace_kronecker, Matrix.trace_one, mul_comm]

/-- The factorial bound scaled by the internal multiplicity: `d^n` times the `n`-th elementary
symmetric function of the spectrum is at most `d^n (Tr A)^n / n!`.  This is the form the estimate
takes for a one-particle operator `A ⊗ I_K` with `dim K = d`, by `trace_kronecker_one`. -/
theorem multiplicity_mul_sum_powersetCard_eigenvalues_le {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) (d n : ℕ) :
    (d : ℝ) ^ n * ∑ t ∈ (Finset.univ : Finset m).powersetCard n, ∏ i ∈ t, hA.1.eigenvalues i
      ≤ (d : ℝ) ^ n * (A.trace.re ^ n / (n ! : ℝ)) := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact sum_powersetCard_eigenvalues_le_trace_pow_div_factorial hA n

/-! ### The componentwise permutation projection

A constant braid twist equal to `-I` on the internal factor generates a permutation action that
exchanges only the external (rapidity) variables, carrying the sign.  Its invariant subspace is
componentwise rapidity antisymmetry — antisymmetry in the external variable for each fixed internal
index tuple — and the corresponding projection is the antisymmetriser applied to the external
variable alone. -/

variable {m k : Type*} {n : ℕ}

/-- An `n`-particle amplitude, written in external (rapidity) and internal indices. -/
abbrev ParticleTensor (m k : Type*) (n : ℕ) : Type _ := (Fin n → m) → (Fin n → k) → ℂ

/-- The identity-zero braid twist: exchange of the external variables alone, with the sign of the
permutation.  The internal indices are untouched. -/
def identityZeroTwist (σ : Equiv.Perm (Fin n)) (v : ParticleTensor m k n) : ParticleTensor m k n :=
  fun x y => ((Equiv.Perm.sign σ : ℤ) : ℂ) * v (x ∘ σ) y

/-- The twist is a representation of the permutation group. -/
theorem identityZeroTwist_one (v : ParticleTensor m k n) : identityZeroTwist 1 v = v := by
  funext x y
  simp [identityZeroTwist]

theorem identityZeroTwist_mul (σ τ : Equiv.Perm (Fin n)) (v : ParticleTensor m k n) :
    identityZeroTwist (σ * τ) v = identityZeroTwist σ (identityZeroTwist τ v) := by
  funext x y
  simp only [identityZeroTwist, Equiv.Perm.coe_mul, map_mul, Units.val_mul, Int.cast_mul]
  rw [← Function.comp_assoc]
  ring

/-- The projection onto the componentwise rapidity-antisymmetric subspace. -/
noncomputable def componentwiseAntisymmetrizer (v : ParticleTensor m k n) :
    ParticleTensor m k n :=
  fun x y => (n ! : ℂ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * v (x ∘ σ) y

theorem card_perm_fin (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = n ! := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- The antisymmetriser lands in the invariant subspace of the twist. -/
theorem identityZeroTwist_componentwiseAntisymmetrizer (τ : Equiv.Perm (Fin n))
    (v : ParticleTensor m k n) :
    identityZeroTwist τ (componentwiseAntisymmetrizer v) = componentwiseAntisymmetrizer v := by
  funext x y
  simp only [identityZeroTwist, componentwiseAntisymmetrizer]
  rw [← mul_assoc, mul_comm (((Equiv.Perm.sign τ : ℤ) : ℂ)) ((n ! : ℂ)⁻¹), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft τ)
    (fun ρ : Equiv.Perm (Fin n) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * v (x ∘ ρ) y)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.coe_mulLeft, map_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.coe_mul,
    ← Function.comp_assoc]
  ring

/-- A vector fixed by the whole twist representation is fixed by the antisymmetriser. -/
theorem componentwiseAntisymmetrizer_eq_self_of_invariant {v : ParticleTensor m k n}
    (hv : ∀ σ : Equiv.Perm (Fin n), identityZeroTwist σ v = v) :
    componentwiseAntisymmetrizer v = v := by
  funext x y
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * v (x ∘ σ) y = v x y := by
    intro σ
    exact congrFun (congrFun (hv σ) x) y
  have hfac : (n ! : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [componentwiseAntisymmetrizer, Finset.sum_congr rfl fun σ _ => hterm σ,
    Finset.sum_const, Finset.card_univ, card_perm_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

/-- **The projection.**  The componentwise antisymmetriser is idempotent. -/
theorem componentwiseAntisymmetrizer_idempotent (v : ParticleTensor m k n) :
    componentwiseAntisymmetrizer (componentwiseAntisymmetrizer v) =
      componentwiseAntisymmetrizer v :=
  componentwiseAntisymmetrizer_eq_self_of_invariant
    (fun σ => identityZeroTwist_componentwiseAntisymmetrizer σ v)

/-- **Range of the projection.**  The antisymmetriser fixes exactly the invariant vectors of the
identity-zero twist: componentwise rapidity antisymmetry. -/
theorem componentwiseAntisymmetrizer_eq_self_iff (v : ParticleTensor m k n) :
    componentwiseAntisymmetrizer v = v ↔
      ∀ σ : Equiv.Perm (Fin n), identityZeroTwist σ v = v := by
  constructor
  · intro hv σ
    rw [← hv]
    exact identityZeroTwist_componentwiseAntisymmetrizer σ v
  · exact componentwiseAntisymmetrizer_eq_self_of_invariant

/-- Invariance stated as antisymmetry in the external variable, for each fixed internal tuple. -/
theorem identityZeroTwist_eq_self_iff_antisymm (v : ParticleTensor m k n) :
    (∀ σ : Equiv.Perm (Fin n), identityZeroTwist σ v = v) ↔
      ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → m) (y : Fin n → k),
        v (x ∘ σ) y = ((Equiv.Perm.sign σ : ℤ) : ℂ) * v x y := by
  constructor
  · intro hv σ x y
    have h := congrFun (congrFun (hv σ) x) y
    have hsign : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    calc v (x ∘ σ) y
        = 1 * v (x ∘ σ) y := (one_mul _).symm
      _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (((Equiv.Perm.sign σ : ℤ) : ℂ) * v (x ∘ σ) y) := by rw [← mul_assoc, hsign]
      _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) * v x y := by rw [show
            ((Equiv.Perm.sign σ : ℤ) : ℂ) * v (x ∘ σ) y = v x y from h]
  · intro hv σ
    funext x y
    simp only [identityZeroTwist, hv σ x y]
    have hsign : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    rw [← mul_assoc, hsign, one_mul]

end GaloisForLFunctions.HTGeometry
