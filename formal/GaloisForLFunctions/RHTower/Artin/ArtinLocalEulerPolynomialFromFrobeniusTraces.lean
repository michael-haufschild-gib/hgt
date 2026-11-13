import GaloisForLFunctions.RHTower.Artin.ArtinFrobeniusTracesOfAnInducedFunction
import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactor
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.HTGeometry.SchurTriangulation
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# The local Euler polynomial is determined by its Frobenius traces

For a polynomial `P` with `P(0) = 1` the power traces `a_m`, `m ≥ 1`, are the coefficients of
`−X P'/P = Σ_{m ≥ 1} a_m X^m`. Without division, in the ring of power series,

  `P · Σ_{m ≥ 0} a_m X^m = a_0 P − X P'`   (`HasPowerTraces`).

* `1 − tX` has the power traces `t^m`; a product has the sum of the power traces; `P(X^f)` has
  the power traces `f a_{m/f}` for `f ∣ m` and `0` otherwise (`hasPowerTraces_one_sub_C_mul_X`,
  `HasPowerTraces.mul`, `HasPowerTraces.expand`).
* **Newton** (`HasPowerTraces.eq_of_coeff_zero`). The equation is the recursion
  `(n+1) p_{n+1} = −Σ_{i+j=n} p_i a_{j+1}`, so the power traces and `P(0)` determine `P`.
  Conversely `P` with `P(0) = 1` determines `a_m` for `m ≥ 1` (`HasPowerTraces.traces_eq`).
* **Operators** (`hasPowerTraces_charpoly_reverse`). `det(1 − X A)` has the power traces
  `tr(A^m)`: triangulate `A`.
* **Inertia invariants** (`trace_toInvariants`). For a normal subgroup `I` the trace of `g` on
  `V^I` is the mean of the character over the coset `g I`: the mean of `ρ` over `I` is a
  projection onto `V^I`.

Hence Artin's local polynomial `det(1 − X φ | V^I)` has the power traces `a_m(χ; I, φ)` of the
character `χ` (`hasPowerTraces_localEulerPolynomial`), and it is the only polynomial with
constant term `1` that has them.
-/

open scoped Classical BigOperators
open Polynomial

noncomputable section

universe u w

namespace GaloisForLFunctions

/-! ### Power traces -/

/-- `a` are the power traces of `P`: `P · Σ_m a_m X^m = a_0 P − X P'`. -/
def HasPowerTraces (P : ℂ[X]) (a : ℕ → ℂ) : Prop :=
  (P : PowerSeries ℂ) * PowerSeries.mk a =
    PowerSeries.C (a 0) * (P : PowerSeries ℂ) -
      PowerSeries.X * ((derivative P : ℂ[X]) : PowerSeries ℂ)

theorem hasPowerTraces_one : HasPowerTraces 1 fun _ => 0 := by
  unfold HasPowerTraces
  rw [derivative_one, Polynomial.coe_zero, mul_zero, sub_zero, map_zero, zero_mul]
  ext n
  rw [Polynomial.coe_one, one_mul, PowerSeries.coeff_mk, map_zero]

/-- `1 − tX` has the power traces `t^m`: `(1 − tX) Σ_m t^m X^m = 1`. -/
theorem hasPowerTraces_one_sub_C_mul_X (t : ℂ) :
    HasPowerTraces (1 - C t * X) fun m => t ^ m := by
  unfold HasPowerTraces
  have hd : derivative (1 - C t * X : ℂ[X]) = -C t := by
    rw [derivative_sub, derivative_one, derivative_C_mul, derivative_X, mul_one, zero_sub]
  have hgeom : ((1 - C t * X : ℂ[X]) : PowerSeries ℂ) * PowerSeries.mk (fun m => t ^ m) = 1 := by
    rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X]
    ext n
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, mul_assoc, PowerSeries.coeff_C_mul]
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, pow_zero, PowerSeries.coeff_zero_one]
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, pow_succ', sub_self,
        PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
  rw [hgeom, hd]
  beta_reduce
  rw [pow_zero, map_one, one_mul, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_neg, Polynomial.coe_C, Polynomial.coe_X]
  ring

/-- Power traces add under products. -/
theorem HasPowerTraces.mul {P Q : ℂ[X]} {a b : ℕ → ℂ} (hP : HasPowerTraces P a)
    (hQ : HasPowerTraces Q b) : HasPowerTraces (P * Q) fun m => a m + b m := by
  unfold HasPowerTraces at *
  have hmk : PowerSeries.mk (fun m => a m + b m) = PowerSeries.mk a + PowerSeries.mk b := by
    ext n
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rw [hmk, derivative_mul, Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_mul,
    Polynomial.coe_mul, map_add]
  linear_combination (Q : PowerSeries ℂ) * hP + (P : PowerSeries ℂ) * hQ

/-- Only the power traces `a_m` with `m ≥ 1` matter. -/
theorem HasPowerTraces.congr {P : ℂ[X]} {a b : ℕ → ℂ} (hP : HasPowerTraces P a)
    (h : ∀ m, 1 ≤ m → a m = b m) : HasPowerTraces P b := by
  unfold HasPowerTraces at *
  have hmk : PowerSeries.mk b = PowerSeries.mk a + PowerSeries.C (b 0 - a 0) := by
    ext n
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_C]
    cases n with
    | zero => rw [if_pos rfl, add_sub_cancel]
    | succ n => rw [if_neg (Nat.succ_ne_zero n), add_zero, h (n + 1) (Nat.succ_pos n)]
  rw [hmk, map_sub]
  linear_combination hP

/-- The power traces of a finite product. -/
theorem hasPowerTraces_prod {ι : Type*} (s : Finset ι) (P : ι → ℂ[X]) (a : ι → ℕ → ℂ)
    (h : ∀ i ∈ s, HasPowerTraces (P i) (a i)) :
    HasPowerTraces (∏ i ∈ s, P i) fun m => ∑ i ∈ s, a i m := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact hasPowerTraces_one
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- `Π_t (1 − tX)` has the power sums of the `t` as power traces. -/
theorem hasPowerTraces_multiset_prod (d : Multiset ℂ) :
    HasPowerTraces (d.map fun t => (1 : ℂ[X]) - C t * X).prod
      fun m => (d.map fun t => t ^ m).sum := by
  induction d using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero]
    exact hasPowerTraces_one
  | cons t d ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (hasPowerTraces_one_sub_C_mul_X t).mul ih

/-- **Substitution of `X^f`**: `P(X^f)` has the power traces `f a_{m/f}` at the multiples of
`f` and `0` elsewhere. -/
theorem HasPowerTraces.expand {P : ℂ[X]} {a : ℕ → ℂ} (hP : HasPowerTraces P a) {f : ℕ}
    (hf : 0 < f) :
    HasPowerTraces (Polynomial.expand ℂ f P)
      fun m => if f ∣ m then (f : ℂ) * a (m / f) else 0 := by
  unfold HasPowerTraces at *
  have hf0 : f ≠ 0 := hf.ne'
  have hcoe : ∀ Q : ℂ[X], ((Polynomial.expand ℂ f Q : ℂ[X]) : PowerSeries ℂ) =
      PowerSeries.expand f hf0 (Q : PowerSeries ℂ) := by
    intro Q
    ext n
    rw [Polynomial.coeff_coe, Polynomial.coeff_expand hf, PowerSeries.coeff_expand]
    split_ifs
    · rw [Polynomial.coeff_coe]
    · rfl
  have hmk : PowerSeries.mk (fun m => if f ∣ m then (f : ℂ) * a (m / f) else 0) =
      PowerSeries.C (f : ℂ) * PowerSeries.expand f hf0 (PowerSeries.mk a) := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
    split_ifs
    · rw [PowerSeries.coeff_mk]
    · rw [mul_zero]
  have hexp := congrArg (PowerSeries.expand f hf0) hP
  rw [map_mul, map_sub, map_mul, map_mul, PowerSeries.expand_C, PowerSeries.expand_X] at hexp
  have hX : (PowerSeries.X : PowerSeries ℂ) * PowerSeries.X ^ (f - 1) = PowerSeries.X ^ f := by
    rw [← pow_succ', Nat.sub_add_cancel hf]
  rw [hmk, hcoe, Polynomial.derivative_expand, Polynomial.coe_mul, hcoe, Polynomial.coe_mul,
    Polynomial.coe_pow, Polynomial.coe_X, ← Polynomial.C_eq_natCast, Polynomial.coe_C]
  beta_reduce
  rw [if_pos (dvd_zero f), Nat.zero_div, map_mul]
  linear_combination (PowerSeries.C (f : ℂ)) * hexp +
    (PowerSeries.C (f : ℂ) * PowerSeries.expand f hf0 ((derivative P : ℂ[X]) : PowerSeries ℂ)) * hX

/-- **Newton's recursion** `(n+1) p_{n+1} = −Σ_{i+j=n} p_i a_{j+1}`. -/
theorem HasPowerTraces.coeff_succ {P : ℂ[X]} {a : ℕ → ℂ} (hP : HasPowerTraces P a) (n : ℕ) :
    ((n : ℂ) + 1) * P.coeff (n + 1) =
      -∑ p ∈ Finset.antidiagonal n, P.coeff p.1 * a (p.2 + 1) := by
  have h := congrArg (PowerSeries.coeff (n + 1)) hP
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ', map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at h
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk, Polynomial.coeff_derivative] at h
  linear_combination h

/-- **The power traces and the constant term determine the polynomial.** -/
theorem HasPowerTraces.eq_of_coeff_zero {P Q : ℂ[X]} {a : ℕ → ℂ} (hP : HasPowerTraces P a)
    (hQ : HasPowerTraces Q a) (h0 : P.coeff 0 = Q.coeff 0) : P = Q := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      have h1 := hP.coeff_succ n
      have hsum : ∑ p ∈ Finset.antidiagonal n, P.coeff p.1 * a (p.2 + 1) =
          ∑ p ∈ Finset.antidiagonal n, Q.coeff p.1 * a (p.2 + 1) :=
        Finset.sum_congr rfl fun p hp => by
          have hp' := Finset.mem_antidiagonal.mp hp
          rw [ih p.1 (by omega)]
      rw [hsum, ← hQ.coeff_succ n] at h1
      exact mul_left_cancel₀ (Nat.cast_add_one_ne_zero n) h1

/-- A polynomial with constant term `1` determines its power traces `a_m`, `m ≥ 1`. -/
theorem HasPowerTraces.traces_eq {P : ℂ[X]} {a b : ℕ → ℂ} (hP : HasPowerTraces P a)
    (hQ : HasPowerTraces P b) (h0 : P.coeff 0 = 1) {m : ℕ} (hm : 1 ≤ m) : a m = b m := by
  unfold HasPowerTraces at hP hQ
  have hsub : (P : PowerSeries ℂ) * (PowerSeries.mk a - PowerSeries.C (a 0) -
      (PowerSeries.mk b - PowerSeries.C (b 0))) = 0 := by
    linear_combination hP - hQ
  have hP0 : (P : PowerSeries ℂ) ≠ 0 := by
    intro h
    have h' := congrArg (PowerSeries.coeff 0) h
    rw [Polynomial.coeff_coe, h0, map_zero] at h'
    exact one_ne_zero h'
  have hz := (mul_eq_zero.mp hsub).resolve_left hP0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  have h := congrArg (PowerSeries.coeff (n + 1)) hz
  simp only [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n),
    sub_zero, map_zero] at h
  exact sub_eq_zero.mp h

/-! ### Operators -/

section Operators

variable {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- `det(1 − X A)` and the traces of the powers of `A` through one list of eigenvalues: the
diagonal of a triangular form. -/
theorem exists_multiset_charpoly_reverse_eq (A : Module.End ℂ V) :
    ∃ d : Multiset ℂ, A.charpoly.reverse = (d.map fun t => (1 : ℂ[X]) - C t * X).prod ∧
      ∀ k : ℕ, LinearMap.trace ℂ V (A ^ k) = (d.map fun t => t ^ k).sum := by
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := HTGeometry.exists_schur_triangulation _
    (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) A)
  refine ⟨Finset.univ.val.map fun i => T i i, ?_, fun k => ?_⟩
  · rw [← LinearMap.charpoly_toMatrix A (Module.finBasis ℂ V), Matrix.reverse_charpoly]
    refine Polynomial.funext fun z => ?_
    -- `det(1 − X M)` at `z` is `det(1 + (−z) M)`
    have hdet : (Matrix.charpolyRev
        (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) A)).eval z =
        (1 + (-z) • LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) A).det := by
      unfold Matrix.charpolyRev
      rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
      congr 1
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, smul_eq_mul, Polynomial.coe_evalRingHom, eval_sub,
        eval_mul, eval_X, eval_C]
      split_ifs
      · rw [eval_one]
        ring
      · rw [eval_zero]
        ring
    rw [hdet, HTGeometry.det_one_add_smul_eq_prod hU2 hT hMT (-z), Multiset.map_map,
      Polynomial.eval_multiset_prod, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
    ring
  · rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← LinearMap.toMatrix_pow,
      HTGeometry.trace_pow_eq_sum_diag hU1 hU2 hT hMT k, Multiset.map_map]
    rfl

/-- **`det(1 − X A)` has the power traces `tr(A^m)`.** -/
theorem hasPowerTraces_charpoly_reverse (A : Module.End ℂ V) :
    HasPowerTraces A.charpoly.reverse fun m => LinearMap.trace ℂ V (A ^ m) := by
  obtain ⟨d, hd, htr⟩ := exists_multiset_charpoly_reverse_eq A
  rw [hd, show (fun m => LinearMap.trace ℂ V (A ^ m)) = fun m => (d.map fun t => t ^ m).sum from
    funext htr]
  exact hasPowerTraces_multiset_prod d

end Operators

/-! ### The trace on the invariants of a normal subgroup -/

section Invariants

variable {Γ : Type u} [Group Γ] [Fintype Γ] {V : Type w} [AddCommGroup V] [Module ℂ V]

/-- The mean of a representation over a subgroup. -/
def subgroupMean (ρ : Representation ℂ Γ V) (I : Subgroup Γ) : V →ₗ[ℂ] V :=
  (Nat.card I : ℂ)⁻¹ • ∑ τ : I, ρ (τ : Γ)

theorem subgroupMean_apply (ρ : Representation ℂ Γ V) (I : Subgroup Γ) (v : V) :
    subgroupMean ρ I v = (Nat.card I : ℂ)⁻¹ • ∑ τ : I, ρ (τ : Γ) v := by
  rw [subgroupMean, LinearMap.smul_apply, LinearMap.sum_apply]

/-- The mean over `I` maps into the invariants of `I`. -/
theorem subgroupMean_mem_invariants (ρ : Representation ℂ Γ V) (I : Subgroup Γ) (v : V) :
    subgroupMean ρ I v ∈ Representation.invariants (ρ.comp I.subtype) := by
  intro σ
  change ρ (σ : Γ) (subgroupMean ρ I v) = subgroupMean ρ I v
  rw [subgroupMean_apply, map_smul, map_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft σ) fun τ : I => ρ (τ : Γ) v]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]

/-- The mean over `I` fixes the invariants of `I`. -/
theorem subgroupMean_of_mem_invariants (ρ : Representation ℂ Γ V) (I : Subgroup Γ) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp I.subtype)) : subgroupMean ρ I v = v := by
  have h1 : ∑ τ : I, ρ (τ : Γ) v = ∑ _τ : I, v := Finset.sum_congr rfl fun τ _ => hv τ
  rw [subgroupMean_apply, h1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]

variable [FiniteDimensional ℂ V]

/-- **The trace on the invariants of a normal subgroup** is the mean of the character over a
coset: `tr(g | V^I) = |I|⁻¹ Σ_{τ ∈ I} χ(g τ)`. -/
theorem trace_toInvariants (ρ : Representation ℂ Γ V) (I : Subgroup Γ) [I.Normal] (g : Γ) :
    LinearMap.trace ℂ _ (Representation.toInvariants ρ I g) =
      (Nat.card I : ℂ)⁻¹ * cosetSum ρ.character I g := by
  -- `g` on `V^I` is `π ∘ ρ(g) ∘ ι` with `ι` the inclusion and `π` the mean
  have hfac : Representation.toInvariants ρ I g =
      ((subgroupMean ρ I).codRestrict (Representation.invariants (ρ.comp I.subtype))
        (subgroupMean_mem_invariants ρ I)) ∘ₗ
        (ρ g ∘ₗ (Representation.invariants (ρ.comp I.subtype)).subtype) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx : ρ g (x : V) ∈ Representation.invariants (ρ.comp I.subtype) :=
      (Representation.toInvariants ρ I g x).2
    exact (subgroupMean_of_mem_invariants ρ I hx).symm
  have hcomp : (ρ g ∘ₗ (Representation.invariants (ρ.comp I.subtype)).subtype) ∘ₗ
      ((subgroupMean ρ I).codRestrict (Representation.invariants (ρ.comp I.subtype))
        (subgroupMean_mem_invariants ρ I)) =
      (Nat.card I : ℂ)⁻¹ • ∑ τ : I, ρ (g * (τ : Γ)) := by
    refine LinearMap.ext fun v => ?_
    change ρ g (subgroupMean ρ I v) = _
    rw [subgroupMean_apply, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => by rw [map_mul, Module.End.mul_apply]
  rw [hfac, LinearMap.trace_comp_comm', hcomp, map_smul, map_sum, smul_eq_mul]
  rfl

/-- The traces of the powers of `φ` on `V^I` are the Frobenius traces of the character. -/
theorem trace_toInvariants_pow (ρ : Representation ℂ Γ V) (I : Subgroup Γ) [I.Normal] (φ : Γ)
    (m : ℕ) :
    LinearMap.trace ℂ _ ((Representation.toInvariants ρ I φ) ^ m) =
      frobeniusTrace ρ.character I φ m := by
  rw [← map_pow, trace_toInvariants]
  rfl

/-- **Artin's local polynomial `det(1 − X φ | V^I)` has the Frobenius traces of the character
as power traces.** -/
theorem hasPowerTraces_localEulerPolynomial (ρ : Representation ℂ Γ V) (I : Subgroup Γ)
    [I.Normal] (φ : Γ) :
    HasPowerTraces (localEulerPolynomial ρ I φ) (frobeniusTrace ρ.character I φ) := by
  have h := hasPowerTraces_charpoly_reverse (Representation.toInvariants ρ I φ)
  rwa [show (fun m => LinearMap.trace ℂ _ ((Representation.toInvariants ρ I φ) ^ m)) =
    frobeniusTrace ρ.character I φ from funext (trace_toInvariants_pow ρ I φ)] at h

omit [Fintype Γ] in
theorem localEulerPolynomial_coeff_zero (ρ : Representation ℂ Γ V) (I : Subgroup Γ) [I.Normal]
    (φ : Γ) : (localEulerPolynomial ρ I φ).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact localEulerPolynomial_eval_zero ρ I φ

end Invariants

/-! ### Subgroups as groups

The local polynomial at a prime is formed in the decomposition group `D`. Its power traces are
Frobenius traces in the whole group. -/

section Restrict

variable {G : Type u} [Group G] [Fintype G]

/-- A coset sum in a subgroup is a coset sum in the group. -/
theorem cosetSum_restrict (D : Subgroup G) (χ : G → ℂ) (I : Subgroup D) (g : D) :
    cosetSum (fun d : D => χ d) I g = cosetSum χ (I.map D.subtype) (g : G) := by
  unfold cosetSum
  rw [← Equiv.sum_comp (I.equivMapOfInjective D.subtype D.subtype_injective).toEquiv]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, Subgroup.coe_equivMapOfInjective_apply]
  rfl

theorem frobeniusTrace_restrict (D : Subgroup G) (χ : G → ℂ) (I : Subgroup D) (φ : D) (m : ℕ) :
    frobeniusTrace (fun d : D => χ d) I φ m = frobeniusTrace χ (I.map D.subtype) (φ : G) m := by
  unfold frobeniusTrace
  rw [cosetSum_restrict, Subgroup.coe_pow,
    Nat.card_congr (I.equivMapOfInjective D.subtype D.subtype_injective).toEquiv]

variable {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **The local polynomial of a representation of `G` at a subgroup `D`** with inertia `I ⊴ D`
and Frobenius `φ ∈ D` has the Frobenius traces of the character in `G`. -/
theorem hasPowerTraces_localEulerPolynomial_restrict (ρ : Representation ℂ G V) (D : Subgroup G)
    (I : Subgroup D) [I.Normal] (φ : D) :
    HasPowerTraces (localEulerPolynomial (ρ.comp D.subtype) I φ)
      (frobeniusTrace ρ.character (I.map D.subtype) (φ : G)) := by
  have h := hasPowerTraces_localEulerPolynomial (ρ.comp D.subtype) I φ
  rwa [show frobeniusTrace (Representation.character (ρ.comp D.subtype)) I φ =
    frobeniusTrace ρ.character (I.map D.subtype) (φ : G) from
    funext fun m => frobeniusTrace_restrict D ρ.character I φ m] at h

end Restrict

end GaloisForLFunctions
