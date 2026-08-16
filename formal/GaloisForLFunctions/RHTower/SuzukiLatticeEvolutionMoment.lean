import GaloisForLFunctions.RHTower.SuzukiLatticeEvolutionUnitary
import GaloisForLFunctions.RHTower.SuzukiLatticeMomentAlgebra

/-!
# The evolution's coefficients, evaluated pointwise

Evaluation at a lattice point is a continuous linear functional on `ℓ²`, so the exponential series
may be evaluated termwise.  Each term is an adjacency word applied to the delta field, which the
moment algebra computes exactly — and the two facts together turn the position moment of the
evolution into the evolution of the commutator adjacency, with one factor of the time.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
/-- Evaluation of an `ℓ²` field at a point, as a continuous linear functional. -/
theorem norm_eval_le (ψ : H) (r : P → ℤ) : ‖(ψ : (P → ℤ) → ℂ) r‖ ≤ ‖ψ‖ :=
  lp.norm_apply_le_norm (by norm_num) ψ r

omit [Fintype P] [DecidableEq P] in
/-- Evaluation as a bundled continuous linear map. -/
def evalL2 (r : P → ℤ) : H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (ψ : (P → ℤ) → ℂ) r
      map_add' := fun ψ φ => by simp
      map_smul' := fun a ψ => by simp } 1 (fun ψ => by simpa using norm_eval_le ψ r)

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem evalL2_apply (r : P → ℤ) (ψ : H) : evalL2 r ψ = (ψ : (P → ℤ) → ℂ) r := rfl

/-- The delta vector at the origin. -/
def deltaL2 : H := lp.single 2 (0 : P → ℤ) (1 : ℂ)

omit [DecidableEq P] in
theorem coe_deltaL2 : ((deltaL2 : H) : (P → ℤ) → ℂ) = deltaField (0 : P → ℤ) := by
  funext ν
  rw [deltaL2, lp.single_apply, deltaField]
  by_cases h : ν = 0
  · subst h
    simp
  · simp [h]

omit [Fintype P] [DecidableEq P] in
theorem coe_latticeAdjacency_pow (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (n : ℕ) (ψ : H) :
    (((latticeAdjacency Q c) ^ n) ψ : (P → ℤ) → ℂ)
      = (adjacencyField Q c)^[n] ((ψ : (P → ℤ) → ℂ)) := by
  induction n generalizing ψ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Function.iterate_succ_apply']
    have hstep : (((latticeAdjacency Q c) ^ k * latticeAdjacency Q c) ψ : H)
        = ((latticeAdjacency Q c) ^ k) (latticeAdjacency Q c ψ) := rfl
    rw [hstep, ih]
    have hfun : ((latticeAdjacency Q c ψ : H) : (P → ℤ) → ℂ)
        = adjacencyField Q c (ψ : (P → ℤ) → ℂ) := by
      funext ν
      exact latticeAdjacency_apply Q c ψ ν
    rw [hfun, ← Function.iterate_succ_apply (f := adjacencyField Q c),
      Function.iterate_succ_apply' (f := adjacencyField Q c)]

omit [Fintype P] [DecidableEq P] in
/-- The exponential series may be evaluated termwise at a lattice point. -/
theorem eval_exp_smul_latticeAdjacency (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (z : ℂ)
    (ψ : H) (r : P → ℤ) :
    ((NormedSpace.exp (z • latticeAdjacency Q c) ψ : H) : (P → ℤ) → ℂ) r
      = ∑' n : ℕ, (((Nat.factorial n : ℕ) : ℂ)⁻¹ * z ^ n)
          * ((adjacencyField Q c)^[n] ((ψ : (P → ℤ) → ℂ))) r := by
  set T : H →L[ℂ] H := z • latticeAdjacency Q c with hTdef
  have hsum : Summable fun n : ℕ => (((Nat.factorial n : ℕ) : ℂ)⁻¹) • T ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) T
  have hexp : NormedSpace.exp T = ∑' n : ℕ, (((Nat.factorial n : ℕ) : ℂ)⁻¹) • T ^ n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  have happ : (NormedSpace.exp T) ψ = ∑' n : ℕ, (((Nat.factorial n : ℕ) : ℂ)⁻¹) • ((T ^ n) ψ) := by
    rw [hexp]
    have := (ContinuousLinearMap.apply ℂ H ψ).map_tsum hsum
    simpa using this
  have hev : ((NormedSpace.exp T ψ : H) : (P → ℤ) → ℂ) r
      = ∑' n : ℕ, (((Nat.factorial n : ℕ) : ℂ)⁻¹) * (((T ^ n) ψ : H) : (P → ℤ) → ℂ) r := by
    have hsum2 : Summable fun n : ℕ => (((Nat.factorial n : ℕ) : ℂ)⁻¹) • ((T ^ n) ψ) := by
      refine (hsum.map (ContinuousLinearMap.apply ℂ H ψ) ?_).congr (fun n => rfl)
      exact (ContinuousLinearMap.apply ℂ H ψ).continuous
    rw [happ]
    have := (evalL2 (P := P) r).map_tsum hsum2
    simpa using this
  rw [hev]
  refine tsum_congr fun n => ?_
  have hpow : ((T ^ n) ψ : H) = (z ^ n) • (((latticeAdjacency Q c) ^ n) ψ) := by
    rw [hTdef, smul_pow, smul_apply]
  rw [hpow, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coe_latticeAdjacency_pow]
  ring

omit [Fintype P] [DecidableEq P] in
/-- The evaluated exponential series is summable. -/
theorem summable_eval_expTerms (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (z : ℂ)
    (ψ : H) (r : P → ℤ) :
    Summable fun n : ℕ => (((Nat.factorial n : ℕ) : ℂ)⁻¹ * z ^ n)
      * ((adjacencyField Q c)^[n] ((ψ : (P → ℤ) → ℂ))) r := by
  set T : H →L[ℂ] H := z • latticeAdjacency Q c with hTdef
  have hsum : Summable fun n : ℕ => (((Nat.factorial n : ℕ) : ℂ)⁻¹) • T ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) T
  have hsum2 : Summable fun n : ℕ => (((Nat.factorial n : ℕ) : ℂ)⁻¹) • ((T ^ n) ψ) := by
    refine (hsum.map (ContinuousLinearMap.apply ℂ H ψ) ?_).congr (fun n => rfl)
    exact (ContinuousLinearMap.apply ℂ H ψ).continuous
  have hsum3 := hsum2.map (evalL2 (P := P) r) (evalL2 (P := P) r).continuous
  refine hsum3.congr fun n => ?_
  simp only [Function.comp_apply, map_smul, evalL2_apply, smul_eq_mul]
  have hpow : ((T ^ n) ψ : H) = (z ^ n) • (((latticeAdjacency Q c) ^ n) ψ) := by
    rw [hTdef, smul_pow, smul_apply]
  rw [hpow, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coe_latticeAdjacency_pow]
  ring

omit [DecidableEq P] in
/-- **The exact position moment of the evolution.**  Multiplying the evolved delta field by a
coordinate is the same as evolving the commutator adjacency, at the cost of one factor of the
time. -/
theorem eval_posMul_exp_deltaL2 (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (z : ℂ)
    (r : P → ℤ) :
    ((r p : ℤ) : ℂ)
        * ((NormedSpace.exp (z • latticeAdjacency Q c) (deltaL2 : H) : H) : (P → ℤ) → ℂ) r
      = -z * ((NormedSpace.exp (z • latticeAdjacency Q c)
          (latticeAdjacency Q (stepWeighted p c) (deltaL2 : H)) : H) : (P → ℤ) → ℂ) r := by
  have hAp : ((latticeAdjacency Q (stepWeighted p c) (deltaL2 : H) : H) : (P → ℤ) → ℂ)
      = adjacencyField Q (stepWeighted p c) (deltaField (0 : P → ℤ)) := by
    funext ν
    rw [latticeAdjacency_apply, coe_deltaL2]
  rw [eval_exp_smul_latticeAdjacency, eval_exp_smul_latticeAdjacency, hAp, coe_deltaL2]
  have hsum := summable_eval_expTerms Q c z (deltaL2 : H) r
  rw [coe_deltaL2] at hsum
  rw [← tsum_mul_left, (hsum.mul_left ((r p : ℤ) : ℂ)).tsum_eq_zero_add]
  have hzero : (((Nat.factorial 0 : ℕ) : ℂ)⁻¹ * z ^ 0)
      * ((adjacencyField Q c)^[0] (deltaField (0 : P → ℤ))) r = ((deltaField (0 : P → ℤ)) r) := by
    simp
  have hterm : ∀ n : ℕ, ((r p : ℤ) : ℂ) * ((((Nat.factorial (n + 1) : ℕ) : ℂ)⁻¹ * z ^ (n + 1))
      * ((adjacencyField Q c)^[n + 1] (deltaField (0 : P → ℤ))) r)
      = -z * ((((Nat.factorial n : ℕ) : ℂ)⁻¹ * z ^ n)
        * ((adjacencyField Q c)^[n]
            (adjacencyField Q (stepWeighted p c) (deltaField (0 : P → ℤ)))) r) := by
    intro n
    have hmom := congrFun (posMulField_adjacencyField_iterate Q c p n) r
    rw [posMulField] at hmom
    have hfac : ((Nat.factorial (n + 1) : ℕ) : ℂ) = ((n : ℂ) + 1) * ((Nat.factorial n : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hne1 : ((n : ℂ) + 1) ≠ 0 := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Nat.cast_ne_zero]
      omega
    rw [show ((r p : ℤ) : ℂ) * ((((Nat.factorial (n + 1) : ℕ) : ℂ)⁻¹ * z ^ (n + 1))
        * ((adjacencyField Q c)^[n + 1] (deltaField (0 : P → ℤ))) r)
      = (((Nat.factorial (n + 1) : ℕ) : ℂ)⁻¹ * z ^ (n + 1))
        * (((r p : ℤ) : ℂ) * ((adjacencyField Q c)^[n + 1] (deltaField (0 : P → ℤ))) r) by ring,
      hmom, hfac, pow_succ]
    field_simp
  have hcongr : ∀ n : ℕ, ((r p : ℤ) : ℂ) * ((((Nat.factorial (n + 1) : ℕ) : ℂ)⁻¹ * z ^ (n + 1))
      * ((adjacencyField Q c)^[n + 1] (deltaField (0 : P → ℤ))) r)
      = -z * ((((Nat.factorial n : ℕ) : ℂ)⁻¹ * z ^ n)
        * ((adjacencyField Q c)^[n]
            (adjacencyField Q (stepWeighted p c) (deltaField (0 : P → ℤ)))) r) := hterm
  rw [hzero]
  have hdelta : ((r p : ℤ) : ℂ) * ((deltaField (0 : P → ℤ)) r) = 0 := by
    have h := congrFun (posMulField_deltaField (P := P) p) r
    rw [posMulField] at h
    exact h
  rw [hdelta, zero_add, ← tsum_mul_left]
  exact tsum_congr hcongr

end RHTower
