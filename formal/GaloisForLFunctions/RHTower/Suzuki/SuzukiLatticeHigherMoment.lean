import GaloisForLFunctions.RHTower.Suzuki.SuzukiLatticeEvolutionMoment

/-!
# Higher position moments of the evolution

The moment identity holds for an arbitrary field, not only the delta at the origin: the position
factor either passes through the adjacency word or is spent on one commutator, and the commutator is
again a finite-range adjacency.  Because the commutator costs one power of the word, the exponential
series reassembles with exactly one factor of the time — which is what makes every moment of the
evolution grow only polynomially.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
/-- **The general position moment of an adjacency word.**  The commutator term costs one power of
the word. -/
theorem posMulField_adjacencyField_iterate_gen (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P)
    (n : ℕ) (ψ : (P → ℤ) → ℂ) :
    posMulField p ((adjacencyField Q c)^[n + 1] ψ)
      = fun r => ((adjacencyField Q c)^[n + 1] (posMulField p ψ)) r
          - ((n : ℂ) + 1) * ((adjacencyField Q c)^[n]
              (adjacencyField Q (stepWeighted p c) ψ)) r := by
  induction n with
  | zero =>
    rw [Function.iterate_one, posMulField_adjacencyField]
    funext r
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply' (f := adjacencyField Q c) (n := k + 1),
      posMulField_adjacencyField, ih]
    have hsub : adjacencyField Q c
        (fun r => ((adjacencyField Q c)^[k + 1] (posMulField p ψ)) r
          - ((k : ℂ) + 1) * ((adjacencyField Q c)^[k]
              (adjacencyField Q (stepWeighted p c) ψ)) r)
        = fun r => adjacencyField Q c ((adjacencyField Q c)^[k + 1] (posMulField p ψ)) r
          - ((k : ℂ) + 1) * adjacencyField Q c ((adjacencyField Q c)^[k]
              (adjacencyField Q (stepWeighted p c) ψ)) r := by
      rw [adjacencyField_sub Q c ((adjacencyField Q c)^[k + 1] (posMulField p ψ))
        (fun r => ((k : ℂ) + 1) * ((adjacencyField Q c)^[k]
          (adjacencyField Q (stepWeighted p c) ψ)) r),
        adjacencyField_smul Q c ((k : ℂ) + 1)
          ((adjacencyField Q c)^[k] (adjacencyField Q (stepWeighted p c) ψ))]
    rw [hsub]
    funext r
    have hcomm : adjacencyField Q (stepWeighted p c) ((adjacencyField Q c)^[k + 1] ψ)
        = (adjacencyField Q c)^[k + 1] (adjacencyField Q (stepWeighted p c) ψ) :=
      (adjacencyField_iterate_comm Q c (stepWeighted p c) (k + 1) ψ).symm
    rw [hcomm, ← Function.iterate_succ_apply' (f := adjacencyField Q c) (n := k + 1),
      ← Function.iterate_succ_apply' (f := adjacencyField Q c) (n := k)]
    push_cast
    ring

omit [Fintype P] [DecidableEq P] in
/-- **The general position moment of the evolution.** -/
theorem eval_posMul_exp (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (z : ℂ)
    (ψ φ : H) (hφ : ((φ : H) : (P → ℤ) → ℂ) = posMulField p ((ψ : H) : (P → ℤ) → ℂ))
    (r : P → ℤ) :
    ((r p : ℤ) : ℂ) * ((NormedSpace.exp (z • latticeAdjacency Q c) ψ : H) : (P → ℤ) → ℂ) r
      = ((NormedSpace.exp (z • latticeAdjacency Q c) φ : H) : (P → ℤ) → ℂ) r
        - z * ((NormedSpace.exp (z • latticeAdjacency Q c)
            (latticeAdjacency Q (stepWeighted p c) ψ) : H) : (P → ℤ) → ℂ) r := by
  have hAp : ((latticeAdjacency Q (stepWeighted p c) ψ : H) : (P → ℤ) → ℂ)
      = adjacencyField Q (stepWeighted p c) ((ψ : H) : (P → ℤ) → ℂ) := by
    funext ν
    exact latticeAdjacency_apply Q (stepWeighted p c) ψ ν
  rw [eval_exp_smul_latticeAdjacency, eval_exp_smul_latticeAdjacency,
    eval_exp_smul_latticeAdjacency, hAp, hφ]
  have hsumψ := summable_eval_expTerms Q c z ψ r
  have hsumφ := summable_eval_expTerms Q c z φ r
  rw [hφ] at hsumφ
  have hsumA := summable_eval_expTerms Q c z (latticeAdjacency Q (stepWeighted p c) ψ) r
  rw [hAp] at hsumA
  rw [← tsum_mul_left, (hsumψ.mul_left ((r p : ℤ) : ℂ)).tsum_eq_zero_add,
    hsumφ.tsum_eq_zero_add, ← tsum_mul_left]
  have hzero : ((r p : ℤ) : ℂ) * ((((Nat.factorial 0 : ℕ) : ℂ)⁻¹ * z ^ (0 : ℕ))
      * ((adjacencyField Q c)^[0] ((ψ : H) : (P → ℤ) → ℂ)) r)
      = (((Nat.factorial 0 : ℕ) : ℂ)⁻¹ * z ^ (0 : ℕ))
        * ((adjacencyField Q c)^[0] (posMulField p ((ψ : H) : (P → ℤ) → ℂ))) r := by
    simp [posMulField]
  rw [hzero]
  have htail : ∀ k : ℕ, ((r p : ℤ) : ℂ) * ((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹ * z ^ (k + 1))
      * ((adjacencyField Q c)^[k + 1] ((ψ : H) : (P → ℤ) → ℂ)) r)
      = (((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹ * z ^ (k + 1))
          * ((adjacencyField Q c)^[k + 1] (posMulField p ((ψ : H) : (P → ℤ) → ℂ))) r
        - z * ((((Nat.factorial k : ℕ) : ℂ)⁻¹ * z ^ k)
          * ((adjacencyField Q c)^[k]
              (adjacencyField Q (stepWeighted p c) ((ψ : H) : (P → ℤ) → ℂ))) r) := by
    intro k
    have hmom := congrFun (posMulField_adjacencyField_iterate_gen Q c p k
      ((ψ : H) : (P → ℤ) → ℂ)) r
    rw [posMulField] at hmom
    have hfac : ((Nat.factorial (k + 1) : ℕ) : ℂ)
        = ((k : ℂ) + 1) * ((Nat.factorial k : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hne1 : ((k : ℂ) + 1) ≠ 0 := by
      have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast, Nat.cast_ne_zero]
      omega
    rw [show ((r p : ℤ) : ℂ) * ((((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹ * z ^ (k + 1))
        * ((adjacencyField Q c)^[k + 1] ((ψ : H) : (P → ℤ) → ℂ)) r)
      = (((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹ * z ^ (k + 1))
        * (((r p : ℤ) : ℂ) * ((adjacencyField Q c)^[k + 1]
            ((ψ : H) : (P → ℤ) → ℂ)) r) by ring, hmom, hfac, pow_succ]
    field_simp
  rw [tsum_congr htail]
  have hshift : Summable fun k : ℕ => (((Nat.factorial (k + 1) : ℕ) : ℂ)⁻¹ * z ^ (k + 1))
      * ((adjacencyField Q c)^[k + 1] (posMulField p ((ψ : H) : (P → ℤ) → ℂ))) r :=
    (summable_nat_add_iff 1).mpr hsumφ
  rw [Summable.tsum_sub hshift (hsumA.mul_left z)]
  ring

end RHTower
