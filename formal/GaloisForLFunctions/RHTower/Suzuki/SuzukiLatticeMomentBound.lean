import GaloisForLFunctions.RHTower.Suzuki.SuzukiLatticeHigherMoment

/-!
# The moment of the evolution is an `ℓ²` field with a polynomial bound

The pointwise moment identity exhibits the position moment of the evolution as a difference of two
evolved vectors, hence as an honest `ℓ²` field; unitarity then bounds its norm by the moment of the
initial vector plus the time times the norm of the commutator vector.  That is the induction step
behind the polynomial group estimate.
-/

open Finset Complex

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
/-- The position moment of the evolution, as an `ℓ²` field. -/
theorem coe_posMul_exp (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (z : ℂ)
    (ψ φ : H) (hφ : ((φ : H) : (P → ℤ) → ℂ) = posMulField p ((ψ : H) : (P → ℤ) → ℂ)) :
    posMulField p ((NormedSpace.exp (z • latticeAdjacency Q c) ψ : H) : (P → ℤ) → ℂ)
      = ((NormedSpace.exp (z • latticeAdjacency Q c) φ
          - z • NormedSpace.exp (z • latticeAdjacency Q c)
              (latticeAdjacency Q (stepWeighted p c) ψ) : H) : (P → ℤ) → ℂ) := by
  funext r
  rw [posMulField, eval_posMul_exp Q c p z ψ φ hφ r, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

omit [Fintype P] [DecidableEq P] in
/-- **The moment bound.**  Unitarity turns the moment identity into a bound that costs exactly one
power of the time. -/
theorem norm_posMul_exp_le {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (p : P) (x : ℝ) (ψ φ : H) :
    ‖(NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) φ
        - (-(x : ℂ) * Complex.I) • NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
            (latticeAdjacency Q (stepWeighted p c) ψ) : H)‖
      ≤ ‖φ‖ + |x| * ‖latticeAdjacency Q (stepWeighted p c) ψ‖ := by
  have h1 : ‖NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) φ‖ = ‖φ‖ :=
    norm_exp_latticeAdjacency_apply hsa x φ
  have h2 : ‖NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
      (latticeAdjacency Q (stepWeighted p c) ψ)‖
      = ‖latticeAdjacency Q (stepWeighted p c) ψ‖ :=
    norm_exp_latticeAdjacency_apply hsa x _
  have hz : ‖(-(x : ℂ) * Complex.I)‖ = |x| := by
    rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) φ
        - (-(x : ℂ) * Complex.I) • NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
            (latticeAdjacency Q (stepWeighted p c) ψ) : H)‖
      ≤ ‖NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) φ‖
        + ‖(-(x : ℂ) * Complex.I) • NormedSpace.exp
            ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
            (latticeAdjacency Q (stepWeighted p c) ψ)‖ := norm_sub_le _ _
    _ = ‖φ‖ + |x| * ‖latticeAdjacency Q (stepWeighted p c) ψ‖ := by
        rw [h1, norm_smul, hz, h2]

end RHTower
