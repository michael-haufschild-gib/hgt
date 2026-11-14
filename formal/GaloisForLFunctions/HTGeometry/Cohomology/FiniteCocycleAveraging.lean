import GaloisForLFunctions.HTGeometry.OmegaObstruction

/-!
# Explicit primitives for finite-group cocycles

Over a field of characteristic zero, averaging a two-cocycle over its
second argument gives a primitive. The formula works with every linear
group action and kills the existing second constraint cohomology class.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

variable {K G A : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
  [AddCommGroup A] [Module K A] [DistribMulAction G A] [SMulCommClass G K A]

/-- Average a two-cochain in its second argument. -/
def finiteCocycleAverage (ω : G → G → A) (g : G) : A :=
  (Fintype.card G : K)⁻¹ • ∑ k, ω g k

/-- Averaging supplies an actual primitive of every finite-group
two-cocycle with characteristic-zero linear coefficients. -/
theorem isTwoCocycle_eq_twoCoboundary_average {ω : G → G → A}
    (hω : IsTwoCocycle ω) : ω = twoCoboundary (finiteCocycleAverage (K := K) ω) := by
  classical
  funext g h
  let S : G → A := fun g => ∑ k, ω g k
  have hreindex : (∑ k, ω g (h * k)) = ∑ k, ω g k :=
    Equiv.sum_comp (Equiv.mulLeft h) (ω g)
  have hs : g • S h + S g = S (g * h) + Fintype.card G • ω g h := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
      rfl (fun k _ => hω g h k)
    simpa only [Finset.sum_add_distrib, ← Finset.smul_sum,
      Finset.sum_const, Finset.card_univ, hreindex] using hh
  have hn : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscaled : g • ((Fintype.card G : K)⁻¹ • S h) +
      (Fintype.card G : K)⁻¹ • S g =
      (Fintype.card G : K)⁻¹ • S (g * h) + ω g h := by
    have hc := congrArg (fun x : A => (Fintype.card G : K)⁻¹ • x) hs
    rw [smul_add, smul_add, ← smul_comm g (Fintype.card G : K)⁻¹,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hn, one_smul] at hc
    exact hc
  change ω g h = g • ((Fintype.card G : K)⁻¹ • S h) -
    (Fintype.card G : K)⁻¹ • S (g * h) + (Fintype.card G : K)⁻¹ • S g
  calc
    ω g h = (g • ((Fintype.card G : K)⁻¹ • S h) +
        (Fintype.card G : K)⁻¹ • S g) - (Fintype.card G : K)⁻¹ • S (g * h) := by
      rw [hscaled]
      abel
    _ = _ := by abel

include K in
/-- Finite-group constraint cohomology vanishes with characteristic-zero
linear coefficients; the primitive is the explicit average above. -/
theorem finite_obstructionClass_eq_zero (ω : twoCocycles (G := G) (A := A)) :
    obstructionClass ω = 0 := by
  apply (obstructionClass_eq_zero_iff_exists_cochain ω).mpr
  refine ⟨finiteCocycleAverage (K := K) ω, ?_⟩
  apply Subtype.ext
  exact isTwoCocycle_eq_twoCoboundary_average (K := K) ω.property

#print axioms isTwoCocycle_eq_twoCoboundary_average
#print axioms finite_obstructionClass_eq_zero

end GaloisForLFunctions.RHTower
