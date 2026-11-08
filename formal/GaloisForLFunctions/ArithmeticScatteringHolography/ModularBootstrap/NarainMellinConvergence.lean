import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellin
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellin

/-!
# Absolute Mellin convergence of the scalar Narain heat sum

The scalar Dirichlet series controls the integrals of the exponential
summands' norms. Countable reindexing applies the norm-Fubini criterion.
-/

open Complex RHTower MeasureTheory Set

noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem scalarCharge_infinite : Infinite NonzeroScalarCharge := by
  let f : ℕ → NonzeroScalarCharge := fun k =>
    ⟨(((k : ℤ) + 1, 0), (0, 0)), by
      constructor
      · norm_num
      · intro h
        have he : (k : ℤ) + 1 = 0 := congrArg (fun q => q.1.1) h
        have hk : (0 : ℤ) ≤ k := Nat.cast_nonneg k
        linarith only [he, hk]⟩
  apply Infinite.of_injective f
  intro a b h
  have he := congrArg (fun q : NonzeroScalarCharge => q.val.1.1) h
  change (a : ℤ) + 1 = (b : ℤ) + 1 at he
  exact_mod_cast add_right_cancel he

/-- The actual scalar heat Mellin integral converges absolutely on `Re s > 1`. -/
theorem mellinConvergent_narainScalarHeat (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) : MellinConvergent (narainScalarHeat ρ σ) s := by
  letI : Infinite NonzeroScalarCharge := scalarCharge_infinite
  let e : ℕ ≃ NonzeroScalarCharge := Classical.choice inferInstance
  have hm (q : NonzeroScalarCharge) : 0 < narainMassSq ρ σ q.val :=
    narainMassSq_pos ρ σ q.property.2
  have hsum : Summable (fun q : NonzeroScalarCharge => 1 / narainMassSq ρ σ q.val ^ s.re) := by
    refine (summable_narainDirichletTerm ρ σ hs).norm.congr fun q => ?_
    rw [narainDirichletTerm, Complex.norm_cpow_eq_rpow_re_of_pos (hm q),
      Complex.neg_re, Real.rpow_neg (hm q).le, one_div]
  have hsumπ : Summable (fun q : NonzeroScalarCharge =>
      1 / (Real.pi * narainMassSq ρ σ q.val) ^ s.re) := by
    refine (hsum.div_const (Real.pi ^ s.re)).congr fun q => ?_
    rw [Real.mul_rpow Real.pi_pos.le (hm q).le]
    ring
  apply WeilSingularArithmetic.mellinConvergent_of_exponential_series
    (a := fun _ : ℕ => (1 : ℂ))
    (p := fun n => Real.pi * narainMassSq ρ σ (e n).val)
  · intro n
    exact Or.inr (mul_pos Real.pi_pos (hm (e n)))
  · exact lt_trans zero_lt_one hs
  · intro y hy
    have h : HasSum (fun n : ℕ => (narainBoltzmann ρ σ y (e n).val : ℂ))
        (narainScalarHeat ρ σ y) :=
      e.hasSum_iff.mpr (summable_narainScalarHeatTerm ρ σ hy).hasSum
    refine h.congr_fun fun n => ?_
    rw [one_mul, narainBoltzmann]
    congr 2
    ring
  · exact (e.summable_iff.mpr hsumπ).congr fun n => by
      simp only [Function.comp_apply, norm_one]

#print axioms mellinConvergent_narainScalarHeat

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
