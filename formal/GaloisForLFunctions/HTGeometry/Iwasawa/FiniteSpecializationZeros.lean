import GaloisForLFunctions.HTGeometry.BirchTateIwasawaEvaluation
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Finite exceptional specializations of an Iwasawa series

Every nonzero integral p-adic power series is a nonzero scalar times a
distinguished polynomial times a unit. Its zeros in the open unit disc
are therefore exactly the roots of one monic polynomial. The scalar is
constructed from the least coefficient valuation; no primitiveness or
Weierstrass-factorization hypothesis is imposed on the input series.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.IwasawaSpecialization
open PowerSeries

variable (p : ℕ) [Fact p.Prime]

/-- Remove the common p-power from all coefficients, leaving a nonzero residue series. -/
theorem exists_primitive_factor {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ (k : ℕ) (g : PowerSeries ℤ_[p]),
      f = C ((p : ℤ_[p]) ^ k) * g ∧
      g.map (IsLocalRing.residue ℤ_[p]) ≠ 0 := by
  classical
  have hex : ∃ k, ∃ i, coeff i f ≠ 0 ∧ (coeff i f).valuation = k := by
    have hi : ∃ i, coeff i f ≠ 0 := by
      by_contra h
      apply hf
      ext i
      simpa using (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hi
    exact ⟨_, i, hi, rfl⟩
  let k := Nat.find hex
  obtain ⟨i, hi, hik⟩ := Nat.find_spec hex
  have hmin (j : ℕ) (hj : coeff j f ≠ 0) : k ≤ (coeff j f).valuation :=
    Nat.find_min' hex ⟨j, hj, rfl⟩
  let g : PowerSeries ℤ_[p] := mk fun j =>
    if hj : coeff j f = 0 then 0
    else (PadicInt.unitCoeff hj : ℤ_[p]) * (p : ℤ_[p]) ^ ((coeff j f).valuation - k)
  refine ⟨k, g, ?_, ?_⟩
  · ext j
    simp only [coeff_C_mul, g, coeff_mk]
    split_ifs with hj
    · simp [hj]
    · calc
        coeff j f = (PadicInt.unitCoeff hj : ℤ_[p]) *
            (p : ℤ_[p]) ^ (coeff j f).valuation := PadicInt.unitCoeff_spec hj
        _ = (p : ℤ_[p]) ^ k * ((PadicInt.unitCoeff hj : ℤ_[p]) *
            (p : ℤ_[p]) ^ ((coeff j f).valuation - k)) := by
          rw [mul_left_comm, ← mul_assoc, ← pow_add, Nat.add_sub_of_le (hmin j hj)]
  · have hu : IsUnit (coeff i g) := by
      simp only [g, coeff_mk, dif_neg hi, hik, show Nat.find hex = k from rfl,
        Nat.sub_self, pow_zero, mul_one]
      exact Units.isUnit _
    intro hz
    have hc := congrArg (coeff i) hz
    rw [coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff] at hc
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hc

/-- Evaluation agrees with ordinary polynomial evaluation on a finite series. -/
theorem eval_polynomial {x : ℤ_[p]} (hx : ‖x‖ < 1) (P : Polynomial ℤ_[p]) :
    padicIntEval p hx (P : PowerSeries ℤ_[p]) = P.eval x := by
  change eval₂ (RingHom.id ℤ_[p]) x (P : PowerSeries ℤ_[p]) = P.eval x
  rw [eval₂_coe]
  rfl

/-- Every nonzero series has exactly a monic polynomial's zeros on the open unit disc. -/
theorem exists_polynomial_zero_locus {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ P : Polynomial ℤ_[p], P.Monic ∧
      ∀ (x : ℤ_[p]) (hx : ‖x‖ < 1),
        padicIntEval p hx f = 0 ↔ P.eval x = 0 := by
  obtain ⟨k, g, hfg, hg⟩ := exists_primitive_factor p hf
  obtain ⟨P, u, hP⟩ := g.exists_isWeierstrassFactorization hg
  refine ⟨P, hP.isDistinguishedAt.monic, ?_⟩
  intro x hx
  have hu : padicIntEval p hx u ≠ 0 := (hP.isUnit.map (padicIntEval p hx)).ne_zero
  have hp : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (NeZero.ne _)
  rw [hfg, hP.eq_mul, map_mul, map_mul, padicIntEval_C, eval_polynomial]
  simp only [mul_eq_zero, hp, hu, or_false, false_or]

/-- Exceptional specialization points, with the convergence condition built into membership. -/
def zeroLocus (f : PowerSeries ℤ_[p]) : Set ℤ_[p] :=
  {x | ∃ hx : ‖x‖ < 1, padicIntEval p hx f = 0}

/-- A nonzero Iwasawa series has finitely many exceptional integral specializations. -/
theorem finite_zeroLocus {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    (zeroLocus p f).Finite := by
  obtain ⟨P, hP, hzero⟩ := exists_polynomial_zero_locus p hf
  apply (Polynomial.finite_setOf_isRoot hP.ne_zero).subset
  rintro x ⟨hx, hfx⟩
  exact (hzero x hx).mp hfx

/-- Unconditional dichotomy: the series is zero or its exceptional set is finite. -/
theorem zero_or_finite_specializations (f : PowerSeries ℤ_[p]) :
    f = 0 ∨ (zeroLocus p f).Finite := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · exact Or.inr (finite_zeroLocus p hf)

end GaloisForLFunctions.HTGeometry.IwasawaSpecialization

#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.exists_primitive_factor
#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.exists_polynomial_zero_locus
#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.zero_or_finite_specializations

