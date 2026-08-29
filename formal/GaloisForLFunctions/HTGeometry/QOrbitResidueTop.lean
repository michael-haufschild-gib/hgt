import GaloisForLFunctions.HTGeometry.QSummabilityFromResidues
import GaloisForLFunctions.HTGeometry.QPrimitiveResidueHypertranscendence

/-!
# The top nonvanishing `q`-discrete residue

Principal-part coefficients vanish above the pole order, and the pole order is bounded by the
degree of the denominator, so the residues along an orbit vanish above a fixed level.  A rational
function that is not `q`-summable therefore has a top nonvanishing residue, which is exactly the
input of the hypertranscendence criterion.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

theorem ratFuncX_sub_algebraMap (c : K) :
    (RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) c
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C c) := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rfl

theorem polePart_eq_zero_of_poleOrder_lt {g : RatFunc K} {c : K} {e : ℕ}
    (he : poleOrder g c < e) : polePart g c e = 0 := by
  refine polePart_eq_zero_of_regularAt_mul_pow (m := poleOrder g c) ?_ he
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  set m : ℕ := poleOrder g c with hm
  set D₁ : Polynomial K := g.denom /ₘ (Polynomial.X - Polynomial.C c) ^ m with hD₁
  have hfac : (Polynomial.X - Polynomial.C c) ^ m * D₁ = g.denom :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq g.denom c
  have hD₁eval : D₁.eval c ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hden
  refine regularAt_of_repr (P := g.num) (Q := D₁) hD₁eval ?_
  have hXm : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C c) ^ m) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c))
  have hD₁ne : algebraMap (Polynomial K) (RatFunc K) D₁ ≠ 0 :=
    RatFunc.algebraMap_ne_zero (fun h => hD₁eval (by rw [h, Polynomial.eval_zero]))
  rw [ratFuncX_sub_algebraMap, ← map_pow]
  conv_lhs => rw [← RatFunc.num_div_denom g, ← hfac]
  rw [map_mul, div_mul_eq_mul_div, mul_comm (algebraMap (Polynomial K) (RatFunc K) g.num),
    mul_div_mul_left _ _ hXm]

theorem poleOrder_le_natDegree_denom (g : RatFunc K) (c : K) :
    poleOrder g c ≤ g.denom.natDegree := by
  have hdvd := Polynomial.pow_rootMultiplicity_dvd g.denom c
  have hle := Polynomial.natDegree_le_of_dvd hdvd (RatFunc.denom_ne_zero g)
  rwa [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one, ← poleOrder] at hle

theorem qOrbitResidue_eq_zero_of_natDegree_lt {q a : K} {r : RatFunc K} {e : ℕ}
    (he : r.denom.natDegree < e) : qOrbitResidue q a e r = 0 := by
  rw [qOrbitResidue_eq_sum r (∅ : Finset ℤ) ?_, Finset.sum_empty]
  intro n hn
  exact absurd (polePart_eq_zero_of_poleOrder_lt
    (lt_of_le_of_lt (poleOrder_le_natDegree_denom r _) he)) hn

/-- **A nonzero residue has a top level.** -/
theorem exists_top_qOrbitResidue {q a : K} {r : RatFunc K} {d : ℕ} (hd : 0 < d)
    (hres : qOrbitResidue q a d r ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ qOrbitResidue q a D r ≠ 0 ∧
      ∀ e : ℕ, D < e → qOrbitResidue q a e r = 0 := by
  classical
  set B : ℕ := r.denom.natDegree with hB
  have hdB : d ≤ B := by
    by_contra hcon
    exact hres (qOrbitResidue_eq_zero_of_natDegree_lt (by omega))
  set P : ℕ → Prop := fun e => qOrbitResidue q a e r ≠ 0 with hP
  set D : ℕ := Nat.findGreatest P B with hD
  have hdD : d ≤ D := Nat.le_findGreatest hdB hres
  have hPD : P D := Nat.findGreatest_spec (m := d) (by omega) hres
  refine ⟨D, by omega, hPD, fun e he => ?_⟩
  by_cases heB : e ≤ B
  · by_contra hcon
    exact Nat.findGreatest_is_greatest he heB hcon
  · exact qOrbitResidue_eq_zero_of_natDegree_lt (by omega)

end

end GaloisForLFunctions.HTGeometry
