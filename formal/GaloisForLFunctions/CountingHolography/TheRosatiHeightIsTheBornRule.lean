import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.ArithmeticEffectivityTheory.NaiveHeightsAreTraces
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration

/-!
# The Rosati height is the Born rule

The dictionary between heights on Jacobians and the black holes of branched graphs, on the probe ring
`ℤ[F]` of a curve datum. On a Jacobian, the polarization pairs an endomorphism `P(F)` with its Rosati
transpose, and `Tr(P(F) P(F)′) = Σ_i P(α_i) P(q/α_i)` is the degree of the pulled-back polarization: a
height on the ring of probes (`ArithmeticCorrespondencePositivity.rosatiDeg`). In the language of the
black hole:

* **The Rosati form is a Born rule on all probes** (`rosatiDeg_delay`): the delay `P ↦ X P` multiplies it
  by `q`, because a mode and its partner multiply to `q`.
* **Its two-term part is the count law** (`rosatiDeg_twoTerm`): on `y − x Fⁿ` it is
  `2g (y² + qⁿ x²) − 2 a_n x y`, twice the genus form of level `n`, the equal-weight member of the
  family of Born rules of the oscillator bank.
* **Height, sign, count law and damping are one condition** (`rosati_tfae`): the integral Rosati form has a
  naive height (a function bounded below at bounded distance), it is nonnegative on `ℤ[F]`, the channel
  numbers extend to a count law at every level, the datum is unitary.
* **On true curves all four hold** (`hyperelliptic_countLaw`, `hyperelliptic_naiveHeight`): for
  `y² = f(x)`, `f` squarefree of degree `2g + 1` in odd characteristic, split or not, over every finite
  extension, with the channel numbers given by the actual point counts. The count is produced by
  Stepanov's auxiliary polynomial; the height is then Tate's limit of a count.

The geometric reading of `Tr(P(F) P(F)′)` as a degree on the Jacobian is classical [C]; no theorem here
uses it.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri ArithmeticCorrespondencePositivity
open ArithmeticEffectivityTheory

section Datum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- A mode and its functional-equation partner multiply to `q`. -/
theorem eigenvalue_mul_fePerm (i : ι) : eigenvalue D i * eigenvalue D (D.fePerm i) = D.q := by
  unfold eigenvalue
  have h := D.β_fePerm i
  have hs : ((D.sqrtq : ℂ)) * (D.sqrtq : ℂ) = (D.q : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, D.sqrtq_sq]
  calc (D.sqrtq : ℂ) * D.β i * ((D.sqrtq : ℂ) * D.β (D.fePerm i))
      = ((D.sqrtq : ℂ) * (D.sqrtq : ℂ)) * (D.β (D.fePerm i) * D.β i) := by ring
    _ = D.q := by rw [hs, h, mul_one]

/-- **The Rosati form is a Born rule on the probe ring**: `Tr(F P (F P)′) = q Tr(P P′)`. -/
theorem rosatiDeg_delay (P : ℝ[X]) : rosatiDeg D (X * P) = D.q * rosatiDeg D P := by
  unfold rosatiDeg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, aeval_X]
  linear_combination (aeval (eigenvalue D i) P * aeval (eigenvalue D (D.fePerm i)) P) *
    eigenvalue_mul_fePerm D i

/-- The power sums of the partners are the power sums. -/
theorem sum_eigenvalue_fePerm_pow (n : ℕ) :
    ∑ i, eigenvalue D (D.fePerm i) ^ n = ∑ i, eigenvalue D i ^ n :=
  Equiv.sum_comp D.fePerm (fun i => eigenvalue D i ^ n)

theorem sum_eigenvalue_pow (n : ℕ) : ∑ i, eigenvalue D i ^ n = ((D.sqrtq ^ n * D.trace n : ℝ) : ℂ) := by
  unfold eigenvalue
  simp only [mul_pow, ← Finset.mul_sum]
  have : ∑ i, D.β i ^ n = D.powerSum n := rfl
  rw [this, D.powerSum_eq_trace]
  push_cast
  ring

/-- **The two-term Rosati form is twice the genus form**: on the probe `y − x Fⁿ` it is
`#ι (y² + qⁿ x²) − 2 qⁿᐟ² (Re Σ βⁿ) x y`. -/
theorem rosatiDeg_twoTerm (n : ℕ) (x y : ℝ) :
    rosatiDeg D (C y - C x * X ^ n) =
      ((Fintype.card ι * (y ^ 2 + D.q ^ n * x ^ 2) - 2 * (D.sqrtq ^ n * D.trace n) * x * y : ℝ) : ℂ) := by
  unfold rosatiDeg
  simp only [map_sub, map_mul, aeval_C, aeval_X_pow, Complex.coe_algebraMap]
  have hprod (i : ι) : (eigenvalue D i) ^ n * (eigenvalue D (D.fePerm i)) ^ n = (D.q : ℂ) ^ n := by
    rw [← mul_pow, eigenvalue_mul_fePerm]
  have expand (i : ι) : ((y : ℂ) - (x : ℂ) * eigenvalue D i ^ n) *
      ((y : ℂ) - (x : ℂ) * eigenvalue D (D.fePerm i) ^ n) =
      (y : ℂ) ^ 2 - (x : ℂ) * (y : ℂ) * (eigenvalue D i ^ n + eigenvalue D (D.fePerm i) ^ n) +
        (x : ℂ) ^ 2 * (D.q : ℂ) ^ n := by
    linear_combination (x : ℂ) ^ 2 * hprod i
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sum_eigenvalue_fePerm_pow, sum_eigenvalue_pow]
  push_cast
  ring

/-- **Height, sign, count law and damping are one condition.** For a curve datum of genus `g` with
integer size and natural point counts: the integral Rosati form has a naive height; it is nonnegative on
`ℤ[F]`; the channel numbers extend to a count law at every level; the datum is unitary. -/
theorem rosati_tfae {g Q : ℕ} (hg : Fintype.card ι = 2 * g) (hg0 : 0 < g) (hQ : D.q = Q)
    {N : ℕ → ℕ} (hN : ∀ n, (N n : ℝ) = D.pointCount n) :
    List.TFAE [∃ h : ℤ[X] → ℝ, ∃ K B : ℝ, (∀ P, -K ≤ h P) ∧ ∀ P, |h P - intRosatiDeg D P| ≤ B,
      ∀ P : ℤ[X], 0 ≤ intRosatiDeg D P,
      ∀ n, 1 ≤ n → ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = g ∧ K 1 0 = g * Q ^ n ∧
        K 1 1 = N n + (g - 1) * (Q ^ n + 1),
      ∀ i, ‖D.β i‖ = 1] := by
  tfae_have 1 ↔ 4 := exists_naiveHeight_iff_unitary D
  tfae_have 2 ↔ 4 := intRosatiDeg_nonneg_iff_unitary D
  tfae_have 3 ↔ 4 := towerCountLaw_iff_unitary D hg hg0 hQ hN
  tfae_finish

end Datum

/-! ### True hyperelliptic curves -/

section Hyperelliptic

open GaloisForLFunctions.RHTower.Hyperelliptic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- **The count law of every true odd-degree hyperelliptic curve, at every level.** For `y² = f(x)`,
`f` squarefree of degree `2g + 1`, odd characteristic, and every finite extension `E` of degree `n`, the
channel numbers `g`, `g qⁿ`, `N_E + (g − 1)(qⁿ + 1)` extend to a count law, with `N_E` the number of
points over `E` including the point at infinity. -/
theorem hyperelliptic_countLaw (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) {g : ℕ}
    (hdeg : f.natDegree = 2 * g + 1) (hg : 1 ≤ g) (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = g ∧
      K 1 0 = g * Fintype.card F ^ Module.finrank F E ∧
      K 1 1 = ((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card + 1) +
        (g - 1) * (Fintype.card F ^ Module.finrank F E + 1) := by
  have hodd : Odd f.natDegree := ⟨g, hdeg⟩
  set D := hyperellipticDatum hF hsq hodd
  have hcard : Fintype.card (Fin (lRoots f).toList.length) = 2 * g := by
    rw [card_hyperellipticDatum hodd, hdeg]
    omega
  have hQ : D.q = (Fintype.card F : ℕ) := rfl
  have hN : (((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card + 1 : ℕ) : ℝ) =
      D.pointCount (Module.finrank F E) := by
    rw [hyperellipticDatum_pointCount hF hsq hodd E]
    push_cast
    rfl
  exact (exists_levelCountLaw_iff D hcard hg hQ hN).mpr
    (abs_trace_le_of_unitary D (hyperellipticDatum_unitary hF hsq hodd) _)

/-- **The Rosati form of every true odd-degree hyperelliptic curve has a naive height**, and is a Born rule
on its probe ring. -/
theorem hyperelliptic_naiveHeight (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) :
    (∃ h : ℤ[X] → ℝ, ∃ K B : ℝ, (∀ P, -K ≤ h P) ∧
      ∀ P, |h P - intRosatiDeg (hyperellipticDatum hF hsq hodd) P| ≤ B) ∧
      ∀ P : ℝ[X], rosatiDeg (hyperellipticDatum hF hsq hodd) (X * P) =
        (Fintype.card F : ℂ) * rosatiDeg (hyperellipticDatum hF hsq hodd) P :=
  ⟨hyperellipticDatum_exists_naiveHeight hF hsq hodd, fun P => by
    rw [rosatiDeg_delay]
    rfl⟩

end Hyperelliptic

end GaloisForLFunctions.CountingHolography

end
