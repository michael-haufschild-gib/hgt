import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators

/-!
# Radical fields of Frobenius branch polynomials

For `q=b+2`, the polynomial `c (X^q-X) (1+(X^q-X)^(q-1))^R`
has a simple zero at zero. Eisenstein therefore constructs its radical
function field over any constant field, with the exact prescribed degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)

/-- The Frobenius branch polynomial, factored to display its simple origin zero. -/
def frobeniusKummerBranch : K[X] :=
  C (c : K) * (X * ((X ^ (b + 1) - 1) *
    (1 + (X ^ (b + 2) - X) ^ (b + 1)) ^ R))

/-- The branch polynomial has the standard additive-coordinate presentation. -/
theorem frobeniusKummerBranch_eq : frobeniusKummerBranch c b R =
    C (c : K) * (X ^ (b + 2) - X) * (1 + (X ^ (b + 2) - X) ^ (b + 1)) ^ R := by
  have h : (X : K[X]) * (X ^ (b + 1) - 1) = X ^ (b + 2) - X := by
    rw [mul_sub, mul_one, ← pow_succ']
  rw [frobeniusKummerBranch, ← mul_assoc X, h, ← mul_assoc]

/-- The Frobenius branch polynomial vanishes at zero. -/
theorem frobeniusKummerBranch_coeff_zero : (frobeniusKummerBranch c b R).coeff 0 = 0 := by
  simp only [frobeniusKummerBranch, coeff_zero_eq_eval_zero, eval_mul, eval_C, eval_X,
    zero_mul, mul_zero]

/-- The linear coefficient is the negative of the chosen unit. -/
theorem frobeniusKummerBranch_coeff_one : (frobeniusKummerBranch c b R).coeff 1 = -(c : K) := by
  rw [frobeniusKummerBranch, coeff_C_mul, coeff_X_mul]
  simp only [coeff_zero_eq_eval_zero, eval_mul, eval_sub, eval_pow, eval_X, eval_one,
    eval_add, zero_pow (Nat.succ_ne_zero b), zero_pow (by omega : b + 2 ≠ 0),
    sub_self, zero_sub, add_zero, one_pow, mul_one, mul_neg_one]

/-- The radical equation is irreducible over the rational function field. -/
theorem frobeniusKummerBranch_fraction_irreducible :
    Irreducible (X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X])
      (frobeniusKummerBranch c b R)) : (FractionRing K[X])[X]) := by
  have hi := simpleZero_radical_irreducible (frobeniusKummerBranch_coeff_zero c b R)
    (show (frobeniusKummerBranch c b R).coeff 1 ≠ 0 by
      rw [frobeniusKummerBranch_coeff_one]; exact neg_ne_zero.mpr c.ne_zero) n
  have hm := monic_X_pow_sub_C (frobeniusKummerBranch c b R) (Nat.succ_ne_zero n)
  have h := (hm.isPrimitive.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing K[X])).mp hi
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] using h

/-- The defining polynomial over the rational function field. -/
def frobeniusKummerFieldPolynomial : (FractionRing K[X])[X] :=
  X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X]) (frobeniusKummerBranch c b R))

instance frobeniusKummerFieldPolynomial_irreducible :
    Fact (Irreducible (frobeniusKummerFieldPolynomial c b R n)) :=
  ⟨frobeniusKummerBranch_fraction_irreducible c b R n⟩

/-- The actual radical field; its field structure follows from Eisenstein irreducibility. -/
abbrev FrobeniusKummerField := AdjoinRoot (frobeniusKummerFieldPolynomial c b R n)

/-- The irreducible radical equation makes the field finite-dimensional over its rational base. -/
instance frobeniusKummerField_finiteDimensional :
    FiniteDimensional (FractionRing K[X]) (FrobeniusKummerField c b R n) :=
  (AdjoinRoot.powerBasis
    (frobeniusKummerBranch_fraction_irreducible c b R n).ne_zero).finite

/-- The constant-field embedding preserves characteristic in the constructed radical field. -/
instance frobeniusKummerField_charP (p : ℕ) [CharP K p] :
    CharP (FrobeniusKummerField c b R n) p :=
  charP_of_injective_algebraMap (algebraMap K (FrobeniusKummerField c b R n)).injective p

/-- The polynomial coordinate ring acts faithfully through its fraction field. -/
instance frobeniusKummerField_torsionFree :
    Module.IsTorsionFree K[X] (FrobeniusKummerField c b R n) :=
  Module.IsTorsionFree.trans (FractionRing K[X])

/-- The radical field has exactly the prescribed degree over its rational base. -/
theorem frobeniusKummerField_finrank :
    Module.finrank (FractionRing K[X]) (FrobeniusKummerField c b R n) = n + 1 := by
  have hi := (frobeniusKummerFieldPolynomial_irreducible c b R n).out
  calc
    _ = (AdjoinRoot.powerBasis hi.ne_zero).dim := (AdjoinRoot.powerBasis hi.ne_zero).finrank
    _ = n + 1 := by
      rw [AdjoinRoot.powerBasis_dim, frobeniusKummerFieldPolynomial, natDegree_X_pow_sub_C]

/-- The canonical radical satisfies the literal branch equation. -/
theorem frobeniusKummerField_root_pow :
    AdjoinRoot.root (frobeniusKummerFieldPolynomial c b R n) ^ (n + 1) =
      algebraMap (FractionRing K[X]) (FrobeniusKummerField c b R n)
        (algebraMap K[X] (FractionRing K[X]) (frobeniusKummerBranch c b R)) := by
  have h := AdjoinRoot.eval₂_root (frobeniusKummerFieldPolynomial c b R n)
  change (X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X])
    (frobeniusKummerBranch c b R))).eval₂ (AdjoinRoot.of (frobeniusKummerFieldPolynomial c b R n))
      (AdjoinRoot.root (frobeniusKummerFieldPolynomial c b R n)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

/-- Evaluation at the coordinate is the canonical polynomial embedding. -/
theorem frobeniusKummerField_aeval_coordinate :
    aeval (algebraMap K[X] (FrobeniusKummerField c b R n) X) =
      IsScalarTower.toAlgHom K K[X] (FrobeniusKummerField c b R n) := by
  apply Polynomial.algHom_ext
  rw [aeval_X]
  rfl

/-- The rational coordinate stays transcendental in the constructed radical field. -/
theorem frobeniusKummerField_coordinate_transcendental :
    Transcendental K (algebraMap K[X] (FrobeniusKummerField c b R n) X) := by
  let L := FrobeniusKummerField c b R n
  have hinj : Function.Injective (algebraMap K[X] L) := by
    rw [IsScalarTower.algebraMap_eq K[X] (FractionRing K[X]) L]
    exact (algebraMap (FractionRing K[X]) L).injective.comp (IsFractionRing.injective K[X] _)
  rw [transcendental_iff]
  intro f hf
  rw [frobeniusKummerField_aeval_coordinate] at hf
  exact hinj (hf.trans (map_zero _).symm)

/-- The canonical radical is nonzero. -/
theorem frobeniusKummerField_root_ne_zero :
    AdjoinRoot.root (frobeniusKummerFieldPolynomial c b R n) ≠ 0 := by
  have hf : frobeniusKummerBranch c b R ≠ 0 := by
    intro h
    have he := congrArg (fun f : K[X] => f.coeff 1) h
    rw [frobeniusKummerBranch_coeff_one, coeff_zero] at he
    exact c.ne_zero (neg_eq_zero.mp he)
  intro hz
  have h := frobeniusKummerField_root_pow c b R n
  rw [hz, zero_pow (Nat.succ_ne_zero n)] at h
  have hbase := (algebraMap (FractionRing K[X]) (FrobeniusKummerField c b R n)).injective
    (h.symm.trans (map_zero _).symm)
  exact hf (IsFractionRing.injective K[X] (FractionRing K[X])
    (hbase.trans (map_zero _).symm))

/-- The coordinate generates the full rational base inside every constant subfield. -/
theorem frobeniusKummerField_base_mem_of_coordinate_mem
    (S : IntermediateField K (FrobeniusKummerField c b R n))
    (hX : algebraMap K[X] (FrobeniusKummerField c b R n) X ∈ S) (x : FractionRing K[X]) :
    algebraMap (FractionRing K[X]) (FrobeniusKummerField c b R n) x ∈ S := by
  let L := FrobeniusKummerField c b R n
  have hp : ∀ f : K[X], algebraMap K[X] L f ∈ S := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
    | monomial i a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply S.mul_mem _ (pow_mem hX i)
      have h := S.algebraMap_mem a
      rw [IsScalarTower.algebraMap_apply K K[X] L] at h
      exact h
  obtain ⟨f, g, _, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) x
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact S.div_mem (hp f) (hp g)

/-- The coordinate and radical generate the whole Frobenius branch field. -/
theorem frobeniusKummerField_eq_top_of_coordinate_root_mem
    (S : IntermediateField K (FrobeniusKummerField c b R n))
    (hX : algebraMap K[X] (FrobeniusKummerField c b R n) X ∈ S)
    (hz : AdjoinRoot.root (frobeniusKummerFieldPolynomial c b R n) ∈ S) : S = ⊤ := by
  apply top_unique
  intro x _
  refine AdjoinRoot.induction_on (frobeniusKummerFieldPolynomial c b R n) x ?_
  intro f
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
  | monomial i a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact S.mul_mem (frobeniusKummerField_base_mem_of_coordinate_mem c b R n S hX a)
      (pow_mem hz i)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
