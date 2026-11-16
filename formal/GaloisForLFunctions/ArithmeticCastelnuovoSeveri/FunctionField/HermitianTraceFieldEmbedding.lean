import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianKummerModels
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomialDegree

/-!
# Hermitian trace embeddings of Kummer function fields

The trace substitution extends from polynomial coordinate rings to the
actual irreducible radical fields. Nonconstant trace coordinates give
an embedding of the rational base; the defining radical relation then
gives an injective field homomorphism.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : Kˣ) (d r m : ℕ)

/-- An irreducible radical field with Hermitian-form equation `v^(Q+1)=c(x-x^Q)`. -/
abbrev HermitianTraceSourceField :=
  KummerBranchField c (p ^ ((d + 1) * (r + 1) * (m + 1)) - 2) 1
    (p ^ ((d + 1) * (r + 1) * (m + 1)))

private instance hermitianTraceSource_charP : CharP (HermitianTraceSourceField p c d r m) p :=
  charP_of_injective_algebraMap (algebraMap K (HermitianTraceSourceField p c d r m)).injective p

/-- The power of the trace polynomial that pulls back the Kummer coordinate. -/
def hermitianTraceFieldCoordinate : HermitianTraceSourceField p c d r m :=
  frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1)
    (algebraMap K[X] (HermitianTraceSourceField p c d r m) X) ^
      kummerExponent (p ^ (d + 1)) (r + 1)

/-- The trace coordinate is transcendental, so its rational-function field embeds. -/
theorem hermitianTraceFieldCoordinate_transcendental :
    Transcendental K (hermitianTraceFieldCoordinate p c d r m) := by
  have hdegree : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
  have ht := frobeniusTraceSum_transcendental p ((d + 1) * (r + 1) - 1) m
    (kummerBranchField_coordinate_transcendental c
      (p ^ ((d + 1) * (r + 1) * (m + 1)) - 2) 1
      (p ^ ((d + 1) * (r + 1) * (m + 1))))
  rw [hdegree] at ht
  have hR : 0 < kummerExponent (p ^ (d + 1)) (r + 1) := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (r + 1)) =>
      Nat.zero_le ((p ^ (d + 1)) ^ i)) (Finset.mem_range.mpr (Nat.succ_pos r))
    simpa only [kummerExponent, pow_zero] using h
  intro h
  exact ht (IsIntegral.of_pow hR h.isIntegral).isAlgebraic

/-- The source radical satisfies its literal Hermitian-form relation. -/
theorem hermitianTraceSource_root_pow :
    AdjoinRoot.root (kummerBranchFieldPolynomial c
      (p ^ ((d + 1) * (r + 1) * (m + 1)) - 2) 1
      (p ^ ((d + 1) * (r + 1) * (m + 1)))) ^
        (p ^ ((d + 1) * (r + 1) * (m + 1)) + 1) =
    algebraMap K (HermitianTraceSourceField p c d r m) c *
      (algebraMap K[X] (HermitianTraceSourceField p c d r m) X -
        (algebraMap K[X] (HermitianTraceSourceField p c d r m) X) ^
          p ^ ((d + 1) * (r + 1) * (m + 1))) := by
  let Q := p ^ ((d + 1) * (r + 1) * (m + 1))
  let H := HermitianTraceSourceField p c d r m
  have hQ : 2 ≤ Q := Nat.one_lt_pow
    (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero d) (Nat.succ_ne_zero r))
      (Nat.succ_ne_zero m)) (Fact.out : p.Prime).one_lt
  rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply,
    kummerBranch, map_mul, map_mul, map_pow, map_sub, map_one, map_pow, pow_one]
  have hc : algebraMap K[X] H (C (c : K)) = algebraMap K H c :=
    (IsScalarTower.algebraMap_apply K K[X] H c).symm
  rw [hc]
  change algebraMap K H c * algebraMap K[X] H X *
    (1 - algebraMap K[X] H X ^ (Q - 2 + 1)) = _
  rw [show Q - 2 + 1 = Q - 1 by omega]
  have hpow : algebraMap K[X] H X * algebraMap K[X] H X ^ (Q - 1) =
      algebraMap K[X] H X ^ Q := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  calc
    _ = algebraMap K H c * (algebraMap K[X] H X -
      algebraMap K[X] H X * algebraMap K[X] H X ^ (Q - 1)) := by ring
    _ = _ := by rw [hpow]

private theorem hermitianTraceField_eval :
    (kummerBranchFieldPolynomial (c ^ kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ ((d + 1) * (r + 1) * (m + 1)))).eval₂
        (fracRealize (hermitianTraceFieldCoordinate_transcendental p c d r m))
        (AdjoinRoot.root (kummerBranchFieldPolynomial c
          (p ^ ((d + 1) * (r + 1) * (m + 1)) - 2) 1
          (p ^ ((d + 1) * (r + 1) * (m + 1)))) ^
            kummerExponent (p ^ (d + 1)) (r + 1)) = 0 := by
  let H := HermitianTraceSourceField p c d r m
  let Q := p ^ ((d + 1) * (r + 1) * (m + 1))
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  let v := AdjoinRoot.root (kummerBranchFieldPolynomial c (Q - 2) 1 Q)
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have ht := trace_kummer_identity (K := H) p (d + 1) (r + 1) (m + 1)
    (algebraMap K H c) (algebraMap K[X] H X)
  change (X ^ (Q + 1) - C (algebraMap K[X] (FractionRing K[X])
    (kummerBranch (c ^ R) (p ^ (d + 1) - 2) R))).eval₂
      (fracRealize (hermitianTraceFieldCoordinate_transcendental p c d r m)) (v ^ R) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (v ^ R) ^ (Q + 1) -
    fracRealize (hermitianTraceFieldCoordinate_transcendental p c d r m)
      (algebraMap K[X] (FractionRing K[X]) (kummerBranch (c ^ R) (p ^ (d + 1) - 2) R)) = 0
  rw [fracRealize_algebraMap, kummerBranch]
  simp only [map_mul, map_pow, map_sub, map_one, aeval_C, aeval_X, Units.val_pow_eq_pow_val]
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega,
    ← pow_mul, Nat.mul_comm R (Q + 1), pow_mul, hermitianTraceSource_root_pow]
  exact sub_eq_zero.mpr (by simpa only [map_pow] using ht)

/-- The Hermitian trace substitution embeds the actual Kummer function field. -/
def hermitianKummerFieldHom :
    KummerBranchField (c ^ kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ ((d + 1) * (r + 1) * (m + 1))) →ₐ[K]
        HermitianTraceSourceField p c d r m :=
  AdjoinRoot.liftAlgHom _ (fracRealize (hermitianTraceFieldCoordinate_transcendental p c d r m))
    (AdjoinRoot.root (kummerBranchFieldPolynomial c
      (p ^ ((d + 1) * (r + 1) * (m + 1)) - 2) 1
      (p ^ ((d + 1) * (r + 1) * (m + 1)))) ^
        kummerExponent (p ^ (d + 1)) (r + 1)) (hermitianTraceField_eval p c d r m)

/-- The rational coordinate pulls back to the power of the trace. -/
theorem hermitianKummerFieldHom_coordinate :
    hermitianKummerFieldHom p c d r m
      (algebraMap K[X] _ X) = hermitianTraceFieldCoordinate p c d r m := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]), AdjoinRoot.algebraMap_eq,
    hermitianKummerFieldHom, AdjoinRoot.liftAlgHom_of, fracRealize_algebraMap, aeval_X]

/-- The Kummer radical pulls back to the corresponding power of the Hermitian radical. -/
theorem hermitianKummerFieldHom_root :
    hermitianKummerFieldHom p c d r m
      (AdjoinRoot.root (kummerBranchFieldPolynomial
        (c ^ kummerExponent (p ^ (d + 1)) (r + 1)) (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) (r + 1)) (p ^ ((d + 1) * (r + 1) * (m + 1))))) =
    AdjoinRoot.root (kummerBranchFieldPolynomial c
      (p ^ ((d + 1) * (r + 1) * (m + 1)) - 2) 1
      (p ^ ((d + 1) * (r + 1) * (m + 1)))) ^
        kummerExponent (p ^ (d + 1)) (r + 1) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The trace map is injective because it is a homomorphism of the constructed fields. -/
theorem hermitianKummerFieldHom_injective :
    Function.Injective (hermitianKummerFieldHom p c d r m) :=
  (hermitianKummerFieldHom p c d r m).injective

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
