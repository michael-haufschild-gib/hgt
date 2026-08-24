import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixEquations
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseRectangularMatrixRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixInvariants
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSingularity

/-!
# Matrix rank, equation, and invariant defects at every completion

Faithful completion reflects matrix equations, ranks, characteristic polynomials, determinants,
traces, singularity, and prescribed characteristic roots.  Their failures persist at every
global-field place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- Failure of a fixed number-field linear system persists everywhere. -/
theorem numberFieldMatrix_mulVec_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) (κ : Type w) [Fintype κ]
    (A : Matrix ι κ K) (x : κ → K) (b : ι → K) :
    A.mulVec x ≠ b ↔ ∀ p : NumberFieldPlace K,
      (A.map (placeEmbedding K p)).mulVec (fun j => placeEmbedding K p (x j)) ≠
        fun i => placeEmbedding K p (b i) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_mulVec_eq_iff_exists_place K ι κ A x b)

/-- Failure of a fixed function-field linear system persists everywhere. -/
theorem rationalFunctionMatrix_mulVec_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (ι : Type v) (κ : Type w) [Fintype κ]
    (A : Matrix ι κ (RatFunc F)) (x : κ → RatFunc F) (b : ι → RatFunc F) :
    A.mulVec x ≠ b ↔ ∀ p : RationalFunctionPlace F,
      (A.map (rationalFunctionPlaceEmbedding F p)).mulVec
          (fun j => rationalFunctionPlaceEmbedding F p (x j)) ≠
        fun i => rationalFunctionPlaceEmbedding F p (b i) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_mulVec_eq_iff_exists_place F ι κ A x b)

/-- Failure of a fixed number-field matrix factorization persists everywhere. -/
theorem numberFieldMatrix_mul_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) (κ : Type w) (o : Type x) [Fintype κ]
    (A : Matrix ι κ K) (B : Matrix κ o K) (C : Matrix ι o K) :
    A * B ≠ C ↔ ∀ p : NumberFieldPlace K,
      A.map (placeEmbedding K p) * B.map (placeEmbedding K p) ≠
        C.map (placeEmbedding K p) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_mul_eq_iff_exists_place K ι κ o A B C)

/-- Failure of a fixed function-field matrix factorization persists everywhere. -/
theorem rationalFunctionMatrix_mul_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (ι : Type v) (κ : Type w) (o : Type x) [Fintype κ]
    (A : Matrix ι κ (RatFunc F)) (B : Matrix κ o (RatFunc F))
    (C : Matrix ι o (RatFunc F)) :
    A * B ≠ C ↔ ∀ p : RationalFunctionPlace F,
      A.map (rationalFunctionPlaceEmbedding F p) *
          B.map (rationalFunctionPlaceEmbedding F p) ≠
        C.map (rationalFunctionPlaceEmbedding F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_mul_eq_iff_exists_place F ι κ o A B C)

/-- Failure of a prescribed square-matrix rank over a number field persists everywhere. -/
theorem numberFieldMatrix_rank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) (r : ℕ) :
    M.rank ≠ r ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).rank ≠ r :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_rank_eq_iff_exists_place K n M r)

/-- Failure of a prescribed square-matrix rank over a function field persists everywhere. -/
theorem rationalFunctionMatrix_rank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) (r : ℕ) :
    M.rank ≠ r ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank ≠ r :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_rank_eq_iff_exists_place F n M r)

/-- Failure of a prescribed rectangular-matrix rank over a number field persists everywhere. -/
theorem numberFieldRectMatrix_rank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (r : ℕ) :
    M.rank ≠ r ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).rank ≠ r :=
  not_iff_forall_not_of_iff_exists
    (numberFieldRectMatrix_rank_eq_iff_exists_place K m n M r)

/-- Failure of a prescribed rectangular-matrix rank over a function field persists everywhere. -/
theorem rationalFunctionRectMatrix_rank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n (RatFunc F)) (r : ℕ) :
    M.rank ≠ r ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank ≠ r :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionRectMatrix_rank_eq_iff_exists_place F m n M r)

/-- A wrong number-field matrix characteristic polynomial persists everywhere. -/
theorem numberFieldMatrix_charpoly_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (q : Polynomial K) :
    M.charpoly ≠ q ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).charpoly ≠
        q.map (algebraMap K (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_charpoly_eq_iff_exists_place K n M q)

/-- A wrong function-field matrix characteristic polynomial persists everywhere. -/
theorem rationalFunctionMatrix_charpoly_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (q : Polynomial (RatFunc F)) :
    M.charpoly ≠ q ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).charpoly ≠
        q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_charpoly_eq_iff_exists_place F n M q)

/-- A wrong number-field matrix determinant persists everywhere. -/
theorem numberFieldMatrix_det_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) (c : K) :
    M.det ≠ c ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).det ≠ algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_det_eq_iff_exists_place K n M c)

/-- A wrong function-field matrix determinant persists everywhere. -/
theorem rationalFunctionMatrix_det_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (c : RatFunc F) :
    M.det ≠ c ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).det ≠
        algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_det_eq_iff_exists_place F n M c)

/-- A wrong number-field matrix trace persists everywhere. -/
theorem numberFieldMatrix_trace_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] (M : Matrix n n K) (c : K) :
    M.trace ≠ c ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).trace ≠ algebraMap K (completion K p) c :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_trace_eq_iff_exists_place K n M c)

/-- A wrong function-field matrix trace persists everywhere. -/
theorem rationalFunctionMatrix_trace_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] (M : Matrix n n (RatFunc F)) (c : RatFunc F) :
    M.trace ≠ c ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).trace ≠
        algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_trace_eq_iff_exists_place F n M c)

/-- Failure of a prescribed characteristic root over a number field persists everywhere. -/
theorem numberFieldMatrix_sub_scalar_det_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) (a : K) :
    (M - a • 1).det ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      (M.map (placeEmbedding K p) - placeEmbedding K p a • 1).det ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMatrix_sub_scalar_det_eq_zero_iff_exists_place K n M a)

/-- Failure of a prescribed characteristic root over a function field persists everywhere. -/
theorem rationalFunctionMatrix_sub_scalar_det_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (a : RatFunc F) :
    (M - a • 1).det ≠ 0 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (rationalFunctionPlaceEmbedding F p) -
        rationalFunctionPlaceEmbedding F p a • 1).det ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMatrix_sub_scalar_det_eq_zero_iff_exists_place F n M a)

end GaloisForLFunctions.HTGeometry.ABHN
