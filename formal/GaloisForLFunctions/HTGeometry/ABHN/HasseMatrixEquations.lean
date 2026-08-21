import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSingularity

/-!
# Hasse detection for specified matrix equations

For matrices and vectors with coefficients in a global field, a specified global linear equation
or matrix factorization holds exactly when it holds after scalar extension to every completion.
This detects an already-specified global candidate; it does not assert that unrelated local
solutions descend to one global solution.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w z

/-- A specified linear system over a number field holds exactly when it holds after scalar
extension to every completed place. -/
theorem numberFieldMatrix_mulVec_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) (κ : Type w) [Fintype κ]
    (A : Matrix ι κ K) (x : κ → K) (b : ι → K) :
    A.mulVec x = b ↔ ∀ v : NumberFieldPlace K,
      (A.map (placeEmbedding K v)).mulVec (fun j => placeEmbedding K v (x j)) =
        fun i => placeEmbedding K v (b i) := by
  constructor
  · intro h v
    funext i
    change (A.map (placeEmbedding K v)).mulVec ((placeEmbedding K v) ∘ x) i =
      placeEmbedding K v (b i)
    rw [← (placeEmbedding K v).map_mulVec]
    exact congrArg (placeEmbedding K v) (congrFun h i)
  · intro h
    funext i
    apply (placeEmbedding K (witnessPlace K)).injective
    change placeEmbedding K (witnessPlace K) (A.mulVec x i) =
      placeEmbedding K (witnessPlace K) (b i)
    rw [(placeEmbedding K (witnessPlace K)).map_mulVec]
    have hw := congrFun (h (witnessPlace K)) i
    change (A.map (placeEmbedding K (witnessPlace K))).mulVec
      ((placeEmbedding K (witnessPlace K)) ∘ x) i =
        placeEmbedding K (witnessPlace K) (b i) at hw
    exact hw

/-- A specified linear system over `F(t)` holds exactly when it holds after scalar extension to
every finite and infinite completion. -/
theorem rationalFunctionMatrix_mulVec_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (ι : Type v) (κ : Type w) [Fintype κ]
    (A : Matrix ι κ (RatFunc F)) (x : κ → RatFunc F) (b : ι → RatFunc F) :
    A.mulVec x = b ↔ ∀ v : RationalFunctionPlace F,
      (A.map (rationalFunctionPlaceEmbedding F v)).mulVec
          (fun j => rationalFunctionPlaceEmbedding F v (x j)) =
        fun i => rationalFunctionPlaceEmbedding F v (b i) := by
  constructor
  · intro h v
    funext i
    change (A.map (rationalFunctionPlaceEmbedding F v)).mulVec
      ((rationalFunctionPlaceEmbedding F v) ∘ x) i =
        rationalFunctionPlaceEmbedding F v (b i)
    rw [← (rationalFunctionPlaceEmbedding F v).map_mulVec]
    exact congrArg (rationalFunctionPlaceEmbedding F v) (congrFun h i)
  · intro h
    funext i
    apply (rationalFunctionPlaceEmbedding F .infinite).injective
    change rationalFunctionPlaceEmbedding F .infinite (A.mulVec x i) =
      rationalFunctionPlaceEmbedding F .infinite (b i)
    rw [(rationalFunctionPlaceEmbedding F .infinite).map_mulVec]
    have hw := congrFun (h .infinite) i
    change (A.map (rationalFunctionPlaceEmbedding F .infinite)).mulVec
      ((rationalFunctionPlaceEmbedding F .infinite) ∘ x) i =
        rationalFunctionPlaceEmbedding F .infinite (b i) at hw
    exact hw

/-- A specified matrix factorization over a number field holds exactly when it holds after
scalar extension to every completed place. -/
theorem numberFieldMatrix_mul_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) (κ : Type w) (o : Type z) [Fintype κ]
    (A : Matrix ι κ K) (B : Matrix κ o K) (C : Matrix ι o K) :
    A * B = C ↔ ∀ p : NumberFieldPlace K,
      A.map (placeEmbedding K p) * B.map (placeEmbedding K p) = C.map (placeEmbedding K p) := by
  constructor
  · intro h p
    rw [← Matrix.map_mul]
    exact congrArg (fun X => X.map (placeEmbedding K p)) h
  · intro h
    ext i j
    apply (placeEmbedding K (witnessPlace K)).injective
    change (A * B).map (placeEmbedding K (witnessPlace K)) i j =
      C.map (placeEmbedding K (witnessPlace K)) i j
    rw [Matrix.map_mul]
    exact congrFun (congrFun (h (witnessPlace K)) i) j

/-- A specified matrix factorization over `F(t)` holds exactly when it holds after scalar
extension to every finite and infinite completion. -/
theorem rationalFunctionMatrix_mul_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (ι : Type v) (κ : Type w) (o : Type z) [Fintype κ]
    (A : Matrix ι κ (RatFunc F)) (B : Matrix κ o (RatFunc F))
    (C : Matrix ι o (RatFunc F)) :
    A * B = C ↔ ∀ p : RationalFunctionPlace F,
      A.map (rationalFunctionPlaceEmbedding F p) * B.map (rationalFunctionPlaceEmbedding F p) =
        C.map (rationalFunctionPlaceEmbedding F p) := by
  constructor
  · intro h p
    rw [← Matrix.map_mul]
    exact congrArg (fun X => X.map (rationalFunctionPlaceEmbedding F p)) h
  · intro h
    ext i j
    apply (rationalFunctionPlaceEmbedding F .infinite).injective
    change (A * B).map (rationalFunctionPlaceEmbedding F .infinite) i j =
      C.map (rationalFunctionPlaceEmbedding F .infinite) i j
    rw [Matrix.map_mul]
    exact congrFun (congrFun (h .infinite) i) j

end GaloisForLFunctions.HTGeometry.ABHN
