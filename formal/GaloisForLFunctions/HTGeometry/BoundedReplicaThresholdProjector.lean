import GaloisForLFunctions.HTGeometry.BinomialTailBetaThreshold

/-!
# The literal bounded replica threshold projector

On the `r`-fold tensor power of a finite-dimensional complex Hilbert space, written in the product
basis indexed by `Fin r → n`, the outcome strings of `r` independent yes/no measurements of a
rank-one target projection `P_z` give mutually orthogonal projections.  Their sum over strings with
at least `k` successes,

`Q_{z;r,k} = ∑_{|S| ≥ k} ⊗_i (P_z if i ∈ S else 1 - P_z)`,

is a projection whose expectation in the replica state `v^{⊗r}` is exactly the binomial tail
polynomial evaluated at the squared overlap `|⟨z, v⟩|²`.  This is the bounded quantum hypothesis
test behind the beta-threshold incidence law: a test with both a success and a failure outcome,
never a monomial moment.

Everything here is a finite identity in the product basis; no infinite-dimensional analysis and no
abstract tensor construction are used.
-/

open Finset Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Sesquilinear forms in a finite product basis -/

/-- The sesquilinear form of a matrix, in the convention conjugate-linear in the first slot. -/
def boundedReplicaThresholdProjectorQuadForm {m : Type*} [Fintype m] (M : Matrix m m ℂ) (w : m → ℂ) : ℂ :=
  star w ⬝ᵥ (M *ᵥ w)

theorem quadForm_eq_sum {m : Type*} [Fintype m] (M : Matrix m m ℂ) (w : m → ℂ) :
    boundedReplicaThresholdProjectorQuadForm M w = ∑ f, ∑ g, conj (w f) * M f g * w g := by
  simp [boundedReplicaThresholdProjectorQuadForm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem quadForm_add {m : Type*} [Fintype m] (M N : Matrix m m ℂ) (w : m → ℂ) :
    boundedReplicaThresholdProjectorQuadForm (M + N) w = boundedReplicaThresholdProjectorQuadForm M w + boundedReplicaThresholdProjectorQuadForm N w := by
  simp only [quadForm_eq_sum, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => by ring

theorem quadForm_sum {m ι : Type*} [Fintype m] (s : Finset ι) (M : ι → Matrix m m ℂ)
    (w : m → ℂ) : boundedReplicaThresholdProjectorQuadForm (∑ i ∈ s, M i) w = ∑ i ∈ s, boundedReplicaThresholdProjectorQuadForm (M i) w := by
  classical
  induction s using Finset.induction with
  | empty => simp [quadForm_eq_sum]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, quadForm_add, ih]

theorem star_dotProduct_self {m : Type*} [Fintype m] (u : m → ℂ) :
    star u ⬝ᵥ u = ((∑ c, Complex.normSq (u c) : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- The Gram identity: the form of `Mᴴ * M` is the squared norm of the image vector, hence real
and nonnegative. -/
theorem quadForm_conjTranspose_mul {m : Type*} [Fintype m] (M : Matrix m m ℂ) (w : m → ℂ) :
    boundedReplicaThresholdProjectorQuadForm (Mᴴ * M) w = ((∑ c, Complex.normSq ((M *ᵥ w) c) : ℝ) : ℂ) := by
  rw [boundedReplicaThresholdProjectorQuadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    star_dotProduct_self]

/-! ### Replica tensor powers in the product basis -/

/-- The `r`-fold tensor power of a vector, written in the product basis. -/
def replicaVector (r : ℕ) (v : n → ℂ) : (Fin r → n) → ℂ := fun f => ∏ i, v (f i)

/-- The `r`-fold tensor product of matrices, written in the product basis. -/
def replicaOp (r : ℕ) (A : Fin r → Matrix n n ℂ) : Matrix (Fin r → n) (Fin r → n) ℂ :=
  Matrix.of fun f g => ∏ i, A i (f i) (g i)

omit [Fintype n] [DecidableEq n] in
theorem replicaOp_apply (r : ℕ) (A : Fin r → Matrix n n ℂ) (f g : Fin r → n) :
    replicaOp r A f g = ∏ i, A i (f i) (g i) := rfl

omit [DecidableEq n] in
/-- Tensor products multiply slotwise. -/
theorem replicaOp_mul (r : ℕ) (A B : Fin r → Matrix n n ℂ) :
    replicaOp r A * replicaOp r B = replicaOp r fun i => A i * B i := by
  ext f g
  rw [Matrix.mul_apply]
  simp only [replicaOp_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset n))
    (fun i c => A i (f i) c * B i c (g i)), Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun h _ => Finset.prod_mul_distrib.symm

omit [Fintype n] [DecidableEq n] in
/-- Tensor products transpose slotwise. -/
theorem replicaOp_conjTranspose (r : ℕ) (A : Fin r → Matrix n n ℂ) :
    (replicaOp r A)ᴴ = replicaOp r fun i => (A i)ᴴ := by
  ext f g
  simp only [Matrix.conjTranspose_apply, replicaOp_apply]
  exact star_prod _ _

omit [Fintype n] [DecidableEq n] in
theorem replicaOp_eq_zero_of_factor {r : ℕ} (A : Fin r → Matrix n n ℂ) (i : Fin r)
    (hi : A i = 0) : replicaOp r A = 0 := by
  ext f g
  rw [replicaOp_apply]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [hi]
  rfl

omit [DecidableEq n] in
/-- **The product factorization of the replica expectation.** -/
theorem quadForm_replicaOp (r : ℕ) (A : Fin r → Matrix n n ℂ) (v : n → ℂ) :
    boundedReplicaThresholdProjectorQuadForm (replicaOp r A) (replicaVector r v) = ∏ i, boundedReplicaThresholdProjectorQuadForm (A i) v := by
  have hstep : ∀ i : Fin r, boundedReplicaThresholdProjectorQuadForm (A i) v = ∑ p, ∑ q, conj (v p) * A i p q * v q :=
    fun i => quadForm_eq_sum (A i) v
  simp only [hstep]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset n))
    (fun i p => ∑ q, conj (v p) * A i p q * v q), Fintype.piFinset_univ]
  rw [quadForm_eq_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset n))
    (fun i q => conj (v (f i)) * A i (f i) q * v q), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [replicaVector, replicaOp_apply, map_prod, ← Finset.prod_mul_distrib]

/-! ### The rank-one target projection -/

/-- The Hermitian pairing of two coordinate vectors. -/
def hermInner (z v : n → ℂ) : ℂ := ∑ p, conj (z p) * v p

/-- The rank-one orthogonal projection onto a unit vector. -/
def rankOne (z : n → ℂ) : Matrix n n ℂ := Matrix.of fun p q => z p * conj (z q)

omit [Fintype n] [DecidableEq n] in
theorem rankOne_apply (z : n → ℂ) (p q : n) : rankOne z p q = z p * conj (z q) := rfl

omit [DecidableEq n] in
theorem quadForm_rankOne (z v : n → ℂ) :
    boundedReplicaThresholdProjectorQuadForm (rankOne z) v = ((Complex.normSq (hermInner z v) : ℝ) : ℂ) := by
  rw [quadForm_eq_sum, Complex.normSq_eq_conj_mul_self]
  have hleft : conj (hermInner z v) = ∑ p, conj (v p) * z p := by
    simp only [hermInner, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hleft, hermInner, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [rankOne_apply]
  ring

theorem quadForm_one (v : n → ℂ) : boundedReplicaThresholdProjectorQuadForm (1 : Matrix n n ℂ) v = hermInner v v := by
  rw [quadForm_eq_sum, hermInner]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, ite_mul, zero_mul]

omit [Fintype n] [DecidableEq n] in
theorem rankOne_conjTranspose (z : n → ℂ) : (rankOne z)ᴴ = rankOne z := by
  ext p q
  simp only [Matrix.conjTranspose_apply, rankOne_apply, Complex.star_def, map_mul,
    Complex.conj_conj]
  ring

omit [DecidableEq n] in
theorem rankOne_mul_rankOne {z : n → ℂ} (hz : hermInner z z = 1) :
    rankOne z * rankOne z = rankOne z := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [rankOne_apply]
  have : ∑ c, z p * conj (z c) * (z c * conj (z q)) = z p * conj (z q) * ∑ c, conj (z c) * z c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [this, ← hermInner, hz, mul_one]

/-- The two complementary outcome operators at a single replica slot. -/
def outcomeFactor (z : n → ℂ) {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : Matrix n n ℂ :=
  if i ∈ S then rankOne z else 1 - rankOne z

omit [Fintype n] in
theorem outcomeFactor_conjTranspose (z : n → ℂ) {r : ℕ} (S : Finset (Fin r)) (i : Fin r) :
    (outcomeFactor z S i)ᴴ = outcomeFactor z S i := by
  unfold outcomeFactor
  split
  · exact rankOne_conjTranspose z
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, rankOne_conjTranspose]

theorem outcomeFactor_mul_self {z : n → ℂ} (hz : hermInner z z = 1) {r : ℕ}
    (S : Finset (Fin r)) (i : Fin r) :
    outcomeFactor z S i * outcomeFactor z S i = outcomeFactor z S i := by
  unfold outcomeFactor
  split
  · exact rankOne_mul_rankOne hz
  · rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    rw [rankOne_mul_rankOne hz]
    abel

theorem outcomeFactor_mul_of_ne {z : n → ℂ} (hz : hermInner z z = 1) {r : ℕ}
    {S T : Finset (Fin r)} {i : Fin r} (hi : (i ∈ S) ≠ (i ∈ T)) :
    outcomeFactor z S i * outcomeFactor z T i = 0 := by
  unfold outcomeFactor
  by_cases hS : i ∈ S
  · have hT : i ∉ T := fun h => hi (by simp [hS, h])
    rw [if_pos hS, if_neg hT, mul_sub, mul_one, rankOne_mul_rankOne hz, sub_self]
  · have hT : i ∈ T := by
      by_contra hT
      exact hi (by simp [hS, hT])
    rw [if_neg hS, if_pos hT, sub_mul, one_mul, rankOne_mul_rankOne hz, sub_self]

theorem quadForm_outcomeFactor {z v : n → ℂ} {r : ℕ} (S : Finset (Fin r)) (i : Fin r)
    (hv : hermInner v v = 1) :
    boundedReplicaThresholdProjectorQuadForm (outcomeFactor z S i) v
      = if i ∈ S then ((Complex.normSq (hermInner z v) : ℝ) : ℂ)
          else 1 - ((Complex.normSq (hermInner z v) : ℝ) : ℂ) := by
  unfold outcomeFactor
  split
  · exact quadForm_rankOne z v
  · rw [show (1 : Matrix n n ℂ) - rankOne z = (1 : Matrix n n ℂ) + (-1 : ℂ) • rankOne z by
        rw [neg_one_smul]; abel]
    rw [quadForm_add]
    have hsmul : boundedReplicaThresholdProjectorQuadForm ((-1 : ℂ) • rankOne z) v = -boundedReplicaThresholdProjectorQuadForm (rankOne z) v := by
      simp only [quadForm_eq_sum, Matrix.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hsmul, quadForm_one, hv, quadForm_rankOne]
    ring

/-! ### The bounded replica projector -/

/-- One outcome-string projection on the replica space. -/
def outcomeProjector (z : n → ℂ) (r : ℕ) (S : Finset (Fin r)) :
    Matrix (Fin r → n) (Fin r → n) ℂ := replicaOp r (outcomeFactor z S)

/-- The bounded replica threshold projector: the sum of all outcome strings with at least `k`
successes. -/
def boundedReplicaProjector (z : n → ℂ) (r k : ℕ) : Matrix (Fin r → n) (Fin r → n) ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin r))).filter fun S => k ≤ S.card,
    outcomeProjector z r S

omit [Fintype n] in
theorem outcomeProjector_conjTranspose (z : n → ℂ) (r : ℕ) (S : Finset (Fin r)) :
    (outcomeProjector z r S)ᴴ = outcomeProjector z r S := by
  unfold outcomeProjector
  rw [replicaOp_conjTranspose]
  congr 1
  funext i
  exact outcomeFactor_conjTranspose z S i

theorem outcomeProjector_mul_self {z : n → ℂ} (hz : hermInner z z = 1) (r : ℕ)
    (S : Finset (Fin r)) :
    outcomeProjector z r S * outcomeProjector z r S = outcomeProjector z r S := by
  unfold outcomeProjector
  rw [replicaOp_mul]
  congr 1
  funext i
  exact outcomeFactor_mul_self hz S i

theorem outcomeProjector_mul_of_ne {z : n → ℂ} (hz : hermInner z z = 1) (r : ℕ)
    {S T : Finset (Fin r)} (hST : S ≠ T) :
    outcomeProjector z r S * outcomeProjector z r T = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin r, (i ∈ S) ≠ (i ∈ T) := by
    by_contra hcon
    refine hST (Finset.ext fun i => ?_)
    have hi := not_exists.mp hcon i
    rw [not_ne_iff] at hi
    exact iff_of_eq hi
  unfold outcomeProjector
  rw [replicaOp_mul]
  exact replicaOp_eq_zero_of_factor _ i (outcomeFactor_mul_of_ne hz hi)

omit [Fintype n] in
/-- **Equation (20), self-adjointness.** -/
theorem boundedReplicaProjector_conjTranspose (z : n → ℂ) (r k : ℕ) :
    (boundedReplicaProjector z r k)ᴴ = boundedReplicaProjector z r k := by
  unfold boundedReplicaProjector
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun S _ => outcomeProjector_conjTranspose z r S

/-- **Equation (20), idempotence.** -/
theorem boundedReplicaProjector_mul_self {z : n → ℂ} (hz : hermInner z z = 1) (r k : ℕ) :
    boundedReplicaProjector z r k * boundedReplicaProjector z r k
      = boundedReplicaProjector z r k := by
  classical
  unfold boundedReplicaProjector
  rw [Finset.sum_mul_sum]
  refine (Finset.sum_congr rfl fun S _ => ?_).trans rfl
  rw [Finset.sum_eq_single S]
  · exact outcomeProjector_mul_self hz r S
  · intro T _ hTS
    exact outcomeProjector_mul_of_ne hz r (Ne.symm hTS)
  · intro hS
    exact absurd hS (by simp_all)

/-! ### The replica expectation identity -/

/-- The expectation of one outcome string in the replica state is the corresponding binomial
weight. -/
theorem quadForm_outcomeProjector {z v : n → ℂ} (hv : hermInner v v = 1) (r : ℕ)
    (S : Finset (Fin r)) :
    boundedReplicaThresholdProjectorQuadForm (outcomeProjector z r S) (replicaVector r v)
      = ((Complex.normSq (hermInner z v) : ℝ) : ℂ) ^ S.card
        * (1 - ((Complex.normSq (hermInner z v) : ℝ) : ℂ)) ^ (r - S.card) := by
  classical
  unfold outcomeProjector
  rw [quadForm_replicaOp]
  have hfac : ∀ i : Fin r, boundedReplicaThresholdProjectorQuadForm (outcomeFactor z S i) v
      = if i ∈ S then ((Complex.normSq (hermInner z v) : ℝ) : ℂ)
          else 1 - ((Complex.normSq (hermInner z v) : ℝ) : ℂ) :=
    fun i => quadForm_outcomeFactor S i hv
  simp only [hfac]
  rw [Finset.prod_ite]
  have h1 : (Finset.univ.filter fun i : Fin r => i ∈ S) = S := by
    ext i; simp
  have h2 : (Finset.univ.filter fun i : Fin r => i ∉ S) = Sᶜ := by
    ext i; simp
  rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_compl]
  simp

/-- **Equation (21).**  The bounded replica projector has expectation exactly the binomial tail
polynomial of the squared overlap. -/
theorem quadForm_boundedReplicaProjector {z v : n → ℂ}
    (hv : hermInner v v = 1) (r k : ℕ) :
    boundedReplicaThresholdProjectorQuadForm (boundedReplicaProjector z r k) (replicaVector r v)
      = ((binomialTail r k (Complex.normSq (hermInner z v)) : ℝ) : ℂ) := by
  classical
  set x : ℝ := Complex.normSq (hermInner z v) with hx
  unfold boundedReplicaProjector
  rw [quadForm_sum]
  have hterm : ∀ S ∈ (Finset.univ : Finset (Finset (Fin r))).filter fun S => k ≤ S.card,
      boundedReplicaThresholdProjectorQuadForm (outcomeProjector z r S) (replicaVector r v)
        = ((x : ℂ)) ^ S.card * (1 - (x : ℂ)) ^ (r - S.card) := by
    intro S _
    exact quadForm_outcomeProjector hv r S
  rw [Finset.sum_congr rfl hterm]
  have hmaps : ∀ S ∈ (Finset.univ : Finset (Finset (Fin r))).filter fun S => k ≤ S.card,
      S.card ∈ Finset.Icc k r := by
    intro S hS
    rw [Finset.mem_filter] at hS
    refine Finset.mem_Icc.mpr ⟨hS.2, ?_⟩
    simpa using Finset.card_le_card (Finset.subset_univ S)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun S => ((x : ℂ)) ^ S.card * (1 - (x : ℂ)) ^ (r - S.card))]
  have hfib : ∀ j ∈ Finset.Icc k r,
      (∑ S ∈ ((Finset.univ : Finset (Finset (Fin r))).filter fun S => k ≤ S.card) with
          S.card = j, ((x : ℂ)) ^ S.card * (1 - (x : ℂ)) ^ (r - S.card))
        = ((r.choose j : ℕ) : ℂ) * (x : ℂ) ^ j * (1 - (x : ℂ)) ^ (r - j) := by
    intro j hj
    obtain ⟨hkj, _⟩ := Finset.mem_Icc.mp hj
    have hset : (((Finset.univ : Finset (Finset (Fin r))).filter fun S => k ≤ S.card).filter
        fun S => S.card = j) = Finset.powersetCard j (Finset.univ : Finset (Fin r)) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · rintro h2; exact ⟨by omega, h2⟩
    rw [hset]
    have hconst : ∀ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin r)),
        ((x : ℂ)) ^ S.card * (1 - (x : ℂ)) ^ (r - S.card)
          = (x : ℂ) ^ j * (1 - (x : ℂ)) ^ (r - j) := by
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard]
    simp [nsmul_eq_mul, mul_assoc]
  rw [Finset.sum_congr rfl hfib]
  rw [binomialTail]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by unfold binomialTerm; push_cast; ring

/-! ### Positivity: the test is bounded between the zero and the identity observable -/

/-- **Equation (20), positivity.**  The expectation of the bounded replica projector in any state
is a nonnegative real. -/
theorem quadForm_boundedReplicaProjector_eq_normSq {z : n → ℂ} (hz : hermInner z z = 1)
    (r k : ℕ) (w : (Fin r → n) → ℂ) :
    boundedReplicaThresholdProjectorQuadForm (boundedReplicaProjector z r k) w
      = ((∑ c, Complex.normSq ((boundedReplicaProjector z r k *ᵥ w) c) : ℝ) : ℂ) := by
  have hherm : (boundedReplicaProjector z r k)ᴴ = boundedReplicaProjector z r k :=
    boundedReplicaProjector_conjTranspose z r k
  have hidem : boundedReplicaProjector z r k * boundedReplicaProjector z r k
      = boundedReplicaProjector z r k := boundedReplicaProjector_mul_self hz r k
  have key := quadForm_conjTranspose_mul (boundedReplicaProjector z r k) w
  rw [hherm, hidem] at key
  exact key

/-- **Equation (20), the upper bound.**  The complementary observable is also nonnegative, so the
bounded replica projector never exceeds the identity. -/
theorem quadForm_one_sub_boundedReplicaProjector_eq_normSq {z : n → ℂ} (hz : hermInner z z = 1)
    (r k : ℕ) (w : (Fin r → n) → ℂ) :
    boundedReplicaThresholdProjectorQuadForm (1 - boundedReplicaProjector z r k) w
      = ((∑ c, Complex.normSq (((1 - boundedReplicaProjector z r k) *ᵥ w) c) : ℝ) : ℂ) := by
  set Q := boundedReplicaProjector z r k with hQ
  have hherm : (1 - Q)ᴴ = 1 - Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ,
      boundedReplicaProjector_conjTranspose z r k]
  have hidem : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    rw [hQ, boundedReplicaProjector_mul_self hz r k]
    abel
  have key := quadForm_conjTranspose_mul (1 - Q) w
  rw [hherm, hidem] at key
  exact key

/-! ### The occupied-target maximum -/

/-- The bounded replica test of one target, as a real number. -/
def replicaTest (z v : n → ℂ) (r k : ℕ) : ℝ :=
  binomialTail r k (Complex.normSq (hermInner z v))

theorem quadForm_boundedReplicaProjector_eq_replicaTest {z v : n → ℂ}
    (hv : hermInner v v = 1) (r k : ℕ) :
    boundedReplicaThresholdProjectorQuadForm (boundedReplicaProjector z r k) (replicaVector r v)
      = ((replicaTest z v r k : ℝ) : ℂ) :=
  quadForm_boundedReplicaProjector hv r k

omit [DecidableEq n] in
theorem normSq_hermInner_nonneg (z v : n → ℂ) : 0 ≤ Complex.normSq (hermInner z v) :=
  Complex.normSq_nonneg _

/-- Cauchy–Schwarz in the product basis, obtained from the positivity of the complementary
rank-one projection. -/
theorem normSq_hermInner_le_one {z v : n → ℂ} (hz : hermInner z z = 1)
    (hv : hermInner v v = 1) : Complex.normSq (hermInner z v) ≤ 1 := by
  have hherm : ((1 : Matrix n n ℂ) - rankOne z)ᴴ = 1 - rankOne z := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, rankOne_conjTranspose]
  have hidem : ((1 : Matrix n n ℂ) - rankOne z) * (1 - rankOne z) = 1 - rankOne z := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    rw [rankOne_mul_rankOne hz]
    abel
  have hpos : boundedReplicaThresholdProjectorQuadForm ((1 : Matrix n n ℂ) - rankOne z) v
      = ((∑ c, Complex.normSq ((((1 : Matrix n n ℂ) - rankOne z) *ᵥ v) c) : ℝ) : ℂ) := by
    have key := quadForm_conjTranspose_mul ((1 : Matrix n n ℂ) - rankOne z) v
    rw [hherm, hidem] at key
    exact key
  have hval : boundedReplicaThresholdProjectorQuadForm ((1 : Matrix n n ℂ) - rankOne z) v
      = ((1 - Complex.normSq (hermInner z v) : ℝ) : ℂ) := by
    rw [show (1 : Matrix n n ℂ) - rankOne z = (1 : Matrix n n ℂ) + (-1 : ℂ) • rankOne z by
        rw [neg_one_smul]; abel, quadForm_add]
    have hsmul : boundedReplicaThresholdProjectorQuadForm ((-1 : ℂ) • rankOne z) v = -boundedReplicaThresholdProjectorQuadForm (rankOne z) v := by
      simp only [quadForm_eq_sum, Matrix.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hsmul, quadForm_one, hv, quadForm_rankOne]
    push_cast
    ring
  rw [hval] at hpos
  have hreal : (1 : ℝ) - Complex.normSq (hermInner z v)
      = ∑ c, Complex.normSq ((((1 : Matrix n n ℂ) - rankOne z) *ᵥ v) c) := by
    exact_mod_cast hpos
  have hnn : (0 : ℝ) ≤ ∑ c, Complex.normSq ((((1 : Matrix n n ℂ) - rankOne z) *ᵥ v) c) :=
    Finset.sum_nonneg fun c _ => Complex.normSq_nonneg _
  linarith

/-- **Equation (22).**  Maximizing over the occupied target set commutes with the bounded replica
test, because the binomial tail polynomial is monotone on `[0,1]`. -/
theorem sup'_replicaTest {Z : Finset (n → ℂ)} (hZ : Z.Nonempty) {v : n → ℂ}
    (hv : hermInner v v = 1) (hunit : ∀ z ∈ Z, hermInner z z = 1) (r k : ℕ) :
    Z.sup' hZ (fun z => replicaTest z v r k)
      = binomialTail r k (Z.sup' hZ fun z => Complex.normSq (hermInner z v)) := by
  have hle : ∀ z ∈ Z, Complex.normSq (hermInner z v)
      ≤ Z.sup' hZ fun z => Complex.normSq (hermInner z v) :=
    fun z hzZ => Finset.le_sup' (fun z => Complex.normSq (hermInner z v)) hzZ
  have hY0 : 0 ≤ Z.sup' hZ fun z => Complex.normSq (hermInner z v) := by
    obtain ⟨z, hzZ⟩ := hZ
    exact le_trans (Complex.normSq_nonneg _) (hle z hzZ)
  have hY1 : (Z.sup' hZ fun z => Complex.normSq (hermInner z v)) ≤ 1 :=
    Finset.sup'_le hZ _ fun z hzZ => normSq_hermInner_le_one (hunit z hzZ) hv
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le hZ _ fun z hzZ => ?_
    exact binomialTail_monotoneOn r k
      ⟨Complex.normSq_nonneg _, normSq_hermInner_le_one (hunit z hzZ) hv⟩ ⟨hY0, hY1⟩ (hle z hzZ)
  · obtain ⟨z, hzZ, hzeq⟩ := Finset.exists_mem_eq_sup' hZ fun z => Complex.normSq (hermInner z v)
    rw [hzeq]
    exact Finset.le_sup' (fun z => replicaTest z v r k) hzZ

end

end GaloisForLFunctions.HTGeometry
