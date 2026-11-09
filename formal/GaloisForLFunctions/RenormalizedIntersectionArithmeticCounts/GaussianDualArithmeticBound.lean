import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.GaussianSectionPositivity
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.WordProducts

/-!
# Integer representatives of the dual divisor lattice

Rounding the primitive normal coefficient embeds dual integer coordinates into an
ordinary integer lattice with a uniform quadratic norm bound. This compares Gaussian
tails without a loss in the exponential rate as the conductor grows.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

open ArithmeticDegenerationTheory HTGeometry.IntegerLatticePoisson

/-- Round the real normal coefficient of an integer vector. -/
def divisorNormalRound (N : ℕ) (v : Vertex N → ℤ) : ℤ :=
  round (divisorRealNormal N (fun i => (v i : ℝ)) / divisorSquarefreeCount N)

/-- An integral representative of the same tangential projection. -/
def divisorRoundedRepresentative (N : ℕ) (v : Vertex N → ℤ) : Vertex N → ℤ :=
  fun i => v i - divisorNormalRound N v * moebius i.val

private theorem normal_round_coordinate (a : ℝ) (v : ℤ) (n : ℕ) :
    (moebius n : ℝ)^2 * (a - (round a : ℝ))^2 ≤
      ((v : ℝ) - a * (moebius n : ℝ))^2 := by
  by_cases hz : moebius n = 0
  · simp only [hz, Int.cast_zero, zero_pow (by omega : 2 ≠ 0), zero_mul,
      mul_zero, sub_zero]
    exact sq_nonneg _
  have hr := pow_le_pow_left₀ (abs_nonneg (a - (round a : ℝ)))
    (round_le a (moebius n * v)) 2
  simp only [sq_abs, Int.cast_mul] at hr
  rcases moebius_ne_zero_iff_eq_or.mp hz with h | h
  · simp only [h, Int.cast_one, one_pow, one_mul, mul_one] at hr ⊢
    nlinarith only [hr]
  · simp only [h, Int.cast_neg, Int.cast_one, neg_one_sq, one_mul, neg_mul, mul_neg,
      mul_one, sub_neg_eq_add] at hr ⊢
    nlinarith only [hr]

private theorem divisor_rounding_variance (N : ℕ) (v : Vertex N → ℤ) :
    (divisorSquarefreeCount N : ℝ) *
      (divisorRealNormal N (fun i => (v i : ℝ)) / divisorSquarefreeCount N -
        (divisorNormalRound N v : ℝ))^2 ≤
      divisorEuclideanSq N (divisorRelationProjection N (fun i => (v i : ℝ))) := by
  have hsum : (∑ i : Vertex N, (moebius i.val : ℝ)^2) =
      (divisorSquarefreeCount N : ℝ) := divisorNormalVector_square_sum N
  calc
    _ = (∑ i : Vertex N, (moebius i.val : ℝ)^2) *
        (divisorRealNormal N (fun i => (v i : ℝ)) / divisorSquarefreeCount N -
          (divisorNormalRound N v : ℝ))^2 := by rw [hsum]
    _ ≤ _ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun (i : Vertex N) _ =>
        normal_round_coordinate (divisorRealNormal N (fun j => (v j : ℝ)) /
          divisorSquarefreeCount N) (v i) i.val

private theorem divisor_sq_add_normal (N : ℕ) (v : Vertex N → ℝ) (a : ℝ) :
    divisorEuclideanSq N (v + a • divisorNormalVector N) =
      divisorEuclideanSq N v + 2*a*divisorRealNormal N v +
        (divisorSquarefreeCount N : ℝ)*a^2 := by
  rw [← divisorNormalVector_square_sum N]
  change (∑ i, (v i + a * divisorNormalVector N i)^2) =
    (∑ i, (v i)^2) + 2*a*(∑ i, (moebius i.val : ℝ)*v i) +
      (∑ i, (divisorNormalVector N i)^2)*a^2
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by dsimp only [divisorNormalVector]; ring

/-- Rounding loses at most a factor of two in the squared tangential norm. -/
theorem divisorRoundedRepresentative_sq_le (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℤ) :
    divisorEuclideanSq N (fun i => (divisorRoundedRepresentative N v i : ℝ)) ≤
      2 * divisorEuclideanSq N (divisorRelationProjection N (fun i => (v i : ℝ))) := by
  have hp : divisorRealNormal N (divisorRelationProjection N (fun i => (v i : ℝ))) = 0 :=
    (mem_divisorRelationRealSpace_iff N hN _).mp (divisorRelationProjection_mem N hN _)
  have hv : (fun i => (divisorRoundedRepresentative N v i : ℝ)) =
      divisorRelationProjection N (fun i => (v i : ℝ)) +
        (divisorRealNormal N (fun i => (v i : ℝ)) / divisorSquarefreeCount N -
          (divisorNormalRound N v : ℝ)) • divisorNormalVector N := by
    funext i
    simp only [divisorRoundedRepresentative, Int.cast_sub, Int.cast_mul,
      divisorRelationProjection, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      divisorNormalVector]
    ring
  rw [hv, divisor_sq_add_normal, hp, mul_zero, add_zero]
  linarith only [divisor_rounding_variance N v]

/-- Remove the pole coordinate before taking the tangential dual vector. -/
def divisorDualNonPole (N : ℕ) (hN : 1 ≤ N) (m : Vertex N → ℤ) : Vertex N → ℤ :=
  m - Pi.single (poleVertex N hN) (m (poleVertex N hN))

/-- Integer coding of dual coordinates by their normal integer and a short representative. -/
def divisorDualIntegerEmbedding (N : ℕ) (hN : 1 ≤ N) (m : Vertex N → ℤ) :
    ℤ × (Vertex N → ℤ) :=
  (m (poleVertex N hN), divisorRoundedRepresentative N (divisorDualNonPole N hN m))

/-- The pole entry of the rounded representative records the subtracted multiple of the normal. -/
theorem divisorDualIntegerEmbedding_recover (N : ℕ) (hN : 1 ≤ N) (m : Vertex N → ℤ)
    (i : Vertex N) :
    (divisorDualIntegerEmbedding N hN m).2 i -
      (divisorDualIntegerEmbedding N hN m).2 (poleVertex N hN) * moebius i.val +
        (Pi.single (poleVertex N hN) ((divisorDualIntegerEmbedding N hN m).1) :
          Vertex N → ℤ) i = m i := by
  simp only [divisorDualIntegerEmbedding, divisorRoundedRepresentative, divisorDualNonPole,
    Pi.sub_apply, Pi.single_eq_same, sub_self, poleVertex, moebius_apply_one, mul_one]
  ring

theorem divisorDualIntegerEmbedding_injective (N : ℕ) (hN : 1 ≤ N) :
    Function.Injective (divisorDualIntegerEmbedding N hN) := by
  intro m n he
  funext i
  rw [← divisorDualIntegerEmbedding_recover N hN m i,
    ← divisorDualIntegerEmbedding_recover N hN n i, he]

theorem divisorDualIntegerEmbedding_zero (N : ℕ) (hN : 1 ≤ N) :
    divisorDualIntegerEmbedding N hN 0 = (0, 0) := by
  apply Prod.ext
  · rfl
  · funext i
    simp [divisorDualIntegerEmbedding, divisorDualNonPole, divisorRoundedRepresentative,
      divisorNormalRound, divisorRealNormal]

private theorem divisorEuclidean_inner (N : ℕ) (x y : EuclideanSpace ℝ (Vertex N)) :
    inner ℝ x y = ∑ i, x i * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.star_apply, star_trivial]; ring

/-- The actual dual lattice splits orthogonally into an integer normal and a projected integer vector. -/
theorem divisorGaussianDual_apply (N : ℕ) (hN : 1 ≤ N) (m : Vertex N → ℤ) :
    inverseAdjoint (divisorGaussianLattice N hN) (euclideanIntegerPoint m) =
      WithLp.toLp 2 ((m (poleVertex N hN) : ℝ) • divisorNormalVector N +
        divisorRelationProjection N (fun i => (divisorDualNonPole N hN m i : ℝ))) := by
  apply ext_inner_right ℝ
  intro x
  rw [inverseAdjoint, ContinuousLinearMap.adjoint_inner_left,
    divisorEuclidean_inner, divisorEuclidean_inner]
  have hn : divisorRealNormal N (fun i => (divisorDualNonPole N hN m i : ℝ)) =
      divisorRealNormal N (fun i => (m i : ℝ)) - (m (poleVertex N hN) : ℝ) := by
    change (∑ i : Vertex N, (moebius i.val : ℝ) *
      (divisorDualNonPole N hN m i : ℝ)) = _
    simp only [divisorDualNonPole, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [Pi.single_apply, apply_ite (fun z : ℤ => (z : ℝ)), Int.cast_zero,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      poleVertex, moebius_apply_one, Int.cast_one, one_mul]
  change (∑ i, (m i : ℝ) *
    (x i - (divisorRealNormal N x.ofLp / divisorSquarefreeCount N) *
      divisorNormalVector N i +
      (divisorRealNormal N x.ofLp - x (poleVertex N hN) +
        divisorRealNormal N x.ofLp / divisorSquarefreeCount N) *
          (Pi.single (poleVertex N hN) (1 : ℝ) : Vertex N → ℝ) i)) =
    ∑ i, ((m (poleVertex N hN) : ℝ) * divisorNormalVector N i +
      ((divisorDualNonPole N hN m i : ℝ) -
        (divisorRealNormal N (fun j => (divisorDualNonPole N hN m j : ℝ)) /
          divisorSquarefreeCount N) * divisorNormalVector N i)) * x i
  rw [hn]
  simp only [divisorDualNonPole, Pi.sub_apply, Int.cast_sub, mul_add, mul_sub,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hm (r : ℝ) : (∑ i, (m i : ℝ) * (r * divisorNormalVector N i)) =
      r * divisorRealNormal N (fun i => (m i : ℝ)) := by
    change (∑ i, (m i : ℝ) * (r * (moebius i.val : ℝ))) =
      r * ∑ i, (moebius i.val : ℝ) * (m i : ℝ)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hx (r : ℝ) : (∑ i, r * divisorNormalVector N i * x i) =
      r * divisorRealNormal N x.ofLp := by
    change (∑ i, r * (moebius i.val : ℝ) * x i) =
      r * ∑ i, (moebius i.val : ℝ) * x i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hm, hx, hx]
  simp only [Pi.single_apply, apply_ite (fun z : ℤ => (z : ℝ)), Int.cast_zero,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

/-- The normal and tangential squared lengths are exactly additive in the dual lattice. -/
theorem divisorGaussianDual_norm_sq (N : ℕ) (hN : 1 ≤ N) (m : Vertex N → ℤ) :
    ‖inverseAdjoint (divisorGaussianLattice N hN) (euclideanIntegerPoint m)‖^2 =
      (divisorSquarefreeCount N : ℝ) * (m (poleVertex N hN) : ℝ)^2 +
        divisorEuclideanSq N (divisorRelationProjection N
          (fun i => (divisorDualNonPole N hN m i : ℝ))) := by
  rw [divisorGaussianDual_apply, EuclideanSpace.real_norm_sq_eq]
  change divisorEuclideanSq N (_ + _) = _
  rw [add_comm, divisor_sq_add_normal,
    (mem_divisorRelationRealSpace_iff N hN _).mp (divisorRelationProjection_mem N hN _),
    mul_zero, add_zero, add_comm]

/-- The integer coding has a dimension-independent squared-norm distortion of at most two. -/
theorem divisorDualIntegerEmbedding_sq_le (N : ℕ) (hN : 1 ≤ N) (m : Vertex N → ℤ) :
    ((divisorDualIntegerEmbedding N hN m).1 : ℝ)^2 +
      divisorEuclideanSq N (fun i => ((divisorDualIntegerEmbedding N hN m).2 i : ℝ)) ≤
        2 * ‖inverseAdjoint (divisorGaussianLattice N hN) (euclideanIntegerPoint m)‖^2 := by
  rw [divisorGaussianDual_norm_sq]
  have hr := divisorRoundedRepresentative_sq_le N hN (divisorDualNonPole N hN m)
  have hq : (1 : ℝ) ≤ divisorSquarefreeCount N := by
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have hm := sq_nonneg (m (poleVertex N hN) : ℝ)
  have hqm := mul_le_mul_of_nonneg_right hq hm
  change (m (poleVertex N hN) : ℝ)^2 +
    divisorEuclideanSq N (fun i =>
      (divisorRoundedRepresentative N (divisorDualNonPole N hN m) i : ℝ)) ≤ _
  nlinarith only [hr, hm, hqm]

/-- The Gaussian count on one unrestricted integer coordinate. -/
def divisorScalarTheta (a : ℝ) : ℝ := ∑' z : ℤ, Real.exp (-a*(z : ℝ)^2)

private theorem summable_divisorScalarTheta {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ => Real.exp (-a*(z : ℝ)^2)) := by
  simpa only [pow_zero, one_mul] using
    summable_one_add_natAbs_pow_mul_exp_neg_int_sq 0 ha

/-- The unrestricted arithmetic count factors over its actual integer coordinates. -/
theorem divisorAmbientTheta_eq_scalar (N : ℕ) {a : ℝ} (ha : 0 < a) :
    divisorAmbientTheta N a = divisorScalarTheta a ^ N := by
  let e := Fintype.equivFin (Vertex N)
  let e' : (Vertex N → ℤ) ≃ (Fin (Fintype.card (Vertex N)) → ℤ) :=
    { toFun v j := v (e.symm j)
      invFun v i := v (e i)
      left_inv v := by funext i; simp
      right_inv v := by funext j; simp }
  have hs := (SymmetricCharacters.wordProducts_summable_and_tsum
    (summable_divisorScalarTheta ha) (fun _ => (Real.exp_pos _).le)
      (Fintype.card (Vertex N))).2
  have hc : Fintype.card (Vertex N) = N := by simp [Vertex]
  refine Eq.trans ?_ (congrArg (fun d : ℕ => divisorScalarTheta a ^ d) hc)
  change (∑' v, divisorGaussianWeight N a v) = _
  rw [divisorScalarTheta, ← hs, ← e'.tsum_eq]
  apply tsum_congr
  intro v
  change divisorGaussianWeight N a v =
    ∏ j : Fin (Fintype.card (Vertex N)), Real.exp (-a*(v (e.symm j) : ℝ)^2)
  rw [Fintype.prod_equiv e.symm
    (fun j => Real.exp (-a*(v (e.symm j) : ℝ)^2))
    (fun i => Real.exp (-a*(v i : ℝ)^2)) (fun _ => rfl)]
  rw [divisorGaussianWeight, divisorSectionEnergy_real, ← Real.exp_sum, ← Finset.mul_sum]

private theorem divisorGaussianDual_weight_le (N : ℕ) (hN : 1 ≤ N)
  {a : ℝ} (ha : 0 < a) (m : Vertex N → ℤ) :
    Real.exp (-a*‖inverseAdjoint (divisorGaussianLattice N hN) (euclideanIntegerPoint m)‖^2) ≤
      Real.exp (-(a/2)*((divisorDualIntegerEmbedding N hN m).1 : ℝ)^2) *
        divisorGaussianWeight N (a/2) (divisorDualIntegerEmbedding N hN m).2 := by
  rw [divisorGaussianWeight, divisorSectionEnergy_real, ← Real.exp_add, Real.exp_le_exp]
  have hb := mul_le_mul_of_nonneg_left (divisorDualIntegerEmbedding_sq_le N hN m)
    (half_pos ha).le
  change (a/2)*(_ + ∑ i, ((divisorDualIntegerEmbedding N hN m).2 i : ℝ)^2) ≤ _ at hb
  nlinarith only [hb]

/-- All dual Gaussian samples are bounded by an independent product of integer counts. -/
theorem divisorGaussianDual_theta_le (N : ℕ) (hN : 1 ≤ N) {a : ℝ} (ha : 0 < a) :
    gaussianLatticeSum (inverseAdjointEquiv (divisorGaussianLattice N hN)) a ≤
      divisorScalarTheta (a/2) ^ (N+1) := by
  let f : ℤ → ℝ := fun z => Real.exp (-(a/2)*(z : ℝ)^2)
  let g : (Vertex N → ℤ) → ℝ := divisorGaussianWeight N (a/2)
  have hf : Summable f := summable_divisorScalarTheta (half_pos ha)
  have hg : Summable g := summable_divisorGaussianWeight N (half_pos ha)
  have hs : Summable (fun z : ℤ × (Vertex N → ℤ) => f z.1 * g z.2) :=
    hf.mul_of_nonneg hg (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hm := tsum_comp_le_tsum_of_inj hs (fun z => mul_nonneg (Real.exp_pos _).le
    (Real.exp_pos _).le) (i := divisorDualIntegerEmbedding N hN)
      (divisorDualIntegerEmbedding_injective N hN)
  have hmul := hf.tsum_mul_tsum hg hs
  have hdual : Summable (fun m : Vertex N → ℤ =>
      Real.exp (-a*‖inverseAdjoint (divisorGaussianLattice N hN) (euclideanIntegerPoint m)‖^2)) := by
    simpa only [inverseAdjointEquiv_apply] using
      summable_gaussianLatticeSum (inverseAdjointEquiv (divisorGaussianLattice N hN)) ha
  have hcomp : Summable (fun m : Vertex N → ℤ =>
      f (divisorDualIntegerEmbedding N hN m).1 * g (divisorDualIntegerEmbedding N hN m).2) :=
    hs.comp_injective (divisorDualIntegerEmbedding_injective N hN)
  calc
    _ ≤ ∑' m : Vertex N → ℤ,
        Real.exp (-(a/2)*((divisorDualIntegerEmbedding N hN m).1 : ℝ)^2) *
          divisorGaussianWeight N (a/2) (divisorDualIntegerEmbedding N hN m).2 :=
      hdual.tsum_le_tsum (divisorGaussianDual_weight_le N hN ha) hcomp
    _ ≤ ∑' zm : ℤ × (Vertex N → ℤ),
        Real.exp (-(a/2)*(zm.1 : ℝ)^2) * divisorGaussianWeight N (a/2) zm.2 := hm
    _ = divisorScalarTheta (a/2) * divisorAmbientTheta N (a/2) := hmul.symm
    _ = _ := by rw [divisorAmbientTheta_eq_scalar N (half_pos ha), pow_succ]; ring

#print axioms divisorRoundedRepresentative_sq_le
#print axioms divisorDualIntegerEmbedding_injective
#print axioms divisorDualIntegerEmbedding_zero
#print axioms divisorGaussianDual_apply
#print axioms divisorGaussianDual_norm_sq
#print axioms divisorDualIntegerEmbedding_sq_le
#print axioms divisorAmbientTheta_eq_scalar
#print axioms divisorGaussianDual_theta_le

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
