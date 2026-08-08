import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import GaloisForLFunctions.HTGeometry.KrylovCausalReplicaSieveLaw
import GaloisForLFunctions.HTGeometry.ProjectedReplicaReturnExcisionLaw
import GaloisForLFunctions.HTGeometry.GaussianAngularPolarDisintegrationLaw

/-!
# Krylov projected complete-incidence law

This module proves the sharp causal boundary used by projection-before-replica
incidence.  For every skew-adjoint element of a C-star algebra, its exponential
is approximated by the degree-`K` Taylor section with the exact factorial
remainder and no exponential loss.  The proof is dimension-free and uses only
unitarity of the real-time exponential.

For a bounded self-adjoint Hamiltonian on a finite-dimensional Hilbert space,
the Taylor state lies in the ordinary power Krylov subspace.  Best
approximation by its orthogonal projector therefore inherits the same sharp
factorial boundary.  No spectral gap, eigenvalue independence, or asymptotic
limit is assumed.
-/

open Set NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A]

/-- Banach-valued integral Taylor remainder with the exact factorial. -/
theorem norm_sub_taylorWithinEval_le_factorial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {K : ℕ} {C t : ℝ}
    (ht : 0 ≤ t)
    (hf : ContDiffOn ℝ (K + 1) f (Icc 0 t))
    (hC : ∀ y ∈ Icc 0 t,
      ‖iteratedDerivWithin (K + 1) f (Icc 0 t) y‖ ≤ C) :
    ‖f t - taylorWithinEval f K (Icc 0 t) 0 t‖ ≤
      C * t ^ (K + 1) / (K + 1).factorial := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hrem := taylor_integral_remainder (n := K) (x := t) (x₀ := 0) (by
    simpa [uIcc_of_le ht.le] using hf)
  rw [uIcc_of_le ht.le] at hrem
  rw [hrem]
  have hcontDeriv : ContinuousOn
      (fun y => iteratedDerivWithin (K + 1) f (Icc 0 t) y) (Icc 0 t) :=
    hf.continuousOn_iteratedDerivWithin rfl.le
      (uniqueDiffOn_Icc ht)
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) ht.le
    (f := fun y => ((t - y) ^ K / K.factorial) •
      iteratedDerivWithin (K + 1) f (Icc 0 t) y)
  have hmono :
      (∫ y in (0 : ℝ)..t,
          ‖((t - y) ^ K / K.factorial) •
            iteratedDerivWithin (K + 1) f (Icc 0 t) y‖) ≤
        ∫ y in (0 : ℝ)..t, C * (t - y) ^ K / K.factorial := by
    apply intervalIntegral.integral_mono_on ht.le
    · have hscalar : Continuous
          (fun y : ℝ => (t - y) ^ K / (K.factorial : ℝ)) := by
        fun_prop
      have hc : ContinuousOn
          (fun u => ‖((t - u) ^ K / (K.factorial : ℝ)) •
            iteratedDerivWithin (K + 1) f (Icc 0 t) u‖) (uIcc 0 t) := by
        simpa [uIcc_of_le ht.le] using
          (hscalar.continuousOn.smul hcontDeriv).norm
      exact hc.intervalIntegrable
    · exact ((continuous_const.mul ((continuous_const.sub continuous_id).pow K)).div_const
        (K.factorial : ℝ)).intervalIntegrable 0 t
    · intro y hy
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      · calc
          (t - y) ^ K / (K.factorial : ℝ) *
              ‖iteratedDerivWithin (K + 1) f (Icc 0 t) y‖
              ≤ (t - y) ^ K / (K.factorial : ℝ) * C :=
            mul_le_mul_of_nonneg_left (hC y hy)
              (div_nonneg (pow_nonneg (sub_nonneg.mpr hy.2) K) (by positivity))
          _ = C * (t - y) ^ K / (K.factorial : ℝ) := by ring
      · exact div_nonneg (pow_nonneg (sub_nonneg.mpr hy.2) K) (by positivity)
  have hmodel :
      (∫ y in (0 : ℝ)..t, C * (t - y) ^ K / K.factorial) =
        C * t ^ (K + 1) / (K + 1).factorial := by
    calc
      (∫ y in (0 : ℝ)..t, C * (t - y) ^ K / K.factorial) =
          ∫ y in (0 : ℝ)..t, (C / (K.factorial : ℝ)) * (t - y) ^ K := by
            apply intervalIntegral.integral_congr
            intro y hy
            ring
      _ = (C / (K.factorial : ℝ)) * ∫ y in (0 : ℝ)..t, (t - y) ^ K := by
            rw [intervalIntegral.integral_const_mul]
      _ = C * t ^ (K + 1) / (K + 1).factorial := by
            rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ K) t]
            rw [sub_self, sub_zero, integral_pow, Nat.factorial_succ]
            push_cast
            field_simp
            simp
  linarith

/-- Exact iterated derivative of a one-parameter algebra exponential. -/
theorem iteratedDeriv_exp_real_smul (x : A) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => exp (t • x)) =
      fun t : ℝ => x ^ n * exp (t • x) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) x t).const_mul (x ^ n)
      simpa [pow_succ, mul_assoc] using h.deriv

/-- Every finite differentiability order of the real algebra exponential. -/
theorem contDiff_exp_real_smul (x : A) (N : ℕ) :
    ContDiff ℝ N (fun t : ℝ => exp (t • x)) := by
  exact contDiff_of_differentiable_iteratedDeriv
    (f := fun t : ℝ => exp (t • x)) (n := N) fun n hn => by
    rw [iteratedDeriv_exp_real_smul]
    exact (differentiable_const (c := x ^ n)).mul
      (fun t : ℝ => (hasDerivAt_exp_smul_const' x t).differentiableAt)

/-- Degree-`K` Taylor section of a real one-parameter algebra exponential. -/
def cstarExponentialTaylor (x : A) (K : ℕ) (t : ℝ) : A :=
  ∑ k ∈ Finset.range (K + 1),
    (t ^ k / (k.factorial : ℝ)) • x ^ k

theorem taylorWithinEval_exp_real_smul_eq
    (x : A) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    taylorWithinEval (fun s : ℝ => exp (s • x)) K
        (Icc 0 t) 0 t = cstarExponentialTaylor x K t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [taylorWithinEval_self]
    simp only [zero_smul, exp_zero]
    unfold cstarExponentialTaylor
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      rw [zero_pow hk0, zero_div, zero_smul]
    · simp
  rw [taylor_within_apply]
  unfold cstarExponentialTaylor
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_exp_real_smul x k).contDiffAt) (left_mem_Icc.mpr ht.le)]
  rw [congrFun (iteratedDeriv_exp_real_smul x k) 0]
  simp only [sub_zero, zero_smul, exp_zero, mul_one]
  congr 1
  field_simp

/-- Sharp factorial remainder for nonnegative time and a skew-adjoint generator. -/
theorem norm_exp_sub_cstarExponentialTaylor_le_of_nonneg
    (x : A) (hx : x ∈ skewAdjoint A) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • x) - cstarExponentialTaylor x K t‖ ≤
      ‖x‖ ^ (K + 1) * t ^ (K + 1) / (K + 1).factorial := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [← taylorWithinEval_exp_real_smul_eq x K (t := 0) le_rfl]
    simp
  rw [← taylorWithinEval_exp_real_smul_eq x K ht.le]
  apply norm_sub_taylorWithinEval_le_factorial ht.le
    ((contDiff_exp_real_smul x (K + 1)).contDiffOn)
  intro y hy
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_exp_real_smul x (K + 1)).contDiffAt) hy]
  rw [congrFun (iteratedDeriv_exp_real_smul x (K + 1)) y]
  rw [CStarRing.norm_mul_mem_unitary _
    (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem y hx))]
  exact norm_pow_le' _ (Nat.succ_pos _)

theorem cstarExponentialTaylor_neg_neg (x : A) (K : ℕ) (t : ℝ) :
    cstarExponentialTaylor (-x) K (-t) = cstarExponentialTaylor x K t := by
  unfold cstarExponentialTaylor
  apply Finset.sum_congr rfl
  intro k hk
  by_cases heven : Even k
  · rw [heven.neg_pow t, heven.neg_pow x]
  · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
    rw [hodd.neg_pow t, hodd.neg_pow x]
    have hcoeff : -t ^ k / (k.factorial : ℝ) =
        -(t ^ k / (k.factorial : ℝ)) := by ring
    rw [hcoeff, neg_smul, smul_neg, neg_neg]

/-- Sharp factorial remainder at every real time. -/
theorem norm_exp_sub_cstarExponentialTaylor_le
    (x : A) (hx : x ∈ skewAdjoint A) (K : ℕ) (t : ℝ) :
    ‖exp (t • x) - cstarExponentialTaylor x K t‖ ≤
      ‖x‖ ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using
      norm_exp_sub_cstarExponentialTaylor_le_of_nonneg x hx K ht
  · have htneg : t < 0 := lt_of_not_ge ht
    have hnegx : -x ∈ skewAdjoint A := (skewAdjoint A).neg_mem hx
    have h := norm_exp_sub_cstarExponentialTaylor_le_of_nonneg
      (-x) hnegx K (t := -t) (by linarith)
    simpa [neg_smul, smul_neg, cstarExponentialTaylor_neg_neg,
      abs_of_neg htneg] using h

/-- Hamiltonian Taylor section generated by `-iH`. -/
def selfAdjointHamiltonianTaylor (H : A) (K : ℕ) (t : ℝ) : A :=
  cstarExponentialTaylor ((-Complex.I) • H) K t

/-- Sharp operator-norm Hamiltonian Taylor boundary. -/
theorem norm_selfAdjoint_exp_sub_hamiltonianTaylor_le
    (H : A) (hH : IsSelfAdjoint H) (K : ℕ) (t : ℝ) :
    ‖exp (t • ((-Complex.I) • H)) -
        selfAdjointHamiltonianTaylor H K t‖ ≤
      ‖H‖ ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
  have hskew : (-Complex.I) • H ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]
    simp
  simpa [selfAdjointHamiltonianTaylor, norm_smul] using
    norm_exp_sub_cstarExponentialTaylor_le ((-Complex.I) • H) hskew K t

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Real-time orbit of a bounded Hamiltonian. -/
def boundedHamiltonianOrbit (H : E →L[ℂ] E) (ψ : E) (t : ℝ) : E :=
  exp (t • ((-Complex.I) • H)) ψ

/-- Self-adjoint real-time evolution preserves the state norm exactly. -/
theorem norm_boundedHamiltonianOrbit_eq
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (ψ : E) (t : ℝ) :
    ‖boundedHamiltonianOrbit H ψ t‖ = ‖ψ‖ := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  have hskew : (-Complex.I) • H ∈ skewAdjoint (E →L[ℂ] E) := by
    rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]
    simp
  unfold boundedHamiltonianOrbit
  exact (exp (t • ((-Complex.I) • H))).norm_map_of_mem_unitary
    (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hskew)) ψ

/-- Taylor state of the same bounded Hamiltonian orbit. -/
def boundedHamiltonianTaylorState
    (H : E →L[ℂ] E) (ψ : E) (K : ℕ) (t : ℝ) : E :=
  selfAdjointHamiltonianTaylor H K t ψ

/-- Ordinary degree-`K` power Krylov subspace. -/
def boundedHamiltonianKrylovSubspace
    (H : E →L[ℂ] E) (ψ : E) (K : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (Set.range fun k : Fin (K + 1) => (H ^ (k : ℕ)) ψ)

omit [CompleteSpace E] in
theorem boundedHamiltonianKrylovPower_mem
    (H : E →L[ℂ] E) (ψ : E) {K k : ℕ} (hk : k ≤ K) :
    (H ^ k) ψ ∈ boundedHamiltonianKrylovSubspace H ψ K := by
  apply Submodule.subset_span
  exact ⟨⟨k, Nat.lt_succ_iff.mpr hk⟩, rfl⟩

/-- The Hamiltonian Taylor state is an explicit combination of power-orbit vectors. -/
theorem boundedHamiltonianTaylorState_eq_sum
    (H : E →L[ℂ] E) (ψ : E) (K : ℕ) (t : ℝ) :
    boundedHamiltonianTaylorState H ψ K t =
      ∑ k ∈ Finset.range (K + 1),
        (((t ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * (-Complex.I) ^ k) •
          ((H ^ k) ψ) := by
  unfold boundedHamiltonianTaylorState selfAdjointHamiltonianTaylor
    cstarExponentialTaylor
  have happly :
      (∑ k ∈ Finset.range (K + 1),
        (t ^ k / (k.factorial : ℝ)) • ((-Complex.I) • H) ^ k) ψ =
      ∑ k ∈ Finset.range (K + 1),
        ((t ^ k / (k.factorial : ℝ)) • ((-Complex.I) • H) ^ k) ψ := by
    let f : ℕ → E →L[ℂ] E := fun k =>
      (t ^ k / (k.factorial : ℝ)) • ((-Complex.I) • H) ^ k
    have hsum (s : Finset ℕ) : (∑ k ∈ s, f k) ψ = ∑ k ∈ s, f k ψ := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [ha, ih]
    exact hsum (Finset.range (K + 1))
  rw [happly]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_pow]
  simp only [smul_apply, mul_smul]
  norm_cast

/-- The Taylor state lies in the ordinary Hamiltonian Krylov subspace. -/
theorem boundedHamiltonianTaylorState_mem_krylov
    (H : E →L[ℂ] E) (ψ : E) (K : ℕ) (t : ℝ) :
    boundedHamiltonianTaylorState H ψ K t ∈
      boundedHamiltonianKrylovSubspace H ψ K := by
  rw [boundedHamiltonianTaylorState_eq_sum]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact boundedHamiltonianKrylovPower_mem H ψ
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- State-level sharp Taylor boundary for every unit-bounded initial state. -/
theorem norm_boundedHamiltonianOrbit_sub_taylorState_le
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) {ψ : E} (hψ : ‖ψ‖ ≤ 1)
    (K : ℕ) (t : ℝ) :
    ‖boundedHamiltonianOrbit H ψ t - boundedHamiltonianTaylorState H ψ K t‖ ≤
      ‖H‖ ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
  let D := exp (t • ((-Complex.I) • H)) -
    selfAdjointHamiltonianTaylor H K t
  have hD := ContinuousLinearMap.le_opNorm D ψ
  have hrem := norm_selfAdjoint_exp_sub_hamiltonianTaylor_le H hH K t
  change ‖D ψ‖ ≤ _
  calc
    ‖D ψ‖ ≤ ‖D‖ * ‖ψ‖ := hD
    _ ≤ ‖D‖ * 1 := mul_le_mul_of_nonneg_left hψ (norm_nonneg D)
    _ = ‖D‖ := mul_one _
    _ ≤ _ := hrem

omit [CompleteSpace E] in
theorem norm_sub_starProjection_le_of_mem
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (y : E) {v : E} (hv : v ∈ U) :
    ‖y - U.starProjection y‖ ≤ ‖y - v‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
    (⟨v, hv⟩ : U)

section FiniteDimensional

variable [FiniteDimensional ℂ E]

/-- Orthogonal projection of the orbit onto its degree-`K` Krylov carrier. -/
def boundedHamiltonianKrylovProjection
    (H : E →L[ℂ] E) (ψ : E) (K : ℕ) (t : ℝ) : E :=
  (boundedHamiltonianKrylovSubspace H ψ K).starProjection
    (boundedHamiltonianOrbit H ψ t)

/-- Best Krylov approximation inherits the sharp Hamiltonian Taylor boundary. -/
theorem norm_boundedHamiltonianOrbit_sub_krylovProjection_le
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) {ψ : E} (hψ : ‖ψ‖ ≤ 1)
    (K : ℕ) (t : ℝ) :
    ‖boundedHamiltonianOrbit H ψ t -
        boundedHamiltonianKrylovProjection H ψ K t‖ ≤
      ‖H‖ ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
  exact (norm_sub_starProjection_le_of_mem
    (boundedHamiltonianKrylovSubspace H ψ K)
    (boundedHamiltonianOrbit H ψ t)
    (boundedHamiltonianTaylorState_mem_krylov H ψ K t)).trans
      (norm_boundedHamiltonianOrbit_sub_taylorState_le H hH hψ K t)

/-- Uniform factorial boundary on a norm/time window. -/
def krylovFactorialBoundary (B T : ℝ) (K : ℕ) : ℝ :=
  (B * T) ^ (K + 1) / (K + 1).factorial

/-- Exact paper boundary `eta_K(T)` for `‖H‖ ≤ B` and `|t| ≤ T`. -/
theorem norm_boundedHamiltonianOrbit_sub_krylovProjection_le_boundary
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) {ψ : E} (hψ : ‖ψ‖ ≤ 1)
    (K : ℕ) {B T t : ℝ} (hB : 0 ≤ B) (hHnorm : ‖H‖ ≤ B)
    (ht : |t| ≤ T) :
    ‖boundedHamiltonianOrbit H ψ t -
        boundedHamiltonianKrylovProjection H ψ K t‖ ≤
      krylovFactorialBoundary B T K := by
  have hprod : ‖H‖ * |t| ≤ B * T :=
    mul_le_mul hHnorm ht (abs_nonneg t) hB
  have hpow := pow_le_pow_left₀ (mul_nonneg (norm_nonneg H) (abs_nonneg t))
    hprod (K + 1)
  have hfac : (0 : ℝ) < (K + 1).factorial := by positivity
  calc
    ‖boundedHamiltonianOrbit H ψ t -
        boundedHamiltonianKrylovProjection H ψ K t‖ ≤
        ‖H‖ ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial :=
      norm_boundedHamiltonianOrbit_sub_krylovProjection_le H hH hψ K t
    _ = (‖H‖ * |t|) ^ (K + 1) / (K + 1).factorial := by rw [mul_pow]
    _ ≤ (B * T) ^ (K + 1) / (K + 1).factorial :=
      div_le_div_of_nonneg_right hpow hfac.le
    _ = krylovFactorialBoundary B T K := rfl

/-! ## Complete projection-before-replica incidence -/

/-- **Causal projection before replicas.**  Every complete occupied-image
replica incidence action on a bounded Hamiltonian orbit is dominated by the
same action on the projected occupied image, plus one sharp factorial boundary
paid after the full target union. -/
theorem replicaTargetProjectionMass_boundedHamiltonianOrbit_le_krylov
    {C α : Type*} [Fintype α] [DecidableEq α]
    (H : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (hH : IsSelfAdjoint H) {ψ : EuclideanSpace ℂ α} (hψ : ‖ψ‖ ≤ 1)
    (target : C → α → ℂ) {r : ℕ} (hr : 0 < r) (K : ℕ)
    {B T t : ℝ} (hB : 0 ≤ B) (hHnorm : ‖H‖ ≤ B) (ht : |t| ≤ T) :
    replicaTargetProjectionMass r target
        (fun x => boundedHamiltonianOrbit H ψ t x) ≤
      replicaTargetProjectionMass r
          (projectedReplicaTarget (boundedHamiltonianKrylovSubspace H ψ K) target)
          (fun x => boundedHamiltonianKrylovProjection H ψ K t x) +
        2 * (r : ℝ) * krylovFactorialBoundary B T K := by
  let orbit := boundedHamiltonianOrbit H ψ t
  let S := boundedHamiltonianKrylovSubspace H ψ K
  have horbitCoord : WithLp.toLp 2 (fun x => orbit x) = orbit := by
    ext x
    rfl
  have horbitNorm : ‖WithLp.toLp 2 (fun x => orbit x)‖ ≤ 1 := by
    rw [horbitCoord, norm_boundedHamiltonianOrbit_eq H hH]
    exact hψ
  have hdefect :
      ‖WithLp.toLp 2 (fun x => orbit x) -
          S.starProjection (WithLp.toLp 2 (fun x => orbit x))‖ ≤
        krylovFactorialBoundary B T K := by
    simpa [horbitCoord, orbit, S, boundedHamiltonianKrylovProjection] using
      norm_boundedHamiltonianOrbit_sub_krylovProjection_le_boundary
        H hH hψ K hB hHnorm ht
  simpa [orbit, S, boundedHamiltonianKrylovProjection] using
    replicaTargetProjectionMass_le_projected_add_error
      hr S target (fun x => orbit x) horbitNorm hdefect

/-- The projected complete target image obeys both exact paper rank caps:
rank contraction from the original occupied image and the stars-and-bars
dimension of the causal Krylov carrier. -/
theorem finrank_projectedReplicaTargetSpan_le_krylov_min
    {C α : Type*} [Fintype α] [DecidableEq α]
    (H : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (ψ : EuclideanSpace ℂ α) (K r : ℕ) (target : C → α → ℂ) :
    Module.finrank ℂ
        (replicaTargetSpan r
          (projectedReplicaTarget
            (boundedHamiltonianKrylovSubspace H ψ K) target)) ≤
      min (Module.finrank ℂ (replicaTargetSpan r target))
        ((Module.finrank ℂ (boundedHamiltonianKrylovSubspace H ψ K) + r - 1).choose r) :=
  finrank_projectedReplicaTargetSpan_le_min r
    (boundedHamiltonianKrylovSubspace H ψ K) target

/-! ## Return-excised complete capture laws -/

/-- Shifted-threshold return-excised Krylov incidence law.  Every original
capture at fidelity `a` is controlled by one projected occupied-image moment
at the exact amplitude loss `sqrt a - eta_K(T)`. -/
theorem measureReal_boundedHamiltonian_capture_le_return_add_krylovMoment
    {X C α : Type*} [MeasurableSpace X] [Fintype α] [DecidableEq α]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (H : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (hH : IsSelfAdjoint H) {ψ : EuclideanSpace ℂ α} (hψ : ‖ψ‖ ≤ 1)
    (target : C → α → ℂ)
    (htarget : ∀ c, ‖WithLp.toLp 2 (target c)‖ ≤ 1)
    (time : X → ℝ) (K : ℕ) {B T a : ℝ}
    (hB : 0 ≤ B) (hHnorm : ‖H‖ ≤ B)
    (htime : ∀ x, |time x| ≤ T)
    (hboundary : krylovFactorialBoundary B T K < Real.sqrt a)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hint : MeasureTheory.Integrable
      (fun x => replicaTargetProjectionMass r
        (projectedReplicaTarget (boundedHamiltonianKrylovSubspace H ψ K) target)
        (fun i => boundedHamiltonianKrylovProjection H ψ K (time x) i))
      (μ.restrict returnSetᶜ)) :
    μ.real {x | ∃ c, a ≤ finitePureStateFidelity
        (fun i => boundedHamiltonianOrbit H ψ (time x) i) (target c)} ≤
      μ.real returnSet +
        (∫ x, replicaTargetProjectionMass r
          (projectedReplicaTarget (boundedHamiltonianKrylovSubspace H ψ K) target)
          (fun i => boundedHamiltonianKrylovProjection H ψ K (time x) i)
            ∂(μ.restrict returnSetᶜ)) /
          (Real.sqrt a - krylovFactorialBoundary B T K) ^ (2 * r) := by
  let state : X → α → ℂ := fun x i => boundedHamiltonianOrbit H ψ (time x) i
  let S := boundedHamiltonianKrylovSubspace H ψ K
  have hdefect : ∀ x,
      ‖WithLp.toLp 2 (state x) - S.starProjection (WithLp.toLp 2 (state x))‖ ≤
        krylovFactorialBoundary B T K := by
    intro x
    have hcoord : WithLp.toLp 2 (state x) =
        boundedHamiltonianOrbit H ψ (time x) := by
      ext i
      rfl
    simpa [state, S, hcoord, boundedHamiltonianKrylovProjection] using
      norm_boundedHamiltonianOrbit_sub_krylovProjection_le_boundary
        H hH hψ K hB hHnorm (htime x)
  simpa [state, S, boundedHamiltonianKrylovProjection] using
    measureReal_capture_le_return_add_projectedMoment
      μ hr S target state htarget hboundary hdefect returnSet hreturn (by
        simpa [state, S, boundedHamiltonianKrylovProjection] using hint)

/-- Additive return-excised Krylov incidence law.  It retains the original
fidelity threshold and pays the factorial defect once, after the complete
target union and before integration over the return-free source. -/
theorem measureReal_boundedHamiltonian_capture_le_return_add_krylovMoment_error
    {X C α : Type*} [MeasurableSpace X] [Fintype α] [DecidableEq α]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (H : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (hH : IsSelfAdjoint H) {ψ : EuclideanSpace ℂ α} (hψ : ‖ψ‖ ≤ 1)
    (target : C → α → ℂ)
    (htarget : ∀ c, ‖WithLp.toLp 2 (target c)‖ ≤ 1)
    (time : X → ℝ) (K : ℕ) {B T a : ℝ}
    (hB : 0 ≤ B) (hHnorm : ‖H‖ ≤ B)
    (htime : ∀ x, |time x| ≤ T) (ha : 0 < a)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hintOriginal : MeasureTheory.Integrable
      (fun x => replicaTargetProjectionMass r target
        (fun i => boundedHamiltonianOrbit H ψ (time x) i))
      (μ.restrict returnSetᶜ))
    (hintProjected : MeasureTheory.Integrable
      (fun x => replicaTargetProjectionMass r
        (projectedReplicaTarget (boundedHamiltonianKrylovSubspace H ψ K) target)
        (fun i => boundedHamiltonianKrylovProjection H ψ K (time x) i))
      (μ.restrict returnSetᶜ)) :
    μ.real {x | ∃ c, a ≤ finitePureStateFidelity
        (fun i => boundedHamiltonianOrbit H ψ (time x) i) (target c)} ≤
      μ.real returnSet +
        ((∫ x, replicaTargetProjectionMass r
          (projectedReplicaTarget (boundedHamiltonianKrylovSubspace H ψ K) target)
          (fun i => boundedHamiltonianKrylovProjection H ψ K (time x) i)
            ∂(μ.restrict returnSetᶜ)) +
          2 * (r : ℝ) * krylovFactorialBoundary B T K * μ.real returnSetᶜ) /
            a ^ r := by
  let state : X → α → ℂ := fun x i => boundedHamiltonianOrbit H ψ (time x) i
  let S := boundedHamiltonianKrylovSubspace H ψ K
  have hstate : ∀ x, ‖WithLp.toLp 2 (state x)‖ ≤ 1 := by
    intro x
    have hcoord : WithLp.toLp 2 (state x) =
        boundedHamiltonianOrbit H ψ (time x) := by
      ext i
      rfl
    rw [hcoord, norm_boundedHamiltonianOrbit_eq H hH]
    exact hψ
  have hdefect : ∀ x,
      ‖WithLp.toLp 2 (state x) - S.starProjection (WithLp.toLp 2 (state x))‖ ≤
        krylovFactorialBoundary B T K := by
    intro x
    have hcoord : WithLp.toLp 2 (state x) =
        boundedHamiltonianOrbit H ψ (time x) := by
      ext i
      rfl
    simpa [state, S, hcoord, boundedHamiltonianKrylovProjection] using
      norm_boundedHamiltonianOrbit_sub_krylovProjection_le_boundary
        H hH hψ K hB hHnorm (htime x)
  have htargetReplica : ∀ c,
      ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1 := fun c =>
    norm_finitePureTensorPowerEuclidean_le_one r (target c) (htarget c)
  simpa [state, S, boundedHamiltonianKrylovProjection] using
    measureReal_capture_le_return_add_projectedMoment_error
      μ hr S target state htargetReplica hstate ha hdefect returnSet hreturn
        (by simpa [state] using hintOriginal)
        (by simpa [state, S, boundedHamiltonianKrylovProjection] using hintProjected)

end FiniteDimensional

end Hilbert

/-! ## Radial rigidity of Krylov incidence -/

theorem boundedHamiltonianKrylovSubspace_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (H : E →L[ℂ] E) (ψ : E) (K : ℕ) {c : ℂ} (hc : c ≠ 0) :
    boundedHamiltonianKrylovSubspace (c • H) ψ K =
      boundedHamiltonianKrylovSubspace H ψ K := by
  apply le_antisymm
  · rw [boundedHamiltonianKrylovSubspace]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    change (((c • H) ^ (k : ℕ)) ψ) ∈ _
    rw [smul_pow]
    simp only [smul_apply]
    exact Submodule.smul_mem _ _
      (boundedHamiltonianKrylovPower_mem H ψ (Nat.le_of_lt_succ k.isLt))
  · rw [boundedHamiltonianKrylovSubspace]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    change ((H ^ (k : ℕ)) ψ) ∈ _
    have hpow : c ^ (k : ℕ) ≠ 0 := pow_ne_zero _ hc
    have hmem := boundedHamiltonianKrylovPower_mem (c • H) ψ
      (Nat.le_of_lt_succ k.isLt)
    rw [smul_pow] at hmem
    simp only [smul_apply] at hmem
    have hscaled := Submodule.smul_mem
      (boundedHamiltonianKrylovSubspace (c • H) ψ K) (c ^ (k : ℕ))⁻¹ hmem
    simpa [← smul_assoc, hpow] using hscaled

theorem boundedHamiltonianOrbit_real_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (H : E →L[ℂ] E) (ψ : E) (c t : ℝ) :
    boundedHamiltonianOrbit ((c : ℂ) • H) ψ t =
      boundedHamiltonianOrbit H ψ (c * t) := by
  unfold boundedHamiltonianOrbit
  congr 2
  ext x
  simp only [smul_apply]
  module

theorem boundedHamiltonianKrylovProjection_real_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E]
    (H : E →L[ℂ] E) (ψ : E) (K : ℕ) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    boundedHamiltonianKrylovProjection ((c : ℂ) • H) ψ K t =
      boundedHamiltonianKrylovProjection H ψ K (c * t) := by
  unfold boundedHamiltonianKrylovProjection
  simp only [boundedHamiltonianKrylovSubspace_smul H ψ K
    (Complex.ofReal_ne_zero.mpr hc), boundedHamiltonianOrbit_real_smul]

theorem projectedReplicaTarget_krylov_real_smul
    {C α : Type*} [Fintype α]
    (H : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (ψ : EuclideanSpace ℂ α) (K : ℕ) (target : C → α → ℂ)
    {c : ℝ} (hc : c ≠ 0) :
    projectedReplicaTarget
        (boundedHamiltonianKrylovSubspace ((c : ℂ) • H) ψ K) target =
      projectedReplicaTarget
        (boundedHamiltonianKrylovSubspace H ψ K) target := by
  simp only [boundedHamiltonianKrylovSubspace_smul H ψ K
    (Complex.ofReal_ne_zero.mpr hc)]

theorem replicaTargetProjectionMass_krylov_real_smul
    {C α : Type*} [Fintype α]
    (H : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (ψ : EuclideanSpace ℂ α) (K r : ℕ) (target : C → α → ℂ)
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    replicaTargetProjectionMass r
        (projectedReplicaTarget
          (boundedHamiltonianKrylovSubspace ((c : ℂ) • H) ψ K) target)
        (fun i => boundedHamiltonianKrylovProjection
          ((c : ℂ) • H) ψ K t i) =
      replicaTargetProjectionMass r
        (projectedReplicaTarget
          (boundedHamiltonianKrylovSubspace H ψ K) target)
        (fun i => boundedHamiltonianKrylovProjection H ψ K (c * t) i) := by
  rw [projectedReplicaTarget_krylov_real_smul H ψ K target hc]
  congr 2
  funext i
  exact congrArg (fun v : EuclideanSpace ℂ α => v i)
    (boundedHamiltonianKrylovProjection_real_smul H ψ K hc t)

def realLinearHamiltonianFamily
    {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : J → E →L[ℂ] E) (x : J → ℝ) : E →L[ℂ] E :=
  ∑ j, ((x j : ℝ) : ℂ) • A j

theorem realLinearHamiltonianFamily_smul
    {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : J → E →L[ℂ] E) (c : ℝ) (x : J → ℝ) :
    realLinearHamiltonianFamily A (c • x) =
      (c : ℂ) • realLinearHamiltonianFamily A x := by
  unfold realLinearHamiltonianFamily
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.smul_apply, smul_smul]
  congr 1
  rw [smul_eq_mul]
  push_cast
  rfl

theorem realLinearHamiltonianFamily_krylovSubspace_smul
    {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : J → E →L[ℂ] E) (x : J → ℝ) (ψ : E) (K : ℕ)
    {c : ℝ} (hc : c ≠ 0) :
    boundedHamiltonianKrylovSubspace
        (realLinearHamiltonianFamily A (c • x)) ψ K =
      boundedHamiltonianKrylovSubspace
        (realLinearHamiltonianFamily A x) ψ K := by
  rw [realLinearHamiltonianFamily_smul]
  exact boundedHamiltonianKrylovSubspace_smul _ ψ K
    (Complex.ofReal_ne_zero.mpr hc)

theorem realLinearHamiltonianFamily_orbit_smul
    {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : J → E →L[ℂ] E) (x : J → ℝ) (ψ : E)
    (c t : ℝ) :
    boundedHamiltonianOrbit
        (realLinearHamiltonianFamily A (c • x)) ψ t =
      boundedHamiltonianOrbit
        (realLinearHamiltonianFamily A x) ψ (c * t) := by
  rw [realLinearHamiltonianFamily_smul]
  exact boundedHamiltonianOrbit_real_smul _ ψ c t

theorem realLinearHamiltonianFamily_krylovProjection_smul
    {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E]
    (A : J → E →L[ℂ] E) (x : J → ℝ) (ψ : E) (K : ℕ)
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    boundedHamiltonianKrylovProjection
        (realLinearHamiltonianFamily A (c • x)) ψ K t =
      boundedHamiltonianKrylovProjection
        (realLinearHamiltonianFamily A x) ψ K (c * t) := by
  rw [realLinearHamiltonianFamily_smul]
  exact boundedHamiltonianKrylovProjection_real_smul _ ψ K hc t

theorem realLinearHamiltonianFamily_incidence_smul
    {J C α : Type*} [Fintype J] [Fintype α]
    (A : J → EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (x : J → ℝ) (ψ : EuclideanSpace ℂ α) (K r : ℕ)
    (target : C → α → ℂ) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    replicaTargetProjectionMass r
        (projectedReplicaTarget
          (boundedHamiltonianKrylovSubspace
            (realLinearHamiltonianFamily A (c • x)) ψ K) target)
        (fun i => boundedHamiltonianKrylovProjection
          (realLinearHamiltonianFamily A (c • x)) ψ K t i) =
      replicaTargetProjectionMass r
        (projectedReplicaTarget
          (boundedHamiltonianKrylovSubspace
            (realLinearHamiltonianFamily A x) ψ K) target)
        (fun i => boundedHamiltonianKrylovProjection
          (realLinearHamiltonianFamily A x) ψ K (c * t) i) := by
  rw [realLinearHamiltonianFamily_smul]
  exact replicaTargetProjectionMass_krylov_real_smul
    (realLinearHamiltonianFamily A x) ψ K r target hc t

/-- Projected complete-incidence action of a finite real-linear Hamiltonian
dictionary. -/
def realLinearHamiltonianKrylovIncidenceAction
    {J C α : Type*} [Fintype J] [Fintype α]
    (A : J → EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (ψ : EuclideanSpace ℂ α) (K r : ℕ) (target : C → α → ℂ)
    (x : J → ℝ) (t : ℝ) : ℝ :=
  replicaTargetProjectionMass r
    (projectedReplicaTarget
      (boundedHamiltonianKrylovSubspace
        (realLinearHamiltonianFamily A x) ψ K) target)
    (fun i => boundedHamiltonianKrylovProjection
      (realLinearHamiltonianFamily A x) ψ K t i)

/-- Radial coefficient scaling changes only the clock of the complete Krylov
incidence action. -/
theorem realLinearHamiltonianKrylovIncidenceAction_smul
    {J C α : Type*} [Fintype J] [Fintype α]
    (A : J → EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (ψ : EuclideanSpace ℂ α) (K r : ℕ) (target : C → α → ℂ)
    (x : J → ℝ) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    realLinearHamiltonianKrylovIncidenceAction A ψ K r target (c • x) t =
      realLinearHamiltonianKrylovIncidenceAction A ψ K r target x (c * t) := by
  exact realLinearHamiltonianFamily_incidence_smul
    A x ψ K r target hc t

/-- **Unconditional Gaussian independent-product incidence law.**  Gaussian
coefficient averaging equals averaging over an independent normalized uniform
direction and chi radius, with the radius transported entirely into time. -/
theorem integral_stdGaussian_realLinearHamiltonianKrylovIncidenceAction_product
    {m : ℕ} (hm : 0 < m) {C α : Type*} [Fintype α]
    (A : Fin m → EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (ψ : EuclideanSpace ℂ α) (K r : ℕ) (target : C → α → ℂ)
    (t : ℝ) :
    (∫ x, realLinearHamiltonianKrylovIncidenceAction
        A ψ K r target x t
      ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) =
      ∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Set.Ioi (0 : ℝ),
        realLinearHamiltonianKrylovIncidenceAction
          A ψ K r target p.1.1 (p.2.1 * t)
        ∂((gaussianAngularMeasure m).prod (gaussianRadiusMeasure m)) := by
  have hcoord (direction : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin m)) 1) (radius : ℝ) :
      (fun j => (radius • direction.1 : EuclideanSpace ℝ (Fin m)) j) =
        radius • (fun j => direction.1 j) := by
    funext j
    rfl
  refine integral_stdGaussian_radialTimeProduct hm
    (fun x time => realLinearHamiltonianKrylovIncidenceAction
      A ψ K r target (fun j => x j) time) ?_ t
  intro direction radius hradius time
  rw [hcoord]
  exact realLinearHamiltonianKrylovIncidenceAction_smul
    A ψ K r target (fun j => direction.1 j) hradius.ne' time

/-- **Gaussian fixed-shell temporal mixture.**  A standard Gaussian
Hamiltonian coefficient vector is exactly a chi-radius mixture of uniform
fixed-shell Krylov incidence actions, with radius transported into time. -/
theorem integral_stdGaussian_realLinearHamiltonianKrylovIncidenceAction
    {m : ℕ} (hm : 0 < m) {C α : Type*} [Fintype α]
    (A : Fin m → EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (ψ : EuclideanSpace ℂ α) (K r : ℕ) (target : C → α → ℂ)
    (t : ℝ)
    (hpolar : MeasureTheory.Integrable
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Set.Ioi (0 : ℝ) =>
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
          Real.exp (-p.2.1 ^ 2 / 2)) •
          realLinearHamiltonianKrylovIncidenceAction
            A ψ K r target (p.2.1 • p.1.1) t)
      ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin m))).toSphere.prod
        (MeasureTheory.Measure.volumeIoiPow (m - 1)))) :
    (∫ x, realLinearHamiltonianKrylovIncidenceAction
        A ψ K r target x t
      ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) =
      ∫ radius in Set.Ioi (0 : ℝ), gaussianRadialDensity m radius •
        gaussianSphereAverage m (fun direction =>
          realLinearHamiltonianKrylovIncidenceAction
            A ψ K r target direction.1 (radius * t)) := by
  have hcoord (direction : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin m)) 1) (radius : ℝ) :
      (fun j => (radius • direction.1 : EuclideanSpace ℝ (Fin m)) j) =
        radius • (fun j => direction.1 j) := by
    funext j
    rfl
  refine integral_stdGaussian_radialTimeMixture hm
    (fun x time => realLinearHamiltonianKrylovIncidenceAction
      A ψ K r target (fun j => x j) time) ?_ t ?_
  · intro direction radius hradius time
    rw [hcoord]
    exact realLinearHamiltonianKrylovIncidenceAction_smul
      A ψ K r target (fun j => direction.1 j) hradius.ne' time
  · apply hpolar.congr
    filter_upwards with p
    congr 2

end GaloisForLFunctions.HTGeometry
