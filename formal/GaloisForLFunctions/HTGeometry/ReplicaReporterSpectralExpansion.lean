import GaloisForLFunctions.HTGeometry.FiniteQuditHermitianStringBasis
import GaloisForLFunctions.HTGeometry.GaussianRadialSpectralPacket
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity

/-!
# Spectral expansion of a replica reporter

A reporter of replica order `k` evaluates an operator on the `k`-fold tensor
power against the `k`-fold tensor power of the state projector.  Inserting the
spectral resolution of the evolved state in every tensor factor expands the
reporter into a finite packet of characters whose detuning is the total forward
energy minus the total backward energy, and whose coefficient is the trace of
the operator against the corresponding tensor product of spectral rank-one
blocks.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D k : ℕ} [NeZero D] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one operator `|ψ⟩⟨φ|`. -/
def outerProduct (ψ φ : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun r c => ψ r * (starRingEnd ℂ) (φ c)

omit [NeZero D] in
@[simp] theorem outerProduct_apply (ψ φ : Fin D → ℂ) (r c : Fin D) :
    outerProduct ψ φ r c = ψ r * (starRingEnd ℂ) (φ c) := rfl

/-- The `k`-replica reporter attached to an operator on the `k`-fold tensor
power of the local space. -/
def replicaReporter (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (ψ : Fin D → ℂ) : ℂ :=
  (A * quditStringOf (fun _ : Fin k => outerProduct ψ ψ)).trace

omit [NeZero D] [DecidableEq ι] in
/-- The state projector of a spectral superposition expands into the double
spectral sum of rank-one blocks. -/
theorem outerProduct_sum (w : ι → ℂ) (v : ι → (Fin D → ℂ)) :
    outerProduct (∑ i, w i • v i) (∑ i, w i • v i)
      = ∑ q : ι × ι, (w q.1 * (starRingEnd ℂ) (w q.2)) •
          outerProduct (v q.1) (v q.2) := by
  ext r c
  rw [outerProduct_apply, Matrix.sum_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Matrix.smul_apply, outerProduct_apply]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Total replica detuning: the forward energy sum minus the backward energy
sum. -/
def replicaDetuning (E : ι → ℝ) (p : Fin k → ι × ι) : ℝ :=
  ∑ j, (E (p j).1 - E (p j).2)

/-- The exact replica coefficient: the spectral amplitude product times the trace
of the reporter operator against the corresponding tensor block. -/
def replicaCoefficient (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : ι → (Fin D → ℂ)) (α : ι → ℂ) (p : Fin k → ι × ι) : ℂ :=
  (∏ j, α (p j).1 * (starRingEnd ℂ) (α (p j).2))
    * (A * quditStringOf (fun j => outerProduct (v (p j).1) (v (p j).2))).trace

omit [NeZero D] in
/-- **Replica spectral expansion.**  A replica reporter of the spectrally
evolved state is a finite packet of characters in the total replica detuning. -/
theorem replicaReporter_spectral_expansion
    (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : ι → (Fin D → ℂ)) (α : ι → ℂ) (E : ι → ℝ) (s : ℝ) :
    replicaReporter A
        (∑ i, (Complex.exp (-((s * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)
      = ∑ p : Fin k → ι × ι,
          replicaCoefficient A v α p *
            Complex.exp (-((s * replicaDetuning E p : ℝ) : ℂ) * Complex.I) := by
  classical
  set w : ι → ℂ := fun i => Complex.exp (-((s * E i : ℝ) : ℂ) * Complex.I) * α i
    with hw
  rw [replicaReporter, outerProduct_sum w v,
    quditStringOf_sum_family (fun q : ι × ι => outerProduct (v q.1) (v q.2))
      (fun _ : Fin k => fun q : ι × ι => w q.1 * (starRingEnd ℂ) (w q.2))]
  rw [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, replicaCoefficient]
  have hfactor : ∀ j : Fin k,
      w (p j).1 * (starRingEnd ℂ) (w (p j).2)
        = (α (p j).1 * (starRingEnd ℂ) (α (p j).2)) *
          Complex.exp (-((s * (E (p j).1 - E (p j).2) : ℝ) : ℂ) * Complex.I) := by
    intro j
    have hconj : (starRingEnd ℂ) (Complex.exp (-((s * E (p j).2 : ℝ) : ℂ) * Complex.I))
        = Complex.exp (((s * E (p j).2 : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_I]
    simp only [hw, map_mul, hconj]
    rw [show Complex.exp (-((s * E (p j).1 : ℝ) : ℂ) * Complex.I) * α (p j).1 *
          (Complex.exp (((s * E (p j).2 : ℝ) : ℂ) * Complex.I)
            * (starRingEnd ℂ) (α (p j).2))
        = (α (p j).1 * (starRingEnd ℂ) (α (p j).2)) *
          (Complex.exp (-((s * E (p j).1 : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((s * E (p j).2 : ℝ) : ℂ) * Complex.I)) from by ring,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun j (_ : j ∈ Finset.univ) => hfactor j),
    Finset.prod_mul_distrib, ← Complex.exp_sum]
  rw [show (∑ j : Fin k, -((s * (E (p j).1 - E (p j).2) : ℝ) : ℂ) * Complex.I)
      = -((s * replicaDetuning E p : ℝ) : ℂ) * Complex.I by
    rw [← Finset.sum_mul]
    congr 1
    rw [replicaDetuning]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]]
  ring

omit [NeZero D] in
/-- The replica reporter of the state evolved for the Gaussian radial time is
exactly a radial spectral packet. -/
theorem replicaReporter_eq_radialSpectralPacket
    (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : ι → (Fin D → ℂ)) (α : ι → ℂ) (E : ι → ℝ) (time r : ℝ) :
    replicaReporter A
        (∑ i, (Complex.exp (-((time * r * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)
      = radialSpectralPacket Finset.univ (replicaCoefficient A v α)
          (replicaDetuning E) time r := by
  rw [replicaReporter_spectral_expansion A v α E (time * r), radialSpectralPacket]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  push_cast
  ring

omit [NeZero D] in
/-- **Exact radial observer--spectral action law.**  Gaussian radial averaging of
a replica reporter evaluates the universal radial kernel at every replica
action. -/
theorem integral_replicaReporter_radial {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : ι → (Fin D → ℂ)) (α : ι → ℂ) (E : ι → ℝ) (time : ℝ) :
    (∫ x, replicaReporter A
        (∑ i, (Complex.exp (-((time * ‖x‖ * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      = ∑ p : Fin k → ι × ι,
          replicaCoefficient A v α p *
            radialActionKernel m (time * replicaDetuning E p) := by
  rw [show (fun x : EuclideanSpace ℝ (Fin m) => replicaReporter A
        (∑ i, (Complex.exp (-((time * ‖x‖ * E i : ℝ) : ℂ) * Complex.I) * α i) • v i))
      = fun x : EuclideanSpace ℝ (Fin m) =>
        radialSpectralPacket Finset.univ (replicaCoefficient A v α)
          (replicaDetuning E) time ‖x‖ from
    funext fun x => replicaReporter_eq_radialSpectralPacket A v α E time ‖x‖]
  exact integral_radialSpectralPacket hm Finset.univ (replicaCoefficient A v α)
    (replicaDetuning E) time

omit [NeZero D] in
/-- **Zero-action completion law for replica reporters.**  At unbounded Gaussian
radial observation time, exactly the zero-replica-action sector survives. -/
theorem tendsto_integral_replicaReporter_radial_atTop {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : ι → (Fin D → ℂ)) (α : ι → ℂ) (E : ι → ℝ) :
    Tendsto
      (fun time : ℝ =>
        ∫ x, replicaReporter A
          (∑ i, (Complex.exp (-((time * ‖x‖ * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop
      (𝓝 (∑ p ∈ Finset.univ.filter fun p : Fin k → ι × ι => replicaDetuning E p = 0,
            replicaCoefficient A v α p)) := by
  classical
  have hpacket : ∀ time : ℝ,
      (∫ x, replicaReporter A
          (∑ i, (Complex.exp (-((time * ‖x‖ * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
        = ∫ x, radialSpectralPacket Finset.univ (replicaCoefficient A v α)
            (replicaDetuning E) time ‖x‖
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    intro time
    exact congrArg _ (funext fun x =>
      replicaReporter_eq_radialSpectralPacket A v α E time ‖x‖)
  refine Tendsto.congr (fun time => (hpacket time).symm) ?_
  exact tendsto_integral_radialSpectralPacket_atTop hm Finset.univ
    (replicaCoefficient A v α) (replicaDetuning E)

omit [NeZero D] in
/-- **Completed-time average of a replica reporter.**  The Bohr mean value — the
Haar average over the completed one-parameter time group — of a replica reporter
is exactly its zero-action sector. -/
theorem bohrMean_replicaReporter
    (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : ι → (Fin D → ℂ)) (α : ι → ℂ) (E : ι → ℝ) :
    bohrMean (fun s : ℝ => replicaReporter A
        (∑ i, (Complex.exp (-((s * E i : ℝ) : ℂ) * Complex.I) * α i) • v i))
      = ∑ p ∈ Finset.univ.filter fun p : Fin k → ι × ι => replicaDetuning E p = 0,
          replicaCoefficient A v α p := by
  classical
  have hchar : ∀ s : ℝ, (fun s : ℝ => replicaReporter A
        (∑ i, (Complex.exp (-((s * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)) s
      = ∑ p : Fin k → ι × ι,
        replicaCoefficient A v α p * expChar (-replicaDetuning E p) s := by
    intro s
    dsimp only
    rw [replicaReporter_spectral_expansion A v α E s]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    rw [expChar]
    congr 1
    push_cast
    ring
  rw [funext hchar, bohrMean_sum_expChar Finset.univ (replicaCoefficient A v α)
    (fun p => -replicaDetuning E p), Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : replicaDetuning E p = 0
  · rw [if_pos (by rw [hp]; ring), if_pos hp]
  · rw [if_neg (fun h => hp (neg_eq_zero.mp h)), if_neg hp]

omit [NeZero D] in
/-- **Gaussian radial completion.**  The Gaussian radial observation of a replica
reporter converges, as the observation time grows, to its completed-time Haar
average. -/
theorem tendsto_integral_replicaReporter_radial_bohrMean {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin k → Fin D) (Fin k → Fin D) ℂ)
    (v : ι → (Fin D → ℂ)) (α : ι → ℂ) (E : ι → ℝ) :
    Tendsto
      (fun time : ℝ =>
        ∫ x, replicaReporter A
          (∑ i, (Complex.exp (-((time * ‖x‖ * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop
      (𝓝 (bohrMean (fun s : ℝ => replicaReporter A
        (∑ i, (Complex.exp (-((s * E i : ℝ) : ℂ) * Complex.I) * α i) • v i)))) := by
  classical
  rw [bohrMean_replicaReporter A v α E]
  exact tendsto_integral_replicaReporter_radial_atTop hm A v α E

end

end GaloisForLFunctions.HTGeometry
