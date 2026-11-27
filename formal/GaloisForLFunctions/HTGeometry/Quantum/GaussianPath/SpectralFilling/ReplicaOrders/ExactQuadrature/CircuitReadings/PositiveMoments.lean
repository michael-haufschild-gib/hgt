import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.ReplicaMoment
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-! # Positive real readings and the spectral moment of a finite clock -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section

/-- Average of a real observable over physical half-period choices. -/
def reading (ws : List ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  (average ws (fun t => (f t:ℂ)) a).re

private theorem reading_cons (w : ℝ) (ws : List ℝ) (f : ℝ → ℝ) (a : ℝ) :
    reading (w::ws) f a=(reading ws f a+reading ws f (a+π/|w|))/2 := by
  simp only [reading,average,show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.div_ofReal_re,Complex.add_re]

theorem reading_mono (ws : List ℝ) {f g : ℝ → ℝ} (h : ∀ t, f t≤g t) (a : ℝ) :
    reading ws f a≤reading ws g a := by
  induction ws generalizing a with
  | nil => exact h a
  | cons w ws ih =>
    rw [reading_cons,reading_cons]
    exact div_le_div_of_nonneg_right (add_le_add (ih a) (ih _) ) (by norm_num)

theorem reading_mul (ws : List ℝ) (c : ℝ) (f : ℝ → ℝ) (a : ℝ) :
    reading ws (fun t => c*f t) a=c*reading ws f a := by
  simp only [reading,Complex.ofReal_mul,average_scale,Complex.re_ofReal_mul]

theorem reading_sum {J : Type*} [Fintype J] (ws : List ℝ) (f : J → ℝ → ℝ) (a : ℝ) :
    reading ws (fun t => ∑ j, f j t) a=∑ j, reading ws (f j) a := by
  simp only [reading,Complex.ofReal_sum,average_sum,Complex.re_sum]

/-- Every unit-modulus target twist on a maximally projective spectrum
has a sampled trace moment bounded by the exact permutation floor. -/
theorem reading_trace_floor {I : Type*} [Fintype I] [DecidableEq I]
    (w E : I → ℝ) (hw : ∀ i, 0<w i) (hmax : MaximallyProjectiveEnergy E)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖=1) (q : ℕ) (a : ℝ) :
    reading (frequencies E q).toList (fun t => ‖twistedFiniteSpectralAmplitude w E v t‖^(2*q)) a≤
      fidelityReplicaPermutationFloor w q := by
  classical
  let S := (univ : Finset I).piAntidiag q
  let e := replicaMultiplicityEnergy E
  let c (p k : I → ℕ) := (fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist v p k
  have rigid := (forall_replicaRigidAt_iff_maximallyProjectiveEnergy E).mpr hmax q
  have he (p : I → ℕ) (hp : p∈S) : (∑ k∈S, if e p=e k then c p k else 0)=c p p := by
    rw [sum_eq_single p,if_pos rfl]
    · intro k hk hkp
      exact if_neg fun h => hkp (rigid p hp k hk h).symm
    · intro h
      exact (h hp).elim
  have hpow (t : ℝ) : ((‖twistedFiniteSpectralAmplitude w E v t‖^(2*q):ℝ):ℂ)=
      twistedFiniteSpectralFidelity w E v t^q := by
    simp only [twistedFiniteSpectralFidelity,Complex.sq_norm,pow_mul,Complex.ofReal_pow]
  rw [reading]
  simp_rw [hpow]
  rw [exact_replica_moment]
  change (∑ p∈S, ∑ k∈S, if e p=e k then c p k else 0).re≤_
  rw [Complex.re_sum]
  refine sum_le_sum fun p hp => ?_
  rw [he p hp]
  apply (Complex.re_le_norm _).trans
  simp only [c,norm_mul,norm_replicaMultiplicityTwist hv,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (fidelityReplicaMultiplicityWeight_pos hw p p),le_refl]

#print axioms reading_trace_floor
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
