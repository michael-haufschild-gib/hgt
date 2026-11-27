import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Stability

/-! # Sharp joint near-line gain for independent elementary primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across

open Filter Real
open PrimeCalibration (log_pos_prime)
open scoped Topology

variable {F : Finset Nat.Primes} [Nonempty F] {J : F → Type*}
  [∀ p, Fintype (J p)] [∀ p, Nonempty (J p)]

/-- Maximum after normalizing each prime by its own elementary radial
displacement. The distance h is measured from the isometry line. -/
def normalizedError (k : (p : F) → J p → ℕ+) (h t : ℝ) := peak fun p =>
  jointError p.val (k p) ⟨1/2+h,t⟩ / (2*|sinh (h*log p.val.val)|)

private def weights (k : (p : F) → J p → ℕ+) (h : ℝ) (p : F) (i : J p) :=
  amplification (k p i) (h*log p.val.val)

private theorem normalized_score (k : (p : F) → J p → ℕ+) (h t : ℝ) (hn : h≠0) :
    normalizedError k h t=score k (weights k h) (fun p => t*log p.val.val) := by
  unfold normalizedError score
  congr 1; funext p
  have shift : radial p.val (1/2+h)=h*log p.val.val := by unfold radial; ring
  have off := mul_ne_zero hn (log_pos_prime p.val).ne'
  have radial_ne : radial p.val (1/2+h)≠0 := by rwa [shift]
  rw [joint_formula p.val (k p) (⟨1/2+h,t⟩ : ℂ) radial_ne]
  change 2*|sinh (radial p.val (1/2+h))| * sensitivity _ _ _ / (2*|sinh (h*log p.val.val)|)=_
  have scale_ne : 2*|sinh (h*log p.val.val)|≠0 :=
    mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sinh_ne_zero.mpr off))
  simp only [shift,mul_div_cancel_left₀ _ scale_ne,sensitivity,weights]

private theorem independent_limit (k : (p : F) → J p → ℕ+) (θ : F → ℝ) :
    Tendsto (fun h => score k (weights k h) θ) (𝓝[≠] 0) (𝓝 (peak fun p => angular (k p) (θ p))) := by
  apply peak_limit
  intro p
  have hp := (log_pos_prime p.val).ne'
  have scale : Tendsto (fun h : ℝ => h*log p.val.val) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : ContinuousWithinAt (fun u : ℝ => u*log p.val.val) ({0}ᶜ) 0 :=
        (continuous_id.mul_const _).continuousAt.continuousWithinAt
      simpa only [zero_mul] using hh.tendsto
    · filter_upwards [show ∀ᶠ h : ℝ in 𝓝[≠] 0, h≠0 from self_mem_nhdsWithin] with h hn
      exact mul_ne_zero hn hp
  exact (sensitivity_limit (k p) (θ p)).comp scale

/-- Independent phase recurrence makes the largest individual prime
gain sharp, in every punctured neighborhood of the critical line. -/
theorem optimal_gain (k : (p : F) → J p → ℕ+) (δ K : ℝ) (hδ : 0<δ) :
    (∀ h t : ℝ, h≠0 → |h|<δ → K ≤ normalizedError k h t) ↔
      K ≤ peak fun p => gain (k p) := by
  constructor
  · intro lower
    choose θ hθ using fun p => attain_gain (k p)
    have near : ∀ᶠ h : ℝ in 𝓝[≠] 0, K ≤ score k (weights k h) θ := by
      have small : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h|<δ := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact continuous_abs.continuousAt.tendsto.eventually_lt_const (by simpa only [abs_zero] using hδ)
      filter_upwards [small,show ∀ᶠ h : ℝ in 𝓝[≠] 0, h≠0 from self_mem_nhdsWithin] with h hs hn
      have atHeights (t : ℝ) : K ≤ score k (weights k h) (fun p => t*log p.val.val) := by
        rw [←normalized_score k h t hn]
        exact lower h t hn hs
      exact ((all_heights k (weights k h) K).mp atHeights) θ
    simpa only [hθ] using
      le_of_tendsto_of_tendsto tendsto_const_nhds (independent_limit k θ) near
  · intro upper h t hn _
    rw [normalized_score k h t hn]
    apply upper.trans
    apply peak_le.mpr
    intro p
    apply (sensitivity_lower (k p) (h*log p.val.val) (t*log p.val.val)
      (mul_ne_zero hn (log_pos_prime p.val).ne')).trans
    exact to_peak (fun q : F => sensitivity (k q) (h*log q.val.val) (t*log q.val.val)) p

#print axioms optimal_gain

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across
