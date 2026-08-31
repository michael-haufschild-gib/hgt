import GaloisForLFunctions.HTGeometry.PrincipalPartMatching
import GaloisForLFunctions.HTGeometry.JacobiThetaSourcePrincipalPart

/-!
# The theta source as the universal one-pole quasi-elliptic increment

The theta logarithmic derivative is analytic off the odd half-period orbit and has principal part
`1/(w - q)` at every point of it.  Any meromorphic function with the same divisor, the same simple
principal parts, period one and a constant quasiperiod increment therefore differs from it by a
constant, and its increment is forced to be `-2πi`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Elementary transformations of a principal part -/

theorem HasPrincipalPart.const_mul {f : ℂ → ℂ} {q r : ℂ} (h : HasPrincipalPart f q r) (c : ℂ) :
    HasPrincipalPart (fun w => c * f w) q (c * r) := by
  obtain ⟨g, hg, heq⟩ := h
  refine ⟨fun w => c * g w, analyticAt_const.mul hg, ?_⟩
  filter_upwards [heq] with w hw
  rw [hw]
  ring

theorem HasPrincipalPart.comp_sub {f : ℂ → ℂ} {q r : ℂ} (h : HasPrincipalPart f q r) (a : ℂ) :
    HasPrincipalPart (fun w => f (w - a)) (q + a) r := by
  obtain ⟨g, hg, heq⟩ := h
  have hshift : AnalyticAt ℂ (fun w : ℂ => g (w - a)) (q + a) := by
    have hlin : AnalyticAt ℂ (fun w : ℂ => w - a) (q + a) := analyticAt_id.sub analyticAt_const
    have : ((q : ℂ) + a) - a = q := by ring
    exact hg.comp_of_eq hlin this
  refine ⟨fun w => g (w - a), hshift, ?_⟩
  have ht : Tendsto (fun w : ℂ => w - a) (𝓝[≠] (q + a)) (𝓝[≠] q) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun w : ℂ => w - a) (𝓝 (q + a)) (𝓝 (q + a - a)) :=
        (continuousAt_id.sub continuousAt_const).tendsto
      have hval : q + a - a = q := by ring
      rw [hval] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
      intro hcon
      exact hw (by linear_combination hcon)
  filter_upwards [ht.eventually heq] with w hw
  have hshiftq : (w - a) - q = w - (q + a) := by ring
  rw [hshiftq] at hw
  exact hw

/-! ### The theta divisor and the theta source -/

/-- The theta divisor: the odd half-period orbit. -/
def thetaDivisor (τ : ℂ) : Set ℂ :=
  {z | ∃ m n : ℤ, z = thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ}

theorem hasPrincipalPart_thetaSource {τ : ℂ} (hτ : 0 < τ.im) {q : ℂ}
    (hq : q ∈ thetaDivisor τ) : HasPrincipalPart (thetaSource τ) q 1 := by
  obtain ⟨m, n, rfl⟩ := hq
  refine hasPrincipalPart_logDeriv_of_simple_zero (analyticAt_jacobiTheta₂_fst hτ _) ?_ ?_
  · exact jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero τ m n
  · rw [deriv_jacobiTheta₂_fst hτ]
    exact jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero hτ m n

theorem analyticAt_thetaSource_of_notMem {τ : ℂ} (hτ : 0 < τ.im) {z : ℂ}
    (hz : z ∉ thetaDivisor τ) : AnalyticAt ℂ (thetaSource τ) z := by
  have hne : jacobiTheta₂ z τ ≠ 0 := fun h =>
    hz ((jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp h)
  exact (analyticAt_deriv_jacobiTheta₂_fst hτ z).div (analyticAt_jacobiTheta₂_fst hτ z) hne

theorem eventually_jacobiTheta₂_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, jacobiTheta₂ w τ ≠ 0 := by
  rcases (analyticAt_jacobiTheta₂_fst hτ z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨k, hk⟩ := exists_meromorphicOrderAt_jacobiTheta₂ hτ z
    have htop : meromorphicOrderAt (jacobiTheta₂ · τ) z = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (h.filter_mono nhdsWithin_le_nhds)
    rw [hk] at htop
    exact absurd htop (by simp)
  · exact h

theorem eventually_thetaSource_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z,
      thetaSource τ (w + τ) = thetaSource τ w + -(2 * (Real.pi : ℂ) * Complex.I) := by
  filter_upwards [eventually_jacobiTheta₂_ne_zero hτ z] with w hw
  rw [thetaSource_shift hτ hw]
  ring

/-- **The one-pole classification of a quasi-elliptic increment.**  A meromorphic function with the
theta divisor as pole set, the principal part `1/(w - q)` at each pole, punctured period one and a
punctured constant quasiperiod increment differs from the theta source by a constant, and its
increment is `-2πi`. -/
theorem const_sub_thetaSource_of_matching_principal_parts
    {τ : ℂ} (hτ : 0 < τ.im) {U : ℂ → ℂ}
    (hUan : ∀ z ∉ thetaDivisor τ, AnalyticAt ℂ U z)
    (hUp : ∀ q ∈ thetaDivisor τ, HasPrincipalPart U q 1)
    (hUper : ∀ z, ∀ᶠ w in 𝓝[≠] z, U (w + 1) = U w)
    {k : ℂ} (hUinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, U (w + τ) = U w + k) :
    (∀ x y, toMeromorphicNFOn (fun w => U w - thetaSource τ w) Set.univ x
        = toMeromorphicNFOn (fun w => U w - thetaSource τ w) Set.univ y)
      ∧ k = -(2 * (Real.pi : ℂ) * Complex.I) := by
  refine const_sub_of_matching_principal_parts hτ (thetaDivisor τ) 1 hUan
    (fun z hz => analyticAt_thetaSource_of_notMem hτ hz) hUp
    (fun q hq => hasPrincipalPart_thetaSource hτ hq) hUper ?_ hUinc
    (fun z => eventually_thetaSource_shift hτ z)
  intro z
  filter_upwards with w
  exact thetaSource_periodic τ w

end GaloisForLFunctions.HTGeometry
